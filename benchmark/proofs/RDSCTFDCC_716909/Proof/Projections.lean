import Mathlib
import Proof.Types.BoolMat
import Proof.Types.Interlace
import Proof.Types.Subgame
import Proof.Types.Extract
import Proof.Types.Equipartition
import Proof.Types.QProjection
import Proof.ChungProductTheorem

open Proof.Types.BoolMat
open Proof.Types.Interlace
open Proof.Types.Subgame
open Proof.Types.Extract
open Proof.Types.Equipartition
open Proof.Types.QProjection

open Finset

namespace Proof.Projections

/-! ### Helper lemmas for the Projection Lemma -/

/-- Sum of base-`n` digits weighted by powers is `< n^β`. -/
theorem digsum_lt (n β : ℕ) (b : ℕ → ℕ) (hn : 0 < n) (hb : ∀ γ, γ < β → b γ < n) :
    (∑ γ ∈ Finset.range β, b γ * n ^ γ) < n ^ β := by
  induction β with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have ihk : (∑ γ ∈ Finset.range k, b γ * n ^ γ) < n ^ k :=
      ih (fun γ hγ => hb γ (by omega))
    have hbk : b k < n := hb k (by omega)
    calc (∑ γ ∈ Finset.range k, b γ * n ^ γ) + b k * n ^ k
        < n ^ k + b k * n ^ k := by omega
      _ ≤ n ^ k + (n-1) * n ^ k := by
            apply Nat.add_le_add_left
            exact Nat.mul_le_mul_right _ (by omega)
      _ = n ^ (k+1) := by
            rw [pow_succ]
            cases n with
            | zero => omega
            | succ q =>
              have : (q + 1 - 1) = q := by omega
              rw [this]; ring

/-- Digit-extraction identity: the `β`-th base-`n` digit of `∑ b γ n^γ` is `b β`. -/
theorem digit_extract (n ℓ β : ℕ) (b : ℕ → ℕ) (hn : 0 < n) (hβ : β < ℓ)
    (hb : ∀ γ, γ < ℓ → b γ < n) :
    (∑ γ ∈ Finset.range ℓ, b γ * n ^ γ) / n ^ β % n = b β := by
  set lo := ∑ γ ∈ Finset.range β, b γ * n ^ γ with hlo
  set M := b β + ∑ γ ∈ Finset.Ico (β+1) ℓ, b γ * n ^ (γ - β) with hM
  have hlolt : lo < n ^ β := digsum_lt n β b hn (fun γ hγ => hb γ (by omega))
  have hdecomp : (∑ γ ∈ Finset.range ℓ, b γ * n ^ γ) = lo + n ^ β * M := by
    rw [hlo, hM, mul_add]
    have e1 : ∑ γ ∈ Finset.range ℓ, b γ * n ^ γ
        = (∑ γ ∈ Finset.range β, b γ * n ^ γ) + ∑ γ ∈ Finset.Ico β ℓ, b γ * n ^ γ := by
      rw [Finset.sum_range_add_sum_Ico _ (by omega : β ≤ ℓ)]
    rw [e1]
    have e2 : ∑ γ ∈ Finset.Ico β ℓ, b γ * n ^ γ
        = b β * n ^ β + ∑ γ ∈ Finset.Ico (β+1) ℓ, b γ * n ^ γ := by
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : β < ℓ)]
    rw [e2]
    have e3 : n ^ β * ∑ γ ∈ Finset.Ico (β+1) ℓ, b γ * n ^ (γ - β)
        = ∑ γ ∈ Finset.Ico (β+1) ℓ, b γ * n ^ γ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro γ hγ
      rw [Finset.mem_Ico] at hγ
      rw [← mul_assoc, mul_comm (n^β) (b γ), mul_assoc, ← pow_add]
      congr 2
      omega
    rw [e3]; ring
  have hMmod : M % n = b β := by
    rw [hM]
    have hdvd : n ∣ ∑ γ ∈ Finset.Ico (β+1) ℓ, b γ * n ^ (γ - β) := by
      apply Finset.dvd_sum
      intro γ hγ
      rw [Finset.mem_Ico] at hγ
      have hd : n ∣ n ^ (γ - β) := dvd_pow_self n (by omega)
      exact Dvd.dvd.mul_left hd _
    obtain ⟨w, hw⟩ := hdvd
    rw [hw, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (hb β hβ)
  rw [hdecomp]
  rw [Nat.add_mul_div_left _ _ (pow_pos hn β)]
  rw [Nat.div_eq_of_lt hlolt, Nat.zero_add]
  exact hMmod

/-- The `getD` of the sorted list at an in-range position equals `orderEmbOfFin`. -/
theorem sortGetD_eq_orderEmbOfFin (R : Finset ℕ) (i : Fin R.card) :
    (R.sort (· ≤ ·)).getD i 0 = R.orderEmbOfFin rfl i := by
  rw [Finset.orderEmbOfFin_apply]
  rw [List.getD_eq_getElem _ _ (by rw [Finset.length_sort]; exact i.2)]
  rfl

/-- The position of a member `x ∈ R` in the sorted order of `R`. -/
noncomputable def posOf (R : Finset ℕ) (x : ℕ) (hx : x ∈ R) : Fin R.card :=
  (R.orderIsoOfFin rfl).symm ⟨x, hx⟩

theorem orderEmbOfFin_posOf (R : Finset ℕ) (x : ℕ) (hx : x ∈ R) :
    R.orderEmbOfFin rfl (posOf R x hx) = x := by
  unfold posOf
  rw [← Finset.coe_orderIsoOfFin_apply]
  rw [OrderIso.apply_symm_apply]

theorem posOf_inj (R : Finset ℕ) (x y : ℕ) (hx : x ∈ R) (hy : y ∈ R)
    (h : posOf R x hx = posOf R y hy) : x = y := by
  unfold posOf at h
  have := (R.orderIsoOfFin rfl).symm.injective h
  exact congrArg Subtype.val this

/-- Membership in the projected row set `S` (non-empty `Q` branch): each `x ∈ S`
decomposes as `x = m*(x/m) + x%m` with `x/m < |Q|`, `x%m < m`, and the lifted
row `m*qElem Q (x/m) + x%m` lies in `R`. -/
theorem S_mem_char (R C : Finset ℕ) (m n p : ℕ) (Q : Finset ℕ) (hne : Q ≠ ∅) (x : ℕ)
    (hx : x ∈ (qProjection R C m n p Q).1) :
    x / m < Q.card ∧ x % m < m ∧ (m * qElem Q (x/m) + x % m) ∈ R ∧
      x = m * (x/m) + x % m := by
  unfold qProjection at hx
  simp only [hne, if_false] at hx
  rw [Finset.mem_image] at hx
  obtain ⟨pr, hpr, hpreq⟩ := hx
  rw [Finset.mem_filter] at hpr
  obtain ⟨hpr1, hpr2⟩ := hpr
  rw [show (Finset.range #Q).product (Finset.range m)
        = (Finset.range #Q) ×ˢ (Finset.range m) from rfl,
    Finset.mem_product, Finset.mem_range, Finset.mem_range] at hpr1
  obtain ⟨hγ, ht⟩ := hpr1
  have hxdiv : x / m = pr.1 := by
    rw [← hpreq, Nat.mul_add_div (lt_of_le_of_lt (Nat.zero_le _) ht),
      Nat.div_eq_of_lt ht, Nat.add_zero]
  have hxmod : x % m = pr.2 := by
    rw [← hpreq, Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hxdiv]; exact hγ
  · rw [hxmod]; exact ht
  · rw [hxdiv, hxmod]; exact hpr2
  · rw [hxdiv, hxmod]; omega

/-- Constructor direction for `S` membership (non-empty `Q` branch):
if `γ < |Q|`, `r < m`, and the lifted row `m*qElem Q γ + r ∈ R`, then
`m*γ + r ∈ S`. -/
theorem S_mem_of (R C : Finset ℕ) (m n p : ℕ) (Q : Finset ℕ) (hne : Q ≠ ∅)
    (γ r : ℕ) (hγ : γ < Q.card) (hr : r < m) (hmem : (m * qElem Q γ + r) ∈ R) :
    (m * γ + r) ∈ (qProjection R C m n p Q).1 := by
  unfold qProjection
  simp only [hne, if_false]
  rw [Finset.mem_image]
  refine ⟨(γ, r), ?_, rfl⟩
  rw [Finset.mem_filter]
  refine ⟨?_, hmem⟩
  rw [show (Finset.range #Q).product (Finset.range m)
        = (Finset.range #Q) ×ˢ (Finset.range m) from rfl,
    Finset.mem_product, Finset.mem_range, Finset.mem_range]
  exact ⟨hγ, hr⟩

/-- Membership in the projected column set `D` (non-empty `Q` branch): each
`d ∈ D` has a witness `c ∈ C` with `d = ∑_{γ<|Q|} digit c n (qElem Q γ) * n^γ`. -/
theorem D_mem_witness (R C : Finset ℕ) (m n p : ℕ) (Q : Finset ℕ) (hne : Q ≠ ∅) (d : ℕ)
    (hd : d ∈ (qProjection R C m n p Q).2) :
    ∃ c ∈ C, d = ∑ γ ∈ Finset.range Q.card, digit c n (qElem Q γ) * n ^ γ := by
  unfold qProjection at hd
  simp only [hne, if_false] at hd
  rw [Finset.mem_image] at hd
  obtain ⟨c, hc, hceq⟩ := hd
  exact ⟨c, hc, hceq.symm⟩

/-- `qElem Q γ ∈ Q` when `γ < |Q|`. -/
theorem qElem_mem (Q : Finset ℕ) (γ : ℕ) (hγ : γ < Q.card) : qElem Q γ ∈ Q := by
  unfold qElem
  have hlen : (Q.sort (· ≤ ·)).length = Q.card := Finset.length_sort _
  have hidx : γ < (Q.sort (· ≤ ·)).length := by rw [hlen]; exact hγ
  rw [List.getD_eq_getElem _ _ hidx]
  have : (Q.sort (· ≤ ·))[γ] ∈ (Q.sort (· ≤ ·)) := List.getElem_mem hidx
  rwa [Finset.mem_sort] at this

/-- `qElem Q γ = orderEmbOfFin` for `γ < |Q|`. -/
theorem qElem_eq_orderEmbOfFin (Q : Finset ℕ) (γ : ℕ) (hγ : γ < Q.card) :
    qElem Q γ = Q.orderEmbOfFin rfl ⟨γ, hγ⟩ := by
  unfold qElem
  have := sortGetD_eq_orderEmbOfFin Q ⟨γ, hγ⟩
  simpa using this

/-- `qElem` is strictly monotone on `[0, |Q|)`: the sorted enumeration of `Q` is
strictly increasing. -/
theorem qElem_lt_qElem (Q : Finset ℕ) (a b : ℕ) (ha : a < Q.card) (hb : b < Q.card)
    (hab : a < b) : qElem Q a < qElem Q b := by
  rw [qElem_eq_orderEmbOfFin Q a ha, qElem_eq_orderEmbOfFin Q b hb]
  exact (Q.orderEmbOfFin rfl).strictMono (by simpa using hab)

/-- `qElem Q γ < p` when `γ < |Q|` and `Q ⊆ [p)`. -/
theorem qElem_lt_p (Q : Finset ℕ) (p γ : ℕ) (hQ : Q ⊆ Finset.range p) (hγ : γ < Q.card) :
    qElem Q γ < p := by
  have := qElem_mem Q γ hγ
  have := hQ this
  rwa [Finset.mem_range] at this

/-- Chung's Product Theorem (Chung 1986). Now proved in this workspace (see
`Proof.ChungProductTheorem.chung_main`); no longer admitted as an axiom. The `0 < k`
hypothesis is required (the bare inequality is false at k=0, F=∅). -/
theorem Chung1986_ProductTheorem {U : Type*} [Fintype U] [DecidableEq U] {p : ℕ}
    (A : Fin p → Finset U) (k : ℕ) (hk : 0 < k)
    (hcover : ∀ u : U, k ≤ (Finset.univ.filter (fun i => u ∈ A i)).card)
    (F : Finset (Finset U)) :
    (F.card) ^ k ≤ ∏ i, (F.image (· ∩ A i)).card :=
  Proof.ChungProductTheorem.chung_main A k hk hcover F

/-- Theorem 3.18 (Product Theorem — Chung 1986, EXTERNAL).
Let `U` be a finite set and `A_1,…,A_p ⊆ U` such that every element of `U` lies in at
least `k` of them. Let `F` be a family of subsets of `U` and `F_i = { F ∩ A_i : F ∈ F }`.
Then `|F|^k ≤ ∏_{i=1}^p |F_i|`. -/
theorem product_theorem
    {U : Type*} [Fintype U] [DecidableEq U] {p : ℕ}
    (A : Fin p → Finset U) (k : ℕ) (hk : 0 < k)
    (hcover : ∀ u : U, k ≤ (Finset.univ.filter (fun i => u ∈ A i)).card)
    (F : Finset (Finset U)) :
    (F.card) ^ k ≤ ∏ i, (F.image (· ∩ A i)).card :=
  Chung1986_ProductTheorem A k hk hcover F

/-- Corollary 3.19.
Let `U = [n] × [p]` and `F` a family of subsets of `U`. For any integer `1 ≤ ℓ ≤ p`
there exists `Q ⊆ [p]` with `|Q| = ℓ` such that `|F|^{ℓ/p} ≤ |F_Q|`, where
`F_Q = { F ∩ ([n] × Q) : F ∈ F }`, modeled as keeping pairs whose second coordinate
lies in `Q`. -/
theorem corollary_3_19
    {n p : ℕ} (F : Finset (Finset (Fin n × Fin p)))
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓp : ℓ ≤ p) :
    ∃ Q : Finset (Fin p), Q.card = ℓ ∧
      (F.card : ℝ) ^ ((ℓ : ℝ) / (p : ℝ)) ≤
        ((F.image (fun S => S.filter (fun z => z.2 ∈ Q))).card : ℝ) := by
  classical
  have hp1 : 1 ≤ p := le_trans hℓ1 hℓp
  -- The collection 𝒬 of all ℓ-subsets of [p].
  set 𝒬 : Finset (Finset (Fin p)) := (Finset.univ : Finset (Fin p)).powersetCard ℓ with h𝒬
  set t : ℕ := 𝒬.card with ht
  have htchoose : t = Nat.choose p ℓ := by
    rw [ht, h𝒬, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have htpos : 0 < t := by
    rw [htchoose]; exact Nat.choose_pos hℓp
  -- An enumeration of the ℓ-subsets.
  let e : {x // x ∈ 𝒬} ≃ Fin t := 𝒬.equivFin
  -- The cover family.
  let A : Fin t → Finset (Fin n × Fin p) :=
    fun i => Finset.univ.filter (fun z => z.2 ∈ (e.symm i).1)
  set k : ℕ := Nat.choose (p - 1) (ℓ - 1) with hk
  -- Cover hypothesis: every element lies in exactly k of the A i.
  have hcover : ∀ u : Fin n × Fin p,
      k ≤ (Finset.univ.filter (fun i => u ∈ A i)).card := by
    intro u
    -- count of indices i with u ∈ A i equals count of Q ∈ 𝒬 with u.2 ∈ Q.
    have hbij : (Finset.univ.filter (fun i => u ∈ A i)).card
        = (𝒬.filter (fun Q => u.2 ∈ Q)).card := by
      apply Finset.card_bij (fun i _ => (e.symm i).1)
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, A] at hi
        rw [Finset.mem_filter]
        exact ⟨(e.symm i).2, hi⟩
      · intro i1 _ i2 _ heq
        have : e.symm i1 = e.symm i2 := Subtype.ext heq
        exact e.symm.injective this
      · intro Q hQ
        rw [Finset.mem_filter] at hQ
        refine ⟨e ⟨Q, hQ.1⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, A,
            Equiv.symm_apply_apply]
          exact hQ.2
        · simp [Equiv.symm_apply_apply]
    rw [hbij]
    -- now show k ≤ count of ℓ-subsets containing u.2
    have hcount : (𝒬.filter (fun Q => u.2 ∈ Q)).card = k := by
      rw [hk]
      rw [show (Nat.choose (p-1) (ℓ-1))
            = ((Finset.univ.erase u.2).powersetCard (ℓ-1)).card by
            rw [Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ u.2),
              Finset.card_univ, Fintype.card_fin]]
      apply Finset.card_bij (fun Q _ => Q.erase u.2)
      · intro Q hQ
        simp only [Finset.mem_filter, h𝒬, Finset.mem_powersetCard, Finset.mem_univ,
          true_and] at hQ
        rw [Finset.mem_powersetCard]
        refine ⟨Finset.erase_subset_erase _ (Finset.subset_univ _), ?_⟩
        rw [Finset.card_erase_of_mem hQ.2, hQ.1.2]
      · intro Q1 h1 Q2 h2 heq
        simp only [Finset.mem_filter] at h1 h2
        rw [← Finset.insert_erase h1.2, ← Finset.insert_erase h2.2, heq]
      · intro T hT
        rw [Finset.mem_powersetCard] at hT
        obtain ⟨hsub, hcard⟩ := hT
        refine ⟨insert u.2 T, ?_, ?_⟩
        · simp only [Finset.mem_filter, h𝒬, Finset.mem_powersetCard, Finset.mem_univ,
            true_and]
          refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.mem_insert_self u.2 T⟩
          rw [Finset.card_insert_of_notMem, hcard, Nat.sub_add_cancel hℓ1]
          intro hmem
          have := hsub hmem
          simp at this
        · rw [Finset.erase_insert]
          intro hmem
          have := hsub hmem
          simp at this
    rw [hcount]
  -- Apply the product theorem.
  have hkpos : 0 < k := by rw [hk]; exact Nat.choose_pos (by omega)
  have hprod := product_theorem A k hkpos hcover F
  -- Bound product by maximal factor.
  obtain ⟨istar, _, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin t))
      (fun i => (F.image (· ∩ A i)).card) (Finset.univ_nonempty_iff.2 ⟨⟨0, htpos⟩⟩)
  set b : ℕ := (F.image (· ∩ A istar)).card with hb
  have hpmax : (∏ i, (F.image (· ∩ A i)).card) ≤ b ^ t := by
    have := Finset.prod_le_pow_card (Finset.univ : Finset (Fin t))
      (fun i => (F.image (· ∩ A i)).card) b (fun i _ => hmax i (Finset.mem_univ i))
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hnat : F.card ^ k ≤ b ^ t := le_trans hprod hpmax
  -- The witness.
  refine ⟨(e.symm istar).1, ?_, ?_⟩
  · have hmem := (e.symm istar).2
    simp only [h𝒬, Finset.mem_powersetCard] at hmem
    exact hmem.2
  -- Bridge image equality so b is the RHS quantity.
  have himg : F.image (· ∩ A istar)
      = F.image (fun S => S.filter (fun z => z.2 ∈ (e.symm istar).1)) := by
    apply Finset.image_congr
    intro S _
    ext z
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, A]
  -- Exponent identity ℓ * (p choose ℓ) = p * ((p-1) choose (ℓ-1)).
  have hexp : ℓ * t = p * k := by
    rw [htchoose, hk]
    have h := Nat.add_one_mul_choose_eq (p-1) (ℓ-1)
    rw [Nat.sub_add_cancel hp1, Nat.sub_add_cancel hℓ1] at h
    linarith [h]
  -- Now the real-analysis part.
  rw [← himg, ← hb]
  -- Goal: (F.card : ℝ) ^ (ℓ/p) ≤ (b : ℝ)
  have hppos : 0 < (p : ℝ) := by exact_mod_cast hp1
  have hbnn : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hFnn : (0 : ℝ) ≤ (F.card : ℝ) := Nat.cast_nonneg _
  -- From hnat over ℝ.
  have hnatR : (F.card : ℝ) ^ k ≤ (b : ℝ) ^ t := by exact_mod_cast hnat
  -- Take t-th root: ((F.card)^k)^(1/t) ≤ ((b)^t)^(1/t) = b.
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htpos
  -- (F.card)^(k/t) = ((F.card)^k)^(1/t)
  have key : (F.card : ℝ) ^ ((k : ℝ) / (t : ℝ)) ≤ (b : ℝ) := by
    have lhs_eq : (F.card : ℝ) ^ ((k : ℝ) / (t : ℝ))
        = (((F.card : ℝ) ^ k) : ℝ) ^ ((1 : ℝ) / (t : ℝ)) := by
      rw [← Real.rpow_natCast (F.card : ℝ) k, ← Real.rpow_mul hFnn]
      congr 1
      field_simp
    rw [lhs_eq]
    have rhs_eq : (b : ℝ) = (((b : ℝ) ^ t) : ℝ) ^ ((1 : ℝ) / (t : ℝ)) := by
      rw [← Real.rpow_natCast (b : ℝ) t, ← Real.rpow_mul hbnn]
      rw [mul_one_div, div_self (ne_of_gt htR), Real.rpow_one]
    rw [rhs_eq]
    exact Real.rpow_le_rpow (pow_nonneg hFnn k) hnatR
      (div_nonneg zero_le_one (le_of_lt htR))
  -- Replace k/t with ℓ/p.
  have hexpR : (k : ℝ) / (t : ℝ) = (ℓ : ℝ) / (p : ℝ) := by
    have htRne : (t : ℝ) ≠ 0 := ne_of_gt htR
    have hpRne : (p : ℝ) ≠ 0 := ne_of_gt hppos
    have hid : (ℓ : ℝ) * (t : ℝ) = (p : ℝ) * (k : ℝ) := by exact_mod_cast hexp
    field_simp
    linarith [hid]
  rw [← hexpR]
  exact key

/-- The `(i,j)` entry of `extract M R C`, when the sorted-position lookups are
in range, reads the underlying matrix `M` at those indices. -/
theorem extract_e_eq (M : BoolMat) (R C : Finset ℕ)
    (i : Fin (extract M R C).m) (j : Fin (extract M R C).n)
    (hr : (R.sort (· ≤ ·)).getD i 0 < M.m) (hc : (C.sort (· ≤ ·)).getD j 0 < M.n) :
    (extract M R C).e i j = M.e ⟨(R.sort (· ≤ ·)).getD i 0, hr⟩ ⟨(C.sort (· ≤ ·)).getD j 0, hc⟩ := by
  show (if h : (R.sort (· ≤ ·)).getD i 0 < M.m ∧ (C.sort (· ≤ ·)).getD j 0 < M.n then
      M.e ⟨_, h.1⟩ ⟨_, h.2⟩ else false) = _
  rw [dif_pos ⟨hr, hc⟩]

/-- The `(i,j)` entry of `interlace A p` in terms of base-`n` digits, given the
component/digit are in range. -/
theorem interlace_e_eq (A : BoolMat) (p : ℕ) (i : Fin (interlace A p).m)
    (j : Fin (interlace A p).n)
    (hi' : i.val % A.m < A.m) (hj' : (j.val / A.n ^ (i.val / A.m)) % A.n < A.n) :
    (interlace A p).e i j = A.e ⟨i.val % A.m, hi'⟩ ⟨(j.val / A.n ^ (i.val / A.m)) % A.n, hj'⟩ := by
  rfl

/-- Lemma 3.16 (Projection Lemma).
For any `m × n` matrix `A`, positive integer `p`, and selections `R ⊆ [m·p)`,
`C ⊆ [n^p)`, if `Q ⊆ [p)` is non-empty with Q-projection `(S, D)`, then
`ε(⟨A⟩^{|Q|}, S, D) ⊑ ε(⟨A⟩^p, R, C)`. -/
theorem projection_lemma
    (A : BoolMat) (p : ℕ)
    (R C : Finset ℕ)
    (hR : R ⊆ Finset.range (A.m * p))
    (hC : C ⊆ Finset.range (A.n ^ p))
    (Q : Finset ℕ)
    (hQ : Q ⊆ Finset.range p) (hQne : Q.Nonempty) :
    IsSubgame
      (extract (interlace A Q.card)
        (qProjection R C A.m A.n p Q).1 (qProjection R C A.m A.n p Q).2)
      (extract (interlace A p) R C) := by
  classical
  set m := A.m with hm_def
  set n := A.n with hn_def
  set ℓ := Q.card with hℓ_def
  have hQemp : Q ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hQne
  set S := (qProjection R C m n p Q).1 with hS_def
  set D := (qProjection R C m n p Q).2 with hD_def
  -- `p > 0` from `Q ⊆ [p)` nonempty.
  obtain ⟨q0, hq0⟩ := hQne
  have hp_pos : 0 < p := by
    have := hQ hq0; rw [Finset.mem_range] at this; omega
  -- value-level row map: lift `s_i = orderEmbOfFin S i` to `σ'(s_i) ∈ R`.
  -- `s_i ∈ S` membership + characterisation.
  have hsiMem : ∀ i : Fin S.card, S.orderEmbOfFin rfl i ∈ S :=
    fun i => S.orderEmbOfFin_mem rfl i
  have hsiChar : ∀ i : Fin S.card,
      (S.orderEmbOfFin rfl i) / m < ℓ ∧ (S.orderEmbOfFin rfl i) % m < m ∧
        (m * qElem Q ((S.orderEmbOfFin rfl i)/m) + (S.orderEmbOfFin rfl i) % m) ∈ R ∧
        (S.orderEmbOfFin rfl i) = m * ((S.orderEmbOfFin rfl i)/m) + (S.orderEmbOfFin rfl i) % m :=
    fun i => S_mem_char R C m n p Q hQemp _ (hsiMem i)
  -- value-level column map: each `d_j` has a chosen preimage `c_j ∈ C`.
  have hdjMem : ∀ j : Fin D.card, D.orderEmbOfFin rfl j ∈ D :=
    fun j => D.orderEmbOfFin_mem rfl j
  have hdjWit : ∀ j : Fin D.card,
      ∃ c ∈ C, D.orderEmbOfFin rfl j = ∑ γ ∈ Finset.range ℓ, digit c n (qElem Q γ) * n ^ γ :=
    fun j => D_mem_witness R C m n p Q hQemp _ (hdjMem j)
  -- the chosen witness `c_j` and its defining equation.
  set cj : Fin D.card → ℕ := fun j => Classical.choose (hdjWit j) with hcj_def
  have hcjMem : ∀ j, cj j ∈ C := fun j => (Classical.choose_spec (hdjWit j)).1
  have hcjEq : ∀ j, D.orderEmbOfFin rfl j
      = ∑ γ ∈ Finset.range ℓ, digit (cj j) n (qElem Q γ) * n ^ γ :=
    fun j => (Classical.choose_spec (hdjWit j)).2
  -- the position maps.
  set σ : Fin S.card → Fin R.card :=
    fun i => posOf R _ (hsiChar i).2.2.1 with hσ_def
  set τ : Fin D.card → Fin C.card := fun j => posOf C (cj j) (hcjMem j) with hτ_def
  refine ⟨σ, τ, ?_, ?_, ?_⟩
  · -- injectivity of σ
    intro i i' hii
    rw [hσ_def] at hii
    simp only at hii
    -- σ'(s_i) = σ'(s_{i'})
    have hval : m * qElem Q ((S.orderEmbOfFin rfl i)/m) + (S.orderEmbOfFin rfl i) % m
        = m * qElem Q ((S.orderEmbOfFin rfl i')/m) + (S.orderEmbOfFin rfl i') % m :=
      posOf_inj R _ _ (hsiChar i).2.2.1 (hsiChar i').2.2.1 hii
    set γ := (S.orderEmbOfFin rfl i)/m with hγ
    set γ' := (S.orderEmbOfFin rfl i')/m with hγ'
    set t := (S.orderEmbOfFin rfl i) % m with ht
    set t' := (S.orderEmbOfFin rfl i') % m with ht'
    have htlt : t < m := (hsiChar i).2.1
    have htlt' : t' < m := (hsiChar i').2.1
    -- reduce mod m: t = t'
    have hmod : t = t' := by
      have h1 : (m * qElem Q γ + t) % m = t := by
        rw [Nat.mul_add_mod_self_left]; exact Nat.mod_eq_of_lt htlt
      have h2 : (m * qElem Q γ' + t') % m = t' := by
        rw [Nat.mul_add_mod_self_left]; exact Nat.mod_eq_of_lt htlt'
      rw [← h1, ← h2, hval]
    -- then m * qElem γ = m * qElem γ'
    have hmq : m * qElem Q γ = m * qElem Q γ' := by omega
    have hm_pos : 0 < m := lt_of_le_of_lt (Nat.zero_le t) htlt
    have hqe : qElem Q γ = qElem Q γ' := Nat.eq_of_mul_eq_mul_left hm_pos hmq
    -- qElem injective on range ⟹ γ = γ'
    have hγlt : γ < ℓ := (hsiChar i).1
    have hγlt' : γ' < ℓ := (hsiChar i').1
    have hγeq : γ = γ' := by
      rcases lt_trichotomy γ γ' with h | h | h
      · exact absurd hqe (ne_of_lt (qElem_lt_qElem Q γ γ' hγlt hγlt' h))
      · exact h
      · exact absurd hqe.symm (ne_of_lt (qElem_lt_qElem Q γ' γ hγlt' hγlt h))
    -- s_i = s_{i'}
    have hseq : S.orderEmbOfFin rfl i = S.orderEmbOfFin rfl i' := by
      rw [(hsiChar i).2.2.2, (hsiChar i').2.2.2, ← hγ, ← hγ', ← ht, ← ht', hγeq, hmod]
    exact (S.orderEmbOfFin rfl).injective hseq
  · -- injectivity of τ
    intro j j' hjj
    rw [hτ_def] at hjj
    simp only at hjj
    have hcval : cj j = cj j' := posOf_inj C _ _ (hcjMem j) (hcjMem j') hjj
    -- d_j and d_{j'} have the same digit expansion ⟹ equal
    have hdeq : D.orderEmbOfFin rfl j = D.orderEmbOfFin rfl j' := by
      rw [hcjEq j, hcjEq j', hcval]
    exact (D.orderEmbOfFin rfl).injective hdeq
  · -- entry equality
    intro i j
    -- name the sorted-position values
    set si := S.orderEmbOfFin rfl i with hsi_def
    set dj := D.orderEmbOfFin rfl j with hdj_def
    -- positivity of m and n
    have hm_pos : 0 < m := lt_of_le_of_lt (Nat.zero_le _) (hsiChar i).2.1
    have hn_pos : 0 < n := by
      have hcjlt : cj j < n ^ p := by
        have := hC (hcjMem j); rwa [Finset.mem_range] at this
      have hpow : 0 < n ^ p := lt_of_le_of_lt (Nat.zero_le _) hcjlt
      by_contra h
      have hz : n = 0 := Nat.le_zero.mp (Nat.not_lt.mp h)
      rw [hz, Nat.zero_pow hp_pos] at hpow
      exact absurd hpow (lt_irrefl 0)
    -- abbreviations for the component γ and within-block row t of si
    set γ := si / m with hγ_def
    set t := si % m with ht_def
    have hγlt : γ < ℓ := (hsiChar i).1
    have htlt : t < m := (hsiChar i).2.1
    have hsiR : m * qElem Q γ + t ∈ R := (hsiChar i).2.2.1
    have hsidecomp : si = m * γ + t := (hsiChar i).2.2.2
    -- LHS sorted lookup = si, in range si < A.m * ℓ
    have hsival : (S.sort (· ≤ ·)).getD i 0 = si := by
      rw [hsi_def]; exact sortGetD_eq_orderEmbOfFin S i
    have hsi_mem : si ∈ S := by rw [hsi_def]; exact hsiMem i
    have hsi_lt : si < m * ℓ := by
      -- si = m*γ + t < m*γ + m = m*(γ+1) ≤ m*ℓ
      have : si < m * γ + m := by rw [hsidecomp]; omega
      calc si < m * γ + m := this
        _ = m * (γ + 1) := by ring
        _ ≤ m * ℓ := Nat.mul_le_mul_left _ (by omega)
    -- RHS row sorted lookup = m*qElem γ + t
    have hσval : (R.sort (· ≤ ·)).getD (σ i) 0 = m * qElem Q γ + t := by
      rw [sortGetD_eq_orderEmbOfFin R (σ i)]
      rw [hσ_def]
      simp only
      rw [orderEmbOfFin_posOf]
    -- RHS row in range < A.m * p
    have hqγ_lt_p : qElem Q γ < p := qElem_lt_p Q p γ hQ (by rw [hℓ_def] at hγlt; exact hγlt)
    have hσ_lt : m * qElem Q γ + t < m * p := by
      have : m * qElem Q γ + t < m * qElem Q γ + m := by omega
      calc m * qElem Q γ + t < m * qElem Q γ + m := this
        _ = m * (qElem Q γ + 1) := by ring
        _ ≤ m * p := Nat.mul_le_mul_left _ (by omega)
    -- RHS column sorted lookup = cj j
    have hτval : (C.sort (· ≤ ·)).getD (τ j) 0 = cj j := by
      rw [sortGetD_eq_orderEmbOfFin C (τ j)]
      rw [hτ_def]
      simp only
      rw [orderEmbOfFin_posOf]
    have hcj_lt : cj j < n ^ p := by
      have := hC (hcjMem j); rwa [Finset.mem_range] at this
    -- the τ'-digit identity at component γ: digit dj n γ = digit (cj j) n (qElem γ)
    have hdigit : dj / n ^ γ % n = digit (cj j) n (qElem Q γ) := by
      rw [hdj_def, hcjEq j]
      have hbnd : ∀ γ', γ' < ℓ → digit (cj j) n (qElem Q γ') < n := by
        intro γ' _
        unfold digit
        exact Nat.mod_lt _ hn_pos
      rw [digit_extract n ℓ γ (fun γ' => digit (cj j) n (qElem Q γ')) hn_pos hγlt hbnd]
    -- Now rewrite both extract entries via interlace.
    -- LHS
    have hLm : (interlace A ℓ).m = m * ℓ := by rw [hm_def]; rfl
    have hLn : (interlace A ℓ).n = n ^ ℓ := by rw [hn_def]; rfl
    have hPm : (interlace A p).m = m * p := by rw [hm_def]; rfl
    have hPn : (interlace A p).n = n ^ p := by rw [hn_def]; rfl
    -- ranges for the LHS interlace lookup
    have hsi_lt_M : (S.sort (· ≤ ·)).getD i 0 < (interlace A ℓ).m := by
      rw [hsival, hLm]; exact hsi_lt
    have hdj_lt_M : (D.sort (· ≤ ·)).getD j 0 < (interlace A ℓ).n := by
      have hdj_mem : dj ∈ D := by rw [hdj_def]; exact hdjMem j
      -- dj = Σ digit < n^ℓ
      have hdjval2 : dj = ∑ γ' ∈ Finset.range ℓ, digit (cj j) n (qElem Q γ') * n ^ γ' := by
        rw [hdj_def]; exact hcjEq j
      have hdj_lt : dj < n ^ ℓ := by
        rw [hdjval2]
        apply digsum_lt n ℓ _ hn_pos
        intro γ' _; unfold digit; exact Nat.mod_lt _ hn_pos
      rw [hdj_def] at hdj_lt
      have : (D.sort (· ≤ ·)).getD j 0 = dj := by rw [hdj_def]; exact sortGetD_eq_orderEmbOfFin D j
      rw [this, hLn, hdj_def]; exact hdj_lt
    -- ranges for the RHS interlace lookup
    have hσ_lt_P : (R.sort (· ≤ ·)).getD (σ i) 0 < (interlace A p).m := by
      rw [hσval, hPm]; exact hσ_lt
    have hτ_lt_P : (C.sort (· ≤ ·)).getD (τ j) 0 < (interlace A p).n := by
      rw [hτval, hPn]; exact hcj_lt
    -- unfold both extract entries to interlace entries
    rw [extract_e_eq (interlace A ℓ) S D i j hsi_lt_M hdj_lt_M]
    rw [extract_e_eq (interlace A p) R C (σ i) (τ j) hσ_lt_P hτ_lt_P]
    -- now both are interlace entries; unfold to A.e
    have hrowL : ((S.sort (· ≤ ·)).getD i 0) % A.m < A.m := by
      rw [hsival]; rw [← hm_def]; exact (by omega : si % m < m)
    have hcolL : (((D.sort (· ≤ ·)).getD j 0) / A.n ^ (((S.sort (· ≤ ·)).getD i 0) / A.m)) % A.n < A.n := by
      rw [← hn_def]; exact Nat.mod_lt _ hn_pos
    have hrowP : ((R.sort (· ≤ ·)).getD (σ i) 0) % A.m < A.m := by
      rw [← hm_def]; exact Nat.mod_lt _ hm_pos
    have hcolP : (((C.sort (· ≤ ·)).getD (τ j) 0) / A.n ^ (((R.sort (· ≤ ·)).getD (σ i) 0) / A.m)) % A.n < A.n := by
      rw [← hn_def]; exact Nat.mod_lt _ hn_pos
    rw [interlace_e_eq A ℓ ⟨_, hsi_lt_M⟩ ⟨_, hdj_lt_M⟩ hrowL hcolL]
    rw [interlace_e_eq A p ⟨_, hσ_lt_P⟩ ⟨_, hτ_lt_P⟩ hrowP hcolP]
    -- now both are A.e at concrete indices; show the row and column indices match.
    congr 1
    · -- row index: si % A.m = (m*qElem γ + t) % A.m, both equal t
      apply Fin.ext
      simp only
      rw [hsival, hσval, ← hm_def]
      conv_lhs => rw [hsidecomp]
      rw [Nat.mul_add_mod_self_left, Nat.mul_add_mod_self_left]
    · -- column index
      apply Fin.ext
      simp only
      rw [hsival, hσval, hτval, ← hm_def, ← hn_def]
      -- fold the D sorted lookup to dj
      have hdjsort : (D.sort (· ≤ ·)).getD (j : ℕ) 0 = dj := by
        rw [hdj_def]; exact sortGetD_eq_orderEmbOfFin D j
      rw [hdjsort]
      -- component on LHS: si / m = γ ; on RHS: (m*qElem γ + t)/m = qElem γ
      conv_lhs => rw [hsidecomp]
      rw [Nat.mul_add_div hm_pos, Nat.div_eq_of_lt htlt, Nat.add_zero]
      rw [Nat.mul_add_div hm_pos, Nat.div_eq_of_lt htlt, Nat.add_zero]
      -- now LHS: dj / n^γ % n  ; RHS: cj j / n^(qElem γ) % n = digit (cj j) n (qElem γ)
      rw [hdigit]
      rfl

/-! ### Helper lemmas for the Balancing Lemma (3.20) -/

/-- Transitivity of `⊑` (local copy used before the file's `subgame_trans`). -/
theorem subgame_trans_bl {X Y Z : BoolMat} (h1 : IsSubgame X Y) (h2 : IsSubgame Y Z) :
    IsSubgame X Z := by
  obtain ⟨r1, c1, hr1, hc1, he1⟩ := h1
  obtain ⟨r2, c2, hr2, hc2, he2⟩ := h2
  refine ⟨r2 ∘ r1, c2 ∘ c1, hr2.comp hr1, hc2.comp hc1, ?_⟩
  intro i j
  rw [he1 i j, he2 (r1 i) (c1 j)]
  rfl

/-- A `0`-row matrix is a subgame of any matrix (vacuous row map). -/
theorem subgame_zero_rows_bl (A B : BoolMat) (hA : A.m = 0)
    (c : Fin A.n → Fin B.n) (hc : Function.Injective c) :
    IsSubgame A B := by
  refine ⟨fun i => (Fin.cast hA i).elim0, c, ?_, hc, ?_⟩
  · intro i; exact (Fin.cast hA i).elim0
  · intro i j; exact (Fin.cast hA i).elim0

/-- Row-subset subgame (local copy). -/
theorem row_subset_subgame_bl (M : BoolMat) (S S' D : Finset ℕ) (hSS : S ⊆ S') :
    IsSubgame (extract M S D) (extract M S' D) := by
  classical
  have hmem : ∀ i : Fin (extract M S D).m, (S.orderEmbOfFin rfl i) ∈ S' := by
    intro i
    exact hSS (S.orderEmbOfFin_mem rfl i)
  refine ⟨fun i => posOf S' (S.orderEmbOfFin rfl i) (hmem i), fun j => j, ?_, ?_, ?_⟩
  · intro i i' h
    simp only at h
    have := posOf_inj S' _ _ (hmem i) (hmem i') h
    exact (S.orderEmbOfFin rfl).injective this
  · intro j j' h; exact h
  · intro i j
    have hrow : (S'.sort (· ≤ ·)).getD ((posOf S' (S.orderEmbOfFin rfl i) (hmem i)) : ℕ) 0
        = (S.sort (· ≤ ·)).getD (i : ℕ) 0 := by
      rw [sortGetD_eq_orderEmbOfFin S' (posOf S' (S.orderEmbOfFin rfl i) (hmem i)),
        orderEmbOfFin_posOf, sortGetD_eq_orderEmbOfFin S i]
    show (if h : (S.sort (· ≤ ·)).getD (i : ℕ) 0 < M.m ∧ (D.sort (· ≤ ·)).getD (j : ℕ) 0 < M.n then
        M.e ⟨_, h.1⟩ ⟨_, h.2⟩ else false)
      = (if h : (S'.sort (· ≤ ·)).getD ((posOf S' (S.orderEmbOfFin rfl i) (hmem i)) : ℕ) 0 < M.m
            ∧ (D.sort (· ≤ ·)).getD (j : ℕ) 0 < M.n then
          M.e ⟨_, h.1⟩ ⟨_, h.2⟩ else false)
    simp only [hrow]

/-- Per-block thinning (local copy). -/
theorem exists_thinned_bl (S' : Finset ℕ) (m ℓ k : ℕ)
    (hblk : ∀ κ < ℓ, k ≤ (S'.filter (fun i => m * κ ≤ i ∧ i < m * (κ+1))).card) :
    ∃ S : Finset ℕ, S ⊆ S' ∧
      ∀ κ < ℓ, (S.filter (fun i => m * κ ≤ i ∧ i < m * (κ+1))).card = k := by
  classical
  have hchoose : ∀ κ, ∃ t : Finset ℕ,
      t ⊆ S'.filter (fun i => m * κ ≤ i ∧ i < m * (κ+1)) ∧
        (κ < ℓ → t.card = k) := by
    intro κ
    by_cases hκ : κ < ℓ
    · obtain ⟨t, hsub, hcard⟩ := Finset.exists_subset_card_eq (hblk κ hκ)
      exact ⟨t, hsub, fun _ => hcard⟩
    · exact ⟨∅, Finset.empty_subset _, fun h => absurd h hκ⟩
  choose ch hch1 hch2 using hchoose
  refine ⟨(Finset.range ℓ).biUnion ch, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨κ, _, hxκ⟩ := hx
    have := hch1 κ hxκ
    rw [Finset.mem_filter] at this
    exact this.1
  · intro κ₀ hκ₀
    have heq : ((Finset.range ℓ).biUnion ch).filter (fun i => m * κ₀ ≤ i ∧ i < m * (κ₀+1))
        = ch κ₀ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
      constructor
      · rintro ⟨⟨κ, hκ, hxκ⟩, hlo, hhi⟩
        have hmemκ := hch1 κ hxκ
        rw [Finset.mem_filter] at hmemκ
        obtain ⟨_, hlo', hhi'⟩ := hmemκ
        have hκκ₀ : κ = κ₀ := by
          rcases Nat.eq_zero_or_pos m with hm0 | hmpos
          · subst hm0; simp at hhi
          · have e1 : x / m = κ := Nat.div_eq_of_lt_le
              (by rw [Nat.mul_comm]; exact hlo') (by rw [Nat.mul_comm]; exact hhi')
            have e2 : x / m = κ₀ := Nat.div_eq_of_lt_le
              (by rw [Nat.mul_comm]; exact hlo) (by rw [Nat.mul_comm]; exact hhi)
            omega
        rw [← hκκ₀]; exact hxκ
      · intro hx
        have hmemκ := hch1 κ₀ hx
        rw [Finset.mem_filter] at hmemκ
        obtain ⟨_, hlo, hhi⟩ := hmemκ
        exact ⟨⟨κ₀, hκ₀, hx⟩, hlo, hhi⟩
    rw [heq]; exact hch2 κ₀ hκ₀

/-- `ℓ ≤ p`: the balancing target never exceeds `p`. -/
theorem balancing_ell_le_p
    (m p : ℕ) (R : Finset ℕ) (hRcard : R.card ≤ m * p)
    (T : ℝ) (hT0 : 0 ≤ T) (hTm : T < m)
    (ℓ : ℕ)
    (hℓ : (ℓ : ℝ) = ⌈(p : ℝ) * (1 - (1 - (R.card : ℝ) / ((p : ℝ) * (m : ℝ)))
                  / (1 - T / (m : ℝ)))⌉₊) :
    ℓ ≤ p := by
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso; rw [h] at hTm; simp at hTm; linarith
    · exact h
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hmT : (0 : ℝ) < (m : ℝ) - T := by linarith
  have hle : (p : ℝ) * (1 - (1 - (R.card : ℝ) / ((p : ℝ) * (m : ℝ)))
                  / (1 - T / (m : ℝ))) ≤ (p : ℝ) := by
    rcases Nat.eq_zero_or_pos p with hp0 | hp0
    · simp [hp0]
    · have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
      have hRle : (R.card : ℝ) ≤ (p : ℝ) * (m : ℝ) := by
        have : (R.card : ℝ) ≤ ((m * p : ℕ) : ℝ) := by exact_mod_cast hRcard
        rw [Nat.cast_mul] at this; nlinarith [this]
      have hnum : (0 : ℝ) ≤ 1 - (R.card : ℝ) / ((p : ℝ) * (m : ℝ)) := by
        rw [sub_nonneg, div_le_one (by positivity)]; exact hRle
      have hden : (0 : ℝ) < 1 - T / (m : ℝ) := by
        rw [sub_pos, div_lt_one hmR]; exact hTm
      have hfrac : (0 : ℝ) ≤ (1 - (R.card : ℝ) / ((p : ℝ) * (m : ℝ))) / (1 - T / (m : ℝ)) :=
        div_nonneg hnum (le_of_lt hden)
      nlinarith [hfrac, hpR]
  have hℓnat : ℓ = ⌈(p : ℝ) * (1 - (1 - (R.card : ℝ) / ((p : ℝ) * (m : ℝ)))
                  / (1 - T / (m : ℝ)))⌉₊ := by exact_mod_cast hℓ
  rw [hℓnat]
  exact Nat.ceil_le.mpr (le_trans hle (by exact_mod_cast le_refl p))

/-- The projected row set is contained in `[0, m·|Q|)`. -/
theorem qProjection_S_subset_range_bl (R C : Finset ℕ) (m n p : ℕ) (Q : Finset ℕ) :
    (qProjection R C m n p Q).1 ⊆ Finset.range (m * Q.card) := by
  by_cases hQe : Q = ∅
  · simp [qProjection, hQe]
  · intro x hx
    obtain ⟨hxdiv, hxmod, _, hxdecomp⟩ := S_mem_char R C m n p Q hQe x hx
    rw [Finset.mem_range]
    have hm_pos : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hxmod
    calc x = m * (x / m) + x % m := hxdecomp
      _ < m * (x / m) + m := by omega
      _ = m * (x / m + 1) := by ring
      _ ≤ m * Q.card := Nat.mul_le_mul_left _ (by omega)

/-- The projected column set is contained in `[0, n^|Q|)` when `n > 0`. -/
theorem qProjection_D_subset_range_bl (R C : Finset ℕ) (m n p : ℕ) (Q : Finset ℕ)
    (hn : 0 < n) :
    (qProjection R C m n p Q).2 ⊆ Finset.range (n ^ Q.card) := by
  by_cases hQe : Q = ∅
  · simp [qProjection, hQe]
  · intro d hd
    obtain ⟨c, _, hdeq⟩ := D_mem_witness R C m n p Q hQe d hd
    rw [Finset.mem_range, hdeq]
    apply digsum_lt n Q.card _ hn
    intro γ _; unfold digit; exact Nat.mod_lt _ hn

/-- **HARD STEP (equipartition thinning — Step 5).** If `Q ≠ ∅` and each chosen
component holds at least `⌈T⌉₊` rows of `R`, the projected row set `S'` admits an
`m,T,|Q|`-equipartitioned subset `S ⊆ S'`. -/
theorem balancing_exists_equipartition
    (R C : Finset ℕ) (m n p : ℕ) (Q : Finset ℕ) (hQne : Q ≠ ∅)
    (T : ℝ)
    (hblock : ∀ γ ∈ Q, ⌈T⌉₊ ≤ (R.filter (fun i => m * γ ≤ i ∧ i < m * (γ + 1))).card) :
    ∃ S : Finset ℕ, S ⊆ (qProjection R C m n p Q).1 ∧
      IsEquipartitioned S m T Q.card := by
  classical
  set S' := (qProjection R C m n p Q).1 with hS'_def
  set ℓ := Q.card with hℓ_def
  -- block-card equality: S'-block κ ↔ R-block (qElem Q κ).
  have hcardeq : ∀ κ < ℓ,
      (S'.filter (fun i => m * κ ≤ i ∧ i < m * (κ + 1))).card
        = (R.filter (fun i => m * qElem Q κ ≤ i ∧ i < m * (qElem Q κ + 1))).card := by
    intro κ hκ
    set q := qElem Q κ with hq_def
    have hκℓ : κ < Q.card := by rw [← hℓ_def]; exact hκ
    apply Finset.card_nbij'
      (i := fun x => m * q + x % m)
      (j := fun y => m * κ + y % m)
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx ⊢
      obtain ⟨hxS, hxlo, hxhi⟩ := hx
      rw [hS'_def] at hxS
      obtain ⟨hdiv, hmod, hRmem, hdecomp⟩ := S_mem_char R C m n p Q hQne x hxS
      have hxdivκ : x / m = κ :=
        Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact hxlo) (by rw [Nat.mul_comm]; exact hxhi)
      have hqsucc : m * (q + 1) = m * q + m := by ring
      refine ⟨?_, ?_, ?_⟩
      · rw [hxdivκ] at hRmem; rw [← hq_def] at hRmem; exact hRmem
      · exact Nat.le_add_right _ _
      · rw [hqsucc]; have : x % m < m := hmod; omega
    · intro y hy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hy ⊢
      obtain ⟨hyR, hylo, hyhi⟩ := hy
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · exfalso; rw [h] at hylo hyhi; omega
        · exact h
      have hymod : y % m < m := Nat.mod_lt _ hm_pos
      have hydiv : y / m = q :=
        Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact hylo) (by rw [Nat.mul_comm]; exact hyhi)
      have hydecomp : y = m * q + y % m := by
        conv_lhs => rw [← Nat.div_add_mod y m, hydiv]
      have hκsucc : m * (κ + 1) = m * κ + m := by ring
      refine ⟨?_, ?_, ?_⟩
      · rw [hS'_def]
        exact S_mem_of R C m n p Q hQne κ (y % m) hκℓ hymod
          (by rw [← hq_def, ← hydecomp]; exact hyR)
      · exact Nat.le_add_right _ _
      · rw [hκsucc]; omega
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
      obtain ⟨hxS, hxlo, hxhi⟩ := hx
      rw [hS'_def] at hxS
      obtain ⟨hdiv, hmod, hRmem, hdecomp⟩ := S_mem_char R C m n p Q hQne x hxS
      have hxdivκ : x / m = κ :=
        Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact hxlo) (by rw [Nat.mul_comm]; exact hxhi)
      simp only
      rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hmod]
      conv_rhs => rw [hdecomp, hxdivκ]
    · intro y hy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hy
      obtain ⟨hyR, hylo, hyhi⟩ := hy
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · exfalso; rw [h] at hylo hyhi; omega
        · exact h
      have hymod : y % m < m := Nat.mod_lt _ hm_pos
      have hydiv : y / m = q :=
        Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact hylo) (by rw [Nat.mul_comm]; exact hyhi)
      have hydecomp : y = m * q + y % m := by
        conv_lhs => rw [← Nat.div_add_mod y m, hydiv]
      simp only
      rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hymod]
      rw [← hydecomp]
  -- each S'-block has ≥ ⌈T⌉₊ elements.
  have hblk : ∀ κ < ℓ, ⌈T⌉₊ ≤ (S'.filter (fun i => m * κ ≤ i ∧ i < m * (κ + 1))).card := by
    intro κ hκ
    rw [hcardeq κ hκ]
    exact hblock (qElem Q κ) (qElem_mem Q κ (by rw [hℓ_def] at hκ; exact hκ))
  obtain ⟨S, hSS', hSblock⟩ := exists_thinned_bl S' m ℓ ⌈T⌉₊ hblk
  refine ⟨S, hSS', ?_⟩
  intro γ hγ
  exact hSblock γ hγ

/-- **HARD STEP (counting — Steps 0–4).** There is a component set `Q ⊆ [p)` of
size `ℓ` such that every chosen component `γ ∈ Q` contains at least `⌈T⌉₊` rows of
`R` in its block. -/
theorem balancing_exists_good_Q
    (m p : ℕ) (R : Finset ℕ) (hR : R ⊆ Finset.range (m * p))
    (T : ℝ) (hT0 : 0 ≤ T) (hTm : T < m) (hRT : (p : ℝ) * T ≤ (R.card : ℝ))
    (ℓ : ℕ)
    (hℓ : (ℓ : ℝ) = ⌈(p : ℝ) * (1 - (1 - (R.card : ℝ) / ((p : ℝ) * (m : ℝ)))
                  / (1 - T / (m : ℝ)))⌉₊) :
    ∃ Q : Finset ℕ, Q ⊆ Finset.range p ∧ Q.card = ℓ ∧
      ∀ γ ∈ Q, ⌈T⌉₊ ≤ (R.filter (fun i => m * γ ≤ i ∧ i < m * (γ + 1))).card := by
  classical
  -- m ≥ 1.
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso; rw [h] at hTm; simp at hTm; linarith
    · exact h
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hmT : (0 : ℝ) < (m : ℝ) - T := by linarith
  -- per-block count of R.
  set blkC : ℕ → ℕ := fun γ => (R.filter (fun i => m * γ ≤ i ∧ i < m * (γ + 1))).card with hblkC
  -- GOOD set uses the real threshold `T < blkC γ`; BAD set is `blkC γ ≤ T`.
  set good : Finset ℕ := (Finset.range p).filter (fun γ => (T : ℝ) < (blkC γ : ℝ)) with hgood_def
  set bad : Finset ℕ := (Finset.range p).filter (fun γ => ¬ ((T : ℝ) < (blkC γ : ℝ))) with hbad_def
  have hRcard : R.card ≤ m * p := by
    have := Finset.card_le_card hR; rwa [Finset.card_range] at this
  -- each block of R has ≤ m elements.
  have hblkC_le : ∀ γ, blkC γ ≤ m := by
    intro γ
    rw [hblkC]; simp only
    have hsub : R.filter (fun i => m * γ ≤ i ∧ i < m * (γ + 1))
        ⊆ Finset.Ico (m * γ) (m * (γ + 1)) := by
      intro x hx; rw [Finset.mem_filter] at hx; rw [Finset.mem_Ico]; exact hx.2
    calc (R.filter (fun i => m * γ ≤ i ∧ i < m * (γ + 1))).card
        ≤ (Finset.Ico (m * γ) (m * (γ + 1))).card := Finset.card_le_card hsub
      _ = m := by
            rw [Nat.card_Ico]
            have h : m * (γ + 1) = m * γ + m := by ring
            omega
  -- ∑ blkC over [p) = |R| (blocks partition [0,m*p) and R ⊆ that).
  have hsum_blocks : ∑ γ ∈ Finset.range p, blkC γ = R.card := by
    rw [hblkC]
    simp only
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
      constructor
      · rintro ⟨γ, _, hxr, _, _⟩; exact hxr
      · intro hxr
        have hxrng := hR hxr
        rw [Finset.mem_range] at hxrng
        refine ⟨x / m, ?_, hxr, ?_, ?_⟩
        · rw [Nat.div_lt_iff_lt_mul (by omega : 0 < m), Nat.mul_comm]; exact hxrng
        · exact Nat.mul_div_le x m
        · have : x % m < m := Nat.mod_lt _ (by omega)
          calc x = m * (x/m) + x % m := (Nat.div_add_mod x m).symm
            _ < m * (x/m) + m := by omega
            _ = m * (x/m + 1) := by ring
    · intro a _ b _ hab
      simp only [Finset.disjoint_left, Finset.mem_filter]
      rintro x ⟨_, hax, hbx⟩ ⟨_, hcx, hdx⟩
      have e1 : x / m = a := Nat.div_eq_of_lt_le
        (by rw [Nat.mul_comm]; exact hax) (by rw [Nat.mul_comm]; exact hbx)
      have e2 : x / m = b := Nat.div_eq_of_lt_le
        (by rw [Nat.mul_comm]; exact hcx) (by rw [Nat.mul_comm]; exact hdx)
      exact hab (by omega)
  -- |good| + |bad| = p.
  have hgb : good.card + bad.card = p := by
    rw [hgood_def, hbad_def, Finset.card_filter_add_card_filter_not, Finset.card_range]
  -- key real inequality: m*p − |R| ≥ |bad| * (m − T).
  -- Work with real-valued sum of (m − blkC γ).
  have hmiss_sum : (∑ γ ∈ Finset.range p, ((m : ℝ) - (blkC γ : ℝ)))
      = (m : ℝ) * p - (R.card : ℝ) := by
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (∑ γ ∈ Finset.range p, (blkC γ : ℝ)) = (R.card : ℝ) := by
      rw [← Nat.cast_sum, hsum_blocks]
    rw [this]; ring
  -- term-wise: for γ ∈ bad, (m − blkC γ) ≥ (m − T) ≥ 0 ; for γ ∈ good, (m − blkC γ) ≥ 0.
  have hbad_term : ∀ γ ∈ bad, (m : ℝ) - T ≤ (m : ℝ) - (blkC γ : ℝ) := by
    intro γ hγ
    rw [hbad_def, Finset.mem_filter] at hγ
    have : (blkC γ : ℝ) ≤ T := not_lt.mp hγ.2
    linarith
  have hall_nonneg : ∀ γ ∈ Finset.range p, (0 : ℝ) ≤ (m : ℝ) - (blkC γ : ℝ) := by
    intro γ _
    have := hblkC_le γ
    have : (blkC γ : ℝ) ≤ (m : ℝ) := by exact_mod_cast this
    linarith
  -- sum over bad ≤ sum over all.
  have hbad_sub : bad ⊆ Finset.range p := Finset.filter_subset _ _
  have hsum_ge : (bad.card : ℝ) * ((m : ℝ) - T)
      ≤ ∑ γ ∈ Finset.range p, ((m : ℝ) - (blkC γ : ℝ)) := by
    calc (bad.card : ℝ) * ((m : ℝ) - T)
        = ∑ _γ ∈ bad, ((m : ℝ) - T) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ γ ∈ bad, ((m : ℝ) - (blkC γ : ℝ)) := Finset.sum_le_sum hbad_term
      _ ≤ ∑ γ ∈ Finset.range p, ((m : ℝ) - (blkC γ : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hbad_sub
              (fun γ hγ _ => hall_nonneg γ hγ)
  -- thus |bad| ≤ (m*p − |R|)/(m − T).
  have hbad_le : (bad.card : ℝ) ≤ ((m : ℝ) * p - (R.card : ℝ)) / ((m : ℝ) - T) := by
    rw [le_div_iff₀ hmT]
    calc (bad.card : ℝ) * ((m : ℝ) - T)
        ≤ ∑ γ ∈ Finset.range p, ((m : ℝ) - (blkC γ : ℝ)) := hsum_ge
      _ = (m : ℝ) * p - (R.card : ℝ) := hmiss_sum
  -- ℓ ≤ p − |bad| = |good|.
  have hℓnat : ℓ = ⌈(p : ℝ) * (1 - (1 - (R.card : ℝ) / ((p : ℝ) * (m : ℝ)))
                  / (1 - T / (m : ℝ)))⌉₊ := by exact_mod_cast hℓ
  -- the ceiling argument equals (|R| − pT)/(m − T).
  have hℓ_le_good : ℓ ≤ good.card := by
    -- |good| = p − |bad| (as naturals via hgb).
    have hgood_eq : good.card = p - bad.card := by omega
    -- show ℓ ≤ p − |bad|.
    rw [hgood_eq, hℓnat]
    -- bound the ceiling argument by (p − |bad| : ℝ).
    apply Nat.ceil_le.mpr
    have hbadlep : bad.card ≤ p := by omega
    rcases Nat.eq_zero_or_pos p with hp0 | hp0
    · subst hp0
      simp only [Nat.cast_zero, zero_mul]
      have : bad.card = 0 := by omega
      rw [this]; simp
    · have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
      -- algebraic rewrite of the ceiling argument.
      have hkey : (p : ℝ) * (1 - (1 - (R.card : ℝ) / ((p : ℝ) * (m : ℝ)))
                  / (1 - T / (m : ℝ)))
          = (p : ℝ) - ((m : ℝ) * p - (R.card : ℝ)) / ((m : ℝ) - T) := by
        have h1m : (1 : ℝ) - T / (m : ℝ) = ((m : ℝ) - T) / (m : ℝ) := by
          field_simp
        have hmTne : (m : ℝ) - T ≠ 0 := ne_of_gt hmT
        have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
        have hpne : (p : ℝ) ≠ 0 := ne_of_gt hpR
        rw [h1m]
        field_simp
      rw [hkey]
      -- (p − |bad|) cast.
      have hcast : ((p - bad.card : ℕ) : ℝ) = (p : ℝ) - (bad.card : ℝ) := by
        rw [Nat.cast_sub hbadlep]
      rw [hcast]
      linarith [hbad_le]
  -- choose Q ⊆ good with |Q| = ℓ.
  obtain ⟨Q, hQsub, hQcard⟩ := Finset.exists_subset_card_eq hℓ_le_good
  refine ⟨Q, ?_, hQcard, ?_⟩
  · exact subset_trans hQsub (Finset.filter_subset _ _)
  · intro γ hγ
    have hγgood := hQsub hγ
    rw [hgood_def, Finset.mem_filter] at hγgood
    have hgt : (T : ℝ) < (blkC γ : ℝ) := hγgood.2
    -- ⌈T⌉₊ ≤ blkC γ from T < blkC γ.
    rw [hblkC] at hgt
    simp only at hgt ⊢
    -- T ≤ (blkC γ) ⟹ ⌈T⌉₊ ≤ ⌈blkC γ⌉₊ = blkC γ.
    have hle : T ≤ ((R.filter (fun i => m * γ ≤ i ∧ i < m * (γ + 1))).card : ℝ) := le_of_lt hgt
    calc ⌈T⌉₊ ≤ ⌈((R.filter (fun i => m * γ ≤ i ∧ i < m * (γ + 1))).card : ℝ)⌉₊ :=
          Nat.ceil_le_ceil hle
      _ = (R.filter (fun i => m * γ ≤ i ∧ i < m * (γ + 1))).card := Nat.ceil_natCast _

/-- The digit shift: `digit c n (γ+1) = digit (c/n) n γ`. -/
theorem digit_shift (c n γ : ℕ) : digit c n (γ + 1) = digit (c / n) n γ := by
  unfold digit
  rw [pow_succ, mul_comm (n ^ γ) n, ← Nat.div_div_eq_div_mul]

/-- Base-`n` reconstruction: `c = ∑_{γ<p} digit c n γ * n^γ` when `c < n^p`. -/
theorem digit_recompose (n : ℕ) (hn : 0 < n) :
    ∀ (p c : ℕ), c < n ^ p → (∑ γ ∈ Finset.range p, digit c n γ * n ^ γ) = c := by
  intro p
  induction p with
  | zero =>
    intro c hc
    simp only [pow_zero, Nat.lt_one_iff] at hc
    simp [hc]
  | succ k ih =>
    intro c hc
    rw [Finset.sum_range_succ']
    have hshift : ∀ γ, digit c n (γ + 1) * n ^ (γ + 1)
        = (digit (c / n) n γ * n ^ γ) * n := by
      intro γ
      rw [digit_shift, pow_succ]; ring
    rw [Finset.sum_congr rfl (fun γ _ => hshift γ)]
    rw [← Finset.sum_mul]
    have hcn : c / n < n ^ k := by
      rw [Nat.div_lt_iff_lt_mul hn]
      rw [show n ^ k * n = n ^ (k + 1) by rw [pow_succ]]
      exact hc
    rw [ih (c / n) hcn]
    unfold digit
    simp only [pow_zero, Nat.div_one, mul_one]
    rw [Nat.div_add_mod']

/-- **HARD STEP (column fibre count — Step 6).** `|D| ≥ |C| / n^{p − ℓ}`. -/
theorem balancing_column_bound
    (R C : Finset ℕ) (m n p : ℕ) (Q : Finset ℕ) (hQne : Q ≠ ∅)
    (hC : C ⊆ Finset.range (n ^ p)) (hQ : Q ⊆ Finset.range p)
    (ℓ : ℕ) (hℓ : Q.card = ℓ) :
    ((qProjection R C m n p Q).2.card : ℝ) ≥ (C.card : ℝ) / (n : ℝ) ^ (p - ℓ) := by
  classical
  -- ℓ ≤ p (Q ⊆ range p).
  have hℓp : ℓ ≤ p := by
    rw [← hℓ]
    calc Q.card ≤ (Finset.range p).card := Finset.card_le_card hQ
      _ = p := Finset.card_range p
  -- p > 0 since Q nonempty.
  have hQnonempty : Q.Nonempty := Finset.nonempty_iff_ne_empty.mpr hQne
  obtain ⟨q0, hq0⟩ := hQnonempty
  have hp_pos : 0 < p := by
    have := hQ hq0; rw [Finset.mem_range] at this; omega
  -- D as image of gD over C.
  set gD : ℕ → ℕ := fun c => ∑ γ ∈ Finset.range ℓ, digit c n (qElem Q γ) * n ^ γ with hgD_def
  have hD_eq : (qProjection R C m n p Q).2 = C.image gD := by
    unfold qProjection
    simp only [hQne, if_false, hgD_def, hℓ]
  -- It suffices to show |C| ≤ |D| * n^(p-ℓ).
  rcases Finset.eq_empty_or_nonempty C with hCe | hCne
  · -- C = ∅ : RHS = 0.
    subst hCe
    simp only [Finset.card_empty, Nat.cast_zero]
    rw [ge_iff_le, zero_div]
    exact Nat.cast_nonneg _
  · -- C nonempty ⟹ some c ∈ C ⊆ range (n^p) ⟹ n^p > 0 ⟹ n > 0.
    obtain ⟨c0, hc0⟩ := hCne
    have hc0lt : c0 < n ^ p := by have := hC hc0; rwa [Finset.mem_range] at this
    have hnp_pos : 0 < n ^ p := Nat.pos_of_ne_zero (by rintro h; rw [h] at hc0lt; omega)
    have hn : 0 < n := by
      by_contra h
      have : n = 0 := by omega
      rw [this, Nat.zero_pow hp_pos] at hnp_pos; omega
    -- The complement Qc = (range p) \ Q.
    set Qc : Finset ℕ := (Finset.range p) \ Q with hQc_def
    have hQc_card : Qc.card = p - ℓ := by
      have hsub : Q ⊆ Finset.range p := hQ
      rw [hQc_def, Finset.card_sdiff_of_subset hsub, Finset.card_range, hℓ]
    -- complement packing.
    set gC : ℕ → ℕ := fun c => ∑ j ∈ Finset.range (p - ℓ), digit c n (qElem Qc j) * n ^ j with hgC_def
    -- gC c < n^(p-ℓ).
    have hgC_lt : ∀ c, gC c < n ^ (p - ℓ) := by
      intro c
      rw [hgC_def]
      apply digsum_lt n (p - ℓ) _ hn
      intro j _; unfold digit; exact Nat.mod_lt _ hn
    -- Fibre bound via card_le_mul_card_image: each fibre {c ∈ C | gD c = b} has ≤ n^(p-ℓ) elements.
    -- We bound the fibre by injecting via gC into range (n^(p-ℓ)).
    have hfibre : ∀ b ∈ C.image gD, {c ∈ C | gD c = b}.card ≤ n ^ (p - ℓ) := by
      intro b _
      -- inject the fibre into range (n^(p-ℓ)) via gC.
      have hmaps : ∀ c ∈ {c ∈ C | gD c = b}, gC c ∈ Finset.range (n ^ (p - ℓ)) := by
        intro c _; rw [Finset.mem_range]; exact hgC_lt c
      have hinj : ∀ c1 ∈ {c ∈ C | gD c = b}, ∀ c2 ∈ {c ∈ C | gD c = b},
          gC c1 = gC c2 → c1 = c2 := by
        intro c1 hc1 c2 hc2 hgceq
        simp only [Finset.mem_filter] at hc1 hc2
        have hc1lt : c1 < n ^ p := by have := hC hc1.1; rwa [Finset.mem_range] at this
        have hc2lt : c2 < n ^ p := by have := hC hc2.1; rwa [Finset.mem_range] at this
        -- gD c1 = gD c2 = b.
        have hgdeq : gD c1 = gD c2 := by rw [hc1.2, hc2.2]
        -- digits agree at every position γ < p.
        have hdigeq : ∀ γ, γ < p → digit c1 n γ = digit c2 n γ := by
          intro γ hγ
          by_cases hγQ : γ ∈ Q
          · -- γ = qElem Q β for some β < ℓ.
            obtain ⟨β, hβ, hβeq⟩ : ∃ β, β < ℓ ∧ γ = qElem Q β := by
              refine ⟨(posOf Q γ hγQ).val, ?_, ?_⟩
              · have h2 := (posOf Q γ hγQ).2; omega
              · rw [qElem_eq_orderEmbOfFin Q (posOf Q γ hγQ).val (posOf Q γ hγQ).2,
                  show (⟨(posOf Q γ hγQ).val, (posOf Q γ hγQ).2⟩ : Fin Q.card) = posOf Q γ hγQ from rfl,
                  orderEmbOfFin_posOf]
            have hbnd : ∀ γ', γ' < ℓ → digit c1 n (qElem Q γ') < n :=
              fun γ' _ => by unfold digit; exact Nat.mod_lt _ hn
            have hbnd2 : ∀ γ', γ' < ℓ → digit c2 n (qElem Q γ') < n :=
              fun γ' _ => by unfold digit; exact Nat.mod_lt _ hn
            -- extract digit β of gD c1 / gD c2.
            have e1 : digit (gD c1) n β = digit c1 n (qElem Q β) := by
              unfold digit; rw [hgD_def]
              exact digit_extract n ℓ β (fun γ' => digit c1 n (qElem Q γ')) hn hβ hbnd
            have e2 : digit (gD c2) n β = digit c2 n (qElem Q β) := by
              unfold digit; rw [hgD_def]
              exact digit_extract n ℓ β (fun γ' => digit c2 n (qElem Q γ')) hn hβ hbnd2
            rw [hβeq, ← e1, ← e2, hgdeq]
          · -- γ ∈ Qc.
            have hγQc : γ ∈ Qc := by rw [hQc_def, Finset.mem_sdiff]; exact ⟨Finset.mem_range.mpr hγ, hγQ⟩
            obtain ⟨j, hj, hjeq⟩ : ∃ j, j < p - ℓ ∧ γ = qElem Qc j := by
              refine ⟨(posOf Qc γ hγQc).val, ?_, ?_⟩
              · have h2 := (posOf Qc γ hγQc).2; omega
              · rw [qElem_eq_orderEmbOfFin Qc (posOf Qc γ hγQc).val (posOf Qc γ hγQc).2,
                  show (⟨(posOf Qc γ hγQc).val, (posOf Qc γ hγQc).2⟩ : Fin Qc.card) = posOf Qc γ hγQc from rfl,
                  orderEmbOfFin_posOf]
            have hbnd : ∀ j', j' < p - ℓ → digit c1 n (qElem Qc j') < n :=
              fun j' _ => by unfold digit; exact Nat.mod_lt _ hn
            have hbnd2 : ∀ j', j' < p - ℓ → digit c2 n (qElem Qc j') < n :=
              fun j' _ => by unfold digit; exact Nat.mod_lt _ hn
            have e1 : digit (gC c1) n j = digit c1 n (qElem Qc j) := by
              unfold digit; rw [hgC_def]
              exact digit_extract n (p - ℓ) j (fun j' => digit c1 n (qElem Qc j')) hn hj hbnd
            have e2 : digit (gC c2) n j = digit c2 n (qElem Qc j) := by
              unfold digit; rw [hgC_def]
              exact digit_extract n (p - ℓ) j (fun j' => digit c2 n (qElem Qc j')) hn hj hbnd2
            rw [hjeq, ← e1, ← e2, hgceq]
        -- recompose.
        have r1 : (∑ γ ∈ Finset.range p, digit c1 n γ * n ^ γ) = c1 :=
          digit_recompose n hn p c1 hc1lt
        have r2 : (∑ γ ∈ Finset.range p, digit c2 n γ * n ^ γ) = c2 :=
          digit_recompose n hn p c2 hc2lt
        rw [← r1, ← r2]
        apply Finset.sum_congr rfl
        intro γ hγ
        rw [Finset.mem_range] at hγ
        rw [hdigeq γ hγ]
      -- fibre injects into range (n^(p-ℓ)).
      calc {c ∈ C | gD c = b}.card
          ≤ (Finset.range (n ^ (p - ℓ))).card :=
            Finset.card_le_card_of_injOn gC hmaps (fun c1 hc1 c2 hc2 h =>
              hinj c1 hc1 c2 hc2 h)
        _ = n ^ (p - ℓ) := Finset.card_range _
    -- Apply card_le_mul_card_image.
    have hCle : C.card ≤ n ^ (p - ℓ) * (C.image gD).card :=
      Finset.card_le_mul_card_image C (n ^ (p - ℓ)) hfibre
    -- translate to the real division goal.
    rw [hD_eq, ge_iff_le, div_le_iff₀ (by positivity)]
    have hCleR : (C.card : ℝ) ≤ ((C.image gD).card : ℝ) * (n : ℝ) ^ (p - ℓ) := by
      have : (C.card : ℝ) ≤ ((n ^ (p - ℓ) * (C.image gD).card : ℕ) : ℝ) := by exact_mod_cast hCle
      rw [Nat.cast_mul] at this
      push_cast at this ⊢
      nlinarith [this]
    linarith [hCleR]

/-- Lemma 3.20 (Balancing Lemma).
For any `m × n` matrix `A`, positive integer `p`, selections `R ⊆ [m·p)`, `C ⊆ [n^p)`,
and any real `0 ≤ T < m` with `p·T ≤ |R|`, there exist `ℓ`, `S ⊆ [m·ℓ)`, `D ⊆ [n^ℓ)` with
`ℓ = ⌈ p·(1 − (1 − |R|/(p·m))/(1 − T/m)) ⌉`, such that `S` is `m,T,ℓ`-equipartitioned
whenever `ℓ ≥ 1`, `|D| ≥ |C| / n^{p-ℓ}`, and `ε(⟨A⟩^ℓ, S, D) ⊑ ε(⟨A⟩^p, R, C)`. -/
theorem balancing_lemma
    (A : BoolMat) (p : ℕ)
    (R C : Finset ℕ)
    (hR : R ⊆ Finset.range (A.m * p))
    (hC : C ⊆ Finset.range (A.n ^ p))
    (T : ℝ) (hT0 : 0 ≤ T) (hTm : T < A.m)
    (hRT : (p : ℝ) * T ≤ (R.card : ℝ)) :
    ∃ (ℓ : ℕ) (S D : Finset ℕ),
      S ⊆ Finset.range (A.m * ℓ) ∧ D ⊆ Finset.range (A.n ^ ℓ) ∧
      (ℓ : ℝ) = ⌈(p : ℝ) * (1 - (1 - (R.card : ℝ) / ((p : ℝ) * (A.m : ℝ)))
                  / (1 - T / (A.m : ℝ)))⌉₊ ∧
      (1 ≤ ℓ → IsEquipartitioned S A.m T ℓ) ∧
      (D.card : ℝ) ≥ (C.card : ℝ) / (A.n : ℝ) ^ (p - ℓ) ∧
      IsSubgame (extract (interlace A ℓ) S D) (extract (interlace A p) R C) := by
  classical
  set m := A.m with hm_def
  set n := A.n with hn_def
  set ℓ : ℕ := ⌈(p : ℝ) * (1 - (1 - (R.card : ℝ) / ((p : ℝ) * (m : ℝ)))
                  / (1 - T / (m : ℝ)))⌉₊ with hℓ_def
  have hℓcast : (ℓ : ℝ) = ⌈(p : ℝ) * (1 - (1 - (R.card : ℝ) / ((p : ℝ) * (m : ℝ)))
                  / (1 - T / (m : ℝ)))⌉₊ := by rw [hℓ_def]
  have hRcard : R.card ≤ m * p := by
    have := Finset.card_le_card hR; rwa [Finset.card_range] at this
  have hTm' : T < (m : ℝ) := by rw [hm_def]; exact hTm
  have hℓp : ℓ ≤ p := balancing_ell_le_p m p R hRcard T hT0 hTm' ℓ hℓcast
  by_cases hℓ0 : ℓ = 0
  · -- Degenerate case ℓ = 0.
    rcases Finset.eq_empty_or_nonempty C with hCe | hCne
    · refine ⟨0, ∅, ∅, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · rw [hℓ0]
      · intro h; omega
      · subst hCe; simp
      · refine ⟨fun i => (Fin.cast (by simp) i).elim0, fun j => (Fin.cast (by subst hCe; simp) j).elim0,
          ?_, ?_, ?_⟩
        · intro i; exact (Fin.cast (by simp) i).elim0
        · intro j; exact (Fin.cast (by subst hCe; simp) j).elim0
        · intro i; exact (Fin.cast (by simp) i).elim0
    · refine ⟨0, ∅, {0}, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · rw [pow_zero]; simp
      · rw [hℓ0]
      · intro h; omega
      · simp only [Finset.card_singleton, Nat.cast_one]
        rw [Nat.sub_zero]
        have hCle : C.card ≤ n ^ p := by
          have := Finset.card_le_card hC
          rwa [Finset.card_range] at this
        have hnp_pos : (0 : ℝ) < (n : ℝ) ^ p := by
          have hcpos : 0 < C.card := Finset.card_pos.mpr hCne
          have : 0 < n ^ p := lt_of_lt_of_le hcpos hCle
          exact_mod_cast this
        rw [ge_iff_le, div_le_one hnp_pos]
        calc (C.card : ℝ) ≤ (n ^ p : ℕ) := by exact_mod_cast hCle
          _ = (n : ℝ) ^ p := by push_cast; ring
      · have hCcard : 0 < C.card := Finset.card_pos.mpr hCne
        refine subgame_zero_rows_bl _ _ (by simp) (fun j => ⟨0, hCcard⟩) ?_
        intro j j' _
        have hjlt : (j : ℕ) < 1 := by have := j.2; simpa using this
        have hj'lt : (j' : ℕ) < 1 := by have := j'.2; simpa using this
        exact Fin.ext (by omega)
  · -- Main case ℓ ≥ 1.
    have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr hℓ0
    obtain ⟨Q, hQrange, hQcard, hQblock⟩ :=
      balancing_exists_good_Q m p R hR T hT0 hTm' hRT ℓ hℓcast
    have hQne : Q ≠ ∅ := by
      rw [← Finset.nonempty_iff_ne_empty, ← Finset.card_pos, hQcard]; omega
    have hQnonempty : Q.Nonempty := Finset.nonempty_iff_ne_empty.mpr hQne
    set S' := (qProjection R C m n p Q).1 with hS'_def
    set D := (qProjection R C m n p Q).2 with hD_def
    obtain ⟨S, hSsub, hSeq⟩ :=
      balancing_exists_equipartition R C m n p Q hQne T (fun γ hγ => hQblock γ hγ)
    rw [hQcard] at hSeq
    have hproj := projection_lemma A p R C hR hC Q hQrange hQnonempty
    rw [← hm_def, ← hn_def, hQcard] at hproj
    have hcolbound := balancing_column_bound R C m n p Q hQne hC hQrange ℓ hQcard
    rw [← hD_def] at hcolbound
    refine ⟨ℓ, S, D, ?_, ?_, hℓcast, ?_, ?_, ?_⟩
    · refine subset_trans hSsub ?_
      rw [← hQcard]
      exact qProjection_S_subset_range_bl R C m n p Q
    · rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · have hp_pos : 0 < p := by
          have := hQrange (Finset.nonempty_iff_ne_empty.mpr hQne |>.choose_spec)
          rw [Finset.mem_range] at this; omega
        have hCe : C = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro c hc
          have := hC hc
          rw [Finset.mem_range] at this
          simp [hn0, hp_pos.ne'] at this
        have hDe : D = ∅ := by
          rw [hD_def]; unfold qProjection
          simp only [hQne, if_false, hCe]
          simp
        rw [hDe]; simp
      · rw [hD_def, ← hQcard]
        exact qProjection_D_subset_range_bl R C m n p Q hnpos
    · intro _; rw [hm_def]; exact hSeq
    · exact hcolbound
    · have hrowsub := row_subset_subgame_bl (interlace A ℓ) S S' D hSsub
      exact subgame_trans_bl hrowsub hproj

/-- Transitivity of the subgame relation. -/
theorem subgame_trans {X Y Z : BoolMat} (h1 : IsSubgame X Y) (h2 : IsSubgame Y Z) :
    IsSubgame X Z := by
  obtain ⟨r1, c1, hr1, hc1, he1⟩ := h1
  obtain ⟨r2, c2, hr2, hc2, he2⟩ := h2
  refine ⟨r2 ∘ r1, c2 ∘ c1, hr2.comp hr1, hc2.comp hc1, ?_⟩
  intro i j
  rw [he1 i j, he2 (r1 i) (c1 j)]
  rfl

/-- Row-subset subgame: if `S ⊆ S'`, then extracting on rows `S` is a subgame
of extracting on rows `S'` (same matrix, same columns). -/
theorem row_subset_subgame (M : BoolMat) (S S' D : Finset ℕ) (hSS : S ⊆ S') :
    IsSubgame (extract M S D) (extract M S' D) := by
  classical
  have hmem : ∀ i : Fin S.card, S.orderEmbOfFin rfl i ∈ S' :=
    fun i => hSS (S.orderEmbOfFin_mem rfl i)
  set r : Fin (extract M S D).m → Fin (extract M S' D).m :=
    fun i => posOf S' (S.orderEmbOfFin rfl i) (hmem i) with hr_def
  refine ⟨r, fun j => j, ?_, fun j j' h => h, ?_⟩
  · intro i i' hii
    rw [hr_def] at hii
    simp only at hii
    have hval : S.orderEmbOfFin rfl i = S.orderEmbOfFin rfl i' :=
      posOf_inj S' _ _ (hmem i) (hmem i') hii
    exact (S.orderEmbOfFin rfl).injective hval
  · intro i j
    have hSval : (S.sort (· ≤ ·)).getD (i : ℕ) 0 = S.orderEmbOfFin rfl i :=
      sortGetD_eq_orderEmbOfFin S i
    have hS'val : (S'.sort (· ≤ ·)).getD ((r i) : ℕ) 0 = S.orderEmbOfFin rfl i := by
      rw [sortGetD_eq_orderEmbOfFin S' (r i)]
      rw [hr_def]; simp only
      rw [orderEmbOfFin_posOf]
    show (extract M S D).e i j = (extract M S' D).e (r i) j
    have hrow : (S.sort (· ≤ ·)).getD (i : ℕ) 0 = (S'.sort (· ≤ ·)).getD ((r i) : ℕ) 0 := by
      rw [hSval, hS'val]
    show (let rr := (S.sort (· ≤ ·)).getD (i : ℕ) 0
          let cc := (D.sort (· ≤ ·)).getD (j : ℕ) 0
          if h : rr < M.m ∧ cc < M.n then M.e ⟨rr, h.1⟩ ⟨cc, h.2⟩ else false)
        = (let rr := (S'.sort (· ≤ ·)).getD ((r i) : ℕ) 0
           let cc := (D.sort (· ≤ ·)).getD (j : ℕ) 0
           if h : rr < M.m ∧ cc < M.n then M.e ⟨rr, h.1⟩ ⟨cc, h.2⟩ else false)
    simp only
    rw [hrow]

/-- Per-block thinning: given a finset `S'` whose every block `[m*κ, m*(κ+1))`
(for `κ < ℓ`) contains at least `k` elements, there is a subset `S ⊆ S'` whose
every block contains exactly `k` elements. -/
theorem exists_thinned (S' : Finset ℕ) (m ℓ k : ℕ)
    (hblk : ∀ κ < ℓ, k ≤ (S'.filter (fun i => m * κ ≤ i ∧ i < m * (κ+1))).card) :
    ∃ S : Finset ℕ, S ⊆ S' ∧
      ∀ κ < ℓ, (S.filter (fun i => m * κ ≤ i ∧ i < m * (κ+1))).card = k := by
  classical
  have hchoose : ∀ κ, ∃ t : Finset ℕ,
      t ⊆ S'.filter (fun i => m * κ ≤ i ∧ i < m * (κ+1)) ∧
        (κ < ℓ → t.card = k) := by
    intro κ
    by_cases hκ : κ < ℓ
    · obtain ⟨t, hsub, hcard⟩ := Finset.exists_subset_card_eq (hblk κ hκ)
      exact ⟨t, hsub, fun _ => hcard⟩
    · exact ⟨∅, Finset.empty_subset _, fun h => absurd h hκ⟩
  choose ch hch1 hch2 using hchoose
  refine ⟨(Finset.range ℓ).biUnion ch, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨κ, _, hxκ⟩ := hx
    have := hch1 κ hxκ
    rw [Finset.mem_filter] at this
    exact this.1
  · intro κ₀ hκ₀
    have heq : ((Finset.range ℓ).biUnion ch).filter (fun i => m * κ₀ ≤ i ∧ i < m * (κ₀+1))
        = ch κ₀ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
      constructor
      · rintro ⟨⟨κ, hκ, hxκ⟩, hlo, hhi⟩
        have hmemκ := hch1 κ hxκ
        rw [Finset.mem_filter] at hmemκ
        obtain ⟨_, hlo', hhi'⟩ := hmemκ
        have hκκ₀ : κ = κ₀ := by
          rcases Nat.eq_zero_or_pos m with hm0 | hmpos
          · subst hm0; simp at hhi
          · have e1 : x / m = κ := Nat.div_eq_of_lt_le
              (by rw [Nat.mul_comm]; exact hlo') (by rw [Nat.mul_comm]; exact hhi')
            have e2 : x / m = κ₀ := Nat.div_eq_of_lt_le
              (by rw [Nat.mul_comm]; exact hlo) (by rw [Nat.mul_comm]; exact hhi)
            omega
        rw [← hκκ₀]; exact hxκ
      · intro hx
        have hmemκ := hch1 κ₀ hx
        rw [Finset.mem_filter] at hmemκ
        obtain ⟨_, hlo, hhi⟩ := hmemκ
        exact ⟨⟨κ₀, hκ₀, hx⟩, hlo, hhi⟩
    rw [heq]; exact hch2 κ₀ hκ₀

/-- Helper for Lemma 3.21 (row-thinning + subgame). Given a non-empty index set
`Q ⊆ [0,p)` whose `Q`-projection row set `S'` has, in each of its `|Q|` target
blocks, at least `⌈T/2⌉₊` rows (stated here via the original component blocks of
`R'` indexed by `qElem Q γ`), there is a thinned subset `S ⊆ S'` that is
`m, T/2, |Q|`-equipartitioned and whose extracted subgame still embeds in the
parent game `ε(⟨A⟩^p, R', C)`.

This packages the paper's "choose an `m,⌈T/2⌉,ℓᵢ`-equipartitioned subset `Sᵢ ⊆ Sᵢ'`
then apply Lemma 3.16" step: the block re-indexing of the `Q`-projection, the
per-block thinning to exactly `⌈T/2⌉₊` rows, the rank-embedding subgame
`ε(⟨A⟩^{|Q|}, S, D) ⊑ ε(⟨A⟩^{|Q|}, S', D)`, and its composition with the
Projection Lemma (3.16) by transitivity of `⊑`. -/
theorem thinned_projection_subgame
    (A : BoolMat) (p : ℕ) (T : ℝ)
    (R' C : Finset ℕ)
    (hR' : R' ⊆ Finset.range (A.m * p))
    (hC : C ⊆ Finset.range (A.n ^ p))
    (Q : Finset ℕ) (hQ : Q ⊆ Finset.range p) (hQne : Q.Nonempty)
    (hblock : ∀ γ < Q.card,
      ⌈T / 2⌉₊ ≤ (R'.filter (fun i =>
        A.m * qElem Q γ ≤ i ∧ i < A.m * (qElem Q γ + 1))).card) :
    ∃ S : Finset ℕ, S ⊆ Finset.range (A.m * Q.card) ∧
      (qProjection R' C A.m A.n p Q).2 ⊆ Finset.range (A.n ^ Q.card) ∧
      IsEquipartitioned S A.m (T / 2) Q.card ∧
      IsSubgame (extract (interlace A Q.card) S (qProjection R' C A.m A.n p Q).2)
        (extract (interlace A p) R' C) := by
  classical
  set m := A.m with hm_def
  set n := A.n with hn_def
  set ℓ := Q.card with hℓ_def
  set k := ⌈T / 2⌉₊ with hk_def
  have hQemp : Q ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hQne
  set S' := (qProjection R' C m n p Q).1 with hS'_def
  set D := (qProjection R' C m n p Q).2 with hD_def
  -- p > 0
  obtain ⟨q0, hq0⟩ := hQne
  have hp_pos : 0 < p := by
    have := hQ hq0; rw [Finset.mem_range] at this; omega
  -- block-card equality: S'-block κ ↔ R'-block (qElem Q κ).
  have hcardeq : ∀ κ < ℓ,
      (S'.filter (fun i => m * κ ≤ i ∧ i < m * (κ + 1))).card
        = (R'.filter (fun i => m * qElem Q κ ≤ i ∧ i < m * (qElem Q κ + 1))).card := by
    intro κ hκ
    set q := qElem Q κ with hq_def
    have hκℓ : κ < Q.card := by rw [← hℓ_def]; exact hκ
    apply Finset.card_nbij'
      (i := fun x => m * q + x % m)
      (j := fun y => m * κ + y % m)
    · -- MapsTo : S'-block → R'-block
      intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx ⊢
      obtain ⟨hxS, hxlo, hxhi⟩ := hx
      rw [hS'_def] at hxS
      obtain ⟨hdiv, hmod, hRmem, hdecomp⟩ := S_mem_char R' C m n p Q hQemp x hxS
      have hxdivκ : x / m = κ :=
        Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact hxlo) (by rw [Nat.mul_comm]; exact hxhi)
      have hqsucc : m * (q + 1) = m * q + m := by ring
      refine ⟨?_, ?_, ?_⟩
      · rw [hxdivκ] at hRmem; rw [← hq_def] at hRmem; exact hRmem
      · exact Nat.le_add_right _ _
      · rw [hqsucc]; have : x % m < m := hmod; omega
    · -- MapsTo : R'-block → S'-block
      intro y hy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hy ⊢
      obtain ⟨hyR, hylo, hyhi⟩ := hy
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · exfalso; rw [h] at hylo hyhi; omega
        · exact h
      have hymod : y % m < m := Nat.mod_lt _ hm_pos
      have hydiv : y / m = q :=
        Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact hylo) (by rw [Nat.mul_comm]; exact hyhi)
      have hydecomp : y = m * q + y % m := by
        conv_lhs => rw [← Nat.div_add_mod y m, hydiv]
      have hκsucc : m * (κ + 1) = m * κ + m := by ring
      refine ⟨?_, ?_, ?_⟩
      · rw [hS'_def]
        exact S_mem_of R' C m n p Q hQemp κ (y % m) hκℓ hymod
          (by rw [← hq_def, ← hydecomp]; exact hyR)
      · exact Nat.le_add_right _ _
      · rw [hκsucc]; omega
    · -- LeftInvOn
      intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
      obtain ⟨hxS, hxlo, hxhi⟩ := hx
      rw [hS'_def] at hxS
      obtain ⟨hdiv, hmod, hRmem, hdecomp⟩ := S_mem_char R' C m n p Q hQemp x hxS
      have hxdivκ : x / m = κ :=
        Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact hxlo) (by rw [Nat.mul_comm]; exact hxhi)
      simp only
      rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hmod]
      conv_rhs => rw [hdecomp, hxdivκ]
    · -- RightInvOn
      intro y hy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hy
      obtain ⟨hyR, hylo, hyhi⟩ := hy
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · exfalso; rw [h] at hylo hyhi; omega
        · exact h
      have hymod : y % m < m := Nat.mod_lt _ hm_pos
      have hydiv : y / m = q :=
        Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact hylo) (by rw [Nat.mul_comm]; exact hyhi)
      have hydecomp : y = m * q + y % m := by
        conv_lhs => rw [← Nat.div_add_mod y m, hydiv]
      simp only
      rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hymod]
      rw [← hydecomp]
  -- each S'-block has ≥ k elements.
  have hblk : ∀ κ < ℓ, k ≤ (S'.filter (fun i => m * κ ≤ i ∧ i < m * (κ + 1))).card := by
    intro κ hκ
    rw [hcardeq κ hκ]
    rw [hk_def]; rw [hm_def]
    exact hblock κ hκ
  -- n positivity helper used for the D-range bound (in the nonempty C / nonempty Q regime).
  -- S' ⊆ range (m*ℓ).
  have hS'range : S' ⊆ Finset.range (m * ℓ) := by
    intro x hx
    rw [hS'_def] at hx
    obtain ⟨hdiv, hmod, _, hdecomp⟩ := S_mem_char R' C m n p Q hQemp x hx
    rw [← hℓ_def] at hdiv
    rw [Finset.mem_range]
    calc x = m * (x / m) + x % m := hdecomp
      _ < m * (x / m) + m := by omega
      _ = m * (x / m + 1) := by ring
      _ ≤ m * ℓ := Nat.mul_le_mul_left _ (by omega)
  -- D ⊆ range (n^ℓ).
  have hDrange : D ⊆ Finset.range (n ^ ℓ) := by
    intro d hd
    rw [hD_def] at hd
    obtain ⟨c, hcmem, hceq⟩ := D_mem_witness R' C m n p Q hQemp d hd
    rw [Finset.mem_range]
    by_cases hn0 : n = 0
    · exfalso
      have := hC hcmem
      rw [Finset.mem_range, hn0, Nat.zero_pow hp_pos] at this
      omega
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      rw [hceq, ← hℓ_def]
      exact digsum_lt n ℓ _ hnpos (fun γ _ => by unfold digit; exact Nat.mod_lt _ hnpos)
  -- thin S' to S.
  obtain ⟨S, hSS', hSblock⟩ := exists_thinned S' m ℓ k hblk
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · -- S ⊆ range (m*ℓ) via S ⊆ S' ⊆ range (m*ℓ).
    exact fun x hx => hS'range (hSS' hx)
  · -- D ⊆ range (n^ℓ).
    exact hDrange
  · -- equipartition: each block of S has exactly ⌈T/2⌉₊ elements.
    intro γ hγ
    have hb := hSblock γ hγ
    rw [hm_def] at hb
    rw [hb, hk_def]
  · -- subgame via transitivity: S ⊆ S', projection_lemma.
    have hQne' : Q.Nonempty := ⟨q0, hq0⟩
    have hrow : IsSubgame (extract (interlace A ℓ) S D) (extract (interlace A ℓ) S' D) :=
      row_subset_subgame (interlace A ℓ) S S' D hSS'
    have hproj : IsSubgame (extract (interlace A ℓ) S' D) (extract (interlace A p) R' C) := by
      have hpl := projection_lemma A p R' C hR' hC Q hQ hQne'
      rw [← hℓ_def, ← hS'_def, ← hD_def] at hpl
      exact hpl
    exact subgame_trans hrow hproj

theorem digit_lt (c n q : ℕ) (hn : 0 < n) : digit c n q < n := by
  unfold digit; exact Nat.mod_lt _ hn

/-- The base-`n` digit-graph of a column `c` over component range `[0,p)`:
the set of pairs `(b_γ, γ)` recording each digit. -/
def colGraph (n p c : ℕ) : Finset (Fin n × Fin p) :=
  Finset.univ.filter (fun z : Fin n × Fin p => z.1.val = digit c n z.2.val)

/-- Helper for Lemma 3.21 (column bound, projected-family side). The number of
distinct `Q`-restricted digit-graphs of columns of `C` is at most the number of
distinct `Q`-projected column values. This is the bijection between the
projected family `F_Q` and the column set `D` of the `Q`-projection (the
base-`n` digit reconstruction). -/
theorem proj_image_card_le
    (m n p : ℕ) (R' C : Finset ℕ) (hn : 0 < n)
    (Q : Finset ℕ) (hQ : Q ⊆ Finset.range p) :
    (((C.image (colGraph n p)).image
        (fun S => S.filter (fun z => (z.2 : Fin p).val ∈ Q))).card)
      ≤ (qProjection R' C m n p Q).2.card := by
  classical
  by_cases hQe : Q = ∅
  · -- Q = ∅ : D = {0} so card 1; F_Q is at most a singleton.
    subst hQe
    have hD : (qProjection R' C m n p ∅).2.card = 1 := by
      unfold qProjection; simp
    rw [hD]
    -- the inner image: each filtered graph keeps z with z.2.val ∈ ∅, i.e. ∅.
    have hcollapse : (C.image (colGraph n p)).image
        (fun S => S.filter (fun z => (z.2 : Fin p).val ∈ (∅ : Finset ℕ)))
          ⊆ {∅} := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨S, _, hSeq⟩ := hx
      rw [Finset.mem_singleton, ← hSeq]
      rw [Finset.filter_eq_empty_iff]
      intro z _
      simp
    calc _ ≤ ({∅} : Finset (Finset (Fin n × Fin p))).card := Finset.card_le_card hcollapse
      _ = 1 := by simp
  · -- Q ≠ ∅ : factor both sides through the reconstruction.
    set ℓ := Q.card with hℓ_def
    have hℓpos : 0 < ℓ := by
      rw [hℓ_def, Finset.card_pos]; exact Finset.nonempty_iff_ne_empty.mpr hQe
    -- digit bound helper.
    have hdigit_lt : ∀ c q, digit c n q < n := fun c q => by
      unfold digit; exact Nat.mod_lt _ hn
    -- qElem of Q lands in [0,p).
    have hqElem_lt_p : ∀ γ, γ < ℓ → qElem Q γ < p := by
      intro γ hγ; exact qElem_lt_p Q p γ hQ hγ
    -- membership characterization of Q via qElem positions.
    have hQ_qElem : ∀ x : ℕ, x ∈ Q ↔ ∃ γ, γ < ℓ ∧ x = qElem Q γ := by
      intro x
      constructor
      · intro hx
        refine ⟨(posOf Q x hx).val, ?_, ?_⟩
        · exact lt_of_lt_of_eq (posOf Q x hx).2 hℓ_def.symm
        · rw [qElem_eq_orderEmbOfFin Q (posOf Q x hx).val (posOf Q x hx).2]
          rw [show (⟨(posOf Q x hx).val, (posOf Q x hx).2⟩ : Fin Q.card)
                = posOf Q x hx from rfl]
          rw [orderEmbOfFin_posOf]
      · rintro ⟨γ, hγ, rfl⟩
        exact qElem_mem Q γ (by rw [hℓ_def] at hγ; exact hγ)
    -- reconstruction map.
    set Ψ : ℕ → Finset (Fin n × Fin p) :=
      fun d => (Finset.range ℓ).image
        (fun γ => (⟨digit d n γ % n, Nat.mod_lt _ hn⟩,
                   ⟨qElem Q γ % p, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) (hqElem_lt_p 0 hℓpos))⟩))
        with hΨ_def
    -- gD : D-element for column c.
    set gD : ℕ → ℕ :=
      fun c => ∑ γ ∈ Finset.range ℓ, digit c n (qElem Q γ) * n ^ γ with hgD_def
    -- gQ : filtered graph for column c.
    set gQ : ℕ → Finset (Fin n × Fin p) :=
      fun c => (colGraph n p c).filter (fun z => (z.2 : Fin p).val ∈ Q) with hgQ_def
    have hp_pos : 0 < p := lt_of_le_of_lt (Nat.zero_le _) (hqElem_lt_p 0 hℓpos)
    -- D = C.image gD.
    have hD_eq : (qProjection R' C m n p Q).2 = C.image gD := by
      unfold qProjection
      simp only [hQe, if_false, hgD_def, hℓ_def]
    -- F_Q = C.image gQ.
    have hFQ_eq : (C.image (colGraph n p)).image
        (fun S => S.filter (fun z => (z.2 : Fin p).val ∈ Q)) = C.image gQ := by
      rw [Finset.image_image]; rfl
    -- per-column reconstruction: gQ c = Ψ (gD c).
    have hrecon : ∀ c ∈ C, gQ c = Ψ (gD c) := by
      intro c hc
      have hdig : ∀ γ, γ < ℓ → digit (gD c) n γ = digit c n (qElem Q γ) := by
        intro γ hγ
        unfold digit
        rw [hgD_def]
        have hbnd : ∀ γ', γ' < ℓ → digit c n (qElem Q γ') < n :=
          fun γ' _ => hdigit_lt c (qElem Q γ')
        exact digit_extract n ℓ γ (fun γ' => digit c n (qElem Q γ')) hn hγ hbnd
      rw [hgQ_def, hΨ_def]
      simp only [colGraph]
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_range, Prod.ext_iff, Fin.ext_iff]
      constructor
      · rintro ⟨hz1, hz2⟩
        have hz2' : (z.2 : Fin p).val ∈ Q := hz2
        obtain ⟨γ, hγ, hγeq⟩ := (hQ_qElem z.2.val).mp hz2'
        refine ⟨γ, hγ, ?_, ?_⟩
        · rw [hdig γ hγ, ← hγeq, hz1, Nat.mod_eq_of_lt (hdigit_lt c z.2.val)]
        · rw [← hγeq, Nat.mod_eq_of_lt z.2.2]
      · rintro ⟨γ, hγ, hz1, hz2⟩
        have hqlt : qElem Q γ < p := hqElem_lt_p γ hγ
        rw [Nat.mod_eq_of_lt hqlt] at hz2
        refine ⟨?_, ?_⟩
        · rw [← hz1, hdig γ hγ, Nat.mod_eq_of_lt (hdigit_lt c (qElem Q γ)), hz2]
        · show (z.2 : Fin p).val ∈ Q
          rw [← hz2]; exact (hQ_qElem _).mpr ⟨γ, hγ, rfl⟩
    rw [hFQ_eq, hD_eq]
    have hcongr : C.image gQ = C.image (Ψ ∘ gD) := by
      apply Finset.image_congr
      intro c hc; rw [Finset.mem_coe] at hc; exact hrecon c hc
    rw [hcongr, ← Finset.image_image]
    exact Finset.card_image_le

/-- Helper for Lemma 3.21 (column bound). The product of the column-set
cardinalities of the `Q₁`- and `Q₂`-projections is at least `|C|`, where
`Q₁, Q₂` partition `[0,p)`. This is the Product Theorem 3.14 (Chung 1986) with
`k = 1`, applied to the base-`n` digit-graph encoding of the columns. -/
theorem product_column_bound
    (A : BoolMat) (p : ℕ)
    (R₁ R₂ C : Finset ℕ)
    (hC : C ⊆ Finset.range (A.n ^ p))
    (Q₁ Q₂ : Finset ℕ)
    (hQ1 : Q₁ ⊆ Finset.range p) (hQ2 : Q₂ ⊆ Finset.range p)
    (hpart : Q₁ ∪ Q₂ = Finset.range p) (hdisj : Disjoint Q₁ Q₂) :
    (qProjection R₁ C A.m A.n p Q₁).2.card *
      (qProjection R₂ C A.m A.n p Q₂).2.card ≥ C.card := by
  classical
  set n := A.n with hn_def
  set m := A.m with hm_def
  -- Edge case p = 0 ⟹ Q₁ = Q₂ = ∅, both D = {0}, and C ⊆ {0}.
  by_cases hp0 : p = 0
  · subst hp0
    have hQ1e : Q₁ = ∅ := by
      have := hQ1; rw [Finset.range_zero, Finset.subset_empty] at this; exact this
    have hQ2e : Q₂ = ∅ := by
      have := hQ2; rw [Finset.range_zero, Finset.subset_empty] at this; exact this
    have hD1 : (qProjection R₁ C m n 0 Q₁).2.card = 1 := by
      rw [hQ1e]; unfold qProjection; simp
    have hD2 : (qProjection R₂ C m n 0 Q₂).2.card = 1 := by
      rw [hQ2e]; unfold qProjection; simp
    have hCle : C.card ≤ 1 := by
      have hsub : C ⊆ {0} := by
        intro c hc
        have := hC hc
        rw [Finset.mem_range, pow_zero] at this
        simp only [Finset.mem_singleton]; omega
      calc C.card ≤ ({0} : Finset ℕ).card := Finset.card_le_card hsub
        _ = 1 := by simp
    rw [hD1, hD2]; omega
  -- Edge case n = 0 (and p > 0) ⟹ C = ∅.
  by_cases hn0 : n = 0
  · have hCempty : C = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro c hc
      have hcr := hC hc
      rw [Finset.mem_range, hn0] at hcr
      rw [Nat.zero_pow (by omega)] at hcr; omega
    rw [hCempty]; simp
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    -- The digit-graph encoding.
    set f : ℕ → Finset (Fin n × Fin p) := colGraph n p with hf_def
    set F : Finset (Finset (Fin n × Fin p)) := C.image f with hF_def
    -- |F| = |C| : f is injective on C.
    have hf_inj : Set.InjOn f ↑C := by
      intro c hc c' hc' hcc'
      rw [Finset.mem_coe] at hc hc'
      have hclt : c < n ^ p := by
        have := hC hc; rwa [Finset.mem_range] at this
      have hc'lt : c' < n ^ p := by
        have := hC hc'; rwa [Finset.mem_range] at this
      have hdigit_lt : ∀ d q, digit d n q < n := fun d q => by
        unfold digit; exact Nat.mod_lt _ hn
      have hdigeq : ∀ γ, γ < p → digit c n γ = digit c' n γ := by
        intro γ hγ
        have hmem : ((⟨digit c n γ, hdigit_lt c γ⟩ : Fin n), (⟨γ, hγ⟩ : Fin p)) ∈ f c := by
          rw [hf_def, colGraph]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hcc'] at hmem
        rw [hf_def, colGraph] at hmem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        exact hmem
      have e1 : (∑ γ ∈ Finset.range p, digit c n γ * n ^ γ) = c :=
        digit_recompose n hn p c hclt
      have e2 : (∑ γ ∈ Finset.range p, digit c' n γ * n ^ γ) = c' :=
        digit_recompose n hn p c' hc'lt
      rw [← e1, ← e2]
      apply Finset.sum_congr rfl
      intro γ hγ
      rw [Finset.mem_range] at hγ
      rw [hdigeq γ hγ]
    have hFC : F.card = C.card := by rw [hF_def, Finset.card_image_of_injOn hf_inj]
    -- The two cover sets.
    set Aset : Finset ℕ → Finset (Fin n × Fin p) :=
      fun Q => Finset.univ.filter (fun z : Fin n × Fin p => (z.2 : Fin p).val ∈ Q) with hAset_def
    -- cover: every z lies in at least 1 of (Aset Q₁, Aset Q₂).
    set Av : Fin 2 → Finset (Fin n × Fin p) := ![Aset Q₁, Aset Q₂] with hAv_def
    have hcover : ∀ z : Fin n × Fin p,
        1 ≤ (Finset.univ.filter (fun i => z ∈ Av i)).card := by
      intro z
      have hz : (z.2 : Fin p).val ∈ Finset.range p := by
        rw [Finset.mem_range]; exact z.2.2
      rw [← hpart, Finset.mem_union] at hz
      rcases hz with h | h
      · apply Finset.card_pos.mpr
        refine ⟨0, ?_⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hAv_def]; simp only [Matrix.cons_val_zero]
        rw [hAset_def, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
      · apply Finset.card_pos.mpr
        refine ⟨1, ?_⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        show z ∈ Aset Q₂
        rw [hAset_def, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
    -- Apply product theorem with k = 1.
    have hprod := product_theorem Av 1 Nat.one_pos hcover F
    rw [pow_one] at hprod
    -- expand the product over Fin 2.
    have hprodexp : (∏ i, (F.image (fun x => x ∩ Av i)).card)
        = (F.image (fun x => x ∩ Aset Q₁)).card * (F.image (fun x => x ∩ Aset Q₂)).card := by
      rw [Fin.prod_univ_two]
      rw [hAv_def]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [hprodexp] at hprod
    -- relate F.image(·∩Aset Q) to the projected family used in proj_image_card_le.
    have hbridge : ∀ Q : Finset ℕ,
        (F.image (fun x => x ∩ Aset Q)).card
          = ((C.image (colGraph n p)).image
              (fun S => S.filter (fun z => (z.2 : Fin p).val ∈ Q))).card := by
      intro Q
      congr 1
      rw [hF_def, hf_def, Finset.image_image, Finset.image_image]
      apply Finset.image_congr
      intro x hx
      -- (colGraph n p x) ∩ Aset Q = (colGraph n p x).filter (z.2.val ∈ Q)
      simp only [Function.comp]
      rw [hAset_def]
      ext z
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hbridge Q₁, hbridge Q₂] at hprod
    have h1 := proj_image_card_le m n p R₁ C hn Q₁ hQ1
    have h2 := proj_image_card_le m n p R₂ C hn Q₂ hQ2
    rw [hm_def, hn_def] at h1 h2
    rw [ge_iff_le, ← hFC]
    calc F.card
        ≤ ((C.image (colGraph n p)).image
              (fun S => S.filter (fun z => (z.2 : Fin p).val ∈ Q₁))).card
          * ((C.image (colGraph n p)).image
              (fun S => S.filter (fun z => (z.2 : Fin p).val ∈ Q₂))).card := hprod
      _ ≤ (qProjection R₁ C A.m A.n p Q₁).2.card
          * (qProjection R₂ C A.m A.n p Q₂).2.card :=
            Nat.mul_le_mul h1 h2

/-- Lemma 3.21 (Product of Projections Lemma).
For any `m × n` matrix `A`, positive integer `p`, an `m,T,p`-equipartitioned `R ⊆ [m·p)`,
and `C ⊆ [n^p)`, for any partition `R = R₁ ∪ R₂` we can write `p = ℓ₁ + ℓ₂` such that there
exist `S₁ S₂ ⊆ ...`, `D₁ D₂ ⊆ ...` with `|D₁|·|D₂| ≥ |C|`, and for each `i ∈ {1,2}`:
whenever `ℓᵢ ≥ 1`, `Sᵢ` is `m, T/2, ℓᵢ`-equipartitioned and
`ε(⟨A⟩^{ℓᵢ}, Sᵢ, Dᵢ) ⊑ ε(⟨A⟩^p, Rᵢ, C)`. -/
theorem product_of_projections_lemma
    (A : BoolMat) (p : ℕ) (T : ℝ)
    (R C : Finset ℕ)
    (hR : R ⊆ Finset.range (A.m * p))
    (hRep : IsEquipartitioned R A.m T p)
    (hC : C ⊆ Finset.range (A.n ^ p))
    (R₁ R₂ : Finset ℕ) (hRpart : R₁ ∪ R₂ = R) (hRdisj : Disjoint R₁ R₂) :
    ∃ (ℓ₁ ℓ₂ : ℕ) (S₁ S₂ D₁ D₂ : Finset ℕ),
      ℓ₁ + ℓ₂ = p ∧
      D₁.card * D₂.card ≥ C.card ∧
      (1 ≤ ℓ₁ → S₁ ⊆ Finset.range (A.m * ℓ₁) ∧ D₁ ⊆ Finset.range (A.n ^ ℓ₁) ∧
        IsEquipartitioned S₁ A.m (T / 2) ℓ₁ ∧
        IsSubgame (extract (interlace A ℓ₁) S₁ D₁) (extract (interlace A p) R₁ C)) ∧
      (1 ≤ ℓ₂ → S₂ ⊆ Finset.range (A.m * ℓ₂) ∧ D₂ ⊆ Finset.range (A.n ^ ℓ₂) ∧
        IsEquipartitioned S₂ A.m (T / 2) ℓ₂ ∧
        IsSubgame (extract (interlace A ℓ₂) S₂ D₂) (extract (interlace A p) R₂ C)) := by
  classical
  set m := A.m with hm_def
  -- the per-block count of a set `X` at component `γ`.
  set bc : Finset ℕ → ℕ → ℕ :=
    fun X γ => (X.filter (fun i => m * γ ≤ i ∧ i < m * (γ + 1))).card with hbc_def
  -- the integer ceiling fact `2⌈S/2⌉ ≤ ⌈S⌉ + 1`.
  have hceil : ∀ (S : ℝ), 2 * ⌈S / 2⌉₊ ≤ ⌈S⌉₊ + 1 := by
    intro S
    rcases le_total S 0 with h | h
    · rw [Nat.ceil_eq_zero.mpr (by linarith : S / 2 ≤ 0), Nat.ceil_eq_zero.mpr h]; omega
    · have h1 : (S : ℝ) ≤ ⌈S⌉₊ := Nat.le_ceil S
      have h2 : (⌈S / 2⌉₊ : ℝ) < S / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
      have hlt : (2 * ⌈S / 2⌉₊ : ℝ) < (⌈S⌉₊ : ℝ) + 2 := by push_cast; nlinarith
      have hnat : 2 * ⌈S / 2⌉₊ < ⌈S⌉₊ + 2 := by exact_mod_cast hlt
      omega
  -- block additivity from the disjoint partition `R = R₁ ∪ R₂`.
  have hadd : ∀ q < p, bc R₁ q + bc R₂ q = ⌈T⌉₊ := by
    intro q hq
    rw [hbc_def]
    simp only
    rw [← hRep q hq, ← hRpart, Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hRdisj)]
  -- the component split.
  set Q₁ : Finset ℕ := (Finset.range p).filter (fun γ => ⌈T⌉₊ ≤ 2 * bc R₁ γ) with hQ1_def
  set Q₂ : Finset ℕ := (Finset.range p).filter (fun γ => ¬ (⌈T⌉₊ ≤ 2 * bc R₁ γ)) with hQ2_def
  set ℓ₁ := Q₁.card with hℓ1_def
  set ℓ₂ := Q₂.card with hℓ2_def
  -- Q₁, Q₂ subsets of range p.
  have hQ1sub : Q₁ ⊆ Finset.range p := Finset.filter_subset _ _
  have hQ2sub : Q₂ ⊆ Finset.range p := Finset.filter_subset _ _
  -- Q₁, Q₂ partition range p.
  have hpartQ : Q₁ ∪ Q₂ = Finset.range p := by
    rw [hQ1_def, hQ2_def, Finset.filter_union_filter_not_eq]
  have hdisjQ : Disjoint Q₁ Q₂ := by
    rw [hQ1_def, hQ2_def]; exact Finset.disjoint_filter_filter_not _ _ _
  -- ℓ₁ + ℓ₂ = p.
  have hℓsum : ℓ₁ + ℓ₂ = p := by
    rw [hℓ1_def, hℓ2_def, hQ1_def, hQ2_def, Finset.card_filter_add_card_filter_not,
      Finset.card_range]
  -- the column sets.
  set D₁ := (qProjection R₁ C m A.n p Q₁).2 with hD1_def
  set D₂ := (qProjection R₂ C m A.n p Q₂).2 with hD2_def
  -- helper: membership of a component `q := qElem Qᵢ γ` in `Qᵢ` gives `q < p`
  -- and the relevant block-count condition; we package the per-block hypotheses
  -- for `thinned_projection_subgame`.
  -- R₁, R₂ subsets of range (m*p).
  have hR1sub : R₁ ⊆ Finset.range (m * p) := by
    rw [hm_def]; intro x hx; exact hR (hRpart ▸ Finset.mem_union_left _ hx)
  have hR2sub : R₂ ⊆ Finset.range (m * p) := by
    rw [hm_def]; intro x hx; exact hR (hRpart ▸ Finset.mem_union_right _ hx)
  -- per-block bound for Q₁.
  have hblock1 : Q₁.Nonempty → ∀ γ < Q₁.card,
      ⌈T / 2⌉₊ ≤ (R₁.filter (fun i =>
        m * qElem Q₁ γ ≤ i ∧ i < m * (qElem Q₁ γ + 1))).card := by
    intro _ γ hγ
    have hcond : ⌈T⌉₊ ≤ 2 * bc R₁ (qElem Q₁ γ) := by
      have hqmem : qElem Q₁ γ ∈ Q₁ := qElem_mem Q₁ γ hγ
      rw [hQ1_def, Finset.mem_filter] at hqmem
      exact hqmem.2
    have hb := hceil T
    have hgoal : ⌈T / 2⌉₊ ≤ bc R₁ (qElem Q₁ γ) := by omega
    rw [hbc_def] at hgoal
    exact hgoal
  -- per-block bound for Q₂.
  have hblock2 : Q₂.Nonempty → ∀ γ < Q₂.card,
      ⌈T / 2⌉₊ ≤ (R₂.filter (fun i =>
        m * qElem Q₂ γ ≤ i ∧ i < m * (qElem Q₂ γ + 1))).card := by
    intro _ γ hγ
    have hqmem : qElem Q₂ γ ∈ Q₂ := qElem_mem Q₂ γ hγ
    have hcond : ¬ (⌈T⌉₊ ≤ 2 * bc R₁ (qElem Q₂ γ)) := by
      have h := hqmem
      rw [hQ2_def, Finset.mem_filter] at h
      exact h.2
    have hqrng : qElem Q₂ γ < p := by
      have := hQ2sub hqmem; rwa [Finset.mem_range] at this
    have hc1 : 2 * bc R₁ (qElem Q₂ γ) < ⌈T⌉₊ := by omega
    have hsum := hadd (qElem Q₂ γ) hqrng
    have hb := hceil T
    have hgoal : ⌈T / 2⌉₊ ≤ bc R₂ (qElem Q₂ γ) := by omega
    rw [hbc_def] at hgoal
    exact hgoal
  -- now choose S₁ and S₂.
  have hS1ex : ∃ S₁, (1 ≤ ℓ₁ → S₁ ⊆ Finset.range (m * ℓ₁) ∧ D₁ ⊆ Finset.range (A.n ^ ℓ₁) ∧
      IsEquipartitioned S₁ m (T / 2) ℓ₁ ∧
      IsSubgame (extract (interlace A ℓ₁) S₁ D₁) (extract (interlace A p) R₁ C)) := by
    by_cases h1 : 1 ≤ ℓ₁
    · have hQ1ne : Q₁.Nonempty := by rw [← Finset.card_pos]; rw [← hℓ1_def]; omega
      obtain ⟨S₁, hSr, hDr, heq, hsub⟩ :=
        thinned_projection_subgame A p T R₁ C hR1sub hC Q₁ hQ1sub hQ1ne
          (hblock1 hQ1ne)
      refine ⟨S₁, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
      · rw [hℓ1_def]; exact hSr
      · rw [hD1_def, hℓ1_def]; exact hDr
      · rw [hℓ1_def]; exact heq
      · rw [hD1_def, hℓ1_def]; exact hsub
    · exact ⟨∅, fun h => absurd h h1⟩
  have hS2ex : ∃ S₂, (1 ≤ ℓ₂ → S₂ ⊆ Finset.range (m * ℓ₂) ∧ D₂ ⊆ Finset.range (A.n ^ ℓ₂) ∧
      IsEquipartitioned S₂ m (T / 2) ℓ₂ ∧
      IsSubgame (extract (interlace A ℓ₂) S₂ D₂) (extract (interlace A p) R₂ C)) := by
    by_cases h2 : 1 ≤ ℓ₂
    · have hQ2ne : Q₂.Nonempty := by rw [← Finset.card_pos]; rw [← hℓ2_def]; omega
      obtain ⟨S₂, hSr, hDr, heq, hsub⟩ :=
        thinned_projection_subgame A p T R₂ C hR2sub hC Q₂ hQ2sub hQ2ne
          (hblock2 hQ2ne)
      refine ⟨S₂, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
      · rw [hℓ2_def]; exact hSr
      · rw [hD2_def, hℓ2_def]; exact hDr
      · rw [hℓ2_def]; exact heq
      · rw [hD2_def, hℓ2_def]; exact hsub
    · exact ⟨∅, fun h => absurd h h2⟩
  obtain ⟨S₁, hS₁⟩ := hS1ex
  obtain ⟨S₂, hS₂⟩ := hS2ex
  -- the column bound.
  have hcol : D₁.card * D₂.card ≥ C.card := by
    rw [hD1_def, hD2_def]
    exact product_column_bound A p R₁ R₂ C hC Q₁ Q₂ hQ1sub hQ2sub hpartQ hdisjQ
  exact ⟨ℓ₁, ℓ₂, S₁, S₂, D₁, D₂, hℓsum, hcol, hS₁, hS₂⟩

/-- Strengthened Product of Projections Lemma: same conclusion as
`product_of_projections_lemma`, but additionally exposes the unconditional card
bounds `|Dᵢ| ≤ n^{ℓᵢ}` (valid even when `ℓᵢ = 0`), which give `yᵢ ≤ 1`.  Requires
`0 < A.n`. -/
theorem product_of_projections_lemma_card
    (A : BoolMat) (p : ℕ) (T : ℝ) (hn : 0 < A.n)
    (R C : Finset ℕ)
    (hR : R ⊆ Finset.range (A.m * p))
    (hRep : IsEquipartitioned R A.m T p)
    (hC : C ⊆ Finset.range (A.n ^ p))
    (R₁ R₂ : Finset ℕ) (hRpart : R₁ ∪ R₂ = R) (hRdisj : Disjoint R₁ R₂) :
    ∃ (ℓ₁ ℓ₂ : ℕ) (S₁ S₂ D₁ D₂ : Finset ℕ),
      ℓ₁ + ℓ₂ = p ∧
      D₁.card * D₂.card ≥ C.card ∧
      D₁.card ≤ A.n ^ ℓ₁ ∧
      D₂.card ≤ A.n ^ ℓ₂ ∧
      (1 ≤ ℓ₁ → S₁ ⊆ Finset.range (A.m * ℓ₁) ∧ D₁ ⊆ Finset.range (A.n ^ ℓ₁) ∧
        IsEquipartitioned S₁ A.m (T / 2) ℓ₁ ∧
        IsSubgame (extract (interlace A ℓ₁) S₁ D₁) (extract (interlace A p) R₁ C)) ∧
      (1 ≤ ℓ₂ → S₂ ⊆ Finset.range (A.m * ℓ₂) ∧ D₂ ⊆ Finset.range (A.n ^ ℓ₂) ∧
        IsEquipartitioned S₂ A.m (T / 2) ℓ₂ ∧
        IsSubgame (extract (interlace A ℓ₂) S₂ D₂) (extract (interlace A p) R₂ C)) := by
  classical
  set m := A.m with hm_def
  set bc : Finset ℕ → ℕ → ℕ :=
    fun X γ => (X.filter (fun i => m * γ ≤ i ∧ i < m * (γ + 1))).card with hbc_def
  have hceil : ∀ (S : ℝ), 2 * ⌈S / 2⌉₊ ≤ ⌈S⌉₊ + 1 := by
    intro S
    rcases le_total S 0 with h | h
    · rw [Nat.ceil_eq_zero.mpr (by linarith : S / 2 ≤ 0), Nat.ceil_eq_zero.mpr h]; omega
    · have h1 : (S : ℝ) ≤ ⌈S⌉₊ := Nat.le_ceil S
      have h2 : (⌈S / 2⌉₊ : ℝ) < S / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
      have hlt : (2 * ⌈S / 2⌉₊ : ℝ) < (⌈S⌉₊ : ℝ) + 2 := by push_cast; nlinarith
      have hnat : 2 * ⌈S / 2⌉₊ < ⌈S⌉₊ + 2 := by exact_mod_cast hlt
      omega
  have hadd : ∀ q < p, bc R₁ q + bc R₂ q = ⌈T⌉₊ := by
    intro q hq
    rw [hbc_def]
    simp only
    rw [← hRep q hq, ← hRpart, Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hRdisj)]
  set Q₁ : Finset ℕ := (Finset.range p).filter (fun γ => ⌈T⌉₊ ≤ 2 * bc R₁ γ) with hQ1_def
  set Q₂ : Finset ℕ := (Finset.range p).filter (fun γ => ¬ (⌈T⌉₊ ≤ 2 * bc R₁ γ)) with hQ2_def
  set ℓ₁ := Q₁.card with hℓ1_def
  set ℓ₂ := Q₂.card with hℓ2_def
  have hQ1sub : Q₁ ⊆ Finset.range p := Finset.filter_subset _ _
  have hQ2sub : Q₂ ⊆ Finset.range p := Finset.filter_subset _ _
  have hpartQ : Q₁ ∪ Q₂ = Finset.range p := by
    rw [hQ1_def, hQ2_def, Finset.filter_union_filter_not_eq]
  have hdisjQ : Disjoint Q₁ Q₂ := by
    rw [hQ1_def, hQ2_def]; exact Finset.disjoint_filter_filter_not _ _ _
  have hℓsum : ℓ₁ + ℓ₂ = p := by
    rw [hℓ1_def, hℓ2_def, hQ1_def, hQ2_def, Finset.card_filter_add_card_filter_not,
      Finset.card_range]
  set D₁ := (qProjection R₁ C m A.n p Q₁).2 with hD1_def
  set D₂ := (qProjection R₂ C m A.n p Q₂).2 with hD2_def
  have hR1sub : R₁ ⊆ Finset.range (m * p) := by
    rw [hm_def]; intro x hx; exact hR (hRpart ▸ Finset.mem_union_left _ hx)
  have hR2sub : R₂ ⊆ Finset.range (m * p) := by
    rw [hm_def]; intro x hx; exact hR (hRpart ▸ Finset.mem_union_right _ hx)
  have hblock1 : Q₁.Nonempty → ∀ γ < Q₁.card,
      ⌈T / 2⌉₊ ≤ (R₁.filter (fun i =>
        m * qElem Q₁ γ ≤ i ∧ i < m * (qElem Q₁ γ + 1))).card := by
    intro _ γ hγ
    have hcond : ⌈T⌉₊ ≤ 2 * bc R₁ (qElem Q₁ γ) := by
      have hqmem : qElem Q₁ γ ∈ Q₁ := qElem_mem Q₁ γ hγ
      rw [hQ1_def, Finset.mem_filter] at hqmem
      exact hqmem.2
    have hb := hceil T
    have hgoal : ⌈T / 2⌉₊ ≤ bc R₁ (qElem Q₁ γ) := by omega
    rw [hbc_def] at hgoal
    exact hgoal
  have hblock2 : Q₂.Nonempty → ∀ γ < Q₂.card,
      ⌈T / 2⌉₊ ≤ (R₂.filter (fun i =>
        m * qElem Q₂ γ ≤ i ∧ i < m * (qElem Q₂ γ + 1))).card := by
    intro _ γ hγ
    have hqmem : qElem Q₂ γ ∈ Q₂ := qElem_mem Q₂ γ hγ
    have hcond : ¬ (⌈T⌉₊ ≤ 2 * bc R₁ (qElem Q₂ γ)) := by
      have h := hqmem
      rw [hQ2_def, Finset.mem_filter] at h
      exact h.2
    have hqrng : qElem Q₂ γ < p := by
      have := hQ2sub hqmem; rwa [Finset.mem_range] at this
    have hc1 : 2 * bc R₁ (qElem Q₂ γ) < ⌈T⌉₊ := by omega
    have hsum := hadd (qElem Q₂ γ) hqrng
    have hb := hceil T
    have hgoal : ⌈T / 2⌉₊ ≤ bc R₂ (qElem Q₂ γ) := by omega
    rw [hbc_def] at hgoal
    exact hgoal
  have hS1ex : ∃ S₁, (1 ≤ ℓ₁ → S₁ ⊆ Finset.range (m * ℓ₁) ∧ D₁ ⊆ Finset.range (A.n ^ ℓ₁) ∧
      IsEquipartitioned S₁ m (T / 2) ℓ₁ ∧
      IsSubgame (extract (interlace A ℓ₁) S₁ D₁) (extract (interlace A p) R₁ C)) := by
    by_cases h1 : 1 ≤ ℓ₁
    · have hQ1ne : Q₁.Nonempty := by rw [← Finset.card_pos]; rw [← hℓ1_def]; omega
      obtain ⟨S₁, hSr, hDr, heq, hsub⟩ :=
        thinned_projection_subgame A p T R₁ C hR1sub hC Q₁ hQ1sub hQ1ne
          (hblock1 hQ1ne)
      refine ⟨S₁, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
      · rw [hℓ1_def]; exact hSr
      · rw [hD1_def, hℓ1_def]; exact hDr
      · rw [hℓ1_def]; exact heq
      · rw [hD1_def, hℓ1_def]; exact hsub
    · exact ⟨∅, fun h => absurd h h1⟩
  have hS2ex : ∃ S₂, (1 ≤ ℓ₂ → S₂ ⊆ Finset.range (m * ℓ₂) ∧ D₂ ⊆ Finset.range (A.n ^ ℓ₂) ∧
      IsEquipartitioned S₂ m (T / 2) ℓ₂ ∧
      IsSubgame (extract (interlace A ℓ₂) S₂ D₂) (extract (interlace A p) R₂ C)) := by
    by_cases h2 : 1 ≤ ℓ₂
    · have hQ2ne : Q₂.Nonempty := by rw [← Finset.card_pos]; rw [← hℓ2_def]; omega
      obtain ⟨S₂, hSr, hDr, heq, hsub⟩ :=
        thinned_projection_subgame A p T R₂ C hR2sub hC Q₂ hQ2sub hQ2ne
          (hblock2 hQ2ne)
      refine ⟨S₂, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
      · rw [hℓ2_def]; exact hSr
      · rw [hD2_def, hℓ2_def]; exact hDr
      · rw [hℓ2_def]; exact heq
      · rw [hD2_def, hℓ2_def]; exact hsub
    · exact ⟨∅, fun h => absurd h h2⟩
  obtain ⟨S₁, hS₁⟩ := hS1ex
  obtain ⟨S₂, hS₂⟩ := hS2ex
  have hcol : D₁.card * D₂.card ≥ C.card := by
    rw [hD1_def, hD2_def]
    exact product_column_bound A p R₁ R₂ C hC Q₁ Q₂ hQ1sub hQ2sub hpartQ hdisjQ
  -- the new card bounds, valid for all ℓᵢ (including 0) via the range containment.
  have hcard1 : D₁.card ≤ A.n ^ ℓ₁ := by
    have hsub : D₁ ⊆ Finset.range (A.n ^ ℓ₁) := by
      rw [hD1_def, hℓ1_def]
      exact qProjection_D_subset_range_bl R₁ C m A.n p Q₁ hn
    calc D₁.card ≤ (Finset.range (A.n ^ ℓ₁)).card := Finset.card_le_card hsub
      _ = A.n ^ ℓ₁ := Finset.card_range _
  have hcard2 : D₂.card ≤ A.n ^ ℓ₂ := by
    have hsub : D₂ ⊆ Finset.range (A.n ^ ℓ₂) := by
      rw [hD2_def, hℓ2_def]
      exact qProjection_D_subset_range_bl R₂ C m A.n p Q₂ hn
    calc D₂.card ≤ (Finset.range (A.n ^ ℓ₂)).card := Finset.card_le_card hsub
      _ = A.n ^ ℓ₂ := Finset.card_range _
  exact ⟨ℓ₁, ℓ₂, S₁, S₂, D₁, D₂, hℓsum, hcol, hcard1, hcard2, hS₁, hS₂⟩

/-- Lemma 3.22 (Maximum Projection Lemma).
For any `m × n` matrix `A`, positive integer `p`, an `m,T,p`-equipartitioned `R ⊆ [m·p)`,
and `C ⊆ [n^p)`, for any integer `1 ≤ ℓ < p` there exist `S ⊆ [m·ℓ)`, `D ⊆ [n^ℓ)` such that
`S` is `m,T,ℓ`-equipartitioned, `|D| ≥ |C|^{ℓ/p}`, and
`ε(⟨A⟩^ℓ, S, D) ⊑ ε(⟨A⟩^p, R, C)`. -/
theorem maximum_projection_lemma
    (A : BoolMat) (p : ℕ) (T : ℝ)
    (R C : Finset ℕ)
    (hR : R ⊆ Finset.range (A.m * p))
    (hRep : IsEquipartitioned R A.m T p)
    (hC : C ⊆ Finset.range (A.n ^ p))
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓp : ℓ < p) :
    ∃ (S D : Finset ℕ),
      S ⊆ Finset.range (A.m * ℓ) ∧
      D ⊆ Finset.range (A.n ^ ℓ) ∧
      IsEquipartitioned S A.m T ℓ ∧
      (D.card : ℝ) ≥ Real.rpow (C.card : ℝ) ((ℓ : ℝ) / (p : ℝ)) ∧
      IsSubgame (extract (interlace A ℓ) S D) (extract (interlace A p) R C) := by
  classical
  set m := A.m with hm_def
  set n := A.n with hn_def
  have hp_pos : 0 < p := lt_of_le_of_lt (le_of_lt hℓ1) hℓp
  -- Step 1-3 isolated: produce a valid Q' with the cardinality bound on D.
  have hclaim : ∃ Q' : Finset ℕ, Q' ⊆ Finset.range p ∧ Q'.card = ℓ ∧
      ((qProjection R C m n p Q').2.card : ℝ) ≥ Real.rpow (C.card : ℝ) ((ℓ : ℝ) / (p : ℝ)) := by
    -- Edge case: n = 0 forces C = ∅ (every c ∈ C has c < n^p = 0).
    by_cases hn0 : n = 0
    · -- C = ∅
      have hCempty : C = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro c hc
        have := hC hc
        rw [Finset.mem_range, hn0, Nat.zero_pow hp_pos] at this
        omega
      -- choose Q' = range ℓ (any ℓ-subset of [p]); D = ∅ so its card is 0;
      -- RHS = 0^{ℓ/p} = 0.
      refine ⟨Finset.range ℓ, ?_, ?_, ?_⟩
      · exact Finset.range_subset_range.mpr (le_of_lt hℓp)
      · exact Finset.card_range ℓ
      · -- D = ∅, RHS = 0^{ℓ/p} = 0.
        have hDcard : (qProjection R C m n p (Finset.range ℓ)).2.card = 0 := by
          rw [hCempty]
          have hrng : (Finset.range ℓ : Finset ℕ) ≠ ∅ := by
            rw [← Finset.nonempty_iff_ne_empty]
            exact ⟨0, Finset.mem_range.mpr hℓ1⟩
          unfold qProjection
          simp only [hrng, if_false, Finset.image_empty, Finset.card_empty]
        have hCcard0 : (C.card : ℝ) = 0 := by rw [hCempty]; simp
        rw [hDcard, hCcard0]
        have hexp : (ℓ : ℝ) / (p : ℝ) ≠ 0 := by
          have : (0:ℝ) < (ℓ:ℝ)/(p:ℝ) := by
            apply div_pos
            · exact_mod_cast hℓ1
            · exact_mod_cast hp_pos
          exact ne_of_gt this
        have hzr : Real.rpow 0 ((ℓ : ℝ) / (p : ℝ)) = 0 := Real.zero_rpow hexp
        rw [hzr]
        norm_num
    · -- n > 0 : the column-graph encoding.
      have hn : 0 < n := Nat.pos_of_ne_zero hn0
      -- Encode each column c as the graph f c ⊆ [n] × [p].
      -- f c = { z : Fin n × Fin p | z.1 = digit c n z.2 }.
      set f : ℕ → Finset (Fin n × Fin p) :=
        fun c => Finset.univ.filter (fun z => z.1.val = digit c n z.2.val) with hf_def
      set F : Finset (Finset (Fin n × Fin p)) := C.image f with hF_def
      -- Apply Corollary 3.19.
      obtain ⟨Q, hQcard, hQbd⟩ := corollary_3_19 F ℓ hℓ1 (le_of_lt hℓp)
      -- The Q' ⊆ ℕ is the value-image of Q.
      set Q' : Finset ℕ := Q.image Fin.val with hQ'eq
      have hQ'card : Q'.card = ℓ := by
        rw [hQ'eq, Finset.card_image_of_injective _ Fin.val_injective, hQcard]
      have hQ'sub : Q' ⊆ Finset.range p := by
        intro x hx
        rw [hQ'eq, Finset.mem_image] at hx
        obtain ⟨q, _, rfl⟩ := hx
        rw [Finset.mem_range]; exact q.2
      -- digit bound and qElem bound helpers
      have hdigit_lt : ∀ c q, digit c n q < n := fun c q => by
        unfold digit; exact Nat.mod_lt _ hn
      have hqElem_lt_p : ∀ γ, γ < ℓ → qElem Q' γ < p := by
        intro γ hγ
        exact qElem_lt_p Q' p γ hQ'sub (by rw [hQ'card]; exact hγ)
      -- Membership in Q' characterised via qElem positions.
      have hQ'_qElem : ∀ x : ℕ, x ∈ Q' ↔ ∃ γ, γ < ℓ ∧ x = qElem Q' γ := by
        intro x
        constructor
        · intro hx
          refine ⟨(posOf Q' x hx).val, ?_, ?_⟩
          · exact lt_of_lt_of_eq (posOf Q' x hx).2 hQ'card
          · rw [qElem_eq_orderEmbOfFin Q' (posOf Q' x hx).val (posOf Q' x hx).2]
            rw [show (⟨(posOf Q' x hx).val, (posOf Q' x hx).2⟩ : Fin Q'.card)
                  = posOf Q' x hx from rfl]
            rw [orderEmbOfFin_posOf]
        · rintro ⟨γ, hγ, rfl⟩
          exact qElem_mem Q' γ (by rw [hQ'card]; exact hγ)
      -- The reconstruction map Ψ : ℕ → Finset (Fin n × Fin p).
      set Ψ : ℕ → Finset (Fin n × Fin p) :=
        fun d => (Finset.range ℓ).image
          (fun γ => (⟨digit d n γ % n, Nat.mod_lt _ hn⟩,
                     ⟨qElem Q' γ % p, Nat.mod_lt _ hp_pos⟩)) with hΨ_def
      -- gD c = the D-element for column c.
      set gD : ℕ → ℕ :=
        fun c => ∑ γ ∈ Finset.range ℓ, digit c n (qElem Q' γ) * n ^ γ with hgD_def
      -- gQ c = filtered graph = (f c).filter (z.2 ∈ Q).
      set gQ : ℕ → Finset (Fin n × Fin p) :=
        fun c => (f c).filter (fun z => z.2 ∈ Q) with hgQ_def
      -- D is exactly C.image gD.
      have hD_eq : (qProjection R C m n p Q').2 = C.image gD := by
        unfold qProjection
        have hQ'ne : Q' ≠ ∅ := by
          rw [← Finset.nonempty_iff_ne_empty, ← Finset.card_pos, hQ'card]; omega
        simp only [hQ'ne, if_false, hgD_def, hQ'card]
      -- F_Q is exactly C.image gQ.
      have hFQ_eq : F.image (fun S => S.filter (fun z => z.2 ∈ Q)) = C.image gQ := by
        rw [hF_def, Finset.image_image]
        rfl
      -- Per-column reconstruction: gQ c = Ψ (gD c) for c ∈ C.
      have hrecon : ∀ c ∈ C, gQ c = Ψ (gD c) := by
        intro c hc
        -- digit of gD c at index γ (< ℓ) equals digit c n (qElem Q' γ).
        have hdig : ∀ γ, γ < ℓ → digit (gD c) n γ = digit c n (qElem Q' γ) := by
          intro γ hγ
          unfold digit
          rw [hgD_def]
          have hbnd : ∀ γ', γ' < ℓ → digit c n (qElem Q' γ') < n :=
            fun γ' _ => hdigit_lt c (qElem Q' γ')
          exact digit_extract n ℓ γ (fun γ' => digit c n (qElem Q' γ')) hn hγ hbnd
        rw [hgQ_def, hΨ_def, hf_def]
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
          Finset.mem_range, Prod.ext_iff, Fin.ext_iff]
        constructor
        · rintro ⟨hz1, hz2⟩
          -- z.2 ∈ Q, so z.2.val ∈ Q', so = qElem Q' γ for some γ < ℓ.
          have hz2' : (z.2 : Fin p).val ∈ Q' := by
            rw [hQ'eq, Finset.mem_image]; exact ⟨z.2, hz2, rfl⟩
          obtain ⟨γ, hγ, hγeq⟩ := (hQ'_qElem z.2.val).mp hz2'
          refine ⟨γ, hγ, ?_, ?_⟩
          · rw [hdig γ hγ, ← hγeq, hz1, Nat.mod_eq_of_lt (hdigit_lt c z.2.val)]
          · rw [← hγeq, Nat.mod_eq_of_lt z.2.2]
        · rintro ⟨γ, hγ, hz1, hz2⟩
          have hqlt : qElem Q' γ < p := hqElem_lt_p γ hγ
          rw [Nat.mod_eq_of_lt hqlt] at hz2
          have hz2mem : z.2 ∈ Q := by
            have hmemQ' : z.2.val ∈ Q' := by
              rw [← hz2]; exact (hQ'_qElem _).mpr ⟨γ, hγ, rfl⟩
            rw [hQ'eq, Finset.mem_image] at hmemQ'
            obtain ⟨q, hq, hqv⟩ := hmemQ'
            have hqz : q = z.2 := Fin.val_injective hqv
            rwa [hqz] at hq
          refine ⟨?_, hz2mem⟩
          rw [← hz1, hdig γ hγ, Nat.mod_eq_of_lt (hdigit_lt c (qElem Q' γ)), hz2]
      -- f is injective on C.
      have hf_inj : Set.InjOn f ↑C := by
        intro c hc c' hc' hcc'
        rw [Finset.mem_coe] at hc hc'
        have hclt : c < n ^ p := by have := hC hc; rwa [Finset.mem_range] at this
        have hc'lt : c' < n ^ p := by have := hC hc'; rwa [Finset.mem_range] at this
        -- digits agree at every position γ < p.
        have hdigeq : ∀ γ, γ < p → digit c n γ = digit c' n γ := by
          intro γ hγ
          have hmem : ((⟨digit c n γ, hdigit_lt c γ⟩ : Fin n), (⟨γ, hγ⟩ : Fin p)) ∈ f c := by
            rw [hf_def]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hcc'] at hmem
          rw [hf_def] at hmem
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
          exact hmem
        -- recompose.
        have e1 : (∑ γ ∈ Finset.range p, digit c n γ * n ^ γ) = c :=
          digit_recompose n hn p c hclt
        have e2 : (∑ γ ∈ Finset.range p, digit c' n γ * n ^ γ) = c' :=
          digit_recompose n hn p c' hc'lt
        rw [← e1, ← e2]
        apply Finset.sum_congr rfl
        intro γ hγ
        rw [Finset.mem_range] at hγ
        rw [hdigeq γ hγ]
      -- Now assemble cardinalities.
      have hFC : F.card = C.card := by
        rw [hF_def, Finset.card_image_of_injOn hf_inj]
      have hFQ_le_D : (F.image (fun S => S.filter (fun z => z.2 ∈ Q))).card
          ≤ (qProjection R C m n p Q').2.card := by
        rw [hFQ_eq, hD_eq]
        -- C.image gQ = (C.image gD).image Ψ
        have hcongr : C.image gQ = C.image (Ψ ∘ gD) := by
          apply Finset.image_congr
          intro c hc; rw [Finset.mem_coe] at hc; exact hrecon c hc
        rw [hcongr, ← Finset.image_image]
        exact Finset.card_image_le
      -- Conclude the bound.
      refine ⟨Q', hQ'sub, hQ'card, ?_⟩
      calc Real.rpow (C.card : ℝ) ((ℓ : ℝ) / (p : ℝ))
          = (C.card : ℝ) ^ ((ℓ : ℝ) / (p : ℝ)) := rfl
        _ = (F.card : ℝ) ^ ((ℓ : ℝ) / (p : ℝ)) := by rw [hFC]
        _ ≤ ((F.image (fun S => S.filter (fun z => z.2 ∈ Q))).card : ℝ) := hQbd
        _ ≤ ((qProjection R C m n p Q').2.card : ℝ) := by exact_mod_cast hFQ_le_D
  obtain ⟨Q', hQ'sub, hQ'card, hQ'bound⟩ := hclaim
  have hQ'ne : Q'.Nonempty := by
    rw [← Finset.card_pos, hQ'card]; omega
  have hQ'emp : Q' ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hQ'ne
  -- The Q'-projection.
  set S := (qProjection R C m n p Q').1 with hS_def
  set D := (qProjection R C m n p Q').2 with hD_def
  refine ⟨S, D, ?_, ?_, ?_, ?_, ?_⟩
  · -- S ⊆ range (m * ℓ)
    intro x hx
    rw [hS_def] at hx
    obtain ⟨hdiv, hmod, _, hdecomp⟩ := S_mem_char R C m n p Q' hQ'emp x hx
    rw [Finset.mem_range]
    rw [hQ'card] at hdiv
    calc x = m * (x / m) + x % m := hdecomp
      _ < m * (x / m) + m := by omega
      _ = m * (x / m + 1) := by ring
      _ ≤ m * ℓ := Nat.mul_le_mul_left _ (by omega)
  · -- D ⊆ range (n ^ ℓ)
    intro d hd
    rw [hD_def] at hd
    obtain ⟨c, hcmem, hceq⟩ := D_mem_witness R C m n p Q' hQ'emp d hd
    rw [Finset.mem_range]
    by_cases hn0 : n = 0
    · -- n = 0 forces C = ∅, contradiction with c ∈ C
      exfalso
      have := hC hcmem
      rw [Finset.mem_range, hn0, Nat.zero_pow hp_pos] at this
      omega
    · have hn : 0 < n := Nat.pos_of_ne_zero hn0
      rw [hceq, hQ'card]
      exact digsum_lt n ℓ _ hn (fun γ _ => digit_lt c n (qElem Q' γ) hn)
  · -- S is m,T,ℓ-equipartitioned
    intro γ₀ hγ₀
    set q := qElem Q' γ₀ with hq_def
    have hγ₀ℓ : γ₀ < Q'.card := by rw [hQ'card]; exact hγ₀
    have hqp : q < p := qElem_lt_p Q' p γ₀ hQ'sub hγ₀ℓ
    -- bijection between the γ₀-block of S and the q-block of R
    have hcardeq :
        (S.filter (fun i => m * γ₀ ≤ i ∧ i < m * (γ₀ + 1))).card
          = (R.filter (fun i => m * q ≤ i ∧ i < m * (q + 1))).card := by
      apply Finset.card_nbij'
        (i := fun x => m * q + x % m)
        (j := fun y => m * γ₀ + y % m)
      · -- MapsTo i : S-block → R-block
        intro x hx
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx ⊢
        obtain ⟨hxS, hxlo, hxhi⟩ := hx
        rw [hS_def] at hxS
        obtain ⟨hdiv, hmod, hRmem, hdecomp⟩ := S_mem_char R C m n p Q' hQ'emp x hxS
        -- within block γ₀ : x / m = γ₀
        have hxdivγ : x / m = γ₀ :=
          Nat.div_eq_of_lt_le (k := γ₀) (n := m) (m := x)
            (by rw [Nat.mul_comm]; exact hxlo) (by rw [Nat.mul_comm]; exact hxhi)
        have hqsucc : m * (q + 1) = m * q + m := by ring
        refine ⟨?_, ?_, ?_⟩
        · rw [hxdivγ] at hRmem; rw [← hq_def] at hRmem; exact hRmem
        · exact Nat.le_add_right _ _
        · rw [hqsucc]; have : x % m < m := hmod; omega
      · -- MapsTo j : R-block → S-block
        intro y hy
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hy ⊢
        obtain ⟨hyR, hylo, hyhi⟩ := hy
        have hm_pos : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h | h
          · exfalso; rw [h] at hylo hyhi; omega
          · exact h
        have hymod : y % m < m := Nat.mod_lt _ hm_pos
        have hydiv : y / m = q :=
          Nat.div_eq_of_lt_le (k := q) (n := m) (m := y)
            (by rw [Nat.mul_comm]; exact hylo) (by rw [Nat.mul_comm]; exact hyhi)
        have hydecomp : y = m * q + y % m := by
          conv_lhs => rw [← Nat.div_add_mod y m, hydiv]
        have hγsucc : m * (γ₀ + 1) = m * γ₀ + m := by ring
        refine ⟨?_, ?_, ?_⟩
        · exact S_mem_of R C m n p Q' hQ'emp γ₀ (y % m) hγ₀ℓ hymod
            (by rw [← hq_def, ← hydecomp]; exact hyR)
        · exact Nat.le_add_right _ _
        · rw [hγsucc]; omega
      · -- LeftInvOn
        intro x hx
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
        obtain ⟨hxS, hxlo, hxhi⟩ := hx
        rw [hS_def] at hxS
        obtain ⟨hdiv, hmod, hRmem, hdecomp⟩ := S_mem_char R C m n p Q' hQ'emp x hxS
        have hxdivγ : x / m = γ₀ :=
          Nat.div_eq_of_lt_le (k := γ₀) (n := m) (m := x)
            (by rw [Nat.mul_comm]; exact hxlo) (by rw [Nat.mul_comm]; exact hxhi)
        simp only
        rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hmod]
        conv_rhs => rw [hdecomp, hxdivγ]
      · -- RightInvOn
        intro y hy
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hy
        obtain ⟨hyR, hylo, hyhi⟩ := hy
        have hm_pos : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h | h
          · exfalso; rw [h] at hylo hyhi; omega
          · exact h
        have hymod : y % m < m := Nat.mod_lt _ hm_pos
        have hydiv : y / m = q :=
          Nat.div_eq_of_lt_le (k := q) (n := m) (m := y)
            (by rw [Nat.mul_comm]; exact hylo) (by rw [Nat.mul_comm]; exact hyhi)
        have hydecomp : y = m * q + y % m := by
          conv_lhs => rw [← Nat.div_add_mod y m, hydiv]
        simp only
        rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hymod]
        rw [← hydecomp]
    rw [hcardeq]
    exact hRep q hqp
  · -- |D| ≥ |C|^{ℓ/p}
    rw [hD_def]; exact hQ'bound
  · -- subgame
    have := projection_lemma A p R C hR hC Q' hQ'sub hQ'ne
    rw [hQ'card] at this
    rw [hS_def, hD_def]
    exact this

end Proof.Projections

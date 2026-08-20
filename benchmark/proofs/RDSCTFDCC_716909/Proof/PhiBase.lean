import Mathlib
import Proof.Types.BoolMat
import Proof.Types.MatComplexity
import Proof.Types.Interlace
import Proof.Types.AlternatingGame
import Proof.Types.Bracket
import Proof.Types.Lambda
import Proof.Projections
import Proof.BracketLemmas
import Proof.Induction
import Proof.Types.Subgame
import Proof.Types.Extract
import Proof.Types.Equipartition
import Proof.Types.QProjection
import Proof.ProofLemmas.SublemmaPrecompNoIncrease
import Proof.LogRankBound

open Proof.Types.BoolMat
open Proof.Types.MatComplexity
open Proof.Types.Interlace
open Proof.Types.AlternatingGame
open Proof.Types.Bracket
open Proof.Types.Lambda
open Proof.Types.Subgame
open Proof.Types.Extract
open Proof.Types.Equipartition
open Proof.Types.QProjection
open Proof.Types.CommComplexity

/-- The paper fixes `k = 10000`. -/
private abbrev kk : ℕ := 10000

/-- The paper fixes `a = 10`. -/
private abbrev aa : ℕ := 10

/-- The paper fixes `B = Q = 255 · 2^{k-8}` with `k = 10000`. -/
private abbrev Q : ℕ := 255 * 2 ^ (10000 - 8)

namespace Proof.PhiBase

/-- Helper: `0 < 2^e` for any real exponent. -/
private lemma rpow2_pos (e : ℝ) : 0 < Real.rpow 2 e :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- Helper: `2^e ≤ 1` when `e ≤ 0`. -/
private lemma rpow2_le_one {e : ℝ} (he : e ≤ 0) : Real.rpow 2 e ≤ 1 := by
  rw [show (1 : ℝ) = Real.rpow 2 0 from (Real.rpow_zero 2).symm]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) he

/-- Helper: `logb 2 (2^e) = e`. -/
private lemma logb2_rpow2 (e : ℝ) : Real.logb 2 (Real.rpow 2 e) = e :=
  Real.logb_rpow (b := 2) (x := e) (by norm_num) (by norm_num)

/-- Helper: `2 ≤ Q` (kept opaque, no numeral blowup). -/
private lemma two_le_Q : (2 : ℕ) ≤ Q := by
  have h : 0 < 2 ^ (10000 - 8) := pow_pos (by norm_num) _
  calc (2 : ℕ) ≤ 255 * 1 := by norm_num
    _ ≤ 255 * 2 ^ (10000 - 8) := Nat.mul_le_mul_left 255 h

private lemma Q_pos : 0 < Q := lt_of_lt_of_le (by norm_num) two_le_Q

/-! ### Structural helpers for the subgame relation -/

/-- Reflexivity of `IsSubgame`. -/
private theorem isSubgame_refl (A : BoolMat) : IsSubgame A A :=
  ⟨id, id, Function.injective_id, Function.injective_id, fun _ _ => rfl⟩

/-- Transitivity of `IsSubgame`. -/
private theorem isSubgame_trans {A B C : BoolMat}
    (h1 : IsSubgame A B) (h2 : IsSubgame B C) : IsSubgame A C := by
  obtain ⟨r1, c1, hr1, hc1, he1⟩ := h1
  obtain ⟨r2, c2, hr2, hc2, he2⟩ := h2
  exact ⟨r2 ∘ r1, c2 ∘ c1, hr2.comp hr1, hc2.comp hc1, fun i j => by
    rw [he1 i j, he2 (r1 i) (c1 j)]; rfl⟩

/-- Entry of `interlace N 1` at valid coords equals `N.e`. -/
private theorem interlace_one_e (N : BoolMat) (a b : ℕ)
    (ha : a < (interlace N 1).m) (hb : b < (interlace N 1).n)
    (ha' : a < N.m) (hb' : b < N.n) :
    (interlace N 1).e ⟨a, ha⟩ ⟨b, hb⟩ = N.e ⟨a, ha'⟩ ⟨b, hb'⟩ := by
  simp only [interlace]
  congr 1 <;> · apply Fin.ext; simp [Nat.mod_eq_of_lt, Nat.div_eq_of_lt, ha', hb']

/-- `extract (interlace N 1) R C` and `extract N R C` are the SAME game. -/
private theorem extract_interlace_one_eq (N : BoolMat) (R C : Finset ℕ) :
    extract (interlace N 1) R C = extract N R C := by
  have he : (extract (interlace N 1) R C).e = (extract N R C).e := by
    funext i j
    simp only [extract]
    set r := (R.sort (· ≤ ·)).getD i.val 0 with hr
    set c := (C.sort (· ≤ ·)).getD j.val 0 with hc
    by_cases h : r < (interlace N 1).m ∧ c < (interlace N 1).n
    · obtain ⟨hrm, hcn⟩ := h
      have hrM : r < N.m := by simpa [interlace] using hrm
      have hcM : c < N.n := by simpa [interlace] using hcn
      rw [dif_pos ⟨hrm, hcn⟩, dif_pos ⟨hrM, hcM⟩]
      exact interlace_one_e N r c hrm hcn hrM hcM
    · have h' : ¬ (r < N.m ∧ c < N.n) := by
        intro ⟨hrM, hcM⟩
        exact h ⟨by simpa [interlace] using hrM, by simpa [interlace] using hcM⟩
      rw [dif_neg h, dif_neg h']
  exact congrArg (fun e => (⟨R.card, C.card, e⟩ : BoolMat)) he

/-- A column-subset is a subgame (keep all rows, take a subset of columns).
If `C' ⊆ C` then `extract A R C' ⊑ extract A R C`. -/
private theorem extract_col_subset_subgame (A : BoolMat) (R C' C : Finset ℕ)
    (hsub : C' ⊆ C) :
    IsSubgame (extract A R C') (extract A R C) := by
  classical
  set sC := C.sort (· ≤ ·) with hsC
  set sC' := C'.sort (· ≤ ·) with hsC'
  -- helper: the k-th smallest element of C' (via getD) is a member of C'.
  have getDmemC' : ∀ k : ℕ, k < sC'.length → sC'.getD k 0 ∈ C' := by
    intro k hk
    have hm : sC'.getD k 0 ∈ sC' := by
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    rw [hsC', Finset.mem_sort] at hm; exact hm
  -- column index map: rank in C of the j-th smallest element of C'.
  have colidx : ∀ j : Fin (extract A R C').n,
      sC.idxOf (sC'.getD j.val 0) < (extract A R C).n := by
    intro j
    have hj : j.val < C'.card := by simpa [extract] using j.isLt
    have hjlen : j.val < sC'.length := by rw [hsC', Finset.length_sort]; exact hj
    have hvmem : sC'.getD j.val 0 ∈ C := hsub (getDmemC' j.val hjlen)
    have hidx : sC.idxOf (sC'.getD j.val 0) < sC.length := by
      rw [List.idxOf_lt_length_iff]
      rw [hsC, Finset.mem_sort]; exact hvmem
    simpa [extract, hsC, Finset.length_sort] using hidx
  refine ⟨fun i => ⟨i.val, by simpa [extract] using i.isLt⟩,
    fun j => ⟨sC.idxOf (sC'.getD j.val 0), colidx j⟩, ?_, ?_, ?_⟩
  · intro i1 i2 h
    apply Fin.ext
    simpa using congrArg Fin.val h
  · intro j1 j2 h
    apply Fin.ext
    have hj1 : j1.val < C'.card := by simpa [extract] using j1.isLt
    have hj2 : j2.val < C'.card := by simpa [extract] using j2.isLt
    have hj1len : j1.val < sC'.length := by rw [hsC', Finset.length_sort]; exact hj1
    have hj2len : j2.val < sC'.length := by rw [hsC', Finset.length_sort]; exact hj2
    have hmem1 : sC'.getD j1.val 0 ∈ sC := by
      rw [hsC, Finset.mem_sort]; exact hsub (getDmemC' j1.val hj1len)
    have hmem2 : sC'.getD j2.val 0 ∈ sC := by
      rw [hsC, Finset.mem_sort]; exact hsub (getDmemC' j2.val hj2len)
    have heq : sC.idxOf (sC'.getD j1.val 0) = sC.idxOf (sC'.getD j2.val 0) := by
      simpa using congrArg Fin.val h
    have hb1 : sC[sC.idxOf (sC'.getD j1.val 0)]? = some (sC'.getD j1.val 0) :=
      List.getElem?_idxOf hmem1
    have hb2 : sC[sC.idxOf (sC'.getD j2.val 0)]? = some (sC'.getD j2.val 0) :=
      List.getElem?_idxOf hmem2
    rw [heq] at hb1
    have hval : sC'.getD j1.val 0 = sC'.getD j2.val 0 := by
      have := hb1.symm.trans hb2
      exact (Option.some.injEq _ _ ▸ this)
    have hnd : sC'.Nodup := by rw [hsC']; exact Finset.sort_nodup _ _
    rw [List.getD_eq_getElem _ _ hj1len, List.getD_eq_getElem _ _ hj2len] at hval
    exact (List.Nodup.getElem_inj_iff hnd).mp hval
  · intro i j
    simp only [extract]
    -- row value matches (same getD i), column value matches (rank reproduces the value).
    have hj : j.val < C'.card := by simpa [extract] using j.isLt
    have hjlen : j.val < sC'.length := by rw [hsC', Finset.length_sort]; exact hj
    have hvmem : sC'.getD j.val 0 ∈ sC := by
      rw [hsC, Finset.mem_sort]; exact hsub (getDmemC' j.val hjlen)
    -- the C-column value selected on the RHS equals sC'.getD j 0
    have hcolval : sC.getD (sC.idxOf (sC'.getD j.val 0)) 0 = sC'.getD j.val 0 := by
      have hidx : sC.idxOf (sC'.getD j.val 0) < sC.length := by
        rw [List.idxOf_lt_length_iff]; exact hvmem
      rw [List.getD_eq_getElem _ _ hidx]
      have hb : sC[sC.idxOf (sC'.getD j.val 0)]? = some (sC'.getD j.val 0) :=
        List.getElem?_idxOf hvmem
      rw [List.getElem?_eq_getElem hidx] at hb
      exact (Option.some.injEq _ _ ▸ hb)
    -- now both dite branches use identical (r, c) data.
    simp only [hsC, hsC'] at hcolval ⊢
    simp only [hcolval]

/-- Local copy of Proposition 3.11 (Subgames Are Easier), to avoid an import
cycle through `Proof.MainTheorem`. -/
private theorem subgames_are_easier (Φ' Φ : Set BoolMat) (hΦ : Φ.Nonempty)
    (h : IsSubgameSet Φ' Φ) : DSet Φ' ≤ DSet Φ := by
  have hcrux : ∀ A B : BoolMat, IsSubgame A B → Dmat A ≤ Dmat B := by
    intro A B hAB
    obtain ⟨r, c, _hr, _hc, hAe⟩ := hAB
    have hfun : A.e = fun i j => B.e (r i) (c j) := by
      funext i j; exact hAe i j
    show D A.e ≤ D B.e
    rw [hfun]
    exact Proof.ProofLemmas.SublemmaPrecompNoIncrease (g := B.e) (α := r) (β := c)
  apply le_csInf
  · obtain ⟨M₀, hM₀⟩ := hΦ
    exact ⟨Dmat M₀, M₀, hM₀, rfl⟩
  · rintro x ⟨M, hM, rfl⟩
    obtain ⟨M', hM', hsub⟩ := h M hM
    have hle : Dmat M' ≤ Dmat M := hcrux M' M hsub
    refine le_trans ?_ hle
    exact Nat.sInf_le ⟨M', hM', rfl⟩

/-! ### Q-projection helpers -/

/-- The γ-th smallest element of a finset (0-indexed) is a member, when in range. -/
private theorem qElem_mem (s : Finset ℕ) (γ : ℕ) (hγ : γ < s.card) : qElem s γ ∈ s := by
  unfold qElem
  have h : γ < (s.sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact hγ
  rw [List.getD_eq_getElem _ _ h]
  have := List.getElem_mem h
  rwa [Finset.mem_sort] at this

/-- For the `m = 1, n = 2` projection with `Q' ⊆ R` nonempty, the projected
row set is `range Q'.card`. -/
private theorem proj_S_eq_range (R C Q' : Finset ℕ) (hQR : Q' ⊆ R) (hne : Q'.Nonempty) (p : ℕ) :
    (qProjection R C 1 2 p Q').1 = Finset.range Q'.card := by
  unfold qProjection
  rw [if_neg (by rw [Finset.nonempty_iff_ne_empty] at hne; exact hne)]
  simp only
  ext a
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, one_mul]
  constructor
  · rintro ⟨⟨γ, r⟩, ⟨hmem, hr⟩, heq⟩
    obtain ⟨hγ, hr1⟩ := Finset.mem_product.mp hmem
    simp only [Finset.mem_range, Nat.lt_one_iff] at hγ hr1
    subst hr1
    simp only [Nat.add_zero] at heq
    omega
  · intro ha
    refine ⟨(a, 0), ⟨?_, ?_⟩, ?_⟩
    · refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · simp only [Finset.mem_range]; exact ha
      · simp only [Finset.mem_range]; norm_num
    · simp only [Nat.add_zero]
      exact hQR (qElem_mem Q' a ha)
    · simp

/-- The projected column set `D` lives in `range (2 ^ Q'.card)`. -/
private theorem proj_D_subset (R C Q' : Finset ℕ) (Qp : ℕ) (hne : Q'.Nonempty) :
    (qProjection R C 1 2 Qp Q').2 ⊆ Finset.range (2 ^ Q'.card) := by
  unfold qProjection
  rw [if_neg (by rw [Finset.nonempty_iff_ne_empty] at hne; exact hne)]
  simp only
  intro d hd
  simp only [Finset.mem_image] at hd
  obtain ⟨c, _, rfl⟩ := hd
  rw [Finset.mem_range]
  -- ∑ γ < q, digit(c,2,·)·2^γ < 2^q since each digit < 2.
  set ℓ := Q'.card with hℓ
  calc ∑ γ ∈ Finset.range ℓ, digit c 2 (qElem Q' γ) * 2 ^ γ
      ≤ ∑ γ ∈ Finset.range ℓ, 1 * 2 ^ γ := by
        apply Finset.sum_le_sum
        intro γ _
        apply Nat.mul_le_mul_right
        unfold digit
        omega
    _ = 2 ^ ℓ - 1 := by
        simp only [one_mul]
        rw [Nat.geomSum_eq (le_refl 2)]
        omega
    _ < 2 ^ ℓ := by
        have : 0 < 2 ^ ℓ := pow_pos (by norm_num) _
        omega

/-- `digit c 2 i < 2`. -/
private lemma digit_lt_two (c i : ℕ) : digit c 2 i < 2 := by
  unfold digit; omega

/-- Base-2 digit-sum uniqueness on `range N`: if two functions with values `< 2`
give the same `∑ γ < N, f γ * 2^γ`, then they agree on `range N`. -/
private lemma digitsum_inj (N : ℕ) (f g : ℕ → ℕ)
    (hf : ∀ γ, f γ < 2) (hg : ∀ γ, g γ < 2)
    (h : ∑ γ ∈ Finset.range N, f γ * 2 ^ γ = ∑ γ ∈ Finset.range N, g γ * 2 ^ γ) :
    ∀ γ < N, f γ = g γ := by
  induction N generalizing f g with
  | zero => intro γ hγ; omega
  | succ N ih =>
    rw [Finset.sum_range_succ' (fun k => f k * 2 ^ k),
        Finset.sum_range_succ' (fun k => g k * 2 ^ k)] at h
    simp only [pow_zero, mul_one, pow_succ] at h
    have hfsum : ∑ x ∈ Finset.range N, f (x + 1) * (2 ^ x * 2)
        = (∑ x ∈ Finset.range N, f (x + 1) * 2 ^ x) * 2 := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro x _; ring
    have hgsum : ∑ x ∈ Finset.range N, g (x + 1) * (2 ^ x * 2)
        = (∑ x ∈ Finset.range N, g (x + 1) * 2 ^ x) * 2 := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro x _; ring
    rw [hfsum, hgsum] at h
    set Sf := ∑ x ∈ Finset.range N, f (x + 1) * 2 ^ x with hSf
    set Sg := ∑ x ∈ Finset.range N, g (x + 1) * 2 ^ x with hSg
    have hf0 := hf 0
    have hg0 := hg 0
    have hf00 : f 0 = g 0 := by omega
    have hSeq : Sf = Sg := by omega
    have hih := ih (fun γ => f (γ + 1)) (fun γ => g (γ + 1))
      (fun γ => hf (γ + 1)) (fun γ => hg (γ + 1)) hSeq
    intro γ hγ
    match γ with
    | 0 => exact hf00
    | (k + 1) =>
      have hk : k < N := by omega
      exact hih k hk

/-- `digit c 2 i = (c.testBit i).toNat`. -/
private lemma digit_eq_testBit (c i : ℕ) : digit c 2 i = (c.testBit i).toNat := by
  rw [Nat.toNat_testBit]; rfl

/-- If `c < 2^Qp` then `digit c 2 i = 0` for `i ≥ Qp`. -/
private lemma digit_high_eq_zero {c Qp i : ℕ} (hc : c < 2 ^ Qp) (hi : Qp ≤ i) :
    digit c 2 i = 0 := by
  unfold digit
  have : c < 2 ^ i := lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hi)
  rw [Nat.div_eq_of_lt this]

/-- Two numbers `< 2^Qp` agreeing on all digits `< Qp` are equal. -/
private lemma eq_of_digits_eq {c c' Qp : ℕ} (hc : c < 2 ^ Qp) (hc' : c' < 2 ^ Qp)
    (h : ∀ i < Qp, digit c 2 i = digit c' 2 i) : c = c' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < Qp
  · have hd := h i hi
    rw [digit_eq_testBit, digit_eq_testBit] at hd
    rcases hb : c.testBit i <;> rcases hb' : c'.testBit i <;>
      simp only [hb, hb', Bool.toNat_true, Bool.toNat_false] at * <;> first | rfl | omega
  · have hi' : Qp ≤ i := not_lt.mp hi
    have h1 : digit c 2 i = 0 := digit_high_eq_zero hc hi'
    have h2 : digit c' 2 i = 0 := digit_high_eq_zero hc' hi'
    rw [digit_eq_testBit] at h1 h2
    rcases hb : c.testBit i <;> rcases hb' : c'.testBit i <;>
      simp only [hb, hb', Bool.toNat_true, Bool.toNat_false] at * <;> first | rfl | omega

/-- Every element of `s` is `qElem s γ` for some `γ < s.card`. -/
private theorem mem_iff_qElem (s : Finset ℕ) (i : ℕ) (hi : i ∈ s) :
    ∃ γ < s.card, qElem s γ = i := by
  unfold qElem
  have hmem : i ∈ s.sort (· ≤ ·) := by rw [Finset.mem_sort]; exact hi
  obtain ⟨γ, hγlen, hget⟩ := List.getElem_of_mem hmem
  refine ⟨γ, ?_, ?_⟩
  · rw [← Finset.length_sort (· ≤ ·)]; exact hγlen
  · rw [List.getD_eq_getElem _ _ hγlen]; exact hget

/-- digit-sum is `< 2^N` (geometric bound). -/
private lemma digitsum_lt (c N : ℕ) (sel : ℕ → ℕ) :
    ∑ γ ∈ Finset.range N, digit c 2 (sel γ) * 2 ^ γ < 2 ^ N := by
  calc ∑ γ ∈ Finset.range N, digit c 2 (sel γ) * 2 ^ γ
      ≤ ∑ γ ∈ Finset.range N, 1 * 2 ^ γ := by
        apply Finset.sum_le_sum; intro γ _
        apply Nat.mul_le_mul_right
        have := digit_lt_two c (sel γ); omega
    _ = 2 ^ N - 1 := by
        simp only [one_mul]; rw [Nat.geomSum_eq (le_refl 2)]; omega
    _ < 2 ^ N := by have : 0 < 2 ^ N := pow_pos (by norm_num) _; omega

private theorem proj_D_card_lb (R C Q' : Finset ℕ) (Qp : ℕ)
    (hQ' : Q' ⊆ Finset.range Qp) (hcard : Q'.card ≤ Qp) (hne : Q'.Nonempty)
    (hC : C ⊆ Finset.range (2 ^ Qp)) :
    C.card ≤ (qProjection R C 1 2 Qp Q').2.card * 2 ^ (Qp - Q'.card) := by
  classical
  set ℓ := Q'.card with hℓ
  have hDeq : (qProjection R C 1 2 Qp Q').2
      = C.image (fun c => ∑ γ ∈ Finset.range ℓ, digit c 2 (qElem Q' γ) * 2 ^ γ) := by
    unfold qProjection
    rw [if_neg (by rw [Finset.nonempty_iff_ne_empty] at hne; exact hne)]
  rw [hDeq]
  set π : ℕ → ℕ := fun c => ∑ γ ∈ Finset.range ℓ, digit c 2 (qElem Q' γ) * 2 ^ γ with hπ
  set Fr := Finset.range Qp \ Q' with hFr
  have hFrcard : Fr.card = Qp - ℓ := by
    rw [hFr, Finset.card_sdiff, Finset.card_range, Finset.inter_eq_left.mpr hQ', hℓ]
  set ψ : ℕ → ℕ := fun c => ∑ j ∈ Finset.range (Qp - ℓ), digit c 2 (qElem Fr j) * 2 ^ j with hψ
  rw [mul_comm]
  apply Finset.card_le_mul_card_image C (2 ^ (Qp - ℓ))
  intro b hb
  set Fib := {a ∈ C | π a = b} with hFib
  have hmaps : Set.MapsTo ψ ↑Fib (↑(Finset.range (2 ^ (Qp - ℓ)))) := by
    intro c hc
    simp only [Finset.coe_range, Set.mem_Iio]
    exact digitsum_lt c (Qp - ℓ) (qElem Fr)
  have hinj : Set.InjOn ψ ↑Fib := by
    intro c hc c' hc' hψeq
    simp only [hFib, Finset.coe_filter, Set.mem_setOf_eq] at hc hc'
    obtain ⟨hcC, hcb⟩ := hc
    obtain ⟨hc'C, hc'b⟩ := hc'
    have hclt : c < 2 ^ Qp := by have := hC hcC; rwa [Finset.mem_range] at this
    have hc'lt : c' < 2 ^ Qp := by have := hC hc'C; rwa [Finset.mem_range] at this
    have hπeq : π c = π c' := by rw [hcb, hc'b]
    have hQ'digits : ∀ γ < ℓ, digit c 2 (qElem Q' γ) = digit c' 2 (qElem Q' γ) := by
      apply digitsum_inj ℓ (fun γ => digit c 2 (qElem Q' γ)) (fun γ => digit c' 2 (qElem Q' γ))
        (fun γ => digit_lt_two _ _) (fun γ => digit_lt_two _ _)
      simpa [hπ] using hπeq
    have hFrdigits : ∀ j < (Qp - ℓ), digit c 2 (qElem Fr j) = digit c' 2 (qElem Fr j) := by
      apply digitsum_inj (Qp - ℓ) (fun j => digit c 2 (qElem Fr j))
        (fun j => digit c' 2 (qElem Fr j)) (fun j => digit_lt_two _ _) (fun j => digit_lt_two _ _)
      simpa [hψ] using hψeq
    apply eq_of_digits_eq hclt hc'lt
    intro i hi
    by_cases hiQ' : i ∈ Q'
    · obtain ⟨γ, hγ, hγeq⟩ := mem_iff_qElem Q' i hiQ'
      rw [← hγeq]; exact hQ'digits γ (by rw [hℓ]; exact hγ)
    · have hiFr : i ∈ Fr := by
        rw [hFr, Finset.mem_sdiff]; exact ⟨Finset.mem_range.mpr hi, hiQ'⟩
      obtain ⟨j, hj, hjeq⟩ := mem_iff_qElem Fr i hiFr
      rw [← hjeq]; exact hFrdigits j (by rw [← hFrcard]; exact hj)
  have hfibcard : Fib.card ≤ (Finset.range (2 ^ (Qp - ℓ))).card :=
    Finset.card_le_card_of_injOn ψ hmaps hinj
  rw [Finset.card_range] at hfibcard
  exact hfibcard

/-! ### Lemma 4.15 and 4.16 -/

/-- **Columns of a Boolean matrix are pairwise distinct.**  The map sending a
column index `j` to the column vector `fun i => M.e i j` is injective. -/
def DistinctColumns (M : BoolMat) : Prop :=
  Function.Injective (fun (j : Fin M.n) => (fun i : Fin M.m => M.e i j))

/-- **EXTERNAL (prior work) — the log-rank lower bound, in its standard
distinct-columns / fooling form.**

This is the only non-`Mathlib` axiom used in this development.  It packages two
classical facts about deterministic two-party communication complexity:

* the **log-rank lower bound** (Kushilevitz–Nisan, *Communication Complexity*,
  cited in the paper as `Kushilevitz1997`, and Rao–Yehudayoff,
  `rao2020communication`): for every Boolean matrix `M`,
  `D(M) ≥ ⌈log₂ rank_ℝ(M)⌉`, with `rank_ℝ(M)` the rank of the real matrix
  obtained from `M` by the entrywise coercion `true ↦ 1, false ↦ 0`; and
* the **`{0,1}`-column fooling bound**: a Boolean matrix whose `M.n` columns are
  pairwise distinct has `M.n ≤ 2^{rank_ℝ(M)}`, equivalently
  `log₂ M.n ≤ rank_ℝ(M)` (each column lies in the column space of dimension
  `rank`, and a coordinate projection onto a maximal independent set of rows
  embeds the distinct `{0,1}`-columns injectively into `{0,1}^{rank}`).

Composing the two and using monotonicity of `⌈log₂ ·⌉` gives, for any Boolean
matrix `M` with pairwise distinct columns,
`D(M) ≥ ⌈log₂ rank_ℝ(M)⌉ ≥ ⌈log₂ (log₂ M.n)⌉`.

The inner `log₂ M.n` is exactly the column-count whose `log₂` lower-bounds the
real rank (Step 2 of the paper's argument); the outer `log₂` is the log-rank
bound itself (Step 3).  This statement is **not** proved in the paper — it is the
cited external ingredient — and is admitted here as a named axiom. -/
theorem logRank_distinctCols (M : BoolMat) (hM : DistinctColumns M) :
    (Dmat M : ℝ) ≥ Real.logb 2 (Real.logb 2 (M.n : ℝ)) := by
  by_cases hMn : M.n ≤ 1
  · -- M.n ≤ 1: as a Nat, M.n ∈ {0,1}, so logb 2 (M.n) = 0, hence logb 2 (logb 2 M.n) = 0.
    have hlog_zero : Real.logb 2 (M.n : ℝ) = 0 := by
      interval_cases h : M.n
      · simp
      · simp
    have houter_zero : Real.logb 2 (Real.logb 2 (M.n : ℝ)) = 0 := by
      rw [hlog_zero, Real.logb_zero]
    have hD_nonneg : (0 : ℝ) ≤ (Dmat M : ℝ) := by exact_mod_cast Nat.zero_le _
    rw [ge_iff_le, houter_zero]
    exact hD_nonneg
  · -- M.n ≥ 2.
    have hMn2 : 2 ≤ M.n := by omega
    have hMnR : (2 : ℝ) ≤ (M.n : ℝ) := by exact_mod_cast hMn2
    have hMnpos : (0 : ℝ) < (M.n : ℝ) := by linarith
    -- distinct columns ⟹ M.n ≤ 2 ^ boolRank M.
    have hcard : M.n ≤ 2 ^ Proof.LogRankBound.boolRank M :=
      Proof.LogRankBound.distinctCols_card_le_two_pow_rank M hM
    -- boolRank M ≥ 1 (else 2 ≤ M.n ≤ 2^0 = 1, contradiction).
    have hrank1 : 1 ≤ Proof.LogRankBound.boolRank M := by
      by_contra h
      have hr0 : Proof.LogRankBound.boolRank M = 0 := by omega
      rw [hr0, pow_zero] at hcard
      omega
    have hrankR1 : (1 : ℝ) ≤ (Proof.LogRankBound.boolRank M : ℝ) := by
      exact_mod_cast hrank1
    -- logb 2 (M.n) ≤ logb 2 (2 ^ boolRank M) = boolRank M.
    have hcardR : (M.n : ℝ) ≤ (2 : ℝ) ^ Proof.LogRankBound.boolRank M := by
      have := hcard
      have h2 : ((2 ^ Proof.LogRankBound.boolRank M : ℕ) : ℝ)
          = (2 : ℝ) ^ Proof.LogRankBound.boolRank M := by push_cast; ring
      calc (M.n : ℝ) ≤ ((2 ^ Proof.LogRankBound.boolRank M : ℕ) : ℝ) := by exact_mod_cast this
        _ = (2 : ℝ) ^ Proof.LogRankBound.boolRank M := h2
    have hlogMn_le_rank : Real.logb 2 (M.n : ℝ)
        ≤ (Proof.LogRankBound.boolRank M : ℝ) := by
      have hstep : Real.logb 2 (M.n : ℝ)
          ≤ Real.logb 2 ((2 : ℝ) ^ Proof.LogRankBound.boolRank M) :=
        Real.logb_le_logb_of_le (by norm_num) hMnpos hcardR
      have hval : Real.logb 2 ((2 : ℝ) ^ Proof.LogRankBound.boolRank M)
          = (Proof.LogRankBound.boolRank M : ℝ) := by
        rw [Real.logb_pow]
        simp [Real.logb_self_eq_one]
      rw [hval] at hstep; exact hstep
    -- logb 2 (M.n) > 0 since M.n ≥ 2.
    have hlogMn_pos : (0 : ℝ) < Real.logb 2 (M.n : ℝ) :=
      Real.logb_pos (by norm_num) (by linarith)
    -- apply logb 2 again (monotone): logb 2 (logb 2 M.n) ≤ logb 2 (boolRank M).
    have hchain : Real.logb 2 (Real.logb 2 (M.n : ℝ))
        ≤ Real.logb 2 (Proof.LogRankBound.boolRank M : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) hlogMn_pos hlogMn_le_rank
    -- Dmat M ≥ logb 2 (boolRank M).
    have hlb := Proof.LogRankBound.logRank_lowerBound M
    -- chain everything.
    calc Real.logb 2 (Real.logb 2 (M.n : ℝ))
        ≤ Real.logb 2 (Proof.LogRankBound.boolRank M : ℝ) := hchain
      _ ≤ (Dmat M : ℝ) := hlb

/-- Entry of `interlace (phi Q 0) p` at row `i`, column `c`: it is `true` iff the
`i`-th binary digit of `c` is `0` (equivalently `decide (digit c 2 i = 0)`). -/
private theorem interlace_phi0_e (p : ℕ) (i c : ℕ)
    (hi : i < (interlace (phi Q 0) p).m) (hc : c < (interlace (phi Q 0) p).n) :
    (interlace (phi Q 0) p).e ⟨i, hi⟩ ⟨c, hc⟩ = decide (digit c 2 i = 0) := by
  have hm : (interlace (phi Q 0) p).m = p := by simp [interlace, phi_zero]
  have hn : (interlace (phi Q 0) p).n = 2 ^ p := by simp [interlace, phi_zero]
  simp only [interlace, phi_zero, Nat.mod_one, Nat.div_one]
  unfold digit
  rcases Nat.eq_zero_or_pos ((c / 2 ^ i) % 2) with h | h
  · simp [h]
  · have h1 : (c / 2 ^ i) % 2 = 1 := by omega
    simp [h1]

/-- If `decide (digit a 2 i = 0) = decide (digit b 2 i = 0)` then `digit a 2 i = digit b 2 i`
(both digits are `< 2`). -/
private theorem digit_eq_of_decide (a b i : ℕ)
    (h : (decide (digit a 2 i = 0) : Bool) = decide (digit b 2 i = 0)) :
    digit a 2 i = digit b 2 i := by
  rw [decide_eq_decide] at h
  have := digit_lt_two a i; have := digit_lt_two b i; omega

/-- Entry of `extract (interlace (phi Q 0) p) (range p) C` at row `⟨i,hri⟩`, column `col`:
when `i < p` and the underlying column `c := C.sort.getD col.val 0 < 2^p`, the entry equals
`decide (digit c 2 i = 0)`. -/
private theorem extract_phi0_e (p : ℕ) (C : Finset ℕ) (i : ℕ)
    (col : Fin (extract (interlace (phi Q 0) p) (Finset.range p) C).n)
    (hi : i < p)
    (hri : i < (extract (interlace (phi Q 0) p) (Finset.range p) C).m)
    (hc : (C.sort (· ≤ ·)).getD col.val 0 < 2 ^ p) :
    (extract (interlace (phi Q 0) p) (Finset.range p) C).e ⟨i, hri⟩ col
      = decide (digit ((C.sort (· ≤ ·)).getD col.val 0) 2 i = 0) := by
  have hmI : (interlace (phi Q 0) p).m = p := by simp [interlace, phi_zero]
  have hnI : (interlace (phi Q 0) p).n = 2 ^ p := by simp [interlace, phi_zero]
  have hrow : ((Finset.range p).sort (· ≤ ·)).getD i 0 = i := by
    rw [Finset.sort_range, List.getD_eq_getElem _ _ (by rw [List.length_range]; exact hi)]; simp
  have hrlt0 : ((Finset.range p).sort (· ≤ ·)).getD i 0 < (interlace (phi Q 0) p).m := by
    rw [hrow, hmI]; exact hi
  have hclt : (C.sort (· ≤ ·)).getD col.val 0 < (interlace (phi Q 0) p).n := by rw [hnI]; exact hc
  -- the extract entry is the interlace entry at (getD i 0, getD col 0).
  have hentry : (extract (interlace (phi Q 0) p) (Finset.range p) C).e ⟨i, hri⟩ col
      = (interlace (phi Q 0) p).e ⟨((Finset.range p).sort (· ≤ ·)).getD i 0, hrlt0⟩
          ⟨(C.sort (· ≤ ·)).getD col.val 0, hclt⟩ := by
    show (extract (interlace (phi Q 0) p) (Finset.range p) C).e ⟨i, hri⟩ col = _
    unfold extract
    simp only
    rw [dif_pos ⟨hrlt0, hclt⟩]
  rw [hentry, interlace_phi0_e p (((Finset.range p).sort (· ≤ ·)).getD i 0)
      ((C.sort (· ≤ ·)).getD col.val 0) hrlt0 hclt, hrow]

/-- The interlace `⟨φ_0⟩^p` has pairwise distinct columns for `p ≥ 1`. -/
private theorem interlace_phi0_distinctCols (p : ℕ) (hp : 1 ≤ p) :
    DistinctColumns (interlace (phi Q 0) p) := by
  have hm : (interlace (phi Q 0) p).m = p := by simp [interlace, phi_zero]
  have hn : (interlace (phi Q 0) p).n = 2 ^ p := by simp [interlace, phi_zero]
  intro c1 c2 hcols
  have hc1 : c1.val < 2 ^ p := by rw [← hn]; exact c1.isLt
  have hc2 : c2.val < 2 ^ p := by rw [← hn]; exact c2.isLt
  apply Fin.ext
  apply eq_of_digits_eq hc1 hc2
  intro k hk
  have hkm : k < (interlace (phi Q 0) p).m := by rw [hm]; exact hk
  have heq := congrFun hcols ⟨k, hkm⟩
  simp only at heq
  rw [interlace_phi0_e p k c1.val hkm c1.isLt,
      interlace_phi0_e p k c2.val hkm c2.isLt] at heq
  exact digit_eq_of_decide c1.val c2.val k heq

/-- `extract (interlace (phi Q 0) p) (range p) C` has distinct columns, when
`C ⊆ range (2^p)` (so the extracted columns are genuine length-`p` distinct
Boolean vectors).  The row set `range p` keeps all `p` rows. -/
private theorem extract_phi0_distinctCols (p : ℕ) (hp : 1 ≤ p) (C : Finset ℕ)
    (hCsub : C ⊆ Finset.range ((phi Q 0).n ^ p)) :
    DistinctColumns (extract (interlace (phi Q 0) p) (Finset.range p) C) := by
  classical
  have hn : (phi Q 0).n = 2 := rfl
  have hmI : (interlace (phi Q 0) p).m = p := by simp [interlace, phi_zero]
  have hnI : (interlace (phi Q 0) p).n = 2 ^ p := by simp [interlace, phi_zero]
  rw [hn] at hCsub
  set A := interlace (phi Q 0) p with hA
  set sR := (Finset.range p).sort (· ≤ ·) with hsR
  set sC := C.sort (· ≤ ·) with hsC
  -- sorted range p is 0,1,…,p-1: getD i 0 = i for i < p.
  have hsRrange : sR = List.range p := by rw [hsR]; exact Finset.sort_range p
  have hsRget : ∀ i : ℕ, i < p → sR.getD i 0 = i := by
    intro i hi
    rw [hsRrange, List.getD_eq_getElem _ _ (by rw [List.length_range]; exact hi)]
    simp
  have hsClen : sC.length = C.card := by rw [hsC, Finset.length_sort]
  -- column index j of extract maps to actual column sC.getD j 0 in C ⊆ range(2^p).
  have hcv : ∀ j : ℕ, j < C.card → sC.getD j 0 < 2 ^ p := by
    intro j hj
    have hlt : j < sC.length := by rw [hsClen]; exact hj
    have hmem : sC.getD j 0 ∈ C := by
      have : sC.getD j 0 ∈ sC := by
        rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
      rwa [hsC, Finset.mem_sort] at this
    exact Finset.mem_range.mp (hCsub hmem)
  intro c1 c2 hcols
  -- column indices are < C.card.
  have hc1lt : (c1 : ℕ) < C.card := by have := c1.isLt; simpa [extract] using this
  have hc2lt : (c2 : ℕ) < C.card := by have := c2.isLt; simpa [extract] using this
  have hd1 : sC.getD c1.val 0 < 2 ^ p := hcv c1.val hc1lt
  have hd2 : sC.getD c2.val 0 < 2 ^ p := hcv c2.val hc2lt
  -- For every row i < p, the two extract entries agree, hence the digits of the
  -- two underlying column indices agree at i.
  have hdig : ∀ i, i < p → digit (sC.getD c1.val 0) 2 i = digit (sC.getD c2.val 0) 2 i := by
    intro i hi
    have hrowidx : i < (extract A (Finset.range p) C).m := by
      simp only [extract_m, Finset.card_range]; exact hi
    have hee := congrFun hcols ⟨i, hrowidx⟩
    simp only at hee
    -- rewrite both extract entries via extract_phi0_e.
    rw [hA] at hee hrowidx
    rw [extract_phi0_e p C i c1 hi hrowidx (by rw [← hsC]; exact hd1),
        extract_phi0_e p C i c2 hi hrowidx (by rw [← hsC]; exact hd2)] at hee
    rw [hsC]
    exact digit_eq_of_decide ((C.sort (· ≤ ·)).getD c1.val 0)
      ((C.sort (· ≤ ·)).getD c2.val 0) i hee
  -- digit equality on all positions < p ⟹ underlying indices equal.
  have hcoleq : sC.getD c1.val 0 = sC.getD c2.val 0 := eq_of_digits_eq hd1 hd2 hdig
  -- C.sort getD injective on valid indices ⟹ c1 = c2.
  apply Fin.ext
  have hnd : sC.Nodup := by rw [hsC]; exact Finset.sort_nodup _ _
  have h1len : c1.val < sC.length := by rw [hsClen]; exact hc1lt
  have h2len : c2.val < sC.length := by rw [hsClen]; exact hc2lt
  rw [List.getD_eq_getElem _ _ h1len, List.getD_eq_getElem _ _ h2len] at hcoleq
  exact (List.Nodup.getElem_inj_iff hnd).mp hcoleq

/-- For a member of `[φ_0]_{p,x,y}`, the row set `R` (which is `p,1,p`-equipartitioned
into singleton blocks `{γ}`, all of `range p`) equals `range p`. -/
private theorem equip_phi0_R_eq_range (p : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (R : Finset ℕ) (hRsub : R ⊆ Finset.range ((phi Q 0).m * p))
    (hRep : IsEquipartitioned R (phi Q 0).m (((phi Q 0).m : ℝ) * x) p) :
    R = Finset.range p := by
  have hm : (phi Q 0).m = 1 := rfl
  rw [hm, Nat.one_mul] at hRsub
  have hceil : ⌈((1 : ℕ) : ℝ) * x⌉₊ = 1 := by
    rw [Nat.cast_one, one_mul, Nat.ceil_eq_iff (by norm_num)]
    refine ⟨by simpa using hx0, by simpa using hx1⟩
  ext a
  simp only [Finset.mem_range]
  constructor
  · intro ha; exact Finset.mem_range.mp (hRsub ha)
  · intro ha
    -- block γ = a is the singleton {a}; equipartition forces it nonempty.
    have hcard := hRep a ha
    rw [hm] at hcard
    rw [hceil] at hcard
    -- the filter is over {i ∈ R | a ≤ i ∧ i < a+1} = {i ∈ R | i = a}
    have hfilt : R.filter (fun i => 1 * a ≤ i ∧ i < 1 * (a + 1)) = R.filter (fun i => i = a) := by
      apply Finset.filter_congr
      intro i _
      simp only [Nat.one_mul, eq_iff_iff]
      omega
    rw [hfilt] at hcard
    by_contra hnotmem
    have : R.filter (fun i => i = a) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi heq; subst heq; exact hnotmem hi
    rw [this, Finset.card_empty] at hcard
    exact absurd hcard (by norm_num)

/-- Lemma 4.15 (Rank claim — uses the external log-rank lower bound).
For naturals `p` and reals `0 < x ≤ 1`, `0 < y ≤ 1` with `p + log₂ y > 0`,
`D([φ_0]_{p,x,y}) ≥ ⌈ log₂(p + log₂ y) ⌉`. Both logs are base 2. -/
theorem rank_claim
    (p : ℕ) (x y : ℝ)
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hpos : (p : ℝ) + Real.logb 2 y > 0) :
    DSet (bracket (phi Q 0) p x y)
      ≥ ⌈Real.logb 2 ((p : ℝ) + Real.logb 2 y)⌉₊ := by
  classical
  have hm : (phi Q 0).m = 1 := rfl
  have hn : (phi Q 0).n = 2 := rfl
  -- (R0) p ≥ 1 forced by hpos and y ≤ 1.
  have hlogy_le : Real.logb 2 y ≤ 0 := by
    rw [show (0 : ℝ) = Real.logb 2 1 by simp]
    exact Real.logb_le_logb_of_le (by norm_num) hy0 hy1
  have hp1 : 1 ≤ p := by
    by_contra h
    have hp0 : p = 0 := by omega
    rw [hp0] at hpos; push_cast at hpos; linarith
  -- log₂(2^p · y) = p + log₂ y, and N := ⌈2^p·y⌉₊ ≥ 1 with log₂ N ≥ p + log₂ y.
  have h2py_pos : (0 : ℝ) < (2 : ℝ) ^ p * y := by positivity
  -- abbreviate the column count N.
  set N : ℕ := ⌈((((phi Q 0).n ^ p : ℕ)) : ℝ) * y⌉₊ with hNdef
  have hNeq : N = ⌈(2 : ℝ) ^ p * y⌉₊ := by
    rw [hNdef, hn]; norm_num
  have hN_ge : ((2 : ℝ) ^ p * y) ≤ (N : ℝ) := by rw [hNeq]; exact Nat.le_ceil _
  have hN1 : 1 ≤ N := by
    rw [hNeq, Nat.one_le_ceil_iff]; exact h2py_pos
  have hNpos_real : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  -- log₂ N ≥ p + log₂ y.
  have hlogN_ge : (p : ℝ) + Real.logb 2 y ≤ Real.logb 2 (N : ℝ) := by
    have hstep : Real.logb 2 ((2 : ℝ) ^ p * y) ≤ Real.logb 2 (N : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) h2py_pos hN_ge
    have hval : Real.logb 2 ((2 : ℝ) ^ p * y) = (p : ℝ) + Real.logb 2 y := by
      rw [Real.logb_mul (by positivity) (ne_of_gt hy0)]
      congr 1
      rw [Real.logb_pow]
      simp [Real.logb_self_eq_one]
    rw [hval] at hstep; exact hstep
  -- The column count N is ≥ 2 (so log₂ N > 0), since p + log₂ y > 0.
  have hlogN_pos : (0 : ℝ) < Real.logb 2 (N : ℝ) := lt_of_lt_of_le hpos hlogN_ge
  -- Nonemptiness of the bracket: witness R = range p, C = range N.
  have hCle : N ≤ 2 ^ p := by
    rw [hNeq]
    have hle : (2 : ℝ) ^ p * y ≤ ((2 ^ p : ℕ) : ℝ) := by
      push_cast; nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) p]
    calc ⌈(2 : ℝ) ^ p * y⌉₊ ≤ ⌈((2 ^ p : ℕ) : ℝ)⌉₊ := Nat.ceil_le_ceil hle
      _ = 2 ^ p := by rw [Nat.ceil_natCast]
  have hne : (bracket (phi Q 0) p x y).Nonempty := by
    refine ⟨extract (interlace (phi Q 0) p) (Finset.range p) (Finset.range N), ?_⟩
    refine ⟨Finset.range p, Finset.range N, ?_, ?_, ?_, ?_, rfl⟩
    · rw [hm, Nat.one_mul]
    · intro γ hγ
      rw [hm]
      have hfilt : (Finset.range p).filter (fun i => 1 * γ ≤ i ∧ i < 1 * (γ + 1))
          = {γ} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, Nat.one_mul]
        omega
      rw [hfilt, Finset.card_singleton]
      have hceil : ⌈((1 : ℕ) : ℝ) * x⌉₊ = 1 := by
        rw [Nat.cast_one, one_mul, Nat.ceil_eq_iff (by norm_num)]
        refine ⟨by simpa using hx0, by simpa using hx1⟩
      simpa using hceil.symm
    · rw [hn]
      intro c hc
      rw [Finset.mem_range] at hc ⊢
      calc c < N := hc
        _ ≤ 2 ^ p := hCle
    · rw [Finset.card_range, hNdef]
  -- Pass to the infimum: prove every member's Dmat ≥ rhs.
  rw [ge_iff_le, DSet]
  apply le_csInf
  · obtain ⟨M₀, hM₀⟩ := hne
    exact ⟨Dmat M₀, M₀, hM₀, rfl⟩
  · rintro v ⟨g, hg, rfl⟩
    obtain ⟨R, C, hRsub, hRep, hCsub, hCcard, hgeq⟩ := hg
    -- R = range p (all rows kept).
    have hReq : R = Finset.range p := equip_phi0_R_eq_range p x hx0 hx1 R hRsub hRep
    -- g.n = C.card = N.
    have hgn : g.n = N := by rw [hgeq]; simp only [extract_n]; rw [hCcard]
    -- g has distinct columns.
    have hgdist : DistinctColumns g := by
      rw [hgeq, hReq]
      exact extract_phi0_distinctCols p hp1 C hCsub
    -- apply the axiom.
    have hax := logRank_distinctCols g hgdist
    rw [hgn] at hax
    -- bridge: ⌈log₂(p + log₂ y)⌉₊ ≤ Dmat g.
    have hlogchain : Real.logb 2 ((p : ℝ) + Real.logb 2 y) ≤ Real.logb 2 (Real.logb 2 (N : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num) hpos hlogN_ge
    have hfinal : Real.logb 2 ((p : ℝ) + Real.logb 2 y) ≤ (Dmat g : ℝ) :=
      le_trans hlogchain hax
    have hceil : ⌈Real.logb 2 ((p : ℝ) + Real.logb 2 y)⌉₊ ≤ Dmat g := by
      rw [Nat.ceil_le]; exact hfinal
    exact hceil

/-- Lemma 4.16 (`φ_0` seed).
Let `Qp` be a positive integer, `0 < θ ≤ 1`, `0 < y ≤ 1`, `0 < x ≤ 1`, and
`q = ⌊Qp·θ⌋`. If `q ≥ 1`, then `D([⟨φ_0⟩^{Qp}]_{1,θ,y}) ≥ D([φ_0]_{q,x,y})`. -/
theorem phi_zero_seed
    (Qp : ℕ) (hQp : 0 < Qp)
    (θ y x : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hq : 1 ≤ ⌊(Qp : ℝ) * θ⌋₊) :
    DSet (bracket (interlace (phi Q 0) Qp) 1 θ y)
      ≥ DSet (bracket (phi Q 0) (⌊(Qp : ℝ) * θ⌋₊) x y) := by
  classical
  set q : ℕ := ⌊(Qp : ℝ) * θ⌋₊ with hqdef
  set M0 : BoolMat := phi Q 0 with hM0
  have hM0m : M0.m = 1 := rfl
  have hM0n : M0.n = 2 := rfl
  set B : BoolMat := interlace M0 Qp with hB
  have hBm : B.m = Qp := by rw [hB]; simp [interlace, hM0m]
  have hBn : B.n = 2 ^ Qp := by rw [hB]; simp [interlace, hM0n]
  have hqQp : q ≤ Qp := by
    rw [hqdef]
    have hle : (Qp : ℝ) * θ ≤ (Qp : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) Qp]
    calc ⌊(Qp : ℝ) * θ⌋₊ ≤ ⌊(Qp : ℝ)⌋₊ := Nat.floor_le_floor hle
      _ = Qp := by rw [Nat.floor_natCast]
  rw [ge_iff_le]
  apply subgames_are_easier
  · -- Nonemptiness of the source family.
    -- Witness: R = range ⌈Qp·θ⌉₊, C = range ⌈2^Qp·y⌉₊.
    have hTle : ⌈(Qp : ℝ) * θ⌉₊ ≤ Qp := by
      have hle : (Qp : ℝ) * θ ≤ (Qp : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) Qp]
      calc ⌈(Qp : ℝ) * θ⌉₊ ≤ ⌈(Qp : ℝ)⌉₊ := Nat.ceil_le_ceil hle
        _ = Qp := by rw [Nat.ceil_natCast]
    have hCle : ⌈((2 ^ Qp : ℕ) : ℝ) * y⌉₊ ≤ 2 ^ Qp := by
      have hle : ((2 ^ Qp : ℕ) : ℝ) * y ≤ ((2 ^ Qp : ℕ) : ℝ) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) (2 ^ Qp)]
      calc ⌈((2 ^ Qp : ℕ) : ℝ) * y⌉₊ ≤ ⌈((2 ^ Qp : ℕ) : ℝ)⌉₊ := Nat.ceil_le_ceil hle
        _ = 2 ^ Qp := by rw [Nat.ceil_natCast]
    refine ⟨extract (interlace B 1) (Finset.range ⌈(Qp : ℝ) * θ⌉₊)
        (Finset.range ⌈((2 ^ Qp : ℕ) : ℝ) * y⌉₊), ?_⟩
    refine ⟨Finset.range ⌈(Qp : ℝ) * θ⌉₊, Finset.range ⌈((2 ^ Qp : ℕ) : ℝ) * y⌉₊,
      ?_, ?_, ?_, ?_, rfl⟩
    · rw [hBm, Nat.mul_one]
      intro i hi
      rw [Finset.mem_range] at hi ⊢
      omega
    · intro γ hγ
      rw [hBm]
      have hγ0 : γ = 0 := by omega
      subst hγ0
      have hfilt : (Finset.range ⌈(Qp : ℝ) * θ⌉₊).filter
          (fun i => Qp * 0 ≤ i ∧ i < Qp * (0 + 1))
          = Finset.range ⌈(Qp : ℝ) * θ⌉₊ := by
        apply Finset.filter_true_of_mem
        intro i hi
        rw [Finset.mem_range] at hi
        omega
      rw [hfilt, Finset.card_range]
    · rw [hBn, Nat.pow_one]
      intro i hi
      rw [Finset.mem_range] at hi ⊢
      omega
    · rw [hBn, Nat.pow_one, Finset.card_range]
  · -- IsSubgameSet (target) (source).
    intro g hg
    obtain ⟨R, C, hR, hRpart, hC, hCcard, hgeq⟩ := hg
    rw [Nat.mul_one] at hR
    rw [Nat.pow_one] at hC hCcard
    have hRcard : R.card = ⌈(B.m : ℝ) * θ⌉₊ := by
      have h0 := hRpart 0 (by norm_num)
      rw [Finset.filter_true_of_mem] at h0
      · simpa using h0
      · intro i hi
        have := hR hi
        simp only [Finset.mem_range, Nat.mul_one] at this ⊢
        omega
    rw [hBm] at hRcard hR
    rw [hBn] at hC hCcard
    have hqle : q ≤ R.card := by
      rw [hRcard, hqdef]
      have h1 : (⌊(Qp : ℝ) * θ⌋₊ : ℝ) ≤ (Qp : ℝ) * θ := Nat.floor_le (by positivity)
      have h2 : (Qp : ℝ) * θ ≤ (⌈(Qp : ℝ) * θ⌉₊ : ℝ) := Nat.le_ceil _
      have : (⌊(Qp : ℝ) * θ⌋₊ : ℝ) ≤ (⌈(Qp : ℝ) * θ⌉₊ : ℝ) := le_trans h1 h2
      exact_mod_cast this
    obtain ⟨Q', hQ'sub, hQ'card⟩ := Finset.exists_subset_card_eq hqle
    have hQ'ne : Q'.Nonempty := by
      rw [← Finset.card_pos, hQ'card]; omega
    have hQ'range : Q' ⊆ Finset.range Qp := hQ'sub.trans hR
    set SD := qProjection R C M0.m M0.n Qp Q' with hSD
    have hSD1eq : SD.1 = (qProjection R C 1 2 Qp Q').1 := by rw [hSD, hM0m, hM0n]
    have hSD2eq : SD.2 = (qProjection R C 1 2 Qp Q').2 := by rw [hSD, hM0m, hM0n]
    have hS : SD.1 = Finset.range q := by
      rw [hSD1eq, proj_S_eq_range R C Q' hQ'sub hQ'ne Qp, hQ'card]
    have hproj := Proof.Projections.projection_lemma M0 Qp R C
      (by rw [hM0m, Nat.one_mul]; exact hR) (by rw [hM0n]; exact hC) Q' hQ'range hQ'ne
    rw [hQ'card] at hproj
    have hg_eq : g = extract B R C := by rw [hgeq, extract_interlace_one_eq]
    -- D ⊆ range (2^q).
    have hDsub : SD.2 ⊆ Finset.range (2 ^ q) := by
      rw [hSD2eq]
      have := proj_D_subset R C Q' Qp hQ'ne
      rwa [hQ'card] at this
    -- |D| ≥ ⌈2^q · y⌉₊.
    have hDlb : ⌈((2:ℕ) ^ q : ℝ) * y⌉₊ ≤ SD.2.card := by
      have hfib := proj_D_card_lb R C Q' Qp hQ'range (by rw [hQ'card]; exact hqQp) hQ'ne hC
      rw [hQ'card] at hfib
      rw [hSD2eq]
      set Dc := (qProjection R C 1 2 Qp Q').2.card with hDc
      -- hfib : C.card ≤ Dc * 2^(Qp - q),  hCcard : C.card = ⌈2^Qp · y⌉₊
      -- ⟹ Dc ≥ 2^q·y ⟹ Dc ≥ ⌈2^q·y⌉₊.
      apply Nat.ceil_le.mpr
      have hCge : ((2:ℝ) ^ Qp) * y ≤ (C.card : ℝ) := by
        rw [hCcard]; exact_mod_cast Nat.le_ceil _
      have hsplit : (Qp - q) + q = Qp := by omega
      have hpow : (2:ℝ) ^ Qp = 2 ^ (Qp - q) * 2 ^ q := by
        rw [← pow_add, hsplit]
      have hfibR : (C.card : ℝ) ≤ (Dc : ℝ) * 2 ^ (Qp - q) := by exact_mod_cast hfib
      have h2qp : (0:ℝ) < 2 ^ (Qp - q) := by positivity
      -- 2^Qp · y ≤ C.card ≤ Dc·2^(Qp-q) ⟹ 2^q·y ≤ Dc.
      have : ((2:ℕ) ^ q : ℝ) * y ≤ (Dc : ℝ) := by
        push_cast
        rw [hpow] at hCge
        have hchain : (2:ℝ) ^ (Qp - q) * 2 ^ q * y ≤ (Dc : ℝ) * 2 ^ (Qp - q) :=
          le_trans hCge hfibR
        -- divide by 2^(Qp-q)
        have hrw : (2:ℝ) ^ (Qp - q) * 2 ^ q * y = (2 ^ q * y) * 2 ^ (Qp - q) := by ring
        rw [hrw] at hchain
        exact le_of_mul_le_mul_right hchain h2qp
      convert this using 2
    obtain ⟨D', hD'sub, hD'card⟩ := Finset.exists_subset_card_eq hDlb
    refine ⟨extract (interlace M0 q) (Finset.range q) D', ?_, ?_⟩
    · refine ⟨Finset.range q, D', ?_, ?_, ?_, ?_, rfl⟩
      · rw [hM0m, Nat.one_mul]
      · intro γ hγ
        rw [hM0m]
        simp only [Nat.cast_one, one_mul]
        have hx1eq : ⌈x⌉₊ = 1 := by
          rw [Nat.ceil_eq_iff (by norm_num)]
          refine ⟨by simpa using hx0, by simpa using hx1⟩
        rw [hx1eq]
        have hfilt : (Finset.range q).filter (fun i => γ ≤ i ∧ i < γ + 1) = {γ} := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
          omega
        rw [hfilt, Finset.card_singleton]
      · rw [hM0n]
        exact hD'sub.trans hDsub
      · rw [hM0n, hD'card]
        congr 1
        push_cast
        ring_nf
    · rw [hg_eq]
      have h4b : IsSubgame (extract (interlace M0 q) (Finset.range q) D')
          (extract (interlace M0 q) (Finset.range q) SD.2) :=
        extract_col_subset_subgame _ _ _ _ hD'sub
      have h4a : IsSubgame (extract (interlace M0 q) (Finset.range q) SD.2)
          (extract (interlace M0 Qp) R C) := by
        rw [← hS]; exact hproj
      have hcomp := isSubgame_trans h4b h4a
      rw [hB]; exact hcomp

/-- Core reduction shared by Lemmas 4.17 and 4.19.
For any column density `η` with `0 < η ≤ 1`, writing `q = ⌊Q·η⌋₊`, if `q ≥ 1`
and `(q : ℝ) - 10010 > 0`, then
`D([φ_1]_{1, 2^{-k-a}, η}) ≥ ⌈ log₂((q : ℝ) - 10010) ⌉₊`.
This packages the transpose step (4.6), the seed step (4.16), and the rank
claim (4.15), with `2^{-k-a} = 2^{-10010}` as the (fixed) row density and
`x = 2^{-a}` the (immaterial) `φ_0`-row density. -/
private lemma phi_one_bracket_lower (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hq1 : 1 ≤ ⌊(Q : ℝ) * η⌋₊)
    (hqbig : (0 : ℝ) < (⌊(Q : ℝ) * η⌋₊ : ℝ) - 10010) :
    DSet (bracket (phi Q 1) 1 (Real.rpow 2 (-(10000 : ℝ) - 10)) η)
      ≥ ⌈Real.logb 2 ((⌊(Q : ℝ) * η⌋₊ : ℝ) - 10010)⌉₊ := by
  set xr : ℝ := Real.rpow 2 (-(10000 : ℝ) - 10) with hxr
  set x0 : ℝ := Real.rpow 2 (-(10 : ℝ)) with hx0def
  set q : ℕ := ⌊(Q : ℝ) * η⌋₊ with hqdef
  have hxr_pos : 0 < xr := rpow2_pos _
  have hxr_le1 : xr ≤ 1 := rpow2_le_one (by norm_num)
  have hx0_pos : 0 < x0 := rpow2_pos _
  have hx0_le1 : x0 ≤ 1 := rpow2_le_one (by norm_num)
  -- log₂(2^{-k-a}) = -10010.
  have hlogxr : Real.logb 2 xr = -(10010 : ℝ) := by
    rw [hxr, logb2_rpow2]; ring
  -- Step 1: transpose. phi Q 1 = (interlace (phi Q 0) Q).transpose.
  have hphi1 : phi Q 1 = (interlace (phi Q 0) Q).transpose := phi_succ Q 0
  have hT := Proof.BracketLemmas.transpose_bracket (interlace (phi Q 0) Q) η xr
  have hstep1 : DSet (bracket (phi Q 1) 1 xr η)
      = DSet (bracket (interlace (phi Q 0) Q) 1 η xr) := by
    rw [hphi1, hT]
  rw [hstep1]
  -- Step 2: seed lemma with θ = η, y = xr, x = x0.
  have hseed := phi_zero_seed Q Q_pos η xr x0 hη0 hη1 hxr_pos hxr_le1
    hx0_pos hx0_le1 (by rw [← hqdef]; exact hq1)
  rw [← hqdef] at hseed
  refine le_trans ?_ hseed
  -- Step 3: rank claim.  side condition q + log₂ xr > 0.
  have hpos : (q : ℝ) + Real.logb 2 xr > 0 := by rw [hlogxr]; linarith [hqbig]
  have hrank := rank_claim q x0 xr hx0_pos hx0_le1 hxr_pos hxr_le1 hpos
  refine le_trans ?_ hrank
  -- bridge: q + log₂ xr = q - 10010.
  rw [hlogxr]
  apply Nat.ceil_le_ceil
  have : (q : ℝ) + -(10010 : ℝ) = (q : ℝ) - 10010 := by ring
  rw [this]

/-- Lemma 4.17 (`φ_1` weak side condition).
For `k = 10000`, `a = 10`: `D([φ_1]_{1, 2^{-k-a}, 2^{-3}}) ≥ 1`. -/
theorem phi_one_weak_side_condition :
    DSet (bracket (phi Q 1) 1
      (Real.rpow 2 (-(10000 : ℝ) - 10)) (Real.rpow 2 (-3))) ≥ 1 := by
  set yc : ℝ := Real.rpow 2 (-3) with hyc
  have hyc_pos : 0 < yc := rpow2_pos _
  have hyc_le1 : yc ≤ 1 := rpow2_le_one (by norm_num)
  -- q := ⌊Q · 2^{-3}⌋₊ = 255 * 2^(10000-11).
  have hθval : yc = (1 : ℝ) / 8 := by
    rw [hyc]
    show (2 : ℝ) ^ (-3 : ℝ) = 1 / 8
    rw [Real.rpow_neg (by norm_num), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    norm_num
  -- Q·yc = 255 * 2^(10000-11), an exact integer (2^(10000-8)/8 = 2^(10000-11)).
  have hQcast : (Q : ℝ) = 255 * (2 : ℝ) ^ (10000 - 8 : ℕ) := by
    rw [Q]; push_cast; ring
  have hQθ : (Q : ℝ) * yc = ((255 * 2 ^ (10000 - 11) : ℕ) : ℝ) := by
    rw [hθval, hQcast, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
    rw [show (10000 - 8 : ℕ) = (10000 - 11 : ℕ) + 3 by norm_num, pow_add]
    ring
  have hq_eq : ⌊(Q : ℝ) * yc⌋₊ = 255 * 2 ^ (10000 - 11) := by
    rw [hQθ, Nat.floor_natCast]
  -- q ≥ 1.
  have hq1 : 1 ≤ ⌊(Q : ℝ) * yc⌋₊ := by
    rw [hq_eq]
    have h : 0 < 2 ^ (10000 - 11) := pow_pos (by norm_num) _
    calc (1 : ℕ) ≤ 255 * 1 := by norm_num
      _ ≤ 255 * 2 ^ (10000 - 11) := Nat.mul_le_mul_left 255 h
  -- (q : ℝ) - 10010 > 0  (in fact ≥ 2).
  have hqge : (10013 : ℝ) ≤ (⌊(Q : ℝ) * yc⌋₊ : ℝ) := by
    rw [hq_eq]
    norm_cast
  have hqbig : (0 : ℝ) < (⌊(Q : ℝ) * yc⌋₊ : ℝ) - 10010 := by linarith [hqge]
  have hkey := phi_one_bracket_lower yc hyc_pos hyc_le1 hq1 hqbig
  refine le_trans ?_ hkey
  -- ⌈log₂((q:ℝ) - 10010)⌉₊ ≥ 1 since (q:ℝ) - 10010 ≥ 3 > 2.
  have harg : (2 : ℝ) ≤ (⌊(Q : ℝ) * yc⌋₊ : ℝ) - 10010 := by linarith [hqge]
  have hlog2 : (1 : ℝ) ≤ Real.logb 2 ((⌊(Q : ℝ) * yc⌋₊ : ℝ) - 10010) := by
    rw [show (1 : ℝ) = Real.logb 2 2 by rw [Real.logb_self_eq_one] <;> norm_num]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) harg
  rw [Nat.one_le_iff_ne_zero, Ne, Nat.ceil_eq_zero, not_le]
  linarith [hlog2]

/-- Helper: `2^{-3/8} > 10/13`. -/
private lemma eta0_lb : (10 : ℝ) / 13 < Real.rpow 2 (-3 / 8 : ℝ) := by
  have hpos38 : (0:ℝ) < Real.rpow 2 (3/8 : ℝ) := rpow2_pos _
  have h38 : Real.rpow 2 (3 / 8 : ℝ) < 13 / 10 := by
    have hpow : (Real.rpow 2 (3/8 : ℝ))^(8:ℕ) = 8 := by
      rw [((Real.rpow_natCast (Real.rpow 2 (3/8:ℝ)) 8).symm.trans
          (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (3/8) 8).symm)]
      norm_num
    by_contra hle
    push Not at hle
    have hh : ((13/10 : ℝ))^(8:ℕ) ≤ (Real.rpow 2 (3/8:ℝ))^(8:ℕ) :=
      pow_le_pow_left₀ (by norm_num) hle 8
    rw [hpow] at hh
    norm_num at hh
  have hneg : Real.rpow 2 (-3 / 8 : ℝ) = (Real.rpow 2 (3 / 8 : ℝ))⁻¹ := by
    rw [show (-3/8 : ℝ) = -(3/8) by ring]
    exact Real.rpow_neg (by norm_num) (3/8)
  rw [hneg]
  rw [show (10:ℝ)/13 = (13/10 : ℝ)⁻¹ by norm_num]
  exact inv_strictAnti₀ hpos38 h38

/-- Helper: if `(2:ℝ)^m < N` then `m + 1 ≤ ⌈log₂ N⌉₊`. -/
private lemma ceil_log_step (m : ℕ) (N : ℝ) (hN : (2:ℝ)^m < N) :
    m + 1 ≤ ⌈Real.logb 2 N⌉₊ := by
  have hlog : (m : ℝ) < Real.logb 2 N := by
    have h2m : Real.logb 2 ((2:ℝ)^m) = m := by
      rw [Real.logb_pow]; simp [Real.logb_self_eq_one]
    calc (m:ℝ) = Real.logb 2 ((2:ℝ)^m) := h2m.symm
      _ < Real.logb 2 N := Real.logb_lt_logb (by norm_num) (by positivity) hN
  exact_mod_cast Nat.lt_ceil.mpr hlog

/-- Helper: `(Q:ℝ) = 255 * 2^9992`. -/
private lemma Qcast19 : (Q : ℝ) = 255 * (2:ℝ) ^ (9992 : ℕ) := by
  show ((255 * 2 ^ (10000 - 8) : ℕ) : ℝ) = 255 * (2:ℝ) ^ (9992 : ℕ)
  push_cast; norm_num

/-- Rung helper.  For `j ≤ 2` and a column density `η` with
`(10/13)/2^j < η`, we have `2^(9999 - j) < ⌊Q·η⌋₊ - 10010`. -/
private lemma rung19 (j : ℕ) (hj : j ≤ 2) (η : ℝ)
    (hη : (10:ℝ) / 13 / (2 ^ j : ℝ) < η) :
    (2:ℝ) ^ (9999 - j) < (⌊(Q:ℝ) * η⌋₊ : ℝ) - 10010 := by
  set P : ℝ := (2:ℝ) ^ (9992 : ℕ) with hP
  have hPpos : 0 < P := by rw [hP]; positivity
  have hP14 : (16384 : ℝ) ≤ P := by
    rw [hP, show (16384:ℝ) = (2:ℝ)^(14:ℕ) by norm_num]
    exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hQη : (Q:ℝ) * η = 255 * P * η := by rw [Qcast19]
  set D2 : ℝ := (2:ℝ) ^ j with hD2
  have h2d : (0:ℝ) < D2 := by rw [hD2]; positivity
  have h2dge : (1:ℝ) ≤ D2 := by rw [hD2]; exact one_le_pow₀ (by norm_num)
  have h2dle : D2 ≤ 4 := by
    rw [hD2]
    calc (2:ℝ)^j ≤ (2:ℝ)^2 := pow_le_pow_right₀ (by norm_num) hj
      _ = 4 := by norm_num
  -- density bound times 255·P
  have hlb : (255:ℝ) * P * ((10/13)/D2) < (Q:ℝ) * η := by
    rw [hQη]
    exact mul_lt_mul_of_pos_left hη (by positivity)
  have hfloor : (Q:ℝ) * η - 1 < (⌊(Q:ℝ) * η⌋₊ : ℝ) :=
    Nat.sub_one_lt_floor ((Q:ℝ) * η)
  -- 2^(9999-j) · D2 = 128 · P   (since (9999-j) + j = 9999 = 9992 + 7)
  have h2eD : (2:ℝ) ^ (9999 - j) * D2 = 128 * P := by
    rw [hD2, ← pow_add, show 9999 - j + j = 9999 by omega,
        hP, show (9999:ℕ) = 9992 + 7 by norm_num, pow_add]
    ring
  set R : ℝ := (2:ℝ) ^ (9999 - j) with hR
  have hRpos : (0:ℝ) < R := by rw [hR]; positivity
  -- Multiply the density bound through by 13·D2 > 0 to clear all denominators.
  have h13d2 : (0:ℝ) < 13 * D2 := by positivity
  -- hlb : 255·P·(10/13/D2) < Q·η.  Clear denominators:  1950·P < 13·D2·(Q·η).
  have hlb' : 2550 * P < 13 * D2 * ((Q:ℝ) * η) := by
    have e : (255:ℝ) * P * ((10/13)/D2) * (13 * D2) = 2550 * P := by
      field_simp; ring
    have := mul_lt_mul_of_pos_right hlb h13d2
    rw [e] at this; linarith [this]
  -- hfloor : Q·η - 1 < ⌊⌋.  Clear:  13·D2·(Q·η) - 13·D2 < 13·D2·⌊⌋.
  have hfloor' : 13 * D2 * ((Q:ℝ) * η) - 13 * D2 < 13 * D2 * (⌊(Q:ℝ) * η⌋₊ : ℝ) := by
    have h := mul_lt_mul_of_pos_left hfloor h13d2
    nlinarith [h]
  -- 13·D2·R = 1664·P  (from D2·R = 128·P).
  have hDR : D2 * R = 128 * P := by rw [mul_comm]; exact h2eD
  have hDR13 : 13 * D2 * R = 1664 * P := by nlinarith [hDR]
  clear_value P D2 R
  clear hP hD2 hR hQη hlb hfloor hη h2eD hDR
  rw [← sub_pos]
  -- (⌊⌋ - 10010 - R)·(13·D2) > 0, and 13·D2 > 0, so suffices the product > 0.
  have hprod : (0:ℝ) < ((⌊(Q:ℝ) * η⌋₊ : ℝ) - 10010 - R) * (13 * D2) := by
    have hexp : ((⌊(Q:ℝ) * η⌋₊ : ℝ) - 10010 - R) * (13 * D2)
        = 13 * D2 * (⌊(Q:ℝ) * η⌋₊ : ℝ) - 130130 * D2 - 13 * D2 * R := by ring
    rw [hexp, hDR13]
    -- 13·D2·⌊⌋ - 130130·D2 - 1664·P > 886·P - 130143·D2 > 0.
    have hPD : (130143:ℝ) * D2 ≤ 886 * P := by
      have h1 : (130143:ℝ) * D2 ≤ 130143 * 4 :=
        mul_le_mul_of_nonneg_left h2dle (by norm_num)
      have h2 : (886:ℝ) * 16384 ≤ 886 * P :=
        mul_le_mul_of_nonneg_left hP14 (by norm_num)
      norm_num at h1 h2 ⊢
      have h3 : (520572:ℝ) ≤ 14516224 := by norm_num
      linarith [h1, h2, h3]
    linarith [hlb', hfloor', hPD]
  have := (mul_pos_iff_of_pos_right h13d2).mp hprod
  linarith [this]

/-- Lemma 4.19 (`φ_1` lambda).
For `k = 10000`, `a = 10`: `Λ_{φ_1}(1, 2^{-k-a}, 2^{-3/8}) ≥ k`. -/
theorem phi_one_lambda :
    Lambda (phi Q 1) 1
      (Real.rpow 2 (-(10000 : ℝ) - 10)) (Real.rpow 2 (-3 / 8)) ≥ 10000 := by
  set xr : ℝ := Real.rpow 2 (-(10000 : ℝ) - 10) with hxr
  set y : ℝ := Real.rpow 2 (-3 / 8 : ℝ) with hy
  have hy_pos : 0 < y := rpow2_pos _
  have hy_le1 : y ≤ 1 := rpow2_le_one (by norm_num)
  have hy_lb : (10:ℝ) / 13 < y := eta0_lb
  -- Per-rung lower bound:  for j ≤ 2,  DSet(bracket φ₁ 1 xr (y/2^j)) ≥ 10000 - j.
  have rung : ∀ j : ℕ, j ≤ 2 →
      10000 - j ≤ DSet (bracket (phi Q 1) 1 xr (y / (2 ^ j : ℝ))) := by
    intro j hj
    set η : ℝ := y / (2 ^ j : ℝ) with hηdef
    have h2jpos : (0:ℝ) < (2 ^ j : ℝ) := by positivity
    have hη0 : 0 < η := by rw [hηdef]; positivity
    have hη1 : η ≤ 1 := by
      rw [hηdef, div_le_one h2jpos]
      calc y ≤ 1 := hy_le1
        _ ≤ (2 ^ j : ℝ) := one_le_pow₀ (by norm_num)
    have hηlb : (10:ℝ) / 13 / (2 ^ j : ℝ) < η := by
      rw [hηdef]; exact div_lt_div_of_pos_right hy_lb h2jpos
    have hr := rung19 j hj η hηlb
    have hqbig : (0:ℝ) < (⌊(Q:ℝ) * η⌋₊ : ℝ) - 10010 :=
      lt_trans (by positivity) hr
    have hq1 : 1 ≤ ⌊(Q:ℝ) * η⌋₊ := by
      have : (1:ℝ) ≤ (⌊(Q:ℝ) * η⌋₊ : ℝ) := by
        have h0 : (0:ℝ) < (2:ℝ) ^ (9999 - j) := by positivity
        linarith [hr, hqbig]
      exact_mod_cast this
    have hbracket := phi_one_bracket_lower η hη0 hη1 hq1 hqbig
    -- ⌈log₂(⌊Q·η⌋₊ - 10010)⌉₊ ≥ 10000 - j
    have hceil := ceil_log_step (9999 - j) ((⌊(Q:ℝ) * η⌋₊ : ℝ) - 10010) hr
    have hidx : (9999 - j) + 1 = 10000 - j := by omega
    rw [hidx] at hceil
    -- chain
    calc 10000 - j ≤ ⌈Real.logb 2 ((⌊(Q:ℝ) * η⌋₊ : ℝ) - 10010)⌉₊ := hceil
      _ ≤ DSet (bracket (phi Q 1) 1 xr η) := hbracket
  -- Assemble the three rungs into Λ ≥ 10000.
  have h0 := rung 0 (by norm_num)
  have h1 := rung 1 (by norm_num)
  have h2 := rung 2 (by norm_num)
  simp only [pow_zero, pow_one, div_one] at h0 h1
  rw [show ((2:ℝ)^(2:ℕ)) = 4 by norm_num] at h2
  -- rewrite y/2^1 = y/2 and y/4 to match Lambda's branches
  unfold Lambda
  rw [ge_iff_le, le_min_iff, le_min_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact h0
  · -- 10000 ≤ 1 + DSet(bracket .. (y/2))
    have : (10000 - 1) + 1 ≤ 1 + DSet (bracket (phi Q 1) 1 xr (y / 2)) := by
      have := h1
      omega
    omega
  · have : (10000 - 2) + 2 ≤ 2 + DSet (bracket (phi Q 1) 1 xr (y / 4)) := by
      have := h2
      omega
    omega

end Proof.PhiBase

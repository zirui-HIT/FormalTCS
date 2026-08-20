import Mathlib
import Proof.Types.BoolMat
import Proof.Types.Interlace
import Proof.Types.Extract
import Proof.Types.Subgame
import Proof.Types.MatComplexity
import Proof.Types.Bracket
import Proof.Types.Equipartition
import Proof.Types.CommComplexity
import Proof.Types.Protocol
import Proof.Projections
import Proof.ProofLemmas.SublemmaPrecompNoIncrease
import Proof.UpperBound

namespace Proof.BracketLemmas

open Proof.Types.BoolMat
open Proof.Types.Interlace
open Proof.Types.Extract
open Proof.Types.Subgame
open Proof.Types.MatComplexity
open Proof.Types.Bracket
open Proof.Types.Equipartition
open Proof.Types.CommComplexity
open Proof.Types.Protocol
open Proof.UpperBound

/-! ### Helper lemmas for `transpose_bracket` (Lemma 4.6) -/

/-- Entry of `interlace N 1` at valid coords equals `N.e`. -/
private theorem interlace_one_e (N : BoolMat) (a b : ℕ)
    (ha : a < (interlace N 1).m) (hb : b < (interlace N 1).n)
    (ha' : a < N.m) (hb' : b < N.n) :
    (interlace N 1).e ⟨a, ha⟩ ⟨b, hb⟩ = N.e ⟨a, ha'⟩ ⟨b, hb'⟩ := by
  simp only [interlace]
  congr 1 <;> · apply Fin.ext; simp [Nat.mod_eq_of_lt, Nat.div_eq_of_lt, ha', hb']

/-- The transpose member's entry function is the swap of the original member's. -/
private theorem extract_transpose_e_swap (M : BoolMat) (R C : Finset ℕ)
    (j : Fin (extract (interlace M.transpose 1) C R).m)
    (i : Fin (extract (interlace M.transpose 1) C R).n) :
    (extract (interlace M.transpose 1) C R).e j i
      = (extract (interlace M 1) R C).e
          ⟨i.val, by have := i.isLt; simp only [extract] at this ⊢; exact this⟩
          ⟨j.val, by have := j.isLt; simp only [extract] at this ⊢; exact this⟩ := by
  simp only [extract]
  set c := (C.sort (· ≤ ·)).getD j.val 0 with hc
  set r := (R.sort (· ≤ ·)).getD i.val 0 with hr
  have hiff : (c < (interlace M.transpose 1).m ∧ r < (interlace M.transpose 1).n)
      ↔ (r < (interlace M 1).m ∧ c < (interlace M 1).n) := by
    simp only [interlace, BoolMat.transpose, Nat.mul_one, Nat.pow_one]
    tauto
  by_cases h : c < (interlace M.transpose 1).m ∧ r < (interlace M.transpose 1).n
  · obtain ⟨hcm, hrn⟩ := h
    have hcM : c < M.n := by simpa [interlace, BoolMat.transpose] using hcm
    have hrM : r < M.m := by simpa [interlace, BoolMat.transpose] using hrn
    rw [dif_pos ⟨hcm, hrn⟩, dif_pos (hiff.mp ⟨hcm, hrn⟩)]
    rw [interlace_one_e M.transpose c r hcm hrn hcM hrM,
        interlace_one_e M r c (by simpa [interlace] using hrM) (by simpa [interlace] using hcM) hrM hcM]
    rfl
  · rw [dif_neg h, dif_neg (fun hh => h (hiff.mpr hh))]

/-- The transposed extract has equal communication complexity. -/
private theorem Dmat_extract_transpose (M : BoolMat) (R C : Finset ℕ) :
    Dmat (extract (interlace M.transpose 1) C R) = Dmat (extract (interlace M 1) R C) := by
  set g := extract (interlace M 1) R C with hg
  set g' := extract (interlace M.transpose 1) C R with hg'
  have hgm' : g'.m = g.n := by simp [hg, hg', extract]
  have hgn' : g'.n = g.m := by simp [hg, hg', extract]
  let eX : Fin g'.m ≃ Fin g.n := Fin.castOrderIso hgm' |>.toEquiv
  let eY : Fin g'.n ≃ Fin g.m := Fin.castOrderIso hgn' |>.toEquiv
  have hentry : ∀ (j : Fin g'.m) (i : Fin g'.n),
      g'.e j i = (fun (b : Fin g.n) (a : Fin g.m) => g.e a b) (eX j) (eY i) := by
    intro j i
    have hstep := extract_transpose_e_swap M R C j i
    rw [hstep]
    rfl
  unfold Dmat
  rw [show g'.e = (fun j i => (fun (b : Fin g.n) (a : Fin g.m) => g.e a b) (eX j) (eY i))
      from funext fun j => funext fun i => hentry j i]
  rw [D_reindex eX eY (fun (b : Fin g.n) (a : Fin g.m) => g.e a b)]
  exact (Proof.UpperBound.D_swap g.e).symm

/-- At `p = 1`, equipartition of `R ⊆ range k` w.r.t. target `t` is exactly `R.card = ⌈t⌉₊`. -/
private theorem equipartition_one_iff (R : Finset ℕ) (k : ℕ) (t : ℝ) (hR : R ⊆ Finset.range k) :
    IsEquipartitioned R k t 1 ↔ R.card = ⌈t⌉₊ := by
  unfold IsEquipartitioned
  constructor
  · intro h
    have h0 := h 0 (by norm_num)
    rw [Finset.filter_true_of_mem] at h0
    · simpa using h0
    · intro i hi
      have := hR hi
      simp only [Finset.mem_range] at this
      omega
  · intro h γ hγ
    interval_cases γ
    rw [Finset.filter_true_of_mem]
    · simpa using h
    · intro i hi
      have := hR hi
      simp only [Finset.mem_range] at this
      omega

/-- Membership swap: a member of `[M]_{1,x,y}` corresponds to a member of `[Mᵀ]_{1,y,x}`
with equal complexity. -/
private theorem bracket_one_mem_transpose (M : BoolMat) (x y : ℝ) (g : BoolMat)
    (hg : g ∈ bracket M 1 x y) :
    ∃ g' ∈ bracket M.transpose 1 y x, Dmat g' = Dmat g := by
  obtain ⟨R, C, hR, hRpart, hC, hCcard, hgeq⟩ := hg
  simp only [Nat.mul_one, Nat.pow_one] at hR hRpart hC hCcard
  rw [equipartition_one_iff R M.m _ hR] at hRpart
  refine ⟨extract (interlace M.transpose 1) C R, ?_, ?_⟩
  · refine ⟨C, R, ?_, ?_, ?_, ?_, rfl⟩
    · simpa [BoolMat.transpose] using hC
    · simp only [BoolMat.transpose_m]
      rw [equipartition_one_iff C M.n _ hC]
      exact hCcard
    · simpa [BoolMat.transpose] using hR
    · simp only [BoolMat.transpose_n, Nat.pow_one]
      exact hRpart
  · rw [hgeq]
    exact Dmat_extract_transpose M R C

/-! ### Structural helpers for Lemma 4.5 (Extended Balancing) -/

/-- Transitivity of `IsSubgame`. -/
private theorem isSubgame_trans {A B C : BoolMat}
    (h1 : IsSubgame A B) (h2 : IsSubgame B C) : IsSubgame A C := by
  obtain ⟨r1, c1, hr1, hc1, he1⟩ := h1
  obtain ⟨r2, c2, hr2, hc2, he2⟩ := h2
  exact ⟨r2 ∘ r1, c2 ∘ c1, hr2.comp hr1, hc2.comp hc1, fun i j => by
    rw [he1 i j, he2 (r1 i) (c1 j)]; rfl⟩

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

/-- A column-subset is a subgame: if `C' ⊆ C` then `extract A R C' ⊑ extract A R C`. -/
private theorem extract_col_subset_subgame (A : BoolMat) (R C' C : Finset ℕ)
    (hsub : C' ⊆ C) :
    IsSubgame (extract A R C') (extract A R C) := by
  classical
  set sC := C.sort (· ≤ ·) with hsC
  set sC' := C'.sort (· ≤ ·) with hsC'
  have getDmemC' : ∀ k : ℕ, k < sC'.length → sC'.getD k 0 ∈ C' := by
    intro k hk
    have hm : sC'.getD k 0 ∈ sC' := by
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    rw [hsC', Finset.mem_sort] at hm; exact hm
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
    have hj : j.val < C'.card := by simpa [extract] using j.isLt
    have hjlen : j.val < sC'.length := by rw [hsC', Finset.length_sort]; exact hj
    have hvmem : sC'.getD j.val 0 ∈ sC := by
      rw [hsC, Finset.mem_sort]; exact hsub (getDmemC' j.val hjlen)
    have hcolval : sC.getD (sC.idxOf (sC'.getD j.val 0)) 0 = sC'.getD j.val 0 := by
      have hidx : sC.idxOf (sC'.getD j.val 0) < sC.length := by
        rw [List.idxOf_lt_length_iff]; exact hvmem
      rw [List.getD_eq_getElem _ _ hidx]
      have hb : sC[sC.idxOf (sC'.getD j.val 0)]? = some (sC'.getD j.val 0) :=
        List.getElem?_idxOf hvmem
      rw [List.getElem?_eq_getElem hidx] at hb
      exact (Option.some.injEq _ _ ▸ hb)
    simp only [hsC, hsC'] at hcolval ⊢
    simp only [hcolval]

/-- A row-subset is a subgame: if `R' ⊆ R` then `extract A R' C ⊑ extract A R C`. -/
private theorem extract_row_subset_subgame (A : BoolMat) (R' R C : Finset ℕ)
    (hsub : R' ⊆ R) :
    IsSubgame (extract A R' C) (extract A R C) := by
  classical
  set sR := R.sort (· ≤ ·) with hsR
  set sR' := R'.sort (· ≤ ·) with hsR'
  have getDmemR' : ∀ k : ℕ, k < sR'.length → sR'.getD k 0 ∈ R' := by
    intro k hk
    have hm : sR'.getD k 0 ∈ sR' := by
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    rw [hsR', Finset.mem_sort] at hm; exact hm
  have rowidx : ∀ i : Fin (extract A R' C).m,
      sR.idxOf (sR'.getD i.val 0) < (extract A R C).m := by
    intro i
    have hi : i.val < R'.card := by simpa [extract] using i.isLt
    have hilen : i.val < sR'.length := by rw [hsR', Finset.length_sort]; exact hi
    have hvmem : sR'.getD i.val 0 ∈ R := hsub (getDmemR' i.val hilen)
    have hidx : sR.idxOf (sR'.getD i.val 0) < sR.length := by
      rw [List.idxOf_lt_length_iff]
      rw [hsR, Finset.mem_sort]; exact hvmem
    simpa [extract, hsR, Finset.length_sort] using hidx
  refine ⟨fun i => ⟨sR.idxOf (sR'.getD i.val 0), rowidx i⟩,
    fun j => ⟨j.val, by simpa [extract] using j.isLt⟩, ?_, ?_, ?_⟩
  · intro i1 i2 h
    apply Fin.ext
    have hi1 : i1.val < R'.card := by simpa [extract] using i1.isLt
    have hi2 : i2.val < R'.card := by simpa [extract] using i2.isLt
    have hi1len : i1.val < sR'.length := by rw [hsR', Finset.length_sort]; exact hi1
    have hi2len : i2.val < sR'.length := by rw [hsR', Finset.length_sort]; exact hi2
    have hmem1 : sR'.getD i1.val 0 ∈ sR := by
      rw [hsR, Finset.mem_sort]; exact hsub (getDmemR' i1.val hi1len)
    have hmem2 : sR'.getD i2.val 0 ∈ sR := by
      rw [hsR, Finset.mem_sort]; exact hsub (getDmemR' i2.val hi2len)
    have heq : sR.idxOf (sR'.getD i1.val 0) = sR.idxOf (sR'.getD i2.val 0) := by
      simpa using congrArg Fin.val h
    have hb1 : sR[sR.idxOf (sR'.getD i1.val 0)]? = some (sR'.getD i1.val 0) :=
      List.getElem?_idxOf hmem1
    have hb2 : sR[sR.idxOf (sR'.getD i2.val 0)]? = some (sR'.getD i2.val 0) :=
      List.getElem?_idxOf hmem2
    rw [heq] at hb1
    have hval : sR'.getD i1.val 0 = sR'.getD i2.val 0 := by
      have := hb1.symm.trans hb2
      exact (Option.some.injEq _ _ ▸ this)
    have hnd : sR'.Nodup := by rw [hsR']; exact Finset.sort_nodup _ _
    rw [List.getD_eq_getElem _ _ hi1len, List.getD_eq_getElem _ _ hi2len] at hval
    exact (List.Nodup.getElem_inj_iff hnd).mp hval
  · intro j1 j2 h
    apply Fin.ext
    simpa using congrArg Fin.val h
  · intro i j
    simp only [extract]
    have hi : i.val < R'.card := by simpa [extract] using i.isLt
    have hilen : i.val < sR'.length := by rw [hsR', Finset.length_sort]; exact hi
    have hvmem : sR'.getD i.val 0 ∈ sR := by
      rw [hsR, Finset.mem_sort]; exact hsub (getDmemR' i.val hilen)
    have hrowval : sR.getD (sR.idxOf (sR'.getD i.val 0)) 0 = sR'.getD i.val 0 := by
      have hidx : sR.idxOf (sR'.getD i.val 0) < sR.length := by
        rw [List.idxOf_lt_length_iff]; exact hvmem
      rw [List.getD_eq_getElem _ _ hidx]
      have hb : sR[sR.idxOf (sR'.getD i.val 0)]? = some (sR'.getD i.val 0) :=
        List.getElem?_idxOf hvmem
      rw [List.getElem?_eq_getElem hidx] at hb
      exact (Option.some.injEq _ _ ▸ hb)
    simp only [hsR, hsR'] at hrowval ⊢
    simp only [hrowval]

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

/-- A matrix with `0` rows has communication complexity `0`. -/
private theorem Dmat_zero_of_m_zero (A : BoolMat) (h : A.m = 0) : Dmat A = 0 := by
  have hmem : (0 : ℕ) ∈ AchievableCosts A.e := by
    refine ⟨Protocol.leaf false, rfl, ?_⟩
    intro x y
    have := x.isLt; omega
  unfold Dmat D
  exact Nat.le_zero.mp (Nat.sInf_le hmem)

/-- A matrix with `0` columns has communication complexity `0`. -/
private theorem Dmat_zero_of_n_zero (A : BoolMat) (h : A.n = 0) : Dmat A = 0 := by
  have hmem : (0 : ℕ) ∈ AchievableCosts A.e := by
    refine ⟨Protocol.leaf false, rfl, ?_⟩
    intro x y
    have := y.isLt; omega
  unfold Dmat D
  exact Nat.le_zero.mp (Nat.sInf_le hmem)

/-- In the degenerate dimension cases, the right-hand bracket complexity is `0`. -/
private theorem DSet_zero_of_dmat_zero (Φ : Set BoolMat)
    (h : ∀ g ∈ Φ, Dmat g = 0) : DSet Φ = 0 := by
  unfold DSet
  rcases Set.eq_empty_or_nonempty Φ with hΦ | ⟨g₀, hg₀⟩
  · rw [show {c : ℕ | ∃ M ∈ Φ, Dmat M = c} = ∅ from ?_]
    · exact Nat.sInf_empty
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro c ⟨M, hM, _⟩
      rw [hΦ] at hM; exact hM
  · apply Nat.le_zero.mp
    apply Nat.sInf_le
    exact ⟨g₀, hg₀, h g₀ hg₀⟩

/-- The left bracket `[⟨M⟩^p]_{1, α·x, y}` is nonempty when `m, n, p ≥ 1`,
`α·x ≤ 1` and `y ≤ 1`. Witnessed by taking the first `⌈(m·p)·αx⌉` rows and
first `⌈(n^p)·y⌉` columns. -/
private theorem left_bracket_nonempty (M : BoolMat) (p : ℕ) (α x y : ℝ)
    (N : BoolMat) (hN : N = interlace M p)
    (hmpos : 0 < M.m) (hnpos : 0 < M.n) (hp1 : 1 ≤ p)
    (hαx1 : α * x ≤ 1) (hy1 : y ≤ 1) :
    (bracket N 1 (α * x) y).Nonempty := by
  classical
  -- `N.m = M.m * p > 0`, `N.n = M.n ^ p > 0`.
  have hNmpos : 0 < N.m := by
    rw [hN]; show 0 < M.m * p; exact Nat.mul_pos hmpos hp1
  have hNnpos : 0 < N.n := by
    rw [hN]; show 0 < M.n ^ p; exact pow_pos hnpos p
  -- Witness row and column sets.
  set Rc : ℕ := ⌈((N.m : ℕ) : ℝ) * (α * x)⌉₊ with hRcdef
  set Cc : ℕ := ⌈((N.n : ℕ) : ℝ) * y⌉₊ with hCcdef
  -- `Rc ≤ N.m` from `α·x ≤ 1`.
  have hRc_le : Rc ≤ N.m := by
    rw [hRcdef]
    apply Nat.ceil_le.mpr
    have hle : ((N.m : ℕ) : ℝ) * (α * x) ≤ ((N.m : ℕ) : ℝ) * 1 := by
      apply mul_le_mul_of_nonneg_left hαx1; positivity
    simpa using hle
  -- `Cc ≤ N.n` from `y ≤ 1`.
  have hCc_le : Cc ≤ N.n := by
    rw [hCcdef]
    apply Nat.ceil_le.mpr
    have hle : ((N.n : ℕ) : ℝ) * y ≤ ((N.n : ℕ) : ℝ) * 1 := by
      apply mul_le_mul_of_nonneg_left hy1; positivity
    simpa using hle
  refine ⟨extract (interlace N 1) (Finset.range Rc) (Finset.range Cc), ?_⟩
  refine ⟨Finset.range Rc, Finset.range Cc, ?_, ?_, ?_, ?_, rfl⟩
  · -- `R ⊆ range (N.m * 1)`.
    rw [Nat.mul_one]
    exact Finset.range_subset_range.mpr hRc_le
  · -- equipartition at `p = 1` ⟺ `|R| = ⌈N.m·(α·x)⌉`.
    rw [equipartition_one_iff (Finset.range Rc) N.m ((N.m : ℝ) * (α * x))
        (Finset.range_subset_range.mpr hRc_le)]
    rw [Finset.card_range, hRcdef]
  · -- `C ⊆ range (N.n ^ 1)`.
    rw [pow_one]
    exact Finset.range_subset_range.mpr hCc_le
  · -- `|C| = ⌈N.n^1·y⌉`.
    rw [Finset.card_range, hCcdef, pow_one]

/-- From the Balancing-Lemma column bound `|D| ≥ |C| / n^{p-ℓ}` together with
`|C| = ⌈n^p · y⌉` and `ℓ ≤ p`, deduce `⌈n^ℓ · y⌉ ≤ |D|`. -/
private theorem column_density_bound (M : BoolMat) (p ℓ : ℕ) (y : ℝ)
    (C D : Finset ℕ) (hnpos : 0 < M.n) (hℓp : ℓ ≤ p)
    (hCcard : C.card = ⌈((M.n ^ p : ℕ) : ℝ) * y⌉₊)
    (hD_card : (D.card : ℝ) ≥ (C.card : ℝ) / (M.n : ℝ) ^ (p - ℓ)) :
    ⌈((M.n ^ ℓ : ℕ) : ℝ) * y⌉₊ ≤ D.card := by
  rw [Nat.ceil_le]
  have hnR : (0 : ℝ) < (M.n : ℝ) := by exact_mod_cast hnpos
  have hpow_pos : (0 : ℝ) < (M.n : ℝ) ^ (p - ℓ) := by positivity
  -- `n^p = n^ℓ · n^{p-ℓ}`.
  have hsplit : (M.n : ℝ) ^ p = (M.n : ℝ) ^ ℓ * (M.n : ℝ) ^ (p - ℓ) := by
    rw [← pow_add]; congr 1; omega
  -- `(M.n^ℓ : ℕ) cast = (M.n : ℝ)^ℓ`.
  have hcastℓ : ((M.n ^ ℓ : ℕ) : ℝ) = (M.n : ℝ) ^ ℓ := by push_cast; ring
  have hcastp : ((M.n ^ p : ℕ) : ℝ) = (M.n : ℝ) ^ p := by push_cast; ring
  -- `|C| ≥ n^p · y`.
  have hC_lb : ((M.n : ℝ) ^ p) * y ≤ (C.card : ℝ) := by
    rw [hCcard, ← hcastp]; exact Nat.le_ceil _
  -- Chain: `n^ℓ·y ≤ |C|/n^{p-ℓ} ≤ |D|`.
  rw [hcastℓ]
  refine le_trans ?_ hD_card
  rw [le_div_iff₀ hpow_pos]
  calc (M.n : ℝ) ^ ℓ * y * (M.n : ℝ) ^ (p - ℓ)
      = (M.n : ℝ) ^ p * y := by rw [hsplit]; ring
    _ ≤ (C.card : ℝ) := hC_lb

/-! ### Helpers for Lemma 4.2 (Monotonicity) -/

/-- `⌈m·x⌉ ≤ m` when `0 ≤ x ≤ 1`. -/
private theorem ceil_mul_le (m : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ⌈(m : ℝ) * x⌉₊ ≤ m := by
  apply Nat.ceil_le.mpr
  calc (m : ℝ) * x ≤ (m : ℝ) * 1 := by
        apply mul_le_mul_of_nonneg_left hx1; positivity
    _ = (m : ℝ) := by ring
    _ = ((m : ℕ) : ℝ) := by norm_num

/-- **SublemmaBracketNonempty.** With `m, n ≥ 1`, `p ≥ 1`, `0 ≤ x ≤ 1`, `0 ≤ y ≤ 1`,
the bracket `[M]_{p,x,y}` is nonempty. Witness: the first `⌈mx⌉` rows of each of
the `p` blocks, and the first `⌈n^p y⌉` columns. -/
private theorem bracket_nonempty (M : BoolMat) (p : ℕ) (x y : ℝ)
    (hmpos : 0 < M.m) (hnpos : 0 < M.n) (hp1 : 1 ≤ p)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (bracket M p x y).Nonempty := by
  classical
  set T : ℕ := ⌈(M.m : ℝ) * x⌉₊ with hTdef
  have hTm : T ≤ M.m := ceil_mul_le M.m x hx0 hx1
  -- Row witness: i % M.m < T, restricted to range (M.m * p).
  set R : Finset ℕ := (Finset.range (M.m * p)).filter (fun i => i % M.m < T) with hRdef
  -- Column witness.
  set Cc : ℕ := ⌈((M.n ^ p : ℕ) : ℝ) * y⌉₊ with hCcdef
  have hCc_le : Cc ≤ M.n ^ p := by
    rw [hCcdef]
    apply Nat.ceil_le.mpr
    calc ((M.n ^ p : ℕ) : ℝ) * y ≤ ((M.n ^ p : ℕ) : ℝ) * 1 := by
          apply mul_le_mul_of_nonneg_left hy1; positivity
      _ = ((M.n ^ p : ℕ) : ℝ) := by ring
  refine ⟨extract (interlace M p) R (Finset.range Cc), R, Finset.range Cc, ?_, ?_, ?_, ?_, rfl⟩
  · exact Finset.filter_subset _ _
  · -- equipartition: each block γ has exactly T elements
    intro γ hγ
    -- The block filter = {i : M.m*γ ≤ i < M.m*(γ+1), i ∈ range(M.m*p), i % M.m < T}
    have hcard : (R.filter (fun i => M.m * γ ≤ i ∧ i < M.m * (γ + 1))).card = T := by
      rw [hRdef]
      -- combine filters
      rw [Finset.filter_filter]
      -- the set equals the image of range T under (r ↦ M.m*γ + r)
      have himg : ((Finset.range (M.m * p)).filter
          (fun i => i % M.m < T ∧ M.m * γ ≤ i ∧ i < M.m * (γ + 1)))
          = (Finset.range T).image (fun r => M.m * γ + r) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
        constructor
        · rintro ⟨hir, hmod, hlo, hhi⟩
          have hexp : M.m * (γ + 1) = M.m * γ + M.m := by ring
          refine ⟨i - M.m * γ, ?_, ?_⟩
          · -- i - M.m*γ < T
            have hdiff : i - M.m * γ < M.m := by omega
            have heqmod : i % M.m = i - M.m * γ := by
              have hi_eq : i = M.m * γ + (i - M.m * γ) := by omega
              conv_lhs => rw [hi_eq]
              rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hdiff]
            omega
          · omega
        · rintro ⟨r, hrT, rfl⟩
          have hrm : r < M.m := lt_of_lt_of_le hrT hTm
          refine ⟨?_, ?_, ?_, ?_⟩
          · -- M.m*γ + r < M.m*p
            have : M.m * γ + r < M.m * (γ + 1) := by ring_nf; omega
            calc M.m * γ + r < M.m * (γ + 1) := this
              _ ≤ M.m * p := Nat.mul_le_mul_left _ (by omega)
          · rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hrm]; exact hrT
          · omega
          · have : M.m * γ + r < M.m * (γ + 1) := by ring_nf; omega
            exact this
      rw [himg]
      rw [Finset.card_image_of_injective _ (fun a b h => by omega)]
      exact Finset.card_range T
    rw [hcard]
  · exact Finset.range_subset_range.mpr hCc_le
  · rw [Finset.card_range, hCcdef]

/-- **SublemmaDegenerateM.** With `M.m = 0`, every bracket member has `0` rows,
so `DSet (bracket M p x y) = 0`. -/
private theorem DSet_bracket_zero_of_m_zero (M : BoolMat) (p : ℕ) (x y : ℝ)
    (hm0 : M.m = 0) : DSet (bracket M p x y) = 0 := by
  apply DSet_zero_of_dmat_zero
  rintro g ⟨R, C, hR, _, _, _, rfl⟩
  have hRempty : R = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    have := hR hi
    rw [hm0, Nat.zero_mul] at this
    simp at this
  apply Dmat_zero_of_m_zero
  simp [extract, hRempty]

/-- **SublemmaDegenerateN.** With `M.n = 0` and `p ≥ 1`, every bracket member has
`0` columns, so `DSet (bracket M p x y) = 0`. -/
private theorem DSet_bracket_zero_of_n_zero (M : BoolMat) (p : ℕ) (x y : ℝ)
    (hn0 : M.n = 0) (hp1 : 1 ≤ p) : DSet (bracket M p x y) = 0 := by
  apply DSet_zero_of_dmat_zero
  rintro g ⟨R, C, _, _, hC, _, rfl⟩
  have hCempty : C = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro j hj
    have := hC hj
    rw [hn0, Nat.zero_pow (by omega : 0 < p)] at this
    simp at this
  apply Dmat_zero_of_n_zero
  simp [extract, hCempty]

/-- **Step 3 (Column-density direction).**  `D([M]_{p,x,y'}) ≤ D([M]_{p,x,y})` for
`0 < y' ≤ y ≤ 1`, given `m, n ≥ 1`, `p ≥ 1`, `0 < x ≤ 1`. -/
private theorem mono_col (M : BoolMat) (p : ℕ) (x y' y : ℝ)
    (hmpos : 0 < M.m) (hnpos : 0 < M.n) (hp1 : 1 ≤ p)
    (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy'0 : 0 < y') (hy'y : y' ≤ y) (hy1 : y ≤ 1) :
    DSet (bracket M p x y') ≤ DSet (bracket M p x y) := by
  classical
  apply subgames_are_easier
  · exact bracket_nonempty M p x y hmpos hnpos hp1 hx0.le hx1 (by linarith) hy1
  · intro g hg
    obtain ⟨R, C, hR, hRpart, hC, hCcard, hgeq⟩ := hg
    -- ⌈n^p y'⌉ ≤ |C| = ⌈n^p y⌉
    have hle : ⌈((M.n ^ p : ℕ) : ℝ) * y'⌉₊ ≤ C.card := by
      rw [hCcard]
      apply Nat.ceil_le_ceil
      apply mul_le_mul_of_nonneg_left hy'y
      positivity
    obtain ⟨C', hC'sub, hC'card⟩ := Finset.exists_subset_card_eq hle
    refine ⟨extract (interlace M p) R C', ?_, ?_⟩
    · refine ⟨R, C', hR, hRpart, subset_trans hC'sub hC, hC'card, rfl⟩
    · rw [hgeq]
      exact extract_col_subset_subgame (interlace M p) R C' C hC'sub

/-- **SublemmaThinEquipartition (existential form).** From an `m,Tblk,p`-style row set
(each block γ<p has exactly `Tblk` elements) with `T' ≤ Tblk`, there is a subset keeping
exactly `T'` elements in each block. -/
private theorem thin_exists (m p Tblk T' : ℕ) (R : Finset ℕ)
    (hT'T : T' ≤ Tblk)
    (hblocks : ∀ γ < p, (R.filter (fun i => m * γ ≤ i ∧ i < m * (γ + 1))).card = Tblk) :
    ∃ R' ⊆ R, ∀ γ < p, (R'.filter (fun i => m * γ ≤ i ∧ i < m * (γ + 1))).card = T' := by
  classical
  have hpick : ∀ γ : ℕ, ∃ s : Finset ℕ,
      (γ < p → s ⊆ (R.filter (fun i => m * γ ≤ i ∧ i < m * (γ + 1))) ∧ s.card = T') := by
    intro γ
    by_cases hγ : γ < p
    · obtain ⟨s, hssub, hscard⟩ := Finset.exists_subset_card_eq
        (by rw [hblocks γ hγ]; exact hT'T :
          T' ≤ (R.filter (fun i => m * γ ≤ i ∧ i < m * (γ + 1))).card)
      exact ⟨s, fun _ => ⟨hssub, hscard⟩⟩
    · exact ⟨∅, fun h => absurd h hγ⟩
  choose pick hpick using hpick
  refine ⟨(Finset.range p).biUnion pick, ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_biUnion] at hi
    obtain ⟨γ, hγ, hiγ⟩ := hi
    rw [Finset.mem_range] at hγ
    have := (hpick γ hγ).1 hiγ
    rw [Finset.mem_filter] at this
    exact this.1
  · intro γ hγ
    have hfilter : ((Finset.range p).biUnion pick).filter
        (fun i => m * γ ≤ i ∧ i < m * (γ + 1)) = pick γ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
      constructor
      · rintro ⟨⟨δ, hδ, hiδ⟩, hlo, hhi⟩
        have hib : i ∈ (R.filter (fun i => m * δ ≤ i ∧ i < m * (δ + 1))) :=
          (hpick δ hδ).1 hiδ
        rw [Finset.mem_filter] at hib
        obtain ⟨_, hlo', hhi'⟩ := hib
        have hδγ : δ = γ := by
          rcases Nat.eq_zero_or_pos m with hm0 | hmpos
          · simp [hm0] at hhi'
          · have h1 : i / m = δ :=
              Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact hlo') (by rw [Nat.mul_comm]; exact hhi')
            have h2 : i / m = γ :=
              Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact hlo) (by rw [Nat.mul_comm]; exact hhi)
            omega
        rw [← hδγ]; exact hiδ
      · intro hi
        have hib : i ∈ (R.filter (fun i => m * γ ≤ i ∧ i < m * (γ + 1))) :=
          (hpick γ hγ).1 hi
        rw [Finset.mem_filter] at hib
        exact ⟨⟨γ, hγ, hi⟩, hib.2⟩
    rw [hfilter]
    exact (hpick γ hγ).2

/-- **Step 2 (Row-density direction).**  `D([M]_{p,x',y'}) ≤ D([M]_{p,x,y'})` for
`0 < x' ≤ x ≤ 1`, given `m, n ≥ 1`, `p ≥ 1`, `0 < y' ≤ 1`.

The thinned row set keeps, in each block, exactly `T' = ⌈mx'⌉` elements. -/
private theorem mono_row (M : BoolMat) (p : ℕ) (x' x y' : ℝ)
    (hmpos : 0 < M.m) (hnpos : 0 < M.n) (hp1 : 1 ≤ p)
    (hx'0 : 0 < x') (hx'x : x' ≤ x) (hx1 : x ≤ 1)
    (hy'0 : 0 < y') (hy'1 : y' ≤ 1) :
    DSet (bracket M p x' y') ≤ DSet (bracket M p x y') := by
  classical
  have hx0 : 0 < x := lt_of_lt_of_le hx'0 hx'x
  apply subgames_are_easier
  · exact bracket_nonempty M p x y' hmpos hnpos hp1 hx0.le hx1 hy'0.le hy'1
  · intro g hg
    obtain ⟨R, C, hR, hRpart, hC, hCcard, hgeq⟩ := hg
    -- T' = ⌈m x'⌉ ≤ T = ⌈m x⌉.
    set T : ℕ := ⌈(M.m : ℝ) * x⌉₊ with hTdef
    set T' : ℕ := ⌈(M.m : ℝ) * x'⌉₊ with hT'def
    have hT'T : T' ≤ T := by
      rw [hT'def, hTdef]
      apply Nat.ceil_le_ceil
      apply mul_le_mul_of_nonneg_left hx'x; positivity
    -- Each block of R has card T.
    have hblocks : ∀ γ < p, (R.filter (fun i => M.m * γ ≤ i ∧ i < M.m * (γ + 1))).card = T := by
      intro γ hγ
      have := hRpart γ hγ
      rw [hTdef]; exact this
    -- Thin R to R' keeping T' per block.
    obtain ⟨R', hR'sub, hR'blocks⟩ := thin_exists M.m p T T' R hT'T hblocks
    refine ⟨extract (interlace M p) R' C, ?_, ?_⟩
    · refine ⟨R', C, subset_trans hR'sub hR, ?_, hC, hCcard, rfl⟩
      -- R' is m,(M.m*x'),p-equipartitioned
      intro γ hγ
      rw [hR'blocks γ hγ, hT'def]
    · rw [hgeq]
      exact extract_row_subset_subgame (interlace M p) R' R C hR'sub

/-- `qElem (range p') γ = γ` for `γ < p'`. -/
private theorem qElem_range (p' γ : ℕ) (hγ : γ < p') :
    Proof.Types.QProjection.qElem (Finset.range p') γ = γ := by
  unfold Proof.Types.QProjection.qElem
  rw [Finset.sort_range]; simp [hγ]

/-- Membership characterization of the projected row set `S` for `Q = range p'`:
`x ∈ S ↔ ∃ γ < p', ∃ r < m, x = m*γ + r ∧ (m*γ + r) ∈ R`. -/
private theorem qproj_S_mem (R C : Finset ℕ) (m n p p' : ℕ) (hp' : 1 ≤ p') (x : ℕ) :
    x ∈ (Proof.Types.QProjection.qProjection R C m n p (Finset.range p')).1
      ↔ ∃ γ < p', ∃ r < m, x = m * γ + r ∧ (m * γ + r) ∈ R := by
  classical
  have hne : (Finset.range p') ≠ ∅ := by
    rw [Finset.nonempty_iff_ne_empty.symm]; exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  unfold Proof.Types.QProjection.qProjection
  simp only [hne, if_false]
  rw [Finset.card_range, Finset.mem_image]
  constructor
  · rintro ⟨pr, hpr, rfl⟩
    rw [Finset.mem_filter, show (Finset.range p').product (Finset.range m)
          = (Finset.range p') ×ˢ (Finset.range m) from rfl,
      Finset.mem_product, Finset.mem_range, Finset.mem_range] at hpr
    obtain ⟨⟨hγ, hr⟩, hmem⟩ := hpr
    rw [qElem_range p' pr.1 hγ] at hmem
    exact ⟨pr.1, hγ, pr.2, hr, rfl, hmem⟩
  · rintro ⟨γ, hγ, r, hr, rfl, hmem⟩
    refine ⟨(γ, r), ?_, rfl⟩
    rw [Finset.mem_filter, show (Finset.range p').product (Finset.range m)
          = (Finset.range p') ×ˢ (Finset.range m) from rfl,
      Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨hγ, hr⟩, by rw [qElem_range p' γ hγ]; exact hmem⟩

/-- The projected row set `S ⊆ range (m * p')`. -/
private theorem qproj_S_range (R C : Finset ℕ) (m n p p' : ℕ) (hp' : 1 ≤ p')
    (S : Finset ℕ) (hSdef : S = (Proof.Types.QProjection.qProjection R C m n p (Finset.range p')).1) :
    S ⊆ Finset.range (m * p') := by
  intro x hx
  rw [hSdef, qproj_S_mem R C m n p p' hp'] at hx
  obtain ⟨γ, hγ, r, hr, rfl, _⟩ := hx
  rw [Finset.mem_range]
  calc m * γ + r < m * γ + m := by omega
    _ = m * (γ + 1) := by ring
    _ ≤ m * p' := Nat.mul_le_mul_left _ (by omega)

/-- The projected row set `S` is `m, ⌈m·x'⌉, p'`-equipartitioned. -/
private theorem qproj_S_equipartition (R C : Finset ℕ) (m n p p' : ℕ) (x' : ℝ)
    (hpp : p' ≤ p)
    (S : Finset ℕ) (hSdef : S = (Proof.Types.QProjection.qProjection R C m n p (Finset.range p')).1)
    (R' : Finset ℕ) (hReq : IsEquipartitioned R' m ((m : ℝ) * x') p)
    (hRR : R = R') :
    IsEquipartitioned S m ((m : ℝ) * x') p' := by
  classical
  subst hRR
  intro β hβ
  -- block β of S equals image of {r < m : m*β+r ∈ R} under (r ↦ m*β+r)
  have hp' : 1 ≤ p' := by omega
  have hblock : (S.filter (fun i => m * β ≤ i ∧ i < m * (β + 1)))
      = ((Finset.range m).filter (fun r => (m * β + r) ∈ R)).image (fun r => m * β + r) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hiS, hlo, hhi⟩
      rw [hSdef, qproj_S_mem R C m n p p' hp'] at hiS
      obtain ⟨γ, hγ, r, hr, rfl, hmem⟩ := hiS
      -- m*β ≤ m*γ+r < m*(β+1) with r<m ⟹ γ=β
      have hγβ : γ = β := by
        rcases Nat.lt_trichotomy γ β with h | h | h
        · exfalso
          have : m * γ + r < m * β := by
            calc m * γ + r < m * γ + m := by omega
              _ = m * (γ + 1) := by ring
              _ ≤ m * β := Nat.mul_le_mul_left _ (by omega)
          omega
        · exact h
        · exfalso
          have : m * (β + 1) ≤ m * γ := Nat.mul_le_mul_left _ (by omega)
          have hr2 : m * (β + 1) = m * β + m := by ring
          omega
      subst hγβ
      exact ⟨r, ⟨hr, hmem⟩, rfl⟩
    · rintro ⟨r, ⟨hr, hmem⟩, rfl⟩
      refine ⟨?_, by omega, ?_⟩
      · rw [hSdef, qproj_S_mem R C m n p p' hp']
        exact ⟨β, by omega, r, hr, rfl, hmem⟩
      · have hr2 : m * (β + 1) = m * β + m := by ring
        omega
  rw [hblock]
  rw [Finset.card_image_of_injective _ (fun a b h => by omega)]
  -- now |{r<m : m*β+r∈R}| = |R ∩ block β| = ⌈m·x'⌉
  have hbij : ((Finset.range m).filter (fun r => (m * β + r) ∈ R)).card
      = (R.filter (fun i => m * β ≤ i ∧ i < m * (β + 1))).card := by
    apply Finset.card_bij (fun r _ => m * β + r)
    · intro r hr
      rw [Finset.mem_filter, Finset.mem_range] at hr
      rw [Finset.mem_filter]
      refine ⟨hr.2, by omega, ?_⟩
      have : m * (β + 1) = m * β + m := by ring
      omega
    · intro a ha b hb hab; omega
    · intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨hiR, hlo, hhi⟩ := hi
      refine ⟨i - m * β, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_range]
        have : m * (β + 1) = m * β + m := by ring
        refine ⟨by omega, ?_⟩
        rw [show m * β + (i - m * β) = i by omega]; exact hiR
      · omega
  rw [hbij]
  exact hReq β (lt_of_lt_of_le hβ hpp)

/-- Base-`n` digit-weighted sum of the low `p'` digits equals `c mod n^{p'}`. -/
private theorem qproj_digsum_eq_mod (n p' c : ℕ) :
    (∑ γ ∈ Finset.range p', Proof.Types.QProjection.digit c n γ * n ^ γ) = c % n ^ p' := by
  induction p' with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    unfold Proof.Types.QProjection.digit
    rw [pow_succ, Nat.mod_mul]; ring

/-- For `Q = range p'`, the column projection `D = qProjection.2` equals the image of
`C` under `c ↦ c mod n^{p'}`. -/
private theorem qproj_col_eq_image_mod (R C : Finset ℕ) (m n p p' : ℕ) (hp' : 1 ≤ p') :
    (Proof.Types.QProjection.qProjection R C m n p (Finset.range p')).2
      = C.image (fun c => c % n ^ p') := by
  classical
  have hne : (Finset.range p') ≠ ∅ := by
    rw [Finset.nonempty_iff_ne_empty.symm]; exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  unfold Proof.Types.QProjection.qProjection
  simp only [hne, if_false]
  apply Finset.image_congr
  intro c _
  simp only [Finset.card_range]
  -- qElem (range p') γ = γ for γ < p'
  have hqe : ∀ γ ∈ Finset.range p',
      Proof.Types.QProjection.digit c n (Proof.Types.QProjection.qElem (Finset.range p') γ) * n ^ γ
        = Proof.Types.QProjection.digit c n γ * n ^ γ := by
    intro γ hγ
    rw [Finset.mem_range] at hγ
    rw [qElem_range p' γ hγ]
  rw [Finset.sum_congr rfl hqe]
  exact qproj_digsum_eq_mod n p' c

/-- **Step 1 (Count direction).**  `D([M]_{p',x',y'}) ≤ D([M]_{p,x',y'})` for
`1 ≤ p' ≤ p`, given `m, n ≥ 1`, `0 < x' ≤ 1`, `0 < y' ≤ 1`. -/
private theorem mono_count (M : BoolMat) (p' p : ℕ) (x' y' : ℝ)
    (hmpos : 0 < M.m) (hnpos : 0 < M.n) (hp' : 1 ≤ p') (hpp : p' ≤ p)
    (hx'0 : 0 < x') (hx'1 : x' ≤ 1) (hy'0 : 0 < y') (hy'1 : y' ≤ 1) :
    DSet (bracket M p' x' y') ≤ DSet (bracket M p x' y') := by
  classical
  have hp1 : 1 ≤ p := le_trans hp' hpp
  have hnR : (0 : ℝ) < (M.n : ℝ) := by exact_mod_cast hnpos
  apply subgames_are_easier
  · exact bracket_nonempty M p x' y' hmpos hnpos hp1 hx'0.le hx'1 hy'0.le hy'1
  · intro g hg
    obtain ⟨R, C, hR, hRpart, hC, hCcard, hgeq⟩ := hg
    -- abbreviations
    set q := p - p' with hq
    have hpsum : p' + q = p := by omega
    -- target column count
    set Tcol : ℕ := ⌈((M.n ^ p' : ℕ) : ℝ) * y'⌉₊ with hTcoldef
    -- Pigeonhole: classify columns of C by high part c / n^p'. There are ≤ n^q classes.
    -- Use the real-valued pigeonhole with bound b = (n^p' : ℝ) * y'.
    have hmaps : ∀ c ∈ C, c / M.n ^ p' ∈ Finset.range (M.n ^ q) := by
      intro c hc
      have := hC hc
      rw [Finset.mem_range] at this ⊢
      -- c < n^p = n^p' · n^q  ⟹  c / n^p' < n^q
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc c < M.n ^ p := this
        _ = M.n ^ p' * M.n ^ q := by rw [← pow_add, hpsum]
        _ = M.n ^ q * M.n ^ p' := by ring
    have htne : (Finset.range (M.n ^ q)).Nonempty := by
      refine ⟨0, ?_⟩; rw [Finset.mem_range]; positivity
    -- nsmul bound: (n^q) • ((n^p' : ℝ) * y') ≤ |C|
    have hsmul : (Finset.range (M.n ^ q)).card • (((M.n ^ p' : ℕ) : ℝ) * y') ≤ (C.card : ℝ) := by
      rw [Finset.card_range, nsmul_eq_mul]
      rw [hCcard]
      refine le_trans ?_ (Nat.le_ceil _)
      push_cast
      rw [← mul_assoc, ← pow_add]
      rw [show q + p' = p by omega]
    obtain ⟨w, _hw, hwcard⟩ :=
      Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps htne hsmul
    -- the fiber C⋆
    set Cstar : Finset ℕ := {c ∈ C | c / M.n ^ p' = w} with hCstardef
    have hCstar_sub : Cstar ⊆ C := by intro c hc; rw [hCstardef, Finset.mem_filter] at hc; exact hc.1
    have hCstar_lb : ((M.n ^ p' : ℕ) : ℝ) * y' ≤ (Cstar.card : ℝ) := by
      rw [hCstardef]; exact hwcard
    have hTcol_le : Tcol ≤ Cstar.card := by
      rw [hTcoldef]; exact Nat.ceil_le.mpr hCstar_lb
    -- choose C' ⊆ Cstar with |C'| = Tcol
    obtain ⟨C', hC'sub_star, hC'card⟩ := Finset.exists_subset_card_eq hTcol_le
    have hC'sub : C' ⊆ C := subset_trans hC'sub_star hCstar_sub
    -- all of C' lies in the single fiber w
    have hC'fiber : ∀ c ∈ C', c / M.n ^ p' = w := by
      intro c hc
      have := hC'sub_star hc
      rw [hCstardef, Finset.mem_filter] at this
      exact this.2
    -- Now the Q-projection with Q = range p'.
    set S : Finset ℕ := (Proof.Types.QProjection.qProjection R C' M.m M.n p (Finset.range p')).1 with hSdef
    set D : Finset ℕ := (Proof.Types.QProjection.qProjection R C' M.m M.n p (Finset.range p')).2 with hDdef
    -- D = image of C' under (· % n^p')
    have hDimg : D = C'.image (fun c => c % M.n ^ p') := by
      rw [hDdef]; exact qproj_col_eq_image_mod R C' M.m M.n p p' hp'
    -- The map c ↦ c % n^p' is injective on C' (single fiber).
    have hDcard : D.card = Tcol := by
      rw [hDimg, ← hC'card]
      apply Finset.card_image_of_injOn
      intro a ha b hb hab
      -- a % n^p' = b % n^p', a / n^p' = b / n^p' = w  ⟹  a = b
      have ha2 := hC'fiber a ha
      have hb2 := hC'fiber b hb
      have hdeca : a = M.n ^ p' * (a / M.n ^ p') + a % M.n ^ p' := (Nat.div_add_mod a (M.n ^ p')).symm
      have hdecb : b = M.n ^ p' * (b / M.n ^ p') + b % M.n ^ p' := (Nat.div_add_mod b (M.n ^ p')).symm
      simp only [] at hab
      rw [hdeca, hdecb, ha2, hb2, hab]
    -- The projection lemma: extract (interlace M p') S D ⊑ extract (interlace M p) R C'.
    have hC'_range : C' ⊆ Finset.range (M.n ^ p) := subset_trans hC'sub hC
    have hQrange : (Finset.range p') ⊆ Finset.range p := Finset.range_subset_range.mpr hpp
    have hQne : (Finset.range p').Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
    have hQcard : (Finset.range p').card = p' := Finset.card_range p'
    have hproj := Proof.Projections.projection_lemma M p R C' hR hC'_range (Finset.range p') hQrange hQne
    -- rewrite Q.card = p' in the projection
    rw [hQcard] at hproj
    rw [← hSdef, ← hDdef] at hproj
    -- Assemble: g' = extract (interlace M p') S D
    refine ⟨extract (interlace M p') S D, ?_, ?_⟩
    · -- membership in bracket M p' x' y'
      refine ⟨S, D, ?_, ?_, ?_, ?_, rfl⟩
      · -- S ⊆ range (M.m * p')
        exact qproj_S_range R C' M.m M.n p p' hp' S hSdef
      · -- S is M.m, ⌈M.m x'⌉, p'-equipartitioned
        exact qproj_S_equipartition R C' M.m M.n p p' x' hpp S hSdef R hRpart rfl
      · -- D ⊆ range (M.n ^ p')
        rw [hDimg]
        intro d hd
        rw [Finset.mem_image] at hd
        obtain ⟨c, _, rfl⟩ := hd
        rw [Finset.mem_range]
        exact Nat.mod_lt _ (by positivity)
      · -- |D| = ⌈M.n ^ p' · y'⌉
        rw [hDcard, hTcoldef]
    · -- g' ⊑ g
      rw [hgeq]
      refine isSubgame_trans hproj ?_
      exact extract_col_subset_subgame (interlace M p) R C' C hC'sub

/-- **Lemma 4.2 (Monotonicity Lemma).**  For an `m × n` matrix `M`, integers
`1 ≤ p' ≤ p`, and reals `0 < x' ≤ x ≤ 1`, `0 < y' ≤ y ≤ 1`:
`D([M]_{p',x',y'}) ≤ D([M]_{p,x,y})`. -/
theorem monotonicity (M : BoolMat) (p' p : ℕ) (x' x y' y : ℝ)
    (hp' : 1 ≤ p') (hpp : p' ≤ p)
    (hx'0 : 0 < x') (hx'x : x' ≤ x) (hx1 : x ≤ 1)
    (hy'0 : 0 < y') (hy'y : y' ≤ y) (hy1 : y ≤ 1) :
    DSet (bracket M p' x' y') ≤ DSet (bracket M p x y) := by
  -- Degenerate dimensions handled first.
  rcases Nat.eq_zero_or_pos M.m with hm0 | hmpos
  · rw [DSet_bracket_zero_of_m_zero M p' x' y' hm0]; exact Nat.zero_le _
  rcases Nat.eq_zero_or_pos M.n with hn0 | hnpos
  · rw [DSet_bracket_zero_of_n_zero M p' x' y' hn0 hp']; exact Nat.zero_le _
  have hx'1 : x' ≤ 1 := le_trans hx'x hx1
  have hy'1 : y' ≤ 1 := le_trans hy'y hy1
  have hp1 : 1 ≤ p := le_trans hp' hpp
  have hx0 : 0 < x := lt_of_lt_of_le hx'0 hx'x
  -- Compose the three directions:
  --   (p',x',y') ≤ (p,x',y') ≤ (p,x,y') ≤ (p,x,y)
  calc DSet (bracket M p' x' y')
      ≤ DSet (bracket M p x' y') :=
        mono_count M p' p x' y' hmpos hnpos hp' hpp hx'0 hx'1 hy'0 hy'1
    _ ≤ DSet (bracket M p x y') :=
        mono_row M p x' x y' hmpos hnpos hp1 hx'0 hx'x hx1 hy'0 hy'1
    _ ≤ DSet (bracket M p x y) :=
        mono_col M p x y' y hmpos hnpos hp1 hx0 hx1 hy'0 hy'y hy1

/-- **SublemmaCeilOfIntDivByPow.**  When `0 < n`, the column count
`⌈n^ℓ · (|D|/n^ℓ)⌉₊` equals `|D|`, since `n^ℓ · (|D|/n^ℓ) = |D|` is a natural
number and the ceiling of a natural-number-valued real is that number. -/
private theorem ceil_card_div_pow (n ℓ d : ℕ) (hn : 0 < n) :
    ⌈((n ^ ℓ : ℕ) : ℝ) * ((d : ℝ) / (n : ℝ) ^ ℓ)⌉₊ = d := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpow_pos : (0 : ℝ) < (n : ℝ) ^ ℓ := by positivity
  have hcast : ((n ^ ℓ : ℕ) : ℝ) = (n : ℝ) ^ ℓ := by push_cast; ring
  rw [hcast]
  rw [mul_div_assoc']
  rw [mul_comm, mul_div_assoc]
  rw [div_self (ne_of_gt hpow_pos), mul_one]
  exact Nat.ceil_natCast d

/-- **Lemma 4.3 (Extended Product of Projection Lemma).**  Given
`g = ε(⟨M⟩^p, R, C) ∈ [M]_{p,x,y}` with rows `R`, columns `C`, and a partition
`R = R₁ ∪ R₂`, there exist `ℓ₁, ℓ₂, y₁, y₂, S₁, S₂, D₁, D₂` with `y₁·y₂ ≥ y`,
`ℓ₁ + ℓ₂ = p`, `yᵢ = |Dᵢ| / n^{ℓᵢ}`, and for each `i` with `ℓᵢ ≥ 1`:
`ε(⟨M⟩^{ℓᵢ}, Sᵢ, Dᵢ) ⊑ ε(⟨M⟩^p, Rᵢ, C)` and
`ε(⟨M⟩^{ℓᵢ}, Sᵢ, Dᵢ) ∈ [M]_{ℓᵢ, x/2, yᵢ}`. -/
theorem extended_product_of_projection
    (M : BoolMat) (p : ℕ) (x y : ℝ)
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1) (hn : 1 ≤ M.n)
    (R C : Finset ℕ)
    (hR_sub : R ⊆ Finset.range (M.m * p))
    (hR_equi : IsEquipartitioned R M.m ((M.m : ℝ) * x) p)
    (hC_sub : C ⊆ Finset.range (M.n ^ p))
    (hC_card : C.card = ⌈((M.n ^ p : ℕ) : ℝ) * y⌉₊)
    (R₁ R₂ : Finset ℕ) (hR_union : R₁ ∪ R₂ = R) (hR_disj : Disjoint R₁ R₂) :
    ∃ (ℓ₁ ℓ₂ : ℕ) (y₁ y₂ : ℝ) (S₁ S₂ D₁ D₂ : Finset ℕ),
      y₁ * y₂ ≥ y ∧
      ℓ₁ + ℓ₂ = p ∧
      y₁ = (D₁.card : ℝ) / (M.n : ℝ) ^ ℓ₁ ∧
      y₂ = (D₂.card : ℝ) / (M.n : ℝ) ^ ℓ₂ ∧
      y₁ ≤ 1 ∧ y₂ ≤ 1 ∧
      (1 ≤ ℓ₁ →
        IsSubgame (extract (interlace M ℓ₁) S₁ D₁) (extract (interlace M p) R₁ C) ∧
        (extract (interlace M ℓ₁) S₁ D₁) ∈ bracket M ℓ₁ (x / 2) y₁) ∧
      (1 ≤ ℓ₂ →
        IsSubgame (extract (interlace M ℓ₂) S₂ D₂) (extract (interlace M p) R₂ C) ∧
        (extract (interlace M ℓ₂) S₂ D₂) ∈ bracket M ℓ₂ (x / 2) y₂) := by
  classical
  have hnpos : 0 < M.n := hn
  have hnR : (0 : ℝ) < (M.n : ℝ) := by exact_mod_cast hnpos
  -- Step 1: apply the (strengthened) Product of Projections Lemma (3.21).
  obtain ⟨ℓ₁, ℓ₂, S₁, S₂, D₁, D₂, hℓsum, hcol, hcard1, hcard2, hS₁, hS₂⟩ :=
    Proof.Projections.product_of_projections_lemma_card M p ((M.m : ℝ) * x) hnpos R C
      hR_sub hR_equi hC_sub R₁ R₂ hR_union hR_disj
  -- Abbreviations for the y-values.
  set y₁ : ℝ := (D₁.card : ℝ) / (M.n : ℝ) ^ ℓ₁ with hy1def
  set y₂ : ℝ := (D₂.card : ℝ) / (M.n : ℝ) ^ ℓ₂ with hy2def
  refine ⟨ℓ₁, ℓ₂, y₁, y₂, S₁, S₂, D₁, D₂, ?_, hℓsum, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · -- Step 3: y₁ · y₂ ≥ y.
    -- y₁·y₂ = |D₁||D₂| / n^p ≥ |C| / n^p ≥ n^p·y / n^p = y.
    have hpow_pos₁ : (0 : ℝ) < (M.n : ℝ) ^ ℓ₁ := by positivity
    have hpow_pos₂ : (0 : ℝ) < (M.n : ℝ) ^ ℓ₂ := by positivity
    have hpow_posp : (0 : ℝ) < (M.n : ℝ) ^ p := by positivity
    have hprod : y₁ * y₂ = ((D₁.card : ℝ) * (D₂.card : ℝ)) / (M.n : ℝ) ^ p := by
      rw [hy1def, hy2def, div_mul_div_comm, ← pow_add, hℓsum]
    rw [hprod]
    rw [ge_iff_le, le_div_iff₀ hpow_posp]
    -- goal: y * n^p ≤ |D₁| * |D₂|.
    -- |C| ≤ |D₁||D₂| (as ℕ), and n^p·y ≤ |C| (ceiling).
    have hcolR : (C.card : ℝ) ≤ (D₁.card : ℝ) * (D₂.card : ℝ) := by
      have : (C.card : ℝ) ≤ ((D₁.card * D₂.card : ℕ) : ℝ) := by exact_mod_cast hcol
      rwa [Nat.cast_mul] at this
    have hC_lb : ((M.n ^ p : ℕ) : ℝ) * y ≤ (C.card : ℝ) := by
      rw [hC_card]; exact Nat.le_ceil _
    have hcast : ((M.n ^ p : ℕ) : ℝ) = (M.n : ℝ) ^ p := by push_cast; ring
    rw [hcast] at hC_lb
    calc y * (M.n : ℝ) ^ p = (M.n : ℝ) ^ p * y := by ring
      _ ≤ (C.card : ℝ) := hC_lb
      _ ≤ (D₁.card : ℝ) * (D₂.card : ℝ) := hcolR
  · -- y₁ ≤ 1, from |D₁| ≤ n^ℓ₁.
    rw [hy1def, div_le_one (by positivity)]
    calc (D₁.card : ℝ) ≤ ((M.n ^ ℓ₁ : ℕ) : ℝ) := by exact_mod_cast hcard1
      _ = (M.n : ℝ) ^ ℓ₁ := by push_cast; ring
  · -- y₂ ≤ 1, from |D₂| ≤ n^ℓ₂.
    rw [hy2def, div_le_one (by positivity)]
    calc (D₂.card : ℝ) ≤ ((M.n ^ ℓ₂ : ℕ) : ℝ) := by exact_mod_cast hcard2
      _ = (M.n : ℝ) ^ ℓ₂ := by push_cast; ring
  · -- index-1 clause.
    intro h1
    obtain ⟨hSr, hDr, heq, hsub⟩ := hS₁ h1
    refine ⟨hsub, ?_⟩
    refine ⟨S₁, D₁, hSr, ?_, hDr, ?_, rfl⟩
    · -- equipartition at density x/2: (M.m:ℝ)*(x/2) = ((M.m:ℝ)*x)/2.
      have hT : (M.m : ℝ) * (x / 2) = ((M.m : ℝ) * x) / 2 := by ring
      rw [hT]; exact heq
    · -- column count = |D₁|.
      rw [hy1def]; exact (ceil_card_div_pow M.n ℓ₁ D₁.card hnpos).symm
  · -- index-2 clause.
    intro h2
    obtain ⟨hSr, hDr, heq, hsub⟩ := hS₂ h2
    refine ⟨hsub, ?_⟩
    refine ⟨S₂, D₂, hSr, ?_, hDr, ?_, rfl⟩
    · have hT : (M.m : ℝ) * (x / 2) = ((M.m : ℝ) * x) / 2 := by ring
      rw [hT]; exact heq
    · rw [hy2def]; exact (ceil_card_div_pow M.n ℓ₂ D₂.card hnpos).symm

/-- **Step 3 helper for Lemma 4.4.**  The identity `(n^p)^{ℓ/p} = n^ℓ` over `ℝ`,
valid for all `n ≥ 0` (including `n = 0`, where `1 ≤ ℓ, p` make both sides `0`). -/
private theorem npow_rpow_div (n p ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hp1 : 1 ≤ p) :
    ((n ^ p : ℕ) : ℝ) ^ ((ℓ : ℝ) / (p : ℝ)) = ((n ^ ℓ : ℕ) : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp1
  have hcastp : ((n ^ p : ℕ) : ℝ) = (n : ℝ) ^ (p : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; ring
  have hcastℓ : ((n ^ ℓ : ℕ) : ℝ) = (n : ℝ) ^ (ℓ : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; ring
  rw [hcastp, hcastℓ]
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  field_simp

/-- **Step 3 (column-count bound) for Lemma 4.4.**  Given the maximum-projection
column bound `|D| ≥ |C|^{ℓ/p}` and the bracket constraint `|C| = ⌈n^p · y⌉`, with
`0 ≤ y`, deduce `⌈n^ℓ · y^{ℓ/p}⌉ ≤ |D|`. -/
private theorem max_proj_col_bound (M : BoolMat) (p ℓ : ℕ) (y : ℝ)
    (C D : Finset ℕ) (hℓ1 : 1 ≤ ℓ) (hp1 : 1 ≤ p) (hy0 : 0 ≤ y)
    (hCcard : C.card = ⌈((M.n ^ p : ℕ) : ℝ) * y⌉₊)
    (hD_card : (D.card : ℝ) ≥ Real.rpow (C.card : ℝ) ((ℓ : ℝ) / (p : ℝ))) :
    ⌈((M.n ^ ℓ : ℕ) : ℝ) * Real.rpow y ((ℓ : ℝ) / (p : ℝ))⌉₊ ≤ D.card := by
  set e : ℝ := (ℓ : ℝ) / (p : ℝ) with hedef
  have he0 : 0 ≤ e := by
    rw [hedef]; positivity
  rw [Nat.ceil_le]
  refine le_trans ?_ hD_card
  -- `|C| ≥ n^p · y ≥ 0`
  have hnpy0 : (0 : ℝ) ≤ ((M.n ^ p : ℕ) : ℝ) * y := by positivity
  have hC_lb : ((M.n ^ p : ℕ) : ℝ) * y ≤ (C.card : ℝ) := by
    rw [hCcard]; exact Nat.le_ceil _
  -- monotonicity of `t ↦ t^e` on nonneg base
  have hmono : (((M.n ^ p : ℕ) : ℝ) * y) ^ e ≤ (C.card : ℝ) ^ e :=
    Real.rpow_le_rpow hnpy0 hC_lb he0
  refine le_trans (le_of_eq ?_) hmono
  -- `n^ℓ · y^e = (n^p)^e · y^e = (n^p · y)^e`
  rw [Real.mul_rpow (by positivity) hy0]
  rw [npow_rpow_div M.n p ℓ hℓ1 hp1]
  rfl

/-- Generalized bracket nonemptiness: needs only row-feasibility `⌈m·x⌉ ≤ m`
(any sign of `x`) together with `0 ≤ y ≤ 1`. -/
private theorem bracket_nonempty' (M : BoolMat) (p : ℕ) (x y : ℝ)
    (hmpos : 0 < M.m) (hp1 : 1 ≤ p)
    (hTm : ⌈(M.m : ℝ) * x⌉₊ ≤ M.m) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (bracket M p x y).Nonempty := by
  classical
  set T : ℕ := ⌈(M.m : ℝ) * x⌉₊ with hTdef
  set R : Finset ℕ := (Finset.range (M.m * p)).filter (fun i => i % M.m < T) with hRdef
  set Cc : ℕ := ⌈((M.n ^ p : ℕ) : ℝ) * y⌉₊ with hCcdef
  have hCc_le : Cc ≤ M.n ^ p := by
    rw [hCcdef]
    apply Nat.ceil_le.mpr
    calc ((M.n ^ p : ℕ) : ℝ) * y ≤ ((M.n ^ p : ℕ) : ℝ) * 1 := by
          apply mul_le_mul_of_nonneg_left hy1; positivity
      _ = ((M.n ^ p : ℕ) : ℝ) := by ring
  refine ⟨extract (interlace M p) R (Finset.range Cc), R, Finset.range Cc, ?_, ?_, ?_, ?_, rfl⟩
  · exact Finset.filter_subset _ _
  · intro γ hγ
    have hcard : (R.filter (fun i => M.m * γ ≤ i ∧ i < M.m * (γ + 1))).card = T := by
      rw [hRdef]
      rw [Finset.filter_filter]
      have himg : ((Finset.range (M.m * p)).filter
          (fun i => i % M.m < T ∧ M.m * γ ≤ i ∧ i < M.m * (γ + 1)))
          = (Finset.range T).image (fun r => M.m * γ + r) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
        constructor
        · rintro ⟨hir, hmod, hlo, hhi⟩
          have hexp : M.m * (γ + 1) = M.m * γ + M.m := by ring
          refine ⟨i - M.m * γ, ?_, ?_⟩
          · have hdiff : i - M.m * γ < M.m := by omega
            have heqmod : i % M.m = i - M.m * γ := by
              have hi_eq : i = M.m * γ + (i - M.m * γ) := by omega
              conv_lhs => rw [hi_eq]
              rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hdiff]
            omega
          · omega
        · rintro ⟨r, hrT, rfl⟩
          have hrm : r < M.m := lt_of_lt_of_le hrT hTm
          refine ⟨?_, ?_, ?_, ?_⟩
          · have : M.m * γ + r < M.m * (γ + 1) := by ring_nf; omega
            calc M.m * γ + r < M.m * (γ + 1) := this
              _ ≤ M.m * p := Nat.mul_le_mul_left _ (by omega)
          · rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hrm]; exact hrT
          · omega
          · have : M.m * γ + r < M.m * (γ + 1) := by ring_nf; omega
            exact this
      rw [himg]
      rw [Finset.card_image_of_injective _ (fun a b h => by omega)]
      exact Finset.card_range T
    rw [hcard]
  · exact Finset.range_subset_range.mpr hCc_le
  · rw [Finset.card_range, hCcdef]

/-- Row-infeasibility (`⌈m·x⌉ > m`) makes the bracket empty (when `p ≥ 1`). -/
private theorem bracket_empty_of_row_infeasible (M : BoolMat) (p : ℕ) (x y : ℝ)
    (hp1 : 1 ≤ p) (hTm : M.m < ⌈(M.m : ℝ) * x⌉₊) :
    bracket M p x y = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro g ⟨R, C, hR, hRpart, _, _, _⟩
  -- block 0 of R must have ⌈m·x⌉ elements, but it lives in [0, m), so ≤ m.
  have hblk := hRpart 0 (by omega)
  have hsub : (R.filter (fun i => M.m * 0 ≤ i ∧ i < M.m * (0 + 1)))
      ⊆ Finset.range M.m := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_range]; omega
  have hle : (R.filter (fun i => M.m * 0 ≤ i ∧ i < M.m * (0 + 1))).card ≤ M.m := by
    calc _ ≤ (Finset.range M.m).card := Finset.card_le_card hsub
      _ = M.m := Finset.card_range M.m
  rw [hblk] at hle
  omega

/-- Column-infeasibility (`⌈n^p·y⌉ > n^p`) makes the bracket empty. -/
private theorem bracket_empty_of_col_infeasible (M : BoolMat) (p : ℕ) (x y : ℝ)
    (hCc : M.n ^ p < ⌈((M.n ^ p : ℕ) : ℝ) * y⌉₊) :
    bracket M p x y = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro g ⟨R, C, _, _, hC, hCcard, _⟩
  have hle : C.card ≤ M.n ^ p := by
    calc C.card ≤ (Finset.range (M.n ^ p)).card := Finset.card_le_card hC
      _ = M.n ^ p := Finset.card_range _
  rw [hCcard] at hle
  omega

/-- **Lemma 4.4 (Extended Maximum Projection Lemma).**  For all `1 ≤ ℓ ≤ p`:
`D([M]_{p,x,y}) ≥ D([M]_{ℓ, x, y^{ℓ/p}})`. -/
theorem extended_maximum_projection (M : BoolMat) (p ℓ : ℕ) (x y : ℝ)
    (hℓ1 : 1 ≤ ℓ) (hℓp : ℓ ≤ p) (hy0 : 0 < y) :
    DSet (bracket M p x y) ≥
      DSet (bracket M ℓ x (Real.rpow y ((ℓ : ℝ) / (p : ℝ)))) := by
  classical
  rw [ge_iff_le]
  have hp1 : 1 ≤ p := le_trans hℓ1 hℓp
  -- Degenerate dimensions: the LEFT bracket has complexity 0.
  rcases Nat.eq_zero_or_pos M.m with hm0 | hmpos
  · rw [DSet_bracket_zero_of_m_zero M ℓ x _ hm0]; exact Nat.zero_le _
  rcases Nat.eq_zero_or_pos M.n with hn0 | hnpos
  · rw [DSet_bracket_zero_of_n_zero M ℓ x _ hn0 hℓ1]; exact Nat.zero_le _
  -- Case `ℓ = p`: the two brackets coincide.
  rcases eq_or_lt_of_le hℓp with hℓeq | hℓlt
  · subst hℓeq
    have hediv : (ℓ : ℝ) / (ℓ : ℝ) = 1 := by
      have : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (by omega : ℓ ≠ 0)
      field_simp
    rw [hediv, show y.rpow 1 = y from Real.rpow_one y]
  -- Main case: `m, n ≥ 1`, `1 ≤ ℓ < p`.
  set e : ℝ := (ℓ : ℝ) / (p : ℝ) with hedef
  have he0 : 0 ≤ e := by rw [hedef]; positivity
  -- Row feasibility: `⌈m·x⌉ ≤ m` or not.  The row condition is identical for
  -- both brackets, so row-infeasibility makes BOTH empty.
  by_cases hrow : ⌈(M.m : ℝ) * x⌉₊ ≤ M.m
  · -- Row-feasible.  Split on `y`.
    by_cases hy : 0 ≤ y ∧ y ≤ 1
    · -- `0 ≤ y ≤ 1`: the full projection construction.
      obtain ⟨hy0, hy1⟩ := hy
      apply subgames_are_easier
      · exact bracket_nonempty' M p x y hmpos hp1 hrow hy0 hy1
      · intro g hg
        obtain ⟨R, C, hR, hRpart, hC, hCcard, hgeq⟩ := hg
        obtain ⟨S, D, hS_range, hD_range, hS_equi, hD_card, hsub⟩ :=
          Proof.Projections.maximum_projection_lemma M p ((M.m : ℝ) * x) R C
            hR hRpart hC ℓ hℓ1 hℓlt
        have hD_lb : ⌈((M.n ^ ℓ : ℕ) : ℝ) * Real.rpow y e⌉₊ ≤ D.card :=
          max_proj_col_bound M p ℓ y C D hℓ1 hp1 hy0 hCcard hD_card
        obtain ⟨D', hD'sub, hD'card⟩ := Finset.exists_subset_card_eq hD_lb
        refine ⟨extract (interlace M ℓ) S D', ?_, ?_⟩
        · refine ⟨S, D', ?_, ?_, ?_, ?_, rfl⟩
          · exact hS_range
          · exact hS_equi
          · exact subset_trans hD'sub hD_range
          · exact hD'card
        · rw [hgeq]
          exact isSubgame_trans
            (extract_col_subset_subgame (interlace M ℓ) S D' D hD'sub) hsub
    · -- `¬(0 ≤ y ≤ 1)`: either `y < 0` or `y > 1`.
      rw [not_and_or, not_le, not_le] at hy
      rcases hy with hyneg | hygt
      · -- `y < 0`.  This corner is now vacuous: the restored `0 < y` hypothesis
        -- contradicts `y < 0`.
        exact absurd hy0 (by linarith)
      · -- `y > 1`: both brackets are column-infeasible, hence empty.
        have hnp1 : 1 ≤ M.n ^ p := Nat.one_le_pow _ _ hnpos
        have hnℓ1 : 1 ≤ M.n ^ ℓ := Nat.one_le_pow _ _ hnpos
        -- right empty
        have hRinf : M.n ^ p < ⌈((M.n ^ p : ℕ) : ℝ) * y⌉₊ := by
          apply Nat.lt_ceil.mpr
          have : ((M.n ^ p : ℕ) : ℝ) * 1 < ((M.n ^ p : ℕ) : ℝ) * y := by
            apply mul_lt_mul_of_pos_left hygt
            exact_mod_cast hnp1
          simpa using this
        -- left empty: `y^{ℓ/p} > 1` so `n^ℓ · y^{ℓ/p} > n^ℓ`.
        have hyrpow_gt : (1 : ℝ) < Real.rpow y e := by
          apply Real.one_lt_rpow_iff_of_pos (by linarith) |>.mpr
          left
          refine ⟨hygt, ?_⟩
          rw [hedef]
          apply div_pos <;> exact_mod_cast (by omega : 0 < _)
        have hLinf : M.n ^ ℓ < ⌈((M.n ^ ℓ : ℕ) : ℝ) * Real.rpow y e⌉₊ := by
          apply Nat.lt_ceil.mpr
          have : ((M.n ^ ℓ : ℕ) : ℝ) * 1 < ((M.n ^ ℓ : ℕ) : ℝ) * Real.rpow y e := by
            apply mul_lt_mul_of_pos_left hyrpow_gt
            exact_mod_cast hnℓ1
          simpa using this
        rw [bracket_empty_of_col_infeasible M p x y hRinf]
        rw [bracket_empty_of_col_infeasible M ℓ x (Real.rpow y e) hLinf]
  · -- Row-infeasible: `⌈m·x⌉ > m`.  Both brackets empty.
    push Not at hrow
    rw [bracket_empty_of_row_infeasible M p x y hp1 hrow]
    rw [bracket_empty_of_row_infeasible M ℓ x (Real.rpow y e) hℓ1 hrow]

/-- **Lemma 4.5 (Extended Balancing Lemma).**  For an `m × n` matrix `M`,
integer `p`, `1 < α`, `0 < x < 1`, `0 < α·x ≤ 1`, `0 < y ≤ 1`, if `m·x ∈ ℕ`
and `p* = ⌊p·(α−1)·x/(1−x)⌋ ≥ 1`, then
`D([⟨M⟩^p]_{1, α·x, y}) ≥ D([M]_{p*, x, y})`. -/
theorem extended_balancing (M : BoolMat) (p : ℕ) (α x y : ℝ)
    (hα : 1 < α) (hx0 : 0 < x) (hx1 : x < 1)
    (hαx0 : 0 < α * x) (hαx1 : α * x ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hmx_int : ∃ t : ℕ, (M.m : ℝ) * x = (t : ℝ))
    (hpstar : ⌊(p : ℝ) * (α - 1) * x / (1 - x)⌋₊ ≥ 1) :
    DSet (bracket (interlace M p) 1 (α * x) y) ≥
      DSet (bracket M (⌊(p : ℝ) * (α - 1) * x / (1 - x)⌋₊) x y) := by
  classical
  set pstar : ℕ := ⌊(p : ℝ) * (α - 1) * x / (1 - x)⌋₊ with hpstardef
  rw [ge_iff_le]
  -- `1 - x > 0`.
  have h1mx : (0 : ℝ) < 1 - x := by linarith
  -- Step 1a: `p ≥ 1` follows from `pstar ≥ 1`.
  have hp1 : 1 ≤ p := by
    by_contra hp0
    have : p = 0 := by omega
    rw [this] at hpstardef
    simp only [Nat.cast_zero, zero_mul] at hpstardef
    rw [zero_div] at hpstardef
    rw [hpstardef] at hpstar
    simp at hpstar
  -- Degenerate dimension cases.
  rcases Nat.eq_zero_or_pos M.m with hm0 | hmpos
  · -- m = 0: every right-bracket member has 0 rows.
    rw [DSet_zero_of_dmat_zero (bracket M pstar x y) ?_]
    · exact Nat.zero_le _
    · rintro g ⟨R, C, hR, _, _, _, rfl⟩
      have hRempty : R = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro i hi
        have := hR hi
        rw [hm0, Nat.zero_mul] at this
        simp at this
      apply Dmat_zero_of_m_zero
      simp [extract, hRempty]
  rcases Nat.eq_zero_or_pos M.n with hn0 | hnpos
  · -- n = 0 (m ≥ 1): every right-bracket member has 0 columns (since pstar ≥ 1).
    rw [DSet_zero_of_dmat_zero (bracket M pstar x y) ?_]
    · exact Nat.zero_le _
    · rintro g ⟨R, C, _, _, hC, _, rfl⟩
      have hCempty : C = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro j hj
        have := hC hj
        rw [hn0, Nat.zero_pow (by omega : 0 < pstar)] at this
        simp at this
      apply Dmat_zero_of_n_zero
      simp [extract, hCempty]
  -- Main argument: m ≥ 1, n ≥ 1.
  -- Abbreviations.
  set N : BoolMat := interlace M p with hN
  have hNm : N.m = M.m * p := rfl
  have hNn : N.n = M.n ^ p := rfl
  -- The (constant) row cardinality of left-bracket members.
  set Rcard : ℕ := ⌈((M.m * p : ℕ) : ℝ) * (α * x)⌉₊ with hRcarddef
  -- `T = m·x`, an integer in `[0, m)`.
  set T : ℝ := (M.m : ℝ) * x with hTdef
  obtain ⟨t, hT_int⟩ := hmx_int
  have hT0 : 0 ≤ T := by rw [hTdef]; positivity
  have hTm : T < (M.m : ℝ) := by
    rw [hTdef]
    have : (M.m : ℝ) * x < (M.m : ℝ) * 1 := by
      apply mul_lt_mul_of_pos_left hx1
      exact_mod_cast hmpos
    simpa using this
  -- The balancing σ for left-bracket members (same for every member since |R| = Rcard).
  set sigma : ℕ := ⌈(p : ℝ) * (1 - (1 - (Rcard : ℝ) / ((p : ℝ) * (M.m : ℝ))) /
      (1 - T / (M.m : ℝ)))⌉₊ with hsigmadef
  have hmR : (0 : ℝ) < (M.m : ℝ) := by exact_mod_cast hmpos
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp1
  have hnR : (0 : ℝ) < (M.n : ℝ) := by exact_mod_cast hnpos
  -- `Rcard ≥ p · α · m · x`, i.e. `Rcard / (p·m) ≥ α·x`.
  have hRcard_lb : (p : ℝ) * (M.m : ℝ) * (α * x) ≤ (Rcard : ℝ) := by
    rw [hRcarddef]
    refine le_trans ?_ (Nat.le_ceil _)
    push_cast
    ring_nf
    rw [mul_comm]
  -- `Rcard ≤ p · m` (since `R ⊆ range (m·p)`); equivalently `Rcard / (p·m) ≤ 1`.
  have hRcard_ub : (Rcard : ℝ) ≤ (p : ℝ) * (M.m : ℝ) := by
    rw [hRcarddef]
    rw [show (p : ℝ) * (M.m : ℝ) = (((M.m * p : ℕ)) : ℝ) by push_cast; ring]
    rw [Nat.cast_le]
    apply Nat.ceil_le.mpr
    have : ((M.m * p : ℕ) : ℝ) * (α * x) ≤ ((M.m * p : ℕ) : ℝ) * 1 := by
      apply mul_le_mul_of_nonneg_left hαx1
      positivity
    simpa using this
  -- `T / m = x`.
  have hTm_eq : T / (M.m : ℝ) = x := by
    rw [hTdef]; field_simp
  -- Inner real quantity dominates `z = p(α-1)x/(1-x)`.
  set zinner : ℝ := (p : ℝ) * (1 - (1 - (Rcard : ℝ) / ((p : ℝ) * (M.m : ℝ))) /
      (1 - T / (M.m : ℝ))) with hzinnerdef
  set z : ℝ := (p : ℝ) * (α - 1) * x / (1 - x) with hzdef
  -- `Rcard / m ≥ p·α·x`.
  have hRcard_div : (p : ℝ) * (α * x) ≤ (Rcard : ℝ) / (M.m : ℝ) := by
    rw [le_div_iff₀ hmR]
    calc (p : ℝ) * (α * x) * (M.m : ℝ) = (p : ℝ) * (M.m : ℝ) * (α * x) := by ring
      _ ≤ (Rcard : ℝ) := hRcard_lb
  have hz_le_inner : z ≤ zinner := by
    rw [hzinnerdef, hzdef, hTm_eq]
    -- inner = p·(1 - (1 - Rcard/(p·m))/(1-x)); expand `(1 - Rcard/(p·m))`.
    have hexpand : (p : ℝ) * (1 - (1 - (Rcard : ℝ) / ((p : ℝ) * (M.m : ℝ))) / (1 - x))
        = ((p : ℝ) * (1 - x) - (p : ℝ) + (Rcard : ℝ) / (M.m : ℝ)) / (1 - x) := by
      rw [eq_div_iff (ne_of_gt h1mx)]
      field_simp
      ring
    rw [hexpand]
    rw [div_le_div_iff_of_pos_right h1mx]
    -- goal: p(α-1)x ≤ p(1-x) - p + Rcard/m
    have : (p : ℝ) * (1 - x) - (p : ℝ) + (Rcard : ℝ) / (M.m : ℝ)
        = (Rcard : ℝ) / (M.m : ℝ) - (p : ℝ) * x := by ring
    rw [this]
    -- p(α-1)x ≤ Rcard/m - p·x  ⟺  p·α·x ≤ Rcard/m
    nlinarith [hRcard_div]
  -- Step 3: `sigma ≥ pstar`.
  have hsigma_ge_pstar : pstar ≤ sigma := by
    rw [hsigmadef, hpstardef]
    calc ⌊z⌋₊ ≤ ⌈z⌉₊ := Nat.floor_le_ceil z
      _ ≤ ⌈zinner⌉₊ := Nat.ceil_le_ceil hz_le_inner
  -- `1 ≤ sigma` (since `pstar ≥ 1`).
  have hsigma1 : 1 ≤ sigma := le_trans hpstar hsigma_ge_pstar
  -- Step 3': `sigma ≤ p` (needed for the column-density / exponent step).
  have hsigma_le_p : sigma ≤ p := by
    rw [hsigmadef]
    have hzinner_le_p : zinner ≤ (p : ℝ) := by
      rw [hzinnerdef, hTm_eq]
      have hfrac_nonneg : (0 : ℝ) ≤ (1 - (Rcard : ℝ) / ((p : ℝ) * (M.m : ℝ))) / (1 - x) := by
        apply div_nonneg _ h1mx.le
        have : (Rcard : ℝ) / ((p : ℝ) * (M.m : ℝ)) ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact hRcard_ub
        linarith
      nlinarith [hpR, hfrac_nonneg]
    calc ⌈zinner⌉₊ ≤ ⌈(p : ℝ)⌉₊ := Nat.ceil_le_ceil hzinner_le_p
      _ = p := by simp
  -- Step 1 (final): `monotonicity` lowers the interlace level `sigma → pstar`.
  refine le_trans
    (monotonicity M pstar sigma x x y y hpstar hsigma_ge_pstar hx0 le_rfl hx1.le hy0 le_rfl hy1) ?_
  -- Step 4–5: `bracket M sigma x y` is a subgame-set of `bracket N 1 (α·x) y`.
  apply subgames_are_easier
  · -- The left bracket `bracket N 1 (α·x) y` is nonempty.
    exact left_bracket_nonempty M p α x y N hN hmpos hnpos hp1 hαx1 hy1
  · -- The subgame-set relation, member by member.
    intro g hg
    -- Unpack a left-bracket member.
    obtain ⟨R, C, hRsub, hRpart, hCsub, hCcard, hgeq⟩ := hg
    -- Simplify the `*1` / `^1` from the `p = 1` interlace base.
    simp only [Nat.mul_one, pow_one] at hRsub hCsub hCcard hRpart
    -- `N.m = M.m * p`, `N.n = M.n ^ p`: rewrite the index ranges.
    rw [hNm] at hRsub hRpart
    rw [hNn] at hCsub hCcard
    -- `g = extract (interlace M p) R C`.
    have hgeq' : g = extract (interlace M p) R C := by
      rw [hgeq, hN, extract_interlace_one_eq]
    -- `|R| = Rcard`.
    have hRcard_eq : R.card = Rcard := by
      rw [equipartition_one_iff R (M.m * p) ((M.m * p : ℕ) * (α * x)) hRsub] at hRpart
      rw [hRcarddef, hRpart]
    -- Lower bound for the balancing lemma: `p · T ≤ |R|`.
    have hRT : (p : ℝ) * T ≤ (R.card : ℝ) := by
      rw [hRcard_eq, hTdef]
      calc (p : ℝ) * ((M.m : ℝ) * x) = (p : ℝ) * (M.m : ℝ) * x := by ring
        _ ≤ (p : ℝ) * (M.m : ℝ) * (α * x) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [hx0, hα]
        _ ≤ (Rcard : ℝ) := hRcard_lb
    -- Apply the Balancing Lemma (Lemma 3.20).
    obtain ⟨ℓ, S, D, hS_range, hD_range, hℓ_eq, hS_equi, hD_card, hsub⟩ :=
      Proof.Projections.balancing_lemma M p R C hRsub hCsub T hT0 hTm hRT
    -- `ℓ = sigma`.
    have hℓ_sigma : ℓ = sigma := by
      have : (ℓ : ℝ) = (sigma : ℝ) := by
        rw [hℓ_eq, hsigmadef, hzinnerdef, hRcard_eq]
      exact_mod_cast this
    subst hℓ_sigma
    -- `S` is genuinely equipartitioned (since `sigma ≥ 1`).
    have hS_equi' : IsEquipartitioned S M.m T sigma := hS_equi hsigma1
    -- Column-density: `|D| ≥ ⌈M.n ^ sigma · y⌉`.
    have hD_lb : (⌈((M.n ^ sigma : ℕ) : ℝ) * y⌉₊ : ℕ) ≤ D.card :=
      column_density_bound M p sigma y C D hnpos hsigma_le_p hCcard hD_card
    -- Trim columns to land inside `bracket M sigma x y`.
    obtain ⟨D', hD'sub, hD'card⟩ := Finset.exists_subset_card_eq hD_lb
    -- The assembled subgame member `g'' = extract (interlace M sigma) S D'`.
    refine ⟨extract (interlace M sigma) S D', ?_, ?_⟩
    · -- Membership in `bracket M sigma x y`.
      refine ⟨S, D', ?_, ?_, ?_, ?_, rfl⟩
      · -- `S ⊆ range (M.m * sigma)`.
        exact hS_range
      · -- `S` is `M.m, T, sigma`-equipartitioned with target `(M.m : ℝ) * x = T`.
        have hTeq : ((M.m : ℝ) * x) = T := hTdef.symm
        rw [hTeq]; exact hS_equi'
      · -- `D' ⊆ range (M.n ^ sigma)`.
        exact subset_trans hD'sub hD_range
      · -- `|D'| = ⌈M.n ^ sigma · y⌉`.
        exact hD'card
    · -- `g'' ⊑ g`: column-subset subgame composed with the balancing subgame.
      rw [hgeq']
      refine isSubgame_trans (extract_col_subset_subgame (interlace M sigma) S D' D hD'sub) hsub

/-- **Lemma 4.6 (Transpose of bracket).**  `D([M]_{1,x,y}) = D([Mᵀ]_{1,y,x})`. -/
theorem transpose_bracket (M : BoolMat) (x y : ℝ) :
    DSet (bracket M 1 x y) = DSet (bracket M.transpose 1 y x) := by
  have htt : M.transpose.transpose = M := rfl
  have hsub : ∀ (N : BoolMat) (a b : ℝ),
      { c : ℕ | ∃ G ∈ bracket N 1 a b, Dmat G = c }
        ⊆ { c : ℕ | ∃ G ∈ bracket N.transpose 1 b a, Dmat G = c } := by
    intro N a b c hc
    obtain ⟨G, hGmem, hGc⟩ := hc
    obtain ⟨G', hG'mem, hG'c⟩ := bracket_one_mem_transpose N a b G hGmem
    exact ⟨G', hG'mem, hG'c.trans hGc⟩
  have hset : { c : ℕ | ∃ G ∈ bracket M 1 x y, Dmat G = c }
      = { c : ℕ | ∃ G ∈ bracket M.transpose 1 y x, Dmat G = c } := by
    apply Set.eq_of_subset_of_subset
    · exact hsub M x y
    · have := hsub M.transpose y x
      rw [htt] at this
      exact this
  unfold DSet
  rw [hset]

/-! ### Helpers for Lemma 4.7 (Old Partition) -/

/-- First-round protocol split: if `1 ≤ D f`, an optimal protocol's root either
splits Alice's inputs or Bob's; each child computes `f` on its half with cost
`≤ D f - 1`. -/
private theorem D_pos_split {A B : Type*} [Fintype A] [Fintype B] (f : A → B → Bool)
    (h : 1 ≤ D f) :
    (∃ (a : A → Bool) (P₀ P₁ : Protocol A B Bool),
        (∀ x y, a x = false → P₀.eval x y = f x y) ∧
        (∀ x y, a x = true → P₁.eval x y = f x y) ∧
        P₀.cost ≤ D f - 1 ∧ P₁.cost ≤ D f - 1)
    ∨ (∃ (b : B → Bool) (P₀ P₁ : Protocol A B Bool),
        (∀ x y, b y = false → P₀.eval x y = f x y) ∧
        (∀ x y, b y = true → P₁.eval x y = f x y) ∧
        P₀.cost ≤ D f - 1 ∧ P₁.cost ≤ D f - 1) := by
  classical
  have hne : (AchievableCosts f).Nonempty := Proof.UpperBound.AchievableCosts_nonempty f
  have hmem : D f ∈ AchievableCosts f := Nat.sInf_mem hne
  obtain ⟨P, hcost, hcomp⟩ := hmem
  cases P with
  | leaf z =>
      exfalso
      simp only [Protocol.cost] at hcost
      omega
  | aNode a l r =>
      left
      refine ⟨a, l, r, ?_, ?_, ?_, ?_⟩
      · intro x y hax
        have := hcomp x y
        simp only [Protocol.eval, hax, Bool.false_eq_true, if_false] at this
        exact this
      · intro x y hax
        have := hcomp x y
        simp only [Protocol.eval, hax, if_true] at this
        exact this
      · have : Protocol.cost (Protocol.aNode a l r) = 1 + max (Protocol.cost l) (Protocol.cost r) := rfl
        rw [this] at hcost
        omega
      · have : Protocol.cost (Protocol.aNode a l r) = 1 + max (Protocol.cost l) (Protocol.cost r) := rfl
        rw [this] at hcost
        omega
  | bNode b l r =>
      right
      refine ⟨b, l, r, ?_, ?_, ?_, ?_⟩
      · intro x y hby
        have := hcomp x y
        simp only [Protocol.eval, hby, Bool.false_eq_true, if_false] at this
        exact this
      · intro x y hby
        have := hcomp x y
        simp only [Protocol.eval, hby, if_true] at this
        exact this
      · have : Protocol.cost (Protocol.bNode b l r) = 1 + max (Protocol.cost l) (Protocol.cost r) := rfl
        rw [this] at hcost
        omega
      · have : Protocol.cost (Protocol.bNode b l r) = 1 + max (Protocol.cost l) (Protocol.cost r) := rfl
        rw [this] at hcost
        omega

/-- Classifier: value of predicate `a` at the R-rank of `r` (false off-range). -/
private noncomputable def arank (R : Finset ℕ) (a : Fin R.card → Bool) (r : ℕ) : Bool :=
  if h : (R.sort (· ≤ ·)).idxOf r < R.card then a ⟨_, h⟩ else false

/-- Row-partition complexity bridge (Case 1). -/
private theorem Dmat_row_part_le
    (A : BoolMat) (R C : Finset ℕ) (a : Fin (extract A R C).m → Bool) (b : Bool)
    (P : Protocol (Fin (extract A R C).m) (Fin (extract A R C).n) Bool) (k : ℕ)
    (hP : ∀ i j, a i = b → P.eval i j = (extract A R C).e i j)
    (hPcost : P.cost ≤ k) :
    Dmat (extract A (R.filter (fun r => arank R a r = b)) C) ≤ k := by
  classical
  set R' : Finset ℕ := R.filter (fun r => arank R a r = b) with hR'def
  have hR'sub : R' ⊆ R := Finset.filter_subset _ _
  set sR := R.sort (· ≤ ·) with hsR
  set sR' := R'.sort (· ≤ ·) with hsR'
  have getDmemR' : ∀ i : Fin (extract A R' C).m, sR'.getD i.val 0 ∈ R' := by
    intro i
    have hi : i.val < R'.card := by simpa [extract] using i.isLt
    have hilen : i.val < sR'.length := by rw [hsR', Finset.length_sort]; exact hi
    have hm : sR'.getD i.val 0 ∈ sR' := by
      rw [List.getD_eq_getElem _ _ hilen]; exact List.getElem_mem hilen
    rw [hsR', Finset.mem_sort] at hm; exact hm
  have rowidx : ∀ i : Fin (extract A R' C).m,
      sR.idxOf (sR'.getD i.val 0) < (extract A R C).m := by
    intro i
    have hvmem : sR'.getD i.val 0 ∈ R := hR'sub (getDmemR' i)
    have hidx : sR.idxOf (sR'.getD i.val 0) < sR.length := by
      rw [List.idxOf_lt_length_iff, hsR, Finset.mem_sort]; exact hvmem
    simpa [extract, hsR, Finset.length_sort] using hidx
  have colidx : ∀ j : Fin (extract A R' C).n, j.val < (extract A R C).n := by
    intro j; simpa [extract] using j.isLt
  set ρ : Fin (extract A R' C).m → Fin (extract A R C).m :=
    fun i => ⟨sR.idxOf (sR'.getD i.val 0), rowidx i⟩ with hρdef
  set cρ : Fin (extract A R' C).n → Fin (extract A R C).n :=
    fun j => ⟨j.val, colidx j⟩ with hcρdef
  have hrowval : ∀ i : Fin (extract A R' C).m,
      sR.getD (sR.idxOf (sR'.getD i.val 0)) 0 = sR'.getD i.val 0 := by
    intro i
    have hvmem : sR'.getD i.val 0 ∈ sR := by
      rw [hsR, Finset.mem_sort]; exact hR'sub (getDmemR' i)
    have hidx : sR.idxOf (sR'.getD i.val 0) < sR.length := by
      rw [List.idxOf_lt_length_iff]; exact hvmem
    rw [List.getD_eq_getElem _ _ hidx]
    have hb : sR[sR.idxOf (sR'.getD i.val 0)]? = some (sR'.getD i.val 0) :=
      List.getElem?_idxOf hvmem
    rw [List.getElem?_eq_getElem hidx] at hb
    exact (Option.some.injEq _ _ ▸ hb)
  have hentry : ∀ i j, (extract A R' C).e i j = (extract A R C).e (ρ i) (cρ j) := by
    intro i j
    simp only [extract, hρdef, hcρdef]
    have hrv := hrowval i
    simp only [hsR, hsR'] at hrv ⊢
    simp only [hrv]
  have harank : ∀ i : Fin (extract A R' C).m, a (ρ i) = b := by
    intro i
    have hmem : sR'.getD i.val 0 ∈ R.filter (fun r => arank R a r = b) := getDmemR' i
    have hval : arank R a (sR'.getD i.val 0) = b := (Finset.mem_filter.mp hmem).2
    rw [arank] at hval
    have hcond : (R.sort (· ≤ ·)).idxOf (sR'.getD i.val 0) < R.card := by
      have := rowidx i; simpa [extract, hsR] using this
    rw [dif_pos hcond] at hval
    rw [hρdef]
    convert hval using 1
    exact congrArg a (Fin.ext (by simpa [hsR]))
  have hPgood : ∀ i j, P.eval (ρ i) (cρ j) = (extract A R' C).e i j := by
    intro i j
    rw [hP (ρ i) (cρ j) (harank i), ← hentry i j]
  unfold Dmat D
  have hmem : P.cost ∈ AchievableCosts (extract A R' C).e := by
    refine ⟨Proof.UpperBound.Protocol.comap ρ cρ P, ?_, ?_⟩
    · rw [Proof.UpperBound.Protocol.comap_cost]
    · intro i j
      rw [Proof.UpperBound.Protocol.comap_eval]
      exact hPgood i j
  calc sInf (AchievableCosts (extract A R' C).e) ≤ P.cost := Nat.sInf_le hmem
    _ ≤ k := hPcost

/-- Classifier: value of predicate `b` at the C-rank of `c` (false off-range). -/
private noncomputable def crank (C : Finset ℕ) (b : Fin C.card → Bool) (c : ℕ) : Bool :=
  if h : (C.sort (· ≤ ·)).idxOf c < C.card then b ⟨_, h⟩ else false

/-- Column-partition complexity bridge (Case 2). -/
private theorem Dmat_col_part_le
    (A : BoolMat) (R C : Finset ℕ) (bp : Fin (extract A R C).n → Bool) (b : Bool)
    (P : Protocol (Fin (extract A R C).m) (Fin (extract A R C).n) Bool) (k : ℕ)
    (hP : ∀ i j, bp j = b → P.eval i j = (extract A R C).e i j)
    (hPcost : P.cost ≤ k) :
    Dmat (extract A R (C.filter (fun c => crank C bp c = b))) ≤ k := by
  classical
  set C' : Finset ℕ := C.filter (fun c => crank C bp c = b) with hC'def
  have hC'sub : C' ⊆ C := Finset.filter_subset _ _
  set sC := C.sort (· ≤ ·) with hsC
  set sC' := C'.sort (· ≤ ·) with hsC'
  have getDmemC' : ∀ j : Fin (extract A R C').n, sC'.getD j.val 0 ∈ C' := by
    intro j
    have hj : j.val < C'.card := by simpa [extract] using j.isLt
    have hjlen : j.val < sC'.length := by rw [hsC', Finset.length_sort]; exact hj
    have hm : sC'.getD j.val 0 ∈ sC' := by
      rw [List.getD_eq_getElem _ _ hjlen]; exact List.getElem_mem hjlen
    rw [hsC', Finset.mem_sort] at hm; exact hm
  have colidx : ∀ j : Fin (extract A R C').n,
      sC.idxOf (sC'.getD j.val 0) < (extract A R C).n := by
    intro j
    have hvmem : sC'.getD j.val 0 ∈ C := hC'sub (getDmemC' j)
    have hidx : sC.idxOf (sC'.getD j.val 0) < sC.length := by
      rw [List.idxOf_lt_length_iff, hsC, Finset.mem_sort]; exact hvmem
    simpa [extract, hsC, Finset.length_sort] using hidx
  have rowidx : ∀ i : Fin (extract A R C').m, i.val < (extract A R C).m := by
    intro i; simpa [extract] using i.isLt
  set ρ : Fin (extract A R C').m → Fin (extract A R C).m :=
    fun i => ⟨i.val, rowidx i⟩ with hρdef
  set cρ : Fin (extract A R C').n → Fin (extract A R C).n :=
    fun j => ⟨sC.idxOf (sC'.getD j.val 0), colidx j⟩ with hcρdef
  have hcolval : ∀ j : Fin (extract A R C').n,
      sC.getD (sC.idxOf (sC'.getD j.val 0)) 0 = sC'.getD j.val 0 := by
    intro j
    have hvmem : sC'.getD j.val 0 ∈ sC := by
      rw [hsC, Finset.mem_sort]; exact hC'sub (getDmemC' j)
    have hidx : sC.idxOf (sC'.getD j.val 0) < sC.length := by
      rw [List.idxOf_lt_length_iff]; exact hvmem
    rw [List.getD_eq_getElem _ _ hidx]
    have hb : sC[sC.idxOf (sC'.getD j.val 0)]? = some (sC'.getD j.val 0) :=
      List.getElem?_idxOf hvmem
    rw [List.getElem?_eq_getElem hidx] at hb
    exact (Option.some.injEq _ _ ▸ hb)
  have hentry : ∀ i j, (extract A R C').e i j = (extract A R C).e (ρ i) (cρ j) := by
    intro i j
    simp only [extract, hρdef, hcρdef]
    have hcv := hcolval j
    simp only [hsC, hsC'] at hcv ⊢
    simp only [hcv]
  have hcrank : ∀ j : Fin (extract A R C').n, bp (cρ j) = b := by
    intro j
    have hmem : sC'.getD j.val 0 ∈ C.filter (fun c => crank C bp c = b) := getDmemC' j
    have hval : crank C bp (sC'.getD j.val 0) = b := (Finset.mem_filter.mp hmem).2
    rw [crank] at hval
    have hcond : (C.sort (· ≤ ·)).idxOf (sC'.getD j.val 0) < C.card := by
      have := colidx j; simpa [extract, hsC] using this
    rw [dif_pos hcond] at hval
    rw [hcρdef]
    convert hval using 1
    exact congrArg bp (Fin.ext (by simpa [hsC]))
  have hPgood : ∀ i j, P.eval (ρ i) (cρ j) = (extract A R C').e i j := by
    intro i j
    rw [hP (ρ i) (cρ j) (hcrank j), ← hentry i j]
  unfold Dmat D
  have hmem : P.cost ∈ AchievableCosts (extract A R C').e := by
    refine ⟨Proof.UpperBound.Protocol.comap ρ cρ P, ?_, ?_⟩
    · rw [Proof.UpperBound.Protocol.comap_cost]
    · intro i j
      rw [Proof.UpperBound.Protocol.comap_eval]
      exact hPgood i j
  calc sInf (AchievableCosts (extract A R C').e) ≤ P.cost := Nat.sInf_le hmem
    _ ≤ k := hPcost

/-- Density split parameter (SublemmaSplit). -/
private theorem split_density (y y₁ y₂ : ℝ)
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hy10 : 0 < y₁) (hy11 : y₁ ≤ 1)
    (hy20 : 0 < y₂) (hy21 : y₂ ≤ 1)
    (hprod : y₁ * y₂ ≥ y) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ Real.rpow y a = y₁ ∧ Real.rpow y (1 - a) ≤ y₂ := by
  have hy1gey : y ≤ y₁ := by
    calc y ≤ y₁ * y₂ := hprod
      _ ≤ y₁ * 1 := by apply mul_le_mul_of_nonneg_left hy21 hy10.le
      _ = y₁ := mul_one _
  rcases eq_or_lt_of_le hy1 with hyeq | hylt
  · refine ⟨1, by norm_num, le_refl 1, ?_, ?_⟩
    · show y ^ (1:ℝ) = y₁
      rw [Real.rpow_one]
      rw [hyeq] at hy1gey ⊢
      linarith
    · show y ^ (1 - 1 : ℝ) ≤ y₂
      rw [show (1:ℝ) - 1 = 0 by ring, Real.rpow_zero]
      rw [hyeq] at hy1gey
      have hy1eq : y₁ = 1 := le_antisymm hy11 hy1gey
      rw [hy1eq, one_mul, hyeq] at hprod
      linarith
  · have hlogy_neg : Real.log y < 0 := Real.log_neg hy0 hylt
    have hlogy_ne : Real.log y ≠ 0 := ne_of_lt hlogy_neg
    set a : ℝ := Real.log y₁ / Real.log y with hadef
    have hlogy1_nonpos : Real.log y₁ ≤ 0 := Real.log_nonpos hy10.le hy11
    have ha0 : 0 ≤ a := by
      rw [hadef]
      exact div_nonneg_iff.mpr (Or.inr ⟨hlogy1_nonpos, hlogy_neg.le⟩)
    have ha1 : a ≤ 1 := by
      rw [hadef]
      exact (div_le_one_of_neg hlogy_neg).mpr (Real.log_le_log hy0 hy1gey)
    have hya : Real.rpow y a = y₁ := by
      show y ^ a = y₁
      rw [hadef, Real.rpow_def_of_pos hy0, mul_comm, div_mul_cancel₀ _ hlogy_ne]
      exact Real.exp_log hy10
    refine ⟨a, ha0, ha1, hya, ?_⟩
    have hsub : Real.rpow y (1 - a) = y / y₁ := by
      show y ^ (1 - a) = y / y₁
      rw [Real.rpow_sub hy0, Real.rpow_one, show y ^ a = y₁ from hya]
    rw [hsub, div_le_iff₀ hy10]
    calc y ≤ y₁ * y₂ := hprod
      _ = y₂ * y₁ := by ring

/-- Subgame monotonicity at the `Dmat` level. -/
private theorem Dmat_le_of_subgame {A B : BoolMat} (hAB : IsSubgame A B) :
    Dmat A ≤ Dmat B := by
  obtain ⟨r, c, _hr, _hc, hAe⟩ := hAB
  have hfun : A.e = fun i j => B.e (r i) (c j) := by
    funext i j; exact hAe i j
  show D A.e ≤ D B.e
  rw [hfun]
  exact Proof.ProofLemmas.SublemmaPrecompNoIncrease (g := B.e) (α := r) (β := c)

/-- `DSet (bracket …) ≤ Dmat g` for any bracket member `g`. -/
private theorem DSet_bracket_le_Dmat {M : BoolMat} {q : ℕ} {x y : ℝ} {g : BoolMat}
    (hg : g ∈ bracket M q x y) : DSet (bracket M q x y) ≤ Dmat g :=
  Nat.sInf_le ⟨g, hg, rfl⟩

/-- **B-branch core.**  Given the two children of the row split with the larger part
`q₁ ≥ q₂ ≥ 1`, summing to `2p+δ`, with densities `zᵢ ∈ (0,1]`, `z₁·z₂ ≥ y`, and the
per-child bracket bounds `DSet([M]_{qᵢ,x,zᵢ}) ≤ K`, the `B`-infimum is `≤ K`.  The
bigger part is assigned exponent `a` (via `split_density`), landing in the
`p+δ+ℓ` slot, and the smaller part is the `p-ℓ` slot. -/
private theorem B_branch_core (M : BoolMat) (p δ : ℕ) (x y : ℝ) (q₁ q₂ : ℕ) (z₁ z₂ : ℝ)
    (K : ℕ)
    (hmpos : 0 < M.m) (hnpos : 0 < M.n)
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hsum : q₁ + q₂ = 2 * p + δ) (hδ : δ ≤ 1)
    (hq2 : 1 ≤ q₂) (hq21 : q₂ ≤ q₁)
    (hz10 : 0 < z₁) (hz11 : z₁ ≤ 1) (hz20 : 0 < z₂) (hz21 : z₂ ≤ 1)
    (hprod : z₁ * z₂ ≥ y)
    (hD1 : DSet (bracket M q₁ x z₁) ≤ K)
    (hD2 : DSet (bracket M q₂ x z₂) ≤ K) :
    sInf { v : ℕ | ∃ (ℓ : ℕ) (a : ℝ),
        ℓ < p ∧ 0 ≤ a ∧ a ≤ 1 ∧
        v = max (DSet (bracket M (p + δ + ℓ) x (Real.rpow y a)))
                (DSet (bracket M (p - ℓ) x (Real.rpow y (1 - a)))) } ≤ K := by
  -- Index `ℓ` for the `B`-family.
  set ℓ : ℕ := q₁ - p - δ with hℓdef
  -- `q₁ = p + δ + ℓ` and `q₂ = p - ℓ`, with `ℓ < p`.
  have hq1eq : q₁ = p + δ + ℓ := by omega
  have hq2eq : q₂ = p - ℓ := by omega
  have hℓp : ℓ < p := by omega
  -- Density split: exponent `a` with `y^a = z₁`, `y^{1-a} ≤ z₂`.
  obtain ⟨a, ha0, ha1, hya, hyb⟩ :=
    split_density y z₁ z₂ hy0 hy1 hz10 hz11 hz20 hz21 hprod
  -- First slot: `DSet([M]_{q₁,x,y^a}) ≤ K` (since `y^a = z₁`).
  have hbig : DSet (bracket M q₁ x (Real.rpow y a)) ≤ K := by
    rw [hya]; exact hD1
  -- Second slot: monotone-down from `z₂` to `y^{1-a}`.
  have hyb_pos : (0:ℝ) < Real.rpow y (1 - a) := Real.rpow_pos_of_pos hy0 _
  have hsmall : DSet (bracket M q₂ x (Real.rpow y (1 - a))) ≤ K := by
    have hmono : DSet (bracket M q₂ x (Real.rpow y (1 - a)))
        ≤ DSet (bracket M q₂ x z₂) :=
      mono_col M q₂ x (Real.rpow y (1 - a)) z₂ hmpos hnpos hq2 hx0 hx1
        hyb_pos hyb hz21
    exact le_trans hmono hD2
  -- This particular `(ℓ, a)` gives a member of the `B`-family `≤ K`.
  have hmemle : max (DSet (bracket M (p + δ + ℓ) x (Real.rpow y a)))
                    (DSet (bracket M (p - ℓ) x (Real.rpow y (1 - a)))) ≤ K := by
    apply max_le
    · rw [← hq1eq]; exact hbig
    · rw [← hq2eq]; exact hsmall
  refine le_trans (Nat.sInf_le ?_) hmemle
  exact ⟨ℓ, a, hℓp, ha0, ha1, rfl⟩

/-- **Lemma 4.7 (Old Partition Lemma).**  For any matrix `M`, `0 < x ≤ 1/2`,
`0 < y ≤ 1`, and `δ ∈ {0,1}`, if `D([M]_{2p+δ, 2x, y}) ≥ 1`, then
`D([M]_{2p+δ, 2x, y}) ≥ 1 + min A (min B C)` where
`A = D([M]_{2p+δ, x, y})`,
`B = min_{ℓ ∈ [p), a ∈ [0,1]} max(D([M]_{p+δ+ℓ, x, y^a}), D([M]_{p−ℓ, x, y^{1−a}}))`,
`C = D([M]_{2p+δ, 2x, y/2})`. -/
theorem old_partition (M : BoolMat) (p δ : ℕ) (x y : ℝ)
    (hx0 : 0 < x) (hx12 : x ≤ 1 / 2) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hδ : δ ≤ 1)
    (hpos : DSet (bracket M (2 * p + δ) (2 * x) y) ≥ 1) :
    DSet (bracket M (2 * p + δ) (2 * x) y) ≥
      1 + min (DSet (bracket M (2 * p + δ) x y))
        (min
          (sInf { v : ℕ | ∃ (ℓ : ℕ) (a : ℝ),
              ℓ < p ∧ 0 ≤ a ∧ a ≤ 1 ∧
              v = max (DSet (bracket M (p + δ + ℓ) x (Real.rpow y a)))
                      (DSet (bracket M (p - ℓ) x (Real.rpow y (1 - a)))) })
          (DSet (bracket M (2 * p + δ) (2 * x) (y / 2)))) := by
  classical
  set P : ℕ := 2 * p + δ with hPdef
  -- Abbreviations for the three branches.
  set A : ℕ := DSet (bracket M P x y) with hAdef
  set Bset : Set ℕ := { v : ℕ | ∃ (ℓ : ℕ) (a : ℝ),
      ℓ < p ∧ 0 ≤ a ∧ a ≤ 1 ∧
      v = max (DSet (bracket M (p + δ + ℓ) x (Real.rpow y a)))
              (DSet (bracket M (p - ℓ) x (Real.rpow y (1 - a)))) } with hBsetdef
  set B : ℕ := sInf Bset with hBdef
  set C : ℕ := DSet (bracket M P (2 * x) (y / 2)) with hCdef
  set RHS : ℕ := 1 + min A (min B C) with hRHSdef
  rw [ge_iff_le]
  -- The bracket value-set.
  set Φ : Set BoolMat := bracket M P (2 * x) y with hΦdef
  set valset : Set ℕ := { c : ℕ | ∃ M' ∈ Φ, Dmat M' = c } with hvalsetdef
  -- `hpos : 1 ≤ DSet Φ = sInf valset`.
  have hposval : 1 ≤ sInf valset := by
    have : DSet Φ = sInf valset := rfl
    rw [← this]; exact hpos
  -- The value-set is nonempty (else sInf = 0 < 1).
  have hvne : valset.Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty] at he
    rw [he, Nat.sInf_empty] at hposval
    omega
  -- Per-member bound `(⋆)`: every member of `Φ` has `Dmat ≥ RHS`.
  have hx0' : (0:ℝ) < 2 * x := by linarith
  have hx1' : 2 * x ≤ 1 := by linarith
  have hstar : ∀ c ∈ valset, RHS ≤ c := by
    rintro c ⟨g, hgΦ, rfl⟩
    -- `Dmat g ≥ 1`.
    have hDg1 : 1 ≤ Dmat g := by
      have : sInf valset ≤ Dmat g := Nat.sInf_le ⟨g, hgΦ, rfl⟩
      omega
    -- Unpack the bracket membership.
    obtain ⟨R, C0, hRsub, hRpart, hCsub, hCcard, hgeq⟩ := hgΦ
    subst hgeq
    -- Index positivity: `1 ≤ P`.
    have hP1 : 1 ≤ P := by
      rcases Nat.eq_zero_or_pos P with hP0 | hP0
      · exfalso
        have hRempty : R = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro i hi
          have := hRsub hi
          rw [hP0, Nat.mul_zero] at this
          simp at this
        have : Dmat (extract (interlace M P) R C0) = 0 := by
          apply Dmat_zero_of_m_zero
          simp [extract, hRempty]
        omega
      · exact hP0
    set g : BoolMat := extract (interlace M P) R C0 with hgdef
    -- `Dmat g = D g.e`.
    have hDmatg : Dmat g = D g.e := rfl
    have hsplit := D_pos_split g.e (by rw [← hDmatg]; exact hDg1)
    rcases hsplit with hrow | hcol
    · -- Case 1: row player speaks first.
      obtain ⟨a, P₀, P₁, hPa0, hPa1, hca0, hca1⟩ := hrow
      -- Positivity of `M.m`, `M.n` from `Dmat g ≥ 1`.
      have hRpos : 0 < R.card := by
        by_contra h
        push Not at h
        have : R.card = 0 := by omega
        have : Dmat g = 0 := by
          apply Dmat_zero_of_m_zero; rw [hgdef, extract_m]; exact this
        omega
      have hCpos : 0 < C0.card := by
        by_contra h
        push Not at h
        have : C0.card = 0 := by omega
        have : Dmat g = 0 := by
          apply Dmat_zero_of_n_zero; rw [hgdef, extract_n]; exact this
        omega
      have hmpos : 0 < M.m := by
        rcases Nat.eq_zero_or_pos M.m with h | h
        · exfalso
          have hRempty : R = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro i hi; have := hRsub hi
            rw [h, Nat.zero_mul] at this; simp at this
          rw [hRempty] at hRpos; simp at hRpos
        · exact h
      have hnpos : 0 < M.n := by
        rcases Nat.eq_zero_or_pos M.n with h | h
        · exfalso
          have hCempty : C0 = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro j hj; have := hCsub hj
            rw [h, Nat.zero_pow (by omega : 0 < P)] at this; simp at this
          rw [hCempty] at hCpos; simp at hCpos
        · exact h
      have hn1 : 1 ≤ M.n := hnpos
      -- Row partition via the classifier `a`.
      set R₁ : Finset ℕ := R.filter (fun r => arank R a r = false) with hR₁def
      set R₂ : Finset ℕ := R.filter (fun r => arank R a r = true) with hR₂def
      have hR₁sub : R₁ ⊆ R := Finset.filter_subset _ _
      have hR₂sub : R₂ ⊆ R := Finset.filter_subset _ _
      have hR_union : R₁ ∪ R₂ = R := by
        rw [hR₁def, hR₂def]
        have hcong : (R.filter (fun r => arank R a r = true))
            = (R.filter (fun r => ¬ arank R a r = false)) := by
          apply Finset.filter_congr; intro r _; simp [Bool.not_eq_false]
        rw [hcong, Finset.filter_union_filter_not_eq]
      have hR_disj : Disjoint R₁ R₂ := by
        rw [hR₁def, hR₂def, Finset.disjoint_left]
        intro r h1 h2
        rw [Finset.mem_filter] at h1 h2
        rw [h1.2] at h2; simp at h2
      -- Row-class complexity bounds.
      have hbr0 : Dmat (extract (interlace M P) R₁ C0) ≤ Dmat g - 1 := by
        have := Dmat_row_part_le (interlace M P) R C0 a false P₀ (Dmat g - 1)
          (fun i j hbj => hPa0 i j hbj) (by rw [hDmatg]; exact hca0)
        exact this
      have hbr1 : Dmat (extract (interlace M P) R₂ C0) ≤ Dmat g - 1 := by
        have := Dmat_row_part_le (interlace M P) R C0 a true P₁ (Dmat g - 1)
          (fun i j hbj => hPa1 i j hbj) (by rw [hDmatg]; exact hca1)
        exact this
      -- Apply Lemma 4.3 (Extended Product of Projection) with this row partition.
      have h43 := extended_product_of_projection M P (2 * x) y
        hx0' hx1' hy0 hy1 hn1 R C0 hRsub hRpart hCsub hCcard R₁ R₂ hR_union hR_disj
      obtain ⟨ℓ₁, ℓ₂, y₁, y₂, S₁, S₂, D₁, D₂, hyy, hℓsum, hy1eq, hy2eq, hy1le, hy2le, hidx1, hidx2⟩ := h43
      -- Basic numerics.
      have hxeq : (2 * x / 2 : ℝ) = x := by ring
      have hx1f : x ≤ 1 := le_trans hx12 (by norm_num)
      -- Density positivity for the two children.
      have hy1nn : 0 ≤ y₁ := by rw [hy1eq]; positivity
      have hy2nn : 0 ≤ y₂ := by rw [hy2eq]; positivity
      have hygey1 : y ≤ y₁ := by nlinarith [hyy, hy2le, hy2nn]
      have hygey2 : y ≤ y₂ := by nlinarith [hyy, hy1le, hy1nn]
      have hy10 : 0 < y₁ := lt_of_lt_of_le hy0 hygey1
      have hy20 : 0 < y₂ := lt_of_lt_of_le hy0 hygey2
      -- Reduce the goal `RHS ≤ Dmat g` to `min A (min B C) ≤ Dmat g - 1`.
      rw [hRHSdef]
      suffices hmin : min A (min B C) ≤ Dmat g - 1 by omega
      -- `A`-branch helper: from a full-count child of density `z ≥ y`, with the
      -- subgame bound `Dmat(extract … R' C0) ≤ Dmat g - 1`, conclude `A ≤ Dmat g - 1`.
      have hAbranch : ∀ (R' : Finset ℕ) (z : ℝ) (g' : BoolMat),
          y ≤ z → z ≤ 1 →
          g' ∈ bracket M P x z →
          IsSubgame g' (extract (interlace M P) R' C0) →
          Dmat (extract (interlace M P) R' C0) ≤ Dmat g - 1 →
          A ≤ Dmat g - 1 := by
        intro R' z g' hyz hz1 hg'mem hg'sub hbrR'
        have hA_le : A ≤ DSet (bracket M P x z) := by
          rw [hAdef]
          exact mono_col M P x y z hmpos hnpos hP1 hx0 hx1f hy0 hyz hz1
        have hsetz : DSet (bracket M P x z) ≤ Dmat g' :=
          DSet_bracket_le_Dmat hg'mem
        have hg'le : Dmat g' ≤ Dmat g - 1 :=
          le_trans (Dmat_le_of_subgame hg'sub) hbrR'
        exact le_trans hA_le (le_trans hsetz hg'le)
      -- Split on the two parts being zero or positive.
      rcases Nat.eq_zero_or_pos ℓ₂ with hℓ2z | hℓ2p
      · -- Subcase 1a: `ℓ₂ = 0`, so `ℓ₁ = P`. Use the `A`-branch via child 1.
        have hℓ1P : ℓ₁ = P := by omega
        have hℓ1pos : 1 ≤ ℓ₁ := by omega
        obtain ⟨hsub1, hmem1⟩ := hidx1 hℓ1pos
        rw [hxeq] at hmem1
        -- `g₁ ∈ bracket M P x y₁`.
        rw [hℓ1P] at hmem1 hsub1
        have hA : A ≤ Dmat g - 1 :=
          hAbranch R₁ y₁ _ hygey1 hy1le hmem1 hsub1 hbr0
        exact le_trans (min_le_left _ _) hA
      · rcases Nat.eq_zero_or_pos ℓ₁ with hℓ1z | hℓ1p
        · -- Subcase 1a': `ℓ₁ = 0`, so `ℓ₂ = P`. Use the `A`-branch via child 2.
          have hℓ2P : ℓ₂ = P := by omega
          have hℓ2pos : 1 ≤ ℓ₂ := by omega
          obtain ⟨hsub2, hmem2⟩ := hidx2 hℓ2pos
          rw [hxeq] at hmem2
          rw [hℓ2P] at hmem2 hsub2
          have hA : A ≤ Dmat g - 1 :=
            hAbranch R₂ y₂ _ hygey2 hy2le hmem2 hsub2 hbr1
          exact le_trans (min_le_left _ _) hA
        · -- Subcase 1b: both parts `≥ 1`.  Use the `B`-branch.
          obtain ⟨hsub1, hmem1⟩ := hidx1 hℓ1p
          obtain ⟨hsub2, hmem2⟩ := hidx2 hℓ2p
          rw [hxeq] at hmem1 hmem2
          -- Per-child bracket bounds: `DSet([M]_{ℓᵢ,x,yᵢ}) ≤ Dmat g - 1`.
          have hD1 : DSet (bracket M ℓ₁ x y₁) ≤ Dmat g - 1 :=
            le_trans (DSet_bracket_le_Dmat hmem1)
              (le_trans (Dmat_le_of_subgame hsub1) hbr0)
          have hD2 : DSet (bracket M ℓ₂ x y₂) ≤ Dmat g - 1 :=
            le_trans (DSet_bracket_le_Dmat hmem2)
              (le_trans (Dmat_le_of_subgame hsub2) hbr1)
          -- `B ≤ Dmat g - 1`, via `B_branch_core`, relabelling so the bigger part is first.
          have hB : B ≤ Dmat g - 1 := by
            rw [hBdef, hBsetdef]
            rcases le_total ℓ₂ ℓ₁ with hle | hle
            · -- `ℓ₁ ≥ ℓ₂`: child 1 is the big slot.
              exact B_branch_core M p δ x y ℓ₁ ℓ₂ y₁ y₂ (Dmat g - 1)
                hmpos hnpos hx0 hx1f hy0 hy1 hℓsum hδ hℓ2p hle
                hy10 hy1le hy20 hy2le hyy hD1 hD2
            · -- `ℓ₂ ≥ ℓ₁`: child 2 is the big slot; commute the product hypothesis.
              exact B_branch_core M p δ x y ℓ₂ ℓ₁ y₂ y₁ (Dmat g - 1)
                hmpos hnpos hx0 hx1f hy0 hy1 (by omega) hδ hℓ1p hle
                hy20 hy2le hy10 hy1le (by rw [mul_comm]; exact hyy) hD2 hD1
          exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) hB)
    · -- Case 2: column player speaks first.
      obtain ⟨b, P₀, P₁, hPb0, hPb1, hc0, hc1⟩ := hcol
      -- Bridges: each column class has small complexity.
      have hbr0 : Dmat (extract (interlace M P) R (C0.filter (fun c => crank C0 b c = false)))
          ≤ Dmat g - 1 := by
        have := Dmat_col_part_le (interlace M P) R C0 b false P₀ (Dmat g - 1)
          (fun i j hbj => hPb0 i j hbj) (by rw [hDmatg]; exact hc0)
        exact this
      have hbr1 : Dmat (extract (interlace M P) R (C0.filter (fun c => crank C0 b c = true)))
          ≤ Dmat g - 1 := by
        have := Dmat_col_part_le (interlace M P) R C0 b true P₁ (Dmat g - 1)
          (fun i j hbj => hPb1 i j hbj) (by rw [hDmatg]; exact hc1)
        exact this
      -- The two column classes partition `C0`.
      set Cf : Finset ℕ := C0.filter (fun c => crank C0 b c = false) with hCfdef
      set Ct : Finset ℕ := C0.filter (fun c => crank C0 b c = true) with hCtdef
      have hcardsum : Cf.card + Ct.card = C0.card := by
        rw [hCfdef, hCtdef]
        have hcong : (C0.filter (fun c => crank C0 b c = true))
            = (C0.filter (fun c => ¬ crank C0 b c = false)) := by
          apply Finset.filter_congr
          intro c _
          simp [Bool.not_eq_false]
        rw [hcong]
        exact Finset.card_filter_add_card_filter_not
          (p := fun c => crank C0 b c = false)
      -- One class has at least half the columns; pick `C1` with `⌈n^P·(y/2)⌉` columns.
      have hhalf : ⌈((M.n ^ P : ℕ) : ℝ) * (y / 2)⌉₊ ≤ Cf.card ∨
          ⌈((M.n ^ P : ℕ) : ℝ) * (y / 2)⌉₊ ≤ Ct.card := by
        -- `⌈n^P·(y/2)⌉ ≤ ⌈|C0|/2⌉ ≤ max Cf Ct`.
        have hkey : ⌈((M.n ^ P : ℕ) : ℝ) * (y / 2)⌉₊ * 2 ≤ C0.card + 1 := by
          rw [hCcard]
          -- `2·⌈n^P·(y/2)⌉ ≤ ⌈n^P·y⌉ + 1`.
          have hub : ((M.n ^ P : ℕ) : ℝ) * y ≤ (⌈((M.n ^ P : ℕ) : ℝ) * y⌉₊ : ℝ) :=
            Nat.le_ceil _
          have hlb : (⌈((M.n ^ P : ℕ) : ℝ) * (y / 2)⌉₊ : ℝ) < ((M.n ^ P : ℕ) : ℝ) * (y / 2) + 1 :=
            Nat.ceil_lt_add_one (by positivity)
          -- pass to a real inequality strict, then to ℕ.
          set Xh : ℕ := ⌈((M.n ^ P : ℕ) : ℝ) * (y / 2)⌉₊ with hXhdef
          set Xy : ℕ := ⌈((M.n ^ P : ℕ) : ℝ) * y⌉₊ with hXydef
          have hreal : (Xh : ℝ) * 2 < (Xy : ℝ) + 2 := by
            rw [hXhdef, hXydef]; nlinarith [hub, hlb]
          have hnatlt : Xh * 2 < Xy + 2 := by exact_mod_cast hreal
          omega
        by_contra hcon
        push Not at hcon
        obtain ⟨hlf, hlt⟩ := hcon
        omega
      -- Generic finisher: any column class `C1 ⊆ C0` with enough columns and small
      -- complexity yields the `C`-branch bound.
      have hfinish : ∀ C1 : Finset ℕ, C1 ⊆ C0 →
          ⌈((M.n ^ P : ℕ) : ℝ) * (y / 2)⌉₊ ≤ C1.card →
          Dmat (extract (interlace M P) R C1) ≤ Dmat g - 1 →
          RHS ≤ Dmat g := by
        intro C1 hC1sub hC1card hC1Dmat
        -- Choose `C' ⊆ C1` of exact cardinality `⌈n^P·(y/2)⌉`.
        obtain ⟨C', hC'sub1, hC'card⟩ := Finset.exists_subset_card_eq hC1card
        have hC'sub0 : C' ⊆ C0 := subset_trans hC'sub1 hC1sub
        have hC'range : C' ⊆ Finset.range (M.n ^ P) := subset_trans hC'sub0 hCsub
        -- `g' = extract (interlace M P) R C'` is a bracket member at density `y/2`.
        have hg'mem : extract (interlace M P) R C' ∈ bracket M P (2 * x) (y / 2) := by
          refine ⟨R, C', hRsub, hRpart, hC'range, ?_, rfl⟩
          rw [hC'card]
        -- `g' ⊑ extract (interlace M P) R C1` (column subset), so its `Dmat` is smaller.
        have hg'sub : IsSubgame (extract (interlace M P) R C')
            (extract (interlace M P) R C1) :=
          extract_col_subset_subgame (interlace M P) R C' C1 hC'sub1
        have hg'le : Dmat (extract (interlace M P) R C') ≤ Dmat g - 1 := by
          have hmono : Dmat (extract (interlace M P) R C')
              ≤ Dmat (extract (interlace M P) R C1) := by
            obtain ⟨r, c, _, _, he⟩ := hg'sub
            show D (extract (interlace M P) R C').e ≤ D (extract (interlace M P) R C1).e
            rw [show (extract (interlace M P) R C').e
                  = fun i j => (extract (interlace M P) R C1).e (r i) (c j)
                from funext fun i => funext fun j => he i j]
            exact Proof.ProofLemmas.SublemmaPrecompNoIncrease
              (g := (extract (interlace M P) R C1).e) (α := r) (β := c)
          exact le_trans hmono hC1Dmat
        -- `C = DSet (bracket M P (2x) (y/2)) ≤ Dmat g'`.
        have hCle : C ≤ Dmat (extract (interlace M P) R C') := by
          rw [hCdef]
          exact Nat.sInf_le ⟨extract (interlace M P) R C', hg'mem, rfl⟩
        have hCfin : C ≤ Dmat g - 1 := le_trans hCle hg'le
        -- `RHS = 1 + min A (min B C) ≤ 1 + C ≤ 1 + (Dmat g - 1) = Dmat g`.
        rw [hRHSdef]
        have hminle : min A (min B C) ≤ C := le_trans (min_le_right _ _) (min_le_right _ _)
        omega
      rcases hhalf with hf | ht
      · exact hfinish Cf (Finset.filter_subset _ _) hf hbr0
      · exact hfinish Ct (Finset.filter_subset _ _) ht hbr1
  -- Transfer the per-member bound to the infimum.
  show RHS ≤ DSet Φ
  have : DSet Φ = sInf valset := rfl
  rw [this]
  exact le_csInf hvne hstar

end Proof.BracketLemmas

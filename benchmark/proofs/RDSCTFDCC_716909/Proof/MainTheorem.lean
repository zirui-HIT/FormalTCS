import Mathlib
import Proof.Types.BoolMat
import Proof.Types.CommComplexity
import Proof.Types.MatComplexity
import Proof.Types.DirectSum
import Proof.Types.Subgame
import Proof.Types.AlternatingGame
import Proof.Types.Interlace
import Proof.Types.Protocol
import Proof.UpperBound
import Proof.PhiInduction
import Proof.ProofLemmas.DimRecurrence
import Proof.ProofLemmas.SublemmaDimPositive
import Proof.ProofLemmas.SublemmaDimUnbounded
import Proof.ProofLemmas.SublemmaInSn
import Proof.ProofLemmas.SublemmaSurjOntoFin
import Proof.ProofLemmas.SublemmaPrecompNoIncrease
import Proof.ProofLemmas.SublemmaSurjRestrictGE
import Proof.ProofLemmas.SublemmaPrecompEq
import Proof.ProofLemmas.SublemmaDirectSumPrecomp

open Proof.Types.BoolMat
open Proof.Types.CommComplexity
open Proof.Types.MatComplexity
open Proof.Types.DirectSum
open Proof.Types.Subgame
open Proof.Types.AlternatingGame
open Proof.Types.Protocol

set_option maxRecDepth 8000

namespace Proof.MainTheorem

/-- The fixed parameter `B = Q = 255 · 2^{k-8}` with `k = 10000`, used from Section 4 onward. -/
private abbrev Q : ℕ := 255 * 2 ^ (10000 - 8)

/-- Proposition 2.7 (Complexity Invariant to Transposition).
For any Boolean matrix `M`, `D(Mᵀ) = D(M)`. -/
theorem complexity_invariant_to_transposition (M : BoolMat) :
    Dmat M.transpose = Dmat M := by
  show D M.transpose.e = D M.e
  exact (Proof.UpperBound.D_swap M.e).symm

/-- Proposition 3.11 (Subgames Are Easier).
If `Φ' ⊑ Φ` then `D(Φ') ≤ D(Φ)`. The family `Φ` is assumed nonempty, matching the
paper's `D(Φ) = min_{f ∈ Φ} D(f)`, which is only well-defined for nonempty families. -/
theorem subgames_are_easier (Φ' Φ : Set BoolMat) (hΦ : Φ.Nonempty) (h : IsSubgameSet Φ' Φ) :
    DSet Φ' ≤ DSet Φ := by
  -- Crux: a subgame has no greater complexity.
  have hcrux : ∀ A B : BoolMat, IsSubgame A B → Dmat A ≤ Dmat B := by
    intro A B hAB
    obtain ⟨r, c, _hr, _hc, hAe⟩ := hAB
    have hfun : A.e = fun i j => B.e (r i) (c j) := by
      funext i j; exact hAe i j
    show D A.e ≤ D B.e
    rw [hfun]
    exact Proof.ProofLemmas.SublemmaPrecompNoIncrease (g := B.e) (α := r) (β := c)
  -- It suffices to bound `DSet Φ'` below the inf over `Φ`.
  apply le_csInf
  · -- nonemptiness of the `Φ`-candidate set, from `hΦ`.
    obtain ⟨M₀, hM₀⟩ := hΦ
    exact ⟨Dmat M₀, M₀, hM₀, rfl⟩
  · -- per-element bound.
    rintro x ⟨M, hM, rfl⟩
    obtain ⟨M', hM', hsub⟩ := h M hM
    have hle : Dmat M' ≤ Dmat M := hcrux M' M hsub
    refine le_trans ?_ hle
    exact Nat.sInf_le ⟨M', hM', rfl⟩

/-- Largest index `j ≤ 2n+1` whose `phi Q j` fits inside `2^n × 2^n`. -/
private noncomputable def iN (n : ℕ) : ℕ :=
  Nat.findGreatest (fun j => (phi Q j).m ≤ 2 ^ n ∧ (phi Q j).n ≤ 2 ^ n) (2 * n + 1)

/-- Existence statement packaging the witness family for index `n`. In the "good"
regime the family is `phi Q (iN n)` precomposed with chosen surjections `σ, τ`;
otherwise the constant-`false` function. This is the data we `Classical.choose`
from to define `fam`, so that `fam`'s body contains NO `dite` on a
`phi`-dependent decidable instance (which made the kernel deep-recurse). -/
private lemma fam_exists (n : ℕ) :
    ∃ f : (Fin n → Bool) → (Fin n → Bool) → Bool,
      ((1 ≤ (phi Q (iN n)).m ∧ (phi Q (iN n)).m ≤ 2 ^ n) ∧
       (1 ≤ (phi Q (iN n)).n ∧ (phi Q (iN n)).n ≤ 2 ^ n)) →
      ∃ (σ : (Fin n → Bool) → Fin ((phi Q (iN n)).m))
        (τ : (Fin n → Bool) → Fin ((phi Q (iN n)).n)),
        Function.Surjective σ ∧ Function.Surjective τ ∧
        f = fun u v => (phi Q (iN n)).e (σ u) (τ v) := by
  by_cases h : ((1 ≤ (phi Q (iN n)).m ∧ (phi Q (iN n)).m ≤ 2 ^ n) ∧
                (1 ≤ (phi Q (iN n)).n ∧ (phi Q (iN n)).n ≤ 2 ^ n))
  · obtain ⟨σ, hσ⟩ := Proof.ProofLemmas.SublemmaSurjOntoFin (phi Q (iN n)).m n h.1.1 h.1.2
    obtain ⟨τ, hτ⟩ := Proof.ProofLemmas.SublemmaSurjOntoFin (phi Q (iN n)).n n h.2.1 h.2.2
    exact ⟨fun u v => (phi Q (iN n)).e (σ u) (τ v), fun _ => ⟨σ, τ, hσ, hτ, rfl⟩⟩
  · exact ⟨fun _ _ => false, fun hg => absurd hg h⟩

/-- The witness family of total functions, packaged via `Classical.choose` so its
body has no `phi`-dependent `dite`. -/
private noncomputable def fam (n : ℕ) : (Fin n → Bool) → (Fin n → Bool) → Bool :=
  Classical.choose (fam_exists n)

set_option maxRecDepth 100000 in
/-- Theorem 2.9 (Main Theorem — refutation of the Direct Sum Conjecture). -/
theorem refutation_of_direct_sum_conjecture :
    ∃ f : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Bool,
      ∀ N L C : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ ℓ : ℕ, L ≤ ℓ ∧
        (D (f n) : ℝ) > (D (directSum (f n) ℓ) : ℝ) / (ℓ : ℝ) + (C : ℝ) := by
  -- abbreviations
  set dimPos := Proof.ProofLemmas.SublemmaDimPositive with hdimPos
  set dimUnb := Proof.ProofLemmas.SublemmaDimUnbounded with hdimUnb
  refine ⟨fam, ?_⟩
  intro N L C
  -- the index `i` we want inside S_n, and the witnesses
  set i : ℕ := 178 * (C + 2) with hi
  set n : ℕ := max N (max (Nat.clog 2 ((phi Q i).m)) (Nat.clog 2 ((phi Q i).n))) with hn
  refine ⟨n, le_max_left _ _, 178 * (L + 1), ?_, ?_⟩
  · -- L ≤ 178 * (L + 1)
    nlinarith
  -- Now the main inequality. First, the membership facts.
  -- positivity of dimensions of phi Q i
  have hposm : 1 ≤ (phi Q i).m := (dimPos.1 i).1
  have hposn : 1 ≤ (phi Q i).n := (dimPos.1 i).2
  -- 2^n ≥ (phi Q i).m and .n via SublemmaInSn
  have hclogm : Nat.clog 2 ((phi Q i).m) ≤ n := by
    rw [hn]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hclogn : Nat.clog 2 ((phi Q i).n) ≤ n := by
    rw [hn]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hInSn := Proof.ProofLemmas.SublemmaInSn i n hclogm hclogn
  -- i ≤ 2n+1 from DimUnbounded.2
  have hi_le : i ≤ 2 * n + 1 := dimUnb.2 n i hInSn.1 hInSn.2
  -- i ∈ S_n  ⟹  i ≤ iN n
  have hPi : (phi Q i).m ≤ 2 ^ n ∧ (phi Q i).n ≤ 2 ^ n := hInSn
  have hi_le_iN : i ≤ iN n := by
    rw [iN]
    exact Nat.le_findGreatest hi_le hPi
  -- P (iN n) holds: dims of phi Q (iN n) ≤ 2^n
  have hspec : (phi Q (iN n)).m ≤ 2 ^ n ∧ (phi Q (iN n)).n ≤ 2 ^ n := by
    have := Nat.findGreatest_spec (P := fun j => (phi Q j).m ≤ 2 ^ n ∧ (phi Q j).n ≤ 2 ^ n)
      (n := 2 * n + 1) hi_le hPi
    rw [iN]; exact this
  -- positivity of dims of phi Q (iN n)
  have hposmJ : 1 ≤ (phi Q (iN n)).m := (dimPos.1 (iN n)).1
  have hposnJ : 1 ≤ (phi Q (iN n)).n := (dimPos.1 (iN n)).2
  -- the regime condition is satisfied for `fam n`
  set j : ℕ := iN n with hj
  have hcond : (1 ≤ (phi Q (iN n)).m ∧ (phi Q (iN n)).m ≤ 2 ^ n) ∧
               (1 ≤ (phi Q (iN n)).n ∧ (phi Q (iN n)).n ≤ 2 ^ n) :=
    ⟨⟨hposmJ, hspec.1⟩, ⟨hposnJ, hspec.2⟩⟩
  -- extract the chosen surjections and the precomposition identity from `fam_exists`
  obtain ⟨σ, τ, hσ, hτ, hfam⟩ := Classical.choose_spec (fam_exists n) hcond
  -- Step 4 : D (fam n) = Dmat (phi Q (iN n))
  have hD4 : D (fam n) = Dmat (phi Q (iN n)) := by
    rw [show fam n = fun u v => (phi Q (iN n)).e (σ u) (τ v) from hfam]
    have := Proof.ProofLemmas.SublemmaPrecompEq (phi Q (iN n)).e σ τ hσ hτ
    rw [this]; rfl
  -- Step 5 : D (directSum (fam n) ℓ) = D (directSum (phi Q (iN n)).e ℓ)
  have hD5 : D (directSum (fam n) (178 * (L + 1)))
      = D (directSum ((phi Q (iN n)).e) (178 * (L + 1))) := by
    have hds : directSum (fam n) (178 * (L + 1))
        = directSum (fun u v => (phi Q (iN n)).e (σ u) (τ v)) (178 * (L + 1)) := by
      rw [show fam n = fun u v => (phi Q (iN n)).e (σ u) (τ v) from hfam]
    rw [hds]
    exact Proof.ProofLemmas.SublemmaDirectSumPrecomp (phi Q (iN n)).e σ τ hσ hτ (178 * (L + 1))
  -- lower bound (Cor 4.24)
  have hj1 : 1 ≤ j := by
    rw [hj]; omega
  have hlow : (10000 : ℕ) * j ≤ Dmat (phi Q j) :=
    Proof.PhiInduction.corollary_4_24_lower_bound_phi j hj1
  -- i ≤ j
  have hij : i ≤ j := by rw [hj]; exact hi_le_iN
  -- nat-subtraction identity
  have hsub : 178 * 10000 * (L + 1) - (L + 1) = (L + 1) * (178 * 10000 - 1) := by omega
  -- target rewrite (puts goal entirely in MY `Q`)
  rw [hD4, hD5]
  -- upper bound (Cor 5.8) with h = L+1, brought into MY `Q` via a single ascription
  have hup0 : D (directSum (phi Q (iN n)).e (178 * (L + 1)))
      ≤ 178 * (L + 1) + (iN n) * (178 * 10000 * (L + 1) - (L + 1)) := by
    have h := Proof.UpperBound.upper_bound_directSum_phi_5_8 (iN n) (L + 1) (Nat.le_add_left 1 L)
    convert h using 3
  -- abstract the two communication-complexity naturals as opaque variables
  set Dphi : ℕ := Dmat (phi Q (iN n)) with hDphi
  set Dl : ℕ := D (directSum (phi Q (iN n)).e (178 * (L + 1))) with hDl
  -- now hup0 : Dl ≤ ... and hlow : 10000*j ≤ Dphi (after folding j = iN n)
  have hup : Dl ≤ 178 * (L + 1) + j * (178 * 10000 * (L + 1) - (L + 1)) := hup0
  have hlow' : (10000 : ℕ) * j ≤ Dphi := hlow
  rw [hsub] at hup
  -- detach the let-bound values so later tactics never unfold `iN n`/`phi Q …`
  rw [hi] at hij
  clear_value Dphi Dl j n i
  clear hfam hσ hτ hcond hspec hposmJ hposnJ hi_le_iN hPi hi_le
    hInSn hclogm hclogn hposm hposn hn hD4 hD5 hj1 hDphi hDl hup0 hj hlow hi
    hdimPos hdimUnb dimPos dimUnb σ τ
  -- real versions (no D-atoms inside, so push_cast is safe)
  have hupR : (Dl : ℝ) ≤ 178 * (L + 1) + (j : ℝ) * ((L + 1) * (178 * 10000 - 1)) := by
    have := (Nat.cast_le (α := ℝ)).2 hup
    push_cast at this ⊢
    linarith [this]
  have hlowR : (10000 : ℝ) * (j : ℝ) ≤ (Dphi : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 hlow'
    push_cast at this ⊢
    linarith [this]
  have hijR : (178 : ℝ) * ((C : ℝ) + 2) ≤ (j : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 hij
    push_cast at this
    linarith [this]
  have hLpos : (0 : ℝ) < (L : ℝ) + 1 := by
    have h := Nat.cast_nonneg (α := ℝ) L; linarith
  have hℓpos : (0 : ℝ) < (178 : ℝ) * ((L : ℝ) + 1) := mul_pos (by norm_num) hLpos
  -- Now goal: (Dphi : ℝ) > (Dl : ℝ)/(↑(178*(L+1))) + C
  have hcast : ((178 * (L + 1) : ℕ) : ℝ) = (178 : ℝ) * ((L : ℝ) + 1) := by push_cast; ring
  rw [hcast]
  rw [gt_iff_lt, div_add' _ _ _ (ne_of_gt hℓpos), div_lt_iff₀ hℓpos]
  -- the goal and all `…R`/pos hypotheses are now in fresh real atoms; abstract them
  -- away from any `phi Q …`-bearing term so `nlinarith` never reduces `Q = 255*2^9992`
  have hjR0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg (α := ℝ) j
  revert hupR hlowR hijR hLpos hℓpos hjR0
  generalize (Dphi : ℝ) = dphi
  generalize (Dl : ℝ) = dl
  generalize (j : ℝ) = jr
  generalize (L : ℝ) = lr
  generalize (C : ℝ) = cr
  intro hupR hlowR hijR hLpos hℓpos hjR0
  nlinarith [hlowR, hupR, hijR, hLpos, hℓpos,
    mul_le_mul_of_nonneg_right hijR (le_of_lt hLpos),
    mul_nonneg (le_of_lt hLpos) hjR0]

/-- A protocol of cost `0` is a leaf, hence computes a constant function. -/
private theorem cost_zero_const {X Y Z : Type*} (P : Protocol X Y Z) (h : P.cost = 0) :
    ∃ z : Z, ∀ x y, Protocol.eval P x y = z := by
  cases P with
  | leaf z => exact ⟨z, fun x y => rfl⟩
  | aNode a l r => simp [Protocol.cost] at h
  | bNode b l r => simp [Protocol.cost] at h

/-- `φ_0`'s entry function: true on column 0, false on column 1. -/
private theorem phi_zero_e00 :
    (phi Q 0).e ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = true := by
  simp [phi_zero]

private theorem phi_zero_e01 :
    (phi Q 0).e ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ = false := by
  simp [phi_zero]

/-- The base game `φ_0` requires at least one bit of communication:
`1 ≤ Dmat (phi Q 0)`. -/
private theorem one_le_Dmat_phi_zero : 1 ≤ Dmat (phi Q 0) := by
  unfold Dmat D
  have hb : (phi Q 0).n = 2 := rfl
  set P : Protocol (Fin (phi Q 0).m) (Fin (phi Q 0).n) Bool :=
    Protocol.bNode (fun y => decide ((y : ℕ) = 1)) (Protocol.leaf true) (Protocol.leaf false)
    with hPdef
  have hPcost : P.cost = 1 := by simp [hPdef, Protocol.cost]
  have hPcomp : Protocol.Computes P (phi Q 0).e := by
    intro x y
    fin_cases x
    fin_cases y
    · simp [hPdef, Protocol.eval, phi_zero]
    · simp [hPdef, Protocol.eval, phi_zero]
  have hne : (AchievableCosts (phi Q 0).e).Nonempty := ⟨1, P, hPcost, hPcomp⟩
  rw [Nat.one_le_iff_ne_zero]
  intro hzero
  have hsm := Nat.sInf_mem hne
  rw [hzero] at hsm
  have hmem : (0 : ℕ) ∈ AchievableCosts (phi Q 0).e := hsm
  obtain ⟨P0, hcost, hcomp⟩ := hmem
  obtain ⟨z, hz⟩ := cost_zero_const P0 hcost
  have h0 := hcomp ⟨0, by norm_num⟩ ⟨0, by norm_num⟩
  have h1 := hcomp ⟨0, by norm_num⟩ ⟨1, by norm_num⟩
  rw [hz, phi_zero_e00] at h0
  rw [hz, phi_zero_e01] at h1
  rw [h0] at h1
  simp at h1

/-- Theorem 5.10 (Quantitative / multiplicative consequence).
With `B = Q = 255 · 2^{10000-8}`, for all `i`,
`D(φ_i^{178}) ≤ 178 · D(φ_i) + 177`. -/
theorem multiplicative_consequence (i : ℕ) :
    D (directSum (phi Q i).e 178) ≤ 178 * Dmat (phi Q i) + 177 := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · -- i = 0
    subst hi
    have hub := Proof.UpperBound.upper_bound_directSum_phi_5_8 0 1 (le_refl 1)
    simp only [Nat.mul_one, Nat.zero_mul, Nat.add_zero] at hub
    have hlow := one_le_Dmat_phi_zero
    calc D (directSum (phi Q 0).e 178) ≤ 178 := hub
      _ ≤ 178 * Dmat (phi Q 0) + 177 := by
          have : 178 * 1 ≤ 178 * Dmat (phi Q 0) := Nat.mul_le_mul_left 178 hlow
          omega
  · -- i ≥ 1
    have hub := Proof.UpperBound.upper_bound_directSum_phi_5_8 i 1 (le_refl 1)
    simp only [Nat.mul_one] at hub
    have hlow := Proof.PhiInduction.corollary_4_24_lower_bound_phi i hi
    have key : 178 + i * (178 * 10000 * 1 - 1) ≤ 178 * Dmat (phi Q i) + 177 := by
      have h2 : 178 * (10000 * i) ≤ 178 * Dmat (phi Q i) := Nat.mul_le_mul_left 178 hlow
      have harith : 178 + i * (178 * 10000 * 1 - 1) ≤ 178 * (10000 * i) + 177 := by
        ring_nf
        omega
      omega
    exact le_trans hub key

end Proof.MainTheorem

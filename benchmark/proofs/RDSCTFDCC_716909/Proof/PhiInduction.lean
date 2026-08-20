import Mathlib
import Proof.Types.BoolMat
import Proof.Types.AlternatingGame
import Proof.Types.Bracket
import Proof.Types.Lambda
import Proof.Types.MatComplexity
import Proof.Types.Protocol
import Proof.Types.CommComplexity
import Proof.Types.Interlace
import Proof.Types.Extract
import Proof.Types.Equipartition
import Proof.PhiBase
import Proof.BracketLemmas
import Proof.ProofLemmas.DimRecurrence

open Proof.Types.BoolMat
open Proof.Types.AlternatingGame
open Proof.Types.Bracket
open Proof.Types.Lambda
open Proof.Types.MatComplexity
open Proof.Types.Protocol
open Proof.Types.CommComplexity
open Proof.Types.Interlace
open Proof.Types.Extract
open Proof.Types.Equipartition

/-- The paper fixes `B = Q = 255·2^{k-8}` with `k = 10000`, `a = 10` from Section 4 onward. -/
private abbrev Q : ℕ := 255 * 2 ^ (10000 - 8)

namespace Proof.PhiInduction

/-- Lemma 4.12 (Row divisibility of `φ_i`). For `k = 10000`, `a = 10`, any `i ≥ 1`: both the
number of rows and the number of columns of `φ_i` are divisible by `2^{a+2}` (`= 2^{10+2}`). -/
theorem lemma_4_12_row_divisibility (i : ℕ) (hi : 1 ≤ i) :
    2 ^ (10 + 2) ∣ (phi Q i).m ∧ 2 ^ (10 + 2) ∣ (phi Q i).n := by
  -- Positivity of Q and the key divisibility 2^12 ∣ Q.
  have hpow_pos : 0 < 2 ^ (10000 - 8) := pow_pos (by norm_num) _
  have hQpos : 0 < Q := by
    have : (2 : ℕ) ≤ 255 * 2 ^ (10000 - 8) :=
      le_trans (by norm_num) (Nat.mul_le_mul_left 255 hpow_pos)
    exact lt_of_lt_of_le (by norm_num) this
  have hQne : Q ≠ 0 := Nat.pos_iff_ne_zero.mp hQpos
  have hQdvd : 2 ^ (10 + 2) ∣ Q := by
    have h1 : (2 : ℕ) ^ (10 + 2) ∣ 2 ^ (10000 - 8) :=
      pow_dvd_pow 2 (by norm_num)
    exact Dvd.dvd.mul_left h1 255
  -- 12 ≤ Q via 12 ≤ 2^12 ≤ 2^9992 ≤ 255 * 2^9992 = Q.
  have h12Q : 12 ≤ Q := by
    have ha : (12 : ℕ) ≤ 2 ^ (10 + 2) := by norm_num
    have hb : (2 : ℕ) ^ (10 + 2) ≤ 2 ^ (10000 - 8) :=
      Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have hc : (2 : ℕ) ^ (10000 - 8) ≤ 255 * 2 ^ (10000 - 8) :=
      Nat.le_mul_of_pos_left _ (by norm_num)
    calc (12 : ℕ) ≤ 2 ^ (10 + 2) := ha
      _ ≤ 2 ^ (10000 - 8) := hb
      _ ≤ Q := hc
  induction i, hi using Nat.le_induction with
  | base =>
    -- i = 1 : (phi Q 1).m = (phi Q 0).n ^ Q = 2 ^ Q, (phi Q 1).n = (phi Q 0).m * Q = Q.
    obtain ⟨hm, hn⟩ := Proof.ProofLemmas.DimRecurrence 0
    refine ⟨?_, ?_⟩
    · rw [hm]
      simp only [phi_zero]
      -- goal : 2^12 ∣ 2 ^ Q
      exact pow_dvd_pow 2 h12Q
    · rw [hn]
      simp only [phi_zero]
      -- goal : 2^12 ∣ 1 * Q
      rw [one_mul]
      exact hQdvd
  | succ i hi ih =>
    obtain ⟨ihm, ihn⟩ := ih
    obtain ⟨hm, hn⟩ := Proof.ProofLemmas.DimRecurrence i
    refine ⟨?_, ?_⟩
    · rw [hm]
      exact dvd_pow ihn hQne
    · rw [hn]
      exact Dvd.dvd.mul_right ihm _

/-- Lemma 4.13 (Shifted-rung arithmetic). For `k = 10000`, `a = 10`, `ρ = √(k+a)`,
`β = (ρ−1)/(ρ−2)`, `Q = 255·2^{k-8}`, and `k_j = k−j`, `a_j = a+j`,
`P_j = ⌊ Q · (2^{a−3/8} − 1)/(2^{a_j} − 1) ⌋` for `j ∈ {0,1,2}`: for each `j`,
`(ρ−1)^{k_j−3} ≤ ρ^{k_j−5}` and `P_j ≥ ⌊ 6·2^{k_j−3}·β^2 ⌋`. -/
theorem lemma_4_13_shifted_rung_arithmetic :
    ∀ j : ℕ, j < 3 →
      let ρ : ℝ := Real.sqrt (10000 + 10)
      let β : ℝ := (ρ - 1) / (ρ - 2)
      let k_j : ℕ := 10000 - j
      let a_j : ℕ := 10 + j
      let P_j : ℕ :=
        ⌊ (Q : ℝ) * ((Real.rpow 2 (10 - 3 / 8) - 1) / (Real.rpow 2 (a_j : ℝ) - 1)) ⌋₊
      Real.rpow (ρ - 1) ((k_j : ℝ) - 3) ≤ Real.rpow ρ ((k_j : ℝ) - 5) ∧
        P_j ≥ ⌊ 6 * Real.rpow 2 ((k_j : ℝ) - 3) * β ^ 2 ⌋₊ := by
  intro j hj ρ β k_j a_j P_j
  -- ρ bounds: 100 < ρ < 101
  have hρlo : (100:ℝ) < ρ := by
    show (100:ℝ) < Real.sqrt (10000 + 10)
    rw [show (100:ℝ) = Real.sqrt (100^2) by rw [Real.sqrt_sq] <;> norm_num]
    apply Real.sqrt_lt_sqrt <;> norm_num
  have hρhi : ρ < 101 := by
    show Real.sqrt (10000 + 10) < 101
    rw [show (101:ℝ) = Real.sqrt (101^2) by rw [Real.sqrt_sq] <;> norm_num]
    apply Real.sqrt_lt_sqrt <;> norm_num
  have hρpos : (0:ℝ) < ρ := by linarith
  have hρsq : ρ ^ 2 = 10010 := by
    show (Real.sqrt (10000 + 10)) ^ 2 = 10010
    rw [Real.sq_sqrt (by norm_num)]; norm_num
  have hkj : (k_j : ℝ) = 10000 - (j : ℝ) := by
    show ((10000 - j : ℕ) : ℝ) = 10000 - (j : ℝ)
    rw [Nat.cast_sub (by omega)]; norm_num
  have hjle : (j : ℝ) ≤ 2 := by
    have : j ≤ 2 := by omega
    exact_mod_cast this
  have hn_lo : (9995:ℝ) ≤ (k_j : ℝ) - 3 := by rw [hkj]; linarith
  have hn_nonneg : (0:ℝ) ≤ (k_j : ℝ) - 3 := by linarith
  have hn5_nonneg : (0:ℝ) ≤ (k_j : ℝ) - 5 := by linarith
  refine ⟨?_, ?_⟩
  · -- Part B: (ρ-1)^(k_j-3) ≤ ρ^(k_j-5)
    set n : ℝ := (k_j : ℝ) - 3 with hn
    have hn5 : (k_j : ℝ) - 5 = n - 2 := by rw [hn]; ring
    rw [hn5]
    have hρ1 : ρ - 1 = ρ * (1 - 1/ρ) := by field_simp
    have h1mρ_nonneg : (0:ℝ) ≤ 1 - 1/ρ := by
      have : 1/ρ ≤ 1 := by rw [div_le_one hρpos]; linarith
      linarith
    have hfactor : (ρ - 1).rpow n = ρ.rpow n * (1 - 1/ρ).rpow n := by
      rw [hρ1]; exact Real.mul_rpow (le_of_lt hρpos) h1mρ_nonneg
    have hexp : 1 - 1/ρ ≤ Real.exp (-(1/ρ)) := by
      have := Real.add_one_le_exp (-(1/ρ))
      linarith
    have hpow_exp : (1 - 1/ρ).rpow n ≤ Real.exp (-(n/ρ)) := by
      calc (1 - 1/ρ).rpow n ≤ (Real.exp (-(1/ρ))).rpow n :=
            Real.rpow_le_rpow h1mρ_nonneg hexp hn_nonneg
        _ = Real.exp (-(1/ρ) * n) := (Real.exp_mul _ _).symm
        _ = Real.exp (-(n/ρ)) := by rw [show -(1/ρ) * n = -(n/ρ) by ring]
    have hexp_mono : Real.exp (-(n/ρ)) ≤ Real.exp (-(9995/101)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff]
      have hkey : (9995:ℝ)/101 ≤ n/ρ := by
        rw [div_le_div_iff₀ (by norm_num) hρpos]; nlinarith [hρhi, hn_lo]
      exact hkey
    have hρm2 : ρ.rpow (-2) = 1 / 10010 := by
      have : ρ.rpow (-2) = (ρ.rpow 2)⁻¹ := by
        rw [show (-2:ℝ) = -(2:ℝ) by ring]
        exact Real.rpow_neg (le_of_lt hρpos) 2
      rw [this]
      have h2 : ρ.rpow 2 = ρ ^ (2:ℕ) := by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num]; exact Real.rpow_natCast ρ 2
      rw [h2, hρsq]; norm_num
    have hexp_key : Real.exp (-(9995/101)) < ρ.rpow (-2) := by
      rw [hρm2]
      have h10 : (10010:ℝ) < Real.exp (9995/101) := by
        have he10 : (10010:ℝ) < Real.exp 10 := by
          have he1 : (2.7:ℝ) < Real.exp 1 := by
            have := Real.exp_one_gt_d9
            linarith
          have heq : Real.exp 10 = (Real.exp 1) ^ (10:ℕ) := by
            rw [← Real.exp_nat_mul]; norm_num
          rw [heq]
          calc (10010:ℝ) < (2.7:ℝ) ^ (10:ℕ) := by norm_num
            _ ≤ (Real.exp 1) ^ (10:ℕ) := by
                apply pow_le_pow_left₀ (by norm_num) (le_of_lt he1)
        calc (10010:ℝ) < Real.exp 10 := he10
          _ ≤ Real.exp (9995/101) := by
              apply Real.exp_le_exp.mpr; norm_num
      rw [Real.exp_neg]
      rw [show (1:ℝ)/10010 = (10010:ℝ)⁻¹ by norm_num]
      exact (inv_lt_inv₀ (by positivity) (by norm_num)).mpr h10
    have hρn_pos : (0:ℝ) < ρ.rpow n := Real.rpow_pos_of_pos hρpos n
    have hsub : ρ.rpow (n - 2) = ρ.rpow n * ρ.rpow (-2) := by
      rw [show ρ.rpow (n-2) = ρ.rpow (n + (-2)) by ring_nf]
      exact Real.rpow_add hρpos n (-2)
    rw [hfactor, hsub]
    have hchain : (1 - 1/ρ).rpow n ≤ ρ.rpow (-2) :=
      le_trans hpow_exp (le_trans hexp_mono (le_of_lt hexp_key))
    exact mul_le_mul_of_nonneg_left hchain (le_of_lt hρn_pos)
  · -- Part C: P_j ≥ ⌊ 6 * 2^(k_j-3) * β^2 ⌋₊
    have hρm2' : (0:ℝ) < ρ - 2 := by linarith
    have hβpos : (0:ℝ) < β := by
      show (0:ℝ) < (ρ - 1) / (ρ - 2)
      apply div_pos (by linarith) hρm2'
    have hβhi : β < 99/98 := by
      show (ρ - 1) / (ρ - 2) < 99/98
      rw [div_lt_div_iff₀ hρm2' (by norm_num)]
      nlinarith [hρlo]
    have hβsq : β ^ 2 < (99/98)^2 := by
      have := mul_lt_mul'' hβhi hβhi (le_of_lt hβpos) (le_of_lt hβpos)
      rw [pow_two, pow_two]; linarith [this]
    have hβsq_nonneg : (0:ℝ) ≤ β ^ 2 := by positivity
    have h238_pos : (0:ℝ) < Real.rpow 2 (3/8 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    have h238 : Real.rpow 2 (3/8 : ℝ) < 13/10 := by
      apply lt_of_pow_lt_pow_left₀ 8 (by norm_num : (0:ℝ) ≤ 13/10)
      have he : (Real.rpow 2 (3/8 : ℝ)) ^ (8:ℕ) = 8 := by
        rw [show Real.rpow 2 (3/8:ℝ) = (2:ℝ) ^ (3/8:ℝ) from rfl,
            ← Real.rpow_natCast ((2:ℝ) ^ (3/8:ℝ)) 8,
            ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
      rw [he]; norm_num
    have hval238 : Real.rpow 2 (10 - 3 / 8) = 1024 / Real.rpow 2 (3/8 : ℝ) := by
      rw [show (10 - 3/8 : ℝ) = (10:ℝ) + (-(3/8:ℝ)) by ring]
      rw [show Real.rpow 2 ((10:ℝ) + (-(3/8:ℝ))) = (2:ℝ) ^ ((10:ℝ) + (-(3/8:ℝ))) from rfl,
          Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      rw [show ((2:ℝ) ^ (10:ℝ)) = (1024:ℝ) by
            rw [show (10:ℝ) = ((10:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num]
      rw [show ((2:ℝ) ^ (3/8:ℝ)) = Real.rpow 2 (3/8:ℝ) from rfl]
      rw [div_eq_mul_inv]; ring
    have hden1_lb : (10227:ℝ)/13 < Real.rpow 2 (10 - 3 / 8) - 1 := by
      rw [hval238]
      have hstep : (10240:ℝ)/13 < 1024 / Real.rpow 2 (3/8:ℝ) := by
        rw [div_lt_div_iff₀ (by norm_num) h238_pos]
        nlinarith [h238, h238_pos]
      linarith
    have hden1_pos : (0:ℝ) < Real.rpow 2 (10 - 3 / 8) - 1 := by
      have : (0:ℝ) < 10227/13 := by norm_num
      linarith
    have hQreal : (Q : ℝ) = 255 * (2:ℝ)^(9992:ℕ) := by
      show ((255 * 2 ^ (10000 - 8) : ℕ) : ℝ) = 255 * (2:ℝ)^(9992:ℕ)
      rw [show (10000 - 8 : ℕ) = 9992 from rfl]
      push_cast; ring
    have hpow_pos : (0:ℝ) < (2:ℝ)^(9992:ℕ) := by positivity
    have hpow_fac : Real.rpow 2 ((k_j : ℝ) - 3) = (2:ℝ)^(9992:ℕ) * Real.rpow 2 (5 - (j:ℝ)) := by
      rw [hkj]
      rw [show (10000 - (j:ℝ)) - 3 = (9992:ℝ) + (5 - (j:ℝ)) by ring]
      rw [show Real.rpow 2 ((9992:ℝ) + (5 - (j:ℝ))) = (2:ℝ) ^ ((9992:ℝ) + (5 - (j:ℝ))) from rfl,
         Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1
      rw [show (9992:ℝ) = ((9992:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    apply Nat.floor_le_floor
    rw [hpow_fac, hQreal]
    have haj_concrete : Real.rpow 2 (a_j : ℝ) - 1 > 0 := by
      have : (1024:ℝ) ≤ Real.rpow 2 (a_j : ℝ) := by
        have haj : (a_j:ℝ) = 10 + (j:ℝ) := by
          show ((10 + j : ℕ):ℝ) = 10 + (j:ℝ); push_cast; ring
        rw [haj]
        calc (1024:ℝ) = Real.rpow 2 (10:ℝ) := by
                rw [show (10:ℝ) = ((10:ℕ):ℝ) by norm_num,
                    show Real.rpow 2 ((10:ℕ):ℝ) = (2:ℝ) ^ ((10:ℕ):ℝ) from rfl,
                    Real.rpow_natCast]; norm_num
          _ ≤ Real.rpow 2 (10 + (j:ℝ)) := by
                apply Real.rpow_le_rpow_of_exponent_le (by norm_num); simp
      linarith
    rw [← mul_div_assoc, le_div_iff₀ haj_concrete]
    have hajeq : (a_j:ℝ) = 10 + (j:ℝ) := by
      show ((10 + j : ℕ):ℝ) = 10 + (j:ℝ); push_cast; ring
    have hcore : 6 * Real.rpow 2 (5 - (j:ℝ)) * β^2 * (Real.rpow 2 (a_j:ℝ) - 1)
        ≤ 255 * (Real.rpow 2 (10 - 3/8) - 1) := by
      rw [hajeq]
      have hβ2lt : β^2 < (99/98)^2 := hβsq
      set D1 : ℝ := Real.rpow 2 (10 - 3/8) - 1 with hD1
      clear_value k_j a_j P_j ρ
      interval_cases j
      · have e1 : Real.rpow 2 (5 - ((0:ℕ):ℝ)) = 32 := by
          rw [show (5 - ((0:ℕ):ℝ)) = ((5:ℕ):ℝ) by norm_num,
              show Real.rpow 2 ((5:ℕ):ℝ) = (2:ℝ)^((5:ℕ):ℝ) from rfl, Real.rpow_natCast]; norm_num
        have e2 : Real.rpow 2 (10 + ((0:ℕ):ℝ)) = 1024 := by
          rw [show (10 + ((0:ℕ):ℝ)) = ((10:ℕ):ℝ) by norm_num,
              show Real.rpow 2 ((10:ℕ):ℝ) = (2:ℝ)^((10:ℕ):ℝ) from rfl, Real.rpow_natCast]; norm_num
        rw [e1, e2]; nlinarith [hβ2lt, hden1_lb, hβsq_nonneg, hden1_pos]
      · have e1 : Real.rpow 2 (5 - ((1:ℕ):ℝ)) = 16 := by
          rw [show (5 - ((1:ℕ):ℝ)) = ((4:ℕ):ℝ) by norm_num,
              show Real.rpow 2 ((4:ℕ):ℝ) = (2:ℝ)^((4:ℕ):ℝ) from rfl, Real.rpow_natCast]; norm_num
        have e2 : Real.rpow 2 (10 + ((1:ℕ):ℝ)) = 2048 := by
          rw [show (10 + ((1:ℕ):ℝ)) = ((11:ℕ):ℝ) by norm_num,
              show Real.rpow 2 ((11:ℕ):ℝ) = (2:ℝ)^((11:ℕ):ℝ) from rfl, Real.rpow_natCast]; norm_num
        rw [e1, e2]; nlinarith [hβ2lt, hden1_lb, hβsq_nonneg, hden1_pos]
      · have e1 : Real.rpow 2 (5 - ((2:ℕ):ℝ)) = 8 := by
          rw [show (5 - ((2:ℕ):ℝ)) = ((3:ℕ):ℝ) by norm_num,
              show Real.rpow 2 ((3:ℕ):ℝ) = (2:ℝ)^((3:ℕ):ℝ) from rfl, Real.rpow_natCast]; norm_num
        have e2 : Real.rpow 2 (10 + ((2:ℕ):ℝ)) = 4096 := by
          rw [show (10 + ((2:ℕ):ℝ)) = ((12:ℕ):ℝ) by norm_num,
              show Real.rpow 2 ((12:ℕ):ℝ) = (2:ℝ)^((12:ℕ):ℝ) from rfl, Real.rpow_natCast]; norm_num
        rw [e1, e2]; nlinarith [hβ2lt, hden1_lb, hβsq_nonneg, hden1_pos]
    calc 6 * (2 ^ 9992 * Real.rpow 2 (5 - (j:ℝ))) * β ^ 2 * (Real.rpow 2 (a_j:ℝ) - 1)
          = (2:ℝ)^(9992:ℕ) * (6 * Real.rpow 2 (5 - (j:ℝ)) * β^2 * (Real.rpow 2 (a_j:ℝ) - 1)) := by ring
      _ ≤ (2:ℝ)^(9992:ℕ) * (255 * (Real.rpow 2 (10 - 3/8) - 1)) :=
          mul_le_mul_of_nonneg_left hcore (le_of_lt hpow_pos)
      _ = 255 * 2 ^ 9992 * (Real.rpow 2 (10 - 3 / 8) - 1) := by ring

private theorem p414_rp2 (e : ℝ) : Real.rpow 2 e = (2:ℝ)^e := rfl
private theorem p414_rpf (b e : ℝ) : Real.rpow b e = b ^ e := rfl

/-- Per-`j` bound (statement (7) of the NL proof): for each `j ∈ {0,1,2}`,
`D([φ_{i+1}]_{1, 2^{-k-a}, η_j}) ≥ (k - j) + Λ_{φ_i}(1, 2^{-k-a}, 2^{-3/8})`. -/
private theorem p414_per_j (i : ℕ) (hi : 1 ≤ i)
    (hside :
      DSet (bracket (phi Q i) 1 (Real.rpow 2 (-(10000 : ℝ) - 10)) (Real.rpow 2 (-3))) ≥ 1)
    (j : ℕ) (hj : j < 3) :
    DSet (bracket (phi Q (i + 1)) 1 (Real.rpow 2 (-(10000 : ℝ) - 10))
        (Real.rpow 2 (-3 / 8 - (j : ℝ)))) ≥
      (10000 - j) +
        Lambda (phi Q i) 1 (Real.rpow 2 (-(10000 : ℝ) - 10)) (Real.rpow 2 (-3 / 8)) := by
  -- Abbreviations.
  set M : BoolMat := phi Q i with hM
  set x0 : ℝ := Real.rpow 2 (-(10000 : ℝ) - 10) with hx0def
  -- ρ = √(k+a) = √10010, β = (ρ-1)/(ρ-2).
  set ρ : ℝ := Real.sqrt (10000 + 10) with hρdef
  set β : ℝ := (ρ - 1) / (ρ - 2) with hβdef
  -- Numerical facts about ρ.
  have hρlo : (100:ℝ) < ρ := by
    rw [hρdef, show (100:ℝ) = Real.sqrt (100^2) by rw [Real.sqrt_sq] <;> norm_num]
    apply Real.sqrt_lt_sqrt <;> norm_num
  have hρhi : ρ < 101 := by
    rw [hρdef, show (101:ℝ) = Real.sqrt (101^2) by rw [Real.sqrt_sq] <;> norm_num]
    apply Real.sqrt_lt_sqrt <;> norm_num
  have hρ2 : (2:ℝ) < ρ := by linarith
  have hρpos : (0:ℝ) < ρ := by linarith
  have hρsq : ρ^2 = 10010 := by
    rw [hρdef, Real.sq_sqrt (by norm_num)]; norm_num
  -- j-dependent parameters (over ℝ).
  have hjle : (j:ℝ) ≤ 2 := by have : j ≤ 2 := by omega
                              exact_mod_cast this
  have hj0 : (0:ℝ) ≤ (j:ℝ) := by positivity
  -- k_j - 3 = 9997 - j, k_j = 10000 - j (as reals).
  -- α = 2^{a-3/8} = 2^{10-3/8}, x_j = 2^{-a-j} = 2^{-10-j}.
  set α : ℝ := Real.rpow 2 (10 - 3/8) with hαdef
  set xj : ℝ := Real.rpow 2 (-10 - (j:ℝ)) with hxjdef
  -- α·x_j = η_j = 2^{-3/8-j}.
  have hαxj : α * xj = Real.rpow 2 (-3/8 - (j:ℝ)) := by
    rw [hαdef, hxjdef]; simp only [p414_rp2]
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; ring_nf
  have hα1 : (1:ℝ) < α := by
    rw [hαdef, p414_rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  have hxj0 : (0:ℝ) < xj := by rw [hxjdef, p414_rp2]; positivity
  have hxj1 : xj < 1 := by
    rw [hxjdef, p414_rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hαxj0 : (0:ℝ) < α * xj := by rw [hαxj, p414_rp2]; positivity
  have hαxj1 : α * xj ≤ 1 := by
    rw [hαxj, p414_rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hx00 : (0:ℝ) < x0 := by rw [hx0def, p414_rp2]; positivity
  have hx01 : x0 ≤ 1 := by
    rw [hx0def, p414_rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  -- The integrality precondition for extended_balancing: M.m · x_j ∈ ℕ.
  have hdiv : ∃ t : ℕ, (M.m : ℝ) * xj = (t : ℝ) := by
    obtain ⟨hdvd, _⟩ := lemma_4_12_row_divisibility i hi
    have h10j : (2:ℕ)^(10 + j) ∣ M.m := by
      rw [hM]; exact dvd_trans (pow_dvd_pow 2 (by omega)) hdvd
    obtain ⟨c, hc⟩ := h10j
    refine ⟨c, ?_⟩
    rw [hxjdef, p414_rp2, hc]
    rw [show (-10 - (j:ℝ)) = -(((10 + j : ℕ)):ℝ) by push_cast; ring,
        Real.rpow_neg (by norm_num), Real.rpow_natCast]
    push_cast
    field_simp
  -- The balancing partition floor p* = P_j; the numeric bound from Lemma 4.13.
  set Pj : ℕ := ⌊(Q : ℝ) * (α - 1) * xj / (1 - xj)⌋₊ with hPjdef
  -- (α-1)·x_j/(1-x_j) = (2^{10-3/8}-1)/(2^{10+j}-1).
  have hmul_eq : (α - 1) * xj / (1 - xj)
      = (Real.rpow 2 (10 - 3/8) - 1) / (Real.rpow 2 ((10 + j : ℕ):ℝ) - 1) := by
    rw [hαdef, hxjdef]
    have hpow1 : Real.rpow 2 (-10 - (j:ℝ)) = (Real.rpow 2 ((10 + j : ℕ):ℝ))⁻¹ := by
      simp only [p414_rp2]
      rw [show (-10 - (j:ℝ)) = -(((10 + j : ℕ)):ℝ) by push_cast; ring,
          Real.rpow_neg (by norm_num)]
    rw [hpow1]
    set A : ℝ := Real.rpow 2 (10 - 3/8) with hAdef
    set B : ℝ := Real.rpow 2 ((10 + j : ℕ):ℝ) with hBdef
    have hBpos : (0:ℝ) < B := by rw [hBdef, p414_rp2]; positivity
    have hB1 : (1:ℝ) < B := by
      rw [hBdef, p414_rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by positivity)
    field_simp
  -- P_j ≥ ⌊6·2^{k_j-3}·β²⌋ from Lemma 4.13 (with Q on the left).
  set p'j : ℕ := ⌊6 * Real.rpow 2 (((10000 - j : ℕ):ℝ) - 3) * β ^ 2⌋₊ with hp'jdef
  have h413 := lemma_4_13_shifted_rung_arithmetic j hj
  simp only at h413
  obtain ⟨h413rung, h413P⟩ := h413
  -- h413P : ⌊Q·((2^{10-3/8}-1)/(2^{10+j}-1))⌋₊ ≥ ⌊6·2^{(10000-j)-3}·β²⌋₊
  -- Bridge P_j = ⌊Q·(α-1)x_j/(1-x_j)⌋₊ to the 4.13 form.
  have hPj_eq : Pj = ⌊(Q : ℝ) * ((Real.rpow 2 (10 - 3/8) - 1)
      / (Real.rpow 2 ((10 + j : ℕ):ℝ) - 1))⌋₊ := by
    rw [hPjdef]; congr 1
    rw [show (Q : ℝ) * (α - 1) * xj / (1 - xj) = (Q : ℝ) * ((α - 1) * xj / (1 - xj)) by ring]
    rw [hmul_eq]
  -- p'j matches 4.13's RHS floor (with ρ,β from 4.13 being our ρ,β).
  have hPk_ge_p'j : p'j ≤ Pj := by
    rw [hPj_eq, hp'jdef, hβdef]
    exact h413P
  have hp'j1 : 1 ≤ p'j := by
    rw [hp'jdef, Nat.one_le_floor_iff]
    -- 6·2^{(10000-j)-3}·β² ≥ 1.  2^{...}≥4 (exponent ≥9994≥2), β>1.
    have hβ12 : (1:ℝ) < β := by
      rw [hβdef, lt_div_iff₀ (by linarith : (0:ℝ) < ρ - 2)]; linarith
    have hβsq1 : (1:ℝ) ≤ β^2 := by nlinarith [hβ12]
    have hexp_nonneg : (0:ℝ) ≤ ((10000 - j : ℕ):ℝ) - 3 := by
      have : (9997:ℝ) ≤ ((10000 - j : ℕ):ℝ) := by
        rw [Nat.cast_sub (by omega : j ≤ 10000)]
        have : (j:ℝ) ≤ 2 := hjle; push_cast; linarith
      linarith
    have hrpow1 : (1:ℝ) ≤ Real.rpow 2 (((10000 - j : ℕ):ℝ) - 3) := by
      rw [p414_rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_nonneg
    nlinarith [hrpow1, hβsq1]
  -- ===== Step 1: transpose. =====
  rw [phi_succ]
  rw [← Proof.BracketLemmas.transpose_bracket (interlace M Q)
      (Real.rpow 2 (-3 / 8 - (j:ℝ))) x0]
  -- Goal: DSet (bracket (interlace M Q) 1 (η_j) x0) ≥ ...
  rw [← hαxj]
  -- ===== Step 1b: extended balancing. =====
  have hEB := Proof.BracketLemmas.extended_balancing M Q α xj x0
      hα1 hxj0 hxj1 hαxj0 hαxj1 hx00 hx01 hdiv (by rw [← hPjdef]; exact hp'j1.trans hPk_ge_p'j)
  rw [← hPjdef] at hEB
  -- hEB : DSet (bracket (interlace M Q) 1 (α*xj) x0) ≥ DSet (bracket M Pj xj x0)
  refine le_trans ?_ hEB
  -- ===== Step 2: monotonicity P_j ≥ p'_j. =====
  have hmono : DSet (bracket M p'j xj x0) ≤ DSet (bracket M Pj xj x0) :=
    Proof.BracketLemmas.monotonicity M p'j Pj xj xj x0 x0 hp'j1 hPk_ge_p'j
      hxj0 (le_refl xj) (le_of_lt hxj1) hx00 (le_refl x0) hx01
  refine le_trans ?_ hmono
  -- ===== Step 3+4 via Cor 4.9 and Lemma 4.10. =====
  -- k̃ = (10000-j)-3, s = 2, p = 6, xc = 2^{3-k-a} = 2^{-10007}, yc = 2^{-1}.
  set kt : ℕ := (10000 - j) - 3 with hktdef
  set xc : ℝ := Real.rpow 2 ((3:ℝ) - 10000 - 10) with hxcdef
  set yc : ℝ := Real.rpow 2 (-1) with hycdef
  -- ktR = (10000-j)-3 over ℝ = 9997 - j.
  have hktR : ((kt : ℕ):ℝ) = 9997 - (j:ℝ) := by
    rw [hktdef, Nat.cast_sub (by omega : 3 ≤ 10000 - j),
        Nat.cast_sub (by omega : j ≤ 10000)]
    push_cast; ring
  have hxc0 : (0:ℝ) < xc := by rw [hxcdef, p414_rp2]; positivity
  have hxck : xc ≤ Real.rpow 2 (-((kt:ℕ):ℝ)) := by
    rw [hxcdef, p414_rp2, p414_rp2, hktR]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hyc0 : (0:ℝ) < yc := by rw [hycdef, p414_rp2]; positivity
  have hyc1 : yc ≤ 1 := by
    rw [hycdef, p414_rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  -- yc/4 = 2^{-3}.
  have hyc4 : yc / 4 = Real.rpow 2 (-3) := by
    rw [hycdef]; simp only [p414_rp2]
    rw [show (-3:ℝ) = (-1) + (-2) by norm_num, Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    rw [show (2:ℝ)^(-2:ℝ) = 1/4 by
      rw [show (-2:ℝ) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg (by norm_num), Real.rpow_natCast]
      norm_num]
    ring
  -- Seed: D([M]_{6, xc, yc/4}) ≥ 1, from hside (= D([M]_{1, x0, 2^{-3}}) ≥ 1) by monotonicity.
  have hxc1 : xc ≤ 1 := le_trans hxck (by
    rw [p414_rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by simp only [neg_nonpos]; positivity))
  have hseed6 : DSet (bracket M 6 xc (yc / 4)) ≥ 1 := by
    rw [hyc4]
    have hxy : x0 ≤ xc := by
      rw [hx0def, hxcdef]; simp only [p414_rp2]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h23pos : (0:ℝ) < Real.rpow 2 (-3) := by rw [p414_rp2]; positivity
    have h23le1 : Real.rpow 2 (-3) ≤ 1 := by
      rw [p414_rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    calc (1:ℕ) ≤ DSet (bracket M 1 x0 (Real.rpow 2 (-3))) := hside
      _ ≤ DSet (bracket M 6 xc (Real.rpow 2 (-3))) :=
          Proof.BracketLemmas.monotonicity M 1 6 x0 xc (Real.rpow 2 (-3)) (Real.rpow 2 (-3))
            (le_refl 1) (by norm_num) hx00 hxy hxc1 h23pos (le_refl _) h23le1
  -- Rung condition for cor 4.9: (ρ-1)^{kt} ≤ ρ^{kt-2}, from 4.13 (h413rung gives kt-... form).
  have hrung6 : Real.rpow (ρ - 1) ((kt:ℕ):ℝ) ≤ Real.rpow ρ (((kt:ℕ):ℝ) - ((2:ℕ):ℝ)) := by
    rw [hρdef, hktR, show ((2:ℕ):ℝ) = (2:ℝ) by norm_num]
    -- h413rung : (ρ-1)^{(10000-j)-3} ≤ ρ^{(10000-j)-5}, and (10000-j)-3 = 9997-j, -5 → 9995-j.
    have e1 : ((10000 - j : ℕ):ℝ) - 3 = 9997 - (j:ℝ) := by
      rw [Nat.cast_sub (by omega : j ≤ 10000)]; push_cast; ring
    have e2 : ((10000 - j : ℕ):ℝ) - 5 = (9997 - (j:ℝ)) - 2 := by
      rw [Nat.cast_sub (by omega : j ≤ 10000)]; push_cast; ring
    rw [e1, e2] at h413rung
    exact h413rung
  -- H = Λ_M(6, xc, yc), with the three rung bounds (the canonical Λ-unfolding).
  set H : ℝ := (Lambda M 6 xc yc : ℝ) with hHdef
  have hH0 : (DSet (bracket M 6 xc yc) : ℝ) ≥ H := by
    rw [hHdef]; unfold Lambda; push_cast
    exact le_trans (min_le_left _ _) (le_refl _)
  have hH1 : (DSet (bracket M 6 xc (yc / 2)) : ℝ) ≥ H - 1 := by
    rw [hHdef]; unfold Lambda; push_cast
    have h1 := min_le_right (DSet (bracket M 6 xc yc) : ℝ)
      (min (1 + (DSet (bracket M 6 xc (yc/2)) : ℝ)) (2 + (DSet (bracket M 6 xc (yc/4)) : ℝ)))
    have h2 := min_le_left (1 + (DSet (bracket M 6 xc (yc/2)) : ℝ))
      (2 + (DSet (bracket M 6 xc (yc/4)) : ℝ))
    have h3 := le_trans h1 h2
    push_cast at h3 ⊢
    linarith
  have hH2 : (DSet (bracket M 6 xc (yc / 4)) : ℝ) ≥ H - 2 := by
    rw [hHdef]; unfold Lambda; push_cast
    have h1 := min_le_right (DSet (bracket M 6 xc yc) : ℝ)
      (min (1 + (DSet (bracket M 6 xc (yc/2)) : ℝ)) (2 + (DSet (bracket M 6 xc (yc/4)) : ℝ)))
    have h2 := min_le_right (1 + (DSet (bracket M 6 xc (yc/2)) : ℝ))
      (2 + (DSet (bracket M 6 xc (yc/4)) : ℝ))
    have h3 := le_trans h1 h2
    push_cast at h3 ⊢
    linarith
  -- Apply Corollary 4.9.
  have hcor := Proof.Induction.cor_4_9_iterated_partition_seed ρ hρ2 β hβdef M 2 kt
      (by rw [hktdef]; omega) 6 (by norm_num) xc yc hxc0 hxck hyc0 hyc1 hseed6 hrung6 H hH0 hH1 hH2
  -- Parameter-match the cor 4.9 bracket to bracket M p'j xj x0.
  have hcnt : ⌊Real.rpow 2 ((kt:ℕ):ℝ) * β.rpow ((2:ℕ):ℝ) * ((6:ℕ):ℝ)⌋₊ = p'j := by
    rw [hp'jdef]; congr 1
    rw [show (((10000 - j : ℕ)):ℝ) - 3 = ((kt:ℕ):ℝ) by rw [hktR]; rw [Nat.cast_sub (by omega : j ≤ 10000)]; push_cast; ring]
    rw [show (β.rpow ((2:ℕ):ℝ)) = β^2 by rw [p414_rpf, Real.rpow_natCast]]
    push_cast; ring
  have hrow : Real.rpow 2 ((kt:ℕ):ℝ) * xc = xj := by
    rw [hxjdef, hxcdef]; simp only [p414_rp2]
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), hktR]; ring_nf
  have hcol : yc.rpow (ρ.rpow ((2:ℕ):ℝ)) = x0 := by
    rw [hx0def, hycdef, hρdef]
    have hsq2 : Real.rpow (Real.sqrt (10000 + 10)) ((2:ℕ):ℝ) = (10000:ℝ) + 10 := by
      rw [show Real.rpow (Real.sqrt (10000+10)) ((2:ℕ):ℝ)
            = (Real.sqrt (10000+10)) ^ ((2:ℕ):ℝ) from rfl, Real.rpow_natCast]
      exact Real.sq_sqrt (by norm_num)
    rw [hsq2]; simp only [p414_rp2]
    rw [show Real.rpow ((2:ℝ)^(-1:ℝ)) ((10000:ℝ)+10) = ((2:ℝ)^(-1:ℝ))^((10000:ℝ)+10) from rfl,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    ring_nf
  rw [hcnt, hrow, hcol] at hcor
  -- hcor : ↑(DSet (bracket M p'j xj x0)) ≥ ↑kt + H
  -- Lemma 4.10: H = Λ_M(6, xc, yc) ≥ 3 + Λ_M(1, x0, 2^{-3/8}).
  have hx0cast : Real.rpow 2 (-((10000:ℕ):ℝ) - 10) = x0 := by
    rw [hx0def]; norm_num
  have h410 := Proof.Induction.lemma_4_10_seed_collapse M 10 (by norm_num) 10000 (by norm_num)
    (by
      rw [hx0cast]; exact hside)
  -- h410 : Λ M 6 (2^{3-10000-10}) (2^{-1}) ≥ 3 + Λ M 1 (2^{-10000-10}) (2^{-3/8})
  rw [show Real.rpow 2 ((3:ℝ) - ((10000:ℕ):ℝ) - 10) = xc by rw [hxcdef]; norm_num,
      show Real.rpow 2 (-1) = yc from hycdef.symm, hx0cast] at h410
  have h410R : H ≥ 3 + (Lambda M 1 x0 (Real.rpow 2 (-3 / 8)) : ℝ) := by
    rw [hHdef]; exact_mod_cast h410
  -- Final: kt + H ≥ kt + 3 + Λ = (10000-j) + Λ.
  have hktk : ((kt:ℕ):ℝ) + 3 = ((10000 - j : ℕ):ℝ) := by
    rw [hktR, Nat.cast_sub (by omega : j ≤ 10000)]; push_cast; ring
  have hfinal : (((10000 - j : ℕ):ℝ) + (Lambda M 1 x0 (Real.rpow 2 (-3 / 8)) : ℝ))
      ≤ (DSet (bracket M p'j xj x0) : ℝ) := by
    have hkk : ((kt:ℕ):ℝ) + H ≤ (DSet (bracket M p'j xj x0) : ℝ) := hcor
    linarith [hkk, h410R, hktk]
  have hcast : (((10000 - j) + Lambda M 1 x0 (Real.rpow 2 (-3 / 8)) : ℕ) : ℝ)
      ≤ (DSet (bracket M p'j xj x0) : ℝ) := by push_cast; linarith [hfinal]
  exact_mod_cast hcast

/-- Proposition 4.14 (φ-growth step). For `k = 10000`, `a = 10`, `η_j = 2^{-3/8-j}` (`j∈{0,1,2}`),
any `i ≥ 1`, if `D([φ_i]_{1, 2^{-k-a}, 2^{-3}}) ≥ 1`, then for each `j ∈ {0,1,2}`,
`D([φ_{i+1}]_{1, 2^{-k-a}, η_j}) ≥ k − j + Λ_{φ_i}(1, 2^{-k-a}, η_0)`; consequently
`Λ_{φ_{i+1}}(1, 2^{-k-a}, η_0) ≥ k + Λ_{φ_i}(1, 2^{-k-a}, η_0)`. -/
theorem proposition_4_14_phi_growth_step (i : ℕ) (hi : 1 ≤ i)
    (hside :
      DSet (bracket (phi Q i) 1 (Real.rpow 2 (-(10000 : ℝ) - 10)) (Real.rpow 2 (-3))) ≥ 1) :
    (∀ j : ℕ, j < 3 →
        let η : ℕ → ℝ := fun j => Real.rpow 2 (-3 / 8 - (j : ℝ))
        DSet (bracket (phi Q (i + 1)) 1 (Real.rpow 2 (-(10000 : ℝ) - 10)) (η j)) ≥
          10000 - j +
            Lambda (phi Q i) 1 (Real.rpow 2 (-(10000 : ℝ) - 10)) (Real.rpow 2 (-3 / 8))) ∧
      Lambda (phi Q (i + 1)) 1 (Real.rpow 2 (-(10000 : ℝ) - 10)) (Real.rpow 2 (-3 / 8)) ≥
        10000 + Lambda (phi Q i) 1 (Real.rpow 2 (-(10000 : ℝ) - 10)) (Real.rpow 2 (-3 / 8)) := by
  set x0 : ℝ := Real.rpow 2 (-(10000 : ℝ) - 10) with hx0def
  set L : ℕ := Lambda (phi Q i) 1 x0 (Real.rpow 2 (-3 / 8)) with hLdef
  -- Column density identities: 2^{-3/8}/2^j = 2^{-3/8-j}.
  have hcoldiv : ∀ j : ℕ, Real.rpow 2 (-3 / 8) / 2 ^ j = Real.rpow 2 (-3 / 8 - (j : ℝ)) := by
    intro j
    simp only [p414_rp2]
    rw [show (2:ℝ)^j = (2:ℝ)^((j:ℕ):ℝ) by rw [Real.rpow_natCast]]
    rw [show (-3 / 8 - (j:ℝ)) = (-3 / 8) - ((j:ℕ):ℝ) by push_cast; ring]
    rw [← Real.rpow_sub (by norm_num : (0:ℝ) < 2)]
  -- Part 1: per-j bound.
  have hpart1 : ∀ j : ℕ, j < 3 →
      DSet (bracket (phi Q (i + 1)) 1 x0 (Real.rpow 2 (-3 / 8 - (j : ℝ)))) ≥ (10000 - j) + L := by
    intro j hj
    rw [hLdef]
    have := p414_per_j i hi (by rw [hx0def] at hside; exact hside) j hj
    rw [← hx0def] at this
    exact this
  refine ⟨?_, ?_⟩
  · -- The ∀-statement with the `let η`.
    intro j hj η
    show DSet (bracket (phi Q (i + 1)) 1 (Real.rpow 2 (-(10000 : ℝ) - 10)) (η j)) ≥
      10000 - j + Lambda (phi Q i) 1 (Real.rpow 2 (-(10000 : ℝ) - 10)) (Real.rpow 2 (-3 / 8))
    rw [← hx0def, ← hLdef]
    have hηj : η j = Real.rpow 2 (-3 / 8 - (j : ℝ)) := rfl
    rw [hηj]
    exact hpart1 j hj
  · -- Part 2: min over j.
    show Lambda (phi Q (i + 1)) 1 x0 (Real.rpow 2 (-3 / 8)) ≥ 10000 + L
    unfold Lambda
    -- three rungs at densities 2^{-3/8}, 2^{-3/8}/2, 2^{-3/8}/4.
    rw [show Real.rpow 2 (-3 / 8) / 2 = Real.rpow 2 (-3 / 8 - ((1:ℕ):ℝ)) by
          simp only [p414_rp2]
          rw [show (-3 / 8 - ((1:ℕ):ℝ)) = (-3 / 8) - 1 by push_cast; ring,
              Real.rpow_sub (by norm_num : (0:ℝ) < 2), Real.rpow_one],
        show Real.rpow 2 (-3 / 8) / 4 = Real.rpow 2 (-3 / 8 - ((2:ℕ):ℝ)) by
          simp only [p414_rp2]
          rw [show (-3 / 8 - ((2:ℕ):ℝ)) = (-3 / 8) - 2 by push_cast; ring,
              Real.rpow_sub (by norm_num : (0:ℝ) < 2),
              show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
          norm_num]
    have h0 := hpart1 0 (by norm_num)
    have h1 := hpart1 1 (by norm_num)
    have h2 := hpart1 2 (by norm_num)
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, sub_zero] at h0 h1 h2 ⊢
    -- h0 : D(...η_0) ≥ 10000 + L; h1 : D(...η_1) ≥ 9999 + L; h2 : D(...η_2) ≥ 9998 + L
    -- Goal: min(D_0, min(1+D_1, 2+D_2)) ≥ 10000 + L
    refine le_min ?_ (le_min ?_ ?_)
    · exact h0
    · omega
    · omega

/-- Lemma 4.18 (Weak side condition propagates). For `k = 10000`, `a = 10`, any `i ≥ 1`: if
`D([φ_i]_{1, 2^{-k-a}, 2^{-3}}) ≥ 1` then `D([φ_{i+1}]_{1, 2^{-k-a}, 2^{-3}}) ≥ 1`. -/
theorem lemma_4_18_weak_side_condition_propagates (i : ℕ) (hi : 1 ≤ i)
    (hside :
      DSet (bracket (phi Q i) 1 (Real.rpow 2 (-(10000 : ℝ) - 10)) (Real.rpow 2 (-3))) ≥ 1) :
    DSet (bracket (phi Q (i + 1)) 1 (Real.rpow 2 (-(10000 : ℝ) - 10)) (Real.rpow 2 (-3))) ≥ 1 := by
  -- Notation: xrow = 2^{-k-a} (row parameter), ycol = 2^{-3} (column parameter).
  set xrow : ℝ := Real.rpow 2 (-(10000 : ℝ) - 10) with hxrow
  set ycol : ℝ := Real.rpow 2 (-3 : ℝ) with hycol
  -- Balancing parameters: α = 2^{a-3} = 2^7, xa = 2^{-a} = 2^{-10}, and α·xa = 2^{-3} = ycol.
  set α : ℝ := Real.rpow 2 (7 : ℝ) with hα
  set xa : ℝ := Real.rpow 2 (-10 : ℝ) with hxa
  -- Basic positivity / size facts about the rpow constants.
  have hxrow_pos : 0 < xrow := Real.rpow_pos_of_pos (by norm_num) _
  have hycol_pos : 0 < ycol := Real.rpow_pos_of_pos (by norm_num) _
  have hxa_pos : 0 < xa := Real.rpow_pos_of_pos (by norm_num) _
  have hα_pos : 0 < α := Real.rpow_pos_of_pos (by norm_num) _
  have h1lt2 : (1 : ℝ) < 2 := by norm_num
  -- α·xa = ycol = 2^{-3}.
  have hαxa : α * xa = ycol := by
    simp only [hα, hxa, hycol, ← Real.rpow_add (show (0:ℝ) < 2 by norm_num)]
    norm_num
  -- xrow ≤ 1, ycol ≤ 1, xa < 1, α > 1, etc.
  have hxrow_le1 : xrow ≤ 1 := by
    rw [hxrow, show (1 : ℝ) = Real.rpow 2 (0 : ℝ) by simp]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hycol_le1 : ycol ≤ 1 := by
    rw [hycol, show (1 : ℝ) = Real.rpow 2 (0 : ℝ) by simp]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hxa_le1 : xa ≤ 1 := by
    rw [hxa, show (1 : ℝ) = Real.rpow 2 (0 : ℝ) by simp]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hxa_lt1 : xa < 1 := by
    rw [hxa, show (1 : ℝ) = Real.rpow 2 (0 : ℝ) by simp]
    exact Real.rpow_lt_rpow_of_exponent_lt h1lt2 (by norm_num)
  have hα_gt1 : 1 < α := by
    rw [hα, show (1 : ℝ) = Real.rpow 2 (0 : ℝ) by simp]
    exact Real.rpow_lt_rpow_of_exponent_lt h1lt2 (by norm_num)
  -- xrow ≤ xa : 2^{-10010} ≤ 2^{-10}.
  have hxrow_le_xa : xrow ≤ xa := by
    rw [hxrow, hxa]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  -- Concrete values of the rpow constants.
  have hαval : α = 128 := by
    rw [hα, show Real.rpow 2 (7:ℝ) = (2:ℝ)^(7:ℝ) from rfl,
      show (7:ℝ) = ((7:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hxaval : xa = (1:ℝ)/1024 := by
    rw [hxa, show Real.rpow 2 (-10:ℝ) = (2:ℝ)^(-10:ℝ) from rfl,
      show (-10:ℝ) = -((10:ℕ):ℝ) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_natCast]; norm_num
  -- (Q : ℝ) = 255 * 2^9992, kept with 2^9992 opaque.
  have hQreal : (Q : ℝ) = 255 * (2:ℝ)^(9992:ℕ) := by
    show ((255 * 2 ^ (10000 - 8) : ℕ) : ℝ) = 255 * (2:ℝ)^(9992:ℕ)
    rw [show (10000 - 8 : ℕ) = 9992 from rfl]
    push_cast; ring
  -- 2^9992 ≥ 16384 (= 2^14), used to clear the 10010 lower bound.
  have hpow_big : (16384:ℝ) ≤ (2:ℝ)^(9992:ℕ) := by
    have : (2:ℝ)^(14:ℕ) ≤ (2:ℝ)^(9992:ℕ) :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)
    calc (16384:ℝ) = (2:ℝ)^(14:ℕ) := by norm_num
      _ ≤ (2:ℝ)^(9992:ℕ) := this
  have hpow_pos : (0:ℝ) < (2:ℝ)^(9992:ℕ) := by positivity
  -- The balancing partition size p*.
  set pstar : ℕ := ⌊(Q : ℝ) * (α - 1) * xa / (1 - xa)⌋₊ with hpstar
  -- The real value inside the floor equals 2^9992 * (32385/1023) ≥ 2^9992.
  have hbalexpr : (Q : ℝ) * (α - 1) * xa / (1 - xa) = (2:ℝ)^(9992:ℕ) * (32385/1023) := by
    rw [hQreal, hαval, hxaval]; ring
  have hbalge : (10010:ℝ) ≤ (Q : ℝ) * (α - 1) * xa / (1 - xa) := by
    rw [hbalexpr]
    have h1 : (1:ℝ) ≤ 32385/1023 := by norm_num
    have h2 : (10010:ℝ) ≤ (2:ℝ)^(9992:ℕ) := le_trans (by norm_num) hpow_big
    calc (10010:ℝ) ≤ (2:ℝ)^(9992:ℕ) := h2
      _ = (2:ℝ)^(9992:ℕ) * 1 := by ring
      _ ≤ (2:ℝ)^(9992:ℕ) * (32385/1023) := by
          apply mul_le_mul_of_nonneg_left h1 (le_of_lt hpow_pos)
  -- Lower bound p* ≥ 10010 (enough to force (k+a)/p* ≤ 3 and 1 ≤ p*).
  have hpstar_ge : pstar ≥ 10010 := by
    rw [hpstar]
    exact Nat.le_floor (by exact_mod_cast hbalge)
  have hpstar_ge1 : pstar ≥ 1 := le_trans (by norm_num) hpstar_ge
  -- (N4) ycol ≤ xrow^{1/p*}: equivalently (k+a)/p* ≤ 3.
  have hpstar_pos : (0:ℝ) < (pstar : ℝ) := by
    have : (1:ℝ) ≤ (pstar : ℝ) := by exact_mod_cast hpstar_ge1
    linarith
  have hpstar_ge_real : (10010:ℝ) ≤ (pstar : ℝ) := by exact_mod_cast hpstar_ge
  have hN4 : ycol ≤ Real.rpow xrow (((1:ℕ) : ℝ) / (pstar : ℝ)) := by
    -- xrow^{1/p*} = 2^{(-10010)/p*}
    have hrw : Real.rpow xrow (((1:ℕ) : ℝ) / (pstar : ℝ))
        = Real.rpow 2 ((-(10000:ℝ) - 10) * (((1:ℕ) : ℝ) / (pstar : ℝ))) := by
      rw [hxrow]
      exact (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (-(10000:ℝ) - 10)
        (((1:ℕ):ℝ)/(pstar:ℝ))).symm
    rw [hrw, hycol]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    -- need: -3 ≤ (-10010) * (1 / p*), i.e. 10010 / p* ≤ 3
    rw [Nat.cast_one, mul_one_div, le_div_iff₀ hpstar_pos]
    -- goal: -3 * p* ≤ -10010  ⟺  10010 ≤ 3 * p*  (true since p* ≥ 10010)
    nlinarith [hpstar_ge_real]
  -- xrow^{1/p*} ≤ 1.
  have hproj_le1 : Real.rpow xrow (((1:ℕ) : ℝ) / (pstar : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one (le_of_lt hxrow_pos) hxrow_le1
    positivity
  -- ===== The chain =====
  -- (2a) φ_{i+1} = (interlace (phi Q i) Q)ᵀ.
  rw [phi_succ]
  -- (2b) transpose_bracket: D([Mᵀ]_{1,xrow,ycol}) = D([M]_{1,ycol,xrow}).
  rw [← Proof.BracketLemmas.transpose_bracket (interlace (phi Q i) Q) ycol xrow]
  -- Goal: DSet (bracket (interlace (phi Q i) Q) 1 ycol xrow) ≥ 1.
  -- (2c) balancing: D([⟨M⟩^Q]_{1, α·xa, xrow}) ≥ D([M]_{p*, xa, xrow}).
  rw [← hαxa]
  have hbal :
      DSet (bracket (interlace (phi Q i) Q) 1 (α * xa) xrow) ≥
        DSet (bracket (phi Q i) pstar xa xrow) := by
    have := Proof.BracketLemmas.extended_balancing (phi Q i) Q α xa xrow
      hα_gt1 hxa_pos hxa_lt1 (hαxa ▸ hycol_pos) (hαxa ▸ hycol_le1)
      hxrow_pos hxrow_le1 ?_ ?_
    · exact this
    · -- m·xa ∈ ℕ : 2^a ∣ rows of φ_i.
      obtain ⟨hdvd, _⟩ := lemma_4_12_row_divisibility i hi
      have h10 : (2:ℕ)^10 ∣ (phi Q i).m := dvd_trans (pow_dvd_pow 2 (by norm_num)) hdvd
      obtain ⟨c, hc⟩ := h10
      refine ⟨c, ?_⟩
      rw [hxaval, hc]
      push_cast
      ring
    · -- ⌊Q·(α-1)·xa/(1-xa)⌋₊ ≥ 1
      rw [← hpstar]; exact hpstar_ge1
  -- (2d) projection: D([M]_{p*, xa, xrow}) ≥ D([M]_{1, xa, xrow^{1/p*}}).
  have hproj :
      DSet (bracket (phi Q i) pstar xa xrow) ≥
        DSet (bracket (phi Q i) 1 xa (Real.rpow xrow (((1:ℕ) : ℝ) / (pstar : ℝ)))) :=
    Proof.BracketLemmas.extended_maximum_projection (phi Q i) pstar 1 xa xrow
      (le_refl 1) hpstar_ge1 hxrow_pos
  -- (3) monotonicity: D([M]_{1, xa, xrow^{1/p*}}) ≥ D([M]_{1, xrow, ycol}) ≥ 1.
  have hmono :
      DSet (bracket (phi Q i) 1 xrow ycol) ≤
        DSet (bracket (phi Q i) 1 xa (Real.rpow xrow (((1:ℕ) : ℝ) / (pstar : ℝ)))) :=
    Proof.BracketLemmas.monotonicity (phi Q i) 1 1 xrow xa ycol
      (Real.rpow xrow (((1:ℕ) : ℝ) / (pstar : ℝ)))
      (le_refl 1) (le_refl 1) hxrow_pos hxrow_le_xa hxa_le1 hycol_pos hN4 hproj_le1
  -- Chain the inequalities.
  calc (1 : ℕ) ≤ DSet (bracket (phi Q i) 1 xrow ycol) := hside
    _ ≤ DSet (bracket (phi Q i) 1 xa (Real.rpow xrow (((1:ℕ) : ℝ) / (pstar : ℝ)))) := hmono
    _ ≤ DSet (bracket (phi Q i) pstar xa xrow) := hproj
    _ ≤ DSet (bracket (interlace (phi Q i) Q) 1 (α * xa) xrow) := hbal

/-- Reindex a protocol along maps on the input alphabets. -/
def reindexP {X Y X' Y' Z : Type*} (eX : X' → X) (eY : Y' → Y) :
    Protocol X Y Z → Protocol X' Y' Z
  | Protocol.leaf z => Protocol.leaf z
  | Protocol.aNode a l r =>
      Protocol.aNode (fun x => a (eX x)) (reindexP eX eY l) (reindexP eX eY r)
  | Protocol.bNode b l r =>
      Protocol.bNode (fun y => b (eY y)) (reindexP eX eY l) (reindexP eX eY r)

theorem cost_reindexP {X Y X' Y' Z : Type*} (eX : X' → X) (eY : Y' → Y)
    (P : Protocol X Y Z) : (reindexP eX eY P).cost = P.cost := by
  induction P with
  | leaf z => rfl
  | aNode a l r ihl ihr => simp only [reindexP, Protocol.cost, ihl, ihr]
  | bNode b l r ihl ihr => simp only [reindexP, Protocol.cost, ihl, ihr]

theorem eval_reindexP {X Y X' Y' Z : Type*} (eX : X' → X) (eY : Y' → Y)
    (P : Protocol X Y Z) (x : X') (y : Y') :
    (reindexP eX eY P).eval x y = P.eval (eX x) (eY y) := by
  induction P with
  | leaf z => rfl
  | aNode a l r ihl ihr => simp only [reindexP, Protocol.eval, ihl, ihr]
  | bNode b l r ihl ihr => simp only [reindexP, Protocol.eval, ihl, ihr]

theorem D_reindex {X Y X' Y' Z : Type*} [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (eX : X' ≃ X) (eY : Y' ≃ Y) (f : X → Y → Z) :
    D (fun x y => f (eX x) (eY y)) = D f := by
  unfold D AchievableCosts
  congr 1
  apply Set.eq_of_subset_of_subset
  · rintro c ⟨P, hcost, hcomp⟩
    refine ⟨reindexP eX.symm eY.symm P, ?_, ?_⟩
    · rw [cost_reindexP]; exact hcost
    · intro x y
      rw [eval_reindexP, hcomp]
      simp
  · rintro c ⟨P, hcost, hcomp⟩
    refine ⟨reindexP eX eY P, ?_, ?_⟩
    · rw [cost_reindexP]; exact hcost
    · intro x y
      rw [eval_reindexP]
      exact hcomp (eX x) (eY y)

theorem Dmat_extract_full (M : BoolMat) :
    Dmat (extract (interlace M 1) (Finset.range M.m) (Finset.range M.n)) = Dmat M := by
  set g : BoolMat := extract (interlace M 1) (Finset.range M.m) (Finset.range M.n) with hg
  have hgm : g.m = M.m := by simp [hg]
  have hgn : g.n = M.n := by simp [hg]
  let eX : Fin g.m ≃ Fin M.m := Fin.castOrderIso hgm |>.toEquiv
  let eY : Fin g.n ≃ Fin M.n := Fin.castOrderIso hgn |>.toEquiv
  have hentry : ∀ (i : Fin g.m) (j : Fin g.n), g.e i j = M.e (eX i) (eY j) := by
    intro i j
    have him : i.val < M.m := hgm ▸ i.isLt
    have hjn : j.val < M.n := hgn ▸ j.isLt
    have hr : ((Finset.range M.m).sort (· ≤ ·)).getD i 0 = i.val := by
      rw [Finset.sort_range, List.getD_eq_getElem _ _ (by simpa using him), List.getElem_range]
    have hc : ((Finset.range M.n).sort (· ≤ ·)).getD j 0 = j.val := by
      rw [Finset.sort_range, List.getD_eq_getElem _ _ (by simpa using hjn), List.getElem_range]
    show (extract (interlace M 1) (Finset.range M.m) (Finset.range M.n)).e i j = _
    simp only [extract]
    simp only [hr, hc, interlace, Nat.mul_one, Nat.pow_one]
    rw [dif_pos ⟨him, hjn⟩]
    congr 1 <;> · apply Fin.ext; simp [Nat.mod_eq_of_lt, Nat.div_eq_of_lt, him, hjn, eX, eY]
  unfold Dmat
  rw [show g.e = (fun i j => M.e (eX i) (eY j)) from funext fun i => funext fun j => hentry i j]
  exact D_reindex eX eY M.e

/-- Helper: the bracket `[M]_{1,1,1}` contains a matrix whose communication complexity equals
`Dmat M`, hence `DSet [M]_{1,1,1} ≤ Dmat M`.  (Paper: `[φ_i]_{1,1,1} = {φ_i}`.)
This is the "extraction with full row/column sets reproduces `M`" fact; isolated as a helper. -/
theorem DSet_bracket_one_one_one_le_Dmat (M : BoolMat) :
    DSet (bracket M 1 1 1) ≤ Dmat M := by
  set g : BoolMat := extract (interlace M 1) (Finset.range M.m) (Finset.range M.n) with hg
  have hmem : g ∈ bracket M 1 1 1 := by
    refine ⟨Finset.range M.m, Finset.range M.n, ?_, ?_, ?_, ?_, hg⟩
    · simp
    · intro γ hγ
      interval_cases γ
      simp only [Nat.mul_zero, Nat.zero_le, true_and]
      rw [Finset.filter_true_of_mem]
      · simp
      · intro i hi
        simpa using hi
    · simp
    · simp
  have heq : Dmat g = Dmat M := Dmat_extract_full M
  unfold DSet
  apply Nat.sInf_le
  exact ⟨g, hmem, heq⟩

/-- Corollary 4.20 (Bundled lower bound). For `k = 10000`, `a = 10`, any `i ≥ 1`:
`D([φ_i]_{1, 2^{-k-a}, 2^{-3}}) ≥ 1` and `Λ_{φ_i}(1, 2^{-k-a}, 2^{-3/8}) ≥ k·i`. -/
theorem corollary_4_20_bundled_lower_bound (i : ℕ) (hi : 1 ≤ i) :
    DSet (bracket (phi Q i) 1 (Real.rpow 2 (-(10000 : ℝ) - 10)) (Real.rpow 2 (-3))) ≥ 1 ∧
      Lambda (phi Q i) 1 (Real.rpow 2 (-(10000 : ℝ) - 10)) (Real.rpow 2 (-3 / 8)) ≥ 10000 * i := by
  induction i, hi using Nat.le_induction with
  | base =>
    refine ⟨Proof.PhiBase.phi_one_weak_side_condition, ?_⟩
    have h := Proof.PhiBase.phi_one_lambda
    simpa using h
  | succ i hi ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hprop := proposition_4_14_phi_growth_step i hi ih1
    refine ⟨lemma_4_18_weak_side_condition_propagates i hi ih1, ?_⟩
    -- Λ_{φ_{i+1}} ≥ 10000 + Λ_{φ_i} ≥ 10000 + 10000*i = 10000*(i+1)
    have hstep := hprop.2
    have : 10000 + 10000 * i ≤
        Lambda (phi Q (i + 1)) 1 (Real.rpow 2 (-(10000 : ℝ) - 10)) (Real.rpow 2 (-3 / 8)) := by
      calc 10000 + 10000 * i
          ≤ 10000 + Lambda (phi Q i) 1 (Real.rpow 2 (-(10000 : ℝ) - 10)) (Real.rpow 2 (-3 / 8)) := by
            exact Nat.add_le_add_left ih2 10000
        _ ≤ _ := hstep
    calc 10000 * (i + 1) = 10000 + 10000 * i := by ring
      _ ≤ _ := this

/-- Corollary 4.24 (Lower bound on `φ_i`). For `k = 10000`, `a = 10`, any `i ≥ 1`:
`D(φ_i) ≥ k·i`. -/
theorem corollary_4_24_lower_bound_phi (i : ℕ) (hi : 1 ≤ i) :
    Dmat (phi Q i) ≥ 10000 * i := by
  -- Λ_{φ_i}(1, 2^{-k-a}, 2^{-3/8}) ≥ 10000*i
  have hlam := (corollary_4_20_bundled_lower_bound i hi).2
  set x : ℝ := Real.rpow 2 (-(10000 : ℝ) - 10) with hxdef
  set y : ℝ := Real.rpow 2 (-3 / 8) with hydef
  have hx0 : 0 < x := by rw [hxdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hy0 : 0 < y := by rw [hydef]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hx1 : x ≤ 1 := by
    rw [hxdef]
    rw [show (1 : ℝ) = Real.rpow 2 0 by simp]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    norm_num
  have hy1 : y ≤ 1 := by
    rw [hydef]
    rw [show (1 : ℝ) = Real.rpow 2 0 by simp]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    norm_num
  -- Λ ≤ DSet (bracket M 1 x y)
  have hlam_le : Lambda (phi Q i) 1 x y ≤ DSet (bracket (phi Q i) 1 x y) :=
    min_le_left _ _
  -- monotonicity: DSet (bracket M 1 x y) ≤ DSet (bracket M 1 1 1)
  have hmono : DSet (bracket (phi Q i) 1 x y) ≤ DSet (bracket (phi Q i) 1 1 1) :=
    Proof.BracketLemmas.monotonicity (phi Q i) 1 1 x 1 y 1
      (le_refl 1) (le_refl 1) hx0 hx1 (le_refl 1) hy0 hy1 (le_refl 1)
  -- DSet (bracket M 1 1 1) ≤ Dmat M
  have hsing : DSet (bracket (phi Q i) 1 1 1) ≤ Dmat (phi Q i) :=
    DSet_bracket_one_one_one_le_Dmat (phi Q i)
  calc 10000 * i ≤ Lambda (phi Q i) 1 x y := hlam
    _ ≤ DSet (bracket (phi Q i) 1 x y) := hlam_le
    _ ≤ DSet (bracket (phi Q i) 1 1 1) := hmono
    _ ≤ Dmat (phi Q i) := hsing

end Proof.PhiInduction

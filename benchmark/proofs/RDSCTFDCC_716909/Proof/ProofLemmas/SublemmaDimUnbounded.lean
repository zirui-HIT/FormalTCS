import Mathlib
import Proof.Types.BoolMat
import Proof.Types.Interlace
import Proof.Types.AlternatingGame
import Proof.ProofLemmas.DimRecurrence
import Proof.ProofLemmas.SublemmaDimPositive

open Proof.Types.BoolMat Proof.Types.Interlace Proof.Types.AlternatingGame

set_option maxRecDepth 10000

namespace Proof.ProofLemmas

/-- The fixed parameter `Q := 255 · 2^(10000-8)`. -/
private abbrev Q : ℕ := 255 * 2 ^ (10000 - 8)

/-- **DimUnbounded** (proof of Thm 2.9). Let `Q := 255 · 2^(10000-8)`.

(a) Per-2-step doubling: for every `i`, twice the larger dimension of
`phi Q i` is bounded above by the larger dimension of `phi Q (i+2)`.

(b) Boundedness: any index `i` whose both dimensions of `phi Q i` are at most
`2^n` satisfies `i ≤ 2n+1` (so the set `S_n` is finite/bounded above). -/
theorem SublemmaDimUnbounded :
    (∀ i : ℕ,
        2 * max ((phi Q i).m) ((phi Q i).n)
          ≤ max ((phi Q (i + 2)).m) ((phi Q (i + 2)).n)) ∧
    (∀ n i : ℕ,
        (phi Q i).m ≤ 2 ^ n → (phi Q i).n ≤ 2 ^ n → i ≤ 2 * n + 1) := by
  -- Q facts (kept opaque).
  have hQ2 : 2 ≤ Q := by
    have h : 0 < 2 ^ (10000 - 8) := pow_pos (by norm_num) _
    calc (2 : ℕ) ≤ 255 * 1 := by norm_num
      _ ≤ 255 * 2 ^ (10000 - 8) := Nat.mul_le_mul_left 255 h
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ2
  have hQne : Q ≠ 0 := Nat.pos_iff_ne_zero.mp hQpos
  -- Positivity facts.
  obtain ⟨hpos, _⟩ := SublemmaDimPositive
  -- Part (a): the per-2-step doubling.
  have part_a : ∀ i : ℕ,
      2 * max ((phi Q i).m) ((phi Q i).n)
        ≤ max ((phi Q (i + 2)).m) ((phi Q (i + 2)).n) := by
    intro i
    -- Recurrence applied twice.
    obtain ⟨hm1, hn1⟩ := DimRecurrence i
    obtain ⟨hm2, hn2⟩ := DimRecurrence (i + 1)
    -- so (phi Q (i+2)).m = ((phi Q i).m * Q) ^ Q   [via hm2 with (i+1) then hn1]
    --    (phi Q (i+2)).n = ((phi Q i).n ^ Q) * Q   [via hn2 with (i+1) then hm1]
    set r := (phi Q i).m with hr
    set c := (phi Q i).n with hc
    have hr1 : 1 ≤ r := (hpos i).1
    have hc1 : 1 ≤ c := (hpos i).2
    -- rewrite the i+2 dims
    have hM : (phi Q (i + 2)).m = (r * Q) ^ Q := by
      have : (phi Q (i + 1 + 1)).m = ((phi Q (i + 1)).n) ^ Q := hm2
      rw [show i + 2 = i + 1 + 1 from rfl, this, hn1]
    have hN : (phi Q (i + 2)).n = (c ^ Q) * Q := by
      have : (phi Q (i + 1 + 1)).n = (phi Q (i + 1)).m * Q := hn2
      rw [show i + 2 = i + 1 + 1 from rfl, this, hm1]
    -- bound m at i+2 by 2r
    have hMge : 2 * r ≤ (phi Q (i + 2)).m := by
      rw [hM]
      calc 2 * r ≤ r * Q := by
            rw [Nat.mul_comm 2 r]
            exact Nat.mul_le_mul_left r hQ2
        _ ≤ (r * Q) ^ Q := Nat.le_self_pow hQne (r * Q)
    -- bound n at i+2 by 2c
    have hNge : 2 * c ≤ (phi Q (i + 2)).n := by
      rw [hN]
      calc 2 * c ≤ c * Q := by
            rw [Nat.mul_comm 2 c]
            exact Nat.mul_le_mul_left c hQ2
        _ ≤ (c ^ Q) * Q := by
            exact Nat.mul_le_mul_right Q (Nat.le_self_pow hQne c)
    -- combine
    rw [mul_max 2 r c]
    apply max_le_max hMge hNge
  refine ⟨part_a, ?_⟩
  -- Part (b).
  -- First establish 2^(i/2) ≤ max((phi Q i).m)((phi Q i).n) for all i by two-step induction.
  have hgrow : ∀ i : ℕ, 2 ^ (i / 2) ≤ max ((phi Q i).m) ((phi Q i).n) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      match i, ih with
      | 0, _ =>
          -- max(1,2)=2 ≥ 2^0=1
          simp only [Nat.zero_div, pow_zero]
          exact le_max_of_le_left (hpos 0).1
      | 1, _ =>
          -- 2^(1/2)=2^0=1 ≤ max(...)  since both ≥1
          have h1 : (1 : ℕ) / 2 = 0 := by norm_num
          rw [h1, pow_zero]
          exact le_max_of_le_left (hpos 1).1
      | (j + 2), ih =>
          have ihj : 2 ^ (j / 2) ≤ max ((phi Q j).m) ((phi Q j).n) :=
            ih j (by omega)
          have hdiv : (j + 2) / 2 = j / 2 + 1 := by omega
          rw [hdiv, pow_succ]
          calc 2 ^ (j / 2) * 2 = 2 * 2 ^ (j / 2) := by ring
            _ ≤ 2 * max ((phi Q j).m) ((phi Q j).n) :=
                Nat.mul_le_mul_left 2 ihj
            _ ≤ max ((phi Q (j + 2)).m) ((phi Q (j + 2)).n) := part_a j
  intro n i hm hn
  have hmax : max ((phi Q i).m) ((phi Q i).n) ≤ 2 ^ n := max_le hm hn
  have key : 2 ^ (i / 2) ≤ 2 ^ n := le_trans (hgrow i) hmax
  have hexp : i / 2 ≤ n := by
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp key
  omega

end Proof.ProofLemmas

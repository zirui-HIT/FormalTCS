import Mathlib
import Proof.Types.BoolMat
import Proof.Types.Interlace
import Proof.Types.AlternatingGame
import Proof.ProofLemmas.DimRecurrence

open Proof.Types.BoolMat Proof.Types.Interlace Proof.Types.AlternatingGame

set_option maxRecDepth 10000

namespace Proof.ProofLemmas

private abbrev Q : ℕ := 255 * 2 ^ (10000 - 8)

theorem SublemmaDimPositive :
    (∀ i : ℕ, 1 ≤ (phi Q i).m ∧ 1 ≤ (phi Q i).n) ∧
      (∀ i : ℕ, 2 ≤ (phi Q (i + 1)).n) := by
  have hQ2 : 2 ≤ Q := by
    have h : 0 < 2 ^ (10000 - 8) := pow_pos (by norm_num) _
    calc (2 : ℕ) ≤ 255 * 1 := by norm_num
      _ ≤ 255 * 2 ^ (10000 - 8) := Nat.mul_le_mul_left 255 h
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ2
  have hpos : ∀ i : ℕ, 1 ≤ (phi Q i).m ∧ 1 ≤ (phi Q i).n := by
    intro i
    induction i with
    | zero =>
        rw [phi_zero]
        exact ⟨le_refl 1, by norm_num⟩
    | succ k ih =>
        obtain ⟨hrec_m, hrec_n⟩ := DimRecurrence k
        constructor
        · rw [hrec_m]
          exact Nat.one_le_pow _ _ ih.2
        · rw [hrec_n]
          exact one_le_mul ih.1 hQpos
  refine ⟨hpos, ?_⟩
  intro i
  obtain ⟨_, hrec_n⟩ := DimRecurrence i
  rw [hrec_n]
  calc 2 = 1 * 2 := by norm_num
    _ ≤ (phi Q i).m * Q := Nat.mul_le_mul (hpos i).1 hQ2

end Proof.ProofLemmas

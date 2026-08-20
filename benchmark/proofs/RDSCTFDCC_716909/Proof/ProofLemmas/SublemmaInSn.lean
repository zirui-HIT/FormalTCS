import Mathlib
import Proof.Types.BoolMat
import Proof.Types.Interlace
import Proof.Types.AlternatingGame

open Proof.Types.BoolMat Proof.Types.Interlace Proof.Types.AlternatingGame

namespace Proof.ProofLemmas

private abbrev Q : ℕ := 255 * 2 ^ (10000 - 8)

theorem SublemmaInSn (i n : ℕ)
    (hm : Nat.clog 2 ((phi Q i).m) ≤ n)
    (hn : Nat.clog 2 ((phi Q i).n) ≤ n) :
    (phi Q i).m ≤ 2 ^ n ∧ (phi Q i).n ≤ 2 ^ n := by
  constructor
  · calc (phi Q i).m ≤ 2 ^ Nat.clog 2 ((phi Q i).m) :=
            Nat.le_pow_clog (by norm_num) _
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hm
  · calc (phi Q i).n ≤ 2 ^ Nat.clog 2 ((phi Q i).n) :=
            Nat.le_pow_clog (by norm_num) _
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

end Proof.ProofLemmas

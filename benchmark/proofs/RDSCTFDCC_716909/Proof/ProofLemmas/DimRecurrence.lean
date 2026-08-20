import Mathlib
import Proof.Types.BoolMat
import Proof.Types.Interlace
import Proof.Types.AlternatingGame

open Proof.Types.BoolMat Proof.Types.Interlace Proof.Types.AlternatingGame

namespace Proof.ProofLemmas

private abbrev Q : ℕ := 255 * 2 ^ (10000 - 8)

theorem DimRecurrence (i : ℕ) :
    (phi Q (i + 1)).m = ((phi Q i).n) ^ Q ∧ (phi Q (i + 1)).n = (phi Q i).m * Q := by
  constructor <;> rfl

end Proof.ProofLemmas

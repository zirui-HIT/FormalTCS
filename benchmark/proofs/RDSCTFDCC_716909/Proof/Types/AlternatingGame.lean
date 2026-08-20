import Mathlib
import Proof.Types.BoolMat
import Proof.Types.Interlace

namespace Proof.Types.AlternatingGame

open Proof.Types.BoolMat Proof.Types.Interlace

/-- **The Alternating Communicating Game family `φ`** (Definition 3.7),
parameterised by a positive integer `B`.

It is defined by structural recursion on the second (level) argument:

* `phi B 0` is the `1 × 2` matrix `[1 0]`: it has one row and two columns,
  with a `1` (`true`) in column `0` and a `0` (`false`) in column `1`.
* `phi B (i+1) = (interlace (phi B i) B).transpose`: each successive game is
  obtained by interlacing the previous one `B` times (the operation `⟨·⟩^B`)
  and then transposing. -/
def phi (B : ℕ) : ℕ → BoolMat
  | 0 =>
      { m := 1
        n := 2
        e := fun _ j => if (j : ℕ) = 0 then true else false }
  | (i + 1) => (interlace (phi B i) B).transpose

@[simp]
theorem phi_zero (B : ℕ) :
    phi B 0 =
      { m := 1
        n := 2
        e := fun _ j => if (j : ℕ) = 0 then true else false } := rfl

@[simp]
theorem phi_succ (B i : ℕ) :
    phi B (i + 1) = (interlace (phi B i) B).transpose := rfl

end Proof.Types.AlternatingGame

import Mathlib

namespace Proof.Types.DirectSum

/-- The `l`-fold direct sum (parallel power) of a Boolean function `f : X → Y → Bool`.

Given `l` instances, the inputs become `l`-tuples (`Fin l → X` for Alice,
`Fin l → Y` for Bob), and the output is the `l`-tuple of per-coordinate values
`fun i => f (xs i) (ys i)`. -/
def directSum {X Y : Type*} (f : X → Y → Bool) (l : ℕ) :
    (Fin l → X) → (Fin l → Y) → (Fin l → Bool) :=
  fun xs ys i => f (xs i) (ys i)

end Proof.Types.DirectSum

import Mathlib
import Proof.Types.BoolMat

namespace Proof.Types.Extract

open Proof.Types.BoolMat

/-- Row/column extraction `ε(A, R, C)` (Definition 3.12).

Given a Boolean matrix `A` and two finite sets of indices `R` and `C`, this
selects the rows whose indices lie in `R` and the columns whose indices lie in
`C`, both taken **in increasing order**, and reads off the resulting submatrix.

* The result has `R.card` rows and `C.card` columns.
* For `i : Fin R.card` and `j : Fin C.card`, the `(i, j)` entry is the original
  entry `A.e r c`, where `r` is the `i`-th smallest element of `R` and `c` is the
  `j`-th smallest element of `C` (both `0`-indexed).

To keep the function total even on out-of-range inputs, the entry falls back to
`false` whenever the selected row index is `≥ A.m` or the selected column index
is `≥ A.n`.  In the intended regime `R ⊆ {0, …, A.m-1}` and
`C ⊆ {0, …, A.n-1}`, so this fallback never fires. -/
def extract (A : BoolMat) (R C : Finset ℕ) : BoolMat where
  m := R.card
  n := C.card
  e := fun i j =>
    let r := (R.sort (· ≤ ·)).getD i 0
    let c := (C.sort (· ≤ ·)).getD j 0
    if h : r < A.m ∧ c < A.n then
      A.e ⟨r, h.1⟩ ⟨c, h.2⟩
    else
      false

@[simp]
theorem extract_m (A : BoolMat) (R C : Finset ℕ) : (extract A R C).m = R.card := rfl

@[simp]
theorem extract_n (A : BoolMat) (R C : Finset ℕ) : (extract A R C).n = C.card := rfl

end Proof.Types.Extract

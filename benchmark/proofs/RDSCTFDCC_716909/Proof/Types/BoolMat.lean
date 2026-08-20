import Mathlib

namespace Proof.Types.BoolMat

/-- A finite Boolean matrix, identified with a two-party communication game /
total Boolean function.  `m` rows and `n` columns, with entries `e i j`
indexed by `Fin m` and `Fin n` (indices start at `0`). -/
structure BoolMat where
  /-- Number of rows. -/
  m : ℕ
  /-- Number of columns. -/
  n : ℕ
  /-- The matrix entries: `e i j` is the entry in row `i`, column `j`. -/
  e : Fin m → Fin n → Bool

namespace BoolMat

/-- The transpose of a Boolean matrix: rows and columns are swapped, and the
entry at `(i, j)` of the transpose is the entry at `(j, i)` of the original. -/
def transpose (M : BoolMat) : BoolMat where
  m := M.n
  n := M.m
  e := fun i j => M.e j i

/-- Bridge presenting a `BoolMat` as a function `Fin m → Fin n → Bool`, so it
can be fed to a generic complexity measure taking a function `X → Y → Bool`. -/
def toFun (M : BoolMat) : Fin M.m → Fin M.n → Bool := M.e

@[simp]
theorem transpose_m (M : BoolMat) : (transpose M).m = M.n := rfl

@[simp]
theorem transpose_n (M : BoolMat) : (transpose M).n = M.m := rfl

@[simp]
theorem transpose_e (M : BoolMat) (i : Fin M.n) (j : Fin M.m) :
    (transpose M).e i j = M.e j i := rfl

@[simp]
theorem toFun_apply (M : BoolMat) (i : Fin M.m) (j : Fin M.n) :
    M.toFun i j = M.e i j := rfl

end BoolMat

end Proof.Types.BoolMat

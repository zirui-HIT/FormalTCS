import Mathlib
import Proof.Types.BoolMat

namespace Proof.Types.Interlace

open Proof.Types.BoolMat

/-- **Function form of the interlacing operation** (Definition 3.2).

Given a two-party function `f : X → Y → Bool` and a parameter `k`, the
interlaced function takes Alice's input to be a pair `(component, x)` with
`component : Fin k` and `x : X`, and Bob's input to be a `k`-tuple
`y : Fin k → Y`.  The value is `f` applied to `x` and to the entry of `y` at
the chosen component, i.e. `f x (y component)`. -/
def interlaceFun {X Y : Type*} (f : X → Y → Bool) (k : ℕ) :
    (Fin k × X) → (Fin k → Y) → Bool :=
  fun p y => f p.2 (y p.1)

/-- **Matrix form of the interlacing operation** `⟨A⟩^p` (Definition 3.4).

The result has `A.m * p` rows and `A.n ^ p` columns.  Writing a row index as
`i : Fin (A.m * p)` and a column index as `j : Fin (A.n ^ p)`, set
* `γ := i / A.m`  — the *component* (an element of `[p)`),
* `i' := i % A.m`  — the within-block row (an element of `[A.m)`),
* `j' := (j / A.n ^ γ) % A.n`  — the selected column digit (an element of `[A.n)`).

The entry of the interlaced matrix at `(i, j)` is `A.e i' j'`.  Positivity of
`A.m` and `A.n` (needed to build the `Fin` values) is derived from the row and
column indices being inhabited. -/
def interlace (A : BoolMat) (p : ℕ) : BoolMat where
  m := A.m * p
  n := A.n ^ p
  e := fun i j =>
    -- `A.m * p > i.val ≥ 0`, so `0 < A.m * p`, hence `0 < A.m` and `0 < p`.
    have hi : i.val < A.m * p := i.isLt
    have hmul : 0 < A.m * p := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
    have hm : 0 < A.m := by
      rcases Nat.eq_zero_or_pos A.m with h | h
      · simp [h] at hmul
      · exact h
    have hp : 0 < p := by
      rcases Nat.eq_zero_or_pos p with h | h
      · simp [h] at hmul
      · exact h
    -- `A.n ^ p > j.val ≥ 0`, so `0 < A.n ^ p`; with `0 < p`, get `0 < A.n`.
    have hj : j.val < A.n ^ p := j.isLt
    have hpow : 0 < A.n ^ p := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
    have hn : 0 < A.n := by
      by_contra h
      have hz : A.n = 0 := Nat.le_zero.mp (Nat.not_lt.mp h)
      rw [hz, Nat.zero_pow hp] at hpow
      exact absurd hpow (lt_irrefl 0)
    let γ : ℕ := i.val / A.m
    let i' : Fin A.m := ⟨i.val % A.m, Nat.mod_lt _ hm⟩
    let j' : Fin A.n := ⟨(j.val / A.n ^ γ) % A.n, Nat.mod_lt _ hn⟩
    A.e i' j'

end Proof.Types.Interlace

import Mathlib

namespace Proof.Types.Equipartition

/-- `IsEquipartitioned R m T p` (Definition 3.13): the finite set `R` of
natural-number indices is split evenly across the `p` consecutive blocks
`[m*γ, m*(γ+1))` for `γ = 0, …, p-1`, each block containing exactly `⌈T⌉₊`
elements of `R`.

`T` is a real-valued target and `⌈T⌉₊ = Nat.ceil T` is its natural-number
ceiling. The predicate constrains only `R`'s intersection with each of the
`p` blocks (`γ` ranging over `0, …, p-1`); it says nothing about elements of
`R` lying outside `[0, m*p)`. When `p = 0` the universally-quantified
condition is vacuously true. -/
def IsEquipartitioned (R : Finset ℕ) (m : ℕ) (T : ℝ) (p : ℕ) : Prop :=
  ∀ γ < p, (R.filter (fun i => m * γ ≤ i ∧ i < m * (γ + 1))).card = ⌈T⌉₊

end Proof.Types.Equipartition

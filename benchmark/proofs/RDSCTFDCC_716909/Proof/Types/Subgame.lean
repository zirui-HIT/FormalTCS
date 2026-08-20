import Mathlib
import Proof.Types.BoolMat

namespace Proof.Types.Subgame

open Proof.Types.BoolMat

/-- `IsSubgame A B` ("A is a subgame of B", Definition 3.9): a copy of the
game `A` appears inside `B` as a submatrix obtained by selecting rows and
columns of `B` and (possibly) rearranging them.  This is witnessed by
injective index maps `r : Fin A.m → Fin B.m` (row selection) and
`c : Fin A.n → Fin B.n` (column selection) such that every entry of `A`
matches the corresponding selected entry of `B`. -/
def IsSubgame (A B : BoolMat) : Prop :=
  ∃ (r : Fin A.m → Fin B.m) (c : Fin A.n → Fin B.n),
    Function.Injective r ∧ Function.Injective c ∧
      ∀ i j, A.e i j = B.e (r i) (c j)

/-- `IsSubgameSet Φ' Φ` ("Φ' is a subgame of Φ", Definition 3.10): every game
in the larger collection `Φ` has a subgame lying in the smaller collection
`Φ'`. -/
def IsSubgameSet (Φ' Φ : Set BoolMat) : Prop :=
  ∀ M ∈ Φ, ∃ M' ∈ Φ', IsSubgame M' M

end Proof.Types.Subgame

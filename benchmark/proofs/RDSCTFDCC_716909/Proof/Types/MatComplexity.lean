import Mathlib
import Proof.Types.BoolMat
import Proof.Types.CommComplexity

namespace Proof.Types.MatComplexity

open Proof.Types.BoolMat Proof.Types.CommComplexity

/-- The deterministic communication complexity of a Boolean matrix `M`,
viewed as a two-party total Boolean function (Definition 2.6): it is simply the
deterministic communication complexity `D` of the entry function
`M.e : Fin M.m → Fin M.n → Bool`. -/
noncomputable def Dmat (M : BoolMat) : ℕ := D M.e

/-- The deterministic communication complexity of a *set* of Boolean matrices
`Φ` (Definition 2.6 extended to sets): the minimum complexity `Dmat M` over all
matrices `M ∈ Φ`, i.e. `D(Φ) = min_{f ∈ Φ} D(f)`, expressed as the infimum over
the set of achievable values `{ c | ∃ M ∈ Φ, Dmat M = c }`. -/
noncomputable def DSet (Φ : Set BoolMat) : ℕ :=
  sInf { c : ℕ | ∃ M ∈ Φ, Dmat M = c }

end Proof.Types.MatComplexity

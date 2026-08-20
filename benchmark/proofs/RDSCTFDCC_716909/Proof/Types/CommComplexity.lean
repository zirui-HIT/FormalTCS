import Mathlib
import Proof.Types.Protocol

namespace Proof.Types.CommComplexity

open Proof.Types.Protocol

/-- The set of achievable communication costs for `f`: a natural number `c`
belongs to this set iff there exists a deterministic protocol `P` whose cost
(tree depth) is `c` and which computes `f`. -/
def AchievableCosts {X Y Z : Type*} (f : X → Y → Z) : Set ℕ :=
  { c : ℕ | ∃ P : Protocol X Y Z, P.cost = c ∧ Protocol.Computes P f }

/-- The deterministic communication complexity `D f` (Definition 2.6): the
minimum cost (depth) over all deterministic protocols computing `f`, taken via
`sInf` on the set of achievable costs. Here a protocol is a binary tree with
Alice/Bob nodes and its cost is its tree depth; `D f` is the least depth of any
protocol that computes `f` on every input.

`Z` is left arbitrary so this also covers tuple-valued direct-sum functions. -/
noncomputable def D {X Y Z : Type*} [Fintype X] [Fintype Y] (f : X → Y → Z) : ℕ :=
  sInf (AchievableCosts f)

end Proof.Types.CommComplexity

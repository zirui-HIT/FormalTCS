import GenLimit.Core.GenericGeneration
import Mathlib.Data.Set.Countable

/-!
# Covers of language classes

Neutral finite and increasing-cover interfaces shared by several paper
developments.
-/

namespace GenLimit.Generic

/-- An increasing sequence of subclasses whose union is `H`. -/
def IsNondecreasingCover
    (H : LanguageClass α) (classes : ℕ → LanguageClass α) : Prop :=
  Monotone classes ∧ H = ⋃ n, classes n

/-- A finite indexed collection of subclasses whose union is `H`. -/
def IsFiniteCover
    (H : LanguageClass α) {n : ℕ}
    (classes : Fin n → LanguageClass α) : Prop :=
  H = ⋃ i, classes i

end GenLimit.Generic

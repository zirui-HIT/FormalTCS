import Mathlib
import Proof.Types.Protocol
import Proof.Types.CommComplexity
import Proof.ProofLemmas.SublemmaPrecompNoIncrease
import Proof.ProofLemmas.SublemmaSurjRestrictGE

namespace Proof.ProofLemmas

open Proof.Types.CommComplexity

theorem SublemmaPrecompEq {A B A' B' Z : Type*} [Fintype A] [Fintype B]
    [Fintype A'] [Fintype B'] (g : A → B → Z) (α : A' → A) (β : B' → B)
    (hα : Function.Surjective α) (hβ : Function.Surjective β) :
    D (fun u v => g (α u) (β v)) = D g := by
  exact le_antisymm (Proof.ProofLemmas.SublemmaPrecompNoIncrease g α β)
    (Proof.ProofLemmas.SublemmaSurjRestrictGE g α β hα hβ)

end Proof.ProofLemmas

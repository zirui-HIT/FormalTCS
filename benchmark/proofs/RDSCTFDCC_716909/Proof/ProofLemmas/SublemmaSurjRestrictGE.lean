import Mathlib
import Proof.Types.Protocol
import Proof.Types.CommComplexity
import Proof.ProofLemmas.SublemmaPrecompNoIncrease

open Proof.Types.CommComplexity

namespace Proof.ProofLemmas

/-- Restricting the inputs of `g` along surjective maps `α : A' → A`, `β : B' → B`
to form `g' u v := g (α u) (β v)` cannot decrease the deterministic communication
complexity: `D g ≤ D g'`. -/
theorem SublemmaSurjRestrictGE {A B A' B' Z : Type*}
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (g : A → B → Z) (α : A' → A) (β : B' → B)
    (hα : Function.Surjective α) (hβ : Function.Surjective β) :
    D g ≤ D (fun u v => g (α u) (β v)) := by
  set g' : A' → B' → Z := fun u v => g (α u) (β v) with hg'
  -- right inverses of the surjections
  set α₀ : A → A' := Function.surjInv hα with hα₀
  set β₀ : B → B' := Function.surjInv hβ with hβ₀
  have hαr : ∀ x, α (α₀ x) = x := fun x => Function.surjInv_eq hα x
  have hβr : ∀ y, β (β₀ y) = y := fun y => Function.surjInv_eq hβ y
  -- precomposing g' by α₀, β₀ recovers g
  have hgeq : (fun x y => g' (α₀ x) (β₀ y)) = g := by
    funext x y
    simp only [hg', hαr, hβr]
  -- apply the already-proved lemma to g' with maps α₀, β₀
  have h := SublemmaPrecompNoIncrease g' α₀ β₀
  rw [hgeq] at h
  exact h

end Proof.ProofLemmas

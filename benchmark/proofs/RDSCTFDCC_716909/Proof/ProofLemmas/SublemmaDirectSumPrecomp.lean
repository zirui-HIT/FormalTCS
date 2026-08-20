import Mathlib
import Proof.Types.Protocol
import Proof.Types.CommComplexity
import Proof.Types.DirectSum
import Proof.ProofLemmas.SublemmaPrecompEq

open Proof.Types.CommComplexity
open Proof.Types.DirectSum

namespace Proof.ProofLemmas

theorem SublemmaDirectSumPrecomp {A B A' B' : Type*}
    [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (g : A → B → Bool) (α : A' → A) (β : B' → B)
    (hα : Function.Surjective α) (hβ : Function.Surjective β) (ℓ : ℕ) :
    D (directSum (fun u v => g (α u) (β v)) ℓ) = D (directSum g ℓ) := by
  -- coordinatewise lifts
  set αℓ : (Fin ℓ → A') → (Fin ℓ → A) := fun U j => α (U j) with hαℓdef
  set βℓ : (Fin ℓ → B') → (Fin ℓ → B) := fun V j => β (V j) with hβℓdef
  have hαℓ : Function.Surjective αℓ := by
    intro W
    refine ⟨fun j => Function.surjInv hα (W j), ?_⟩
    funext j
    simp [hαℓdef, Function.surjInv_eq hα]
  have hβℓ : Function.Surjective βℓ := by
    intro W
    refine ⟨fun j => Function.surjInv hβ (W j), ?_⟩
    funext j
    simp [hβℓdef, Function.surjInv_eq hβ]
  have hfun : directSum (fun u v => g (α u) (β v)) ℓ
      = fun (U : Fin ℓ → A') (V : Fin ℓ → B') => directSum g ℓ (αℓ U) (βℓ V) := by
    funext U V
    funext k
    simp [directSum, hαℓdef, hβℓdef]
  rw [hfun]
  exact SublemmaPrecompEq (directSum g ℓ) αℓ βℓ hαℓ hβℓ

end Proof.ProofLemmas

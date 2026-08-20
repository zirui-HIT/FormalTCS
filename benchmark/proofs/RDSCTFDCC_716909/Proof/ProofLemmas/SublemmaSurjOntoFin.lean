import Mathlib

namespace Proof.ProofLemmas

theorem SublemmaSurjOntoFin (r n : ℕ) (hr : 1 ≤ r) (hrn : r ≤ 2^n) :
    ∃ σ : (Fin n → Bool) → Fin r, Function.Surjective σ := by
  have hrpos : 0 < r := hr
  have : Nonempty (Fin r) := ⟨⟨0, hrpos⟩⟩
  rw [Function.exists_surjective_iff]
  refine ⟨⟨fun _ => ⟨0, hrpos⟩⟩, ?_⟩
  apply Function.Embedding.nonempty_of_card_le
  rw [Fintype.card_fin, Fintype.card_pi_const, Fintype.card_bool]
  exact hrn

end Proof.ProofLemmas

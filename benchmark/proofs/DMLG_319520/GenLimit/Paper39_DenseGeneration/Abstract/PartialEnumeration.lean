import GenLimit.Paper39_DenseGeneration.Abstract.PatientScope

/-!
# Counting certificate for partial enumeration

In Section 3.3 the adversary enumerates `enumerated ⊆ target`; consequently
the two ownership sets need cover only `enumerated`, not the whole target.
This certificate is the partial-enumeration analogue of
`PatientScopeCertificate` and retains the same Fact 3.12 and switch-budget
interfaces.
-/

namespace GenLimit
namespace PatientScope

structure PartialEnumerationCertificate where
  target : Language
  enumerated : Language
  enumerated_subset_target : enumerated ⊆ target
  attacker : Set ℕ
  defender : Set ℕ
  output : ℕ → ℕ
  output_range : Set.range output = defender
  output_injective : Function.Injective output
  validFrom : ℕ
  eventual_target : ∀ t, validFrom ≤ t → output t ∈ target
  enumerated_covered : enumerated ⊆ attacker ∪ defender
  attacker_subset_target : attacker ⊆ target
  ownership_disjoint : Disjoint attacker defender
  earlyAttacker : Finset ℕ
  switchLoss : Set ℕ
  switchLoss_subset : switchLoss ⊆ attacker ∩ target
  partner : ℕ → ℕ
  partner_mem : ∀ x,
    x ∈ ordinaryAttacker target attacker switchLoss earlyAttacker →
      partner x ∈ defender ∩ target
  partner_lt : ∀ x,
    x ∈ ordinaryAttacker target attacker switchLoss earlyAttacker →
      partner x < x
  partner_injective : Set.InjOn partner
    (ordinaryAttacker target attacker switchLoss earlyAttacker)
  switchBudget : ℕ → ℕ
  switch_prefix_le : ∀ n,
    prefixCount switchLoss n ≤ switchBudget n

namespace PartialEnumerationCertificate

variable (P : PartialEnumerationCertificate)

noncomputable def attackerCount (n : ℕ) : ℕ :=
  prefixCount (P.attacker ∩ P.target) n

noncomputable def defenderCount (n : ℕ) : ℕ :=
  prefixCount (P.defender ∩ P.target) n

noncomputable def enumeratedCount (n : ℕ) : ℕ :=
  prefixCount P.enumerated n

noncomputable def targetCount (n : ℕ) : ℕ :=
  prefixCount P.target n

/-- The ownership cover of the enumerated subset gives the first inequality
used in Theorem 3.17. -/
theorem enumeratedCount_le_ownership (n : ℕ) :
    P.enumeratedCount n ≤ P.attackerCount n + P.defenderCount n := by
  classical
  let E := prefixFinset P.enumerated n
  let A := prefixFinset (P.attacker ∩ P.target) n
  let D := prefixFinset (P.defender ∩ P.target) n
  have hsubset : E ⊆ A ∪ D := by
    intro x hx
    have hx' := mem_prefixFinset.mp hx
    rcases P.enumerated_covered hx'.2 with hxA | hxD
    · exact Finset.mem_union_left _ <| mem_prefixFinset.mpr
        ⟨hx'.1, hxA, P.enumerated_subset_target hx'.2⟩
    · exact Finset.mem_union_right _ <| mem_prefixFinset.mpr
        ⟨hx'.1, hxD, P.enumerated_subset_target hx'.2⟩
  calc
    P.enumeratedCount n = E.card := rfl
    _ ≤ (A ∪ D).card := Finset.card_le_card hsubset
    _ ≤ A.card + D.card := Finset.card_union_le _ _
    _ = P.attackerCount n + P.defenderCount n := rfl

private theorem attacker_prefix_subset (n : ℕ) :
    prefixFinset (P.attacker ∩ P.target) n ⊆
      (prefixFinset
          (ordinaryAttacker P.target P.attacker P.switchLoss P.earlyAttacker) n ∪
        P.earlyAttacker) ∪ prefixFinset P.switchLoss n := by
  classical
  intro x hx
  have hx' := mem_prefixFinset.mp hx
  by_cases hearly : x ∈ P.earlyAttacker
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hearly)
  · by_cases hswitch : x ∈ P.switchLoss
    · exact Finset.mem_union_right _
        (mem_prefixFinset.mpr ⟨hx'.1, hswitch⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact mem_prefixFinset.mpr
        ⟨hx'.1, hx'.2, by simpa using ⟨hearly, hswitch⟩⟩

theorem ordinary_prefix_le_defender (n : ℕ) :
    prefixCount
        (ordinaryAttacker P.target P.attacker P.switchLoss P.earlyAttacker) n
      ≤ P.defenderCount n := by
  classical
  unfold prefixCount defenderCount
  apply Finset.card_le_card_of_injOn P.partner
  · intro x hx
    have hx' := mem_prefixFinset.mp hx
    exact mem_prefixFinset.mpr
      ⟨lt_trans (P.partner_lt x hx'.2) hx'.1, P.partner_mem x hx'.2⟩
  · intro x hx y hy hxy
    exact P.partner_injective
      (mem_prefixFinset.mp hx).2 (mem_prefixFinset.mp hy).2 hxy

theorem attackerCount_le (n : ℕ) :
    P.attackerCount n ≤
      P.defenderCount n + P.earlyAttacker.card + P.switchBudget n := by
  classical
  let ordinary := prefixFinset
    (ordinaryAttacker P.target P.attacker P.switchLoss P.earlyAttacker) n
  let losses := prefixFinset P.switchLoss n
  have hcard : P.attackerCount n ≤
      (ordinary ∪ P.earlyAttacker ∪ losses).card :=
    Finset.card_le_card (P.attacker_prefix_subset n)
  have hunion : (ordinary ∪ P.earlyAttacker ∪ losses).card ≤
      ordinary.card + P.earlyAttacker.card + losses.card :=
    le_trans (Finset.card_union_le (ordinary ∪ P.earlyAttacker) losses)
      (Nat.add_le_add_right
        (Finset.card_union_le ordinary P.earlyAttacker) losses.card)
  exact le_trans hcard <| le_trans hunion <|
    Nat.add_le_add
      (Nat.add_le_add (P.ordinary_prefix_le_defender n) (Nat.le_refl _))
      (P.switch_prefix_le n)

/-- The finite-prefix inequality immediately before the liminf calculation
in Theorem 3.17. -/
theorem enumeratedCount_le_two_mul_defender
    (hlog : ∀ n, prefixCount P.switchLoss n ≤
      Nat.log2 (P.targetCount n)) (n : ℕ) :
    P.enumeratedCount n ≤
      2 * P.defenderCount n + P.earlyAttacker.card +
        Nat.log2 (P.targetCount n) := by
  have hA : P.attackerCount n ≤
      P.defenderCount n + P.earlyAttacker.card +
        Nat.log2 (P.targetCount n) := by
    let Q : PartialEnumerationCertificate :=
      { P with
        switchBudget := fun m => Nat.log2 (P.targetCount m)
        switch_prefix_le := hlog }
    simpa [Q, attackerCount, defenderCount] using Q.attackerCount_le n
  calc
    P.enumeratedCount n ≤ P.attackerCount n + P.defenderCount n :=
      P.enumeratedCount_le_ownership n
    _ ≤ (P.defenderCount n + P.earlyAttacker.card +
          Nat.log2 (P.targetCount n)) + P.defenderCount n :=
      Nat.add_le_add_right hA _
    _ = 2 * P.defenderCount n + P.earlyAttacker.card +
          Nat.log2 (P.targetCount n) := by omega

end PartialEnumerationCertificate
end PatientScope
end GenLimit

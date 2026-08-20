import GenLimit.Core.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Log

/-!
# An abstract certificate for the patient-scope density argument

This file isolates the finite counting argument used in Fact 3.12, Lemma 3.13,
and Theorem 3.14 of *Dense Language Generation Made Simple*.

It deliberately does **not** claim to implement the patient-scope state
machine.  A `PatientScopeCertificate` records the properties of a completed
trace that the machine proof must eventually supply:

* eventual validity and non-repetition of defender outputs;
* the ownership partition of the target;
* the injective, order-decreasing partner map from ordinary attacker wins to
  defender wins (Fact 3.12);
* a finite-prefix budget for switch losses (the conclusion supplied by the
  charging lemma).

The main theorem in this file derives the exact prefix-count inequality that
feeds the analytic lower-density calculation.  Keeping this layer separate
makes every assumption visible while the considerably longer machine and
charging invariants are formalized.
-/

namespace GenLimit
namespace PatientScope

/-- Elements of `S` in the strict natural-number prefix `{0, ..., n - 1}`. -/
noncomputable def prefixFinset (S : Set ℕ) (n : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range n).filter (fun x => x ∈ S)

@[simp] theorem mem_prefixFinset {S : Set ℕ} {n x : ℕ} :
    x ∈ prefixFinset S n ↔ x < n ∧ x ∈ S := by
  classical
  simp [prefixFinset]

/-- Cardinality of a set inside the strict prefix `{0, ..., n - 1}`. -/
noncomputable def prefixCount (S : Set ℕ) (n : ℕ) : ℕ :=
  (prefixFinset S n).card

/-- Attacker-owned target elements which are neither early exceptions nor
switch losses.  Fact 3.12 pairs precisely these elements with smaller
defender-owned target elements. -/
def ordinaryAttacker
    (target attacker switchLoss : Set ℕ) (earlyAttacker : Finset ℕ) : Set ℕ :=
  (attacker ∩ target) \ ((↑earlyAttacker : Set ℕ) ∪ switchLoss)

/--
An abstract trace certificate for the patient-scope algorithm.

`attacker` and `defender` are ownership sets: an element belongs to the party
that announced it first.  `output` enumerates the defender-owned elements.
The fields `output_injective` and `eventual_target` are the extensional content
of validity needed here.  The full machine bridge should additionally prove
that these sets are induced by the round-by-round game trace.
-/
structure PatientScopeCertificate where
  target : Language
  attacker : Set ℕ
  defender : Set ℕ
  output : ℕ → ℕ

  /-- Every defender-owned element is output, and every output is
  defender-owned. -/
  output_range : Set.range output = defender
  /-- The defender never repeats an output. -/
  output_injective : Function.Injective output
  /-- Lemma 3.11, stated at trace level. -/
  validFrom : ℕ
  eventual_target : ∀ t, validFrom ≤ t → output t ∈ target

  /-- Every target element is eventually owned by one of the two parties. -/
  target_covered : target ⊆ attacker ∪ defender
  /-- First ownership is unique. -/
  ownership_disjoint : Disjoint attacker defender

  /-- Attacker-owned target elements before the validity threshold. -/
  earlyAttacker : Finset ℕ
  /-- Attacker-owned target elements which falsify the preceding focus. -/
  switchLoss : Set ℕ
  switchLoss_subset : switchLoss ⊆ attacker ∩ target

  /-- The partner supplied by Fact 3.12. -/
  partner : ℕ → ℕ
  partner_mem : ∀ x,
    x ∈ ordinaryAttacker target attacker switchLoss earlyAttacker →
      partner x ∈ defender ∩ target
  partner_lt : ∀ x,
    x ∈ ordinaryAttacker target attacker switchLoss earlyAttacker →
      partner x < x
  partner_injective : Set.InjOn partner
    (ordinaryAttacker target attacker switchLoss earlyAttacker)

  /-- An explicit upper bound on switch losses in each prefix.  Lemma 3.13
  supplies `Nat.log2 (prefixCount target n)` here. -/
  switchBudget : ℕ → ℕ
  switch_prefix_le : ∀ n,
    prefixCount switchLoss n ≤ switchBudget n

namespace PatientScopeCertificate

variable (P : PatientScopeCertificate)

/-- Target elements first owned by the attacker. -/
noncomputable def attackerCount (n : ℕ) : ℕ :=
  prefixCount (P.attacker ∩ P.target) n

/-- Target elements first owned by the defender. -/
noncomputable def defenderCount (n : ℕ) : ℕ :=
  prefixCount (P.defender ∩ P.target) n

/-- Number of target elements in a universe prefix. -/
noncomputable def targetCount (n : ℕ) : ℕ :=
  prefixCount P.target n

/-- The certificate explicitly contains generation in the limit at the trace
level: outputs are eventually in the target and are never repeated. -/
theorem validity :
    ∃ T, (∀ t, T ≤ t → P.output t ∈ P.target) ∧
      Function.Injective P.output := by
  exact ⟨P.validFrom, P.eventual_target, P.output_injective⟩

/-- No output value is attacker-owned. -/
theorem output_not_attacker (t : ℕ) : P.output t ∉ P.attacker := by
  intro houtA
  have hout : P.output t ∈ P.defender := by
    rw [← P.output_range]
    exact ⟨t, rfl⟩
  exact Set.disjoint_left.1 P.ownership_disjoint
    houtA hout

/-- Fact 3.12 in the precise form used by counting: ordinary attacker wins
inject into strictly smaller defender-owned target elements. -/
theorem fact_3_12 :
    Set.InjOn P.partner
        (ordinaryAttacker P.target P.attacker P.switchLoss P.earlyAttacker) ∧
      ∀ x,
        x ∈ ordinaryAttacker
          P.target P.attacker P.switchLoss P.earlyAttacker →
        P.partner x ∈ P.defender ∩ P.target ∧ P.partner x < x := by
  refine ⟨P.partner_injective, ?_⟩
  intro x hx
  exact ⟨P.partner_mem x hx, P.partner_lt x hx⟩

/-- The order-decreasing partner map gives a finite-prefix injection. -/
theorem ordinary_prefix_le_defender (n : ℕ) :
    prefixCount
        (ordinaryAttacker P.target P.attacker P.switchLoss P.earlyAttacker) n
      ≤ P.defenderCount n := by
  classical
  unfold prefixCount defenderCount
  apply Finset.card_le_card_of_injOn P.partner
  · intro x hx
    have hxfin : x ∈ prefixFinset
        (ordinaryAttacker P.target P.attacker P.switchLoss P.earlyAttacker) n := hx
    have hx' : x < n ∧
        x ∈ ordinaryAttacker
          P.target P.attacker P.switchLoss P.earlyAttacker := by
      exact mem_prefixFinset.mp hxfin
    apply mem_prefixFinset.mpr
    exact ⟨lt_trans (P.partner_lt x hx'.2) hx'.1,
      P.partner_mem x hx'.2⟩
  · intro x hx y hy hxy
    have hx' : x ∈ ordinaryAttacker
        P.target P.attacker P.switchLoss P.earlyAttacker :=
      (mem_prefixFinset.mp (show x ∈ prefixFinset
        (ordinaryAttacker P.target P.attacker P.switchLoss P.earlyAttacker) n
        from hx)).2
    have hy' : y ∈ ordinaryAttacker
        P.target P.attacker P.switchLoss P.earlyAttacker :=
      (mem_prefixFinset.mp (show y ∈ prefixFinset
        (ordinaryAttacker P.target P.attacker P.switchLoss P.earlyAttacker) n
        from hy)).2
    exact P.partner_injective hx' hy' hxy

/-- The target ownership sets form a disjoint partition in every prefix. -/
theorem targetCount_eq (n : ℕ) :
    P.targetCount n = P.attackerCount n + P.defenderCount n := by
  classical
  let A := prefixFinset (P.attacker ∩ P.target) n
  let D := prefixFinset (P.defender ∩ P.target) n
  have hdis : Disjoint A D := by
    rw [Finset.disjoint_left]
    intro x hxA hxD
    have hxA' : x ∈ P.attacker := (mem_prefixFinset.mp hxA).2.1
    have hxD' : x ∈ P.defender := (mem_prefixFinset.mp hxD).2.1
    exact Set.disjoint_left.1 P.ownership_disjoint hxA' hxD'
  have hunion : prefixFinset P.target n = A ∪ D := by
    ext x
    simp only [mem_prefixFinset, Finset.mem_union, A, D]
    constructor
    · intro hx
      rcases P.target_covered hx.2 with hxA | hxD
      · exact Or.inl ⟨hx.1, hxA, hx.2⟩
      · exact Or.inr ⟨hx.1, hxD, hx.2⟩
    · rintro (⟨hxn, -, hxK⟩ | ⟨hxn, -, hxK⟩)
      · exact ⟨hxn, hxK⟩
      · exact ⟨hxn, hxK⟩
  unfold targetCount attackerCount defenderCount prefixCount
  rw [hunion, Finset.card_union_of_disjoint hdis]

/-- Every attacker-owned target element is ordinary, early, or a switch loss. -/
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
    · exact Finset.mem_union_right _ (mem_prefixFinset.mpr ⟨hx'.1, hswitch⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply mem_prefixFinset.mpr
      refine ⟨hx'.1, hx'.2, ?_⟩
      simpa using ⟨hearly, hswitch⟩

/-- The finite-prefix inequality at the end of the combinatorial part of the
proof of Theorem 3.14.

In paper notation this is
`mu_n(A) ≤ mu_n(D ∩ K) + r + switchBudget(n)`.
-/
theorem attackerCount_le (n : ℕ) :
    P.attackerCount n ≤
      P.defenderCount n + P.earlyAttacker.card + P.switchBudget n := by
  classical
  let O := prefixFinset
    (ordinaryAttacker P.target P.attacker P.switchLoss P.earlyAttacker) n
  let S := prefixFinset P.switchLoss n
  have hsubset := P.attacker_prefix_subset n
  have hcard : P.attackerCount n ≤ (O ∪ P.earlyAttacker ∪ S).card := by
    exact Finset.card_le_card hsubset
  have hunion : (O ∪ P.earlyAttacker ∪ S).card ≤
      O.card + P.earlyAttacker.card + S.card := by
    exact le_trans (Finset.card_union_le (O ∪ P.earlyAttacker) S)
      (Nat.add_le_add_right (Finset.card_union_le O P.earlyAttacker) S.card)
  have hord : O.card ≤ P.defenderCount n := by
    exact P.ordinary_prefix_le_defender n
  have hswitch : S.card ≤ P.switchBudget n := by
    exact P.switch_prefix_le n
  exact le_trans hcard <| le_trans hunion <|
    Nat.add_le_add (Nat.add_le_add hord (Nat.le_refl _)) hswitch

/-- Specialization when Lemma 3.13 supplies the logarithmic switch budget. -/
theorem attackerCount_le_log2
    (hlog : ∀ n,
      prefixCount P.switchLoss n ≤ Nat.log2 (P.targetCount n)) (n : ℕ) :
    P.attackerCount n ≤
      P.defenderCount n + P.earlyAttacker.card +
        Nat.log2 (P.targetCount n) := by
  -- Avoid imposing a relation between an arbitrary stored budget and the
  -- logarithmic one: reconstruct a certificate with the sharper budget.
  let Q : PatientScopeCertificate :=
    { P with
      switchBudget := fun m => Nat.log2 (P.targetCount m)
      switch_prefix_le := hlog }
  simpa [Q, attackerCount, defenderCount] using Q.attackerCount_le n

/-- In the normalized case `target = univ`, the ownership identity has the
form expected by the one-dimensional density endgame. -/
theorem normalized_counting
    (huniv : P.target = Set.univ) (n : ℕ) :
    P.attackerCount n + P.defenderCount n = n := by
  have h := P.targetCount_eq n
  calc
    P.attackerCount n + P.defenderCount n = P.targetCount n := h.symm
    _ = n := by
      simp [targetCount, prefixCount, prefixFinset, huniv]

/-- The ownership identity in the orientation used by the density theorem. -/
theorem normalized_partition
    (huniv : P.target = Set.univ) (n : ℕ) :
    P.defenderCount n + P.attackerCount n = n := by
  rw [Nat.add_comm]
  exact P.normalized_counting huniv n

/-- In the normalized target, the logarithmic charging lemma gives exactly
the counting inequality consumed by `lowerDensity_half_of_counting`. -/
theorem normalized_attackerCount_le_log2
    (huniv : P.target = Set.univ)
    (hlog : ∀ n,
      prefixCount P.switchLoss n ≤ Nat.log2 (P.targetCount n)) (n : ℕ) :
    P.attackerCount n ≤
      P.defenderCount n + P.earlyAttacker.card + Nat.log2 n := by
  have h := P.attackerCount_le_log2 hlog n
  have htarget : P.targetCount n = n := by
    simp [targetCount, prefixCount, prefixFinset, huniv]
  simpa [htarget] using h

end PatientScopeCertificate
end PatientScope
end GenLimit

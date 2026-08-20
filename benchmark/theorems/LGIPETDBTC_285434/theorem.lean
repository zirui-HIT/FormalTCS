import Mathlib.Algebra.Order.Archimedean.IndicatorCard
import Mathlib.Data.Real.CompleteField
import Mathlib.Topology.Order.LiminfLimsup

open Filter
open scoped Topology

namespace GenLimit
namespace PatientScope

abbrev Language := Set ℕ

noncomputable def prefixCount (K : Language) (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range n).filter fun x => x ∈ K).card

noncomputable def relativeLowerDensity (A K : Language) : ℝ :=
  liminf (fun n : ℕ => (prefixCount A n : ℝ) / (prefixCount K n : ℝ)) atTop

structure PartialEnumerationCertificate where
  target : Language
  enumerated : Language
  defender : Language
  switchLoss : Language
  earlyAttacker : Finset ℕ
  enumerated_subset_target : enumerated ⊆ target
  enumerated_count_le_two_mul_defender : ∀ n,
    prefixCount enumerated n ≤
      2 * prefixCount (defender ∩ target) n + earlyAttacker.card + prefixCount switchLoss n

noncomputable def PartialEnumerationCertificate.lowerDensity
    (P : PartialEnumerationCertificate) : ℝ :=
  relativeLowerDensity (P.defender ∩ P.target) P.target

namespace PartialEnumerationCertificate

theorem theorem_3_17
    (P : PartialEnumerationCertificate)
    (hInfinite : P.target.Infinite)
    (hlog : ∀ n, prefixCount P.switchLoss n ≤ Nat.log2 (prefixCount P.target n)) :
    (1 / 2 : ℝ) * relativeLowerDensity P.enumerated P.target ≤ P.lowerDensity := by sorry

end PartialEnumerationCertificate
end PatientScope
end GenLimit

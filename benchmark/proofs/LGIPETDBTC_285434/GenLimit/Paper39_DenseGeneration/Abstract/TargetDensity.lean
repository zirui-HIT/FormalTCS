import GenLimit.Paper39_DenseGeneration.Abstract.Density
import GenLimit.Paper39_DenseGeneration.Abstract.PatientScope
import Mathlib.Algebra.Order.Archimedean.IndicatorCard

/-!
# Lower density in an arbitrary infinite target

The normalized proof in `GenLimit.Paper39_DenseGeneration.Abstract.Density`
indexes prefixes by target rank.
Here we keep the original ambient prefixes.  For an infinite target `K`, its
prefix count tends to infinity; composing the normalized error estimate with
that count gives the same lower-density bound without an order-isomorphism
reduction.
-/

open Filter
open scoped Topology

namespace GenLimit
namespace PatientScope

/-- Lower density of one language relative to another, measured in ambient
natural-number prefixes. -/
noncomputable def relativeLowerDensity (A K : Language) : ℝ :=
  liminf
    (fun n : ℕ => (prefixCount A n : ℝ) / (prefixCount K n : ℝ))
    atTop

/-- Prefix cardinality is the sum of the target's natural-valued indicator. -/
theorem prefixCount_eq_sum_indicator (K : Set ℕ) (n : ℕ) :
    prefixCount K n =
      ∑ k ∈ Finset.range n, K.indicator (fun _ => (1 : ℕ)) k := by
  classical
  change ((Finset.range n).filter fun x => x ∈ K).card = _
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ K <;> simp [Set.indicator, hx]

/-- Prefix counts are monotone under set inclusion. -/
theorem prefixCount_mono {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    prefixCount A n ≤ prefixCount B n := by
  classical
  unfold prefixCount
  apply Finset.card_le_card
  intro x hx
  have hx' := mem_prefixFinset.mp hx
  exact mem_prefixFinset.mpr ⟨hx'.1, hAB hx'.2⟩

/-- The number of elements of an infinite target in ambient prefixes tends
to infinity. -/
theorem tendsto_prefixCount_atTop {K : Set ℕ} (hK : K.Infinite) :
    Tendsto (prefixCount K) atTop atTop := by
  have hsum :
      Tendsto
        (fun n : ℕ =>
          ∑ k ∈ Finset.range n, K.indicator (fun _ => (1 : ℕ)) k)
        atTop atTop :=
    (Set.infinite_iff_tendsto_sum_indicator_atTop
      (R := ℕ) (r := (1 : ℕ)) (by omega)).1 hK
  exact hsum.congr' <| Filter.Eventually.of_forall fun n =>
    (prefixCount_eq_sum_indicator K n).symm

/-- A counting theorem with an arbitrary denominator `N` which tends to
infinity.  This is the ambient-prefix analogue of
`lowerDensity_half_of_counting`. -/
theorem lowerDensity_half_of_counting_atTop
    (N D A : ℕ → ℕ) (r : ℕ)
    (hN : Tendsto N atTop atTop)
    (hpartition : ∀ n, D n + A n = N n)
    (hcharge : ∀ n, A n ≤ D n + r + Nat.log2 (N n)) :
    (1 / 2 : ℝ) ≤
      liminf (fun n : ℕ => (D n : ℝ) / (N n : ℝ)) atTop := by
  let g : ℕ → ℝ := fun n =>
    (1 / 2 : ℝ) -
      ((r + Nat.log2 (N n) : ℕ) : ℝ) / (2 * (N n : ℝ))
  have hg : Tendsto g atTop (𝓝 (1 / 2 : ℝ)) := by
    have hcomp := (tendsto_half_sub_countingError r).comp hN
    change Tendsto
      ((fun n : ℕ => (1 / 2 : ℝ) -
        ((r + Nat.log2 n : ℕ) : ℝ) / (2 * (n : ℝ))) ∘ N)
      atTop (𝓝 (1 / 2 : ℝ))
    exact hcomp
  have hNpos : ∀ᶠ n : ℕ in atTop, 0 < N n :=
    hN.eventually (eventually_gt_atTop 0)
  have hcompare : ∀ᶠ n : ℕ in atTop,
      g n ≤ (D n : ℝ) / (N n : ℝ) := by
    filter_upwards [hNpos] with n hn
    have hnR : (0 : ℝ) < N n := by exact_mod_cast hn
    have hcountNat :
        N n ≤ 2 * D n + r + Nat.log2 (N n) := by
      calc
        N n = D n + A n := (hpartition n).symm
        _ ≤ D n + (D n + r + Nat.log2 (N n)) :=
          Nat.add_le_add_left (hcharge n) _
        _ = 2 * D n + r + Nat.log2 (N n) := by omega
    have hcountR :
        (N n : ℝ) ≤
          2 * (D n : ℝ) + (r : ℝ) + (Nat.log2 (N n) : ℝ) := by
      exact_mod_cast hcountNat
    rw [show g n =
      (1 / 2 : ℝ) -
        ((r : ℝ) + (Nat.log2 (N n) : ℝ)) /
          (2 * (N n : ℝ)) by simp [g]]
    rw [le_div_iff₀ hnR]
    field_simp [hnR.ne']
    nlinarith
  have hD_le_N : ∀ n, D n ≤ N n := fun n => by
    calc
      D n ≤ D n + A n := Nat.le_add_right _ _
      _ = N n := hpartition n
  have hratio_le_one : ∀ n, (D n : ℝ) / (N n : ℝ) ≤ 1 := by
    intro n
    by_cases hn : N n = 0
    · simp [hn]
    · have hnR : (0 : ℝ) < N n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [div_le_one hnR]
      exact_mod_cast hD_le_N n
  calc
    (1 / 2 : ℝ) = liminf g atTop := hg.liminf_eq.symm
    _ ≤ liminf (fun n : ℕ => (D n : ℝ) / (N n : ℝ)) atTop :=
      liminf_le_liminf hcompare hg.isBoundedUnder_ge
        (isCoboundedUnder_ge_of_le atTop hratio_le_one)

/-- Exact arbitrary-target form of the lower-density calculation. -/
theorem lowerDensity_half_of_target_counting
    (K : Set ℕ) (hK : K.Infinite) (D A : ℕ → ℕ) (r : ℕ)
    (hpartition : ∀ n, D n + A n = prefixCount K n)
    (hcharge : ∀ n,
      A n ≤ D n + r + Nat.log2 (prefixCount K n)) :
    (1 / 2 : ℝ) ≤
      liminf
        (fun n : ℕ => (D n : ℝ) / (prefixCount K n : ℝ))
        atTop := by
  exact lowerDensity_half_of_counting_atTop
    (prefixCount K) D A r (tendsto_prefixCount_atTop hK)
    hpartition hcharge

end PatientScope
end GenLimit

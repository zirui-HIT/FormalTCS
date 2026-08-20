import Mathlib
import Proof.Types.BoolMat
import Proof.Types.Bracket
import Proof.Types.MatComplexity
import Proof.Types.Lambda
import Proof.BracketLemmas

namespace Proof.Appendix

open Proof.Types.BoolMat
open Proof.Types.Bracket
open Proof.Types.MatComplexity
open Proof.Types.Lambda
open Proof.BracketLemmas

set_option maxHeartbeats 1000000

/-- Density facts: for `y ∈ (0,1]` and `t ≥ 0`, `y^t ∈ (0,1]`. -/
private theorem rpow_mem_Ioc {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    0 < Real.rpow y t ∧ Real.rpow y t ≤ 1 := by
  refine ⟨Real.rpow_pos_of_pos hy0 t, ?_⟩
  calc Real.rpow y t ≤ Real.rpow y 0 :=
        Real.rpow_le_rpow_of_exponent_ge hy0 hy1 ht
    _ = 1 := Real.rpow_zero y

/-- Antitone in the exponent on `(0,1]`: `a ≤ b ⟹ y^b ≤ y^a`. -/
private theorem rpow_antitone {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) {a b : ℝ} (hab : a ≤ b) :
    Real.rpow y b ≤ Real.rpow y a :=
  Real.rpow_le_rpow_of_exponent_ge hy0 hy1 hab

/-- Fold a nested rpow into a single one (term form to avoid `^`-pattern issues). -/
private theorem rpow_fold (y : ℝ) (hy0 : 0 ≤ y) (a c : ℝ) :
    Real.rpow (Real.rpow y a) c = Real.rpow y (a * c) :=
  (Real.rpow_mul hy0 a c).symm

/-- Lemma A.1 (Partition recurrence).

For a matrix `M`, integer `p ≥ 1`, real `0 < τ ≤ 1`, `δ ∈ {0,1}`,
`0 < x ≤ 1/2`, `0 < y ≤ 1`, if `D([M]_{2p+δ, 2x, y}) ≥ 1`, then
```
D([M]_{2p+δ, 2x, y}) ≥ 1 + min(
    D([M]_{p+δ, x, y^{(p+δ)/(p(1+τ)+δ)}}),
    D([M]_{⌊p(1−τ)⌋+1, x, y^{τ/(1+τ)}}),
    D([M]_{2p+δ, 2x, y/2}) ).
``` -/
theorem lemma_A1_partition_recurrence
    (M : BoolMat) (p : ℕ) (hp : 1 ≤ p) (τ : ℝ) (hτ : 0 < τ ∧ τ ≤ 1)
    (δ : ℕ) (hδ : δ ≤ 1) (x y : ℝ)
    (hxy : 0 < x ∧ x ≤ 1 / 2 ∧ 0 < y ∧ y ≤ 1)
    (h1 : DSet (bracket M (2 * p + δ) (2 * x) y) ≥ 1) :
    DSet (bracket M (2 * p + δ) (2 * x) y) ≥
      1 + min
        (DSet (bracket M (p + δ) x
          (Real.rpow y (((p : ℝ) + δ) / ((p : ℝ) * (1 + τ) + δ)))))
        (min
          (DSet (bracket M (⌊(p : ℝ) * (1 - τ)⌋₊ + 1) x
            (Real.rpow y (τ / (1 + τ)))))
          (DSet (bracket M (2 * p + δ) (2 * x) (y / 2)))) := by
  obtain ⟨hτ0, hτ1⟩ := hτ
  obtain ⟨hx0, hx12, hy0, hy1⟩ := hxy
  -- abbreviations
  set B1 := DSet (bracket M (p + δ) x
      (Real.rpow y (((p : ℝ) + δ) / ((p : ℝ) * (1 + τ) + δ)))) with hB1def
  set B2 := DSet (bracket M (⌊(p : ℝ) * (1 - τ)⌋₊ + 1) x
      (Real.rpow y (τ / (1 + τ)))) with hB2def
  set B3 := DSet (bracket M (2 * p + δ) (2 * x) (y / 2)) with hB3def
  -- Step 0: old_partition
  have hOP := old_partition M p δ x y hx0 hx12 hy0 hy1 hδ h1
  -- E_mid set
  set S : Set ℕ := { v : ℕ | ∃ (ℓ : ℕ) (a : ℝ),
      ℓ < p ∧ 0 ≤ a ∧ a ≤ 1 ∧
      v = max (DSet (bracket M (p + δ + ℓ) x (Real.rpow y a)))
              (DSet (bracket M (p - ℓ) x (Real.rpow y (1 - a)))) } with hSdef
  -- positivity helpers on real denominators
  have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpR0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hδR0 : (0 : ℝ) ≤ (δ : ℝ) := by positivity
  have hden_pos : 0 < (p : ℝ) * (1 + τ) + δ := by nlinarith
  have hpδ_pos : 0 < (p : ℝ) + δ := by linarith
  -- B1 exponent is nonneg, ≤ 1
  have he1_nonneg : 0 ≤ ((p : ℝ) + δ) / ((p : ℝ) * (1 + τ) + δ) :=
    div_nonneg (by linarith) (le_of_lt hden_pos)
  have he2_nonneg : 0 ≤ τ / (1 + τ) := div_nonneg (le_of_lt hτ0) (by linarith)
  -- ===== Step 1: E_0 ≥ B1 =====
  have hStep1 : DSet (bracket M (2 * p + δ) x y) ≥ B1 := by
    -- 1a: lem:TupleCorollary with s = 2p+δ, q = p+δ
    have hℓ1 : 1 ≤ p + δ := by omega
    have hℓp : p + δ ≤ 2 * p + δ := by omega
    have h1a := extended_maximum_projection M (2 * p + δ) (p + δ) x y hℓ1 hℓp hy0
    -- exponent (p+δ)/(2p+δ)
    -- 1b: (p+δ)/(2p+δ) ≤ (p+δ)/(p(1+τ)+δ)
    have h2pδR0 : 0 < ((2 * p + δ : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((2 * p + δ : ℕ) : ℝ) := by
        have : 1 ≤ 2 * p + δ := by omega
        exact_mod_cast this
      linarith
    have hden_le : (p : ℝ) * (1 + τ) + δ ≤ ((2 * p + δ : ℕ) : ℝ) := by
      push_cast; nlinarith
    have h1b : ((p + δ : ℕ) : ℝ) / ((2 * p + δ : ℕ) : ℝ)
        ≤ ((p : ℝ) + δ) / ((p : ℝ) * (1 + τ) + δ) := by
      rw [show ((p + δ : ℕ) : ℝ) = (p : ℝ) + δ by push_cast; ring]
      apply div_le_div_of_nonneg_left (le_of_lt hpδ_pos) hden_pos hden_le
    -- 1c: monotone density
    have hbase_mem := rpow_mem_Ioc hy0 hy1 he1_nonneg
    have hmono := monotonicity M (p + δ) (p + δ) x x
      (Real.rpow y (((p : ℝ) + δ) / ((p : ℝ) * (1 + τ) + δ)))
      (Real.rpow y (((p + δ : ℕ) : ℝ) / ((2 * p + δ : ℕ) : ℝ)))
      (by omega : (1:ℕ) ≤ p + δ) (le_refl _) hx0 (le_refl x) (by linarith)
      (rpow_mem_Ioc hy0 hy1 he1_nonneg).1
      (rpow_antitone hy0 hy1 h1b)
      (rpow_mem_Ioc hy0 hy1
        (div_nonneg (by positivity) (by positivity))).2
    -- chain: E_0 ≥ D[p+δ,x,y^{(p+δ)/(2p+δ)}] ≥ B1
    calc DSet (bracket M (2 * p + δ) x y)
        ≥ DSet (bracket M (p + δ) x
            (Real.rpow y (((p + δ : ℕ) : ℝ) / ((2 * p + δ : ℕ) : ℝ)))) := h1a
      _ ≥ B1 := hmono
  -- ===== Step 2: E_mid ≥ min B1 B2 =====
  have hEmidNE : S.Nonempty := by
    refine ⟨_, 0, 0, hp, le_refl 0, by norm_num, rfl⟩
  have hStep2 : sInf S ≥ min B1 B2 := by
    apply le_csInf hEmidNE
    rintro v ⟨ℓ, a, hℓp, ha0, ha1, rfl⟩
    -- prove max(...) ≥ min B1 B2 for every (ℓ,a)
    have hℓR : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
    -- common: p+δ+ℓ ≥ 1, ≥ p+δ
    have hq1 : 1 ≤ p + δ := by omega
    have hqs : p + δ ≤ p + δ + ℓ := by omega
    by_cases hA : (p : ℝ) * τ ≤ (ℓ : ℝ)
    · -- Case A: first child ≥ B1
      have hfirst : DSet (bracket M (p + δ + ℓ) x (Real.rpow y a)) ≥ B1 := by
        have hcor := extended_maximum_projection M (p + δ + ℓ) (p + δ) x
          (Real.rpow y a) hq1 hqs (Real.rpow_pos_of_pos hy0 a)
        -- (y^a)^{(p+δ)/(p+δ+ℓ)} = y^{a*(p+δ)/(p+δ+ℓ)}
        have hpδℓR0 : 0 < ((p + δ + ℓ : ℕ) : ℝ) := by
          have : 1 ≤ p + δ + ℓ := by omega
          have : (1 : ℝ) ≤ ((p + δ + ℓ : ℕ) : ℝ) := by exact_mod_cast this
          linarith
        have hfold : Real.rpow (Real.rpow y a)
              (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ))
            = Real.rpow y (a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ))) :=
          rpow_fold y (le_of_lt hy0) a _
        rw [hfold] at hcor
        -- exponent bound: a*(p+δ)/(p+δ+ℓ) ≤ (p+δ)/(p(1+τ)+δ)
        have hexp_nonneg : 0 ≤ a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ)) :=
          mul_nonneg ha0 (div_nonneg (by positivity) (by positivity))
        have hexp_le : a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ))
            ≤ ((p : ℝ) + δ) / ((p : ℝ) * (1 + τ) + δ) := by
          have hfrac_le_one : ((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ) ≤ 1 := by
            rw [div_le_one hpδℓR0]; push_cast; linarith
          have h1 : a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ))
              ≤ (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ)) := by
            nlinarith [div_nonneg (show (0:ℝ) ≤ ((p+δ:ℕ):ℝ) by positivity)
              (le_of_lt hpδℓR0)]
          have hden_le2 : (p : ℝ) * (1 + τ) + δ ≤ ((p + δ + ℓ : ℕ) : ℝ) := by
            push_cast; nlinarith
          have h2 : (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ))
              ≤ ((p : ℝ) + δ) / ((p : ℝ) * (1 + τ) + δ) := by
            rw [show ((p + δ : ℕ) : ℝ) = (p : ℝ) + δ by push_cast; ring]
            exact div_le_div_of_nonneg_left (le_of_lt hpδ_pos) hden_pos hden_le2
          linarith
        -- monotone density
        have hmono := monotonicity M (p + δ) (p + δ) x x
          (Real.rpow y (((p : ℝ) + δ) / ((p : ℝ) * (1 + τ) + δ)))
          (Real.rpow y (a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ))))
          (by omega : (1:ℕ) ≤ p + δ) (le_refl _) hx0 (le_refl x) (by linarith)
          (rpow_mem_Ioc hy0 hy1 he1_nonneg).1
          (rpow_antitone hy0 hy1 hexp_le)
          (rpow_mem_Ioc hy0 hy1 hexp_nonneg).2
        calc DSet (bracket M (p + δ + ℓ) x (Real.rpow y a))
            ≥ DSet (bracket M (p + δ) x
                (Real.rpow y (a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ))))) := hcor
          _ ≥ B1 := hmono
      calc max (DSet (bracket M (p + δ + ℓ) x (Real.rpow y a)))
              (DSet (bracket M (p - ℓ) x (Real.rpow y (1 - a))))
          ≥ DSet (bracket M (p + δ + ℓ) x (Real.rpow y a)) := le_max_left _ _
        _ ≥ B1 := hfirst
        _ ≥ min B1 B2 := min_le_left _ _
    · -- ℓ < pτ
      push Not at hA  -- hA : (ℓ:ℝ) < p*τ
      by_cases hB : a ≤ 1 / (1 + τ)
      · -- Case B: first child ≥ B1
        have hfirst : DSet (bracket M (p + δ + ℓ) x (Real.rpow y a)) ≥ B1 := by
          have hcor := extended_maximum_projection M (p + δ + ℓ) (p + δ) x
            (Real.rpow y a) hq1 hqs (Real.rpow_pos_of_pos hy0 a)
          have hpδℓR0 : 0 < ((p + δ + ℓ : ℕ) : ℝ) := by
            have h0 : 1 ≤ p + δ + ℓ := by omega
            have : (1 : ℝ) ≤ ((p + δ + ℓ : ℕ) : ℝ) := by exact_mod_cast h0
            linarith
          have hfold : Real.rpow (Real.rpow y a)
                (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ))
              = Real.rpow y (a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ))) :=
            rpow_fold y (le_of_lt hy0) a _
          rw [hfold] at hcor
          have hexp_nonneg : 0 ≤ a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ)) :=
            mul_nonneg ha0 (div_nonneg (by positivity) (by positivity))
          -- bound: a*(p+δ)/(p+δ+ℓ) ≤ a ≤ 1/(1+τ) ≤ (p+δ)/(p(1+τ)+δ)
          have hfrac_le_one : ((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ) ≤ 1 := by
            rw [div_le_one hpδℓR0]; push_cast; linarith
          have step1 : a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ)) ≤ a := by
            nlinarith [div_nonneg (show (0:ℝ) ≤ ((p+δ:ℕ):ℝ) by positivity)
              (le_of_lt hpδℓR0)]
          have hτ1pos : 0 < 1 + τ := by linarith
          have hlast : 1 / (1 + τ) ≤ ((p : ℝ) + δ) / ((p : ℝ) * (1 + τ) + δ) := by
            rw [div_le_div_iff₀ hτ1pos hden_pos]
            -- p(1+τ)+δ ≤ (p+δ)(1+τ)
            nlinarith [mul_nonneg hδR0 (le_of_lt hτ0)]
          have hexp_le : a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ))
              ≤ ((p : ℝ) + δ) / ((p : ℝ) * (1 + τ) + δ) := by
            linarith
          have hmono := monotonicity M (p + δ) (p + δ) x x
            (Real.rpow y (((p : ℝ) + δ) / ((p : ℝ) * (1 + τ) + δ)))
            (Real.rpow y (a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ))))
            (by omega : (1:ℕ) ≤ p + δ) (le_refl _) hx0 (le_refl x) (by linarith)
            (rpow_mem_Ioc hy0 hy1 he1_nonneg).1
            (rpow_antitone hy0 hy1 hexp_le)
            (rpow_mem_Ioc hy0 hy1 hexp_nonneg).2
          calc DSet (bracket M (p + δ + ℓ) x (Real.rpow y a))
              ≥ DSet (bracket M (p + δ) x
                  (Real.rpow y (a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ))))) := hcor
            _ ≥ B1 := hmono
        calc max (DSet (bracket M (p + δ + ℓ) x (Real.rpow y a)))
                (DSet (bracket M (p - ℓ) x (Real.rpow y (1 - a))))
            ≥ DSet (bracket M (p + δ + ℓ) x (Real.rpow y a)) := le_max_left _ _
          _ ≥ B1 := hfirst
          _ ≥ min B1 B2 := min_le_left _ _
      · -- Case C: a ≥ 1/(1+τ), second child ≥ B2
        push Not at hB  -- hB : 1/(1+τ) < a
        have hτ1pos : 0 < 1 + τ := by linarith
        -- count: p - ℓ ≥ ⌊p(1-τ)⌋₊ + 1
        have hℓltp : ℓ < p := by
          have : (ℓ : ℝ) < (p : ℝ) := by
            calc (ℓ : ℝ) < (p : ℝ) * τ := hA
              _ ≤ (p : ℝ) * 1 := by nlinarith
              _ = (p : ℝ) := by ring
          exact_mod_cast this
        have hp1τ_nonneg : 0 ≤ (p : ℝ) * (1 - τ) := by nlinarith
        -- p - ℓ (as real) > p(1-τ)
        have hpℓ_real : ((p - ℓ : ℕ) : ℝ) = (p : ℝ) - (ℓ : ℝ) := by
          rw [Nat.cast_sub (le_of_lt hℓltp)]
        have hgt : (p : ℝ) * (1 - τ) < ((p - ℓ : ℕ) : ℝ) := by
          rw [hpℓ_real]
          have hexpand : (p : ℝ) * (1 - τ) = (p : ℝ) - (p : ℝ) * τ := by ring
          rw [hexpand]
          linarith only [hA]
        have hcount : ⌊(p : ℝ) * (1 - τ)⌋₊ + 1 ≤ p - ℓ := by
          have hfloor_lt : ⌊(p : ℝ) * (1 - τ)⌋₊ < p - ℓ := by
            have := Nat.floor_lt hp1τ_nonneg (n := p - ℓ)
            rw [this]; exact hgt
          omega
        have hcount1 : 1 ≤ ⌊(p : ℝ) * (1 - τ)⌋₊ + 1 := by omega
        -- density: 1 - a ≤ τ/(1+τ)
        have hdens : 1 - a ≤ τ / (1 + τ) := by
          have heq : τ / (1 + τ) = 1 - 1 / (1 + τ) := by
            field_simp; ring
          rw [heq]
          have hle : 1 / (1 + τ) ≤ a := le_of_lt hB
          linarith
        have h1a_nonneg : 0 ≤ 1 - a := by linarith
        have hsecond : DSet (bracket M (p - ℓ) x (Real.rpow y (1 - a))) ≥ B2 := by
          have hmono := monotonicity M (⌊(p : ℝ) * (1 - τ)⌋₊ + 1) (p - ℓ) x x
            (Real.rpow y (τ / (1 + τ))) (Real.rpow y (1 - a))
            hcount1 hcount hx0 (le_refl x) (by linarith)
            (rpow_mem_Ioc hy0 hy1 he2_nonneg).1
            (rpow_antitone hy0 hy1 hdens)
            (rpow_mem_Ioc hy0 hy1 h1a_nonneg).2
          exact hmono
        calc max (DSet (bracket M (p + δ + ℓ) x (Real.rpow y a)))
                (DSet (bracket M (p - ℓ) x (Real.rpow y (1 - a))))
            ≥ DSet (bracket M (p - ℓ) x (Real.rpow y (1 - a))) := le_max_right _ _
          _ ≥ B2 := hsecond
          _ ≥ min B1 B2 := min_le_right _ _
  -- ===== Step 4: assemble =====
  -- min A (min S C) ≥ min B1 (min B2 B3)
  have hfinal : min (DSet (bracket M (2 * p + δ) x y))
      (min (sInf S) B3) ≥ min B1 (min B2 B3) := by
    have hAB1 : DSet (bracket M (2 * p + δ) x y) ≥ B1 := hStep1
    have hC : B3 = B3 := rfl
    -- min A (min S C) ≥ min B1 (min (min B1 B2) B3) and simplify
    refine le_min ?_ (le_min ?_ ?_)
    · -- B1 ≤ A
      exact le_trans (min_le_left _ _) hAB1
    · -- B2 ≤ S
      exact le_trans (le_min (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))) hStep2
    · -- B3 ≤ C
      exact le_trans (min_le_right _ _) (min_le_right _ _)
  calc DSet (bracket M (2 * p + δ) (2 * x) y)
      ≥ 1 + min (DSet (bracket M (2 * p + δ) x y)) (min (sInf S) B3) := hOP
    _ ≥ 1 + min B1 (min B2 B3) := by
        exact Nat.add_le_add_left hfinal 1

/-- A single rung of the row partition lemma at an arbitrary density `d ∈ (0,1]`.
Both inner children (a) and (b) of `old_partition` are lower-bounded by
`S := D([M]_{p+δ, x, d})`, leaving only the deep child `D([M]_{2p+δ, 2x, d/2})`. -/
private theorem row_rung
    (M : BoolMat) (p : ℕ) (hp : 1 ≤ p) (δ : ℕ) (hδ : δ ≤ 1) (x : ℝ)
    (hx0 : 0 < x) (hx12 : x ≤ 1 / 2) (d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hpos : DSet (bracket M (2 * p + δ) (2 * x) d) ≥ 1) :
    DSet (bracket M (2 * p + δ) (2 * x) d) ≥
      1 + min (DSet (bracket M (p + δ) x d))
              (DSet (bracket M (2 * p + δ) (2 * x) (d / 2))) := by
  have hx1 : x ≤ 1 := by linarith
  -- old_partition at density d
  have hOP := old_partition M p δ x d hx0 hx12 hd0 hd1 hδ hpos
  set S : Set ℕ := { v : ℕ | ∃ (ℓ : ℕ) (a : ℝ),
      ℓ < p ∧ 0 ≤ a ∧ a ≤ 1 ∧
      v = max (DSet (bracket M (p + δ + ℓ) x (Real.rpow d a)))
              (DSet (bracket M (p - ℓ) x (Real.rpow d (1 - a)))) } with hSdef
  set Sd := DSet (bracket M (p + δ) x d) with hSddef
  -- term (a): D[2p+δ, x, d] ≥ Sd  (monotone in projection size)
  have hA : DSet (bracket M (2 * p + δ) x d) ≥ Sd := by
    have := monotonicity M (p + δ) (2 * p + δ) x x d d
      (by omega) (by omega) hx0 (le_refl x) hx1 hd0 (le_refl d) hd1
    exact this
  -- term (b): sInf S ≥ Sd
  have hSNE : S.Nonempty := ⟨_, 0, 0, hp, le_refl 0, by norm_num, rfl⟩
  have hB : sInf S ≥ Sd := by
    apply le_csInf hSNE
    rintro v ⟨ℓ, a, hℓp, ha0, ha1, rfl⟩
    have hq1 : 1 ≤ p + δ := by omega
    have hqs : p + δ ≤ p + δ + ℓ := by omega
    have hfirst : DSet (bracket M (p + δ + ℓ) x (Real.rpow d a)) ≥ Sd := by
      have hcor := extended_maximum_projection M (p + δ + ℓ) (p + δ) x
        (Real.rpow d a) hq1 hqs (Real.rpow_pos_of_pos hd0 a)
      have hpδℓR0 : 0 < ((p + δ + ℓ : ℕ) : ℝ) := by
        have h0 : 1 ≤ p + δ + ℓ := by omega
        have : (1 : ℝ) ≤ ((p + δ + ℓ : ℕ) : ℝ) := by exact_mod_cast h0
        linarith
      have hfold : Real.rpow (Real.rpow d a)
            (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ))
          = Real.rpow d (a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ))) :=
        rpow_fold d (le_of_lt hd0) a _
      rw [hfold] at hcor
      have hfrac_le_one : ((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one hpδℓR0]; push_cast; linarith
      have hexp_nonneg : 0 ≤ a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ)) :=
        mul_nonneg ha0 (div_nonneg (by positivity) (by positivity))
      have hexp_le1 : a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ)) ≤ 1 := by
        nlinarith [div_nonneg (show (0:ℝ) ≤ ((p+δ:ℕ):ℝ) by positivity)
          (le_of_lt hpδℓR0)]
      -- d^{exp} ≥ d^1 = d  since exp ≤ 1 and base ≤ 1
      have hdens : DSet (bracket M (p + δ) x
          (Real.rpow d (a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ))))) ≥ Sd := by
        have hge : Real.rpow d (a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ))) ≥ d := by
          calc Real.rpow d (a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ)))
              ≥ Real.rpow d 1 := rpow_antitone hd0 hd1 hexp_le1
            _ = d := Real.rpow_one d
        have := monotonicity M (p + δ) (p + δ) x x d
          (Real.rpow d (a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ))))
          (by omega) (le_refl _) hx0 (le_refl x) hx1 hd0 hge
          (rpow_mem_Ioc hd0 hd1 hexp_nonneg).2
        exact this
      calc DSet (bracket M (p + δ + ℓ) x (Real.rpow d a))
          ≥ DSet (bracket M (p + δ) x
              (Real.rpow d (a * (((p + δ : ℕ) : ℝ) / ((p + δ + ℓ : ℕ) : ℝ))))) := hcor
        _ ≥ Sd := hdens
    exact le_trans hfirst (le_max_left _ _)
  -- assemble: min(A, min(S, C)) ≥ min(Sd, C)
  have hfinal : min (DSet (bracket M (2 * p + δ) x d)) (min (sInf S)
      (DSet (bracket M (2 * p + δ) (2 * x) (d / 2))))
      ≥ min Sd (DSet (bracket M (2 * p + δ) (2 * x) (d / 2))) := by
    refine le_min ?_ (le_min ?_ ?_)
    · exact le_trans (min_le_left _ _) hA
    · exact le_trans (min_le_left _ _) hB
    · exact min_le_right _ _
  calc DSet (bracket M (2 * p + δ) (2 * x) d)
      ≥ 1 + min (DSet (bracket M (2 * p + δ) x d)) (min (sInf S)
          (DSet (bracket M (2 * p + δ) (2 * x) (d / 2)))) := hOP
    _ ≥ 1 + min Sd (DSet (bracket M (2 * p + δ) (2 * x) (d / 2))) :=
        Nat.add_le_add_left hfinal 1

/-- Lemma A.2 (Three-Rung Partition Lemma) — row inequality.

For a matrix `M`, `p ≥ 1`, `δ ∈ {0,1}`, `0 < x ≤ 1/2`, `0 < y ≤ 1`, assuming
`D([M]_{2p, 2x, y/4}) ≥ 1`:
`D([M]_{2p+δ, 2x, y}) ≥ 1 + min_{0≤j<3}( j + D([M]_{p+δ, x, y/2^j}) )`. -/
theorem lemma_A2_three_rung_row
    (M : BoolMat) (p : ℕ) (hp : 1 ≤ p) (δ : ℕ) (hδ : δ ≤ 1) (x y : ℝ)
    (hxy : 0 < x ∧ x ≤ 1 / 2 ∧ 0 < y ∧ y ≤ 1)
    (h1 : DSet (bracket M (2 * p) (2 * x) (y / 4)) ≥ 1) :
    DSet (bracket M (2 * p + δ) (2 * x) y) ≥
      1 + min
        (DSet (bracket M (p + δ) x y))
        (min
          (1 + DSet (bracket M (p + δ) x (y / 2)))
          (2 + DSet (bracket M (p + δ) x (y / 4)))) := by
  obtain ⟨hx0, hx12, hy0, hy1⟩ := hxy
  have hx1 : x ≤ 1 := by linarith
  -- positivity of the three densities
  have hd1pos : 0 < y / 2 := by positivity
  have hd2pos : 0 < y / 4 := by positivity
  have hd1le : y / 2 ≤ 1 := by linarith
  have hd2le : y / 4 ≤ 1 := by linarith
  -- Step R1: the three nonemptiness facts R0, R1, R2 ≥ 1, all from h1 via monotonicity.
  -- For each j, D[2p, 2x, y/4] ≤ D[2p+δ, 2x, y/2^j].
  have hmono_rung : ∀ d : ℝ, 0 < d → d ≤ 1 → y / 4 ≤ d →
      DSet (bracket M (2 * p + δ) (2 * x) d) ≥ 1 := by
    intro d hd0 hd1 hgd
    have hle := monotonicity M (2 * p) (2 * p + δ) (2 * x) (2 * x) (y / 4) d
      (by omega) (by omega) (by linarith) (le_refl _) (by linarith)
      hd2pos hgd hd1
    exact le_trans h1 hle
  have hR0pos : DSet (bracket M (2 * p + δ) (2 * x) y) ≥ 1 :=
    hmono_rung y hy0 hy1 (by linarith)
  have hR1pos : DSet (bracket M (2 * p + δ) (2 * x) (y / 2)) ≥ 1 :=
    hmono_rung (y / 2) hd1pos hd1le (by linarith)
  have hR2pos : DSet (bracket M (2 * p + δ) (2 * x) (y / 4)) ≥ 1 :=
    hmono_rung (y / 4) hd2pos hd2le (le_refl _)
  -- Abbreviations for S0, S1, S2
  set S0 := DSet (bracket M (p + δ) x y) with hS0def
  set S1 := DSet (bracket M (p + δ) x (y / 2)) with hS1def
  set S2 := DSet (bracket M (p + δ) x (y / 4)) with hS2def
  -- Per-rung bounds
  have hRung0 := row_rung M p hp δ hδ x hx0 hx12 y hy0 hy1 hR0pos
  have hRung1 := row_rung M p hp δ hδ x hx0 hx12 (y / 2) hd1pos hd1le hR1pos
  have hRung2 := row_rung M p hp δ hδ x hx0 hx12 (y / 4) hd2pos hd2le hR2pos
  -- rewrite the densities in the deep children: (y/2)/2 = y/4, (y)/2 = y/2
  have hdiv0 : y / 2 = y / 2 := rfl
  have he1 : (y / 2) / 2 = y / 4 := by ring
  have he2 : (y / 4) / 2 = y / 8 := by ring
  rw [he1] at hRung1
  rw [he2] at hRung2
  -- Step R6: deep child of j=2 (D[2p+δ, 2x, y/8]) ≥ S2.
  have hDeep2 : DSet (bracket M (2 * p + δ) (2 * x) (y / 8)) ≥ S2 := by
    -- extended_maximum_projection with total 2p+δ, target p+δ
    have hcor := extended_maximum_projection M (2 * p + δ) (p + δ) (2 * x)
      (y / 8) (by omega) (by omega) (by positivity)
    -- exponent e := (p+δ)/(2p+δ) ≤ 2/3
    set e : ℝ := ((p + δ : ℕ) : ℝ) / ((2 * p + δ : ℕ) : ℝ) with hedef
    have h2pδR0 : 0 < ((2 * p + δ : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((2 * p + δ : ℕ) : ℝ) := by
        have : 1 ≤ 2 * p + δ := by omega
        exact_mod_cast this
      linarith
    have he_nonneg : 0 ≤ e := by
      rw [hedef]; exact div_nonneg (by positivity) (le_of_lt h2pδR0)
    have he_le : e ≤ 2 / 3 := by
      rw [hedef, div_le_div_iff₀ h2pδR0 (by norm_num : (0:ℝ) < 3)]
      push_cast
      have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have hδR : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ
      nlinarith
    have hy8pos : 0 < y / 8 := by positivity
    have hy8le : y / 8 ≤ 1 := by linarith
    -- (y/8)^e ≥ (y/8)^{2/3} ≥ y/4
    have hstep1 : Real.rpow (y / 8) e ≥ Real.rpow (y / 8) (2 / 3) :=
      rpow_antitone hy8pos hy8le he_le
    -- (y/8)^{2/3} ≥ y/4
    have hstep2 : Real.rpow (y / 8) (2 / 3) ≥ y / 4 := by
      -- both sides positive; cube both sides: ((y/8)^{2/3})^3 = (y/8)^2 = y^2/64;
      -- (y/4)^3 = y^3/64; y^2 ≥ y^3 since y ≤ 1.
      have hlhs_pos : 0 < Real.rpow (y / 8) (2 / 3) := Real.rpow_pos_of_pos hy8pos _
      have hcube_lhs : (Real.rpow (y / 8) (2 / 3)) ^ (3 : ℕ) = (y / 8) ^ (2 : ℕ) := by
        have h1 : (Real.rpow (y / 8) (2 / 3)) ^ (3 : ℕ)
            = Real.rpow (y / 8) ((2 / 3) * (3 : ℕ)) := by
          rw [← Real.rpow_natCast (Real.rpow (y / 8) (2 / 3)) 3]
          exact rpow_fold (y / 8) (le_of_lt hy8pos) (2 / 3) ((3 : ℕ) : ℝ)
        rw [h1, show (2 / 3 : ℝ) * ((3 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by push_cast; ring]
        exact Real.rpow_natCast (y / 8) 2
      -- want y/4 ≤ (y/8)^{2/3}; suffices (y/4)^3 ≤ ((y/8)^{2/3})^3
      have hpow3 : (y / 4) ^ (3 : ℕ) ≤ (Real.rpow (y / 8) (2 / 3)) ^ (3 : ℕ) := by
        rw [hcube_lhs]
        have : (y / 4) ^ (3 : ℕ) = y ^ 3 / 64 := by ring
        rw [this, show (y / 8) ^ (2 : ℕ) = y ^ 2 / 64 by ring]
        have hy2 : y ^ 3 ≤ y ^ 2 := by nlinarith [sq_nonneg y, pow_nonneg (le_of_lt hy0) 2]
        linarith
      -- monotone of x^3 on nonneg
      have hb : (y / 4) ≤ Real.rpow (y / 8) (2 / 3) := by
        by_contra hcon
        push Not at hcon
        have hlt : (Real.rpow (y / 8) (2 / 3)) ^ (3 : ℕ) < (y / 4) ^ (3 : ℕ) :=
          pow_lt_pow_left₀ hcon (le_of_lt hlhs_pos) (by norm_num)
        linarith
      exact hb
    have hdens_ge : Real.rpow (y / 8) e ≥ y / 4 := le_trans hstep2 hstep1
    -- now monotonicity: D[p+δ, 2x, (y/8)^e] ≥ D[p+δ, x, y/4] = S2
    have hxbound : 2 * x ≤ 1 := by linarith
    have hmono := monotonicity M (p + δ) (p + δ) x (2 * x) (y / 4)
      (Real.rpow (y / 8) e) (by omega) (le_refl _) hx0 (by linarith) hxbound
      hd2pos hdens_ge (rpow_mem_Ioc hy8pos hy8le he_nonneg).2
    calc DSet (bracket M (2 * p + δ) (2 * x) (y / 8))
        ≥ DSet (bracket M (p + δ) (2 * x) (Real.rpow (y / 8) e)) := hcor
      _ ≥ DSet (bracket M (p + δ) x (y / 4)) := hmono
  -- Step R7: cascade.
  -- j=2: R2 ≥ 1 + min(S2, deep2) = 1 + S2  (since deep2 ≥ S2)
  have hR2 : DSet (bracket M (2 * p + δ) (2 * x) (y / 4)) ≥ 1 + S2 := by
    have hmineq : min S2 (DSet (bracket M (2 * p + δ) (2 * x) (y / 8))) = S2 :=
      min_eq_left hDeep2
    calc DSet (bracket M (2 * p + δ) (2 * x) (y / 4))
        ≥ 1 + min S2 (DSet (bracket M (2 * p + δ) (2 * x) (y / 8))) := hRung2
      _ = 1 + S2 := by rw [hmineq]
  -- j=1: R1 ≥ 1 + min(S1, R2) ≥ 1 + min(S1, 1+S2)
  have hR1 : DSet (bracket M (2 * p + δ) (2 * x) (y / 2)) ≥ 1 + min S1 (1 + S2) := by
    have hmono_min : min S1 (DSet (bracket M (2 * p + δ) (2 * x) (y / 4)))
        ≥ min S1 (1 + S2) := by
      apply le_min
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) hR2
    calc DSet (bracket M (2 * p + δ) (2 * x) (y / 2))
        ≥ 1 + min S1 (DSet (bracket M (2 * p + δ) (2 * x) (y / 4))) := hRung1
      _ ≥ 1 + min S1 (1 + S2) := Nat.add_le_add_left hmono_min 1
  -- j=0: R0 ≥ 1 + min(S0, R1) ≥ 1 + min(S0, 1 + min(S1, 1+S2))
  have hmono_min0 : min S0 (DSet (bracket M (2 * p + δ) (2 * x) (y / 2)))
      ≥ min S0 (1 + min S1 (1 + S2)) := by
    apply le_min
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) hR1
  have hR0 : DSet (bracket M (2 * p + δ) (2 * x) y) ≥ 1 + min S0 (1 + min S1 (1 + S2)) := by
    calc DSet (bracket M (2 * p + δ) (2 * x) y)
        ≥ 1 + min S0 (DSet (bracket M (2 * p + δ) (2 * x) (y / 2))) := hRung0
      _ ≥ 1 + min S0 (1 + min S1 (1 + S2)) := Nat.add_le_add_left hmono_min0 1
  -- final: 1 + min(S0, 1+min(S1,1+S2)) = 1 + min(S0, min(1+S1, 2+S2))
  have hlattice : min S0 (1 + min S1 (1 + S2)) = min S0 (min (1 + S1) (2 + S2)) := by
    congr 1
    omega
  rw [hlattice] at hR0
  exact hR0

/-- Density relaxation: for `0 < y`, `1 ≤ c`, `0 ≤ w ≤ 1`,
`y^w / c ≤ (y/c)^w`. -/
private theorem density_relax {y w c : ℝ} (hy0 : 0 < y) (hc1 : 1 ≤ c)
    (hw1 : w ≤ 1) :
    Real.rpow y w / c ≤ Real.rpow (y / c) w := by
  have hc0 : 0 < c := by linarith
  have hsplit : Real.rpow (y / c) w = Real.rpow y w / Real.rpow c w :=
    Real.div_rpow (le_of_lt hy0) (le_of_lt hc0) w
  rw [hsplit]
  -- y^w / c ≤ y^w / c^w  since  c^w ≤ c
  have hcw_le : Real.rpow c w ≤ c := by
    calc Real.rpow c w ≤ Real.rpow c 1 :=
          Real.rpow_le_rpow_of_exponent_le hc1 hw1
      _ = c := Real.rpow_one c
  have hcw_pos : 0 < Real.rpow c w := Real.rpow_pos_of_pos hc0 w
  have hyw_pos : 0 < Real.rpow y w := Real.rpow_pos_of_pos hy0 w
  apply div_le_div_of_nonneg_left (le_of_lt hyw_pos) hcw_pos hcw_le

/-- A single rung of the column partition lemma at density `d ∈ (0,1]` via
Lemma A.1 at `δ = 0`, `N = p`. The first exponent `(p+0)/(p(1+τ)+0)` is
simplified to `1/(1+τ)`. -/
private theorem col_rung
    (M : BoolMat) (p : ℕ) (hp : 1 ≤ p) (τ : ℝ) (hτ : 0 < τ ∧ τ ≤ 1)
    (x : ℝ) (hx0 : 0 < x) (hx12 : x ≤ 1 / 2) (d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hTpos : DSet (bracket M (2 * p) (2 * x) d) ≥ 1) :
    DSet (bracket M (2 * p) (2 * x) d) ≥
      1 + min
        (DSet (bracket M p x (Real.rpow d (1 / (1 + τ)))))
        (min
          (DSet (bracket M (⌊(p : ℝ) * (1 - τ)⌋₊ + 1) x (Real.rpow d (τ / (1 + τ)))))
          (DSet (bracket M (2 * p) (2 * x) (d / 2)))) := by
  obtain ⟨hτ0, hτ1⟩ := hτ
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpR0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hτ1pos : 0 < 1 + τ := by linarith
  -- Apply A.1 with δ = 0
  have hA1 := lemma_A1_partition_recurrence M p hp τ ⟨hτ0, hτ1⟩ 0 (by omega) x d
    ⟨hx0, hx12, hd0, hd1⟩ (by simpa using hTpos)
  -- simplify 2*p+0 = 2*p in hypothesis is automatic via simp
  simp only [Nat.add_zero, Nat.cast_zero, add_zero] at hA1
  -- first exponent: (p)/(p*(1+τ)) = 1/(1+τ)
  have hexp1 : ((p : ℝ)) / ((p : ℝ) * (1 + τ)) = 1 / (1 + τ) := by
    field_simp
  rw [hexp1] at hA1
  exact hA1

/-- Lemma A.2 (Three-Rung Partition Lemma) — column inequality.

For a matrix `M`, `p ≥ 1`, `δ ∈ {0,1}`, `0 < x ≤ 1/2`, `0 < y ≤ 1`, assuming
`D([M]_{2p, 2x, y/4}) ≥ 1`, for every `0 < τ ≤ 1`, with `u = y^{1/(1+τ)}`,
`v = y^{τ/(1+τ)}`:
`D([M]_{2p, 2x, y}) ≥ 1 + min( min_{0≤j<3}(j + D([M]_{p, x, u/2^j})),
min_{0≤j<3}(j + D([M]_{⌊p(1−τ)⌋+1, x, v/2^j})) )`. -/
theorem lemma_A2_three_rung_col
    (M : BoolMat) (p : ℕ) (hp : 1 ≤ p) (δ : ℕ) (hδ : δ ≤ 1) (x y : ℝ)
    (hxy : 0 < x ∧ x ≤ 1 / 2 ∧ 0 < y ∧ y ≤ 1)
    (h1 : DSet (bracket M (2 * p) (2 * x) (y / 4)) ≥ 1)
    (τ : ℝ) (hτ : 0 < τ ∧ τ ≤ 1) :
    DSet (bracket M (2 * p) (2 * x) y) ≥
      1 + min
        (let u := Real.rpow y (1 / (1 + τ));
         min
          (DSet (bracket M p x u))
          (min
            (1 + DSet (bracket M p x (u / 2)))
            (2 + DSet (bracket M p x (u / 4)))))
        (let v := Real.rpow y (τ / (1 + τ));
         min
          (DSet (bracket M (⌊(p : ℝ) * (1 - τ)⌋₊ + 1) x v))
          (min
            (1 + DSet (bracket M (⌊(p : ℝ) * (1 - τ)⌋₊ + 1) x (v / 2)))
            (2 + DSet (bracket M (⌊(p : ℝ) * (1 - τ)⌋₊ + 1) x (v / 4))))) := by
  obtain ⟨hx0, hx12, hy0, hy1⟩ := hxy
  obtain ⟨hτ0, hτ1⟩ := hτ
  simp only []
  have hx1 : x ≤ 1 := by linarith
  have hτ1pos : 0 < 1 + τ := by linarith
  -- exponents w1 = 1/(1+τ), w2 = τ/(1+τ); both in (0,1]
  set w1 : ℝ := 1 / (1 + τ) with hw1def
  set w2 : ℝ := τ / (1 + τ) with hw2def
  have hw1_0 : 0 ≤ w1 := by rw [hw1def]; positivity
  have hw1_1 : w1 ≤ 1 := by
    rw [hw1def, div_le_one hτ1pos]; linarith
  have hw2_0 : 0 ≤ w2 := by rw [hw2def]; positivity
  have hw2_1 : w2 ≤ 1 := by
    rw [hw2def, div_le_one hτ1pos]; linarith
  set u : ℝ := Real.rpow y w1 with hudef
  set v : ℝ := Real.rpow y w2 with hvdef
  -- densities
  have hd1pos : 0 < y / 2 := by positivity
  have hd2pos : 0 < y / 4 := by positivity
  have hd1le : y / 2 ≤ 1 := by linarith
  have hd2le : y / 4 ≤ 1 := by linarith
  -- nonemptiness: T0,T1,T2 ≥ 1
  have hmono_rung : ∀ d : ℝ, 0 < d → d ≤ 1 → y / 4 ≤ d →
      DSet (bracket M (2 * p) (2 * x) d) ≥ 1 := by
    intro d hd0 hd1 hgd
    have hle := monotonicity M (2 * p) (2 * p) (2 * x) (2 * x) (y / 4) d
      (by omega) (by omega) (by linarith) (le_refl _) (by linarith)
      hd2pos hgd hd1
    exact le_trans h1 hle
  have hT0pos := hmono_rung y hy0 hy1 (by linarith)
  have hT1pos := hmono_rung (y / 2) hd1pos hd1le (by linarith)
  have hT2pos := hmono_rung (y / 4) hd2pos hd2le (le_refl _)
  -- the floor projection index
  set q : ℕ := ⌊(p : ℝ) * (1 - τ)⌋₊ + 1 with hqdef
  -- abbreviations for U_j and V_j
  set U0 := DSet (bracket M p x u) with hU0def
  set U1 := DSet (bracket M p x (u / 2)) with hU1def
  set U2 := DSet (bracket M p x (u / 4)) with hU2def
  set V0 := DSet (bracket M q x v) with hV0def
  set V1 := DSet (bracket M q x (v / 2)) with hV1def
  set V2 := DSet (bracket M q x (v / 4)) with hV2def
  -- per-rung col bounds (Lemma A.1)
  have hRung0 := col_rung M p hp τ ⟨hτ0, hτ1⟩ x hx0 hx12 y hy0 hy1 hT0pos
  have hRung1 := col_rung M p hp τ ⟨hτ0, hτ1⟩ x hx0 hx12 (y / 2) hd1pos hd1le hT1pos
  have hRung2 := col_rung M p hp τ ⟨hτ0, hτ1⟩ x hx0 hx12 (y / 4) hd2pos hd2le hT2pos
  -- fix deep-child densities: (y/2)/2 = y/4, (y/4)/2 = y/8
  rw [show (y / 2) / 2 = y / 4 by ring] at hRung1
  rw [show (y / 4) / 2 = y / 8 by ring] at hRung2
  -- relate first/second children to U_j and V_j.
  -- For j = 0: y^{w1} = u (def), y^{w2} = v (def).
  -- For j = 1: (y/2)^{w1} ≥ u/2,  (y/2)^{w2} ≥ v/2.
  -- For j = 2: (y/4)^{w1} ≥ u/4,  (y/4)^{w2} ≥ v/4.
  -- We package the j-th rung into: T_j ≥ 1 + min(U_j, min(V_j, T_{j+1})).
  -- j = 0
  have hU0eq : Real.rpow y w1 = u := hudef.symm
  have hV0eq : Real.rpow y w2 = v := hvdef.symm
  have hbound0 : DSet (bracket M (2 * p) (2 * x) y) ≥
      1 + min U0 (min V0 (DSet (bracket M (2 * p) (2 * x) (y / 2)))) := by
    rw [hU0eq, hV0eq] at hRung0
    exact hRung0
  -- helper to relax first child  D[p,x,(y/c)^{w1}] ≥ U_? = D[p,x,u/c]
  -- j = 1 first child
  have relax_U : ∀ (c : ℝ), 1 ≤ c → 0 < y / c → y / c ≤ 1 →
      DSet (bracket M p x (Real.rpow (y / c) w1)) ≥ DSet (bracket M p x (u / c)) := by
    intro c hc1 hyc0 hyc1
    have hge : u / c ≤ Real.rpow (y / c) w1 := by
      rw [hudef]; exact density_relax hy0 hc1 hw1_1
    have huc0 : 0 < u / c := by
      have : 0 < u := Real.rpow_pos_of_pos hy0 w1
      have hc0 : 0 < c := by linarith
      positivity
    exact monotonicity M p p x x (u / c) (Real.rpow (y / c) w1)
      (by omega) (le_refl _) hx0 (le_refl x) hx1 huc0 hge
      (rpow_mem_Ioc hyc0 hyc1 hw1_0).2
  have relax_V : ∀ (c : ℝ), 1 ≤ c → 0 < y / c → y / c ≤ 1 →
      DSet (bracket M q x (Real.rpow (y / c) w2)) ≥ DSet (bracket M q x (v / c)) := by
    intro c hc1 hyc0 hyc1
    have hge : v / c ≤ Real.rpow (y / c) w2 := by
      rw [hvdef]; exact density_relax hy0 hc1 hw2_1
    have hvc0 : 0 < v / c := by
      have : 0 < v := Real.rpow_pos_of_pos hy0 w2
      have hc0 : 0 < c := by linarith
      positivity
    exact monotonicity M q q x x (v / c) (Real.rpow (y / c) w2)
      (by omega) (le_refl _) hx0 (le_refl x) hx1 hvc0 hge
      (rpow_mem_Ioc hyc0 hyc1 hw2_0).2
  -- j = 1
  have hbound1 : DSet (bracket M (2 * p) (2 * x) (y / 2)) ≥
      1 + min U1 (min V1 (DSet (bracket M (2 * p) (2 * x) (y / 4)))) := by
    have hrelU := relax_U 2 (by norm_num) hd1pos hd1le
    have hrelV := relax_V 2 (by norm_num) hd1pos hd1le
    -- rw deep children density divisions in hRung1's terms: (y/2)/2 = y/4 already done.
    -- u/2 = U1 etc; chain monotonicity
    have hmin : min (DSet (bracket M p x (Real.rpow (y / 2) w1)))
        (min (DSet (bracket M q x (Real.rpow (y / 2) w2)))
          (DSet (bracket M (2 * p) (2 * x) (y / 4))))
        ≥ min U1 (min V1 (DSet (bracket M (2 * p) (2 * x) (y / 4)))) := by
      apply le_min
      · exact le_trans (min_le_left _ _) hrelU
      · apply le_min
        · exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) hrelV)
        · exact le_trans (min_le_right _ _) (min_le_right _ _)
    calc DSet (bracket M (2 * p) (2 * x) (y / 2))
        ≥ 1 + min (DSet (bracket M p x (Real.rpow (y / 2) w1)))
            (min (DSet (bracket M q x (Real.rpow (y / 2) w2)))
              (DSet (bracket M (2 * p) (2 * x) (y / 4)))) := hRung1
      _ ≥ 1 + min U1 (min V1 (DSet (bracket M (2 * p) (2 * x) (y / 4)))) :=
          Nat.add_le_add_left hmin 1
  -- j = 2: deep child is D[2p,2x,y/8]; bound it by U2.
  -- Step C4: D[2p,2x,y/8] ≥ U2.
  have hy8pos : 0 < y / 8 := by positivity
  have hy8le : y / 8 ≤ 1 := by linarith
  have hDeep2 : DSet (bracket M (2 * p) (2 * x) (y / 8)) ≥ U2 := by
    -- extended_maximum_projection total 2p, target p; exponent p/(2p)=1/2
    have hcor := extended_maximum_projection M (2 * p) p (2 * x) (y / 8)
      (by omega) (by omega) (by positivity)
    set e : ℝ := ((p : ℕ) : ℝ) / ((2 * p : ℕ) : ℝ) with hedef
    have h2pR0 : 0 < ((2 * p : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((2 * p : ℕ) : ℝ) := by
        have : 1 ≤ 2 * p := by omega
        exact_mod_cast this
      linarith
    have he_half : e = 1 / 2 := by
      rw [hedef]; push_cast; field_simp
    rw [he_half] at hcor
    -- now (y/8)^{1/2} ≥ u/4
    have hge : u / 4 ≤ Real.rpow (y / 8) (1 / 2) := by
      -- u = y^{w1} ≤ y^{1/2} since w1 ≥ 1/2 and base ≤ 1
      have hw1_ge_half : 1 / 2 ≤ w1 := by
        rw [hw1def, le_div_iff₀ hτ1pos]; linarith
      have hu_le : u ≤ Real.rpow y (1 / 2) := by
        rw [hudef]; exact rpow_antitone hy0 hy1 hw1_ge_half
      -- y^{1/2}/4 = √(y/16) ≤ √(y/8) = (y/8)^{1/2}
      -- u/4 ≤ y^{1/2}/4 ≤ (y/8)^{1/2}
      have hstep1 : u / 4 ≤ Real.rpow y (1 / 2) / 4 := by
        apply div_le_div_of_nonneg_right hu_le (by norm_num)
      have hstep2 : Real.rpow y (1 / 2) / 4 ≤ Real.rpow (y / 8) (1 / 2) := by
        -- (y/8)^{1/2} = y^{1/2}/8^{1/2}; want y^{1/2}/4 ≤ y^{1/2}/8^{1/2}, i.e. 8^{1/2} ≤ 4
        rw [show Real.rpow (y / 8) (1 / 2) = Real.rpow y (1/2) / Real.rpow (8:ℝ) (1/2) from
            Real.div_rpow (le_of_lt hy0) (by norm_num : (0:ℝ) ≤ 8) (1/2)]
        have h8 : Real.rpow (8:ℝ) (1/2) ≤ 4 := by
          have h8pos : 0 < Real.rpow (8:ℝ) (1/2) := Real.rpow_pos_of_pos (by norm_num) _
          have hsq : (Real.rpow (8:ℝ) (1/2)) ^ (2 : ℕ) = 8 := by
            have hh : Real.rpow (8:ℝ) (1/2) ^ ((2:ℕ):ℝ)
                = Real.rpow (8:ℝ) ((1/2) * ((2:ℕ):ℝ)) :=
              rpow_fold (8:ℝ) (by norm_num) (1/2) ((2:ℕ):ℝ)
            rw [← Real.rpow_natCast (Real.rpow (8:ℝ) (1/2)) 2, hh]
            norm_num
          nlinarith [hsq, h8pos]
        have h8pos : 0 < Real.rpow (8:ℝ) (1/2) := Real.rpow_pos_of_pos (by norm_num) _
        have hyhalf_pos : 0 < Real.rpow y (1/2) := Real.rpow_pos_of_pos hy0 _
        apply div_le_div_of_nonneg_left (le_of_lt hyhalf_pos) h8pos h8
      linarith
    have huc0 : 0 < u / 4 := by
      have : 0 < u := Real.rpow_pos_of_pos hy0 w1
      positivity
    have hxbound : 2 * x ≤ 1 := by linarith
    have hmono := monotonicity M p p x (2 * x) (u / 4) (Real.rpow (y / 8) (1 / 2))
      (by omega) (le_refl _) hx0 (by linarith) hxbound huc0 hge
      (rpow_mem_Ioc hy8pos hy8le (by norm_num)).2
    calc DSet (bracket M (2 * p) (2 * x) (y / 8))
        ≥ DSet (bracket M p (2 * x) (Real.rpow (y / 8) (1 / 2))) := hcor
      _ ≥ DSet (bracket M p x (u / 4)) := hmono
  have hbound2 : DSet (bracket M (2 * p) (2 * x) (y / 4)) ≥
      1 + min U2 V2 := by
    have hrelU := relax_U 4 (by norm_num) hd2pos hd2le
    have hrelV := relax_V 4 (by norm_num) hd2pos hd2le
    -- hRung2 : T2 ≥ 1 + min (D[p,x,(y/4)^w1]) (min (D[q,x,(y/4)^w2]) (D[2p,2x,y/8]))
    have hmin : min (DSet (bracket M p x (Real.rpow (y / 4) w1)))
        (min (DSet (bracket M q x (Real.rpow (y / 4) w2)))
          (DSet (bracket M (2 * p) (2 * x) (y / 8))))
        ≥ min U2 V2 := by
      apply le_min
      · exact le_trans (min_le_left _ _) hrelU
      · apply le_min
        · exact le_trans (min_le_right _ _) hrelV
        · exact le_trans (min_le_left _ _) hDeep2
    calc DSet (bracket M (2 * p) (2 * x) (y / 4))
        ≥ 1 + min (DSet (bracket M p x (Real.rpow (y / 4) w1)))
            (min (DSet (bracket M q x (Real.rpow (y / 4) w2)))
              (DSet (bracket M (2 * p) (2 * x) (y / 8)))) := hRung2
      _ ≥ 1 + min U2 V2 := Nat.add_le_add_left hmin 1
  -- cascade upward
  -- T1 ≥ 1 + min(U1, min(V1, T2)) ≥ 1 + min(U1, min(V1, 1+min(U2,V2)))
  have hcasc1 : DSet (bracket M (2 * p) (2 * x) (y / 2)) ≥
      1 + min U1 (min V1 (1 + min U2 V2)) := by
    have hmin : min U1 (min V1 (DSet (bracket M (2 * p) (2 * x) (y / 4))))
        ≥ min U1 (min V1 (1 + min U2 V2)) := by
      apply le_min
      · exact min_le_left _ _
      · apply le_min
        · exact le_trans (min_le_right _ _) (min_le_left _ _)
        · exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) hbound2
    calc DSet (bracket M (2 * p) (2 * x) (y / 2))
        ≥ 1 + min U1 (min V1 (DSet (bracket M (2 * p) (2 * x) (y / 4)))) := hbound1
      _ ≥ 1 + min U1 (min V1 (1 + min U2 V2)) := Nat.add_le_add_left hmin 1
  -- T0 ≥ 1 + min(U0, min(V0, T1)) ≥ 1 + min(U0, min(V0, 1+min(U1,min(V1,1+min(U2,V2)))))
  have hcasc0 : DSet (bracket M (2 * p) (2 * x) y) ≥
      1 + min U0 (min V0 (1 + min U1 (min V1 (1 + min U2 V2)))) := by
    have hmin : min U0 (min V0 (DSet (bracket M (2 * p) (2 * x) (y / 2))))
        ≥ min U0 (min V0 (1 + min U1 (min V1 (1 + min U2 V2)))) := by
      apply le_min
      · exact min_le_left _ _
      · apply le_min
        · exact le_trans (min_le_right _ _) (min_le_left _ _)
        · exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) hcasc1
    calc DSet (bracket M (2 * p) (2 * x) y)
        ≥ 1 + min U0 (min V0 (DSet (bracket M (2 * p) (2 * x) (y / 2)))) := hbound0
      _ ≥ 1 + min U0 (min V0 (1 + min U1 (min V1 (1 + min U2 V2)))) :=
          Nat.add_le_add_left hmin 1
  -- reorganize the bound into the u-ladder / v-ladder grouping (Step C6).
  -- Goal RHS = 1 + min(min(U0, min(1+U1, 2+U2)), min(V0, min(1+V1, 2+V2)))
  have hlattice :
      min U0 (min V0 (1 + min U1 (min V1 (1 + min U2 V2))))
      = min (min U0 (min (1 + U1) (2 + U2))) (min V0 (min (1 + V1) (2 + V2))) := by
    omega
  rw [hlattice] at hcasc0
  exact hcasc0

/-- Lemma A.3 (Row ladder step).

Under `D([M]_{2p, 2x, y/4}) ≥ 1` (same hyps as A.2):
`Λ_M(2p+δ, 2x, y) ≥ 1 + Λ_M(p+δ, x, y)`. -/
theorem lemma_A3_row_ladder_step
    (M : BoolMat) (p : ℕ) (hp : 1 ≤ p) (δ : ℕ) (hδ : δ ≤ 1) (x y : ℝ)
    (hxy : 0 < x ∧ x ≤ 1 / 2 ∧ 0 < y ∧ y ≤ 1)
    (h1 : DSet (bracket M (2 * p) (2 * x) (y / 4)) ≥ 1) :
    Lambda M (2 * p + δ) (2 * x) y ≥ 1 + Lambda M (p + δ) x y := by
  obtain ⟨hx0, hx12, hy0, hy1⟩ := hxy
  have hx1 : x ≤ 1 := by linarith
  -- positivity of the three densities
  have hd1pos : 0 < y / 2 := by positivity
  have hd2pos : 0 < y / 4 := by positivity
  have hd1le : y / 2 ≤ 1 := by linarith
  have hd2le : y / 4 ≤ 1 := by linarith
  -- nonemptiness facts R0, R1, R2 ≥ 1 from h1 via monotonicity
  have hmono_rung : ∀ d : ℝ, 0 < d → d ≤ 1 → y / 4 ≤ d →
      DSet (bracket M (2 * p + δ) (2 * x) d) ≥ 1 := by
    intro d hd0 hd1 hgd
    have hle := monotonicity M (2 * p) (2 * p + δ) (2 * x) (2 * x) (y / 4) d
      (by omega) (by omega) (by linarith) (le_refl _) (by linarith)
      hd2pos hgd hd1
    exact le_trans h1 hle
  have hR0pos : DSet (bracket M (2 * p + δ) (2 * x) y) ≥ 1 :=
    hmono_rung y hy0 hy1 (by linarith)
  have hR1pos : DSet (bracket M (2 * p + δ) (2 * x) (y / 2)) ≥ 1 :=
    hmono_rung (y / 2) hd1pos hd1le (by linarith)
  have hR2pos : DSet (bracket M (2 * p + δ) (2 * x) (y / 4)) ≥ 1 :=
    hmono_rung (y / 4) hd2pos hd2le (le_refl _)
  -- Abbreviations for S0, S1, S2
  set S0 := DSet (bracket M (p + δ) x y) with hS0def
  set S1 := DSet (bracket M (p + δ) x (y / 2)) with hS1def
  set S2 := DSet (bracket M (p + δ) x (y / 4)) with hS2def
  -- Per-rung bounds
  have hRung0 := row_rung M p hp δ hδ x hx0 hx12 y hy0 hy1 hR0pos
  have hRung1 := row_rung M p hp δ hδ x hx0 hx12 (y / 2) hd1pos hd1le hR1pos
  have hRung2 := row_rung M p hp δ hδ x hx0 hx12 (y / 4) hd2pos hd2le hR2pos
  have he1 : (y / 2) / 2 = y / 4 := by ring
  have he2 : (y / 4) / 2 = y / 8 := by ring
  rw [he1] at hRung1
  rw [he2] at hRung2
  -- Step R6: deep child of j=2 (D[2p+δ, 2x, y/8]) ≥ S2.
  have hDeep2 : DSet (bracket M (2 * p + δ) (2 * x) (y / 8)) ≥ S2 := by
    have hcor := extended_maximum_projection M (2 * p + δ) (p + δ) (2 * x)
      (y / 8) (by omega) (by omega) (by positivity)
    set e : ℝ := ((p + δ : ℕ) : ℝ) / ((2 * p + δ : ℕ) : ℝ) with hedef
    have h2pδR0 : 0 < ((2 * p + δ : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((2 * p + δ : ℕ) : ℝ) := by
        have : 1 ≤ 2 * p + δ := by omega
        exact_mod_cast this
      linarith
    have he_nonneg : 0 ≤ e := by
      rw [hedef]; exact div_nonneg (by positivity) (le_of_lt h2pδR0)
    have he_le : e ≤ 2 / 3 := by
      rw [hedef, div_le_div_iff₀ h2pδR0 (by norm_num : (0:ℝ) < 3)]
      push_cast
      have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      have hδR : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ
      nlinarith
    have hy8pos : 0 < y / 8 := by positivity
    have hy8le : y / 8 ≤ 1 := by linarith
    have hstep1 : Real.rpow (y / 8) e ≥ Real.rpow (y / 8) (2 / 3) :=
      rpow_antitone hy8pos hy8le he_le
    have hstep2 : Real.rpow (y / 8) (2 / 3) ≥ y / 4 := by
      have hlhs_pos : 0 < Real.rpow (y / 8) (2 / 3) := Real.rpow_pos_of_pos hy8pos _
      have hcube_lhs : (Real.rpow (y / 8) (2 / 3)) ^ (3 : ℕ) = (y / 8) ^ (2 : ℕ) := by
        have h1 : (Real.rpow (y / 8) (2 / 3)) ^ (3 : ℕ)
            = Real.rpow (y / 8) ((2 / 3) * (3 : ℕ)) := by
          rw [← Real.rpow_natCast (Real.rpow (y / 8) (2 / 3)) 3]
          exact rpow_fold (y / 8) (le_of_lt hy8pos) (2 / 3) ((3 : ℕ) : ℝ)
        rw [h1, show (2 / 3 : ℝ) * ((3 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by push_cast; ring]
        exact Real.rpow_natCast (y / 8) 2
      have hpow3 : (y / 4) ^ (3 : ℕ) ≤ (Real.rpow (y / 8) (2 / 3)) ^ (3 : ℕ) := by
        rw [hcube_lhs]
        have : (y / 4) ^ (3 : ℕ) = y ^ 3 / 64 := by ring
        rw [this, show (y / 8) ^ (2 : ℕ) = y ^ 2 / 64 by ring]
        have hy2 : y ^ 3 ≤ y ^ 2 := by nlinarith [sq_nonneg y, pow_nonneg (le_of_lt hy0) 2]
        linarith
      have hb : (y / 4) ≤ Real.rpow (y / 8) (2 / 3) := by
        by_contra hcon
        push Not at hcon
        have hlt : (Real.rpow (y / 8) (2 / 3)) ^ (3 : ℕ) < (y / 4) ^ (3 : ℕ) :=
          pow_lt_pow_left₀ hcon (le_of_lt hlhs_pos) (by norm_num)
        linarith
      exact hb
    have hdens_ge : Real.rpow (y / 8) e ≥ y / 4 := le_trans hstep2 hstep1
    have hxbound : 2 * x ≤ 1 := by linarith
    have hmono := monotonicity M (p + δ) (p + δ) x (2 * x) (y / 4)
      (Real.rpow (y / 8) e) (by omega) (le_refl _) hx0 (by linarith) hxbound
      hd2pos hdens_ge (rpow_mem_Ioc hy8pos hy8le he_nonneg).2
    calc DSet (bracket M (2 * p + δ) (2 * x) (y / 8))
        ≥ DSet (bracket M (p + δ) (2 * x) (Real.rpow (y / 8) e)) := hcor
      _ ≥ DSet (bracket M (p + δ) x (y / 4)) := hmono
  -- Step R7: cascade -> three R-bounds.
  have hR2 : DSet (bracket M (2 * p + δ) (2 * x) (y / 4)) ≥ 1 + S2 := by
    have hmineq : min S2 (DSet (bracket M (2 * p + δ) (2 * x) (y / 8))) = S2 :=
      min_eq_left hDeep2
    calc DSet (bracket M (2 * p + δ) (2 * x) (y / 4))
        ≥ 1 + min S2 (DSet (bracket M (2 * p + δ) (2 * x) (y / 8))) := hRung2
      _ = 1 + S2 := by rw [hmineq]
  have hR1 : DSet (bracket M (2 * p + δ) (2 * x) (y / 2)) ≥ 1 + min S1 (1 + S2) := by
    have hmono_min : min S1 (DSet (bracket M (2 * p + δ) (2 * x) (y / 4)))
        ≥ min S1 (1 + S2) := by
      apply le_min
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) hR2
    calc DSet (bracket M (2 * p + δ) (2 * x) (y / 2))
        ≥ 1 + min S1 (DSet (bracket M (2 * p + δ) (2 * x) (y / 4))) := hRung1
      _ ≥ 1 + min S1 (1 + S2) := Nat.add_le_add_left hmono_min 1
  have hmono_min0 : min S0 (DSet (bracket M (2 * p + δ) (2 * x) (y / 2)))
      ≥ min S0 (1 + min S1 (1 + S2)) := by
    apply le_min
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) hR1
  have hR0 : DSet (bracket M (2 * p + δ) (2 * x) y) ≥ 1 + min S0 (1 + min S1 (1 + S2)) := by
    calc DSet (bracket M (2 * p + δ) (2 * x) y)
        ≥ 1 + min S0 (DSet (bracket M (2 * p + δ) (2 * x) (y / 2))) := hRung0
      _ ≥ 1 + min S0 (1 + min S1 (1 + S2)) := Nat.add_le_add_left hmono_min0 1
  -- Steps 1-4: unfold Lambda on both sides, then min-lattice arithmetic (omega).
  unfold Lambda
  refine le_min ?_ (le_min ?_ ?_)
  · -- R0 ≥ 1 + min S0 (min (1+S1) (2+S2))
    omega
  · -- 1 + R1 ≥ 1 + min S0 (min (1+S1) (2+S2))
    omega
  · -- 2 + R2 ≥ 1 + min S0 (min (1+S1) (2+S2))
    omega

/-- Lemma A.4 (Column ladder step).

Under `D([M]_{2p, 2x, y/4}) ≥ 1`, with `u = y^{1/(1+τ)}`, `v = y^{τ/(1+τ)}`,
`0 < τ ≤ 1`:
`Λ_M(2p, 2x, y) ≥ 1 + min( Λ_M(p, x, u), Λ_M(⌊p(1−τ)⌋+1, x, v) )`. -/
theorem lemma_A4_column_ladder_step
    (M : BoolMat) (p : ℕ) (hp : 1 ≤ p) (x y τ : ℝ)
    (hxyτ : 0 < x ∧ x ≤ 1 / 2 ∧ 0 < y ∧ y ≤ 1 ∧ 0 < τ ∧ τ ≤ 1)
    (h1 : DSet (bracket M (2 * p) (2 * x) (y / 4)) ≥ 1) :
    Lambda M (2 * p) (2 * x) y ≥
      1 + min
        (Lambda M p x (Real.rpow y (1 / (1 + τ))))
        (Lambda M (⌊(p : ℝ) * (1 - τ)⌋₊ + 1) x (Real.rpow y (τ / (1 + τ)))) := by
  obtain ⟨hx0, hx12, hy0, hy1, hτ0, hτ1⟩ := hxyτ
  have hx1 : x ≤ 1 := by linarith
  have hτ1pos : 0 < 1 + τ := by linarith
  -- exponents w1 = 1/(1+τ), w2 = τ/(1+τ); both in (0,1]
  set w1 : ℝ := 1 / (1 + τ) with hw1def
  set w2 : ℝ := τ / (1 + τ) with hw2def
  have hw1_0 : 0 ≤ w1 := by rw [hw1def]; positivity
  have hw1_1 : w1 ≤ 1 := by
    rw [hw1def, div_le_one hτ1pos]; linarith
  have hw2_0 : 0 ≤ w2 := by rw [hw2def]; positivity
  have hw2_1 : w2 ≤ 1 := by
    rw [hw2def, div_le_one hτ1pos]; linarith
  set u : ℝ := Real.rpow y w1 with hudef
  set v : ℝ := Real.rpow y w2 with hvdef
  -- densities
  have hd1pos : 0 < y / 2 := by positivity
  have hd2pos : 0 < y / 4 := by positivity
  have hd1le : y / 2 ≤ 1 := by linarith
  have hd2le : y / 4 ≤ 1 := by linarith
  -- nonemptiness: T0,T1,T2 ≥ 1
  have hmono_rung : ∀ d : ℝ, 0 < d → d ≤ 1 → y / 4 ≤ d →
      DSet (bracket M (2 * p) (2 * x) d) ≥ 1 := by
    intro d hd0 hd1 hgd
    have hle := monotonicity M (2 * p) (2 * p) (2 * x) (2 * x) (y / 4) d
      (by omega) (by omega) (by linarith) (le_refl _) (by linarith)
      hd2pos hgd hd1
    exact le_trans h1 hle
  have hT0pos := hmono_rung y hy0 hy1 (by linarith)
  have hT1pos := hmono_rung (y / 2) hd1pos hd1le (by linarith)
  have hT2pos := hmono_rung (y / 4) hd2pos hd2le (le_refl _)
  -- the floor projection index
  set q : ℕ := ⌊(p : ℝ) * (1 - τ)⌋₊ + 1 with hqdef
  -- abbreviations for U_j and V_j
  set U0 := DSet (bracket M p x u) with hU0def
  set U1 := DSet (bracket M p x (u / 2)) with hU1def
  set U2 := DSet (bracket M p x (u / 4)) with hU2def
  set V0 := DSet (bracket M q x v) with hV0def
  set V1 := DSet (bracket M q x (v / 2)) with hV1def
  set V2 := DSet (bracket M q x (v / 4)) with hV2def
  -- per-rung col bounds (Lemma A.1)
  have hRung0 := col_rung M p hp τ ⟨hτ0, hτ1⟩ x hx0 hx12 y hy0 hy1 hT0pos
  have hRung1 := col_rung M p hp τ ⟨hτ0, hτ1⟩ x hx0 hx12 (y / 2) hd1pos hd1le hT1pos
  have hRung2 := col_rung M p hp τ ⟨hτ0, hτ1⟩ x hx0 hx12 (y / 4) hd2pos hd2le hT2pos
  rw [show (y / 2) / 2 = y / 4 by ring] at hRung1
  rw [show (y / 4) / 2 = y / 8 by ring] at hRung2
  -- j = 0
  have hU0eq : Real.rpow y w1 = u := hudef.symm
  have hV0eq : Real.rpow y w2 = v := hvdef.symm
  have hbound0 : DSet (bracket M (2 * p) (2 * x) y) ≥
      1 + min U0 (min V0 (DSet (bracket M (2 * p) (2 * x) (y / 2)))) := by
    rw [hU0eq, hV0eq] at hRung0
    exact hRung0
  -- relax helpers
  have relax_U : ∀ (c : ℝ), 1 ≤ c → 0 < y / c → y / c ≤ 1 →
      DSet (bracket M p x (Real.rpow (y / c) w1)) ≥ DSet (bracket M p x (u / c)) := by
    intro c hc1 hyc0 hyc1
    have hge : u / c ≤ Real.rpow (y / c) w1 := by
      rw [hudef]; exact density_relax hy0 hc1 hw1_1
    have huc0 : 0 < u / c := by
      have : 0 < u := Real.rpow_pos_of_pos hy0 w1
      have hc0 : 0 < c := by linarith
      positivity
    exact monotonicity M p p x x (u / c) (Real.rpow (y / c) w1)
      (by omega) (le_refl _) hx0 (le_refl x) hx1 huc0 hge
      (rpow_mem_Ioc hyc0 hyc1 hw1_0).2
  have relax_V : ∀ (c : ℝ), 1 ≤ c → 0 < y / c → y / c ≤ 1 →
      DSet (bracket M q x (Real.rpow (y / c) w2)) ≥ DSet (bracket M q x (v / c)) := by
    intro c hc1 hyc0 hyc1
    have hge : v / c ≤ Real.rpow (y / c) w2 := by
      rw [hvdef]; exact density_relax hy0 hc1 hw2_1
    have hvc0 : 0 < v / c := by
      have : 0 < v := Real.rpow_pos_of_pos hy0 w2
      have hc0 : 0 < c := by linarith
      positivity
    exact monotonicity M q q x x (v / c) (Real.rpow (y / c) w2)
      (by omega) (le_refl _) hx0 (le_refl x) hx1 hvc0 hge
      (rpow_mem_Ioc hyc0 hyc1 hw2_0).2
  -- j = 1
  have hbound1 : DSet (bracket M (2 * p) (2 * x) (y / 2)) ≥
      1 + min U1 (min V1 (DSet (bracket M (2 * p) (2 * x) (y / 4)))) := by
    have hrelU := relax_U 2 (by norm_num) hd1pos hd1le
    have hrelV := relax_V 2 (by norm_num) hd1pos hd1le
    have hmin : min (DSet (bracket M p x (Real.rpow (y / 2) w1)))
        (min (DSet (bracket M q x (Real.rpow (y / 2) w2)))
          (DSet (bracket M (2 * p) (2 * x) (y / 4))))
        ≥ min U1 (min V1 (DSet (bracket M (2 * p) (2 * x) (y / 4)))) := by
      apply le_min
      · exact le_trans (min_le_left _ _) hrelU
      · apply le_min
        · exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) hrelV)
        · exact le_trans (min_le_right _ _) (min_le_right _ _)
    calc DSet (bracket M (2 * p) (2 * x) (y / 2))
        ≥ 1 + min (DSet (bracket M p x (Real.rpow (y / 2) w1)))
            (min (DSet (bracket M q x (Real.rpow (y / 2) w2)))
              (DSet (bracket M (2 * p) (2 * x) (y / 4)))) := hRung1
      _ ≥ 1 + min U1 (min V1 (DSet (bracket M (2 * p) (2 * x) (y / 4)))) :=
          Nat.add_le_add_left hmin 1
  -- j = 2 deep child: D[2p,2x,y/8] ≥ U2.
  have hy8pos : 0 < y / 8 := by positivity
  have hy8le : y / 8 ≤ 1 := by linarith
  have hDeep2 : DSet (bracket M (2 * p) (2 * x) (y / 8)) ≥ U2 := by
    have hcor := extended_maximum_projection M (2 * p) p (2 * x) (y / 8)
      (by omega) (by omega) (by positivity)
    set e : ℝ := ((p : ℕ) : ℝ) / ((2 * p : ℕ) : ℝ) with hedef
    have h2pR0 : 0 < ((2 * p : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((2 * p : ℕ) : ℝ) := by
        have : 1 ≤ 2 * p := by omega
        exact_mod_cast this
      linarith
    have he_half : e = 1 / 2 := by
      rw [hedef]; push_cast; field_simp
    rw [he_half] at hcor
    have hge : u / 4 ≤ Real.rpow (y / 8) (1 / 2) := by
      have hw1_ge_half : 1 / 2 ≤ w1 := by
        rw [hw1def, le_div_iff₀ hτ1pos]; linarith
      have hu_le : u ≤ Real.rpow y (1 / 2) := by
        rw [hudef]; exact rpow_antitone hy0 hy1 hw1_ge_half
      have hstep1 : u / 4 ≤ Real.rpow y (1 / 2) / 4 := by
        apply div_le_div_of_nonneg_right hu_le (by norm_num)
      have hstep2 : Real.rpow y (1 / 2) / 4 ≤ Real.rpow (y / 8) (1 / 2) := by
        rw [show Real.rpow (y / 8) (1 / 2) = Real.rpow y (1/2) / Real.rpow (8:ℝ) (1/2) from
            Real.div_rpow (le_of_lt hy0) (by norm_num : (0:ℝ) ≤ 8) (1/2)]
        have h8 : Real.rpow (8:ℝ) (1/2) ≤ 4 := by
          have h8pos : 0 < Real.rpow (8:ℝ) (1/2) := Real.rpow_pos_of_pos (by norm_num) _
          have hsq : (Real.rpow (8:ℝ) (1/2)) ^ (2 : ℕ) = 8 := by
            have hh : Real.rpow (8:ℝ) (1/2) ^ ((2:ℕ):ℝ)
                = Real.rpow (8:ℝ) ((1/2) * ((2:ℕ):ℝ)) :=
              rpow_fold (8:ℝ) (by norm_num) (1/2) ((2:ℕ):ℝ)
            rw [← Real.rpow_natCast (Real.rpow (8:ℝ) (1/2)) 2, hh]
            norm_num
          nlinarith [hsq, h8pos]
        have h8pos : 0 < Real.rpow (8:ℝ) (1/2) := Real.rpow_pos_of_pos (by norm_num) _
        have hyhalf_pos : 0 < Real.rpow y (1/2) := Real.rpow_pos_of_pos hy0 _
        apply div_le_div_of_nonneg_left (le_of_lt hyhalf_pos) h8pos h8
      linarith
    have huc0 : 0 < u / 4 := by
      have : 0 < u := Real.rpow_pos_of_pos hy0 w1
      positivity
    have hxbound : 2 * x ≤ 1 := by linarith
    have hmono := monotonicity M p p x (2 * x) (u / 4) (Real.rpow (y / 8) (1 / 2))
      (by omega) (le_refl _) hx0 (by linarith) hxbound huc0 hge
      (rpow_mem_Ioc hy8pos hy8le (by norm_num)).2
    calc DSet (bracket M (2 * p) (2 * x) (y / 8))
        ≥ DSet (bracket M p (2 * x) (Real.rpow (y / 8) (1 / 2))) := hcor
      _ ≥ DSet (bracket M p x (u / 4)) := hmono
  have hbound2 : DSet (bracket M (2 * p) (2 * x) (y / 4)) ≥
      1 + min U2 V2 := by
    have hrelU := relax_U 4 (by norm_num) hd2pos hd2le
    have hrelV := relax_V 4 (by norm_num) hd2pos hd2le
    have hmin : min (DSet (bracket M p x (Real.rpow (y / 4) w1)))
        (min (DSet (bracket M q x (Real.rpow (y / 4) w2)))
          (DSet (bracket M (2 * p) (2 * x) (y / 8))))
        ≥ min U2 V2 := by
      apply le_min
      · exact le_trans (min_le_left _ _) hrelU
      · apply le_min
        · exact le_trans (min_le_right _ _) hrelV
        · exact le_trans (min_le_left _ _) hDeep2
    calc DSet (bracket M (2 * p) (2 * x) (y / 4))
        ≥ 1 + min (DSet (bracket M p x (Real.rpow (y / 4) w1)))
            (min (DSet (bracket M q x (Real.rpow (y / 4) w2)))
              (DSet (bracket M (2 * p) (2 * x) (y / 8)))) := hRung2
      _ ≥ 1 + min U2 V2 := Nat.add_le_add_left hmin 1
  -- cascade upward to T1, T0
  have hcasc1 : DSet (bracket M (2 * p) (2 * x) (y / 2)) ≥
      1 + min U1 (min V1 (1 + min U2 V2)) := by
    have hmin : min U1 (min V1 (DSet (bracket M (2 * p) (2 * x) (y / 4))))
        ≥ min U1 (min V1 (1 + min U2 V2)) := by
      apply le_min
      · exact min_le_left _ _
      · apply le_min
        · exact le_trans (min_le_right _ _) (min_le_left _ _)
        · exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) hbound2
    calc DSet (bracket M (2 * p) (2 * x) (y / 2))
        ≥ 1 + min U1 (min V1 (DSet (bracket M (2 * p) (2 * x) (y / 4)))) := hbound1
      _ ≥ 1 + min U1 (min V1 (1 + min U2 V2)) := Nat.add_le_add_left hmin 1
  have hcasc0 : DSet (bracket M (2 * p) (2 * x) y) ≥
      1 + min U0 (min V0 (1 + min U1 (min V1 (1 + min U2 V2)))) := by
    have hmin : min U0 (min V0 (DSet (bracket M (2 * p) (2 * x) (y / 2))))
        ≥ min U0 (min V0 (1 + min U1 (min V1 (1 + min U2 V2)))) := by
      apply le_min
      · exact min_le_left _ _
      · apply le_min
        · exact le_trans (min_le_right _ _) (min_le_left _ _)
        · exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) hcasc1
    calc DSet (bracket M (2 * p) (2 * x) y)
        ≥ 1 + min U0 (min V0 (DSet (bracket M (2 * p) (2 * x) (y / 2)))) := hbound0
      _ ≥ 1 + min U0 (min V0 (1 + min U1 (min V1 (1 + min U2 V2)))) :=
          Nat.add_le_add_left hmin 1
  -- We now also need T1 and T2 bounds individually for the Lambda terms 1+T1, 2+T2.
  -- T1 ≥ 1 + min U1 (min V1 (1 + min U2 V2))  (hcasc1)
  -- T2 ≥ 1 + min U2 V2  (hbound2)
  -- Unfold Lambda on goal: LHS = min T0 (min (1+T1) (2+T2));
  --   inner u-term = min U0 (min (1+U1) (2+U2)); v-term = min V0 (min (1+V1) (2+V2)).
  unfold Lambda
  refine le_min ?_ (le_min ?_ ?_)
  · -- T0 ≥ 1 + min (min U0 (min (1+U1) (2+U2))) (min V0 (min (1+V1) (2+V2)))
    omega
  · -- 1 + T1 ≥ ...
    omega
  · -- 2 + T2 ≥ ...
    omega

end Proof.Appendix

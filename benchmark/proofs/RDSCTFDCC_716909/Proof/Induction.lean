import Mathlib
import Proof.Types.BoolMat
import Proof.Types.MatComplexity
import Proof.Types.Bracket
import Proof.Types.Lambda
import Proof.Types.Interlace
import Proof.BracketLemmas
import Proof.Appendix

set_option maxHeartbeats 2000000

namespace Proof.Induction

open Proof.Types.BoolMat
open Proof.Types.MatComplexity
open Proof.Types.Bracket
open Proof.Types.Lambda
open Proof.Types.Interlace
open Proof.BracketLemmas
open Proof.Appendix

/-- `Real.rpow 2 e = (2:ℝ)^e` (defeq, exposed for rewriting). -/
private theorem rp2 (e : ℝ) : Real.rpow 2 e = (2:ℝ)^e := rfl
private theorem rpf (b e : ℝ) : Real.rpow b e = b ^ e := rfl

/-- Row-density exponent identity: `2^{a-3/8}·2^{-a} = 2^{-3/8}`. -/
private theorem rowdens_id (a : ℝ) :
    Real.rpow 2 (a - 3/8) * Real.rpow 2 (-a) = Real.rpow 2 (-3/8) := by
  simp only [rp2]
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  ring_nf

/-- Step-3 row density: `2^{k-3}·2^{3-k-a} = 2^{-a}`. -/
private theorem step3_rowdens (k : ℕ) (a : ℝ) :
    Real.rpow 2 ((k:ℝ)-3) * Real.rpow 2 (3-(k:ℝ)-a) = Real.rpow 2 (-a) := by
  simp only [rp2]
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  ring_nf

/-- Step-3 column density: `(2^{-1})^{(√(k+a))^2} = 2^{-k-a}`. -/
private theorem step3_coldens (k : ℕ) (a : ℝ) (hka : (0:ℝ) ≤ (k:ℝ)+a) :
    Real.rpow (Real.rpow 2 (-1)) (Real.rpow (Real.sqrt ((k:ℝ)+a)) ((2:ℕ):ℝ))
      = Real.rpow 2 (-(k:ℝ)-a) := by
  have hsq2 : Real.rpow (Real.sqrt ((k:ℝ)+a)) ((2:ℕ):ℝ) = (k:ℝ)+a := by
    rw [show Real.rpow (Real.sqrt ((k:ℝ)+a)) ((2:ℕ):ℝ)
          = (Real.sqrt ((k:ℝ)+a)) ^ ((2:ℕ):ℝ) from rfl, Real.rpow_natCast]
    exact Real.sq_sqrt hka
  rw [hsq2]
  simp only [rp2]
  rw [show Real.rpow ((2:ℝ)^(-1:ℝ)) ((k:ℝ)+a) = ((2:ℝ)^(-1:ℝ))^((k:ℝ)+a) from rfl]
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  ring_nf

/-- Step-1 multiplier identity: with `α=2^{a-3/8}`, the product of the two
`a`-dependent fractions collapses to `3/4`. -/
private theorem qk_multiplier (a : ℝ) (ha : 3/8 < a) :
    ((3 * Real.rpow 2 a - 3) / (Real.rpow 2 (13/8) * Real.rpow 2 a - 4))
    * ((Real.rpow 2 (a - 3/8) - 1) * Real.rpow 2 (-a) / (1 - Real.rpow 2 (-a))) = 3/4 := by
  simp only [rp2]
  have htpos : (0:ℝ) < (2:ℝ)^a := Real.rpow_pos_of_pos (by norm_num) a
  have hrpos : (0:ℝ) < (2:ℝ)^(3/8 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have e_am : (2:ℝ)^(a - 3/8) = (2:ℝ)^a / (2:ℝ)^(3/8 : ℝ) := by
    rw [← Real.rpow_sub (by norm_num : (0:ℝ) < 2)]
  have e_13 : (2:ℝ)^(13/8 : ℝ) = 4 / (2:ℝ)^(3/8 : ℝ) := by
    rw [eq_div_iff (ne_of_gt hrpos), ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
        show (4:ℝ) = (2:ℝ)^((2:ℕ):ℝ) by rw [Real.rpow_natCast]; norm_num]
    norm_num
  have e_na : (2:ℝ)^(-a) = 1 / (2:ℝ)^a := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), one_div]
  rw [e_am, e_13, e_na]
  set t := (2:ℝ)^a with ht
  set r := (2:ℝ)^(3/8 : ℝ) with hr
  have ht1 : t > 1 := by
    rw [ht, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have htr : t > r := by
    rw [ht, hr]; exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hne1 : t - 1 ≠ 0 := by linarith
  have hner : t - r ≠ 0 := by linarith
  field_simp

/-- Step-3 numerical side condition: `(ρ-1)^{k-3} ≤ ρ^{(k-3)-2}` follows from
the theorem's hypothesis `√(k+a)-1 ≤ (k+a)^{1/2-1/(k-3)}`. -/
private theorem step3_rung (a : ℝ) (ha : 3/8 < a) (k : ℕ) (hk : 5 ≤ k)
    (hside : Real.sqrt ((k : ℝ) + a) - 1
        ≤ Real.rpow ((k : ℝ) + a) (1 / 2 - 1 / ((k : ℝ) - 3))) :
    Real.rpow (Real.sqrt ((k:ℝ)+a) - 1) (((k-3:ℕ)):ℝ)
      ≤ Real.rpow (Real.sqrt ((k:ℝ)+a)) ((((k-3:ℕ)):ℝ) - (((2:ℕ)):ℝ)) := by
  set ρ := Real.sqrt ((k:ℝ)+a) with hρdef
  have hkR : (5:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hka0 : (0:ℝ) ≤ (k:ℝ) + a := by linarith
  have hka4 : (4:ℝ) < (k:ℝ) + a := by linarith
  have hρ2 : (2:ℝ) < ρ := by
    rw [hρdef]
    have : Real.sqrt 4 < Real.sqrt ((k:ℝ)+a) := Real.sqrt_lt_sqrt (by norm_num) hka4
    rwa [show Real.sqrt 4 = 2 by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
  have hρsq : ρ^2 = (k:ℝ)+a := by rw [hρdef]; exact Real.sq_sqrt hka0
  have hρpos : 0 < ρ := by linarith
  have hk3cast : (((k-3:ℕ)):ℝ) = (k:ℝ) - 3 := by
    have h3 : 3 ≤ k := by omega
    rw [Nat.cast_sub h3]; norm_num
  have h2cast : (((2:ℕ)):ℝ) = (2:ℝ) := by norm_num
  rw [hk3cast, h2cast]
  have hk3pos : (0:ℝ) < (k:ℝ) - 3 := by linarith
  have hρ1 : (0:ℝ) ≤ ρ - 1 := by linarith
  have h1 : Real.rpow (ρ - 1) ((k:ℝ)-3)
      ≤ Real.rpow (Real.rpow ((k:ℝ)+a) (1/2 - 1/((k:ℝ)-3))) ((k:ℝ)-3) :=
    Real.rpow_le_rpow hρ1 hside (le_of_lt hk3pos)
  have h2 : Real.rpow (Real.rpow ((k:ℝ)+a) (1/2 - 1/((k:ℝ)-3))) ((k:ℝ)-3)
      = Real.rpow ((k:ℝ)+a) ((1/2 - 1/((k:ℝ)-3)) * ((k:ℝ)-3)) := by
    simp only [rpf]
    rw [← Real.rpow_mul hka0]
  have hρsq' : (k:ℝ)+a = Real.rpow ρ ((2:ℕ):ℝ) := by
    simp only [rpf]; rw [Real.rpow_natCast]; exact hρsq.symm
  have h3 : Real.rpow ((k:ℝ)+a) ((1/2 - 1/((k:ℝ)-3)) * ((k:ℝ)-3))
      = Real.rpow ρ (((k:ℝ)-3) - 2) := by
    rw [hρsq']
    simp only [rpf]
    rw [← Real.rpow_mul (le_of_lt hρpos)]
    congr 1
    have hne : (k:ℝ) - 3 ≠ 0 := by linarith
    field_simp
    ring
  rw [h2, h3] at h1
  exact h1

/-- Packaged Λ-monotonicity in the column-density argument `y`. -/
private theorem lambda_y_mono (M : BoolMat) (p : ℕ) (hp : 1 ≤ p)
    (x y1 y2 : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy10 : 0 < y1) (hy12 : y1 ≤ y2) (hy21 : y2 ≤ 1) :
    Lambda M p x y1 ≤ Lambda M p x y2 := by
  unfold Lambda
  refine min_le_min ?_ (min_le_min ?_ ?_)
  · exact monotonicity M p p x x y1 y2 hp (le_refl p) hx0 (le_refl x) hx1
      hy10 hy12 hy21
  · exact Nat.add_le_add_left (monotonicity M p p x x (y1/2) (y2/2) hp (le_refl p)
      hx0 (le_refl x) hx1 (by linarith) (by linarith) (by linarith)) 1
  · exact Nat.add_le_add_left (monotonicity M p p x x (y1/4) (y2/4) hp (le_refl p)
      hx0 (le_refl x) hx1 (by linarith) (by linarith) (by linarith)) 2

/-- Packaged Λ-monotonicity in the copy-count argument `p`. -/
private theorem lambda_p_mono (M : BoolMat) (p1 p2 : ℕ) (hp1 : 1 ≤ p1) (hp12 : p1 ≤ p2)
    (x y : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1) :
    Lambda M p1 x y ≤ Lambda M p2 x y := by
  unfold Lambda
  refine min_le_min ?_ (min_le_min ?_ ?_)
  · exact monotonicity M p1 p2 x x y y hp1 hp12 hx0 (le_refl x) hx1
      hy0 (le_refl y) hy1
  · exact Nat.add_le_add_left (monotonicity M p1 p2 x x (y/2) (y/2) hp1 hp12
      hx0 (le_refl x) hx1 (by linarith) (le_refl _) (by linarith)) 1
  · exact Nat.add_le_add_left (monotonicity M p1 p2 x x (y/4) (y/4) hp1 hp12
      hx0 (le_refl x) hx1 (by linarith) (le_refl _) (by linarith)) 2

/-- **Lemma 4.8 (Iterated Partition Lemma).** -/
theorem lemma_4_8_iterated_partition
    (ρ : ℝ) (hρ : 2 < ρ)
    (β : ℝ) (hβ : β = (ρ - 1) / (ρ - 2))
    (M : BoolMat) (s k : ℕ) (hsk : s ≤ k)
    (p : ℕ) (hp : 1 ≤ p)
    (x y : ℝ)
    (hx0 : 0 < x) (hxk : x ≤ Real.rpow 2 (-(k : ℝ)))
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hseed : DSet (bracket M p x (y / 4)) ≥ 1)
    (hrung : Real.rpow (ρ - 1) (k : ℝ) ≤ Real.rpow ρ ((k : ℝ) - (s : ℝ))) :
    Lambda M
        (⌊Real.rpow 2 (k : ℝ) * Real.rpow β (s : ℝ) * (p : ℝ)⌋₊)
        (Real.rpow 2 (k : ℝ) * x)
        (Real.rpow y (Real.rpow ρ (s : ℝ)))
      ≥ k + Lambda M p x y
    ∧ DSet (bracket M
        (⌊Real.rpow 2 (k : ℝ) * Real.rpow β (s : ℝ) * (p : ℝ)⌋₊)
        (Real.rpow 2 (k : ℝ) * x)
        (Real.rpow y (Real.rpow ρ (s : ℝ))))
      ≥ k + Lambda M p x y := by
  -- Basic facts about ρ, τ, β.
  have hρ1 : (1:ℝ) < ρ - 1 := by linarith
  have hρ1pos : (0:ℝ) < ρ - 1 := by linarith
  have hρ2pos : (0:ℝ) < ρ - 2 := by linarith
  have hρpos : (0:ℝ) < ρ := by linarith
  set τ : ℝ := 1/(ρ-1) with hτdef
  have hτ0 : (0:ℝ) < τ := by rw [hτdef]; positivity
  have hτ1 : τ ≤ 1 := by
    rw [hτdef, div_le_one hρ1pos]; linarith
  have h1τ : (1:ℝ) - τ = (ρ-2)/(ρ-1) := by
    rw [hτdef]; field_simp; ring
  have h1τpos : (0:ℝ) < 1 - τ := by rw [h1τ]; positivity
  have hβpos : (0:ℝ) < β := by rw [hβ]; positivity
  have hβ1 : (1:ℝ) < β := by
    rw [hβ, lt_div_iff₀ hρ2pos]; linarith
  -- β = 1/(1-τ).
  have hβinv : β = 1/(1-τ) := by
    rw [hβ, h1τ, one_div_div]
  -- 1 + τ = ρ/(ρ-1).
  have h1pτ : (1:ℝ) + τ = ρ/(ρ-1) := by
    rw [hτdef]; field_simp; ring
  -- 1/(1+τ) = (ρ-1)/ρ.
  have hinv1pτ : (1:ℝ)/(1+τ) = (ρ-1)/ρ := by
    rw [h1pτ, one_div_div]
  -- τ/(1+τ) = 1/ρ.
  have hτ1pτ : τ/(1+τ) = 1/ρ := by
    rw [hτdef, h1pτ]; field_simp
  set Λ₀ : ℕ := Lambda M p x y with hΛ₀def
  -- Exponent function E.
  set E : ℕ → ℕ → ℝ := fun t r =>
    if t = 0 then 1
    else Real.rpow ρ (t:ℝ) * Real.rpow ((ρ-1)/ρ) ((k:ℝ) - (r:ℝ) - ((s:ℝ) - (t:ℝ))) with hEdef
  -- Copy-count function P.
  set P : ℕ → ℕ → ℕ := fun t r => ⌊Real.rpow 2 (r:ℝ) * Real.rpow β (t:ℝ) * (p:ℝ)⌋₊ with hPdef
  -- Grid value F.
  set F : ℕ → ℕ → ℕ := fun t r => Lambda M (P t r) (Real.rpow 2 (r:ℝ) * x) (Real.rpow y (E t r)) with hFdef
  -- Clean unfolding lemmas for E (avoid `simp only` over-reducing `if` on literal t).
  have hE_zero : ∀ r : ℕ, E 0 r = 1 := by
    intro r; show (if (0:ℕ) = 0 then (1:ℝ) else _) = 1; rw [if_pos rfl]
  have hE_nz : ∀ t r : ℕ, t ≠ 0 →
      E t r = Real.rpow ρ (t:ℝ) * Real.rpow ((ρ-1)/ρ) ((k:ℝ) - (r:ℝ) - ((s:ℝ) - (t:ℝ))) := by
    intro t r ht; show (if t = 0 then (1:ℝ) else _) = _; rw [if_neg ht]
  -- E is positive (so densities y^E stay in (0,1]).
  have hEpos : ∀ t r, 0 < E t r := by
    intro t r
    rw [hEdef]; simp only
    split
    · norm_num
    · apply mul_pos (Real.rpow_pos_of_pos hρpos _)
      exact Real.rpow_pos_of_pos (by positivity) _
  -- The density y^E is in (0,1].
  have hyEpos : ∀ t r, 0 < Real.rpow y (E t r) := fun t r => Real.rpow_pos_of_pos hy0 _
  have hyEle1 : ∀ t r, Real.rpow y (E t r) ≤ 1 := by
    intro t r; rw [rpf]
    calc y ^ (E t r) ≤ y ^ (0:ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_ge hy0 hy1 (le_of_lt (hEpos t r))
      _ = 1 := Real.rpow_zero y
  -- 2^r * x is in (0, 1/2] for r < k, and ≤ 1 for r ≤ k.
  have h2rxpos : ∀ r, 0 < Real.rpow 2 (r:ℝ) * x := by
    intro r; apply mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hx0
  have h2rxle : ∀ r : ℕ, (r:ℝ) ≤ (k:ℝ) - 1 → Real.rpow 2 (r:ℝ) * x ≤ 1/2 := by
    intro r hr
    calc Real.rpow 2 (r:ℝ) * x ≤ Real.rpow 2 (r:ℝ) * Real.rpow 2 (-(k:ℝ)) := by
          apply mul_le_mul_of_nonneg_left hxk (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      _ = Real.rpow 2 ((r:ℝ) - (k:ℝ)) := by
          rw [rp2, rp2, rp2, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; ring_nf
      _ ≤ Real.rpow 2 (-1 : ℝ) := by
          rw [rp2, rp2]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1/2 := by rw [rp2, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_one]; norm_num
  have h2rxle1 : ∀ r : ℕ, (r:ℝ) ≤ (k:ℝ) → Real.rpow 2 (r:ℝ) * x ≤ 1 := by
    intro r hr
    calc Real.rpow 2 (r:ℝ) * x ≤ Real.rpow 2 (r:ℝ) * Real.rpow 2 (-(k:ℝ)) := by
          apply mul_le_mul_of_nonneg_left hxk (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      _ = Real.rpow 2 ((r:ℝ) - (k:ℝ)) := by
          rw [rp2, rp2, rp2, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; ring_nf
      _ ≤ Real.rpow 2 (0 : ℝ) := by
          rw [rp2, rp2]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 := by rw [rp2, Real.rpow_zero]
  -- rpow fold helper.
  have rfold : ∀ (b a c : ℝ), 0 ≤ b → (b.rpow a).rpow c = b.rpow (a * c) :=
    fun b a c hb => (Real.rpow_mul hb a c).symm
  -- p > 0 as a real.
  have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp
  -- x ≤ 1.
  have hxle1 : x ≤ 1 := by
    refine le_trans hxk ?_
    rw [rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by simp [Nat.cast_nonneg])
  -- (ρ-1)/ρ ∈ (0,1).
  have hqr_pos : (0:ℝ) < (ρ-1)/ρ := by positivity
  have hqr_lt1 : (ρ-1)/ρ < 1 := by rw [div_lt_one hρpos]; linarith
  -- ====================================================================
  -- (B1) Row bridge: 2 * P t r ≤ P t (r+1).
  -- ====================================================================
  have hbridgeR : ∀ t r : ℕ, 2 * P t r ≤ P t (r+1) := by
    intro t r
    show 2 * ⌊Real.rpow 2 (r:ℝ) * β.rpow (t:ℝ) * (p:ℝ)⌋₊
        ≤ ⌊Real.rpow 2 ((r+1:ℕ):ℝ) * β.rpow (t:ℝ) * (p:ℝ)⌋₊
    have hbpos : (0:ℝ) < β.rpow (t:ℝ) := Real.rpow_pos_of_pos hβpos _
    set w : ℝ := Real.rpow 2 (r:ℝ) * β.rpow (t:ℝ) * (p:ℝ) with hwdef
    have hw0 : 0 ≤ w := by
      rw [hwdef]; have := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (r:ℝ); positivity
    have heq : Real.rpow 2 ((r+1:ℕ):ℝ) * β.rpow (t:ℝ) * (p:ℝ) = 2 * w := by
      rw [hwdef]; push_cast
      rw [rp2, rp2, Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]; ring
    rw [heq, Nat.le_floor_iff (by positivity)]
    have hfl : (⌊w⌋₊ : ℝ) ≤ w := Nat.floor_le hw0
    push_cast; linarith
  -- P t r ≥ 2^r * p ≥ 1.
  have hP_ge : ∀ t r : ℕ, (2^r) * p ≤ P t r := by
    intro t r
    show (2^r) * p ≤ ⌊Real.rpow 2 (r:ℝ) * β.rpow (t:ℝ) * (p:ℝ)⌋₊
    have hbtpos : (0:ℝ) < β.rpow (t:ℝ) := Real.rpow_pos_of_pos hβpos _
    have h2pos : (0:ℝ) < Real.rpow 2 (r:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    rw [Nat.le_floor_iff (by positivity)]
    have hβt : (1:ℝ) ≤ β.rpow (t:ℝ) := by
      rw [show (1:ℝ) = β.rpow 0 from (Real.rpow_zero β).symm]
      exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hβ1) (by positivity)
    have h2r : Real.rpow 2 (r:ℝ) = (2:ℝ)^r := by rw [rp2, Real.rpow_natCast]
    push_cast
    rw [h2r]
    have : ((2:ℝ)^r) * (p:ℝ) ≤ (2:ℝ)^r * β.rpow (t:ℝ) * (p:ℝ) := by
      have h2rp : (0:ℝ) < (2:ℝ)^r := by positivity
      nlinarith [hβt, hppos, h2rp, mul_nonneg (mul_nonneg (le_of_lt h2rp) (le_of_lt hppos)) (sub_nonneg.mpr hβt)]
    linarith
  have hP_pos : ∀ t r : ℕ, 1 ≤ P t r := by
    intro t r
    have h1 : 1 ≤ (2^r) * p := by
      have : 1 ≤ 2^r := Nat.one_le_two_pow
      calc 1 = 1 * 1 := by ring
        _ ≤ (2^r) * p := Nat.mul_le_mul this hp
    exact le_trans h1 (hP_ge t r)
  -- ====================================================================
  -- (B2) Column bridge: ⌊P t r * (1-τ)⌋₊ + 1 ≥ P (t-1) r  for 1 ≤ t.
  -- ====================================================================
  have hbridgeC : ∀ t r : ℕ, 1 ≤ t → P (t-1) r ≤ ⌊(P t r : ℝ) * (1 - τ)⌋₊ + 1 := by
    intro t r ht
    -- P t r = ⌊2^r β^t p⌋₊ ≥ 2^r β^t p - 1.
    have hPtr_ge : (Real.rpow 2 (r:ℝ) * β.rpow (t:ℝ) * (p:ℝ)) - 1 ≤ (P t r : ℝ) := by
      show (Real.rpow 2 (r:ℝ) * β.rpow (t:ℝ) * (p:ℝ)) - 1
          ≤ (⌊Real.rpow 2 (r:ℝ) * β.rpow (t:ℝ) * (p:ℝ)⌋₊ : ℝ)
      have := Nat.sub_one_lt_floor (Real.rpow 2 (r:ℝ) * β.rpow (t:ℝ) * (p:ℝ))
      linarith
    -- 1 - τ = 1/β.
    have h1τβ : (1 - τ) = 1 / β := by rw [hβinv]; field_simp
    -- (1-τ) > 0.
    have h1τ_rpow : (1 - τ) = β.rpow (-1) := by
      rw [rpf, Real.rpow_neg_one, h1τβ, one_div]
    have hβtm1 : β.rpow (t:ℝ) * (1 - τ) = β.rpow ((t:ℝ) - 1) := by
      rw [h1τ_rpow, rpf, rpf, rpf, ← Real.rpow_add hβpos]; ring_nf
    -- P (t-1) r = ⌊2^r β^{t-1} p⌋₊.
    -- Real lower target: 2^r β^{t-1} p ≤ (P t r)/β + something. We use floor facts.
    -- We show:  (P (t-1) r : ℝ) ≤ (P t r : ℝ) * (1-τ) + 1, then floor.
    set A : ℝ := Real.rpow 2 (r:ℝ) * β.rpow ((t:ℝ) - 1) * (p:ℝ) with hAdef
    have htc : ((t-1:ℕ):ℝ) = (t:ℝ) - 1 := by rw [Nat.cast_sub ht]; norm_num
    -- (P t r : ℝ) * (1-τ) ≥ A - (1-τ).
    have hkey : A - (1 - τ) ≤ (P t r : ℝ) * (1 - τ) := by
      have hposτ : (0:ℝ) ≤ 1 - τ := le_of_lt h1τpos
      have := mul_le_mul_of_nonneg_right hPtr_ge hposτ
      have hexpand : (Real.rpow 2 (r:ℝ) * β.rpow (t:ℝ) * (p:ℝ) - 1) * (1 - τ)
          = A - (1 - τ) := by
        rw [hAdef, ← hβtm1]; ring
      linarith [hexpand ▸ this]
    -- Now: P (t-1) r = ⌊A⌋₊ ≤ ⌊(P t r)(1-τ)⌋₊ + 1.
    show (⌊Real.rpow 2 (r:ℝ) * β.rpow ((t-1:ℕ):ℝ) * (p:ℝ)⌋₊ : ℕ)
        ≤ ⌊(P t r : ℝ) * (1 - τ)⌋₊ + 1
    rw [htc]
    -- ⌊A⌋₊ ≤ A ; and A - 1 < (P t r)(1-τ) + (something) ... use FloorShift.
    have hApos : (0:ℝ) ≤ A := by
      rw [hAdef]
      have h1 : (0:ℝ) < Real.rpow 2 (r:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
      have h2 : (0:ℝ) < β.rpow ((t:ℝ)-1) := Real.rpow_pos_of_pos hβpos _
      positivity
    have hAfloor : (⌊A⌋₊ : ℝ) ≤ A := Nat.floor_le hApos
    -- ⌊(P t r)(1-τ)⌋₊ > (P t r)(1-τ) - 1.
    set B : ℝ := (P t r : ℝ) * (1 - τ) with hBdef
    have hBpos : 0 ≤ B := by
      rw [hBdef]; exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt h1τpos)
    have hBfloor : B - 1 < (⌊B⌋₊ : ℝ) := by
      have := Nat.sub_one_lt_floor B
      linarith
    -- Combine: ⌊A⌋₊ ≤ A ≤ B + (1-τ) < B+1 ≤ ⌊B⌋₊ + 1 + 1? Need integer step.
    -- We have A ≤ B + (1-τ) ≤ B + 1.  And ⌊A⌋₊ ≤ A ≤ B+1.  Also ⌊B⌋₊+1 > B.
    -- ⌊A⌋₊ is an integer ≤ A ≤ B+1; ⌊B⌋₊+1 > B so ⌊B⌋₊+1 ≥ ... need ⌊A⌋₊ ≤ ⌊B⌋₊+1.
    have hAB : A ≤ B + 1 := by linarith [hkey]
    have hfloorAB : ⌊A⌋₊ ≤ ⌊B⌋₊ + 1 := by
      by_contra hcon
      push Not at hcon
      -- hcon : ⌊B⌋₊ + 1 < ⌊A⌋₊, i.e. ⌊B⌋₊ + 2 ≤ ⌊A⌋₊
      have h2 : (⌊B⌋₊ : ℝ) + 2 ≤ (⌊A⌋₊ : ℝ) := by
        have : ⌊B⌋₊ + 2 ≤ ⌊A⌋₊ := by omega
        exact_mod_cast this
      linarith [hAfloor, hBfloor, hAB]
    exact hfloorAB
  -- ====================================================================
  -- (S3) Exponent ceiling: E t r ≤ 2^r for admissible (t,r).
  -- ====================================================================
  -- First (S1): E t 0 ≤ 1 for 1 ≤ t ≤ s.
  have hE0 : ∀ t : ℕ, 1 ≤ t → t ≤ s → E t 0 ≤ 1 := by
    intro t ht hts
    rw [hE_nz t 0 (by omega), Nat.cast_zero]
    rw [show ((k:ℝ) - 0 - ((s:ℝ) - (t:ℝ))) = (k:ℝ) - (s:ℝ) + (t:ℝ) by ring]
    -- ρ^t * ((ρ-1)/ρ)^{k-s+t} = (ρ-1)^{k-s+t} / ρ^{k-s}.
    have hsplit : ρ.rpow (t:ℝ) * ((ρ-1)/ρ).rpow ((k:ℝ)-(s:ℝ)+(t:ℝ))
        = (ρ-1).rpow ((k:ℝ)-(s:ℝ)+(t:ℝ)) / ρ.rpow ((k:ℝ)-(s:ℝ)) := by
      simp only [rpf]
      rw [Real.div_rpow (by linarith) (le_of_lt hρpos)]
      rw [div_eq_mul_inv (((ρ-1))^((k:ℝ)-(s:ℝ)+(t:ℝ))) _, ← Real.rpow_neg (le_of_lt hρpos)]
      rw [mul_comm ((ρ)^(t:ℝ)) _, mul_assoc, ← Real.rpow_add hρpos]
      rw [show (-((k:ℝ)-(s:ℝ)+(t:ℝ)) + (t:ℝ)) = -((k:ℝ)-(s:ℝ)) by ring]
      rw [Real.rpow_neg (le_of_lt hρpos), ← div_eq_mul_inv]
    rw [hsplit]
    rw [div_le_one (show (0:ℝ) < ρ.rpow ((k:ℝ) - (s:ℝ)) from Real.rpow_pos_of_pos hρpos _)]
    -- (ρ-1)^{k-s+t} ≤ (ρ-1)^k ≤ ρ^{k-s}.
    have hts' : (t:ℝ) ≤ (s:ℝ) := by exact_mod_cast hts
    have hnum_le : (ρ-1).rpow ((k:ℝ)-(s:ℝ)+(t:ℝ)) ≤ (ρ-1).rpow (k:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hρ1)
        (by push_cast; linarith)
    linarith [hnum_le, hrung]
  -- (S3) by induction on r.
  have hE_ceil : ∀ r t : ℕ, t ≤ s → r ≤ k - s + t → E t r ≤ (2:ℝ)^r := by
    intro r
    induction r with
    | zero =>
      intro t hts hadm
      by_cases ht0 : t = 0
      · subst ht0; rw [hE_zero]; norm_num
      · have := hE0 t (by omega) hts; simpa using this
    | succ r ih =>
      intro t hts hadm
      by_cases ht0 : t = 0
      · subst ht0; rw [hE_zero]
        have : (1:ℝ) ≤ (2:ℝ)^(r+1) := by
          have : (1:ℝ) = (2:ℝ)^(0:ℕ) := by norm_num
          rw [this]; exact pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
      · -- t ≥ 1.  E t (r+1) = (ρ/(ρ-1)) E t r ≤ 2 E t r ≤ 2 * 2^r = 2^{r+1}.
        have hstep : E t (r+1) = (ρ/(ρ-1)) * E t r := by
          rw [hE_nz t (r+1) ht0, hE_nz t r ht0]
          rw [show ((k:ℝ)-((r+1:ℕ):ℝ)-((s:ℝ)-(t:ℝ))) = ((k:ℝ)-(r:ℝ)-((s:ℝ)-(t:ℝ))) - 1 by push_cast; ring]
          simp only [rpf]
          rw [Real.rpow_sub hqr_pos, Real.rpow_one]
          field_simp
        have hEtr_pos : 0 < E t r := hEpos t r
        have hih : E t r ≤ (2:ℝ)^r := ih t hts (by omega)
        have hfrac : ρ/(ρ-1) < 2 := by rw [div_lt_iff₀ hρ1pos]; linarith
        have hfrac_pos : 0 < ρ/(ρ-1) := by positivity
        rw [hstep, pow_succ]
        have : (ρ/(ρ-1)) * E t r ≤ 2 * E t r := by
          apply mul_le_mul_of_nonneg_right (le_of_lt hfrac) (le_of_lt hEtr_pos)
        have h2 : 2 * E t r ≤ 2 * (2:ℝ)^r := by linarith [hih]
        nlinarith [this, h2, hih, hEtr_pos]
  -- ====================================================================
  -- (S) Side condition for admissible (t,r) with r < k-s+t.
  -- ====================================================================
  have hside : ∀ t r : ℕ, t ≤ s → r + 1 ≤ k - s + t →
      DSet (bracket M (2 * P t r) (Real.rpow 2 ((r+1:ℕ):ℝ) * x)
        ((y.rpow (E t (r+1))) / 4)) ≥ 1 := by
    intro t r hts hadm
    -- 1 ≤ p ≤ 2 * P t r.
    have hp_le : p ≤ 2 * P t r := by
      have h1 := hP_ge t r
      have h2 : 1 ≤ 2^r := Nat.one_le_two_pow
      nlinarith [h1, h2, hp]
    -- The projection density: ((y^{E t(r+1)})/4)^{p/(2 P t r)}.
    set q : ℝ := (p:ℝ) / ((2 * P t r : ℕ):ℝ) with hqdef
    have h2Ptr_pos : (0:ℝ) < ((2 * P t r : ℕ):ℝ) := by
      have : 1 ≤ 2 * P t r := by have := hP_pos t r; omega
      have : (1:ℝ) ≤ ((2 * P t r : ℕ):ℝ) := by exact_mod_cast this
      linarith
    have hq_pos : 0 < q := by rw [hqdef]; positivity
    -- q ≤ 1.
    have hq_le1 : q ≤ 1 := by
      rw [hqdef, div_le_one h2Ptr_pos]
      have : (p:ℝ) ≤ ((2 * P t r:ℕ):ℝ) := by exact_mod_cast hp_le
      exact this
    -- E t (r+1) * q ≤ 1.
    have hEq_le1 : E t (r+1) * q ≤ 1 := by
      have hEle : E t (r+1) ≤ (2:ℝ)^(r+1) := hE_ceil (r+1) t hts hadm
      have h2Ptr_ge : (2:ℝ)^(r+1) * (p:ℝ) ≤ ((2 * P t r:ℕ):ℝ) := by
        have hh : (2^(r+1)) * p ≤ 2 * P t r := by
          have := hP_ge t r
          calc (2^(r+1)) * p = 2 * (2^r * p) := by ring
            _ ≤ 2 * P t r := by omega
        have hcast : ((2^(r+1) * p : ℕ):ℝ) ≤ ((2 * P t r:ℕ):ℝ) := by exact_mod_cast hh
        calc (2:ℝ)^(r+1) * (p:ℝ) = ((2^(r+1) * p : ℕ):ℝ) := by push_cast; ring
          _ ≤ ((2 * P t r:ℕ):ℝ) := hcast
      rw [hqdef, ← mul_div_assoc]
      rw [div_le_one h2Ptr_pos]
      have hEpos1 : 0 < E t (r+1) := hEpos t (r+1)
      have h2r1pos : (0:ℝ) < (2:ℝ)^(r+1) := by positivity
      calc E t (r+1) * (p:ℝ) ≤ (2:ℝ)^(r+1) * (p:ℝ) := by
              apply mul_le_mul_of_nonneg_right hEle (le_of_lt hppos)
        _ ≤ ((2 * P t r:ℕ):ℝ) := h2Ptr_ge
    -- The projected density ≥ y/4.
    have hdens_ge : ((y.rpow (E t (r+1))) / 4).rpow q ≥ y / 4 := by
      simp only [rpf]
      rw [Real.div_rpow (show (0:ℝ) ≤ y ^ (E t (r+1)) from le_of_lt (hyEpos t (r+1)))
            (by norm_num : (0:ℝ) ≤ 4) q]
      rw [show (y ^ (E t (r+1))) ^ q = y ^ (E t (r+1) * q) from
            (Real.rpow_mul (le_of_lt hy0) _ _).symm]
      have hyge : y ≤ y ^ (E t (r+1) * q) := by
        nth_rewrite 1 [show y = y ^ (1:ℝ) by rw [Real.rpow_one]]
        exact Real.rpow_le_rpow_of_exponent_ge hy0 hy1 hEq_le1
      have h4pos : (0:ℝ) < (4:ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) _
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) h4pos]
      have h41 : (4:ℝ) ^ q ≤ (4:ℝ) ^ (1:ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hq_le1
      rw [Real.rpow_one] at h41
      nlinarith [hyge, h41, Real.rpow_pos_of_pos hy0 (E t (r+1) * q),
        Real.rpow_nonneg (le_of_lt hy0) (E t (r+1) * q)]
    -- Row range: 2^{r+1} x ≤ 1.
    have hrowle : Real.rpow 2 ((r+1:ℕ):ℝ) * x ≤ 1 := by
      apply h2rxle1
      push_cast
      have : (r:ℝ) + 1 ≤ (k:ℝ) := by
        have hh : r + 1 ≤ k := by omega
        exact_mod_cast hh
      linarith
    -- Monotonicity from hseed.
    have hcor := extended_maximum_projection M (2 * P t r) p
      (Real.rpow 2 ((r+1:ℕ):ℝ) * x) ((y.rpow (E t (r+1))) / 4) hp hp_le
      (by have := hyEpos t (r+1); positivity)
    have hxrow0 : (0:ℝ) < Real.rpow 2 ((r+1:ℕ):ℝ) * x := h2rxpos _
    have hmono := monotonicity M p p x (Real.rpow 2 ((r+1:ℕ):ℝ) * x)
      (y/4) (((y.rpow (E t (r+1))) / 4).rpow q)
      hp (le_refl p) hx0
      (by
        -- x ≤ 2^{r+1} x.
        have : (1:ℝ) ≤ Real.rpow 2 ((r+1:ℕ):ℝ) := by
          rw [rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by positivity)
        nlinarith [hx0, this])
      hrowle (by positivity) hdens_ge
      (by
        have h2 : (0:ℝ) ≤ y.rpow (E t (r+1)) := le_of_lt (hyEpos t (r+1))
        apply Real.rpow_le_one (by positivity) _ (le_of_lt hq_pos)
        have h1 : y.rpow (E t (r+1)) ≤ 1 := hyEle1 t (r+1)
        linarith)
    -- chain.
    have hkey : (1:ℕ) ≤ DSet (bracket M p (Real.rpow 2 ((r+1:ℕ):ℝ) * x)
        (((y.rpow (E t (r+1))) / 4).rpow q)) := le_trans hseed hmono
    -- Now ⌊p / (2 P t r)⌋ form must match hcor.  hcor uses (↑p / ↑(2*Ptr)).
    calc (1:ℕ) ≤ DSet (bracket M p (Real.rpow 2 ((r+1:ℕ):ℝ) * x)
            (((y.rpow (E t (r+1))) / 4).rpow q)) := hkey
      _ ≤ DSet (bracket M (2 * P t r) (Real.rpow 2 ((r+1:ℕ):ℝ) * x)
            ((y.rpow (E t (r+1))) / 4)) := by
          have hcong : (((y.rpow (E t (r+1))) / 4)).rpow ((p:ℝ)/((2 * P t r:ℕ):ℝ))
              = (((y.rpow (E t (r+1))) / 4)).rpow q := by rw [hqdef]
          rw [hcong] at hcor
          exact hcor
  -- ====================================================================
  -- Density identities.
  -- ====================================================================
  -- (S2 rearranged) E t (r+1) * (ρ-1)/ρ = E t r  for 1 ≤ t.
  have hS2 : ∀ t r : ℕ, 1 ≤ t → E t (r+1) * ((ρ-1)/ρ) = E t r := by
    intro t r ht
    have ht0 : t ≠ 0 := by omega
    rw [hE_nz t (r+1) ht0, hE_nz t r ht0]
    simp only [rpf]
    rw [mul_assoc]
    nth_rewrite 2 [show ((ρ-1)/ρ) = ((ρ-1)/ρ)^(1:ℝ) from (Real.rpow_one _).symm]
    rw [← Real.rpow_add hqr_pos]
    congr 2
    push_cast; ring
  -- First-branch density: (y^{E t(r+1)})^{1/(1+τ)} = y^{E t r}  for 1 ≤ t.
  have hSrow : ∀ t r : ℕ, 1 ≤ t →
      Real.rpow (Real.rpow y (E t (r+1))) (1/(1+τ)) = Real.rpow y (E t r) := by
    intro t r ht
    rw [rfold y (E t (r+1)) (1/(1+τ)) (le_of_lt hy0)]
    congr 1
    rw [hinv1pτ]
    rw [← hS2 t r ht]
  -- Second-branch density for t ≥ 2:  (y^{E t(r+1)})^{τ/(1+τ)} = y^{E (t-1) r}.
  have hScol_eq : ∀ t r : ℕ, 2 ≤ t →
      Real.rpow (Real.rpow y (E t (r+1))) (τ/(1+τ)) = Real.rpow y (E (t-1) r) := by
    intro t r ht
    rw [rfold y (E t (r+1)) (τ/(1+τ)) (le_of_lt hy0)]
    congr 1
    rw [hτ1pτ]
    -- E t (r+1) * (1/ρ) = E (t-1) r.
    have ht0 : t ≠ 0 := by omega
    have ht10 : (t-1) ≠ 0 := by omega
    rw [hE_nz t (r+1) ht0, hE_nz (t-1) r ht10]
    have htc : ((t-1:ℕ):ℝ) = (t:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ t)]; norm_num
    rw [htc]
    -- ρ^t · ((ρ-1)/ρ)^{k-(r+1)-(s-t)} · (1/ρ) = ρ^{t-1} · ((ρ-1)/ρ)^{k-r-(s-(t-1))}.
    simp only [rpf]
    rw [show (1:ℝ)/ρ = ρ ^ (-1:ℝ) by rw [Real.rpow_neg_one, one_div]]
    rw [show ρ ^ (t:ℝ) * ((ρ-1)/ρ) ^ ((k:ℝ)-((r+1:ℕ):ℝ)-((s:ℝ)-(t:ℝ))) * ρ ^ (-1:ℝ)
          = (ρ ^ (t:ℝ) * ρ ^ (-1:ℝ)) * ((ρ-1)/ρ) ^ ((k:ℝ)-((r+1:ℕ):ℝ)-((s:ℝ)-(t:ℝ))) by ring]
    rw [← Real.rpow_add hρpos]
    congr 2 <;> push_cast <;> ring
  -- For t = 1:  (y^{E 1(r+1)})^{τ/(1+τ)} ≥ y  (= y^{E 0 r}), when r ≤ k-s.
  have hScol_t1 : ∀ r : ℕ, r ≤ k - s →
      Real.rpow y (E 0 r) ≤ Real.rpow (Real.rpow y (E 1 (r+1))) (τ/(1+τ)) := by
    intro r hr
    rw [rfold y (E 1 (r+1)) (τ/(1+τ)) (le_of_lt hy0)]
    -- E 0 r = 1 ; need y^1 ≤ y^{E 1(r+1)·τ/(1+τ)} with the exponent ≤ 1.
    rw [hE_zero r]
    simp only [rpf]
    -- goal: y ^ (1:ℝ) ≤ y ^ (E 1 (r+1) * (τ/(1+τ)))
    -- exponent e := E 1(r+1)·τ/(1+τ) = ((ρ-1)/ρ)^{k-r-s} ∈ (0,1].
    have hexp_le1 : E 1 (r+1) * (τ/(1+τ)) ≤ 1 := by
      rw [hτ1pτ]
      rw [hE_nz 1 (r+1) (by norm_num)]
      simp only [rpf]
      rw [show (1:ℝ)/ρ = ρ ^ (-1:ℝ) by
            rw [Real.rpow_neg (le_of_lt hρpos), Real.rpow_one, one_div]]
      rw [show ρ ^ ((1:ℕ):ℝ) * ((ρ-1)/ρ) ^ ((k:ℝ)-((r+1:ℕ):ℝ)-((s:ℝ)-((1:ℕ):ℝ))) * ρ ^ (-1:ℝ)
            = (ρ ^ ((1:ℕ):ℝ) * ρ ^ (-1:ℝ)) * ((ρ-1)/ρ) ^ ((k:ℝ)-((r+1:ℕ):ℝ)-((s:ℝ)-((1:ℕ):ℝ))) by ring]
      rw [← Real.rpow_add hρpos]
      rw [show ((1:ℕ):ℝ) + (-1) = 0 by push_cast; ring, Real.rpow_zero, one_mul]
      -- ((ρ-1)/ρ)^{k-r-s} ≤ 1  since base ∈ (0,1) and exponent ≥ 0.
      have hrR : (r:ℝ) ≤ (k:ℝ) - (s:ℝ) := by
        have hh : r ≤ k - s := hr
        have hsk' : s ≤ k := hsk
        have hc : ((k - s : ℕ):ℝ) = (k:ℝ) - (s:ℝ) := by
          rw [Nat.cast_sub hsk']
        have : ((r:ℕ):ℝ) ≤ ((k-s:ℕ):ℝ) := by exact_mod_cast hh
        rw [hc] at this; exact this
      apply Real.rpow_le_one (le_of_lt hqr_pos) (le_of_lt hqr_lt1)
      push_cast; linarith
    have hexp_pos : 0 < E 1 (r+1) * (τ/(1+τ)) := by
      apply mul_pos (hEpos 1 (r+1))
      rw [hτ1pτ]; positivity
    exact Real.rpow_le_rpow_of_exponent_ge hy0 hy1 hexp_le1
  -- ====================================================================
  -- E s k = ρ^s  (terminal exponent).
  -- ====================================================================
  have hEsk : E s k = Real.rpow ρ (s:ℝ) := by
    by_cases hs0 : s = 0
    · subst hs0
      rw [hE_zero k, Nat.cast_zero]
      simp only [rpf]
      rw [Real.rpow_zero]
    · rw [hE_nz s k hs0]
      simp only [rpf]
      rw [show ((k:ℝ) - (k:ℝ) - ((s:ℝ) - (s:ℝ))) = 0 by ring, Real.rpow_zero, mul_one]
  -- P s k = ⌊2^k β^s p⌋₊  (defeq via the P definition).
  have hPsk : P s k = ⌊Real.rpow 2 (k:ℝ) * Real.rpow β (s:ℝ) * (p:ℝ)⌋₊ := rfl
  -- 2^k * x  (defeq).
  have h2skx : Real.rpow 2 (k:ℝ) * x = Real.rpow 2 (k:ℝ) * x := rfl
  -- ====================================================================
  -- MAIN CLAIM:  for admissible (t,r),  r + Λ₀ ≤ F t r.
  -- ====================================================================
  have hMain : ∀ r t : ℕ, t ≤ s → r ≤ k - s + t → r + Λ₀ ≤ F t r := by
    intro r
    induction r with
    | zero =>
      intro t hts hadm
      -- F t 0 ≥ Λ₀.
      rw [hFdef]; simp only
      by_cases ht0 : t = 0
      · subst ht0
        -- P 0 0 = p, 2^0 x = x, y^{E 0 0} = y.
        have hP00 : P 0 0 = p := by
          show ⌊Real.rpow 2 ((0:ℕ):ℝ) * β.rpow ((0:ℕ):ℝ) * (p:ℝ)⌋₊ = p
          rw [Nat.cast_zero]
          simp only [rpf]
          rw [Real.rpow_zero, Real.rpow_zero, one_mul, one_mul, Nat.floor_natCast]
        have hrow0 : Real.rpow 2 ((0:ℕ):ℝ) * x = x := by
          rw [Nat.cast_zero]
          simp only [rpf]
          rw [Real.rpow_zero, one_mul]
        have hcol0 : Real.rpow y (E 0 0) = y := by
          rw [hE_zero 0, rpf, Real.rpow_one]
        rw [hP00, hrow0, hcol0, Nat.zero_add]
      · -- 1 ≤ t.  P t 0 ≥ p, E t 0 ≤ 1.
        have ht1 : 1 ≤ t := by omega
        have hPt0 : p ≤ P t 0 := by
          have h := hP_ge t 0
          rw [pow_zero, one_mul] at h
          exact h
        have hcol_ge : y ≤ Real.rpow y (E t 0) := by
          have hge : y ^ (1:ℝ) ≤ y ^ (E t 0) :=
            Real.rpow_le_rpow_of_exponent_ge hy0 hy1 (hE0 t ht1 hts)
          rw [Real.rpow_one] at hge
          rw [rpf y (E t 0)]; exact hge
        have hrow0 : Real.rpow 2 ((0:ℕ):ℝ) * x = x := by
          rw [Nat.cast_zero]
          simp only [rpf]
          rw [Real.rpow_zero, one_mul]
        rw [Nat.zero_add]
        calc Λ₀ = Lambda M p x y := hΛ₀def
          _ ≤ Lambda M (P t 0) x (Real.rpow y (E t 0)) := by
                refine le_trans (lambda_p_mono M p (P t 0) hp hPt0 x y hx0
                  hxle1 hy0 hy1) ?_
                exact lambda_y_mono M (P t 0) (hP_pos t 0) x y (Real.rpow y (E t 0))
                  hx0 hxle1 hy0 hcol_ge (hyEle1 t 0)
          _ = Lambda M (P t 0) (Real.rpow 2 ((0:ℕ):ℝ) * x) (Real.rpow y (E t 0)) := by
                rw [hrow0]
    | succ r ih =>
      intro t hts hadm
      -- (t,r) admissible, r ≤ k-1, 2^r x ≤ 1/2.
      have hadm_r : r ≤ k - s + t := by omega
      have hrk1 : (r:ℝ) ≤ (k:ℝ) - 1 := by
        have : r + 1 ≤ k := by omega
        have : (r:ℝ) + 1 ≤ (k:ℝ) := by exact_mod_cast this
        linarith
      have h2rx_half : Real.rpow 2 (r:ℝ) * x ≤ 1/2 := h2rxle r hrk1
      have h2rx_pos : 0 < Real.rpow 2 (r:ℝ) * x := h2rxpos r
      -- 2 * (2^r x) = 2^{r+1} x.
      have h2double : (2:ℝ) * (Real.rpow 2 (r:ℝ) * x) = Real.rpow 2 ((r+1:ℕ):ℝ) * x := by
        push_cast
        rw [rp2, rp2, Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]; ring
      -- side condition for the ladder at this grid point.
      have hsidetr := hside t r hts (by omega)
      by_cases ht0 : t = 0
      · -- ===== Case t = 0: row ladder (A.3). =====
        subst ht0
        -- E 0 (r+1) = 1, E 0 r = 1.
        have hE0r1 : E 0 (r+1) = 1 := hE_zero (r+1)
        have hE0r : E 0 r = 1 := hE_zero r
        -- A.3 with p_ladder = P 0 r, δ = 0.
        have hrow := lemma_A3_row_ladder_step M (P 0 r) (hP_pos 0 r) 0 (by norm_num)
          (Real.rpow 2 (r:ℝ) * x) y
          ⟨h2rx_pos, h2rx_half, hy0, hy1⟩
          (by
            -- side: DSet(bracket M (2*P 0 r) (2*(2^r x)) (y/4)) ≥ 1.
            have := hsidetr
            rw [hE0r1, rpf y 1, Real.rpow_one] at this
            rw [h2double]; exact this)
        -- hrow : Lambda M (2*P 0 r + 0) (2*(2^r x)) y ≥ 1 + Lambda M (P 0 r + 0) (2^r x) y
        rw [Nat.add_zero, Nat.add_zero, h2double] at hrow
        -- bridge LHS count 2*P 0 r ≤ P 0 (r+1) via lambda_p_mono.
        have hbr := hbridgeR 0 r
        have hrowle1 : Real.rpow 2 ((r+1:ℕ):ℝ) * x ≤ 1 := by
          apply h2rxle1; push_cast
          have : (r:ℝ) + 1 ≤ (k:ℝ) := by linarith
          linarith
        have hLHS : Lambda M (2 * P 0 r) (Real.rpow 2 ((r+1:ℕ):ℝ) * x) y
            ≤ Lambda M (P 0 (r+1)) (Real.rpow 2 ((r+1:ℕ):ℝ) * x) y :=
          lambda_p_mono M (2 * P 0 r) (P 0 (r+1)) (by have := hP_pos 0 r; omega) hbr
            (Real.rpow 2 ((r+1:ℕ):ℝ) * x) y (h2rxpos ((r+1:ℕ):ℝ)) hrowle1 hy0 hy1
        -- F 0 (r+1) = Lambda M (P 0 (r+1)) (2^{r+1}x) (y^{E 0 (r+1)}) = ... y.
        rw [hFdef]; simp only
        rw [hE0r1, rpf y 1, Real.rpow_one]
        -- IH at (0,r): r + Λ₀ ≤ F 0 r = Lambda M (P 0 r) (2^r x) y.
        have hIH := ih 0 (by omega) (by omega)
        rw [hFdef] at hIH; simp only at hIH
        rw [hE0r, rpf y 1, Real.rpow_one] at hIH
        -- chain.
        have : 1 + Lambda M (P 0 r) (Real.rpow 2 (r:ℝ) * x) y
            ≤ Lambda M (P 0 (r+1)) (Real.rpow 2 ((r+1:ℕ):ℝ) * x) y :=
          le_trans hrow hLHS
        omega
      · -- ===== Cases 1 ≤ t ≤ s: column ladder (A.4). =====
        have ht1 : 1 ≤ t := by omega
        -- A.4 with p_ladder = P t r, τ.
        have hcol := lemma_A4_column_ladder_step M (P t r) (hP_pos t r)
          (Real.rpow 2 (r:ℝ) * x) (Real.rpow y (E t (r+1))) τ
          ⟨h2rx_pos, h2rx_half, hyEpos t (r+1), hyEle1 t (r+1), hτ0, hτ1⟩
          (by
            have := hsidetr
            rw [h2double]; exact this)
        -- rewrite 2*(2^r x) = 2^{r+1} x, and the two branch densities.
        rw [h2double, hSrow t r ht1] at hcol
        -- hcol : Lambda M (2*P t r) (2^{r+1}x) (y^{E t(r+1)})
        --        ≥ 1 + min (F t r) (Lambda M (⌊P t r(1-τ)⌋₊+1) (2^r x) (y^{E t(r+1)})^{τ/(1+τ)}))
        -- LHS count bridge 2*P t r ≤ P t (r+1).
        have hbr := hbridgeR t r
        have hrowle1 : Real.rpow 2 ((r+1:ℕ):ℝ) * x ≤ 1 := by
          apply h2rxle1; push_cast
          have : (r:ℝ) + 1 ≤ (k:ℝ) := by linarith
          linarith
        have hLHS : Lambda M (2 * P t r) (Real.rpow 2 ((r+1:ℕ):ℝ) * x) (Real.rpow y (E t (r+1)))
            ≤ Lambda M (P t (r+1)) (Real.rpow 2 ((r+1:ℕ):ℝ) * x) (Real.rpow y (E t (r+1))) :=
          lambda_p_mono M (2 * P t r) (P t (r+1)) (by have := hP_pos t r; omega) hbr
            (Real.rpow 2 ((r+1:ℕ):ℝ) * x) (Real.rpow y (E t (r+1))) (h2rxpos ((r+1:ℕ):ℝ)) hrowle1
            (hyEpos t (r+1)) (hyEle1 t (r+1))
        -- F t (r+1) form.
        rw [hFdef]; simp only
        -- IH at (t,r): r+Λ₀ ≤ F t r.
        have hIHt := ih t hts hadm_r
        rw [hFdef] at hIHt; simp only at hIHt
        -- second branch ≥ F (t-1) r, and F (t-1) r ≥ r + Λ₀.
        have hbridge2 : P (t-1) r ≤ ⌊(P t r : ℝ) * (1 - τ)⌋₊ + 1 := hbridgeC t r ht1
        -- second-branch density d2 := (y^{E t(r+1)})^{τ/(1+τ)}.
        set d2 := Real.rpow (Real.rpow y (E t (r+1))) (τ/(1+τ)) with hd2def
        have hd2pos : 0 < d2 := by rw [hd2def]; exact Real.rpow_pos_of_pos (hyEpos t (r+1)) _
        have hd2le1 : d2 ≤ 1 := by
          rw [hd2def]
          apply Real.rpow_le_one (le_of_lt (hyEpos t (r+1))) (hyEle1 t (r+1))
          rw [hτ1pτ]; positivity
        -- the second-branch Lambda value.
        set Lsec := Lambda M (⌊(P t r : ℝ) * (1 - τ)⌋₊ + 1) (Real.rpow 2 (r:ℝ) * x) d2 with hLsecdef
        have hsec_ge : r + Λ₀ ≤ Lsec := by
          by_cases ht2 : 2 ≤ t
          · -- t ≥ 2: d2 = y^{E(t-1)r}, second branch ≥ F(t-1)r ≥ r+Λ₀.
            have hdeq : d2 = Real.rpow y (E (t-1) r) := by rw [hd2def, hScol_eq t r ht2]
            have hIHt1 := ih (t-1) (by omega) (by omega)
            rw [hFdef] at hIHt1; simp only at hIHt1
            -- Lsec ≥ Lambda M (P(t-1)r) (2^r x) (y^{E(t-1)r}) = F(t-1)r.
            have hbridgemono : Lambda M (P (t-1) r) (Real.rpow 2 (r:ℝ) * x) (Real.rpow y (E (t-1) r))
                ≤ Lsec := by
              rw [hLsecdef, hdeq]
              exact lambda_p_mono M (P (t-1) r) (⌊(P t r : ℝ) * (1 - τ)⌋₊ + 1)
                (hP_pos (t-1) r) hbridge2 (Real.rpow 2 (r:ℝ) * x) (Real.rpow y (E (t-1) r))
                h2rx_pos (le_trans h2rx_half (by norm_num)) (hyEpos (t-1) r) (hyEle1 (t-1) r)
            omega
          · -- t = 1: d2 ≥ y = y^{E 0 r}, second branch ≥ F 0 r ≥ r+Λ₀.
            have ht_eq : t = 1 := by omega
            subst ht_eq
            have hE0r : E 0 r = 1 := hE_zero r
            have hdge : y ≤ d2 := by
              have h := hScol_t1 r (by omega)
              rw [hE0r, rpf y 1, Real.rpow_one] at h
              rw [hd2def]; exact h
            have hIH0 := ih 0 (by omega) (by omega)
            rw [hFdef] at hIH0; simp only at hIH0
            rw [hE0r, rpf y 1, Real.rpow_one] at hIH0
            -- Lsec ≥ Lambda M (P 0 r) (2^r x) y = F 0 r.
            have hbridgemono : Lambda M (P 0 r) (Real.rpow 2 (r:ℝ) * x) y ≤ Lsec := by
              rw [hLsecdef]
              refine le_trans (lambda_p_mono M (P 0 r) (⌊(P 1 r : ℝ) * (1 - τ)⌋₊ + 1)
                (hP_pos 0 r) hbridge2 (Real.rpow 2 (r:ℝ) * x) y h2rx_pos
                (le_trans h2rx_half (by norm_num)) hy0 hy1) ?_
              exact lambda_y_mono M (⌊(P 1 r : ℝ) * (1 - τ)⌋₊ + 1)
                (by have := hP_pos 1 r; omega) (Real.rpow 2 (r:ℝ) * x) y d2
                h2rx_pos (le_trans h2rx_half (by norm_num)) hy0 hdge hd2le1
            omega
        -- combine: hcol gives ≥ 1 + min (F t r) Lsec; both ≥ r+Λ₀.
        have hmin_ge : r + Λ₀ ≤ min (Lambda M (P t r) (Real.rpow 2 (r:ℝ) * x) (Real.rpow y (E t r))) Lsec := by
          apply le_min hIHt hsec_ge
        omega
  -- ====================================================================
  -- Conclusion.
  -- ====================================================================
  have hsk_adm : k ≤ k - s + s := by omega
  have hclaim := hMain k s (le_refl s) hsk_adm
  -- F s k = Lambda M (⌊2^k β^s p⌋₊) (2^k x) (y^{ρ^s}).
  have hFskval : F s k = Lambda M (⌊Real.rpow 2 (k:ℝ) * Real.rpow β (s:ℝ) * (p:ℝ)⌋₊)
      (Real.rpow 2 (k:ℝ) * x) (Real.rpow y (Real.rpow ρ (s:ℝ))) := by
    rw [hFdef]; simp only
    rw [hEsk]
  rw [hFskval] at hclaim
  refine ⟨?_, ?_⟩
  · -- 4.8a
    rw [hΛ₀def] at hclaim
    omega
  · -- 4.8b:  DSet ≥ Lambda  (via the j=0 term of Lambda).
    have hDSet_ge : Lambda M (⌊Real.rpow 2 (k:ℝ) * Real.rpow β (s:ℝ) * (p:ℝ)⌋₊)
        (Real.rpow 2 (k:ℝ) * x) (Real.rpow y (Real.rpow ρ (s:ℝ)))
        ≤ DSet (bracket M (⌊Real.rpow 2 (k:ℝ) * Real.rpow β (s:ℝ) * (p:ℝ)⌋₊)
          (Real.rpow 2 (k:ℝ) * x) (Real.rpow y (Real.rpow ρ (s:ℝ)))) := by
      unfold Lambda
      exact le_trans (min_le_left _ _) (le_refl _)
    rw [hΛ₀def] at hclaim
    omega

/-- **Corollary 4.9 (Iterated partition seed).** -/
theorem cor_4_9_iterated_partition_seed
    (ρ : ℝ) (hρ : 2 < ρ)
    (β : ℝ) (hβ : β = (ρ - 1) / (ρ - 2))
    (M : BoolMat) (s k : ℕ) (hsk : s ≤ k)
    (p : ℕ) (hp : 1 ≤ p)
    (x y : ℝ)
    (hx0 : 0 < x) (hxk : x ≤ Real.rpow 2 (-(k : ℝ)))
    (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hseed : DSet (bracket M p x (y / 4)) ≥ 1)
    (hrung : Real.rpow (ρ - 1) (k : ℝ) ≤ Real.rpow ρ ((k : ℝ) - (s : ℝ)))
    (H : ℝ)
    (hH0 : (DSet (bracket M p x y) : ℝ) ≥ H)
    (hH1 : (DSet (bracket M p x (y / 2)) : ℝ) ≥ H - 1)
    (hH2 : (DSet (bracket M p x (y / 4)) : ℝ) ≥ H - 2) :
    (DSet (bracket M
        (⌊Real.rpow 2 (k : ℝ) * Real.rpow β (s : ℝ) * (p : ℝ)⌋₊)
        (Real.rpow 2 (k : ℝ) * x)
        (Real.rpow y (Real.rpow ρ (s : ℝ)))) : ℝ)
      ≥ (k : ℝ) + H := by
  have hLam : (H : ℝ) ≤ (Lambda M p x y : ℝ) := by
    unfold Lambda
    push_cast
    refine le_min hH0 (le_min ?_ ?_)
    · linarith
    · linarith
  have h48 := (lemma_4_8_iterated_partition ρ hρ β hβ M s k hsk p hp x y
      hx0 hxk hy0 hy1 hseed hrung).2
  have h48' : ((k : ℝ) + (Lambda M p x y : ℝ))
      ≤ (DSet (bracket M
        (⌊Real.rpow 2 (k : ℝ) * Real.rpow β (s : ℝ) * (p : ℝ)⌋₊)
        (Real.rpow 2 (k : ℝ) * x)
        (Real.rpow y (Real.rpow ρ (s : ℝ)))) : ℝ) := by
    have hcast : ((k + Lambda M p x y : ℕ) : ℝ)
        ≤ (DSet (bracket M
          (⌊Real.rpow 2 (k : ℝ) * Real.rpow β (s : ℝ) * (p : ℝ)⌋₊)
          (Real.rpow 2 (k : ℝ) * x)
          (Real.rpow y (Real.rpow ρ (s : ℝ)))) : ℝ) := by exact_mod_cast h48
    push_cast at hcast
    linarith
  linarith

/-- **Lemma 4.10 (Seed collapse).** -/
theorem lemma_4_10_seed_collapse
    (M : BoolMat) (a : ℝ) (ha : 3 / 8 < a)
    (k : ℕ) (hk : 5 ≤ k)
    (hseed : DSet (bracket M 1
        (Real.rpow 2 (-(k : ℝ) - a)) (Real.rpow 2 (-3))) ≥ 1) :
    Lambda M 6 (Real.rpow 2 ((3 : ℝ) - (k : ℝ) - a)) (Real.rpow 2 (-1))
      ≥ 3 + Lambda M 1 (Real.rpow 2 (-(k : ℝ) - a)) (Real.rpow 2 (-3 / 8)) := by
  have hkR : (5:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  -- Abbreviations for the row parameters and the densities used in the chain.
  set x0 := Real.rpow 2 (-(k:ℝ) - a) with hx0def       -- 2^{-k-a}
  set x1 := Real.rpow 2 (1 - (k:ℝ) - a) with hx1def     -- 2^{1-k-a}
  set x2 := Real.rpow 2 (2 - (k:ℝ) - a) with hx2def     -- 2^{2-k-a}
  set x3 := Real.rpow 2 (3 - (k:ℝ) - a) with hx3def     -- 2^{3-k-a}
  -- Positivity and range facts for the row parameters.
  have hx0pos : (0:ℝ) < x0 := by rw [hx0def, rp2]; positivity
  have hx1pos : (0:ℝ) < x1 := by rw [hx1def, rp2]; positivity
  have hx2pos : (0:ℝ) < x2 := by rw [hx2def, rp2]; positivity
  have hx3pos : (0:ℝ) < x3 := by rw [hx3def, rp2]; positivity
  -- x ≤ 1/2 facts (exponents ≤ -1 since k ≥ 5, a > 3/8).
  have hhalf : (1:ℝ)/2 = Real.rpow 2 (-1) := by
    rw [rp2, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_one]; norm_num
  have hx0half : x0 ≤ 1/2 := by
    rw [hx0def, hhalf, rp2, rp2]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hx1half : x1 ≤ 1/2 := by
    rw [hx1def, hhalf, rp2, rp2]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hx2half : x2 ≤ 1/2 := by
    rw [hx2def, hhalf, rp2, rp2]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  -- x ≤ 1 facts.
  have hx0le1 : x0 ≤ 1 := le_trans hx0half (by norm_num)
  have hx1le1 : x1 ≤ 1 := le_trans hx1half (by norm_num)
  have hx2le1 : x2 ≤ 1 := le_trans hx2half (by norm_num)
  have hx3le1 : x3 ≤ 1 := by
    rw [hx3def, rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  -- Row-doubling identities: 2 * 2^e = 2^{e+1}.
  have hdbl : ∀ e : ℝ, (2:ℝ) * Real.rpow 2 e = Real.rpow 2 (e + 1) := by
    intro e
    rw [rp2, rp2, Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]; ring
  have h2x2 : (2:ℝ) * x2 = x3 := by
    rw [hx2def, hx3def, hdbl]; congr 1; ring
  have h2x1 : (2:ℝ) * x1 = x2 := by
    rw [hx1def, hx2def, hdbl]; congr 1; ring
  have h2x0 : (2:ℝ) * x0 = x1 := by
    rw [hx0def, hx1def, hdbl]; congr 1; ring
  -- Density abbreviations.
  set d1 := Real.rpow 2 (-1) with hd1def       -- 2^{-1}
  set d34 := Real.rpow 2 (-3/4) with hd34def    -- 2^{-3/4}
  set d14 := Real.rpow 2 (-1/4) with hd14def    -- 2^{-1/4}
  set d38 := Real.rpow 2 (-3/8) with hd38def    -- 2^{-3/8}
  -- Density positivity / ≤ 1.
  have hd1pos : (0:ℝ) < d1 := by rw [hd1def, rp2]; positivity
  have hd34pos : (0:ℝ) < d34 := by rw [hd34def, rp2]; positivity
  have hd14pos : (0:ℝ) < d14 := by rw [hd14def, rp2]; positivity
  have hd38pos : (0:ℝ) < d38 := by rw [hd38def, rp2]; positivity
  have hd1le1 : d1 ≤ 1 := by
    rw [hd1def, rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hd34le1 : d34 ≤ 1 := by
    rw [hd34def, rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hd14le1 : d14 ≤ 1 := by
    rw [hd14def, rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hd38le1 : d38 ≤ 1 := by
    rw [hd38def, rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hd3438 : d34 ≤ d14 := by
    rw [hd34def, hd14def, rp2, rp2]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  -- d1 / 4 = 2^{-3}.
  have hd1over4 : d1 / 4 = Real.rpow 2 (-3) := by
    rw [hd1def, rp2, rp2, show (-3:ℝ) = (-1) + (-2) by norm_num,
        Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    rw [show (2:ℝ)^(-2:ℝ) = 1/4 by
      rw [show (-2:ℝ) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg (by norm_num),
          Real.rpow_natCast]; norm_num]
    ring
  -- d34 / 4 = 2^{-11/4}.
  have hd34over4 : d34 / 4 = Real.rpow 2 (-11/4) := by
    rw [hd34def, rp2, rp2, show (-11/4:ℝ) = (-3/4) + (-2) by norm_num,
        Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    rw [show (2:ℝ)^(-2:ℝ) = 1/4 by
      rw [show (-2:ℝ) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg (by norm_num),
          Real.rpow_natCast]; norm_num]
    ring
  -- The seed: 1 ≤ DSet(bracket M 1 x0 2^{-3}).
  have hd23pos : (0:ℝ) < Real.rpow 2 (-3) := by rw [rp2]; positivity
  have hd23le1 : Real.rpow 2 (-3) ≤ 1 := by
    rw [rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hd114pos : (0:ℝ) < Real.rpow 2 (-11/4) := by rw [rp2]; positivity
  have hd114le1 : Real.rpow 2 (-11/4) ≤ 1 := by
    rw [rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  -- Row-parameter orderings (smaller exponent ⇒ smaller value).
  have hx0x1 : x0 ≤ x1 := by
    rw [hx0def, hx1def, rp2, rp2]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hx1x2 : x1 ≤ x2 := by
    rw [hx1def, hx2def, rp2, rp2]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hx2x3 : x2 ≤ x3 := by
    rw [hx2def, hx3def, rp2, rp2]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  -- 2^{-3} ≤ 2^{-11/4}.
  have h23le114 : Real.rpow 2 (-3) ≤ Real.rpow 2 (-11/4) := by
    rw [rp2, rp2]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  -- (F1) DSet(bracket M 6 x3 (2^{-3})) ≥ 1.
  have hF1 : DSet (bracket M 6 x3 (Real.rpow 2 (-3))) ≥ 1 := by
    calc (1:ℕ) ≤ DSet (bracket M 1 x0 (Real.rpow 2 (-3))) := hseed
      _ ≤ DSet (bracket M 6 x3 (Real.rpow 2 (-3))) :=
          monotonicity M 1 6 x0 x3 (Real.rpow 2 (-3)) (Real.rpow 2 (-3))
            (le_refl 1) (by norm_num) hx0pos (le_trans hx0x1 (le_trans hx1x2 hx2x3))
            hx3le1 hd23pos (le_refl _) hd23le1
  -- (F2) DSet(bracket M 2 x2 (2^{-11/4})) ≥ 1.
  have hF2 : DSet (bracket M 2 x2 (Real.rpow 2 (-11/4))) ≥ 1 := by
    calc (1:ℕ) ≤ DSet (bracket M 1 x0 (Real.rpow 2 (-3))) := hseed
      _ ≤ DSet (bracket M 2 x2 (Real.rpow 2 (-11/4))) :=
          monotonicity M 1 2 x0 x2 (Real.rpow 2 (-3)) (Real.rpow 2 (-11/4))
            (le_refl 1) (by norm_num) hx0pos (le_trans hx0x1 hx1x2) hx2le1
            hd23pos h23le114 hd114le1
  -- (F3) DSet(bracket M 2 x1 (2^{-11/4})) ≥ 1.
  have hF3 : DSet (bracket M 2 x1 (Real.rpow 2 (-11/4))) ≥ 1 := by
    calc (1:ℕ) ≤ DSet (bracket M 1 x0 (Real.rpow 2 (-3))) := hseed
      _ ≤ DSet (bracket M 2 x1 (Real.rpow 2 (-11/4))) :=
          monotonicity M 1 2 x0 x1 (Real.rpow 2 (-3)) (Real.rpow 2 (-11/4))
            (le_refl 1) (by norm_num) hx0pos hx0x1 hx1le1
            hd23pos h23le114 hd114le1
  -- ===== Step 1: column ladder with τ = 1/3, p = 3, x = x2, y = d1. =====
  -- Side condition: DSet(bracket M (2*3) (2*x2) (d1/4)) ≥ 1.
  have hside1 : DSet (bracket M (2*3) (2*x2) (d1/4)) ≥ 1 := by
    rw [show (2*3 : ℕ) = 6 from rfl, h2x2, hd1over4]; exact hF1
  have hcol1 := lemma_A4_column_ladder_step M 3 (by norm_num) x2 d1 (1/3)
    ⟨hx2pos, hx2half, hd1pos, hd1le1, by norm_num, by norm_num⟩ hside1
  -- Compute the col-step output densities.
  have hu1 : Real.rpow d1 (1/(1+1/3)) = d34 := by
    rw [hd1def, hd34def, rpf, rpf, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hv1 : Real.rpow d1 ((1/3)/(1+1/3)) = d14 := by
    rw [hd1def, hd14def, rpf, rpf, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hidx1 : ⌊((3:ℕ):ℝ)*(1-1/3)⌋₊ + 1 = 3 := by norm_num
  rw [show (2*3 : ℕ) = 6 from rfl, h2x2, hu1, hv1, hidx1] at hcol1
  -- hcol1 : Lambda M 6 x3 d1 ≥ 1 + min (Lambda M 3 x2 d34) (Lambda M 3 x2 d14)
  -- ===== Step 2: resolve the min via Λ-y-monotonicity (d34 ≤ d14). =====
  have hmin2 : min (Lambda M 3 x2 d34) (Lambda M 3 x2 d14) = Lambda M 3 x2 d34 := by
    apply min_eq_left
    exact lambda_y_mono M 3 (by norm_num) x2 d34 d14 hx2pos hx2le1 hd34pos hd3438 hd14le1
  rw [hmin2] at hcol1
  -- hcol1 : Lambda M 6 x3 d1 ≥ 1 + Lambda M 3 x2 d34
  -- ===== Step 3: row ladder with p = 1, δ = 1, x = x1, y = d34. =====
  have hside3 : DSet (bracket M (2*1) (2*x1) (d34/4)) ≥ 1 := by
    rw [show (2*1 : ℕ) = 2 from rfl, h2x1, hd34over4]; exact hF2
  have hrow3 := lemma_A3_row_ladder_step M 1 (by norm_num) 1 (by norm_num) x1 d34
    ⟨hx1pos, hx1half, hd34pos, hd34le1⟩ hside3
  rw [show (2*1+1 : ℕ) = 3 from rfl, show (1+1 : ℕ) = 2 from rfl, h2x1] at hrow3
  -- hrow3 : Lambda M 3 x2 d34 ≥ 1 + Lambda M 2 x1 d34
  -- ===== Step 4: column ladder with τ = 1, p = 1, x = x0, y = d34. =====
  have hside4 : DSet (bracket M (2*1) (2*x0) (d34/4)) ≥ 1 := by
    rw [show (2*1 : ℕ) = 2 from rfl, h2x0, hd34over4]; exact hF3
  have hcol4 := lemma_A4_column_ladder_step M 1 (by norm_num) x0 d34 (1)
    ⟨hx0pos, hx0half, hd34pos, hd34le1, by norm_num, by norm_num⟩ hside4
  have hu4 : Real.rpow d34 (1/(1+1)) = d38 := by
    rw [hd34def, hd38def, rpf, rpf, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hidx4 : ⌊((1:ℕ):ℝ)*(1-1)⌋₊ + 1 = 1 := by norm_num
  rw [show (2*1 : ℕ) = 2 from rfl, h2x0, hu4, hidx4] at hcol4
  -- hcol4 : Lambda M 2 x1 d34 ≥ 1 + min (Lambda M 1 x0 d38) (Lambda M 1 x0 d38)
  rw [min_self] at hcol4
  -- hcol4 : Lambda M 2 x1 d34 ≥ 1 + Lambda M 1 x0 d38
  -- ===== Assemble the chain. =====
  -- Goal: Lambda M 6 x3 d1 ≥ 3 + Lambda M 1 x0 d38.
  omega

/-- **Theorem 4.11 (Induction step in `k`).** -/
theorem thm_4_11_induction_step
    (a : ℝ) (ha : 3 / 8 < a)
    (k : ℕ) (hk : 5 ≤ k)
    (hside : Real.sqrt ((k : ℝ) + a) - 1
        ≤ Real.rpow ((k : ℝ) + a) (1 / 2 - 1 / ((k : ℝ) - 3)))
    (M : BoolMat)
    (hdiv : ∃ t : ℕ, (M.m : ℝ) * Real.rpow 2 (-a) = (t : ℝ))
    (hseed : DSet (bracket M 1
        (Real.rpow 2 (-(k : ℝ) - a)) (Real.rpow 2 (-3))) ≥ 1) :
    let Q_k : ℕ := ⌈Real.rpow 2 (k : ℝ)
        * ((3 * Real.rpow 2 a - 3) / (Real.rpow 2 (13 / 8) * Real.rpow 2 a - 4))
        * ((Real.sqrt ((k : ℝ) + a) - 1) / (Real.sqrt ((k : ℝ) + a) - 2)) ^ 2⌉₊
    DSet (bracket (interlace M Q_k) 1
        (Real.rpow 2 (-3 / 8)) (Real.rpow 2 (-(k : ℝ) - a)))
      ≥ k + Lambda M 1 (Real.rpow 2 (-(k : ℝ) - a)) (Real.rpow 2 (-3 / 8)) := by
  intro Q_k
  -- Basic numerical facts.
  have hkR : (5:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hka0 : (0:ℝ) ≤ (k:ℝ) + a := by linarith
  have hka4 : (4:ℝ) < (k:ℝ) + a := by linarith
  set ρ := Real.sqrt ((k:ℝ)+a) with hρdef
  have hρ2 : (2:ℝ) < ρ := by
    rw [hρdef]
    have : Real.sqrt 4 < Real.sqrt ((k:ℝ)+a) := Real.sqrt_lt_sqrt (by norm_num) hka4
    rwa [show Real.sqrt 4 = 2 by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
  have hρsq : ρ^2 = (k:ℝ)+a := by rw [hρdef]; exact Real.sq_sqrt hka0
  set β := (ρ - 1) / (ρ - 2) with hβdef
  -- α = 2^{a-3/8}, x = 2^{-a}, y = 2^{-k-a}.
  set α := Real.rpow 2 (a - 3/8) with hαdef
  set x := Real.rpow 2 (-a) with hxdef
  set y := Real.rpow 2 (-(k:ℝ)-a) with hydef
  -- Positivity / size facts for α, x, y.
  have hαx_id : α * x = Real.rpow 2 (-3/8) := by
    rw [hαdef, hxdef]; exact rowdens_id a
  have hα1 : (1:ℝ) < α := by
    rw [hαdef, rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hx0 : (0:ℝ) < x := by rw [hxdef, rp2]; positivity
  have hx1 : x < 1 := by
    rw [hxdef, rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hαx0 : (0:ℝ) < α * x := by rw [hαx_id, rp2]; positivity
  have hαx1 : α * x ≤ 1 := by
    rw [hαx_id, rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hy0 : (0:ℝ) < y := by rw [hydef, rp2]; positivity
  have hy1 : y ≤ 1 := by
    rw [hydef, rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  -- The ceiling argument of Q_k (a positive real); Q_k ≥ it.
  set C : ℝ := Real.rpow 2 (k : ℝ)
      * ((3 * Real.rpow 2 a - 3) / (Real.rpow 2 (13 / 8) * Real.rpow 2 a - 4))
      * ((Real.sqrt ((k : ℝ) + a) - 1) / (Real.sqrt ((k : ℝ) + a) - 2)) ^ 2 with hCdef
  -- The multiplier appearing in extended_balancing's p*: (α-1)·x/(1-x).
  have hmul_pos : (0:ℝ) < (α - 1) * x / (1 - x) := by
    apply div_pos
    · apply mul_pos (by linarith) hx0
    · linarith
  -- Q_k ≥ C  (ceiling ≥ argument; argument is ≥ 0 so the ℕ-ceiling matches).
  have hCnonneg : (0:ℝ) ≤ C := by
    rw [hCdef]
    have h1 : (0:ℝ) ≤ Real.rpow 2 (k:ℝ) := by rw [rp2]; positivity
    have h2 : (0:ℝ) ≤ (3 * Real.rpow 2 a - 3) / (Real.rpow 2 (13/8) * Real.rpow 2 a - 4) := by
      apply div_nonneg
      · have : (1:ℝ) ≤ Real.rpow 2 a := by
          rw [rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        linarith
      · have hd : (4:ℝ) < Real.rpow 2 (13/8) * Real.rpow 2 a := by
          rw [rp2, rp2, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
          rw [show (4:ℝ) = (2:ℝ)^(2:ℝ) by rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num]
          exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
        linarith
    positivity
  have hQk_ge_C : C ≤ (Q_k : ℝ) := by
    show C ≤ ((⌈C⌉₊ : ℕ) : ℝ)
    exact Nat.le_ceil C
  -- Real inequality: Q_k·(α-1)·x/(1-x) ≥ 6·2^{k-3}·((ρ-1)/(ρ-2))^2.
  set p'real : ℝ := 6 * Real.rpow 2 ((k:ℝ)-3) * ((ρ-1)/(ρ-2))^2 with hp'realdef
  have hkey : p'real ≤ (Q_k : ℝ) * (α - 1) * x / (1 - x) := by
    have hstep : (Q_k : ℝ) * (α - 1) * x / (1 - x)
        = (Q_k : ℝ) * ((α - 1) * x / (1 - x)) := by ring
    rw [hstep]
    have hCmul : C * ((α - 1) * x / (1 - x)) = p'real := by
      rw [hCdef, hp'realdef, hαdef, hxdef]
      have hqm := qk_multiplier a ha
      -- regroup: 2^k · [frac1 · frac2] · ((ρ-1)/(ρ-2))^2
      rw [show Real.rpow 2 (k:ℝ)
            * ((3 * Real.rpow 2 a - 3) / (Real.rpow 2 (13/8) * Real.rpow 2 a - 4))
            * ((Real.sqrt ((k:ℝ)+a) - 1) / (Real.sqrt ((k:ℝ)+a) - 2)) ^ 2
            * ((Real.rpow 2 (a - 3/8) - 1) * Real.rpow 2 (-a) / (1 - Real.rpow 2 (-a)))
          = Real.rpow 2 (k:ℝ)
            * (((3 * Real.rpow 2 a - 3) / (Real.rpow 2 (13/8) * Real.rpow 2 a - 4))
               * ((Real.rpow 2 (a - 3/8) - 1) * Real.rpow 2 (-a) / (1 - Real.rpow 2 (-a))))
            * ((Real.sqrt ((k:ℝ)+a) - 1) / (Real.sqrt ((k:ℝ)+a) - 2)) ^ 2 by ring]
      rw [hqm]
      -- now: 2^k · (3/4) · ((ρ-1)/(ρ-2))^2 = 6·2^{k-3}·((ρ-1)/(ρ-2))^2
      have h2 : Real.rpow 2 (k:ℝ) * (3/4) = 6 * Real.rpow 2 ((k:ℝ)-3) := by
        rw [rp2, rp2, show (6:ℝ) = (2:ℝ)^(3:ℝ) * (3/4) by
          rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num]
        rw [show (2:ℝ)^(3:ℝ) * (3/4) * (2:ℝ)^((k:ℝ)-3)
              = (2:ℝ)^(3:ℝ) * (2:ℝ)^((k:ℝ)-3) * (3/4) by ring,
            ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        ring_nf
      rw [show Real.rpow 2 (k:ℝ) * (3/4)
            * ((Real.sqrt ((k:ℝ)+a) - 1) / (Real.sqrt ((k:ℝ)+a) - 2)) ^ 2
          = (Real.rpow 2 (k:ℝ) * (3/4))
            * ((Real.sqrt ((k:ℝ)+a) - 1) / (Real.sqrt ((k:ℝ)+a) - 2)) ^ 2 by ring]
      rw [h2]
    calc p'real = C * ((α - 1) * x / (1 - x)) := hCmul.symm
      _ ≤ (Q_k : ℝ) * ((α - 1) * x / (1 - x)) := by
            apply mul_le_mul_of_nonneg_right hQk_ge_C (le_of_lt hmul_pos)
  -- p'real ≥ 1 (in fact ≥ 24).
  have hρ12 : (1:ℝ) < (ρ - 1) / (ρ - 2) := by
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < ρ - 2)]; linarith
  have hp'real_ge : (1:ℝ) ≤ p'real := by
    rw [hp'realdef]
    have hrpow : (4:ℝ) ≤ Real.rpow 2 ((k:ℝ)-3) := by
      rw [rp2, show (4:ℝ) = (2:ℝ)^(2:ℝ) by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hsq : (1:ℝ) ≤ ((ρ-1)/(ρ-2))^2 := by nlinarith [hρ12]
    nlinarith [hrpow, hsq]
  -- The p* floor is ≥ 1.
  have hpstar1 : ⌊(Q_k : ℝ) * (α - 1) * x / (1 - x)⌋₊ ≥ 1 := by
    rw [ge_iff_le, Nat.le_floor_iff (by linarith [hkey, hp'real_ge])]
    push_cast; linarith [hkey, hp'real_ge]
  -- Step 2: Extended Balancing Lemma (4.5).
  have hEB := extended_balancing M Q_k α x y hα1 hx0 hx1 hαx0 hαx1 hy0 hy1 hdiv hpstar1
  -- hEB : DSet (bracket (interlace M Q_k) 1 (α*x) y) ≥ DSet (bracket M ⌊...⌋₊ x y)
  set P_k : ℕ := ⌊(Q_k : ℝ) * (α - 1) * x / (1 - x)⌋₊ with hPkdef
  -- Rewrite the LHS row density α*x = 2^{-3/8}.
  rw [hαx_id] at hEB
  -- Step 2b: P_k ≥ p' := ⌊6·2^{k-3}·((ρ-1)/(ρ-2))^2⌋₊.
  set p' : ℕ := ⌊p'real⌋₊ with hp'def
  have hPk_ge_p' : p' ≤ P_k := by
    rw [hp'def, hPkdef]
    apply Nat.floor_le_floor
    have : (Q_k : ℝ) * (α - 1) * x / (1 - x) = (Q_k : ℝ) * ((α - 1) * x / (1 - x)) := by ring
    linarith [hkey]
  have hp'1 : 1 ≤ p' := by
    rw [hp'def, Nat.one_le_floor_iff]; exact hp'real_ge
  -- It suffices to bound DSet (bracket M P_k x y).
  refine le_trans ?_ hEB
  -- Step 2b: monotonicity P_k ≥ p'.
  have hmono : DSet (bracket M p' x y) ≤ DSet (bracket M P_k x y) :=
    monotonicity M p' P_k x x y y hp'1 hPk_ge_p' hx0 (le_refl x) (le_of_lt hx1)
      hy0 (le_refl y) hy1
  refine le_trans ?_ hmono
  -- Step 3 + 4 give DSet (bracket M p' x y) ≥ k + Lambda M 1 y (2^{-3/8}).
  -- Apply Corollary 4.9 with k̃ = k-3, s = 2, p = 6, xc = 2^{3-k-a}, yc = 2^{-1}.
  set xc : ℝ := Real.rpow 2 ((3:ℝ) - (k:ℝ) - a) with hxcdef
  set yc : ℝ := Real.rpow 2 (-1) with hycdef
  -- Side conditions for cor 4.9.
  have hxc0 : (0:ℝ) < xc := by rw [hxcdef, rp2]; positivity
  have hxck : xc ≤ Real.rpow 2 (-((k-3:ℕ):ℝ)) := by
    rw [hxcdef, rp2, rp2]
    have hk3cast : ((k-3:ℕ):ℝ) = (k:ℝ) - 3 := by
      rw [Nat.cast_sub (by omega : 3 ≤ k)]; norm_num
    rw [hk3cast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hyc0 : (0:ℝ) < yc := by rw [hycdef, rp2]; positivity
  have hyc1 : yc ≤ 1 := by
    rw [hycdef, rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  -- Seed condition: D([M]_{6, xc, yc/4}) ≥ 1.  Note yc/4 = 2^{-3}.
  have hyc4 : yc / 4 = Real.rpow 2 (-3) := by
    rw [hycdef, rp2, rp2, show (-3:ℝ) = (-1) + (-2) by norm_num,
        Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    rw [show (2:ℝ)^(-2:ℝ) = 1/4 by
      rw [show (-2:ℝ) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg (by norm_num), Real.rpow_natCast]
      norm_num]
    ring
  have hseed6 : DSet (bracket M 6 xc (yc / 4)) ≥ 1 := by
    rw [hyc4]
    -- from hseed by monotonicity: 1 ≤ D([M]_{1, y, 2^{-3}}) ≤ D([M]_{6, xc, 2^{-3}})
    have hxy : y ≤ xc := by
      rw [hydef, hxcdef, rp2, rp2]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hxc1 : xc ≤ 1 := le_trans hxck (by
      rw [rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by simp only [neg_nonpos]; positivity))
    have h23pos : (0:ℝ) < Real.rpow 2 (-3) := by rw [rp2]; positivity
    have h23le1 : Real.rpow 2 (-3) ≤ 1 := by
      rw [rp2, show (1:ℝ) = (2:ℝ)^(0:ℝ) by norm_num]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    calc (1:ℕ) ≤ DSet (bracket M 1 y (Real.rpow 2 (-3))) := hseed
      _ ≤ DSet (bracket M 6 xc (Real.rpow 2 (-3))) :=
          monotonicity M 1 6 y xc (Real.rpow 2 (-3)) (Real.rpow 2 (-3))
            (le_refl 1) (by norm_num) hy0 hxy hxc1 h23pos (le_refl _) h23le1
  -- The rung condition (step3_rung).
  have hrung6 : Real.rpow (ρ - 1) ((k-3:ℕ):ℝ)
      ≤ Real.rpow ρ (((k-3:ℕ):ℝ) - ((2:ℕ):ℝ)) := by
    rw [hρdef]; exact step3_rung a ha k hk hside
  -- H = Lambda M 6 xc yc, with the three rung bounds.
  set H : ℝ := (Lambda M 6 xc yc : ℝ) with hHdef
  have hH0 : (DSet (bracket M 6 xc yc) : ℝ) ≥ H := by
    rw [hHdef]; unfold Lambda; push_cast
    exact le_trans (min_le_left _ _) (le_refl _)
  have hH1 : (DSet (bracket M 6 xc (yc / 2)) : ℝ) ≥ H - 1 := by
    rw [hHdef]; unfold Lambda; push_cast
    have := min_le_right (DSet (bracket M 6 xc yc) : ℝ)
      (min (1 + (DSet (bracket M 6 xc (yc/2)) : ℝ)) (2 + (DSet (bracket M 6 xc (yc/4)) : ℝ)))
    have h2 := min_le_left (1 + (DSet (bracket M 6 xc (yc/2)) : ℝ))
      (2 + (DSet (bracket M 6 xc (yc/4)) : ℝ))
    have := le_trans this h2
    push_cast at this ⊢
    linarith
  have hH2 : (DSet (bracket M 6 xc (yc / 4)) : ℝ) ≥ H - 2 := by
    rw [hHdef]; unfold Lambda; push_cast
    have := min_le_right (DSet (bracket M 6 xc yc) : ℝ)
      (min (1 + (DSet (bracket M 6 xc (yc/2)) : ℝ)) (2 + (DSet (bracket M 6 xc (yc/4)) : ℝ)))
    have h2 := min_le_right (1 + (DSet (bracket M 6 xc (yc/2)) : ℝ))
      (2 + (DSet (bracket M 6 xc (yc/4)) : ℝ))
    have := le_trans this h2
    push_cast at this ⊢
    linarith
  -- Apply Corollary 4.9.
  have hcor := cor_4_9_iterated_partition_seed ρ hρ2 β hβdef M 2 (k-3) (by omega)
      6 (by norm_num) xc yc hxc0 hxck hyc0 hyc1 hseed6 hrung6 H hH0 hH1 hH2
  -- Parameter-matching: the cor 4.9 bracket equals `bracket M p' x y`.
  have hcnt : ⌊Real.rpow 2 ((k-3:ℕ):ℝ) * β.rpow ((2:ℕ):ℝ) * ((6:ℕ):ℝ)⌋₊ = p' := by
    rw [hp'def, hp'realdef, hβdef]; congr 1
    rw [show ((k-3:ℕ):ℝ) = (k:ℝ)-3 by rw [Nat.cast_sub (by omega : 3 ≤ k)]; norm_num]
    rw [show (((ρ-1)/(ρ-2)).rpow ((2:ℕ):ℝ)) = ((ρ-1)/(ρ-2))^2 by rw [rpf, Real.rpow_natCast]]
    push_cast; ring
  have hrow : Real.rpow 2 ((k-3:ℕ):ℝ) * xc = x := by
    rw [hxdef, hxcdef]
    rw [show ((k-3:ℕ):ℝ) = (k:ℝ)-3 by rw [Nat.cast_sub (by omega : 3 ≤ k)]; norm_num]
    exact step3_rowdens k a
  have hcol : yc.rpow (ρ.rpow ((2:ℕ):ℝ)) = y := by
    rw [hydef, hycdef, hρdef]; exact step3_coldens k a hka0
  rw [hcnt, hrow, hcol] at hcor
  -- hcor : ↑(DSet (bracket M p' x y)) ≥ ↑(k-3) + H
  -- Lemma 4.10 (seed collapse): H = Λ_M(6,xc,yc) ≥ 3 + Λ_M(1,y,2^{-3/8}).
  have h410 := lemma_4_10_seed_collapse M a ha k hk hseed
  rw [← hxcdef, ← hycdef, ← hydef] at h410
  -- h410 : Lambda M 6 xc yc ≥ 3 + Lambda M 1 y (Real.rpow 2 (-3/8))
  have h410R : H ≥ 3 + (Lambda M 1 y (Real.rpow 2 (-3 / 8)) : ℝ) := by
    rw [hHdef]; exact_mod_cast h410
  -- Final arithmetic: (k-3)+3 = k.
  have hk3 : ((k-3:ℕ):ℝ) + 3 = (k:ℝ) := by
    rw [Nat.cast_sub (by omega : 3 ≤ k)]; ring
  have hfinal : ((k:ℝ) + (Lambda M 1 y (Real.rpow 2 (-3 / 8)) : ℝ))
      ≤ (DSet (bracket M p' x y) : ℝ) := by
    have hkk : ((k-3:ℕ):ℝ) + H ≤ (DSet (bracket M p' x y) : ℝ) := hcor
    linarith [hkk, h410R, hk3]
  have : ((k + Lambda M 1 y (Real.rpow 2 (-3 / 8)) : ℕ) : ℝ)
      ≤ (DSet (bracket M p' x y) : ℝ) := by push_cast; linarith [hfinal]
  exact_mod_cast this

end Proof.Induction

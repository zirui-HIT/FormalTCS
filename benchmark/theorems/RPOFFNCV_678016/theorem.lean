import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.Real.Sqrt
import Mathlib.InformationTheory.Hamming

set_option linter.all false
set_option maxHeartbeats 500000

def char_word {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : Polynomial F) : F → ℤ :=
  fun α => quadraticChar F (Polynomial.eval α g)

noncomputable def algorithm_a {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (d e : ℕ) (r : F → ℤ) : Polynomial F :=
  letI := Classical.propDecidable
  if h : ∃ p : Polynomial F,
      p.Monic ∧ Squarefree p ∧ p.natDegree ≤ d ∧ hammingDist (char_word p) r ≤ e then
    h.choose
  else 0

def weil_char_sum_bound (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∀ f : Polynomial F, Squarefree f → 1 ≤ f.natDegree →
    |((∑ α : F, char_word f α : ℤ) : ℝ)|
      ≤ ((f.natDegree : ℝ) - 1) * Real.sqrt (Fintype.card F)

theorem algorithm_a_correct {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hodd : Odd (Fintype.card F))
    (hweil : weil_char_sum_bound F)
    (ε : ℝ) (hε : 0 < ε)
    (d e : ℕ)
    (hd : (d : ℝ) ≤ ε / 16 * Real.sqrt (Fintype.card F))
    (he : (e : ℝ) ≤ (1 / 8 - ε) * (Fintype.card F : ℝ))
    (g : Polynomial F) (hmonic : g.Monic) (hsquarefree : Squarefree g)
    (hdeg : g.natDegree ≤ d)
    (r : F → ℤ)
    (hdist : hammingDist (char_word g) r ≤ e) :
    algorithm_a d e r = g := by sorry

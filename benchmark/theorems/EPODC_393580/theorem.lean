import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic

noncomputable def grid_point (m i : ℕ) : ℝ := (i : ℝ) / (m : ℝ)

noncomputable def ece (T : ℕ) (p y : ℕ → ℝ) : ℝ :=
  ∑ v ∈ (Finset.range T).image p,
    |∑ t ∈ (Finset.range T).filter (fun t => p t = v), (p t - y t)|

noncomputable def calibrated (T : ℕ) (q y : ℕ → ℝ) : Prop := ece T q y = 0

noncomputable def l1_dist (T : ℕ) (p q : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T, |p t - q t|

noncomputable def cal_dist (T : ℕ) (p y : ℕ → ℝ) : ℝ :=
  sInf {d : ℝ | ∃ q : ℕ → ℝ, calibrated T q y ∧ d = l1_dist T p q}

noncomputable def cond_bias (t : ℕ) (pt y : ℕ → ℝ) (v : ℝ) : ℝ :=
  ∑ s ∈ (Finset.range t).filter (fun s => pt s = v), (pt s - y s)

def aosa_run (T m : ℕ) (y p pt : ℕ → ℝ) (idx : ℕ → ℕ) : Prop :=
  1 ≤ m ∧ ∀ t < T,
    (y t = 0 ∨ y t = 1) ∧
    idx t + 1 ≤ m ∧
    cond_bias t pt y (grid_point m (idx t)) ≤ 0 ∧
    0 ≤ cond_bias t pt y (grid_point m (idx t + 1)) ∧
    (p t = grid_point m (idx t) ∨ p t = grid_point m (idx t + 1)) ∧
    (pt t = grid_point m (idx t) ∨ pt t = grid_point m (idx t + 1)) ∧
    |pt t - y t| ≤ |grid_point m (idx t) - y t| ∧
    |pt t - y t| ≤ |grid_point m (idx t + 1) - y t|

theorem alg (T m : ℕ) (y p pt : ℕ → ℝ) (idx : ℕ → ℕ) (hm : 1 ≤ m)
    (hms : (m : ℝ) = Real.sqrt T)
    (hrun : aosa_run T m y p pt idx) :
    cal_dist T p y ≤ 2 * Real.sqrt T + 1 := by sorry

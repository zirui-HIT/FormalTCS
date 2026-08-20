import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.Filter.AtTopBot.Defs

def sparse_vector {m : ℕ} (k : ℕ) (z : Fin m → ℝ) : Prop :=
  Set.ncard (Function.support z) ≤ k

def unit_cube_vector {m : ℕ} (z : Fin m → ℝ) : Prop :=
  ∀ i, z i ∈ Set.Icc (-1 : ℝ) 1

def linearly_recovers (m k d : ℕ) (ε : ℝ) : Prop :=
  ∃ A B : Matrix (Fin d) (Fin m) ℝ,
    ∀ z : Fin m → ℝ,
      sparse_vector k z →
      unit_cube_vector z →
      ∀ i, |((B.transpose * A).mulVec z) i - z i| < ε

noncomputable def embedding_dimension (m k : ℕ) (ε : ℝ) : ℕ :=
  sInf {d : ℕ | linearly_recovers m k d ε}

noncomputable def epsilon_threshold (m k : ℕ) : ℝ :=
  Real.sqrt ((k : ℝ) ^ 3) * Real.sqrt 5 / Real.sqrt (m : ℝ)

noncomputable def lower_bound_scale (m k : ℕ) : ℝ :=
  ((k : ℝ) ^ 2 / Real.log (k : ℝ)) *
    Real.log ((m : ℝ) / (k : ℝ))

def lower_bound_filter (ε : ℝ) : Filter (ℕ × ℕ) :=
  Filter.atTop ⊓
    Filter.principal {p : ℕ × ℕ | epsilon_threshold p.1 p.2 < ε}

theorem lower_bound (ε : ℝ) (hε_upper : ε ≤ (1 : ℝ) / 2) :
    Asymptotics.IsBigO (lower_bound_filter ε)
      (fun p : ℕ × ℕ => lower_bound_scale p.1 p.2)
      (fun p : ℕ × ℕ => (embedding_dimension p.1 p.2 ε : ℝ)) := by sorry

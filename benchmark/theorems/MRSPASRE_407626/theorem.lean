import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.all false
set_option maxHeartbeats 500000

abbrev joint_probability_distribution
    (n : ℕ) (Y : Type*) [Fintype Y] := PMF (Fin n → Y)

noncomputable def path_probability
    {n : ℕ} {Y : Type*} [Fintype Y]
    (q : joint_probability_distribution n Y) (w : Fin n → Y) : ℝ :=
  (q w).toReal

noncomputable def conditional_probability
    {n : ℕ} {Y : Type*} [Fintype Y]
    (q : joint_probability_distribution n Y) (t : Fin n)
    (w : Fin n → Y) (y : Y) : ℝ := by
  classical
  let prefixMass :=
    ∑ u : Fin n → Y,
      if ∀ i : Fin n, i.val < t.val → u i = w i
      then path_probability q u else 0
  let extendedMass :=
    ∑ u : Fin n → Y,
      if (∀ i : Fin n, i.val < t.val → u i = w i) ∧ u t = y
      then path_probability q u else 0
  exact if prefixMass = 0 then 0 else extendedMass / prefixMass

noncomputable def shtarkov_sum
    {n : ℕ} {Y : Type*} [Fintype Y]
    (Q : Set (joint_probability_distribution n Y)) : ℝ :=
  ∑ w : Fin n → Y,
    sSup {r : ℝ | ∃ q ∈ Q, r = path_probability q w}

noncomputable def minimax_regret
    {n : ℕ} {Y : Type*} [Fintype Y]
    (Q : Set (joint_probability_distribution n Y)) : ℝ :=
  Real.log (shtarkov_sum Q)

def is_sequential_sqrt_cover
    {n : ℕ} {Y : Type*} [Fintype Y]
    (Q : Set (joint_probability_distribution n Y)) (α : ℝ)
    {k : ℕ} (V : Fin k → joint_probability_distribution n Y) : Prop :=
  ∀ q ∈ Q, ∀ w : Fin n → Y,
    ∃ j : Fin k, ∀ (t : Fin n) (y : Y),
      |Real.sqrt (conditional_probability q t w y) -
          Real.sqrt (conditional_probability (V j) t w y)| ≤ α

noncomputable def sequential_sqrt_covering_number
    {n : ℕ} {Y : Type*} [Fintype Y]
    (Q : Set (joint_probability_distribution n Y)) (α : ℝ) : ℕ :=
  sInf {k : ℕ |
    ∃ V : Fin k → joint_probability_distribution n Y,
      is_sequential_sqrt_cover Q α V}

noncomputable def sequential_sqrt_entropy
    {n : ℕ} {Y : Type*} [Fintype Y]
    (Q : Set (joint_probability_distribution n Y)) (α : ℝ) : ℝ :=
  Real.log (sequential_sqrt_covering_number Q α : ℝ)

noncomputable def entropy_tradeoff
    {n : ℕ} {Y : Type*} [Fintype Y]
    (Q : Set (joint_probability_distribution n Y)) (δ γ : ℝ) : ℝ :=
  (n : ℝ) * δ * Real.sqrt (Fintype.card Y : ℝ) +
    Real.sqrt ((n : ℝ) * (Fintype.card Y : ℝ)) *
      (∫ α in δ..γ, Real.sqrt (sequential_sqrt_entropy Q α)) +
    sequential_sqrt_entropy Q γ

noncomputable def optimized_entropy_tradeoff
    {n : ℕ} {Y : Type*} [Fintype Y]
    (Q : Set (joint_probability_distribution n Y)) : ℝ :=
  sInf {r : ℝ |
    ∃ δ γ : ℝ, 0 < δ ∧ δ < γ ∧ r = entropy_tradeoff Q δ γ}

theorem general_upper_bound :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (n : ℕ) (Y : Type*) [Fintype Y],
        7 ≤ n →
        ∀ (Q : Set (joint_probability_distribution n Y)),
          minimax_regret Q ≤
            C * ((1 : ℝ) + Real.log (n : ℝ) +
              Real.log (Fintype.card Y : ℝ)) ^ k *
              (1 + optimized_entropy_tradeoff Q) := by sorry

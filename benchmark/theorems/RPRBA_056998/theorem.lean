import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

set_option linter.all false
set_option maxHeartbeats 500000

open scoped TensorProduct

variable {EP EL EU X : Type*}
  [NormedAddCommGroup EP] [InnerProductSpace ℝ EP] [FiniteDimensional ℝ EP]
  [NormedAddCommGroup EL] [InnerProductSpace ℝ EL] [FiniteDimensional ℝ EL]
  [NormedAddCommGroup EU] [InnerProductSpace ℝ EU] [FiniteDimensional ℝ EU]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]

structure approachability_instance (EP EL EU : Type*)
    [NormedAddCommGroup EP] [InnerProductSpace ℝ EP]
    [NormedAddCommGroup EL] [InnerProductSpace ℝ EL]
    [NormedAddCommGroup EU] [InnerProductSpace ℝ EU] where
  actions : Set EP
  losses : Set EL
  constraints : Set EU
  constraintForm : EU →ₗ[ℝ] (((EP ⊗[ℝ] EL) →ₗ[ℝ] ℝ) × ℝ)

def is_approachability_instance (I : approachability_instance EP EL EU) : Prop :=
  Convex ℝ I.actions ∧ Bornology.IsBounded I.actions ∧ I.actions.Nonempty ∧
  Convex ℝ I.losses ∧ Bornology.IsBounded I.losses ∧ I.losses.Nonempty ∧
  Convex ℝ I.constraints ∧ Bornology.IsBounded I.constraints ∧ I.constraints.Nonempty

noncomputable def approachability_loss (I : approachability_instance EP EL EU) (T : ℕ)
    (p : Fin T → EP) (l : Fin T → EL) : ℝ :=
  sSup ((fun u => ∑ t,
    (I.constraintForm u).1 (p t ⊗ₜ[ℝ] l t) + (I.constraintForm u).2) ''
    I.constraints)

structure approachability_algorithm (I : approachability_instance EP EL EU) where
  play : (t : ℕ) → (Fin t → EL) → EP
  play_mem : ∀ (t : ℕ) (h : Fin t → EL), play t h ∈ I.actions

def approachability_play_sequence (I : approachability_instance EP EL EU)
    (A : approachability_algorithm I) (T : ℕ) (l : Fin T → EL) : Fin T → EP :=
  fun t => A.play t.val (fun s => l ⟨s.val, s.isLt.trans t.isLt⟩)

noncomputable def approachability_value (I : approachability_instance EP EL EU)
    (A : approachability_algorithm I) (T : ℕ) : ℝ :=
  sSup ((fun l => approachability_loss I T
      (approachability_play_sequence I A T l) l) ''
    {l : Fin T → EL | ∀ t, l t ∈ I.losses})

structure regret_instance (X : Type*)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] where
  actions : Set X
  losses : Set X
  benchmarks : Set (X →ᵃ[ℝ] X)

def is_improper_regret_instance (J : regret_instance X) : Prop :=
  Convex ℝ J.actions ∧ Bornology.IsBounded J.actions ∧ J.actions.Nonempty ∧
  Convex ℝ J.losses ∧ Bornology.IsBounded J.losses ∧ J.losses.Nonempty ∧
  J.benchmarks.Nonempty ∧
  ∀ φ ∈ J.benchmarks, ∃ x ∈ J.actions, φ x = x

noncomputable def phi_regret (J : regret_instance X) (T : ℕ)
    (x y : Fin T → X) : ℝ :=
  sSup ((fun φ : X →ᵃ[ℝ] X =>
    (∑ t, (inner ℝ (x t) (y t) : ℝ)) -
      ∑ t, (inner ℝ (φ (x t)) (y t) : ℝ)) '' J.benchmarks)

structure regret_algorithm (J : regret_instance X) where
  play : (t : ℕ) → (Fin t → X) → X
  play_mem : ∀ (t : ℕ) (h : Fin t → X), play t h ∈ J.actions

def regret_play_sequence (J : regret_instance X) (A : regret_algorithm J)
    (T : ℕ) (y : Fin T → X) : Fin T → X :=
  fun t => A.play t.val (fun s => y ⟨s.val, s.isLt.trans t.isLt⟩)

noncomputable def regret_value (J : regret_instance X) (A : regret_algorithm J)
    (T : ℕ) : ℝ :=
  sSup ((fun y => phi_regret J T (regret_play_sequence J A T y) y) ''
    {y : Fin T → X | ∀ t, y t ∈ J.losses})

def tight_reduction (I : approachability_instance EP EL EU)
    (J : regret_instance X) : Prop :=
  (∀ A : approachability_algorithm I, ∃ A' : regret_algorithm J,
      ∀ T : ℕ, regret_value J A' T = approachability_value I A T) ∧
  (∀ A' : regret_algorithm J, ∃ A : approachability_algorithm I,
      ∀ T : ℕ, approachability_value I A T = regret_value J A' T)

def has_neutral_actions (I : approachability_instance EP EL EU) : Prop :=
  ∀ u ∈ I.constraints, ∃ p ∈ I.actions, ∀ l ∈ I.losses,
    (I.constraintForm u).1 (p ⊗ₜ[ℝ] l) + (I.constraintForm u).2 = 0

theorem app_to_improper (I : approachability_instance EP EL EU)
    (hI : is_approachability_instance I) (hN : has_neutral_actions I) :
    ∃ J : regret_instance
        (WithLp 2
          (EP × WithLp 2 (EL × WithLp 2 ((EU ⊗[ℝ] EP) × EU)))),
      is_improper_regret_instance J ∧ tight_reduction I J := by sorry

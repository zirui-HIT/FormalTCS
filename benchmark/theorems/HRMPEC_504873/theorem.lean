import Mathlib.InformationTheory.Hamming
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic

variable {F : Type*} [Field F] [DecidableEq F]

structure hyperplane (m : ℕ) (K : Type*) [Field K] where
  normal : Fin m → K
  offset : K
  normal_ne_zero : normal ≠ 0

def on_hyperplane {m : ℕ} (h : hyperplane m F) (x : Fin m → F) : Prop :=
  ∑ i, h.normal i * x i = h.offset

def in_general_position {m : ℕ} (H : Finset (hyperplane m F)) : Prop :=
  (∀ S ⊆ H, S.card = m → ∃! x : Fin m → F, ∀ h ∈ S, on_hyperplane h x) ∧
    (∀ S ⊆ H, S.card = m + 1 → ¬∃ x : Fin m → F, ∀ h ∈ S, on_hyperplane h x)

def gap_domain (m t : ℕ) (T : Finset (Fin m → F)) : Prop :=
  ∃ H : Finset (hyperplane m F), H.card = t ∧ in_general_position H ∧
    ∀ x : Fin m → F, x ∈ T ↔ ∃ S ⊆ H, S.card = m ∧ ∀ h ∈ S, on_hyperplane h x

noncomputable def poly_eval_map (m : ℕ) (T : Finset (Fin m → F)) :
    MvPolynomial (Fin m) F →ₗ[F] (↥T → F) :=
  LinearMap.pi fun x : ↥T => (MvPolynomial.aeval (x : Fin m → F)).toLinearMap

noncomputable def gap_code (m d : ℕ) (T : Finset (Fin m → F)) : Submodule F (↥T → F) :=
  (MvPolynomial.restrictTotalDegree (Fin m) F d).map (poly_eval_map m T)

noncomputable def code_min_dist {ι : Type*} [Fintype ι] (C : Submodule F (ι → F)) : ℕ :=
  sInf {w : ℕ | ∃ c₁ ∈ C, ∃ c₂ ∈ C, c₁ ≠ c₂ ∧ hammingDist c₁ c₂ = w}

noncomputable def code_rel_dist {ι : Type*} [Fintype ι] (C : Submodule F (ι → F)) : ℝ :=
  (code_min_dist C : ℝ) / (Fintype.card ι : ℝ)

theorem gap_code_rel_dist (m d t : ℕ) (hd : 0 < d) (hmdt : m + d < t)
    (ε : ℝ) (hε : 0 < ε) (ht : (t : ℝ) = (m : ℝ) + (d : ℝ) + ε * (d : ℝ) - 1)
    (T : Finset (Fin m → F)) (hT : gap_domain m t T) :
    (ε / (1 + ε)) ^ m ≤ code_rel_dist (gap_code m d T) := by sorry

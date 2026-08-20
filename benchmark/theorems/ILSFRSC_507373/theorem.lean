import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.OrderOfElement

set_option linter.all false

variable {F : Type*} [Field F] [Fintype F]

structure folded_rs_code (F : Type*) [Field F] [Fintype F] where
  m : ℕ
  N : ℕ
  K : ℕ
  gamma : F
  hm : 0 < m
  hN : 0 < N
  hK : K ≤ m * N
  horder : m * N ≤ orderOf gamma

def frs_encode (C : folded_rs_code F) (f : Polynomial F) : Fin C.N → Fin C.m → F :=
  fun i j => f.eval (C.gamma ^ (i.val * C.m + j.val))

def frs_code (C : folded_rs_code F) : Set (Fin C.N → Fin C.m → F) :=
  frs_encode C '' ((Polynomial.degreeLT (R := F) C.K : Submodule F (Polynomial F)) :
    Set (Polynomial F))

noncomputable def frs_rate (C : folded_rs_code F) : ℝ :=
  (C.K : ℝ) / ((C.m : ℝ) * (C.N : ℝ))

noncomputable def frs_dist (C : folded_rs_code F) (g h : Fin C.N → Fin C.m → F) : ℝ :=
  (Set.ncard {i : Fin C.N | g i ≠ h i} : ℝ) / (C.N : ℝ)

def frs_list (C : folded_rs_code F) (g : Fin C.N → Fin C.m → F) (eta : ℝ) :
    Set (Fin C.N → Fin C.m → F) :=
  {h | h ∈ frs_code C ∧ frs_dist C g h < eta}

noncomputable def frs_radius (C : folded_rs_code F) (k : ℕ) : ℝ :=
  ((k : ℝ) / ((k : ℝ) + 1)) *
    (1 - ((C.m : ℝ) / ((C.m : ℝ) - (k : ℝ) + 1)) * frs_rate C)

theorem frs_list_size (C : folded_rs_code F) (k : ℕ) (hk1 : 1 ≤ k) (hkm : k ≤ C.m)
    (g : Fin C.N → Fin C.m → F) :
    (frs_list C g (frs_radius C k)).ncard ≤ (k - 1) ^ 2 + 1 := by sorry

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace NOF

def forget {ι G : Type*} (i : ι) (x : ι → G) (j : {j : ι // j ≠ i}) : G := x j

def IsForbiddenPatternWithTip {ι G : Type*} (a : ι → ι → G) (v : ι → G) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → a i j = v j

def IsForbiddenPattern {ι G : Type*} (a : ι → ι → G) : Prop :=
  ∃ v, IsForbiddenPatternWithTip a v

structure Protocol (G : Type*) (d : ℕ) where
  nextBit (i : ZMod d) : ({j : ZMod d // j ≠ i} → G) → List Bool → Bool
  guess (i : ZMod d) : ({j : ZMod d // j ≠ i} → G) → List Bool → Bool

def Protocol.broadcast {G : Type*} {d : ℕ} (P : Protocol G d) (x : ZMod d → G) : ℕ → List Bool
  | 0 => []
  | t + 1 => P.nextBit t (forget (t : ZMod d) x) (P.broadcast x t) :: P.broadcast x t

def Protocol.IsValid {G : Type*} {d : ℕ} (P : Protocol G d) (F : (ZMod d → G) → Bool) (t : ℕ) :
    Prop :=
  ∀ x i, P.guess i (forget i x) (P.broadcast x t) = F x

def eval {ι G : Type*} [Fintype ι] [AddCommGroup G] [DecidableEq G] (x : ι → G) : Bool :=
  ∑ i, x i == 0

theorem trivial_of_isForbiddenPattern_of_isValid_eval {G : Type*} [AddCommGroup G] [DecidableEq G]
    {d : ℕ} [NeZero d] {P : Protocol G d} {t : ℕ} {B : List Bool} {a : ZMod d → ZMod d → G}
    (ha : IsForbiddenPattern a) (hP : P.IsValid eval t) (hE : ∀ i, eval (a i) = true)
    (hB : ∀ i, P.broadcast (a i) t = B) : ∀ i j, a i = a j := by
  sorry

end NOF

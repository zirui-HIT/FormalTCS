import Mathlib

namespace Proof.Types.Protocol

inductive Protocol (X Y Z : Type*) : Type _ where
  | leaf (z : Z) : Protocol X Y Z
  | aNode (a : X → Bool) (l r : Protocol X Y Z) : Protocol X Y Z
  | bNode (b : Y → Bool) (l r : Protocol X Y Z) : Protocol X Y Z

namespace Protocol

variable {X Y Z : Type*}

def cost : Protocol X Y Z → ℕ
  | leaf _ => 0
  | aNode _ l r => 1 + max (cost l) (cost r)
  | bNode _ l r => 1 + max (cost l) (cost r)

def eval : Protocol X Y Z → X → Y → Z
  | leaf z, _, _ => z
  | aNode a l r, x, y => if a x then eval r x y else eval l x y
  | bNode b l r, x, y => if b y then eval r x y else eval l x y

def Computes (P : Protocol X Y Z) (f : X → Y → Z) : Prop :=
  ∀ x y, eval P x y = f x y

end Protocol

end Proof.Types.Protocol

namespace Proof.Types.CommComplexity

open Proof.Types.Protocol

def AchievableCosts {X Y Z : Type*} (f : X → Y → Z) : Set ℕ :=
  { c : ℕ | ∃ P : Protocol X Y Z, P.cost = c ∧ Protocol.Computes P f }

noncomputable def D {X Y Z : Type*} [Fintype X] [Fintype Y] (f : X → Y → Z) : ℕ :=
  sInf (AchievableCosts f)

end Proof.Types.CommComplexity

namespace Proof.Types.DirectSum

def directSum {X Y : Type*} (f : X → Y → Bool) (l : ℕ) :
    (Fin l → X) → (Fin l → Y) → (Fin l → Bool) :=
  fun xs ys i => f (xs i) (ys i)

end Proof.Types.DirectSum

namespace Proof.MainTheorem

open Proof.Types.CommComplexity
open Proof.Types.DirectSum

theorem refutation_of_direct_sum_conjecture :
    ∃ f : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Bool,
      ∀ N L C : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ ℓ : ℕ, L ≤ ℓ ∧
        (D (f n) : ℝ) > (D (directSum (f n) ℓ) : ℝ) / (ℓ : ℝ) + (C : ℝ) := by
  sorry

end Proof.MainTheorem

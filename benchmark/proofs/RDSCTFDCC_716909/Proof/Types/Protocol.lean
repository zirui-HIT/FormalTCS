import Mathlib

namespace Proof.Types.Protocol

/-- A deterministic two-party communication protocol (Definition 2.1).
Inputs are `x : X` (Alice) and `y : Y` (Bob); the protocol outputs a value in `Z`.
The protocol is a binary tree:
* `leaf z` returns the output `z`;
* `aNode a l r` is an internal node where Alice speaks: she evaluates the
  predicate `a : X → Bool` on her input and the protocol descends into `l`
  if `a x = false` and into `r` if `a x = true`;
* `bNode b l r` is an internal node where Bob speaks, analogously with
  `b : Y → Bool` on his input. -/
inductive Protocol (X Y Z : Type*) : Type _ where
  | leaf (z : Z) : Protocol X Y Z
  | aNode (a : X → Bool) (l r : Protocol X Y Z) : Protocol X Y Z
  | bNode (b : Y → Bool) (l r : Protocol X Y Z) : Protocol X Y Z

namespace Protocol

variable {X Y Z : Type*}

/-- The cost of a protocol is the depth (height) of the tree: the maximum
number of bits exchanged along any root-to-leaf path. A leaf has cost `0`;
an internal node (either party) has cost `1 + max (cost l) (cost r)`. -/
def cost : Protocol X Y Z → ℕ
  | leaf _ => 0
  | aNode _ l r => 1 + max (cost l) (cost r)
  | bNode _ l r => 1 + max (cost l) (cost r)

/-- The output computed by the protocol on input `(x, y)`, obtained by walking
from the root to a leaf: at a leaf, return its value; at an Alice node, descend
left if `a x = false` and right if `a x = true`; at a Bob node, descend left if
`b y = false` and right if `b y = true`. -/
def eval : Protocol X Y Z → X → Y → Z
  | leaf z, _, _ => z
  | aNode a l r, x, y => if a x then eval r x y else eval l x y
  | bNode b l r, x, y => if b y then eval r x y else eval l x y

/-- A protocol `P` computes the function `f : X → Y → Z` if its output agrees
with `f` on every input `(x, y)`. -/
def Computes (P : Protocol X Y Z) (f : X → Y → Z) : Prop :=
  ∀ x y, eval P x y = f x y

end Protocol

end Proof.Types.Protocol

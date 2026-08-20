import Mathlib
import Proof.Types.CommComplexity
import Proof.Types.DirectSum
import Proof.Types.Interlace
import Proof.Types.AlternatingGame
import Proof.Types.BoolMat

namespace Proof.UpperBound

open Proof.Types.CommComplexity
open Proof.Types.DirectSum
open Proof.Types.Interlace
open Proof.Types.AlternatingGame
open Proof.Types.BoolMat
open Proof.Types.Protocol

private abbrev Q : ℕ := 255 * 2 ^ (10000 - 8)

/-! ### Protocol transpose -/

/-- Transpose of a protocol: swap Alice and Bob nodes. The resulting protocol
takes inputs in `Y` (Alice) and `X` (Bob). -/
def Protocol.transpose {X Y Z : Type*} : Protocol X Y Z → Protocol Y X Z
  | .leaf z => .leaf z
  | .aNode a l r => .bNode a (Protocol.transpose l) (Protocol.transpose r)
  | .bNode b l r => .aNode b (Protocol.transpose l) (Protocol.transpose r)

theorem Protocol.transpose_cost {X Y Z : Type*} (P : Protocol X Y Z) :
    (Protocol.transpose P).cost = P.cost := by
  induction P with
  | leaf z => rfl
  | aNode a l r ihl ihr => simp [Protocol.transpose, Protocol.cost, ihl, ihr]
  | bNode b l r ihl ihr => simp [Protocol.transpose, Protocol.cost, ihl, ihr]

theorem Protocol.transpose_eval {X Y Z : Type*} (P : Protocol X Y Z) (y : Y) (x : X) :
    (Protocol.transpose P).eval y x = P.eval x y := by
  induction P with
  | leaf z => rfl
  | aNode a l r ihl ihr =>
      simp only [Protocol.transpose, Protocol.eval]
      by_cases h : a x <;> simp [h, ihl, ihr]
  | bNode b l r ihl ihr =>
      simp only [Protocol.transpose, Protocol.eval]
      by_cases h : b y <;> simp [h, ihl, ihr]

theorem AchievableCosts_swap_subset {A B C : Type*} (g : A → B → C) :
    AchievableCosts g ⊆ AchievableCosts (fun b a => g a b) := by
  intro c hc
  obtain ⟨P, hcost, hcomp⟩ := hc
  refine ⟨Protocol.transpose P, ?_, ?_⟩
  · rw [Protocol.transpose_cost]; exact hcost
  · intro b a
    rw [Protocol.transpose_eval]; exact hcomp a b

/-- `D` of a function equals `D` of its swap. -/
theorem D_swap {A B C : Type*} [Fintype A] [Fintype B] (g : A → B → C) :
    D g = D (fun b a => g a b) := by
  have h1 : AchievableCosts g ⊆ AchievableCosts (fun b a => g a b) :=
    AchievableCosts_swap_subset g
  have h2 : AchievableCosts (fun b a => g a b) ⊆ AchievableCosts g := by
    have := AchievableCosts_swap_subset (fun b a => g a b)
    simpa using this
  have heq : AchievableCosts g = AchievableCosts (fun b a => g a b) :=
    Set.Subset.antisymm h1 h2
  unfold D
  rw [heq]

/-! ### Reindexing a protocol along Alice/Bob input maps -/

/-- Reindex a protocol along input maps `αA : A → A'`, `αB : B → B'`. The new
protocol on inputs `(a, b)` simulates `P` on `(αA a, αB b)`. -/
def Protocol.comap {A A' B B' Z : Type*}
    (αA : A → A') (αB : B → B') : Protocol A' B' Z → Protocol A B Z
  | .leaf z => .leaf z
  | .aNode a l r => .aNode (fun x => a (αA x)) (Protocol.comap αA αB l) (Protocol.comap αA αB r)
  | .bNode b l r => .bNode (fun y => b (αB y)) (Protocol.comap αA αB l) (Protocol.comap αA αB r)

theorem Protocol.comap_cost {A A' B B' Z : Type*}
    (αA : A → A') (αB : B → B') (P : Protocol A' B' Z) :
    (Protocol.comap αA αB P).cost = P.cost := by
  induction P with
  | leaf z => rfl
  | aNode a l r ihl ihr => simp [Protocol.comap, Protocol.cost, ihl, ihr]
  | bNode b l r ihl ihr => simp [Protocol.comap, Protocol.cost, ihl, ihr]

theorem Protocol.comap_eval {A A' B B' Z : Type*}
    (αA : A → A') (αB : B → B') (P : Protocol A' B' Z) (a : A) (b : B) :
    (Protocol.comap αA αB P).eval a b = P.eval (αA a) (αB b) := by
  induction P with
  | leaf z => rfl
  | aNode p l r ihl ihr =>
      simp only [Protocol.comap, Protocol.eval]
      by_cases h : p (αA a) <;> simp [h, ihl, ihr]
  | bNode p l r ihl ihr =>
      simp only [Protocol.comap, Protocol.eval]
      by_cases h : p (αB b) <;> simp [h, ihl, ihr]

/-! ### Alice-announce prefix tree -/

/-- A complete depth-`d` binary tree of Alice nodes branching on the bits of an
address `read a : Fin d → Bool`. Leaf word `w : Fin d → Bool` holds protocol
`leaf w`. -/
def announceTree {A B Z : Type*} :
    (d : ℕ) → (leaf : (Fin d → Bool) → Protocol A B Z) → (read : A → Fin d → Bool) →
    Protocol A B Z
  | 0, leaf, _ => leaf (fun i => i.elim0)
  | (d + 1), leaf, read =>
      Protocol.aNode (fun a => read a 0)
        (announceTree d (fun w => leaf (Fin.cons false w)) (fun a i => read a i.succ))
        (announceTree d (fun w => leaf (Fin.cons true w)) (fun a i => read a i.succ))

theorem announceTree_cost {A B Z : Type*} (c : ℕ) :
    ∀ (d : ℕ) (leaf : (Fin d → Bool) → Protocol A B Z) (read : A → Fin d → Bool),
      (∀ w, (leaf w).cost ≤ c) → (announceTree d leaf read).cost ≤ d + c := by
  intro d
  induction d with
  | zero =>
      intro leaf read hc
      simpa [announceTree] using hc _
  | succ d ih =>
      intro leaf read hc
      simp only [announceTree, Protocol.cost]
      have hl := ih (fun w => leaf (Fin.cons false w)) (fun a i => read a i.succ)
        (fun w => hc _)
      have hr := ih (fun w => leaf (Fin.cons true w)) (fun a i => read a i.succ)
        (fun w => hc _)
      have : max (announceTree d (fun w => leaf (Fin.cons false w)) (fun a i => read a i.succ)).cost
          (announceTree d (fun w => leaf (Fin.cons true w)) (fun a i => read a i.succ)).cost ≤ d + c := by
        exact max_le hl hr
      omega

theorem announceTree_eval {A B Z : Type*} :
    ∀ (d : ℕ) (leaf : (Fin d → Bool) → Protocol A B Z) (read : A → Fin d → Bool)
      (a : A) (b : B),
      (announceTree d leaf read).eval a b = (leaf (read a)).eval a b := by
  intro d
  induction d with
  | zero =>
      intro leaf read a b
      simp only [announceTree]
      congr
      funext i
      exact i.elim0
  | succ d ih =>
      intro leaf read a b
      have hword : ∀ (c : Bool), read a 0 = c →
          Fin.cons c (fun i => read a i.succ) = read a := by
        intro c hc
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hc.symm
        · simp [Fin.cons_succ]
      simp only [announceTree, Protocol.eval]
      by_cases h : read a 0 = true
      · simp only [h, if_true]
        rw [ih, hword true h]
      · simp only [Bool.not_eq_true] at h
        simp only [h, Bool.false_eq_true, if_false]
        rw [ih, hword false h]

/-- Every protocol contains at least one leaf value, hence yields an element of `Z`. -/
theorem Protocol.nonempty_codomain {A B Z : Type*} (P : Protocol A B Z) : Nonempty Z := by
  induction P with
  | leaf z => exact ⟨z⟩
  | aNode _ l _ ihl _ => exact ihl
  | bNode _ l _ ihl _ => exact ihl

/-- Bob-side announce tree (mirror of `announceTree`). -/
def bobAnnounceTree {A B Z : Type*} :
    (d : ℕ) → (leaf : (Fin d → Bool) → Protocol A B Z) → (read : B → Fin d → Bool) →
    Protocol A B Z
  | 0, leaf, _ => leaf (fun i => i.elim0)
  | (d + 1), leaf, read =>
      Protocol.bNode (fun b => read b 0)
        (bobAnnounceTree d (fun w => leaf (Fin.cons false w)) (fun b i => read b i.succ))
        (bobAnnounceTree d (fun w => leaf (Fin.cons true w)) (fun b i => read b i.succ))

theorem bobAnnounceTree_eval {A B Z : Type*} :
    ∀ (d : ℕ) (leaf : (Fin d → Bool) → Protocol A B Z) (read : B → Fin d → Bool)
      (a : A) (b : B),
      (bobAnnounceTree d leaf read).eval a b = (leaf (read b)).eval a b := by
  intro d
  induction d with
  | zero =>
      intro leaf read a b
      simp only [bobAnnounceTree]
      congr
      funext i
      exact i.elim0
  | succ d ih =>
      intro leaf read a b
      have hword : ∀ (c : Bool), read b 0 = c →
          Fin.cons c (fun i => read b i.succ) = read b := by
        intro c hc
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hc.symm
        · simp [Fin.cons_succ]
      simp only [bobAnnounceTree, Protocol.eval]
      by_cases h : read b 0 = true
      · simp only [h, if_true]
        rw [ih, hword true h]
      · simp only [Bool.not_eq_true] at h
        simp only [h, Bool.false_eq_true, if_false]
        rw [ih, hword false h]

/-- Any fintype embeds into `Fin (card) → Bool`. -/
theorem exists_bit_embedding (A : Type*) [Fintype A] :
    Nonempty (A ↪ (Fin (Fintype.card A) → Bool)) := by
  classical
  apply Function.Embedding.nonempty_of_card_le
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  exact le_of_lt (Nat.lt_two_pow_self)

/-- For finite `A`, `B` and any `g`, there is a protocol computing `g`
(Alice reveals her input, then Bob reveals his). Hence `AchievableCosts g`
is nonempty. -/
theorem AchievableCosts_nonempty {A B Z : Type*} [Fintype A] [Fintype B]
    [Nonempty Z] (g : A → B → Z) : (AchievableCosts g).Nonempty := by
  classical
  obtain ⟨encA⟩ := exists_bit_embedding A
  obtain ⟨encB⟩ := exists_bit_embedding B
  rcases isEmpty_or_nonempty A with hA | hA
  · refine ⟨0, Protocol.leaf (Classical.arbitrary Z), rfl, fun a => (hA.elim a)⟩
  rcases isEmpty_or_nonempty B with hB | hB
  · refine ⟨0, Protocol.leaf (Classical.arbitrary Z), rfl, fun a b => (hB.elim b)⟩
  haveI : Nonempty A := hA
  haveI : Nonempty B := hB
  let decA : (Fin (Fintype.card A) → Bool) → A := Function.invFun encA
  let decB : (Fin (Fintype.card B) → Bool) → B := Function.invFun encB
  have hdecA : ∀ a, decA (encA a) = a :=
    fun a => Function.leftInverse_invFun encA.injective a
  have hdecB : ∀ b, decB (encB b) = b :=
    fun b => Function.leftInverse_invFun encB.injective b
  -- Alice reveals her input, then (at each Alice-leaf) Bob reveals his.
  let P : Protocol A B Z :=
    announceTree (Fintype.card A)
      (fun wa => bobAnnounceTree (Fintype.card B)
        (fun wb => Protocol.leaf (g (decA wa) (decB wb)))
        (fun b => encB b))
      (fun a => encA a)
  refine ⟨P.cost, P, rfl, ?_⟩
  intro a b
  show P.eval a b = g a b
  simp only [P]
  rw [announceTree_eval, bobAnnounceTree_eval, hdecA, hdecB]
  rfl

/-! ### The announce upper bound -/

/-- **Announce upper bound.** If Alice can determine a key `key a ∈ K`, and for
every key value `k` there is a protocol `P k` computing `g` correctly on all
Alice inputs with `key a = k`, with cost `≤ c`, and `K` fits in `d` bits, then
`D g ≤ d + c`: Alice announces the `d`-bit address of her key, then both run
`P (key a)`. -/
theorem D_le_announce {A B Z : Type*} [Fintype A] [Fintype B]
    (g : A → B → Z) (K : Type*) [Fintype K]
    (key : A → K) (P : K → Protocol A B Z) (d c : ℕ)
    (hcard : Fintype.card K ≤ 2 ^ d)
    (hP : ∀ k a b, key a = k → (P k).eval a b = g a b)
    (hc : ∀ k, (P k).cost ≤ c) :
    D g ≤ d + c := by
  classical
  -- If `A` is empty, any protocol computes `g`; take `P` of any key, cost ≤ c ≤ d+c.
  rcases isEmpty_or_nonempty A with hA | hA
  · -- `A` empty ⇒ `D g = sInf (AchievableCosts g) ≤ d + c`.
    rcases isEmpty_or_nonempty Z with hZ | hZ
    · -- no leaves: achievable set is empty, so `sInf = 0`
      have hempty : AchievableCosts g = ∅ := by
        ext n; simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨P, -, -⟩
        exact (Protocol.nonempty_codomain P).elim (fun z => hZ.elim z)
      rw [D, hempty, Nat.sInf_empty]; exact Nat.zero_le _
    · have hmem : (0 : ℕ) ∈ AchievableCosts g :=
        ⟨Protocol.leaf (Classical.arbitrary Z), rfl, fun a => (hA.elim a)⟩
      calc D g ≤ 0 := Nat.sInf_le hmem
        _ ≤ d + c := Nat.zero_le _
  · haveI : Nonempty K := ⟨key (Classical.arbitrary A)⟩
    -- an injective encoding of keys as `d`-bit words
    have hcard2 : Fintype.card K ≤ Fintype.card (Fin d → Bool) := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      exact hcard
    obtain ⟨enc⟩ := Function.Embedding.nonempty_of_card_le hcard2
    -- decode a word back to its key (left inverse of enc)
    let dec : (Fin d → Bool) → K := Function.invFun enc
    have hdec : ∀ k, dec (enc k) = k :=
      Function.leftInverse_invFun enc.injective
    -- the announce tree: at leaf word `w`, run `P (dec w)`; address of `a` is `enc (key a)`
    let T : Protocol A B Z := announceTree d (fun w => P (dec w)) (fun a => enc (key a))
    have hTcost : T.cost ≤ d + c := by
      apply announceTree_cost
      intro w; exact hc _
    have hTeval : ∀ a b, T.eval a b = g a b := by
      intro a b
      have := announceTree_eval d (fun w => P (dec w)) (fun a => enc (key a)) a b
      simp only [T] at this ⊢
      rw [this, hdec]
      exact hP (key a) a b rfl
    refine Nat.sInf_le ?_ |>.trans hTcost
    exact ⟨T, rfl, hTeval⟩

/-- Cardinality bound: `κ^l ≤ 2^⌈l·log₂κ⌉` for `κ ≥ 1`. -/
theorem card_pow_le (κ l : ℕ) (hκ : 1 ≤ κ) :
    κ ^ l ≤ 2 ^ (⌈(l : ℝ) * Real.logb 2 (κ : ℝ)⌉₊) := by
  have h2 : (1:ℝ) < 2 := by norm_num
  have hκR : (0:ℝ) < (κ:ℝ) := by exact_mod_cast hκ
  have key : ((κ:ℝ)) ^ l = (2:ℝ) ^ ((l:ℝ) * Real.logb 2 (κ:ℝ)) := by
    rw [show ((l:ℝ) * Real.logb 2 (κ:ℝ)) = Real.logb 2 ((κ:ℝ)^l) by rw [Real.logb_pow]]
    rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
  have hle : (2:ℝ) ^ ((l:ℝ) * Real.logb 2 (κ:ℝ))
      ≤ (2:ℝ) ^ ((⌈(l : ℝ) * Real.logb 2 (κ : ℝ)⌉₊ : ℝ)) := by
    apply Real.rpow_le_rpow_left_iff h2 |>.mpr
    exact Nat.le_ceil _
  have hcast : (2:ℝ) ^ ((⌈(l : ℝ) * Real.logb 2 (κ : ℝ)⌉₊ : ℝ))
      = ((2 ^ (⌈(l : ℝ) * Real.logb 2 (κ : ℝ)⌉₊) : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; ring
  have hfin : ((κ ^ l : ℕ) : ℝ) ≤ ((2 ^ (⌈(l : ℝ) * Real.logb 2 (κ : ℝ)⌉₊) : ℕ) : ℝ) := by
    rw [← hcast]
    calc ((κ ^ l : ℕ) : ℝ) = (κ:ℝ)^l := by push_cast; ring
      _ = (2:ℝ) ^ ((l:ℝ) * Real.logb 2 (κ:ℝ)) := key
      _ ≤ (2:ℝ) ^ ((⌈(l : ℝ) * Real.logb 2 (κ : ℝ)⌉₊ : ℝ)) := hle
  exact_mod_cast hfin

/-- Cost of the Bob-side announce tree (mirror of `announceTree_cost`). -/
theorem bobAnnounceTree_cost {A B Z : Type*} (c : ℕ) :
    ∀ (d : ℕ) (leaf : (Fin d → Bool) → Protocol A B Z) (read : B → Fin d → Bool),
      (∀ w, (leaf w).cost ≤ c) → (bobAnnounceTree d leaf read).cost ≤ d + c := by
  intro d
  induction d with
  | zero =>
      intro leaf read hc
      simpa [bobAnnounceTree] using hc _
  | succ d ih =>
      intro leaf read hc
      simp only [bobAnnounceTree, Protocol.cost]
      have hl := ih (fun w => leaf (Fin.cons false w)) (fun b i => read b i.succ)
        (fun w => hc _)
      have hr := ih (fun w => leaf (Fin.cons true w)) (fun b i => read b i.succ)
        (fun w => hc _)
      have : max (bobAnnounceTree d (fun w => leaf (Fin.cons false w)) (fun b i => read b i.succ)).cost
          (bobAnnounceTree d (fun w => leaf (Fin.cons true w)) (fun b i => read b i.succ)).cost ≤ d + c := by
        exact max_le hl hr
      omega

/-- If `g a b` depends only on Bob's input via `read : B → (Fin l → Bool)`
(i.e. `g a b = read b`), then Bob can announce the `l` output bits, giving
`D g ≤ l`. -/
theorem D_le_bob_bits {A B : Type*} {l : ℕ} [Fintype A] [Fintype B]
    (g : A → B → (Fin l → Bool)) (read : B → (Fin l → Bool))
    (hg : ∀ a b, g a b = read b) :
    D g ≤ l := by
  classical
  set T : Protocol A B (Fin l → Bool) :=
    bobAnnounceTree l (fun w => Protocol.leaf w) read with hT
  have hTcost : T.cost ≤ l := by
    have := bobAnnounceTree_cost (A := A) (B := B) (Z := (Fin l → Bool)) 0 l
      (fun w => Protocol.leaf w) read (fun w => le_refl _)
    simpa [hT] using this
  have hTeval : ∀ a b, T.eval a b = g a b := by
    intro a b
    have := bobAnnounceTree_eval l (fun w => Protocol.leaf w) read a b
    simp only [hT] at this ⊢
    rw [this]
    show read b = g a b
    rw [hg a b]
  have hmem : T.cost ∈ AchievableCosts g := ⟨T, rfl, hTeval⟩
  exact (Nat.sInf_le hmem).trans hTcost

/-! ### Theorems -/

theorem observation_5_2 {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (l : ℕ) :
    D (directSum f l) = D (directSum (fun (y : Y) (x : X) => f x y) l) := by
  rw [D_swap (directSum f l)]
  congr 1

theorem subgame_lemma_5_6 {X Y : Type*}
    (f : X → Y → Bool) (κ l : ℕ) (u : Fin l → Fin κ)
    (xs : Fin l → (Fin κ × X)) (ys : Fin l → (Fin κ → Y))
    (hu : ∀ i, (xs i).1 = u i) :
    directSum (interlaceFun f κ) l xs ys
      = directSum f l (fun i => (xs i).2) (fun i => ys i (u i)) := by
  funext i
  simp only [directSum, interlaceFun]
  rw [hu i]

theorem one_round_upper_bound_5_7 {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (κ l : ℕ) :
    D (directSum (interlaceFun f κ) l)
      ≤ D (directSum f l) + ⌈(l : ℝ) * Real.logb 2 (κ : ℝ)⌉₊ := by
  classical
  set d := ⌈(l : ℝ) * Real.logb 2 (κ : ℝ)⌉₊ with hd
  have hne : (AchievableCosts (directSum f l)).Nonempty :=
    AchievableCosts_nonempty (directSum f l)
  have hmem : D (directSum f l) ∈ AchievableCosts (directSum f l) :=
    Nat.sInf_mem hne
  obtain ⟨P0, hcost0, hcomp0⟩ := hmem
  set K := (Fin l → Fin κ) with hK
  rw [Nat.add_comm (D (directSum f l)) d]
  apply D_le_announce (directSum (interlaceFun f κ) l) K
    (fun xs i => (xs i).1)
    (fun u => Protocol.comap (fun xs i => (xs i).2) (fun ys i => ys i (u i)) P0)
    d (D (directSum f l))
  · show Fintype.card (Fin l → Fin κ) ≤ 2 ^ d
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    rcases Nat.eq_zero_or_pos κ with hκ0 | hκ1
    · subst hκ0
      rcases Nat.eq_zero_or_pos l with hl0 | hl1
      · subst hl0; exact Nat.one_le_two_pow
      · rw [Nat.zero_pow (by omega)]; exact Nat.zero_le _
    · exact card_pow_le κ l hκ1
  · intro u xs ys hkey
    rw [Protocol.comap_eval]
    rw [hcomp0]
    rw [subgame_lemma_5_6 f κ l u xs ys]
    intro i
    have := congrFun hkey i
    simpa using this
  · intro u
    rw [Protocol.comap_cost, hcost0]

/-! ### Reindexing helpers (from dev scratch) -/

def reindexP {X Y X' Y' Z : Type*} (eX : X' → X) (eY : Y' → Y) :
    Protocol X Y Z → Protocol X' Y' Z
  | Protocol.leaf z => Protocol.leaf z
  | Protocol.aNode a l r =>
      Protocol.aNode (fun x => a (eX x)) (reindexP eX eY l) (reindexP eX eY r)
  | Protocol.bNode b l r =>
      Protocol.bNode (fun y => b (eY y)) (reindexP eX eY l) (reindexP eX eY r)

theorem cost_reindexP {X Y X' Y' Z : Type*} (eX : X' → X) (eY : Y' → Y)
    (P : Protocol X Y Z) : (reindexP eX eY P).cost = P.cost := by
  induction P with
  | leaf z => rfl
  | aNode a l r ihl ihr => simp only [reindexP, Protocol.cost, ihl, ihr]
  | bNode b l r ihl ihr => simp only [reindexP, Protocol.cost, ihl, ihr]

theorem eval_reindexP {X Y X' Y' Z : Type*} (eX : X' → X) (eY : Y' → Y)
    (P : Protocol X Y Z) (x : X') (y : Y') :
    (reindexP eX eY P).eval x y = P.eval (eX x) (eY y) := by
  induction P with
  | leaf z => rfl
  | aNode a l r ihl ihr => simp only [reindexP, Protocol.eval, ihl, ihr]
  | bNode b l r ihl ihr => simp only [reindexP, Protocol.eval, ihl, ihr]

theorem D_reindex {X Y X' Y' Z : Type*} [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (eX : X' ≃ X) (eY : Y' ≃ Y) (f : X → Y → Z) :
    D (fun x y => f (eX x) (eY y)) = D f := by
  unfold D AchievableCosts
  congr 1
  apply Set.eq_of_subset_of_subset
  · rintro c ⟨P, hcost, hcomp⟩
    refine ⟨reindexP eX.symm eY.symm P, ?_, ?_⟩
    · rw [cost_reindexP]; exact hcost
    · intro x y
      rw [eval_reindexP, hcomp]
      simp
  · rintro c ⟨P, hcost, hcomp⟩
    refine ⟨reindexP eX eY P, ?_, ?_⟩
    · rw [cost_reindexP]; exact hcost
    · intro x y
      rw [eval_reindexP]
      exact hcomp (eX x) (eY y)

/-! ### Interlace bridge -/

theorem D_interlace_bridge (M : BoolMat) (B l : ℕ) (hm : 0 < M.m) (hn : 0 < M.n) :
    D (directSum (interlace M B).e l)
      = D (directSum (interlaceFun M.e B) l) := by
  classical
  haveI : NeZero M.m := ⟨hm.ne'⟩
  haveI : NeZero M.n := ⟨hn.ne'⟩
  have hmQ : M.m * B = B * M.m := Nat.mul_comm _ _
  let eRow0 : Fin (M.m * B) ≃ Fin B × Fin M.m :=
    (finCongr hmQ).trans finProdFinEquiv.symm
  let eCol0 : Fin (M.n ^ B) ≃ (Fin B → Fin M.n) := finFunctionFinEquiv.symm
  let eX : (Fin l → Fin (M.m * B)) ≃ (Fin l → Fin B × Fin M.m) := Equiv.piCongrRight (fun _ => eRow0)
  let eY : (Fin l → Fin (M.n ^ B)) ≃ (Fin l → Fin B → Fin M.n) := Equiv.piCongrRight (fun _ => eCol0)
  have hkey := D_reindex eX eY (directSum (interlaceFun M.e B) l)
  rw [← hkey]
  congr 1

/-! ### Numeric bound -/

theorem nat_pow_bound : (255 : ℕ) ^ 178 ≤ (2 : ℕ) ^ 1423 := by
  have h2 : (2:ℕ) * 255 ^ 178 ≤ 256 ^ 178 := by norm_num
  have h3 : (256 : ℕ) ^ 178 = 2 ^ 1424 := by
    rw [show (256:ℕ) = 2 ^ 8 by norm_num, ← pow_mul]
  have h4 : (2:ℕ) ^ 1424 = 2 * 2 ^ 1423 := by rw [pow_succ]; ring
  omega

theorem logb255_bound : (178 : ℝ) * Real.logb 2 255 ≤ 1423 := by
  have hnat : (255 : ℝ) ^ (178 : ℕ) ≤ (2 : ℝ) ^ (1423 : ℕ) := by
    exact_mod_cast nat_pow_bound
  have he : (178 : ℝ) * Real.logb 2 255 = Real.logb 2 ((255:ℝ)^(178:ℕ)) := by
    rw [Real.logb_pow]; ring
  rw [he]
  rw [show (1423 : ℝ) = ((1423 : ℕ) : ℝ) by norm_num]
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity)]
  rw [Real.rpow_natCast]
  exact hnat

theorem numeric (h : ℕ) (hh : 1 ≤ h) :
    ⌈(178 * h : ℝ) * Real.logb 2 ((Q : ℕ) : ℝ)⌉₊ ≤ 178 * 10000 * h - h := by
  have hQ : ((Q : ℕ) : ℝ) = (255 : ℝ) * (2 : ℝ) ^ (9992 : ℕ) := by
    simp only [Q]
    push_cast
    norm_num
  have hlog : Real.logb 2 ((Q : ℕ) : ℝ) = Real.logb 2 255 + 9992 := by
    rw [hQ, Real.logb_mul (by norm_num) (by positivity), Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
    ring
  rw [hlog]
  have htar : 178 * 10000 * h - h = 1778576 * h + 1423 * h := by omega
  rw [htar]
  rw [Nat.ceil_le]
  push_cast
  have hexp : (178 * (h:ℝ)) * (Real.logb 2 255 + 9992)
      = 178 * (h:ℝ) * Real.logb 2 255 + 1778576 * h := by ring
  rw [hexp]
  have hb := logb255_bound
  have hh' : (0:ℝ) ≤ (h:ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hb hh']

/-! ### Positivity of φ dimensions -/

theorem phi_dims_pos (i : ℕ) : 0 < (phi Q i).m ∧ 0 < (phi Q i).n := by
  induction i with
  | zero => exact ⟨by norm_num, by norm_num⟩
  | succ k ih =>
      obtain ⟨hm, hn⟩ := ih
      rw [phi_succ]
      -- (interlace (phi Q k) Q).transpose has m = (interlace ..).n = (phi Q k).n ^ Q,
      -- n = (interlace ..).m = (phi Q k).m * Q
      simp only [BoolMat.transpose_m, BoolMat.transpose_n, interlace]
      refine ⟨?_, ?_⟩
      · exact pow_pos hn Q
      · exact Nat.mul_pos hm (by norm_num [Q] : 0 < Q)

/-! ### Corollary 5.8 -/

theorem upper_bound_directSum_phi_5_8 (i h : ℕ) (hh : 1 ≤ h) :
    D (directSum (phi Q i).e (178 * h))
      ≤ 178 * h + i * (178 * 10000 * h - h) := by
  induction i with
  | zero =>
      simp only [Nat.zero_mul, Nat.add_zero]
      -- phi Q 0 : m = 1, n = 2, e = fun _ j => if j = 0 then true else false
      -- output depends only on Bob; use D_le_bob_bits with l = 178*h
      have hbob :
          D (directSum (phi Q 0).e (178 * h)) ≤ 178 * h := by
        apply D_le_bob_bits (l := 178 * h)
          (read := fun (b : Fin (178 * h) → Fin (phi Q 0).n) =>
            fun i => (phi Q 0).e (0 : Fin 1) (b i))
        intro a b
        funext k
        simp only [directSum]
        rfl
      exact hbob
  | succ k ih =>
      rw [phi_succ]
      -- Drop the transpose via observation_5_2.
      have htr : D (directSum ((interlace (phi Q k) Q).transpose).e (178 * h))
          = D (directSum (interlace (phi Q k) Q).e (178 * h)) := by
        have := observation_5_2 (interlace (phi Q k) Q).e (178 * h)
        rw [this]
        rfl
      rw [htr]
      -- Bridge to interlaceFun form.
      obtain ⟨hm, hn⟩ := phi_dims_pos k
      rw [D_interlace_bridge (phi Q k) Q (178 * h) hm hn]
      -- One-round upper bound.
      have hone := one_round_upper_bound_5_7 (phi Q k).e Q (178 * h)
      have hnum := numeric h hh
      have hcast : (⌈((178 * h : ℕ) : ℝ) * Real.logb 2 (Q : ℝ)⌉₊)
          = ⌈(178 * h : ℝ) * Real.logb 2 ((Q : ℕ) : ℝ)⌉₊ := by
        congr 1
        push_cast
        ring
      rw [hcast] at hone
      have hbound : D (directSum (interlaceFun (phi Q k).e Q) (178 * h))
          ≤ D (directSum (phi Q k).e (178 * h)) + (178 * 10000 * h - h) :=
        le_trans hone (Nat.add_le_add_left hnum _)
      -- Combine with IH.
      have : D (directSum (phi Q k).e (178 * h)) + (178 * 10000 * h - h)
          ≤ 178 * h + (k + 1) * (178 * 10000 * h - h) := by
        have := ih
        have hkey : 178 * h + k * (178 * 10000 * h - h) + (178 * 10000 * h - h)
            = 178 * h + (k + 1) * (178 * 10000 * h - h) := by ring
        omega
      exact le_trans hbound this

end Proof.UpperBound

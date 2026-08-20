import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.List.TFAE

open SimpleGraph

structure graph where
  V : Type
  G : SimpleGraph V

structure tec where
  V : Type
  red : SimpleGraph V
  blue : SimpleGraph V
  disjoint : ∀ u v, ¬ (red.Adj u v ∧ blue.Adj u v)

def tec_hom (A B : tec) : Prop :=
  ∃ f : A.V → B.V,
    (∀ u v, A.red.Adj u v → B.red.Adj (f u) (f v)) ∧
    (∀ u v, A.blue.Adj u v → B.blue.Adj (f u) (f v))

def tec_inj_hom (A B : tec) : Prop :=
  ∃ f : A.V → B.V, Function.Injective f ∧
    (∀ u v, A.red.Adj u v → B.red.Adj (f u) (f v)) ∧
    (∀ u v, A.blue.Adj u v → B.blue.Adj (f u) (f v))

def star (H : graph) : tec where
  V := H.V
  red := H.Gᶜ
  blue := H.G
  disjoint := by
    intro u v h
    exact ((SimpleGraph.compl_adj H.G u v).1 h.1).2 h.2

def csp (T : tec) : tec → Prop :=
  fun A => Finite A.V ∧ tec_hom A T

def inj_csp (T : tec) : tec → Prop :=
  fun A => Finite A.V ∧ tec_inj_hom A T

def sp (C : graph → Prop) : tec → Prop :=
  fun A => Finite A.V ∧ ∃ E' : SimpleGraph A.V,
    (∀ u v, A.blue.Adj u v → E'.Adj u v) ∧
    (∀ u v, E'.Adj u v → ¬ A.red.Adj u v) ∧
    C ⟨A.V, E'⟩

def iso_closed (C : graph → Prop) : Prop :=
  ∀ G H : graph, Nonempty (G.G ≃g H.G) → C G → C H

def hereditary (C : graph → Prop) : Prop :=
  ∀ (G : graph) (s : Set G.V), Finite G.V → C G → C ⟨_, G.G.induce s⟩

def jep (C : graph → Prop) : Prop :=
  ∀ G H : graph, Finite G.V → Finite H.V → C G → C H →
    ∃ F : graph, Finite F.V ∧ C F ∧ Nonempty (G.G ↪g F.G) ∧ Nonempty (H.G ↪g F.G)

def split_blow_up (G : graph) (twin : G.V → Prop) (β : G.V → Type) :
    SimpleGraph (Σ u, β u) :=
  SimpleGraph.fromRel (fun p q =>
    (p.1 = q.1 ∧ ¬ twin p.1) ∨ (p.1 ≠ q.1 ∧ G.G.Adj p.1 q.1))

def preserved_split_blow_up (C : graph → Prop) : Prop :=
  ∀ G : graph, Finite G.V → C G → ∃ twin : G.V → Prop,
    ∀ β : G.V → Type, (∀ u, Finite (β u)) → (∀ u, Nonempty (β u)) →
      C ⟨_, split_blow_up G twin β⟩

theorem sp_csp_tfae (C : graph → Prop) (hiso : iso_closed C)
    (hne : ∃ G : graph, Finite G.V ∧ C G) :
    List.TFAE
      [ hereditary C ∧ jep C ∧ preserved_split_blow_up C,
        ∃ T : tec, csp T = sp C,
        ∃ H : graph, sp C = csp (star H) ∧ csp (star H) = inj_csp (star H) ] := by sorry

import Mathlib.Logic.Function.Iterate
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.Order.Floor.Defs

open scoped ENNReal

def apply_append (f : List Bool → Bool) (x : List Bool) : List Bool :=
  x ++ [f x]

def cot_trace (f : List Bool → Bool) (T : ℕ) (x : List Bool) : List Bool :=
  (apply_append f)^[T] x

def end_to_end (f : List Bool → Bool) (T : ℕ) (x : List Bool) : Bool :=
  (cot_trace f T x).getLastD false

def trace_input (T : ℕ) (z : List Bool) : List Bool :=
  z.take (z.length - T)

def class_shatters {Z : Type*} (G : Set (Z → Bool)) (s : Finset Z) : Prop :=
  ∀ b : Z → Bool, ∃ g ∈ G, ∀ z ∈ s, g z = b z

noncomputable def vc_dim {Z : Type*} (G : Set (Z → Bool)) : ℕ∞ :=
  sSup {n : ℕ∞ | ∃ s : Finset Z, class_shatters G s ∧ (s.card : ℕ∞) = n}

noncomputable def iid_sample {X : Type*} (D : PMF X) : (m : ℕ) → PMF (Fin m → X)
  | 0 => PMF.pure (fun i => Fin.elim0 i)
  | m + 1 => D.bind fun x => (iid_sample D m).map (fun s => Fin.cons x s)

noncomputable def cot_loss (D : PMF (List Bool)) (fstar : List Bool → Bool) (T : ℕ)
    (h : List Bool → Bool) : ENNReal :=
  D.toOuterMeasure {x : List Bool | h x ≠ end_to_end fstar T x}

def cot_consistent_rule (F : Set (List Bool → Bool)) (T m : ℕ)
    (A : (Fin m → List Bool) → (List Bool → Bool)) : Prop :=
  ∀ z : Fin m → List Bool,
    (∃ f ∈ F, ∀ i, cot_trace f T (trace_input T (z i)) = z i) →
      ∃ f ∈ F, A z = end_to_end f T ∧ ∀ i, cot_trace f T (trace_input T (z i)) = z i

def cot_learnable_with (F : Set (List Bool → Bool)) (T : ℕ) (m : ℝ → ℝ → ℕ) : Prop :=
  ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    ∀ A : (Fin (m ε δ) → List Bool) → (List Bool → Bool), cot_consistent_rule F T (m ε δ) A →
      ∀ (D : PMF (List Bool)) (fstar : List Bool → Bool), fstar ∈ F →
        (iid_sample D (m ε δ)).toOuterMeasure
            {x : Fin (m ε δ) → List Bool |
              ENNReal.ofReal ε < cot_loss D fstar T (A (fun i => cot_trace fstar T (x i)))}
          ≤ ENNReal.ofReal δ

noncomputable def cot_sample_bound (c : ℝ) (d T : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈c * (ε⁻¹ * ((d : ℝ) * Real.log (2 * (T : ℝ)) * Real.log (12 / ε) + Real.log (2 / δ)))⌉₊

theorem cot_VC :
    ∃ c : ℝ, 0 < c ∧ ∀ (F : Set (List Bool → Bool)) (T d : ℕ), 0 < T →
      vc_dim F ≤ (d : ℕ∞) → cot_learnable_with F T (cot_sample_bound c d T) := by sorry

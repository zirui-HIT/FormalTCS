import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Logic.Equiv.Fin.Basic

set_option linter.all false

abbrev csp_relation (D : Type*) (r : ℕ) := Set (Fin r → D)

abbrev csp_clause (r n : ℕ) := Fin r → Fin n

abbrev csp_instance (r n : ℕ) := Finset (csp_clause r n)

def csp_satisfies_clause {D : Type*} {r n : ℕ}
    (R : csp_relation D r) (σ : Fin n → D) (c : csp_clause r n) : Prop :=
  (fun i => σ (c i)) ∈ R

def csp_solutions {D : Type*} {r n : ℕ}
    (R : csp_relation D r) (Y : csp_instance r n) : Set (Fin n → D) :=
  {σ | ∀ c ∈ Y, csp_satisfies_clause R σ c}

def csp_nonredundant {D : Type*} {r n : ℕ}
    (R : csp_relation D r) (Y : csp_instance r n) : Prop :=
  ∀ c ∈ Y, csp_solutions R Y ⊂ csp_solutions R (Y.erase c)

noncomputable def nrd {D : Type*} {r : ℕ} (R : csp_relation D r) (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ Y : csp_instance r n, csp_nonredundant R Y ∧ Y.card = k}

def relation_nontrivial {D : Type*} {r : ℕ} (R : csp_relation D r) : Prop :=
  R.Nonempty ∧ ∃ t : Fin r → D, t ∉ R

abbrev ordp_domain (q : ℕ) := Bool ⊕ (Fin q → Bool)

def ordp_index (p q : ℕ) (j : Fin (p ^ q)) : Fin q → Fin p :=
  finFunctionFinEquiv.symm j

def or_direct_product_relation (p q : ℕ) :
    csp_relation (ordp_domain q) (p + p ^ q) :=
  {t | ∃ x : Fin p → Bool,
    (∀ i : Fin p, t (Fin.castAdd (p ^ q) i) = Sum.inl (x i)) ∧
    (∀ j : Fin (p ^ q),
      t (Fin.natAdd p j) = Sum.inr (fun k => x (ordp_index p q j k))) ∧
    ∃ i : Fin p, x i = true}

noncomputable def nrd_growth {D : Type*} {r : ℕ}
    (R : csp_relation D r) (n : ℕ) : ℝ :=
  (nrd R n : ℝ)

noncomputable def power_growth (a : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ a

def has_theta_nrd {D : Type*} {r : ℕ} (R : csp_relation D r) (a : ℝ) : Prop :=
  Asymptotics.IsTheta Filter.atTop (nrd_growth R) (power_growth a)

def admissible_nrd_exponent {D : Type*} {r : ℕ}
    (R : csp_relation D r) (a : ℝ) : Prop :=
  1 ≤ a ∧ ∀ ε : ℝ, 0 < ε →
    Asymptotics.IsBigO Filter.atTop (nrd_growth R) (power_growth (a + ε))

noncomputable def nrd_exponent {D : Type*} {r : ℕ}
    (R : csp_relation D r) : ℝ :=
  sInf {a : ℝ | admissible_nrd_exponent R a}

theorem frac_nrd (p q : ℕ) (hq : 0 < q) (hpq : q ≤ p) :
    ∃ R : csp_relation (ordp_domain q) (p + p ^ q),
      R = or_direct_product_relation p q ∧
      relation_nontrivial R ∧
      nrd_exponent R = (p : ℝ) / (q : ℝ) ∧
      has_theta_nrd R ((p : ℝ) / (q : ℝ)) := by sorry

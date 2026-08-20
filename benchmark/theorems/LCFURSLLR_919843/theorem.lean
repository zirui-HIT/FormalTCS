import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi

set_option linter.all false
set_option maxHeartbeats 500000

abbrev cnf_variable (n : ℕ) := Fin n

abbrev cnf_assignment (n : ℕ) := cnf_variable n → Bool

abbrev cnf_literal (n : ℕ) := cnf_variable n × Bool

abbrev cnf_clause (n : ℕ) := Finset (cnf_literal n)

abbrev cnf_formula (n : ℕ) := Finset (cnf_clause n)

noncomputable def cnf_clause_variables {n : ℕ} (c : cnf_clause n) : Finset (cnf_variable n) := by
  classical
  exact c.image Prod.fst

def cnf_clause_satisfied {n : ℕ} (c : cnf_clause n) (x : cnf_assignment n) : Prop :=
  ∃ literal ∈ c, x literal.1 = literal.2

def cnf_formula_satisfied {n : ℕ} (φ : cnf_formula n) (x : cnf_assignment n) : Prop :=
  ∀ c ∈ φ, cnf_clause_satisfied c x

def cnf_exact_k_clause {n : ℕ} (k : ℕ) (c : cnf_clause n) : Prop :=
  c.card = k ∧ (cnf_clause_variables c).card = k

noncomputable def cnf_variable_degree {n : ℕ} (φ : cnf_formula n) (v : cnf_variable n) : ℕ := by
  classical
  exact (φ.filter fun c => v ∈ cnf_clause_variables c).card

def cnf_is_kds {n : ℕ} (φ : cnf_formula n) (k d s : ℕ) : Prop :=
  (∀ c ∈ φ, cnf_exact_k_clause k c) ∧
    (∀ v : cnf_variable n, cnf_variable_degree φ v ≤ d) ∧
      (∀ c₁ ∈ φ, ∀ c₂ ∈ φ, c₁ ≠ c₂ →
        ((cnf_clause_variables c₁) ∩ (cnf_clause_variables c₂)).card ≤ s)

noncomputable def all_k_clauses (n k : ℕ) : Finset (cnf_clause n) := by
  classical
  exact Finset.univ.filter (cnf_exact_k_clause k)

noncomputable def valiant_learner {n T : ℕ} (k : ℕ)
    (samples : Fin T → cnf_assignment n) : cnf_formula n := by
  classical
  exact (all_k_clauses n k).filter fun c => ∀ i, cnf_clause_satisfied c (samples i)

def cnf_exactly_learns {n : ℕ} (φ learned : cnf_formula n) : Prop :=
  ∀ x : cnf_assignment n, cnf_formula_satisfied φ x ↔ cnf_formula_satisfied learned x

noncomputable def solution_sample_vectors {n : ℕ} (φ : cnf_formula n) (T : ℕ) :
    Finset (Fin T → cnf_assignment n) := by
  classical
  exact Finset.univ.filter fun samples => ∀ i, cnf_formula_satisfied φ (samples i)

noncomputable def valiant_success_probability {n : ℕ} (φ : cnf_formula n) (k T : ℕ) : ℝ := by
  classical
  exact
    (((solution_sample_vectors φ T).filter fun samples =>
      cnf_exactly_learns φ (valiant_learner k samples)).card : ℝ) /
      ((solution_sample_vectors φ T).card : ℝ)

noncomputable def sublinear_intersection_scale (η : ℝ) (k s : ℕ) : Prop :=
  (s : ℝ) = Real.rpow (k : ℝ) (1 - η)

noncomputable def cnf_local_lemma_regime
    (lowerOrder : ℕ → ℝ) (etaConstant : ℝ → ℝ)
    (η : ℝ) (k d : ℕ) : Prop :=
  Real.logb 2 (d : ℝ) + lowerOrder k + etaConstant η ≤ (k : ℝ)

def valiant_work (n k T : ℕ) : ℕ :=
  (2 ^ k * Nat.choose n k) * T

def valiant_learning_guarantee
    (η : ℝ) (lowerOrder : ℕ → ℝ) (etaConstant : ℝ → ℝ) : Prop :=
  Asymptotics.IsLittleO Filter.atTop lowerOrder (fun m : ℕ => (m : ℝ)) ∧
    ∀ k : ℕ,
      0 < k →
      ∃ sampleConstant runtimeConstant : ℝ,
        0 < sampleConstant ∧
          0 < runtimeConstant ∧
            ∀ (n d s : ℕ) (φ : cnf_formula n) (δ : ℝ),
              0 < n →
              (∃ x : cnf_assignment n, cnf_formula_satisfied φ x) →
              0 < δ →
              δ < 1 →
              sublinear_intersection_scale η k s →
              cnf_local_lemma_regime lowerOrder etaConstant η k d →
              cnf_is_kds φ k d s →
              ∃ T : ℕ,
                0 < T ∧
                  (T : ℝ) ≤ sampleConstant *
                      (1 + Real.logb 2 ((n : ℝ) / δ)) ∧
                    1 - δ ≤ valiant_success_probability φ k T ∧
                      (valiant_work n k T : ℝ) ≤
                        runtimeConstant * (n : ℝ) ^ k *
                          Real.logb 2 ((n : ℝ) / δ)

theorem learning_sublinear_intersection
    (η : ℝ) (hη : η ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ (lowerOrder : ℕ → ℝ) (etaConstant : ℝ → ℝ),
      valiant_learning_guarantee η lowerOrder etaConstant := by sorry

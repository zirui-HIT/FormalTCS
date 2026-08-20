import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

set_option linter.all false
set_option maxHeartbeats 500000

abbrev mdl_concept_class (X Y : Type*) := Set (X → Y)

def mdl_set_shatters {X : Type*} (C : mdl_concept_class X Bool) (W : Set X) : Prop :=
  ∀ W' ⊆ W, ∃ f ∈ C, f ⁻¹' {true} ∩ W = W'

noncomputable def mdl_vc_dim {X : Type*} (C : mdl_concept_class X Bool) : ℕ :=
  sSup {n : ℕ | ∃ W : Finset X, W.card = n ∧ mdl_set_shatters C (↑W)}

def mdl_has_finite_vc_dim {X : Type*} (C : mdl_concept_class X Bool) : Prop :=
  BddAbove {n : ℕ | ∃ W : Finset X, W.card = n ∧ mdl_set_shatters C (↑W)}

inductive mdl_sampling_tree (I S O : Type*) : ℕ → Type _ where
  | output {m : ℕ} (result : O) : mdl_sampling_tree I S O m
  | query {m : ℕ} (source : I) (next : S → mdl_sampling_tree I S O m) :
      mdl_sampling_tree I S O (m + 1)
  | randomize {m : ℕ} (coin : PMF Bool) (next : Bool → mdl_sampling_tree I S O m) :
      mdl_sampling_tree I S O m

noncomputable def mdl_sampling_tree_eval {I S O : Type*} (D : I → PMF S) :
    {m : ℕ} → mdl_sampling_tree I S O m → PMF O
  | _, .output result => PMF.pure result
  | _, .query source next =>
      PMF.bind (D source) (fun sample => mdl_sampling_tree_eval D (next sample))
  | _, .randomize coin next =>
      PMF.bind coin (fun bit => mdl_sampling_tree_eval D (next bit))

noncomputable def fixed_rcn_distribution {X : Type*} (μ : PMF X) (target : X → Bool) :
    PMF (X × Bool) :=
  PMF.bind μ (fun x =>
    PMF.map (fun noise => (x, Bool.xor (target x) noise))
      (PMF.bernoulli (1 / 4) (by
        apply (div_le_one (show (0 : NNReal) < 4 by norm_num)).2
        norm_num)))

def source_indexed_fixed_rcn_family {X : Type*} {k : ℕ}
    (C : mdl_concept_class X Bool) (D : Fin k → PMF (X × Bool)) : Prop :=
  ∃ targets : Fin k → X → Bool, (∀ i, targets i ∈ C) ∧
    ∃ features : Fin k → PMF X,
      ∀ i, D i = fixed_rcn_distribution (features i) (targets i)

noncomputable def pmf_prediction_error {X : Type*} (D : PMF (X × Bool))
    (h : X → Bool) : ENNReal :=
  D.toOuterMeasure {z | h z.1 ≠ z.2}

noncomputable def pmf_optimal_error {X : Type*} (D : PMF (X × Bool))
    (C : mdl_concept_class X Bool) : ENNReal :=
  ⨅ f ∈ C, pmf_prediction_error D f

def personalized_mdl_objective {X : Type*} {k : ℕ} (C : mdl_concept_class X Bool)
    (D : Fin k → PMF (X × Bool)) (ε : ℝ) (output : Fin k → X → Bool) : Prop :=
  ∀ i, pmf_prediction_error (D i) (output i) ≤
    pmf_optimal_error (D i) C + ENNReal.ofReal ε

structure mdl_algorithm (X : Type*) (C : mdl_concept_class X Bool) where
  sampleComplexity : ℕ → ℝ → ℝ → ℕ
  run : (k : ℕ) → (ε δ : ℝ) →
    mdl_sampling_tree (Fin k) (X × Bool) (Fin k → X → Bool)
      (sampleComplexity k ε δ)

def is_mdl_algorithm {X : Type*} {C : mdl_concept_class X Bool}
    (A : mdl_algorithm X C) : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ (D : Fin k → PMF (X × Bool)),
    source_indexed_fixed_rcn_family C D →
    ∀ (ε δ : ℝ),
      0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ENNReal.ofReal (1 - δ) ≤
        (mdl_sampling_tree_eval D (A.run k ε δ)).toOuterMeasure
          {output | personalized_mdl_objective C D ε output}

def admissible_mdl_parameters (d k : ℕ) (ε δ : ℝ) : Prop :=
  0 < k ∧ 0 < ε ∧ ε < 1 ∧ 0 < δ ∧ δ ≤ 0.01 / 3 ∧
    384 * ε ≤ (d : ℝ) ∧ 4 * 10 ^ 7 ≤ min (d : ℝ) (1 / ε)

noncomputable def mdl_lower_bound_rate (d k : ℕ) (ε : ℝ) : ℝ :=
  (d : ℝ) / ε + (k : ℝ) * min (1 / ε ^ 2) ((d : ℝ) / ε)

def has_mdl_rate_lower_bound {X : Type*} {C : mdl_concept_class X Bool}
    (c : ℝ) (A : mdl_algorithm X C) (d : ℕ) : Prop :=
  ∀ (k : ℕ) (ε δ : ℝ),
    admissible_mdl_parameters d k ε δ →
      c * mdl_lower_bound_rate d k ε ≤ (A.sampleComplexity k ε δ : ℝ)

theorem mdl_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ {X : Type*} {C : mdl_concept_class X Bool} (d : ℕ),
        mdl_has_finite_vc_dim C → mdl_vc_dim C = d →
          ∀ (A : mdl_algorithm X C), is_mdl_algorithm A →
            has_mdl_rate_lower_bound c A d := by sorry

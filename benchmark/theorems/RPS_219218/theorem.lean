import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Order.Real

set_option linter.all false
set_option maxHeartbeats 500000

noncomputable def bernoulli_kl (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

def dense_probability_sequence (r : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in Filter.atTop, c ≤ r n

def graph_copy {V : Type} (template image : SimpleGraph V) : Prop :=
  ∃ e : V ≃ V, template.map e.toEmbedding = image

noncomputable def graph_relative_density {V : Type} [Fintype V] [DecidableEq V]
    (larger smaller : SimpleGraph V) : ENNReal := by
  classical
  exact ((larger.edgeFinset \ smaller.edgeFinset).card : ENNReal) /
    (((larger.support \ smaller.support).toFinset.card : ℕ) : ENNReal)

noncomputable def minimal_maximum_subgraph_density {V : Type} [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) : ENNReal :=
  ⨅ S : SimpleGraph V, ⨅ (_ : S < Γ),
    ⨆ F : SimpleGraph V, ⨆ (_ : S < F ∧ F ≤ Γ), graph_relative_density F S

structure onion_decomposition {V : Type} [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) where
  steps : ℕ
  layer : Fin (steps + 1) → SimpleGraph V
  initial : layer ⟨0, Nat.zero_lt_succ steps⟩ = ⊥
  final : layer (Fin.last steps) = Γ
  strict_step : ∀ i : Fin steps, layer i.castSucc < layer i.succ
  contained : ∀ i : Fin (steps + 1), layer i ≤ Γ
  maximizes : ∀ (i : Fin steps) (H : SimpleGraph V),
    layer i.castSucc < H → H ≤ Γ →
      graph_relative_density H (layer i.castSucc) ≤
        graph_relative_density (layer i.succ) (layer i.castSucc)
  maximal : ∀ (i : Fin steps) (H : SimpleGraph V),
    layer i.succ < H → H ≤ Γ →
      graph_relative_density H (layer i.castSucc) <
        graph_relative_density (layer i.succ) (layer i.castSucc)

def onion_full_overlap_rigid {V : Type} [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) : Prop :=
  ∀ (D : onion_decomposition Γ) (i : Fin D.steps)
    (base planted candidate : SimpleGraph V),
    graph_copy (D.layer i.castSucc) base →
    graph_copy (D.layer i.succ) planted →
    graph_copy (D.layer i.succ) candidate →
    base ≤ planted →
    base ≤ candidate →
    candidate.support \ base.support = planted.support \ base.support →
    candidate.edgeSet = planted.edgeSet

noncomputable def peeling_score {V : Type} [Fintype V] [DecidableEq V]
    (observed base extension : SimpleGraph V) : ℕ := by
  classical
  exact (((extension.edgeFinset \ base.edgeFinset) ∩ observed.edgeFinset).card)

def graph_estimator : Type :=
  (n : ℕ) → SimpleGraph (Fin n) → SimpleGraph (Fin n)

def is_likelihood_peeling (Γ : (n : ℕ) → SimpleGraph (Fin n))
    (estimate : graph_estimator) : Prop :=
  ∀ n : ℕ,
    ∃ D : onion_decomposition (Γ n),
    ∀ observed : SimpleGraph (Fin n),
    ∃ selected : Fin (D.steps + 1) → SimpleGraph (Fin n),
      selected ⟨0, Nat.zero_lt_succ D.steps⟩ = ⊥ ∧
      selected (Fin.last D.steps) = estimate n observed ∧
      ∀ i : Fin D.steps,
        graph_copy (D.layer i.succ) (selected i.succ) ∧
        selected i.castSucc ≤ selected i.succ ∧
        ∀ candidate : SimpleGraph (Fin n),
          graph_copy (D.layer i.succ) candidate →
          selected i.castSucc ≤ candidate →
          peeling_score observed (selected i.castSucc) candidate ≤
            peeling_score observed (selected i.castSucc) (selected i.succ)

noncomputable def planted_graph_weight {V : Type} [Fintype V] [DecidableEq V]
    (hidden observed : SimpleGraph V) (p q : ℝ) : ℝ := by
  classical
  exact ∏ e ∈ (⊤ : SimpleGraph V).edgeFinset,
    if e ∈ observed.edgeFinset then
      if e ∈ hidden.edgeFinset then p else q
    else
      if e ∈ hidden.edgeFinset then 1 - p else 1 - q

noncomputable def planted_event_probability {V : Type} [Fintype V] [DecidableEq V]
    (hidden : SimpleGraph V) (p q : ℝ) (event : SimpleGraph V → Prop) : ENNReal := by
  classical
  exact ∑ observed : SimpleGraph V,
    if event observed then ENNReal.ofReal (planted_graph_weight hidden observed p q) else 0

noncomputable def worst_case_recovery_error (Γ : (n : ℕ) → SimpleGraph (Fin n))
    (p q : ℕ → ℝ) (estimate : graph_estimator) (n : ℕ) : ENNReal :=
  ⨆ hidden : SimpleGraph (Fin n), ⨆ (_ : graph_copy (Γ n) hidden),
    planted_event_probability hidden (p n) (q n) (fun observed => estimate n observed ≠ hidden)

def exact_recovery (Γ : (n : ℕ) → SimpleGraph (Fin n))
    (p q : ℕ → ℝ) (estimate : graph_estimator) : Prop :=
  Filter.Tendsto (worst_case_recovery_error Γ p q estimate) Filter.atTop (nhds 0)

theorem optimal_algorithm :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Γ : (n : ℕ) → SimpleGraph (Fin n)) (p q : ℕ → ℝ)
        (estimate : graph_estimator) (ε : ℝ),
        (∀ n, 0 < q n ∧ q n < p n ∧ p n ≤ 1) →
        dense_probability_sequence p →
        dense_probability_sequence q →
        is_likelihood_peeling Γ estimate →
        (∀ᶠ n : ℕ in Filter.atTop, onion_full_overlap_rigid (Γ n)) →
        0 < ε →
        (∀ᶠ n : ℕ in Filter.atTop,
          ENNReal.ofReal
              (C * (1 + ε) * Real.log (n : ℝ) / bernoulli_kl (p n) (q n)) ≤
            minimal_maximum_subgraph_density (Γ n)) →
        exact_recovery Γ p q estimate := by sorry

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Monad

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory
open scoped Topology

abbrev graph_state (n : ℕ) := Finset (Fin n)

noncomputable def independent_set_support {n : ℕ} (G : SimpleGraph (Fin n)) :
    Finset (graph_state n) := by
  classical
  exact Finset.univ.filter fun S => G.IsIndepSet (S : Set (Fin n))

noncomputable def hardcore_measure {n : ℕ} (G : SimpleGraph (Fin n)) :
    PMF (graph_state n) :=
  PMF.uniformOfFinset (independent_set_support G) (by
    classical
    refine ⟨∅, ?_⟩
    simp [independent_set_support, SimpleGraph.IsIndepSet])

noncomputable def erdos_renyi_half (n : ℕ) : Measure (SimpleGraph (Fin n)) :=
  SimpleGraph.binomialRandom (V := Fin n)
    (p := ⟨(1 / 2 : ℝ), by norm_num⟩)

noncomputable def logarithmic_target_size (n : ℕ) : ℕ :=
  Int.toNat
    (⌊Real.log (n : ℝ) / Real.log 2 -
      30 * (Real.log (Real.log (n : ℝ) / Real.log 2) / Real.log 2)⌋ : ℤ)

noncomputable def glauber_time_budget (n k : ℕ) : ℕ :=
  Int.toNat (⌊100 * Real.log (n : ℝ) * (2 : ℝ) ^ k⌋ : ℤ)

def indicator_vector {n : ℕ} (S : graph_state n) (i : Fin n) : ℝ :=
  if i ∈ S then 1 else 0

noncomputable def pmf_expectation {α : Type*} [Fintype α] (μ : PMF α)
    (f : α → ℝ) : ℝ :=
  ∑ x, (μ x).toReal * f x

noncomputable def normalization_scale {n : ℕ} (μ : PMF (graph_state n)) : ℝ :=
  Real.sqrt (pmf_expectation μ fun S => ∑ i, indicator_vector S i ^ 2)

def pmf_coupling {α β : Type*} (π : PMF (α × β)) (μ : PMF α) (ν : PMF β) : Prop :=
  π.map Prod.fst = μ ∧ π.map Prod.snd = ν

noncomputable def normalized_coupling_cost {n : ℕ} (μ ν : PMF (graph_state n))
    (π : PMF (graph_state n × graph_state n)) : ℝ :=
  pmf_expectation π fun ST =>
    ∑ i, (indicator_vector ST.1 i / normalization_scale μ -
      indicator_vector ST.2 i / normalization_scale ν) ^ 2

noncomputable def normalized_wasserstein {n : ℕ} (μ ν : PMF (graph_state n)) : ℝ :=
  Real.sqrt (sInf {c : ℝ | ∃ π : PMF (graph_state n × graph_state n),
    pmf_coupling π μ ν ∧ c = normalized_coupling_cost μ ν π})

noncomputable def glauber_update {n : ℕ} (G : SimpleGraph (Fin n)) (S : graph_state n)
    (v : Fin n) (b : Bool) : graph_state n := by
  classical
  exact if b then
    if G.IsIndepSet ((insert v S : graph_state n) : Set (Fin n)) then insert v S else S
  else
    S.erase v

noncomputable def glauber_step {n : ℕ} (G : SimpleGraph (Fin n)) (S : graph_state n) :
    PMF (graph_state n) :=
  if hn : n = 0 then
    PMF.pure S
  else
    letI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    (PMF.uniformOfFintype (Fin n × Bool)).map fun vb =>
      glauber_update G S vb.1 vb.2

noncomputable def stopped_glauber_run {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    ℕ → PMF (graph_state n)
  | 0 => PMF.pure ∅
  | t + 1 => (stopped_glauber_run G k t).bind fun S =>
      if S.card = k then PMF.pure S else glauber_step G S

noncomputable def glauber_output {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    PMF (graph_state n) :=
  stopped_glauber_run G k (glauber_time_budget n k)

theorem polynomial_time_sampling_wasserstein :
    ∃ failureBound errorBound : ℕ → ℝ,
      Filter.Tendsto failureBound Filter.atTop (𝓝 0) ∧
      Filter.Tendsto errorBound Filter.atTop (𝓝 0) ∧
      ∀ n : ℕ,
        (erdos_renyi_half n {G |
          normalized_wasserstein (hardcore_measure G)
            (glauber_output G (logarithmic_target_size n)) ≤ errorBound n}).toReal ≥
          1 - failureBound n := by sorry

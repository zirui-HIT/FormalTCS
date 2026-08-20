import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

def finite_edge (N : ℕ) := {e : Fin N × Fin N // e.1 < e.2}

noncomputable def edge_pair_state {Ω : Type*} {N : ℕ}
    (G₁ G₂ : Ω → SimpleGraph (Fin N)) (e : finite_edge N) (ω : Ω) : Bool × Bool := by
  classical
  exact (decide ((G₁ ω).Adj e.1.1 e.1.2), decide ((G₂ ω).Adj e.1.1 e.1.2))

def edge_pair_mass (q ρ : ℝ) : Bool × Bool → ℝ
  | (true, true) => q * (ρ + (1 - ρ) * q)
  | (true, false) => q * (1 - ρ) * (1 - q)
  | (false, true) => q * (1 - ρ) * (1 - q)
  | (false, false) => (1 - q) * (ρ + (1 - ρ) * (1 - q))

def is_correlated_erdos_renyi_pair {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (μ : Measure Ω) (q ρ : ℝ) (G₁ G₂ : Ω → SimpleGraph (Fin N)) : Prop :=
  iIndepFun (fun e : finite_edge N => edge_pair_state G₁ G₂ e) μ ∧
    ∀ e : finite_edge N, ∀ s : Bool × Bool,
      μ {ω | edge_pair_state G₁ G₂ e ω = s} = ENNReal.ofReal (edge_pair_mass q ρ s)

noncomputable def shortest_parent_set {N : ℕ} (G : SimpleGraph (Fin N))
    (root v : Fin N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun u => G.Adj u v ∧ G.dist root u + 1 = G.dist root v

noncomputable def local_parent_overlap {N : ℕ} (G₁ G₂ : SimpleGraph (Fin N))
    (root v : Fin N) : ℝ :=
  let P₁ := shortest_parent_set G₁ root v
  let P₂ := shortest_parent_set G₂ root v
  let denominator := max P₁.card P₂.card
  if denominator = 0 then 0 else ((P₁ ∩ P₂).card : ℝ) / denominator

noncomputable def optimal_shortest_path_overlap {N : ℕ}
    (G₁ G₂ : SimpleGraph (Fin N)) (root : Fin N) : ℝ :=
  if hN : N = 0 then 0
  else (∑ v : Fin N, local_parent_overlap G₁ G₂ root v) / N

noncomputable def poisson_overlap_function (a b : ℝ) : ℝ :=
  if a = 0 then 1
  else if b = 0 then 0
  else
    let μa := poissonMeasure a.toNNReal
    let μb := poissonMeasure b.toNNReal
    let μ := (μa.prod μa).prod μb
    let positiveZ : Set ((ℕ × ℕ) × ℕ) := {x | 0 < x.2}
    (∫ x : (ℕ × ℕ) × ℕ,
        (x.2 : ℝ) / ((max x.1.1 x.1.2 + x.2 : ℕ) : ℝ) ∂(μ.restrict positiveZ)) /
      (μb {z | 0 < z}).toReal

noncomputable def interior_overlap_limit (lam gam rho : ℝ) : ℝ :=
  ((1 - 2 * lam + Real.rpow lam (2 - gam)) / (1 - lam)) *
      Real.rpow lam (2 - gam) * rho +
    poisson_overlap_function ((1 - gam) * Real.log (1 / lam))
      (gam * Real.log (1 / lam)) * (1 - Real.rpow lam gam)

noncomputable def overlap_limit (lam gam rho : ℝ) : ℝ :=
  if 0 < lam ∧ lam < 1 then interior_overlap_limit lam gam rho else gam

structure correlated_shortest_path_tree_model (Ω : Type*) [MeasurableSpace Ω] where
  measure : Measure Ω
  probabilityMeasure : IsProbabilityMeasure measure
  alpha : ℕ → ℝ
  edgeProbability : ℕ → ℝ
  correlation : ℕ → ℝ
  lambdaProxy : ℕ → ℝ
  gammaProxy : ℕ → ℝ
  criticalDepth : ℕ → ℕ
  graphOne : (n : ℕ) → Ω → SimpleGraph (Fin (n + 1))
  graphTwo : (n : ℕ) → Ω → SimpleGraph (Fin (n + 1))
  graphLaw : ∀ n, is_correlated_erdos_renyi_pair measure
    (edgeProbability n) (correlation n) (graphOne n) (graphTwo n)
  edgeProbability_eq : ∀ n,
    edgeProbability n = alpha n * Real.log (n + 1 : ℝ) / (n + 1 : ℝ)
  alpha_eventually_bounded : ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    ∀ᶠ n in atTop, c ≤ alpha n ∧ alpha n ≤ C
  edgeProbability_mem : ∀ n, 0 ≤ edgeProbability n ∧ edgeProbability n ≤ 1
  correlation_mem : ∀ n, 0 < correlation n ∧ correlation n < 1
  lambdaProxy_mem : ∀ n, 0 < lambdaProxy n ∧ lambdaProxy n ≤ 1
  gammaProxy_mem : ∀ n, 0 < gammaProxy n ∧ gammaProxy n ≤ 1
  criticalDepth_spec : ∀ n : ℕ,
    let N : ℝ := n + 1
    let growth := N * edgeProbability n
    let threshold := N / (Real.log (Real.log N)) ^ 2
    threshold ≤ growth ^ criticalDepth n ∧
      (criticalDepth n = 0 ∨ growth ^ (criticalDepth n - 1) < threshold)
  lambdaProxy_spec : ∀ n,
    Real.log (1 / lambdaProxy n) =
      (((n + 1 : ℝ) * edgeProbability n) ^ criticalDepth n) / (n + 1 : ℝ)
  gammaProxy_spec : ∀ n,
    gammaProxy n = correlation n ^ criticalDepth n

noncomputable def model_overlap {Ω : Type*} [MeasurableSpace Ω]
    (M : correlated_shortest_path_tree_model Ω) (n : ℕ) (ω : Ω) : ℝ :=
  optimal_shortest_path_overlap (M.graphOne n ω) (M.graphTwo n ω)
    ⟨0, Nat.succ_pos n⟩

abbrev converges_in_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (c : ℝ) : Prop :=
  TendstoInMeasure μ X atTop (fun _ => c)

theorem main_overlap_limit {Ω : Type*} [MeasurableSpace Ω]
    (M : correlated_shortest_path_tree_model Ω) (lam gam rho : ℝ)
    (hLam : Tendsto M.lambdaProxy atTop (𝓝 lam))
    (hGam : Tendsto M.gammaProxy atTop (𝓝 gam))
    (hRho : Tendsto M.correlation atTop (𝓝 rho))
    (hLamMem : 0 ≤ lam ∧ lam ≤ 1) (hGamMem : 0 ≤ gam ∧ gam ≤ 1) :
    converges_in_probability M.measure (model_overlap M)
      (overlap_limit lam gam rho) := by sorry

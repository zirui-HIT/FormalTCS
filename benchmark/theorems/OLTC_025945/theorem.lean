import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Finset.Lattice.Fold

set_option linter.all false
set_option maxHeartbeats 500000

def outcome_cube {OutcomeDim : Type*} (y : OutcomeDim → ℝ) : Prop :=
  ∀ i, y i ∈ Set.Icc (0 : ℝ) 1

noncomputable def finite_sup_norm {OutcomeDim : Type*}
    [Fintype OutcomeDim] [Nonempty OutcomeDim] (v : OutcomeDim → ℝ) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty fun i => |v i|

structure oltc_agent (Action OutcomeDim : Type*) (J : ℕ) where
  utility : Action → (OutcomeDim → ℝ) →ₗ[ℝ] ℝ
  constraint : Fin J → Action → (OutcomeDim → ℝ) → ℝ

def admissible_agent {Action OutcomeDim : Type*} {J : ℕ}
    [Fintype OutcomeDim] [Nonempty OutcomeDim]
    (L : NNReal) (agent : oltc_agent Action OutcomeDim J) : Prop :=
  (∀ a y, outcome_cube y → agent.utility a y ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ j a y, outcome_cube y → agent.constraint j a y ∈ Set.Icc (-1 : ℝ) 1) ∧
      ∀ a y z, outcome_cube y → outcome_cube z →
        |agent.utility a y - agent.utility a z| ≤
          (L : ℝ) * finite_sup_norm (y - z)

noncomputable def benchmark_action_set {Action OutcomeDim : Type*} {J T : ℕ}
    [Fintype Action] (agent : oltc_agent Action OutcomeDim J)
    (outcomes : Fin T → OutcomeDim → ℝ) : Finset Action := by
  classical
  exact Finset.univ.filter fun a => ∀ t j, agent.constraint j a (outcomes t) ≤ 0

def action_count {Action : Type*} {T : ℕ} [DecidableEq Action]
    (played : Fin T → Action) (a : Action) : ℕ :=
  ∑ t, if played t = a then 1 else 0

def decision_calibrated {Action OutcomeDim : Type*} {T : ℕ}
    [DecidableEq Action] [Fintype OutcomeDim] [Nonempty OutcomeDim]
    (alpha : ℝ → ℝ) (predictions outcomes : Fin T → OutcomeDim → ℝ)
    (played : Fin T → Action) : Prop :=
  ∀ a,
    finite_sup_norm (∑ t, if played t = a then predictions t - outcomes t else 0) ≤
      alpha (action_count played a : ℝ)

def runs_elimination_algorithm {Action OutcomeDim : Type*} {J T : ℕ}
    [Fintype Action] [DecidableEq Action]
    (agent : oltc_agent Action OutcomeDim J)
    (outcomes predictions : Fin T → OutcomeDim → ℝ)
    (candidates : Fin T → Finset Action) (played : Fin T → Action) : Prop :=
  (∀ t, played t ∈ candidates t) ∧
    (∀ t a, a ∈ candidates t →
      agent.utility a (predictions t) ≤ agent.utility (played t) (predictions t)) ∧
      ∀ t, benchmark_action_set agent outcomes ⊆ candidates t

noncomputable def constrained_swap_regret {Action OutcomeDim : Type*} {T : ℕ}
    [Fintype Action] [DecidableEq Action]
    (utility : Action → (OutcomeDim → ℝ) →ₗ[ℝ] ℝ)
    (benchmark : Finset Action) (hBenchmark : benchmark.Nonempty)
    (played : Fin T → Action) (outcomes : Fin T → OutcomeDim → ℝ) : ℝ := by
  classical
  letI : Nonempty {a // a ∈ benchmark} := by
    obtain ⟨a, ha⟩ := hBenchmark
    exact ⟨⟨a, ha⟩⟩
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun phi : Action → {a // a ∈ benchmark} =>
      ∑ t, (utility (phi (played t)).1 (outcomes t) -
        utility (played t) (outcomes t)))

theorem swap_regret_realization
    {Action OutcomeDim : Type*} {J T : ℕ}
    [Fintype Action] [DecidableEq Action] [Nonempty Action]
    [Fintype OutcomeDim] [Nonempty OutcomeDim]
    (L : NNReal) (alpha : ℝ → ℝ)
    (agents : Set (oltc_agent Action OutcomeDim J))
    (predictions outcomes : Fin T → OutcomeDim → ℝ)
    (candidates : oltc_agent Action OutcomeDim J → Fin T → Finset Action)
    (played : oltc_agent Action OutcomeDim J → Fin T → Action)
    (hPredictions : ∀ t, outcome_cube (predictions t))
    (hOutcomes : ∀ t, outcome_cube (outcomes t))
    (hAgents : ∀ agent ∈ agents, admissible_agent L agent)
    (hAlpha : ConcaveOn ℝ (Set.univ : Set ℝ) alpha)
    (hRuns : ∀ agent ∈ agents,
      runs_elimination_algorithm agent outcomes predictions (candidates agent) (played agent))
    (hCalibration : ∀ agent ∈ agents,
      decision_calibrated alpha predictions outcomes (played agent))
    (hBenchmark : ∀ agent ∈ agents,
      (benchmark_action_set agent outcomes).Nonempty) :
    ∀ agent, ∀ hAgentMem : agent ∈ agents,
      constrained_swap_regret agent.utility (benchmark_action_set agent outcomes)
        (hBenchmark agent hAgentMem) (played agent) outcomes ≤
          2 * (L : ℝ) * (Fintype.card Action : ℝ) *
            alpha ((T : ℝ) / (Fintype.card Action : ℝ)) := by
  sorry

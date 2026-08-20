import Architect
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Finset.Lattice.Fold

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:outcome-cube"
  (statement := /-- For a coordinate type \(D\), the outcome cube is the set of vectors \(y \in \mathbb{R}^{D}\) whose coordinates all lie in \([0,1]\). -/)
  (title := /-- Outcome cube -/)
  (latexEnv := "definition")]
def outcome_cube {OutcomeDim : Type*} (y : OutcomeDim → ℝ) : Prop :=
  ∀ i, y i ∈ Set.Icc (0 : ℝ) 1

@[blueprint "def:finite-sup-norm"
  (statement := /-- For a nonempty finite coordinate type \(D\), the supremum norm of \(v\in\mathbb R^D\) is
  \[
    \lVert v\rVert_\infty=\max_{i\in D}|v_i|.
  \] -/)
  (title := /-- Supremum norm on finite outcome vectors -/)
  (latexEnv := "definition")]
noncomputable def finite_sup_norm {OutcomeDim : Type*}
    [Fintype OutcomeDim] [Nonempty OutcomeDim] (v : OutcomeDim → ℝ) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty fun i => |v i|

@[blueprint "def:oltc-agent"
  (statement := /-- An agent consists of a real-linear utility functional for each action and a family of \(J\) real-valued constraint functions. The linear maps are defined on the ambient outcome vector space; their restrictions to the outcome cube are the utilities appearing in the online problem. -/)
  (title := /-- Agent data -/)
  (latexEnv := "definition")]
structure oltc_agent (Action OutcomeDim : Type*) (J : ℕ) where
  utility : Action → (OutcomeDim → ℝ) →ₗ[ℝ] ℝ
  constraint : Fin J → Action → (OutcomeDim → ℝ) → ℝ

@[blueprint "def:admissible-agent"
  (statement := /-- Let \(D\) be a finite nonempty coordinate type and let \(L \geq 0\). An agent is \(L\)-admissible if every utility takes values in \([0,1]\) on the outcome cube, every constraint takes values in \([-1,1]\) there, and each utility is \(L\)-Lipschitz on that cube for the product supremum norm. Linearity is already part of the agent data. -/)
  (title := /-- Admissible linear and Lipschitz agents -/)
  (latexEnv := "definition")]
def admissible_agent {Action OutcomeDim : Type*} {J : ℕ}
    [Fintype OutcomeDim] [Nonempty OutcomeDim]
    (L : NNReal) (agent : oltc_agent Action OutcomeDim J) : Prop :=
  (∀ a y, outcome_cube y → agent.utility a y ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ j a y, outcome_cube y → agent.constraint j a y ∈ Set.Icc (-1 : ℝ) 1) ∧
      ∀ a y z, outcome_cube y → outcome_cube z →
        |agent.utility a y - agent.utility a z| ≤
          (L : ℝ) * finite_sup_norm (y - z)

@[blueprint "def:benchmark-action-set"
  (statement := /-- Given an agent with a finite action type and an outcome sequence \((y_t)_{t=1}^{T}\), the terminal benchmark is the set of actions satisfying every constraint at every round:
  \[
    \mathcal A_{1:T}^{\mathbf c}
      = \{a : c_j(a,y_t) \leq 0\ \text{for all }t\text{ and }j\}.
  \] -/)
  (title := /-- Terminal feasible benchmark -/)
  (latexEnv := "definition")]
noncomputable def benchmark_action_set {Action OutcomeDim : Type*} {J T : ℕ}
    [Fintype Action] (agent : oltc_agent Action OutcomeDim J)
    (outcomes : Fin T → OutcomeDim → ℝ) : Finset Action := by
  classical
  exact Finset.univ.filter fun a => ∀ t j, agent.constraint j a (outcomes t) ≤ 0

@[blueprint "def:action-count"
  (statement := /-- For a played-action sequence \((a_t)_{t=1}^{T}\), the count \(T(a)\) is the number of rounds on which action \(a\) is played:
  \[
    T(a)=\sum_{t=1}^{T}\mathbf 1[a_t=a].
  \] -/)
  (title := /-- Number of rounds assigned to an action -/)
  (latexEnv := "definition")]
def action_count {Action : Type*} {T : ℕ} [DecidableEq Action]
    (played : Fin T → Action) (a : Action) : ℕ :=
  ∑ t, if played t = a then 1 else 0

@[blueprint "def:decision-calibrated"
  (statement := /-- Let the action type have decidable equality, let \(D\) be a finite nonempty coordinate type, and let \(\alpha_1:\mathbb R\to\mathbb R\). Predictions \((p_t)_{t=1}^{T}\) are decision calibrated for the played actions \((a_t)_{t=1}^{T}\) and outcomes \((y_t)_{t=1}^{T}\) if, for every action \(a\),
  \[
    \left\|\sum_{t=1}^{T}\mathbf 1[a_t=a](p_t-y_t)\right\|_\infty
      \leq \alpha_1(T(a)).
  \] -/)
  (title := /-- Decision calibration for one agent -/)
  (latexEnv := "definition")]
def decision_calibrated {Action OutcomeDim : Type*} {T : ℕ}
    [DecidableEq Action] [Fintype OutcomeDim] [Nonempty OutcomeDim]
    (alpha : ℝ → ℝ) (predictions outcomes : Fin T → OutcomeDim → ℝ)
    (played : Fin T → Action) : Prop :=
  ∀ a,
    finite_sup_norm (∑ t, if played t = a then predictions t - outcomes t else 0) ≤
      alpha (action_count played a : ℝ)

@[blueprint "def:runs-elimination-algorithm"
  (statement := /-- On a finite action type with decidable equality, an action sequence runs the elimination-based realization algorithm, for the purposes of the regret argument, when at every round the played action belongs to the maintained candidate set and maximizes predicted utility over that set, while the terminal feasible benchmark is contained in every candidate set. -/)
  (title := /-- Semantic interface of the elimination algorithm -/)
  (latexEnv := "definition")]
def runs_elimination_algorithm {Action OutcomeDim : Type*} {J T : ℕ}
    [Fintype Action] [DecidableEq Action]
    (agent : oltc_agent Action OutcomeDim J)
    (outcomes predictions : Fin T → OutcomeDim → ℝ)
    (candidates : Fin T → Finset Action) (played : Fin T → Action) : Prop :=
  (∀ t, played t ∈ candidates t) ∧
    (∀ t a, a ∈ candidates t →
      agent.utility a (predictions t) ≤ agent.utility (played t) (predictions t)) ∧
      ∀ t, benchmark_action_set agent outcomes ⊆ candidates t

@[blueprint "def:constrained-swap-regret"
  (statement := /-- Let \(\mathcal A\) be a finite action type with decidable equality and let \(\mathcal B\subseteq\mathcal A\) be a nonempty benchmark. The \(\mathcal B\)-constrained swap regret is the maximum, over all maps \(\phi:\mathcal A\to\mathcal B\), of
  \[
    \sum_{t=1}^{T}\bigl(u(\phi(a_t),y_t)-u(a_t,y_t)\bigr).
  \] -/)
  (title := /-- Constrained swap regret -/)
  (latexEnv := "definition")]
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

@[blueprint "lem:decision-calibration-actual-utility-error"
  (statement := /-- Let \(\mathcal A\) be a finite nonempty action type and let \(D\) be a finite nonempty coordinate type. Fix \(T\in\mathbb N\), \(L\geq 0\), a concave function \(\alpha_1:\mathbb R\to\mathbb R\), an \(L\)-admissible agent, prediction and outcome sequences in \([0,1]^D\), and a played-action sequence. If the predictions are decision calibrated, then
  \[
    \left|\sum_{t=1}^{T}\bigl(u(a_t,p_t)-u(a_t,y_t)\bigr)\right|
      \leq L|\mathcal A|\alpha_1\!\left(\frac{T}{|\mathcal A|}\right).
  \] -/)
  (proof := /-- First extend the Lipschitz estimate in \(\cref{def:admissible-agent}\) from differences of cube points to every vector \(v\in\mathbb R^D\). If the norm in \(\cref{def:finite-sup-norm}\) vanishes, then every coordinate of \(v\) vanishes. Otherwise set
  \[
    y_i=\frac{\max\{v_i,0\}}{\lVert v\rVert_\infty},
    \qquad
    z_i=\frac{\max\{-v_i,0\}}{\lVert v\rVert_\infty}.
  \]
  The coordinatewise bound \(|v_i|\leq\lVert v\rVert_\infty\) shows, by \(\cref{def:outcome-cube}\), that \(y,z\in[0,1]^D\). Moreover,
  \(v=\lVert v\rVert_\infty(y-z)\) and
  \(\lVert y-z\rVert_\infty\leq1\). Linearity of the utility and the admissibility estimate therefore give
  \[
    |u(a,v)|\leq L\lVert v\rVert_\infty.
  \]
  For each \(a\in\mathcal A\), let
  \[
    r_a=\sum_{t=1}^{T}\mathbf 1[a_t=a](p_t-y_t).
  \]
  Reordering the two finite sums and using utility linearity rewrites the sum in the conclusion as \(\sum_a u(a,r_a)\). The triangle inequality and the preceding estimate bound its absolute value by
  \[
    L\sum_{a\in\mathcal A}\lVert r_a\rVert_\infty.
  \]
  By \(\cref{def:decision-calibrated}\), this is at most
  \(L\sum_a\alpha_1(T(a))\), where \(T(a)\) is defined in
  \(\cref{def:action-count}\). Reordering the indicator sums gives
  \(\sum_aT(a)=T\). Jensen's inequality for the concave function
  \(\alpha_1\), with uniform weight \(1/|\mathcal A|\), yields
  \[
    \sum_a\alpha_1(T(a))
      \leq |\mathcal A|\alpha_1\!\left(\frac{T}{|\mathcal A|}\right).
  \]
  Multiplication by the nonnegative constant \(L\) proves the claim. -/)
  (title := /-- Calibration controls realized utility error -/)
  (latexEnv := "lemma")]
lemma decision_calibration_actual_utility_error
    {Action OutcomeDim : Type*} {J T : ℕ}
    [Fintype Action] [DecidableEq Action] [Nonempty Action]
    [Fintype OutcomeDim] [Nonempty OutcomeDim]
    (L : NNReal) (alpha : ℝ → ℝ) (agent : oltc_agent Action OutcomeDim J)
    (predictions outcomes : Fin T → OutcomeDim → ℝ) (played : Fin T → Action)
    (hAgent : admissible_agent L agent)
    (hPredictions : ∀ t, outcome_cube (predictions t))
    (hOutcomes : ∀ t, outcome_cube (outcomes t))
    (hAlpha : ConcaveOn ℝ (Set.univ : Set ℝ) alpha)
    (hCalibration : decision_calibrated alpha predictions outcomes played) :
    |∑ t, (agent.utility (played t) (predictions t) -
      agent.utility (played t) (outcomes t))| ≤
      (L : ℝ) * (Fintype.card Action : ℝ) *
        alpha ((T : ℝ) / (Fintype.card Action : ℝ)) := by
  classical
  have hNormNonneg (v : OutcomeDim → ℝ) : 0 ≤ finite_sup_norm v := by
    let i : OutcomeDim := Classical.choice inferInstance
    exact (abs_nonneg (v i)).trans (by
      unfold finite_sup_norm
      exact Finset.le_sup' (fun i : OutcomeDim => |v i|) (Finset.mem_univ i))
  have hAbsLeNorm (v : OutcomeDim → ℝ) (i : OutcomeDim) :
      |v i| ≤ finite_sup_norm v := by
    unfold finite_sup_norm
    exact Finset.le_sup' (fun i : OutcomeDim => |v i|) (Finset.mem_univ i)
  have hUtility (a : Action) (v : OutcomeDim → ℝ) :
      |agent.utility a v| ≤ (L : ℝ) * finite_sup_norm v := by
    by_cases hNormZero : finite_sup_norm v = 0
    · have hv : v = 0 := by
        funext i
        apply abs_eq_zero.mp
        exact le_antisymm (hNormZero ▸ hAbsLeNorm v i) (abs_nonneg (v i))
      rw [hv]
      simp only [map_zero, abs_zero]
      exact mul_nonneg (NNReal.coe_nonneg L) (hNormNonneg 0)
    · have hNormPos : 0 < finite_sup_norm v :=
        lt_of_le_of_ne (hNormNonneg v) (Ne.symm hNormZero)
      let y : OutcomeDim → ℝ :=
        fun i => max (v i) 0 / finite_sup_norm v
      let z : OutcomeDim → ℝ :=
        fun i => max (-v i) 0 / finite_sup_norm v
      have hy : outcome_cube y := by
        intro i
        constructor
        · exact div_nonneg (le_max_right _ _) (hNormNonneg v)
        · rw [div_le_one hNormPos]
          exact max_le (le_trans (le_abs_self (v i)) (hAbsLeNorm v i))
            (hNormNonneg v)
      have hz : outcome_cube z := by
        intro i
        constructor
        · exact div_nonneg (le_max_right _ _) (hNormNonneg v)
        · rw [div_le_one hNormPos]
          exact max_le (le_trans (neg_le_abs (v i)) (hAbsLeNorm v i))
            (hNormNonneg v)
      have hvscale : v = finite_sup_norm v • (y - z) := by
        funext i
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        dsimp [y, z]
        field_simp [hNormZero]
        rcases le_total 0 (v i) with hi | hi
        · simp [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]
        · simp [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi)]
      have hNormYZ : finite_sup_norm (y - z) ≤ 1 := by
        unfold finite_sup_norm
        apply Finset.sup'_le
        intro i hi
        rw [abs_le]
        constructor
        · have hyi := (hy i).1
          have hzi := (hz i).2
          change -1 ≤ y i - z i
          linarith
        · have hyi := (hy i).2
          have hzi := (hz i).1
          change y i - z i ≤ 1
          linarith
      have hLip := hAgent.2.2 a y z hy hz
      have hMap :
          agent.utility a v =
            finite_sup_norm v * (agent.utility a y - agent.utility a z) := by
        conv_lhs => rw [hvscale]
        rw [LinearMap.map_smul, LinearMap.map_sub]
        rfl
      calc
        |agent.utility a v| =
            finite_sup_norm v * |agent.utility a y - agent.utility a z| := by
              rw [hMap, abs_mul, abs_of_nonneg (hNormNonneg v)]
        _ ≤ finite_sup_norm v *
            ((L : ℝ) * finite_sup_norm (y - z)) :=
              mul_le_mul_of_nonneg_left hLip (hNormNonneg v)
        _ ≤ finite_sup_norm v * ((L : ℝ) * 1) := by
              gcongr
        _ = (L : ℝ) * finite_sup_norm v := by ring
  let residual : Action → OutcomeDim → ℝ :=
    fun a => ∑ t, if played t = a then predictions t - outcomes t else 0
  have hFiber :
      (∑ t, (agent.utility (played t) (predictions t) -
        agent.utility (played t) (outcomes t))) =
        ∑ a, agent.utility a (residual a) := by
    calc
      (∑ t, (agent.utility (played t) (predictions t) -
        agent.utility (played t) (outcomes t))) =
          ∑ t, ∑ a, if played t = a then
            (agent.utility a (predictions t) - agent.utility a (outcomes t))
          else 0 := by simp
      _ = ∑ a, ∑ t, if played t = a then
            (agent.utility a (predictions t) - agent.utility a (outcomes t))
          else 0 := Finset.sum_comm
      _ = ∑ a, agent.utility a (residual a) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro t ht
        by_cases h : played t = a <;> simp [residual, h, LinearMap.map_sub]
  have hCardPos : 0 < (Fintype.card Action : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hCountSum :
      (∑ a : Action, (action_count played a : ℝ)) = (T : ℝ) := by
    norm_cast
    calc
      (∑ a : Action, action_count played a) =
          ∑ a : Action, ∑ t, if played t = a then 1 else 0 := rfl
      _ = ∑ t, ∑ a : Action, if played t = a then 1 else 0 := Finset.sum_comm
      _ = ∑ t : Fin T, 1 := by
        apply Finset.sum_congr rfl
        intro t ht
        simp
      _ = T := by simp
  have hJensen :
      (∑ a : Action, alpha (action_count played a : ℝ)) ≤
        (Fintype.card Action : ℝ) *
          alpha ((T : ℝ) / (Fintype.card Action : ℝ)) := by
    let n : ℝ := Fintype.card Action
    have hn : 0 < n := hCardPos
    have hAverage := hAlpha.le_map_sum
      (t := Finset.univ) (w := fun _ : Action => n⁻¹)
      (p := fun a => (action_count played a : ℝ))
      (by intro i hi; positivity)
      (by simp [n, ne_of_gt hn])
      (by simp)
    calc
      (∑ a : Action, alpha (action_count played a : ℝ)) =
          n * (∑ a : Action, n⁻¹ * alpha (action_count played a : ℝ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a ha
            field_simp
      _ ≤ n * alpha
          (∑ a : Action, n⁻¹ * (action_count played a : ℝ)) :=
            mul_le_mul_of_nonneg_left hAverage (le_of_lt hn)
      _ = (Fintype.card Action : ℝ) *
          alpha ((T : ℝ) / (Fintype.card Action : ℝ)) := by
            congr 2
            rw [← Finset.mul_sum, hCountSum]
            dsimp [n]
            field_simp
  rw [hFiber]
  calc
    |∑ a, agent.utility a (residual a)| ≤
        ∑ a, |agent.utility a (residual a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, (L : ℝ) * finite_sup_norm (residual a) :=
      Finset.sum_le_sum fun a ha => hUtility a (residual a)
    _ ≤ ∑ a, (L : ℝ) * alpha (action_count played a : ℝ) :=
      Finset.sum_le_sum fun a ha =>
        mul_le_mul_of_nonneg_left (hCalibration a) (NNReal.coe_nonneg L)
    _ = (L : ℝ) * ∑ a, alpha (action_count played a : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ (L : ℝ) * ((Fintype.card Action : ℝ) *
        alpha ((T : ℝ) / (Fintype.card Action : ℝ))) :=
      mul_le_mul_of_nonneg_left hJensen (NNReal.coe_nonneg L)
    _ = (L : ℝ) * (Fintype.card Action : ℝ) *
        alpha ((T : ℝ) / (Fintype.card Action : ℝ)) := by ring

@[blueprint "lem:decision-calibration-swapped-utility-error"
  (statement := /-- Let \(\mathcal A\) be a finite nonempty action type and let \(D\) be a finite nonempty coordinate type. Fix \(T\in\mathbb N\), \(L\geq0\), a concave function \(\alpha_1:\mathbb R\to\mathbb R\), an \(L\)-admissible agent, prediction and outcome sequences in \([0,1]^D\), a played-action sequence for which the predictions are decision calibrated, and an arbitrary map \(\phi:\mathcal A\to\mathcal A\). Then
  \[
    \left|\sum_{t=1}^{T}\bigl(u(\phi(a_t),p_t)-u(\phi(a_t),y_t)\bigr)\right|
      \leq L|\mathcal A|\alpha_1\!\left(\frac{T}{|\mathcal A|}\right).
  \] -/)
  (proof := /-- Define an auxiliary agent whose utility at action \(a\) is the original agent's utility at \(\phi(a)\), and whose constraint functions are unchanged. This auxiliary agent is \(L\)-admissible: its utility range and Lipschitz conditions follow from those of the original agent at the action \(\phi(a)\), while its constraint condition is identical. Applying \(\cref{lem:decision-calibration-actual-utility-error}\) to the auxiliary agent, with the given cube and calibration hypotheses, yields the stated inequality after unfolding its utility. -/)
  (title := /-- Calibration controls swapped utility error -/)
  (latexEnv := "lemma")]
lemma decision_calibration_swapped_utility_error
    {Action OutcomeDim : Type*} {J T : ℕ}
    [Fintype Action] [DecidableEq Action] [Nonempty Action]
    [Fintype OutcomeDim] [Nonempty OutcomeDim]
    (L : NNReal) (alpha : ℝ → ℝ) (agent : oltc_agent Action OutcomeDim J)
    (predictions outcomes : Fin T → OutcomeDim → ℝ) (played : Fin T → Action)
    (phi : Action → Action)
    (hAgent : admissible_agent L agent)
    (hPredictions : ∀ t, outcome_cube (predictions t))
    (hOutcomes : ∀ t, outcome_cube (outcomes t))
    (hAlpha : ConcaveOn ℝ (Set.univ : Set ℝ) alpha)
    (hCalibration : decision_calibrated alpha predictions outcomes played) :
    |∑ t, (agent.utility (phi (played t)) (predictions t) -
      agent.utility (phi (played t)) (outcomes t))| ≤
      (L : ℝ) * (Fintype.card Action : ℝ) *
        alpha ((T : ℝ) / (Fintype.card Action : ℝ)) := by
  let swappedAgent : oltc_agent Action OutcomeDim J :=
    { utility := fun a => agent.utility (phi a)
      constraint := agent.constraint }
  have hSwapped : admissible_agent L swappedAgent := by
    refine ⟨?_, ?_, ?_⟩
    · intro a y hy
      exact hAgent.1 (phi a) y hy
    · intro j a y hy
      exact hAgent.2.1 j a y hy
    · intro a y z hy hz
      exact hAgent.2.2 (phi a) y z hy hz
  convert decision_calibration_actual_utility_error
    (L := L) (alpha := alpha) (agent := swappedAgent)
    (predictions := predictions) (outcomes := outcomes) (played := played)
    hSwapped hPredictions hOutcomes hAlpha hCalibration using 1 <;>
    simp [swappedAgent]

@[blueprint "lem:benchmark-prediction-advantage-nonpositive"
  (statement := /-- Fix a finite action type with decidable equality, an agent, outcome and prediction sequences, maintained candidate sets, and a played-action sequence that runs the elimination algorithm. If \(\phi:\mathcal A\to\mathcal A\) maps every action into the terminal feasible benchmark, then
  \[
    \sum_{t=1}^{T}\bigl(u(\phi(a_t),p_t)-u(a_t,p_t)\bigr)\leq 0.
  \] -/)
  (proof := /-- By \(\cref{def:runs-elimination-algorithm}\), the terminal benchmark is contained in the candidate set at every round. Hence \(\phi(a_t)\) is a candidate action. The same definition states that \(a_t\) maximizes predicted utility over that candidate set, so
  \(u(\phi(a_t),p_t)\leq u(a_t,p_t)\) for every \(t\). Summing these pointwise inequalities proves the claim. -/)
  (title := /-- Best response dominates benchmark swaps on predictions -/)
  (latexEnv := "lemma")]
lemma benchmark_prediction_advantage_nonpositive
    {Action OutcomeDim : Type*} {J T : ℕ}
    [Fintype Action] [DecidableEq Action]
    (agent : oltc_agent Action OutcomeDim J)
    (outcomes predictions : Fin T → OutcomeDim → ℝ)
    (candidates : Fin T → Finset Action) (played : Fin T → Action)
    (phi : Action → Action)
    (hRuns : runs_elimination_algorithm agent outcomes predictions candidates played)
    (hPhi : ∀ a, phi a ∈ benchmark_action_set agent outcomes) :
    (∑ t, (agent.utility (phi (played t)) (predictions t) -
      agent.utility (played t) (predictions t))) ≤ 0 := by
  rcases hRuns with ⟨_, hMax, hSubset⟩
  apply Finset.sum_nonpos
  intro t _
  exact sub_nonpos.mpr (hMax t _ (hSubset t (hPhi (played t))))

@[blueprint "lem:pointwise-swap-regret-bound"
  (statement := /-- Fix a finite nonempty action type \(\mathcal A\), a finite nonempty coordinate type, an \(L\)-admissible agent, prediction and outcome sequences in the outcome cube, maintained candidate sets, and a played-action sequence. If \(\alpha_1:\mathbb R\to\mathbb R\) is concave, the predictions are decision calibrated, and the played actions run the elimination algorithm, then every map \(\phi:\mathcal A\to\mathcal A_{1:T}^{\mathbf c}\) satisfies
  \[
    \sum_{t=1}^{T}\bigl(u(\phi(a_t),y_t)-u(a_t,y_t)\bigr)
      \leq 2L|\mathcal A|\alpha_1\!\left(\frac{T}{|\mathcal A|}\right).
  \] -/)
  (proof := /-- For each round insert the two prediction-space terms and sum:
  \[
  \begin{aligned}
  u(\phi(a_t),y_t)-u(a_t,y_t)
    ={}& u(\phi(a_t),y_t)-u(\phi(a_t),p_t)\\
      &+u(\phi(a_t),p_t)-u(a_t,p_t)\\
      &+u(a_t,p_t)-u(a_t,y_t).
  \end{aligned}
  \]
  The absolute value of the first sum is bounded by \(\cref{lem:decision-calibration-swapped-utility-error}\), the middle sum is nonpositive by \(\cref{lem:benchmark-prediction-advantage-nonpositive}\), and the absolute value of the last sum is bounded by \(\cref{lem:decision-calibration-actual-utility-error}\). Adding the three estimates gives the stated factor \(2\). -/)
  (title := /-- Pointwise regret bound for a benchmark swap -/)
  (latexEnv := "lemma")]
lemma pointwise_swap_regret_bound
    {Action OutcomeDim : Type*} {J T : ℕ}
    [Fintype Action] [DecidableEq Action] [Nonempty Action]
    [Fintype OutcomeDim] [Nonempty OutcomeDim]
    (L : NNReal) (alpha : ℝ → ℝ) (agent : oltc_agent Action OutcomeDim J)
    (predictions outcomes : Fin T → OutcomeDim → ℝ)
    (candidates : Fin T → Finset Action) (played : Fin T → Action)
    (phi : Action → Action)
    (hAgent : admissible_agent L agent)
    (hPredictions : ∀ t, outcome_cube (predictions t))
    (hOutcomes : ∀ t, outcome_cube (outcomes t))
    (hAlpha : ConcaveOn ℝ (Set.univ : Set ℝ) alpha)
    (hCalibration : decision_calibrated alpha predictions outcomes played)
    (hRuns : runs_elimination_algorithm agent outcomes predictions candidates played)
    (hPhi : ∀ a, phi a ∈ benchmark_action_set agent outcomes) :
    (∑ t, (agent.utility (phi (played t)) (outcomes t) -
      agent.utility (played t) (outcomes t))) ≤
      2 * (L : ℝ) * (Fintype.card Action : ℝ) *
        alpha ((T : ℝ) / (Fintype.card Action : ℝ)) := by
  have hSwapped := decision_calibration_swapped_utility_error
    (L := L) (alpha := alpha) (agent := agent)
    (predictions := predictions) (outcomes := outcomes) (played := played)
    (phi := phi) hAgent hPredictions hOutcomes hAlpha hCalibration
  have hActual := decision_calibration_actual_utility_error
    (L := L) (alpha := alpha) (agent := agent)
    (predictions := predictions) (outcomes := outcomes) (played := played)
    hAgent hPredictions hOutcomes hAlpha hCalibration
  have hMiddle := benchmark_prediction_advantage_nonpositive
    (agent := agent) (outcomes := outcomes) (predictions := predictions)
    (candidates := candidates) (played := played) (phi := phi) hRuns hPhi
  have hFirst :
      (∑ t, (agent.utility (phi (played t)) (outcomes t) -
        agent.utility (phi (played t)) (predictions t))) ≤
        (L : ℝ) * (Fintype.card Action : ℝ) *
          alpha ((T : ℝ) / (Fintype.card Action : ℝ)) := by
    calc
      (∑ t, (agent.utility (phi (played t)) (outcomes t) -
        agent.utility (phi (played t)) (predictions t))) =
          -(∑ t, (agent.utility (phi (played t)) (predictions t) -
            agent.utility (phi (played t)) (outcomes t))) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro t ht
              ring
      _ ≤ |-(∑ t, (agent.utility (phi (played t)) (predictions t) -
        agent.utility (phi (played t)) (outcomes t)))| := le_abs_self _
      _ = |∑ t, (agent.utility (phi (played t)) (predictions t) -
        agent.utility (phi (played t)) (outcomes t))| := abs_neg _
      _ ≤ (L : ℝ) * (Fintype.card Action : ℝ) *
        alpha ((T : ℝ) / (Fintype.card Action : ℝ)) := hSwapped
  have hActualUpper :
      (∑ t, (agent.utility (played t) (predictions t) -
        agent.utility (played t) (outcomes t))) ≤
        (L : ℝ) * (Fintype.card Action : ℝ) *
          alpha ((T : ℝ) / (Fintype.card Action : ℝ)) :=
    (le_abs_self _).trans hActual
  calc
    (∑ t, (agent.utility (phi (played t)) (outcomes t) -
      agent.utility (played t) (outcomes t))) =
        (∑ t, (agent.utility (phi (played t)) (outcomes t) -
          agent.utility (phi (played t)) (predictions t))) +
        (∑ t, (agent.utility (phi (played t)) (predictions t) -
          agent.utility (played t) (predictions t))) +
        (∑ t, (agent.utility (played t) (predictions t) -
          agent.utility (played t) (outcomes t))) := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro t ht
            ring
    _ ≤ 2 * (L : ℝ) * (Fintype.card Action : ℝ) *
      alpha ((T : ℝ) / (Fintype.card Action : ℝ)) := by linarith

@[blueprint "lem:constrained-swap-regret-le-of-pointwise"
  (statement := /-- Let \(\mathcal A\) be a finite action type with decidable equality, let \(D\) be a type, and fix \(T\in\mathbb N\). Let \(u(a,\cdot):(D\to\mathbb R)\to\mathbb R\) be linear for every \(a\in\mathcal A\), let \(\mathcal B\) be a nonempty finite subset of \(\mathcal A\), and fix sequences \(a_t\in\mathcal A\) and \(y_t:D\to\mathbb R\), indexed by \(t\in\operatorname{Fin}(T)\), together with \(R\in\mathbb R\). If
  \[
    \sum_{t\in\operatorname{Fin}(T)}
      \bigl(u(\phi(a_t),y_t)-u(a_t,y_t)\bigr)\leq R
  \]
  for every map \(\phi:\mathcal A\to\mathcal B\), then the \(\mathcal B\)-constrained swap regret is at most \(R\). -/)
  (proof := /-- By \(\cref{def:constrained-swap-regret}\), constrained swap regret is the finite supremum of the displayed regrets over all maps into \(\mathcal B\). Since each member of this nonempty finite family is at most \(R\), its supremum is at most \(R\). -/)
  (title := /-- Lift pointwise swap bounds to constrained regret -/)
  (latexEnv := "lemma")]
lemma constrained_swap_regret_le_of_pointwise
    {Action OutcomeDim : Type*} {T : ℕ}
    [Fintype Action] [DecidableEq Action]
    (utility : Action → (OutcomeDim → ℝ) →ₗ[ℝ] ℝ)
    (benchmark : Finset Action) (hBenchmark : benchmark.Nonempty)
    (played : Fin T → Action) (outcomes : Fin T → OutcomeDim → ℝ) (R : ℝ)
    (hPointwise : ∀ phi : Action → {a // a ∈ benchmark},
      (∑ t, (utility (phi (played t)).1 (outcomes t) -
        utility (played t) (outcomes t))) ≤ R) :
    constrained_swap_regret utility benchmark hBenchmark played outcomes ≤ R := by
  classical
  rw [constrained_swap_regret, Finset.sup'_le_iff]
  intro phi _
  exact hPointwise phi

@[blueprint "thm:swap-regret-realization"
  (statement := /-- Let \(\mathcal A\) be a finite nonempty action type with decidable equality, let \(D\) be a finite nonempty coordinate type, and fix \(J,T\in\mathbb N\) and \(L\geq0\). Let \(\mathcal N\) be a set of agents, each equipped with an action-indexed real-linear utility functional on \(\mathbb R^D\) and \(J\) constraint functions. Fix common prediction and outcome sequences \(p,y:\operatorname{Fin}(T)\to[0,1]^D\), and, for each agent, fix maintained candidate sets and a played-action sequence indexed by \(\operatorname{Fin}(T)\). Let \(\alpha_1:\mathbb R\to\mathbb R\) be concave on \(\mathbb R\). Assume that every agent in \(\mathcal N\) is \(L\)-admissible, that its candidate sets and played actions run the elimination algorithm for \(y\) and \(p\), that \(p\) is decision calibrated relative to \(y\) and its played actions, and that its terminal feasible benchmark is nonempty. Then every agent in \(\mathcal N\) has constrained swap regret bounded by
  \[
    \operatorname{Reg}_{\mathrm{swap}}
      \bigl(u,\mathcal A_{1:T}^{\mathbf c},1:T\bigr)
      \leq 2L|\mathcal A|\alpha_1\!\left(\frac{T}{|\mathcal A|}\right).
  \] -/)
  (proof := /-- Fix an agent in \(\mathcal N\). For every map from \(\mathcal A\) into its terminal feasible benchmark, \(\cref{lem:pointwise-swap-regret-bound}\) gives the required bound on realized regret. Applying \(\cref{lem:constrained-swap-regret-le-of-pointwise}\) to this family of inequalities bounds the maximum over all such maps. Since the chosen agent was arbitrary, the assertion holds for every agent in \(\mathcal N\). -/)
  (title := /-- Decision calibration implies constrained swap regret -/)
  (latexEnv := "theorem")]
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
  intro agent hAgentMem
  apply constrained_swap_regret_le_of_pointwise
  intro phi
  exact pointwise_swap_regret_bound
    (L := L) (alpha := alpha) (agent := agent)
    (predictions := predictions) (outcomes := outcomes)
    (candidates := candidates agent) (played := played agent)
    (phi := fun a => (phi a).1)
    (hAgents agent hAgentMem) hPredictions hOutcomes hAlpha
    (hCalibration agent hAgentMem) (hRuns agent hAgentMem)
    (fun a => (phi a).2)

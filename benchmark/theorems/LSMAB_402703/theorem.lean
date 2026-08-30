import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Process.Filtration

set_option linter.all false
set_option maxHeartbeats 800000

structure hierarchical_two_point_bandit
    (Action Node Ω : Type*) [Fintype Action] [Nonempty Action] [DecidableEq Action]
    [Fintype Node] [DecidableEq Node] [MeasurableSpace Ω] where
  depth : ℕ
  levelNodes : Fin depth → Finset Node
  descends : Node → Action → Prop
  commonAtLevel : Fin depth → Action → Action → Prop
  parentCommonAtLevel : Fin depth → Action → Action → Prop
  [descends_decidable : ∀ v a, Decidable (descends v a)]
  [commonAtLevel_decidable : ∀ j a b, Decidable (commonAtLevel j a b)]
  [parentCommonAtLevel_decidable : ∀ j a b, Decidable (parentCommonAtLevel j a b)]
  similarityLevel : Action → Action → Fin depth
  leafLevel : Fin depth
  leafNode : Action → Node
  scale : Fin depth → ℝ
  delta : Fin depth → ℝ
  gap : Action → ℝ
  nodeGap : Node → ℝ
  measure : MeasureTheory.Measure Ω
  probability_measure : MeasureTheory.IsProbabilityMeasure measure
  history : MeasureTheory.Filtration ℕ (‹MeasurableSpace Ω›)
  loss : ℕ → Ω → Action → ℝ
  conditionalMeanLoss : ℕ → Ω → Action → ℝ
  firstAction : ℕ → Ω → Action
  secondAction : ℕ → Ω → Action
  sampledLevel : ℕ → Ω → Fin depth
  bestAction : ℕ → Action
  optimalAction : Action
  leafLevel_maximal : ∀ j, j ≤ leafLevel
  node_has_unique_level : ∀ v, ∃! j, v ∈ levelNodes j
  action_has_unique_ancestor : ∀ j a, ∃! v, v ∈ levelNodes j ∧ descends v a
  leafNode_injective : Function.Injective leafNode
  leaf_nodes_exact : ∀ v, v ∈ levelNodes leafLevel ↔ ∃ a, leafNode a = v
  leaf_descends_iff : ∀ a b, descends (leafNode a) b ↔ a = b
  commonAtLevel_iff :
    ∀ j a b, commonAtLevel j a b ↔
      ∃ v, v ∈ levelNodes j ∧ descends v a ∧ descends v b
  parentCommonAtLevel_iff :
    ∀ j a b, parentCommonAtLevel j a b ↔
      j.val = 0 ∨
        ∃ i : Fin depth, j.val = i.val + 1 ∧ commonAtLevel i a b
  commonAtLevel_mono :
    ∀ i j a b, i ≤ j → commonAtLevel j a b → commonAtLevel i a b
  similarityLevel_spec :
    ∀ a b, a ≠ b →
      ¬commonAtLevel (similarityLevel a b) a b ∧
        ∀ j, j < similarityLevel a b → commonAtLevel j a b
  scale_nonnegative : ∀ j, 0 ≤ scale j
  scale_antitone : Antitone scale
  delta_positive : ∀ j, 0 < delta j
  delta_total : ∑ j, delta j = 1
  gap_nonnegative : ∀ a, 0 ≤ gap a
  nodeGap_nonnegative : ∀ v, 0 ≤ nodeGap v
  nodeGap_le : ∀ v a, descends v a → nodeGap v ≤ gap a
  nodeGap_attained : ∀ j v, v ∈ levelNodes j → ∃ a, descends v a ∧ nodeGap v = gap a
  commonAtLevel_equivalence : ∀ j, Equivalence (commonAtLevel j)
  loss_integrable : ∀ t a, MeasureTheory.Integrable (fun ω => loss t ω a) measure
  conditionalMeanLoss_integrable :
    ∀ t a, MeasureTheory.Integrable (fun ω => conditionalMeanLoss t ω a) measure
  conditionalMeanLoss_measurable :
    ∀ t a, @Measurable Ω ℝ (history t) inferInstance
      (fun ω => conditionalMeanLoss t ω a)
  conditionalMeanLoss_spec :
    ∀ t a E, @MeasurableSet Ω (history t) E →
      (∫ ω in E, loss t ω a ∂measure) =
        ∫ ω in E, conditionalMeanLoss t ω a ∂measure
  first_executed_loss_integrable :
    ∀ t, MeasureTheory.Integrable (fun ω => loss t ω (firstAction t ω)) measure
  second_executed_loss_integrable :
    ∀ t, MeasureTheory.Integrable (fun ω => loss t ω (secondAction t ω)) measure
  tree_compatible :
    ∀ t ω a b,
      |loss t ω a - loss t ω b| ≤
        if a = b then 0 else scale (similarityLevel a b)
  bestAction_minimizes :
    ∀ T a,
      (∫ ω, ∑ t ∈ Finset.range T, loss t ω (bestAction T) ∂measure) ≤
        ∫ ω, ∑ t ∈ Finset.range T, loss t ω a ∂measure

variable {Action Node Ω : Type*} [Fintype Action] [Nonempty Action] [DecidableEq Action]
  [Fintype Node] [DecidableEq Node] [MeasurableSpace Ω]

def probability_vector (p : Action → ℝ) : Prop :=
  p ∈ stdSimplex ℝ Action

noncomputable def subtree_mass
    (M : hierarchical_two_point_bandit Action Node Ω) (x : Action → ℝ) (v : Node) : ℝ := by
  classical
  exact ∑ a, if M.descends v a then x a else 0

def generalized_stochastic_condition
    (M : hierarchical_two_point_bandit Action Node Ω) : Prop :=
  (∀ t a,
      (fun _ => M.gap a) ≤ᵐ[M.measure]
        fun ω => M.conditionalMeanLoss t ω a -
          M.conditionalMeanLoss t ω M.optimalAction) ∧
    M.gap M.optimalAction = 0 ∧
      ∀ t a, M.gap a = 0 →
        (fun ω => M.loss t ω a) =ᵐ[M.measure]
          fun ω => M.loss t ω M.optimalAction

noncomputable def two_point_nested_tsallis_regularizer
    (M : hierarchical_two_point_bandit Action Node Ω) (t : ℕ) (x : Action → ℝ) : ℝ :=
  (2 * Real.sqrt 6) *
    ∑ j,
      (M.scale j / Real.sqrt (M.delta j)) *
        Real.sqrt (max (t : ℝ) (6 / M.delta j)) *
          ∑ v ∈ M.levelNodes j,
            (subtree_mass M x v - Real.sqrt (subtree_mass M x v))

noncomputable def two_point_regret
    (M : hierarchical_two_point_bandit Action Node Ω) (T : ℕ) : ℝ :=
  (∫ ω,
      ∑ t ∈ Finset.range T,
        (M.loss t ω (M.firstAction t ω) + M.loss t ω (M.secondAction t ω)) / 2
      ∂M.measure) -
    ∫ ω, ∑ t ∈ Finset.range T, M.loss t ω (M.bestAction T) ∂M.measure

noncomputable def level_gap_complexity
    (M : hierarchical_two_point_bandit Action Node Ω) (j : Fin M.depth) : ℝ := by
  classical
  exact ∑ v ∈ M.levelNodes j, if M.nodeGap v ≠ 0 then 1 / M.nodeGap v else 0

noncomputable def stochastic_effective_action_number
    (M : hierarchical_two_point_bandit Action Node Ω) : ℝ :=
  (∑ j,
      (M.scale j / Real.sqrt (M.delta j)) *
        Real.sqrt (level_gap_complexity M j)) ^ 2

noncomputable def two_point_adversarial_raw_bound
    (M : hierarchical_two_point_bandit Action Node Ω) (T : ℕ) : ℝ :=
  18 * ∑ j, (M.scale j / M.delta j) * Real.sqrt ((M.levelNodes j).card : ℝ) +
    8 * Real.sqrt 6 *
      (∑ j, (M.scale j / Real.sqrt (M.delta j)) *
        Real.sqrt ((M.levelNodes j).card : ℝ)) * Real.sqrt T

noncomputable def two_point_stochastic_raw_bound
    (M : hierarchical_two_point_bandit Action Node Ω) (T : ℕ) : ℝ :=
  36 * ∑ j, (M.scale j / M.delta j) * Real.sqrt ((M.levelNodes j).card : ℝ) +
    96 * stochastic_effective_action_number M * Real.log (Real.exp 1 * T)

def conditional_independence_over
    (ambient m m₁ m₂ : MeasurableSpace Ω)
    (μ : @MeasureTheory.Measure Ω ambient) : Prop :=
  m ≤ ambient ∧ m₁ ≤ ambient ∧ m₂ ≤ ambient ∧
    ∀ U V : Set Ω, @MeasurableSet Ω m₁ U → @MeasurableSet Ω m₂ V →
      MeasureTheory.condExp (m := m) μ
          ((U ∩ V).indicator (fun _ => (1 : ℝ))) =ᵐ[μ]
        MeasureTheory.condExp (m := m) μ (U.indicator (fun _ => (1 : ℝ))) *
          MeasureTheory.condExp (m := m) μ (V.indicator (fun _ => (1 : ℝ)))

structure two_point_ftrl_run (M : hierarchical_two_point_bandit Action Node Ω) where
  distribution : ℕ → Ω → Action → ℝ
  estimatedLoss : ℕ → Ω → Action → ℝ
  samplingDensity : ℕ → Ω → Action → Fin M.depth → Action → ℝ
  regularizer : ℕ → (Action → ℝ) → ℝ
  shift : Fin M.depth → ℝ
  distribution_mem : ∀ t ω, probability_vector (distribution t ω)
  distribution_measurable :
    ∀ t a, @Measurable Ω ℝ (M.history t) inferInstance
      (fun ω => distribution t ω a)
  estimatedLoss_measurable :
    ∀ t a, @Measurable Ω ℝ (M.history (t + 1)) inferInstance
      (fun ω => estimatedLoss t ω a)
  ftrl_update :
    ∀ t ω q, probability_vector q →
      (∑ a, (∑ s ∈ Finset.range t, estimatedLoss s ω a) * distribution t ω a) +
          regularizer (t + 1) (distribution t ω) ≤
        (∑ a, (∑ s ∈ Finset.range t, estimatedLoss s ω a) * q a) +
          regularizer (t + 1) q
  samplingDensity_formula :
    ∀ t ω a j b,
      samplingDensity t ω a j b =
        distribution t ω a * M.delta j *
          @ite ℝ (M.parentCommonAtLevel j a b)
            (M.parentCommonAtLevel_decidable j a b)
            (distribution t ω b /
              ∑ b', @ite ℝ (M.parentCommonAtLevel j a b')
                (M.parentCommonAtLevel_decidable j a b') (distribution t ω b') 0)
            0
  first_action_conditional_law :
    ∀ t a E, @MeasurableSet Ω (M.history t) E →
      (∫ ω in E, if M.firstAction t ω = a then (1 : ℝ) else 0 ∂M.measure) =
        ∫ ω in E, distribution t ω a ∂M.measure
  sampled_level_conditional_law :
    ∀ t j E, @MeasurableSet Ω (M.history t) E →
      (∫ ω in E, if M.sampledLevel t ω = j then (1 : ℝ) else 0 ∂M.measure) =
        ∫ _ in E, M.delta j ∂M.measure
  feedback_conditional_law :
    ∀ t a j b E, @MeasurableSet Ω (M.history t) E →
      (∫ ω in E,
          if M.firstAction t ω = a ∧ M.sampledLevel t ω = j ∧
              M.secondAction t ω = b then (1 : ℝ) else 0 ∂M.measure) =
        ∫ ω in E, samplingDensity t ω a j b ∂M.measure
  feedback_loss_conditional_independence :
    ∀ t,
      conditional_independence_over inferInstance (M.history t)
        (MeasurableSpace.comap (fun ω => M.loss t ω) inferInstance)
        (⨆ s : {s : ℕ // t ≤ s},
          MeasurableSpace.comap (fun ω => M.firstAction s.1 ω) ⊤ ⊔
            MeasurableSpace.comap (fun ω => M.sampledLevel s.1 ω) ⊤ ⊔
              MeasurableSpace.comap (fun ω => M.secondAction s.1 ω) ⊤)
        M.measure
  estimatedLoss_formula :
    ∀ t ω a,
      estimatedLoss t ω a =
        ∑ v ∈ M.levelNodes (M.sampledLevel t ω),
          @ite ℝ (M.descends v (M.firstAction t ω))
            (M.descends_decidable v (M.firstAction t ω))
            (@ite ℝ (M.descends v a) (M.descends_decidable v a)
              ((M.loss t ω (M.firstAction t ω) -
                    M.loss t ω (M.secondAction t ω) +
                  shift (M.sampledLevel t ω)) /
                  (M.delta (M.sampledLevel t ω) *
                    subtree_mass M (distribution t ω) v))
              0)
            0
  sampled_centered_variance_integrable :
    ∀ t j,
      MeasureTheory.Integrable
        (fun ω =>
          if M.sampledLevel t ω = j then
            ∑ v ∈ M.levelNodes j,
              (subtree_mass M (distribution t ω) v *
                  Real.sqrt (subtree_mass M (distribution t ω) v)) *
                ((@ite ℝ (M.descends v (M.firstAction t ω))
                    (M.descends_decidable v (M.firstAction t ω))
                    ((M.loss t ω (M.firstAction t ω) -
                          M.loss t ω (M.secondAction t ω) + shift j) /
                      (M.delta j * subtree_mass M (distribution t ω) v))
                    0) -
                  (M.loss t ω (M.firstAction t ω) -
                      M.loss t ω (M.secondAction t ω) + shift j) /
                    M.delta j) ^ 2
          else 0)
        M.measure
  estimated_regret_integrable :
    ∀ t q, probability_vector q →
      MeasureTheory.Integrable
        (fun ω => ∑ a, estimatedLoss t ω a * (distribution t ω a - q a))
        M.measure
  estimated_regret_conditional_mean :
    ∀ t q, probability_vector q →
      MeasureTheory.condExp (m := M.history t) M.measure
          (fun ω => ∑ a, estimatedLoss t ω a * (distribution t ω a - q a)) =ᵐ[M.measure]
        fun ω => ∑ a,
          (distribution t ω a - q a) * M.conditionalMeanLoss t ω a
  zero_gap_blockwise_stability :
    ∀ (t : ℕ) (ω : Ω) (j : Fin M.depth) (b : Node → ℝ),
      (∀ v, v ∈ M.levelNodes j → M.nodeGap v ≠ 0 → b v = 0) →
      ∑ v ∈ M.levelNodes j,
        b v * (subtree_mass M (distribution t ω) v -
          subtree_mass M (distribution (t + 1) ω) v) = 0

theorem two_point_feedback
    (M : hierarchical_two_point_bandit Action Node Ω) (run : two_point_ftrl_run M)
    (T : ℕ) (hT : 1 ≤ T)
    (hregularizer :
      ∀ t x, 1 ≤ t → probability_vector x →
        run.regularizer t x = two_point_nested_tsallis_regularizer M t x)
    (hshift : ∀ j, run.shift j = M.scale j) :
    two_point_regret M T ≤ two_point_adversarial_raw_bound M T ∧
      (generalized_stochastic_condition M →
        two_point_regret M T ≤ two_point_stochastic_raw_bound M T) := by sorry

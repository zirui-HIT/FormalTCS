import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Bounded

set_option linter.all false
set_option maxHeartbeats 500000

abbrev online_point (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure lightons_problem where
  dimension : ℕ
  dimension_pos : 0 < dimension
  diameter : ℝ
  diameter_pos : 0 < diameter
  gradientBound : ℝ
  gradientBound_pos : 0 < gradientBound
  expConcavity : ℝ
  expConcavity_pos : 0 < expConcavity
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  deferral : ℝ
  one_lt_deferral : 1 < deferral
  conversionLoss : ℝ
  one_le_conversionLoss : 1 ≤ conversionLoss
  conversionGradient : ℝ
  one_le_conversionGradient : 1 ≤ conversionGradient
  matrixExponent : ℝ
  two_lt_matrixExponent : 2 < matrixExponent
  matrixExponent_le_three : matrixExponent ≤ 3
  projectionCost : ℝ
  projectionCost_nonneg : 0 ≤ projectionCost
  domain : Set (online_point dimension)
  domain_nonempty : domain.Nonempty
  domain_convex : Convex ℝ domain
  domain_compact : IsCompact domain
  domain_diameter : Metric.diam domain ≤ diameter
  domain_radius : ∀ x ∈ domain, ‖x‖ ≤ diameter / 2
  loss : ℕ → online_point dimension → ℝ
  lossGradient : ℕ → online_point dimension → online_point dimension
  loss_hasGradient : ∀ t x, x ∈ domain →
    HasGradientWithinAt (loss t) (lossGradient t x) domain x
  lossGradient_norm : ∀ t x, x ∈ domain →
    ‖lossGradient t x‖ ≤ gradientBound
  loss_lipschitz : ∀ t x, x ∈ domain → ∀ y, y ∈ domain →
    |loss t x - loss t y| ≤ gradientBound * dist x y
  loss_expConcave : ∀ t,
    ConcaveOn ℝ domain (fun x => Real.exp (-expConcavity * loss t x))

structure lightons_run (P : lightons_problem) where
  decision : ℕ → online_point P.dimension
  surrogatePoint : ℕ → online_point P.dimension
  surrogateGradient : ℕ → online_point P.dimension
  surrogateGradientRuntime : ℕ → ℝ
  runtime : ℕ → ℝ
  decision_mem : ∀ t, decision t ∈ P.domain
  surrogatePoint_mem : ∀ t, ‖surrogatePoint t‖ ≤ P.deferral * P.diameter / 2
  surrogateGradientRuntime_nonneg : ∀ t, 0 ≤ surrogateGradientRuntime t
  runtime_nonneg : ∀ T, 0 ≤ runtime T
  surrogateGradient_cost : Asymptotics.IsBigO Filter.atTop surrogateGradientRuntime
    (fun _ : ℕ => P.projectionCost + (P.dimension : ℝ))
  surrogateGradient_norm : ∀ t,
    ‖surrogateGradient t‖ ≤
      P.conversionGradient * ‖P.lossGradient t (decision t)‖
  domainConversion : ∀ t u, u ∈ P.domain →
    inner ℝ (P.lossGradient t (decision t)) (decision t - u) ≤
      P.conversionLoss * inner ℝ (surrogateGradient t) (surrogatePoint t - u)

def online_regret (P : lightons_problem) (run : lightons_run P)
    (T : ℕ) (u : online_point P.dimension) : ℝ :=
  ∑ t ∈ Finset.range T, (P.loss t (run.decision t) - P.loss t u)

noncomputable def gamma_prime (P : lightons_problem) : ℝ :=
  (1 / 2 : ℝ) * min (1 / (P.diameter * P.gradientBound))
    (min P.expConcavity
      (4 / ((P.deferral + 1) * P.conversionLoss * P.conversionGradient *
        P.diameter * P.gradientBound)))

noncomputable def is_lightons_run (P : lightons_problem) (run : lightons_run P) : Prop :=
  ∃ (metric : ℕ → online_point P.dimension → online_point P.dimension → ℝ)
      (proposal : ℕ → online_point P.dimension),
    run.surrogatePoint 0 = 0 ∧
    (∀ v w, metric 0 v w = P.epsilon * inner ℝ v w) ∧
    (∀ t v w,
      metric (t + 1) v w =
        metric t v w +
          inner ℝ (P.conversionLoss • run.surrogateGradient t) v *
            inner ℝ (P.conversionLoss • run.surrogateGradient t) w) ∧
    (∀ t z,
      inner ℝ (P.conversionLoss • run.surrogateGradient t)
          (proposal t - run.surrogatePoint t) +
          gamma_prime P / 2 *
            metric (t + 1) (proposal t - run.surrogatePoint t)
              (proposal t - run.surrogatePoint t) ≤
        inner ℝ (P.conversionLoss • run.surrogateGradient t)
          (z - run.surrogatePoint t) +
          gamma_prime P / 2 *
            metric (t + 1) (z - run.surrogatePoint t)
              (z - run.surrogatePoint t)) ∧
    (∀ t,
      if ‖proposal t‖ ≤ P.deferral * P.diameter / 2 then
        run.surrogatePoint (t + 1) = proposal t
      else
        run.surrogatePoint (t + 1) ∈ P.domain ∧
          ∀ u, u ∈ P.domain →
            metric (t + 1) (run.surrogatePoint (t + 1) - proposal t)
                (run.surrogatePoint (t + 1) - proposal t) ≤
              metric (t + 1) (u - proposal t) (u - proposal t)) ∧
    (∀ t u, u ∈ P.domain →
      dist (run.decision t) (run.surrogatePoint t) ≤
        dist u (run.surrogatePoint t)) ∧
    (∀ T,
      run.runtime T =
        ∑ t ∈ Finset.range T,
          (run.surrogateGradientRuntime t + P.projectionCost +
            (P.dimension : ℝ) ^ 2 +
            if ‖proposal t‖ ≤ P.deferral * P.diameter / 2 then 0
            else Real.rpow (P.dimension : ℝ) P.matrixExponent))

noncomputable def lightons_regret_bound (P : lightons_problem) (T : ℕ) : ℝ :=
  (P.dimension : ℝ) / (2 * gamma_prime P) *
      Real.log (1 +
        (P.conversionLoss ^ 2 * P.conversionGradient ^ 2 * P.gradientBound ^ 2 /
          ((P.dimension : ℝ) * P.epsilon)) * (T : ℝ)) +
    gamma_prime P * P.epsilon * P.diameter ^ 2 / 8

noncomputable def lightons_runtime_scale (P : lightons_problem) (T : ℕ) : ℝ :=
  (P.projectionCost + (P.dimension : ℝ) ^ 2) * (T : ℝ) +
    (P.deferral - 1)⁻¹ *
      Real.rpow (P.dimension : ℝ) (P.matrixExponent + 0.5) *
      Real.sqrt ((T : ℝ) / P.epsilon) * Real.log (T : ℝ)

theorem lightons :
    ∀ C_gradient : ℝ, 0 ≤ C_gradient →
      ∀ P : lightons_problem,
        ∃ C_projection : ℝ, 0 ≤ C_projection ∧
          ∀ run : lightons_run P,
          (∀ t : ℕ, run.surrogateGradientRuntime t ≤
            C_gradient * (P.projectionCost + (P.dimension : ℝ))) →
          is_lightons_run P run →
          (∀ (T : ℕ) (u : online_point P.dimension), u ∈ P.domain →
            online_regret P run T u ≤ lightons_regret_bound P T) ∧
          ∀ T : ℕ, 2 ≤ T →
            run.runtime T ≤
              (C_gradient + C_projection + 1) * lightons_runtime_scale P T := by sorry

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic

set_option maxHeartbeats 500000

structure dr_parameters where
  delta : ℝ
  sampleSize : ℕ
  folds : ℕ
  gridIntervals : ℕ
  actionCount : ℕ
  natarajanDim : ℕ
  outcomeBound : ℝ
  overlapLower : ℝ
  quantileLipschitz : ℝ
  utilityLipschitz : ℝ
  rateF : ℕ → ℝ → ℝ
  rateM : ℕ → ℝ → ℝ

def dr_parameter_assumptions (p : dr_parameters) : Prop :=
  0 < p.delta ∧ p.delta < (1 / 4 : ℝ) ∧
  0 < p.folds ∧ 0 < p.gridIntervals ∧ 0 < p.actionCount ∧
  1 ≤ p.natarajanDim ∧ p.natarajanDim ≤ p.sampleSize ∧
  0 ≤ p.outcomeBound ∧ 0 < p.overlapLower ∧
  0 ≤ p.quantileLipschitz ∧ 0 ≤ p.utilityLipschitz ∧
  (∀ γ ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ p.rateF p.sampleSize γ) ∧
  (∀ γ ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ p.rateM p.sampleSize γ) ∧
  AntitoneOn (p.rateF p.sampleSize) (Set.Ioo (0 : ℝ) 1) ∧
  AntitoneOn (p.rateM p.sampleSize) (Set.Ioo (0 : ℝ) 1) ∧
  p.rateM p.sampleSize (p.delta / (3 * (p.folds : ℝ))) ≤ 1

noncomputable def dr_mesh (p : dr_parameters) : ℝ :=
  1 / (p.gridIntervals : ℝ)

noncomputable def dr_variance_complexity (p : dr_parameters) : ℝ :=
  Real.sqrt
      ((2 * (p.folds : ℝ) * (p.natarajanDim : ℝ) *
          Real.log (Real.exp 1 * (p.sampleSize : ℝ) /
            (p.folds : ℝ) * (p.actionCount : ℝ))) /
        (p.sampleSize : ℝ)) +
    Real.sqrt
      ((2 * (p.folds : ℝ) *
          Real.log (8 * (p.gridIntervals : ℝ) * (p.folds : ℝ) / p.delta)) /
        (p.sampleSize : ℝ))

noncomputable def dr_propensity_rate (p : dr_parameters) : ℝ :=
  p.rateF p.sampleSize (p.delta / (3 * (p.folds : ℝ)))

noncomputable def dr_outcome_rate (p : dr_parameters) : ℝ :=
  p.rateM p.sampleSize (p.delta / (3 * (p.folds : ℝ)))

noncomputable def dr_oracle_constant (p : dr_parameters) : ℝ :=
  4 * p.utilityLipschitz * p.outcomeBound * (1 + 2 / p.overlapLower)

noncomputable def dr_grid_constant (p : dr_parameters) : ℝ :=
  2 * p.utilityLipschitz * p.quantileLipschitz *
    (4 + 6 / p.overlapLower)

noncomputable def dr_nuisance_remainder (p : dr_parameters) : ℝ :=
  2 * p.utilityLipschitz *
    (((2 * dr_propensity_rate p * dr_outcome_rate p / p.overlapLower ^ 2) +
        (4 * p.outcomeBound * dr_propensity_rate p / p.overlapLower ^ 2) +
        (2 * (1 + 1 / p.overlapLower) * dr_outcome_rate p)) *
      dr_variance_complexity p +
      5 * dr_propensity_rate p * dr_outcome_rate p / p.overlapLower ^ 2 +
      4 * p.quantileLipschitz * dr_propensity_rate p /
        p.overlapLower ^ 2 * dr_mesh p)

noncomputable def dr_explicit_bound (p : dr_parameters) : ℝ :=
  dr_oracle_constant p * dr_variance_complexity p +
  dr_grid_constant p * dr_mesh p + dr_nuisance_remainder p

noncomputable def dr_coarse_terms (p : dr_parameters) : ℝ :=
  dr_variance_complexity p + dr_mesh p +
  dr_propensity_rate p * dr_outcome_rate p +
  dr_propensity_rate p * dr_variance_complexity p +
  dr_outcome_rate p * dr_variance_complexity p +
  dr_propensity_rate p * dr_mesh p

noncomputable def dr_coarse_constant
    (utilityLipschitz outcomeBound overlapLower quantileLipschitz : ℝ)
    (folds actionCount : ℕ) : ℝ :=
  1 +
  4 * |utilityLipschitz| * |outcomeBound| *
    (1 + 2 / |overlapLower|) +
  2 * |utilityLipschitz| * |quantileLipschitz| *
    (4 + 6 / |overlapLower|) +
  2 * |utilityLipschitz| *
    (2 / |overlapLower| ^ 2 +
      4 * |outcomeBound| / |overlapLower| ^ 2 +
      2 * (1 + 1 / |overlapLower|) +
      5 / |overlapLower| ^ 2 +
      4 * |quantileLipschitz| / |overlapLower| ^ 2)

def dr_valid_quantile_curve (q : ℝ → ℝ) : Prop :=
  MonotoneOn q (Set.Icc (0 : ℝ) 1) ∧
  (∀ t ∈ Set.Ioc (0 : ℝ) 1,
    ContinuousWithinAt q (Set.Icc (0 : ℝ) t) t) ∧
  MeasureTheory.MemLp q 2
    (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))

structure dr_logged_data (Ω Action Context : Type*) (p : dr_parameters) where
  context : Fin p.folds → Fin (p.sampleSize / p.folds) → Ω → Context
  action : Fin p.folds → Fin (p.sampleSize / p.folds) → Ω → Action
  outcomeQuantile :
    Fin p.folds → Fin (p.sampleSize / p.folds) → Ω → ℝ → ℝ

def dr_natarajan_shatters {Action Context Policy : Type*}
    (policyAction : Policy → Context → Action) (S : Set Context) : Prop :=
  S.Finite ∧
    ∃ f₁ f₂ : Context → Action,
      (∀ x ∈ S, f₁ x ≠ f₂ x) ∧
      ∀ T : Set Context, T ⊆ S →
        ∃ π : Policy,
          (∀ x ∈ T, policyAction π x = f₁ x) ∧
          (∀ x ∈ S \ T, policyAction π x = f₂ x)

def dr_natarajan_dimension {Action Context Policy : Type*}
    (policyAction : Policy → Context → Action) (V : ℕ) : Prop :=
  (∃ S : Set Context,
      dr_natarajan_shatters policyAction S ∧ Nat.card S = V) ∧
    ∀ S : Set Context,
      dr_natarajan_shatters policyAction S → Nat.card S ≤ V

structure dr_model (Ω Action Context Policy : Type*) [MeasurableSpace Ω]
    (p : dr_parameters) where
  μ : MeasureTheory.Measure Ω
  data : dr_logged_data Ω Action Context p
  policyAction : Policy → Context → Action
  potentialOutcomeQuantile :
    Fin p.folds → Fin (p.sampleSize / p.folds) → Action → Ω → ℝ → ℝ
  truePropensity : Action → Context → ℝ
  fittedPropensity : Fin p.folds → Ω → Action → Context → ℝ
  trueOutcomeQuantile : Action → Context → ℝ → ℝ
  fittedOutcomeQuantile :
    Fin p.folds → Ω → Action → Context → ℝ → ℝ
  populationPolicyQuantile : Policy → ℝ → ℝ
  populationPolicyQuantileValid :
    ∀ π, dr_valid_quantile_curve (populationPolicyQuantile π)
  utility : {q : ℝ → ℝ // dr_valid_quantile_curve q} → ℝ
  rearrange : (ℝ → ℝ) → ℝ → ℝ
  rearrangeValid : ∀ q, dr_valid_quantile_curve (rearrange q)
  optimalPolicy : Policy
  learnedPolicy : Ω → Policy

def dr_observation {Ω Action Context Policy : Type*} [MeasurableSpace Ω]
    {p : dr_parameters} (m : dr_model Ω Action Context Policy p)
    (z : Fin p.folds × Fin (p.sampleSize / p.folds)) :
    Ω → Context × Action × (ℝ → ℝ) :=
  fun ω =>
    (m.data.context z.1 z.2 ω,
      m.data.action z.1 z.2 ω,
      m.data.outcomeQuantile z.1 z.2 ω)

noncomputable def dr_curve_distance
    (q₁ q₂ : {q : ℝ → ℝ // dr_valid_quantile_curve q}) : ℝ :=
  Real.sqrt
    (MeasureTheory.integral
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
      (fun t => |q₁.1 t - q₂.1 t| ^ 2))

noncomputable def dr_policy_quantile {Ω Action Context Policy : Type*}
    [MeasurableSpace Ω] {p : dr_parameters}
    (m : dr_model Ω Action Context Policy p) (π : Policy) :
    {q : ℝ → ℝ // dr_valid_quantile_curve q} :=
  ⟨m.populationPolicyQuantile π, m.populationPolicyQuantileValid π⟩

noncomputable def dr_score {Ω Action Context Policy : Type*}
    [MeasurableSpace Ω] [DecidableEq Action] {p : dr_parameters}
    (m : dr_model Ω Action Context Policy p) (ω : Ω)
    (l : Fin p.folds) (i : Fin (p.sampleSize / p.folds))
    (π : Policy) (t : ℝ) : ℝ :=
  let x := m.data.context l i ω
  let aπ := m.policyAction π x
  m.fittedOutcomeQuantile l ω aπ x t +
    if m.data.action l i ω = aπ then
      (m.data.outcomeQuantile l i ω t -
        m.fittedOutcomeQuantile l ω aπ x t) /
        m.fittedPropensity l ω (m.data.action l i ω) x
    else 0

noncomputable def dr_raw_estimated_policy_quantile
    {Ω Action Context Policy : Type*} [MeasurableSpace Ω]
    [DecidableEq Action] {p : dr_parameters}
    (m : dr_model Ω Action Context Policy p) (ω : Ω)
    (π : Policy) : ℝ → ℝ :=
  fun t =>
    (Finset.univ.sum fun l : Fin p.folds =>
      (Finset.univ.sum fun i : Fin (p.sampleSize / p.folds) =>
        dr_score m ω l i π t) /
        (((p.sampleSize / p.folds : ℕ) : ℝ))) /
      (p.folds : ℝ)

noncomputable def dr_estimated_policy_quantile
    {Ω Action Context Policy : Type*} [MeasurableSpace Ω]
    [DecidableEq Action] {p : dr_parameters}
    (m : dr_model Ω Action Context Policy p) (ω : Ω)
    (π : Policy) : {q : ℝ → ℝ // dr_valid_quantile_curve q} :=
  ⟨m.rearrange (dr_raw_estimated_policy_quantile m ω π),
    m.rearrangeValid (dr_raw_estimated_policy_quantile m ω π)⟩

def dr_propensity_error {Ω Action Context Policy : Type*}
    [MeasurableSpace Ω] {p : dr_parameters}
    (m : dr_model Ω Action Context Policy p)
    (l : Fin p.folds) (ω : Ω) (r : ℝ) : Prop :=
  ∀ a x,
    |m.fittedPropensity l ω a x - m.truePropensity a x| ≤ r

def dr_outcome_error {Ω Action Context Policy : Type*}
    [MeasurableSpace Ω] {p : dr_parameters}
    (m : dr_model Ω Action Context Policy p)
    (l : Fin p.folds) (ω : Ω) (r : ℝ) : Prop :=
  ∀ a x (t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}),
    |m.fittedOutcomeQuantile l ω a x t -
      m.trueOutcomeQuantile a x t| ≤ r

noncomputable def dr_uniform_deviation
    {Ω Action Context Policy : Type*} [MeasurableSpace Ω]
    [DecidableEq Action] {p : dr_parameters}
    (m : dr_model Ω Action Context Policy p) (ω : Ω) : ℝ :=
  sSup (Set.range fun π : Policy =>
    dr_curve_distance (dr_estimated_policy_quantile m ω π)
      (dr_policy_quantile m π))

noncomputable def dr_good_event
    {Ω Action Context Policy : Type*} [MeasurableSpace Ω]
    [DecidableEq Action] {p : dr_parameters}
    (m : dr_model Ω Action Context Policy p) : Set Ω :=
  {ω | 2 * p.utilityLipschitz * dr_uniform_deviation m ω ≤
    dr_explicit_bound p}

noncomputable def dr_regret {Ω Action Context Policy : Type*} [MeasurableSpace Ω]
    {p : dr_parameters} (m : dr_model Ω Action Context Policy p) (ω : Ω) : ℝ :=
  m.utility (dr_policy_quantile m m.optimalPolicy) -
    m.utility (dr_policy_quantile m (m.learnedPolicy ω))

def high_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (E : Set Ω) (α : ℝ) : Prop :=
  μ.real E ≥ 1 - α

def dr_structural_assumptions {Ω Action Context Policy : Type*}
    [mΩ : MeasurableSpace Ω] [MeasurableSpace Action] [MeasurableSpace Context]
    [Fintype Action] [DecidableEq Action]
    (p : dr_parameters) (m : dr_model Ω Action Context Policy p) : Prop :=
  p.actionCount = Fintype.card Action ∧
  (dr_natarajan_dimension m.policyAction p.natarajanDim ∧
    (∀ π, Measurable (m.policyAction π)) ∧
    (∀ l i π t, Measurable (fun ω =>
      m.potentialOutcomeQuantile l i
        (m.policyAction π (m.data.context l i ω)) ω t)) ∧
    (∀ l i π t, Measurable (fun ω =>
      m.trueOutcomeQuantile
        (m.policyAction π (m.data.context l i ω))
        (m.data.context l i ω) t)) ∧
    (∀ l i π t, Measurable (fun ω => dr_score m ω l i π t))) ∧
  p.folds ∣ p.sampleSize ∧ p.folds ≤ p.sampleSize ∧
  ProbabilityTheory.iIndepFun
    (fun z : Fin p.folds × Fin (p.sampleSize / p.folds) =>
      dr_observation m z) m.μ ∧
  (∀ z z' : Fin p.folds × Fin (p.sampleSize / p.folds),
    ProbabilityTheory.IdentDistrib (dr_observation m z)
      (dr_observation m z') m.μ m.μ) ∧
  (∀ l, ∃ fitInfo : MeasurableSpace Ω,
    fitInfo ≤ mΩ ∧
    let heldoutInfo := MeasurableSpace.comap
      (fun ω i => @dr_observation Ω Action Context Policy mΩ p m (l, i) ω)
      inferInstance
    heldoutInfo ≤ mΩ ∧
    @ProbabilityTheory.Indep Ω fitInfo heldoutInfo mΩ
      (@dr_model.μ Ω Action Context Policy mΩ p m) ∧
    @Measurable (Ω × (Action × Context)) ℝ
      (fitInfo.prod inferInstance) inferInstance
      (fun z => @dr_model.fittedPropensity Ω Action Context Policy mΩ p m
        l z.1 z.2.1 z.2.2) ∧
    (∀ t, @Measurable (Ω × (Action × Context)) ℝ
      (fitInfo.prod inferInstance) inferInstance
      (fun z => @dr_model.fittedOutcomeQuantile Ω Action Context Policy mΩ p m
        l z.1 z.2.1 z.2.2 t))) ∧
  (∀ l i, ∀ᵐ ω ∂m.μ, ∀ t,
    m.data.outcomeQuantile l i ω t =
      m.potentialOutcomeQuantile l i (m.data.action l i ω) ω t) ∧
  (∀ π t, (dr_policy_quantile m π).1 t =
    (Finset.univ.sum fun l : Fin p.folds =>
      Finset.univ.sum fun i : Fin (p.sampleSize / p.folds) =>
        MeasureTheory.integral m.μ (fun ω =>
          m.potentialOutcomeQuantile l i
            (m.policyAction π (m.data.context l i ω)) ω t)) /
      (p.sampleSize : ℝ)) ∧
  (∀ π t, (dr_policy_quantile m π).1 t =
    (Finset.univ.sum fun l : Fin p.folds =>
      Finset.univ.sum fun i : Fin (p.sampleSize / p.folds) =>
        MeasureTheory.integral m.μ (fun ω =>
          m.trueOutcomeQuantile
            (m.policyAction π (m.data.context l i ω))
            (m.data.context l i ω) t)) /
      (p.sampleSize : ℝ)) ∧
  (∀ l i a (h : Context → ℝ),
    MeasureTheory.integral m.μ (fun ω =>
      h (m.data.context l i ω) *
        ((if m.data.action l i ω = a then 1 else 0) -
          m.truePropensity a (m.data.context l i ω))) = 0) ∧
  (∀ l i a t (h : Context → ℝ),
    MeasureTheory.integral m.μ (fun ω =>
      h (m.data.context l i ω) *
        (if m.data.action l i ω = a then
          m.data.outcomeQuantile l i ω t -
            m.trueOutcomeQuantile a (m.data.context l i ω) t
        else 0)) = 0) ∧
  (∀ a x, p.overlapLower ≤ m.truePropensity a x) ∧
  (∀ l ω a x, p.overlapLower ≤ m.fittedPropensity l ω a x) ∧
  (∀ l i a, ∀ᵐ ω ∂m.μ,
    dr_valid_quantile_curve (m.potentialOutcomeQuantile l i a ω)) ∧
  (∀ a x, dr_valid_quantile_curve (m.trueOutcomeQuantile a x)) ∧
  (∀ l ω a x,
    dr_valid_quantile_curve (m.fittedOutcomeQuantile l ω a x)) ∧
  (∀ l i a, ∀ᵐ ω ∂m.μ, ∀ t, t ∈ Set.Icc (0 : ℝ) 1 →
    |m.potentialOutcomeQuantile l i a ω t| ≤ p.outcomeBound) ∧
  (∀ l i a, ∀ᵐ ω ∂m.μ, ∀ s t, s ∈ Set.Icc (0 : ℝ) 1 →
    t ∈ Set.Icc (0 : ℝ) 1 →
      |m.potentialOutcomeQuantile l i a ω t -
        m.potentialOutcomeQuantile l i a ω s| ≤
        p.quantileLipschitz * |t - s|) ∧
  (∀ a x s t, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 →
    |m.trueOutcomeQuantile a x t - m.trueOutcomeQuantile a x s| ≤
      p.quantileLipschitz * |t - s|) ∧
  (∀ l ω a x s t, s ∈ Set.Icc (0 : ℝ) 1 →
    t ∈ Set.Icc (0 : ℝ) 1 →
    |(m.trueOutcomeQuantile a x t -
        m.fittedOutcomeQuantile l ω a x t) -
      (m.trueOutcomeQuantile a x s -
        m.fittedOutcomeQuantile l ω a x s)| ≤
      2 * p.quantileLipschitz * |t - s|) ∧
  (∀ q₁ q₂, |m.utility q₁ - m.utility q₂| ≤
    p.utilityLipschitz * dr_curve_distance q₁ q₂) ∧
  (∀ ω π,
    dr_curve_distance (dr_estimated_policy_quantile m ω π)
        (dr_policy_quantile m π) ≤
      Real.sqrt
        (MeasureTheory.integral
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
          (fun t =>
            |dr_raw_estimated_policy_quantile m ω π t -
              (dr_policy_quantile m π).1 t| ^ 2))) ∧
  (∀ π, m.utility (dr_policy_quantile m π) ≤
    m.utility (dr_policy_quantile m m.optimalPolicy)) ∧
  (∀ ω π, m.utility (dr_estimated_policy_quantile m ω π) ≤
    m.utility
      (dr_estimated_policy_quantile m ω (m.learnedPolicy ω)))

def dr_nuisance_rate_assumptions {Ω Action Context Policy : Type*}
    [MeasurableSpace Ω] (p : dr_parameters)
    (m : dr_model Ω Action Context Policy p) : Prop :=
  ∀ l (γ : ℝ), 0 < γ → γ < 1 →
    high_probability m.μ
      {ω | dr_outcome_error m l ω (p.rateM p.sampleSize γ) ∧
        dr_propensity_error m l ω (p.rateF p.sampleSize γ)} γ

theorem statistical_guarantee_dr {Ω Action Context Policy : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Action] [MeasurableSpace Context]
    [Fintype Action] [DecidableEq Action] (p : dr_parameters)
    (m : dr_model Ω Action Context Policy p)
    [MeasureTheory.IsProbabilityMeasure m.μ]
    (hp : dr_parameter_assumptions p) (hs : dr_structural_assumptions p m)
    (hn : dr_nuisance_rate_assumptions p m)
    (hE : MeasurableSet (dr_good_event m)) :
    high_probability m.μ {ω | dr_regret m ω ≤ dr_explicit_bound p}
        (4 * p.delta) ∧
      0 < dr_coarse_constant p.utilityLipschitz p.outcomeBound
          p.overlapLower p.quantileLipschitz p.folds p.actionCount ∧
        high_probability m.μ {ω | dr_regret m ω ≤
          dr_coarse_constant p.utilityLipschitz p.outcomeBound
            p.overlapLower p.quantileLipschitz p.folds p.actionCount *
              dr_coarse_terms p}
          (4 * p.delta) := by sorry

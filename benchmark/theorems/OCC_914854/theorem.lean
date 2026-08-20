import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.ENNReal.Basic

set_option linter.all false

structure orthogonal_calibration_model
    (X W Z G V H : Type*)
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H] where
  loss : ℝ → G → Z → ℝ
  lossDerivative : ℝ → G → Z → ℝ
  loss_has_derivative :
    ∀ (a : ℝ) (g : G) (z : Z),
      HasDerivAt (fun t : ℝ => loss t g z) (lossDerivative a g z) a
  covariate : Z → X
  nuisanceEval : G →ₗ[ℝ] (W → V)
  nuisanceEval_injective : Function.Injective nuisanceEval
  conditionalExpectationGivenX : (Z → ℝ) → H
  conditionalExpectationGivenPrediction : (X → ℝ) → H → H
  conditionalScore : (X → ℝ) → G → H
  conditionalScore_eq :
    ∀ (θ : X → ℝ) (g : G),
      conditionalScore θ g =
        conditionalExpectationGivenX
          (fun z : Z => lossDerivative (θ (covariate z)) g z)
  calibrationScore : (X → ℝ) → G → H
  calibrationScore_eq :
    ∀ (θ : X → ℝ) (g : G),
      calibrationScore θ g =
        conditionalExpectationGivenPrediction θ (conditionalScore θ g)
  calibration_contraction :
    ∀ (θ : X → ℝ) (g h : G),
      ‖calibrationScore θ g - calibrationScore θ h‖ ≤
        ‖conditionalScore θ g - conditionalScore θ h‖

def pointwise_nuisance_segment
    {X W Z G V H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (model : orthogonal_calibration_model X W Z G V H) (g h : G) : Set G :=
  {f | ∃ weight : W → ℝ,
    (∀ w : W, weight w ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ w : W,
        model.nuisanceEval f w =
          (weight w) • model.nuisanceEval g w +
            (1 - weight w) • model.nuisanceEval h w}

def calibration_error
    {X W Z G V H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (model : orthogonal_calibration_model X W Z G V H)
    (θ : X → ℝ) (g : G) : ENNReal :=
  ENNReal.ofReal ‖model.calibrationScore θ g‖

def universally_orthogonal
    {X W Z G V H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (model : orthogonal_calibration_model X W Z G V H) (g₀ : G) : Prop :=
  ∀ (θ : X → ℝ) (g : G),
    deriv (fun t : ℝ =>
      model.conditionalScore θ (g₀ + t • (g - g₀))) 0 = 0

noncomputable def second_nuisance_derivative
    {X W Z G V H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (model : orthogonal_calibration_model X W Z G V H)
    (θ : X → ℝ) (f v : G) : H :=
  deriv
    (fun t : ℝ =>
      deriv (fun s : ℝ => model.conditionalScore θ (f + s • v)) t) 0

def second_nuisance_derivative_exists
    {X W Z G V H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (model : orthogonal_calibration_model X W Z G V H) (g₀ : G) : Prop :=
  ∀ (θ : X → ℝ) (g f : G),
    ∃ d₁ d₂ : H,
      HasDerivAt
          (fun t : ℝ =>
            model.conditionalScore θ (f + t • (g - g₀))) d₁ 0 ∧
        HasDerivAt
          (fun t : ℝ =>
            deriv
              (fun s : ℝ =>
                model.conditionalScore θ (f + s • (g - g₀))) t) d₂ 0

noncomputable def nuisance_error
    {X W Z G V H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (model : orthogonal_calibration_model X W Z G V H)
    (g h : G) (θ : X → ℝ) : ENNReal :=
  ⨆ f : {f : G // f ∈ pointwise_nuisance_segment model g h},
    ENNReal.ofReal
      ‖second_nuisance_derivative model θ f.1 (h - g)‖

theorem universal
    {X W Z G V H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (model : orthogonal_calibration_model X W Z G V H)
    (g₀ : G)
    (horth : universally_orthogonal model g₀)
    (hsecond : second_nuisance_derivative_exists model g₀)
    (g : G) (θ : X → ℝ) :
    calibration_error model θ g₀ ≤
      (2 : ENNReal)⁻¹ * nuisance_error model g g₀ θ +
        calibration_error model θ g := by
  sorry

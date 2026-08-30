import Architect
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:soft-big-o"
  (statement := /-- For functions \(f,g:\mathbb N\to\mathbb R\), write
  \(f=\widetilde{\mathcal O}(g)\) if, for some nonnegative integral exponent
  \(k\), the function \(f(n)\) is eventually bounded in norm by a constant
  multiple of \((\log(n+2))^k g(n)\). -/)
  (title := /-- Soft asymptotic order -/)
  (latexEnv := "definition")]
def soft_big_o (f g : ℕ → ℝ) : Prop :=
  ∃ k : ℕ,
    Asymptotics.IsBigO Filter.atTop f
      (fun n => (Real.log ((n : ℝ) + 2)) ^ k * g n)

@[blueprint "def:uniform-soft-bound"
  (statement := /-- Let \(f\) and \(g\) be real-valued random quantities
  indexed by the horizon.  A uniform soft bound \(f\lesssim_{\log}g\) means
  that there are \(C>0\) and \(k\in\mathbb N\) such that, for all sufficiently
  large \(T\), the inequality
  \(f_T(\omega)\le C(\log(T+2))^k g_T(\omega)\) holds for every outcome
  \(\omega\). -/)
  (title := /-- Uniform soft bound for random quantities -/)
  (latexEnv := "definition")]
def uniform_soft_bound {Ω : Type*} (f g : ℕ → Ω → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∃ k : ℕ, ∀ᶠ T in Filter.atTop,
      ∀ ω, f T ω ≤ C * (Real.log ((T : ℝ) + 2)) ^ k * g T ω

@[blueprint "def:high-probability-soft-bound"
  (statement := /-- Let \(\mu_T\) be a measure on the outcome space at
  horizon \(T\), let \(Q_T\) be a real-valued random quantity, and let
  \(B_{\delta,T}\) be a displayed rate.  Say that \(Q\) is bounded by
  \(B\) with uniform high-probability soft order if there are constants
  \(C>0\) and \(k\in\mathbb N\), independent of \(\delta\), such that
  for every \(0<\delta<1\) and every sufficiently large \(T\), there is a
  measurable event \(E_{\delta,T}\) satisfying
  \(\mu_T(E_{\delta,T})\ge1-\delta\) and
  \[
    Q_T(\omega)\le C(\log(T+2))^kB_{\delta,T}(\omega)
    \qquad\text{for every }\omega\in E_{\delta,T}.
  \] -/)
  (title := /-- Uniform high-probability soft bound -/)
  (latexEnv := "definition")]
def high_probability_soft_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → MeasureTheory.Measure Ω) (Q : ℕ → Ω → ℝ)
    (B : ℝ → ℕ → Ω → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∃ k : ℕ, ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∀ᶠ T in Filter.atTop,
        ∃ E : Set Ω, MeasurableSet E ∧
          1 - δ ≤ (μ T).real E ∧
            ∀ ω ∈ E, Q T ω ≤
              C * (Real.log ((T : ℝ) + 2)) ^ k * B δ T ω

@[blueprint "def:identified-property"
  (statement := /-- An identified property on distributions over
  \(\mathcal Y\) consists of a property
  \(\Gamma:\mathcal P(\mathcal Y)\to[0,1]\) and an identification
  function \(V:[0,1]\times\mathcal Y\to\mathbb R\). -/)
  (title := /-- Identified property -/)
  (latexEnv := "definition")]
structure identified_property (Y : Type*) [MeasurableSpace Y] where
  property : MeasureTheory.Measure Y → Set.Icc (0 : ℝ) 1
  identification : Set.Icc (0 : ℝ) 1 → Y → ℝ

@[blueprint "def:elicitable-property"
  (statement := /-- An identified property \(\Gamma\) is elicitable if there
  exists a loss \(\ell:[0,1]\times\mathcal Y\to\mathbb R\) that is strictly
  consistent for \(\Gamma\).  Thus, for every probability measure \(\nu\)
  and every \(\gamma\in[0,1]\), whenever the two relevant loss functions are
  integrable,
  \[
    \int \ell(\Gamma(\nu),y)\,d\nu(y)
      \le \int \ell(\gamma,y)\,d\nu(y),
  \]
  and equality holds if and only if \(\gamma=\Gamma(\nu)\). -/)
  (title := /-- Elicitable property -/)
  (latexEnv := "definition")]
noncomputable def elicitable_property {Y : Type*} [MeasurableSpace Y]
    (Γ : identified_property Y) : Prop :=
  ∃ loss : Set.Icc (0 : ℝ) 1 → Y → ℝ,
    ∀ (ν : MeasureTheory.Measure Y), ν Set.univ = 1 →
      ∀ γ : Set.Icc (0 : ℝ) 1,
        MeasureTheory.Integrable (fun y => loss (Γ.property ν) y) ν →
        MeasureTheory.Integrable (fun y => loss γ y) ν →
          MeasureTheory.integral ν (fun y => loss (Γ.property ν) y) ≤
              MeasureTheory.integral ν (fun y => loss γ y) ∧
            (MeasureTheory.integral ν (fun y => loss (Γ.property ν) y) =
                MeasureTheory.integral ν (fun y => loss γ y) ↔
              γ = Γ.property ν)

@[blueprint "def:is-identification-function"
  (statement := /-- The function \(V\) identifies \(\Gamma\) if, for every
  probability measure \(\nu\) and every \(\gamma\in[0,1]\) for which
  \(V(\gamma,\cdot)\) is integrable,
  \[
    \int V(\gamma,y)\,d\nu(y)=0
      \quad\Longleftrightarrow\quad
    \gamma=\Gamma(\nu).
  \] -/)
  (title := /-- Identification property -/)
  (latexEnv := "definition")]
noncomputable def is_identification_function {Y : Type*} [MeasurableSpace Y]
    (Γ : identified_property Y) : Prop :=
  ∀ (ν : MeasureTheory.Measure Y), ν Set.univ = 1 →
    ∀ γ : Set.Icc (0 : ℝ) 1,
      MeasureTheory.Integrable (fun y => Γ.identification γ y) ν →
        (MeasureTheory.integral ν (fun y => Γ.identification γ y) = 0 ↔
          γ = Γ.property ν)

@[blueprint "def:lipschitz-identification"
  (statement := /-- The identification function \(V\) is
  \(\rho\)-Lipschitz in its prediction coordinate if \(\rho\ge0\) and
  \[
    |V(p,y)-V(q,y)|\le \rho |p-q|
  \]
  for every \(p,q\in[0,1]\) and \(y\in\mathcal Y\). -/)
  (title := /-- Lipschitz identification function -/)
  (latexEnv := "definition")]
def lipschitz_identification {Y : Type*} [MeasurableSpace Y]
    (Γ : identified_property Y) (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧
    ∀ p q y,
      |Γ.identification p y - Γ.identification q y| ≤
        ρ * |(p : ℝ) - (q : ℝ)|

@[blueprint "def:online-agnostic-learner"
  (statement := /-- An online agnostic learner on \(\mathcal X\) supplies,
  for every horizon and every context and sign sequence, a real-valued
  predictor at each round, together with a regret function
  \(\mathsf{Reg}:\mathbb N\to\mathbb R\). -/)
  (title := /-- Online agnostic learner -/)
  (latexEnv := "definition")]
structure online_agnostic_learner (X : Type*) where
  predict :
    (n : ℕ) → (Fin n → X) → (Fin n → ℝ) → Fin n → X → ℝ
  regret : ℕ → ℝ

@[blueprint "def:online-agnostic-regret"
  (statement := /-- A learner \(A\) has regret \(\mathsf{Reg}\) against
  \(\mathcal F\) if, for every horizon \(n\), contexts \(x_t\), and real
  coefficients \(\kappa_t\),
  \[
    \sup_{f\in\mathcal F}\sum_t f(x_t)\kappa_t
      \le \sum_t A_t(x_t)\kappa_t+\mathsf{Reg}(n).
  \] -/)
  (title := /-- Online agnostic regret guarantee -/)
  (latexEnv := "definition")]
noncomputable def online_agnostic_regret {X : Type*}
    (A : online_agnostic_learner X) (F : Set (X → ℝ)) : Prop :=
  ∀ (n : ℕ) (x : Fin n → X) (κ : Fin n → ℝ),
    sSup {a : ℝ | ∃ f ∈ F, a = ∑ t, f (x t) * κ t} ≤
      (∑ t, A.predict n x κ t (x t) * κ t) + A.regret n

@[blueprint "def:forecasting-process"
  (statement := /-- A forecasting process records, for every horizon \(T\)
  and outcome \(\omega\), the contexts \(x_t\), labels \(y_t\), predictions
  \(p_t\in[0,1]\), the number \(N_T\) of grid points, and the probability
  law \(\mu_T\).  Each \(\mu_T\) has total mass one and each \(N_T\) is
  positive. -/)
  (title := /-- Probabilistic forecasting process -/)
  (latexEnv := "definition")]
structure forecasting_process (X Y Ω : Type*) [MeasurableSpace Ω] where
  measure : ℕ → MeasureTheory.Measure Ω
  context : (T : ℕ) → Ω → Fin T → X
  label : (T : ℕ) → Ω → Fin T → Y
  prediction : (T : ℕ) → Ω → Fin T → Set.Icc (0 : ℝ) 1
  gridSize : ℕ → ℕ
  gridSize_pos : ∀ T, 0 < gridSize T
  probability : ∀ T, measure T Set.univ = 1

@[blueprint "def:grid-point"
  (statement := /-- For \(N\ge1\) and \(i\in\{0,\ldots,N-1\}\), define the
  corresponding prediction-grid point by \(z_i=(i+1)/N\).  Thus the grid is
  \(\{1/N,2/N,\ldots,1\}\). -/)
  (title := /-- Uniform prediction grid -/)
  (latexEnv := "definition")]
noncomputable def grid_point (N : ℕ) (i : Fin N) : ℝ :=
  ((i.1 + 1 : ℕ) : ℝ) / (N : ℝ)

@[blueprint "def:prediction-bucket"
  (statement := /-- The \(i\)-th prediction bucket consists of the rounds
  on which the forecaster predicts the grid point \(z_i\). -/)
  (title := /-- Prediction bucket -/)
  (latexEnv := "definition")]
noncomputable def prediction_bucket {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (T : ℕ) (ω : Ω)
    (i : Fin (P.gridSize T)) : Finset (Fin T) := by
  classical
  exact Finset.univ.filter
    (fun t => (P.prediction T ω t : ℝ) = grid_point (P.gridSize T) i)

@[blueprint "def:uses-prediction-grid"
  (statement := /-- A forecasting process uses its prediction grid if every
  prediction at every horizon and outcome equals one of the declared grid
  points. -/)
  (title := /-- Grid-supported predictions -/)
  (latexEnv := "definition")]
def uses_prediction_grid {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) : Prop :=
  ∀ (T : ℕ) (ω : Ω) (t : Fin T),
    ∃ i : Fin (P.gridSize T),
      (P.prediction T ω t : ℝ) = grid_point (P.gridSize T) i

@[blueprint "def:bucket-count"
  (statement := /-- The occupancy \(n_i\) of a prediction bucket is its
  number of rounds. -/)
  (title := /-- Prediction-bucket occupancy -/)
  (latexEnv := "definition")]
noncomputable def bucket_count {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (T : ℕ) (ω : Ω)
    (i : Fin (P.gridSize T)) : ℕ :=
  (prediction_bucket P T ω i).card

@[blueprint "def:bucket-correlation"
  (statement := /-- For a nonempty hypothesis class \(\mathcal F\), the
  normalized correlation in bucket \(i\) is
  \[
    d_i=\frac1{n_i}\sup_{f\in\mathcal F}
      \left|\sum_{t:p_t=z_i} f(x_t)V(p_t,y_t)\right|.
  \]
  It is defined to be zero when \(n_i=0\). -/)
  (title := /-- Normalized bucket correlation -/)
  (latexEnv := "definition")]
noncomputable def bucket_correlation {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (F : Set (X → ℝ))
    (V : Set.Icc (0 : ℝ) 1 → Y → ℝ) (T : ℕ) (ω : Ω)
    (i : Fin (P.gridSize T)) : ℝ :=
  if bucket_count P T ω i = 0 then 0
  else
    ((bucket_count P T ω i : ℕ) : ℝ)⁻¹ *
      sSup {a : ℝ | ∃ f ∈ F,
        a =
          |∑ t ∈ prediction_bucket P T ω i,
            f (P.context T ω t) *
              V (P.prediction T ω t) (P.label T ω t)|}

@[blueprint "def:swap-multicalibration-error"
  (statement := /-- For \(r\ge1\), the \(\ell_r\)-swap multicalibration
  error of a grid-supported forecasting process is
  \[
    \operatorname{smcal}_{V,r}(\mathcal F)
      =\sum_{i=0}^{N_T-1} n_i d_i^r,
  \]
  where \(n_i\) and \(d_i\) are the bucket occupancy and normalized bucket
  correlation. -/)
  (title := /-- Swap multicalibration error -/)
  (latexEnv := "definition")]
noncomputable def swap_multicalibration_error
    {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (F : Set (X → ℝ))
    (V : Set.Icc (0 : ℝ) 1 → Y → ℝ)
    (r : ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  ∑ i : Fin (P.gridSize T),
    (bucket_count P T ω i : ℝ) *
      (bucket_correlation P F V T ω i) ^ r

@[blueprint "def:tuned-grid-size"
  (statement := /-- For an analysis exponent \(q\ge2\), choose the integral
  discretization size
  \[
    N_q(T)=\max\{1,\lceil T^{1/(q+1)}\rceil\}.
  \] -/)
  (title := /-- Tuned discretization size -/)
  (latexEnv := "definition")]
noncomputable def tuned_grid_size (q : ℝ) (T : ℕ) : ℕ :=
  max 1 (Nat.ceil ((T : ℝ) ^ (1 / (q + 1))))

@[blueprint "def:regret-contribution"
  (statement := /-- The aggregate learner-regret contribution at exponent
  \(q\) is
  \[
    \sum_i n_i\left(\frac{\mathsf{Reg}(n_i)}{n_i}\right)^q,
  \]
  with Lean's totalized division convention for empty buckets. -/)
  (title := /-- Aggregate bucket-regret contribution -/)
  (latexEnv := "definition")]
noncomputable def regret_contribution {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (A : online_agnostic_learner X)
    (q : ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  ∑ i : Fin (P.gridSize T),
    (bucket_count P T ω i : ℝ) *
      (A.regret (bucket_count P T ω i) /
        (bucket_count P T ω i : ℝ)) ^ q

@[blueprint "def:discretization-contribution"
  (statement := /-- Before optimizing \(N\), the discretization and
  concentration contribution is
  \[
    \rho^q\frac{T}{N^q}
      +N\left(\log\frac{N}{\delta}\right)^{q/2}.
  \] -/)
  (title := /-- Pre-optimization discretization contribution -/)
  (latexEnv := "definition")]
noncomputable def discretization_contribution
    {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (q ρ δ : ℝ) (T : ℕ) : ℝ :=
  ρ ^ q * (T : ℝ) / (P.gridSize T : ℝ) ^ q +
    (P.gridSize T : ℝ) *
      (Real.log ((P.gridSize T : ℝ) / δ)) ^ (q / 2)

@[blueprint "def:preoptimized-rate"
  (statement := /-- The pre-optimization upper bound supplied by the
  per-bucket deviation estimate is the sum of the discretization,
  concentration, and aggregate learner-regret contributions. -/)
  (title := /-- Pre-optimization swap-error rate -/)
  (latexEnv := "definition")]
noncomputable def preoptimized_rate {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (A : online_agnostic_learner X)
    (q ρ δ : ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  discretization_contribution P q ρ δ T +
    regret_contribution P A q T ω

@[blueprint "def:oracle-efficient-execution"
  (statement := /-- A process is an oracle-efficient execution at exponent
  \(q\) if the paper's per-bucket deviation lemma yields, for every
  \(0<\delta<1\), a high-probability soft bound on its swap error by the
  pre-optimization rate, with a common soft-bound constant and polylogarithmic
  exponent for all \(\delta\).  Each success event is required to be
  measurable.  This predicate is the abstract interface for the algorithm
  that instantiates \(2N_T\) copies of the online agnostic learner. -/)
  (title := /-- Oracle-efficient algorithm interface -/)
  (latexEnv := "definition")]
def oracle_efficient_execution
    {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (A : online_agnostic_learner X)
    (F : Set (X → ℝ)) (V : Set.Icc (0 : ℝ) 1 → Y → ℝ)
    (q ρ : ℝ) : Prop :=
  high_probability_soft_bound P.measure
    (swap_multicalibration_error P F V q)
    (fun δ => preoptimized_rate P A q ρ δ)

@[blueprint "def:large-exponent-rate"
  (statement := /-- For \(q\ge2\), define
  \[
  R_{\ge2}(T,\delta)=
    \rho^qT^{1/(q+1)}
    +T^{1/(q+1)}\left(\log\frac1\delta\right)^{q/2}
    +T^{1-q+q/(q+1)+\alpha q^2/(q+1)}C^q
    +T^{1/(q+1)}C^q .
  \] -/)
  (title := /-- Rate for exponents at least two -/)
  (latexEnv := "definition")]
noncomputable def large_exponent_rate
    (q ρ α complexity δ : ℝ) (T : ℕ) : ℝ :=
  ρ ^ q * (T : ℝ) ^ (1 / (q + 1)) +
    (T : ℝ) ^ (1 / (q + 1)) *
      (Real.log (1 / δ)) ^ (q / 2) +
    (T : ℝ) ^
        (1 - q + q / (q + 1) + α * q ^ 2 / (q + 1)) *
      complexity ^ q +
    (T : ℝ) ^ (1 / (q + 1)) * complexity ^ q

@[blueprint "def:small-exponent-rate"
  (statement := /-- For \(1\le r<2\), define
  \[
  R_{<2}(T,\delta)=
    \rho^rT^{1-r/3}
    +T^{1-r/3}\left(\log\frac1\delta\right)^{r/2}
    +T^{1+2r(\alpha-1)/3}C^r
    +T^{1-r/3}C^r .
  \] -/)
  (title := /-- Rate for exponents below two -/)
  (latexEnv := "definition")]
noncomputable def small_exponent_rate
    (r ρ α complexity δ : ℝ) (T : ℕ) : ℝ :=
  ρ ^ r * (T : ℝ) ^ (1 - r / 3) +
    (T : ℝ) ^ (1 - r / 3) *
      (Real.log (1 / δ)) ^ (r / 2) +
    (T : ℝ) ^ (1 + 2 * r * (α - 1) / 3) *
      complexity ^ r +
    (T : ℝ) ^ (1 - r / 3) * complexity ^ r

@[blueprint "lem:bucket-counts-sum"
  (statement := /-- Let \(X\), \(Y\), and \(\Omega\) be types, let
  \(\Omega\) be equipped with a measurable space, and let \(P\) be a
  forecasting process on these spaces.  Suppose that every prediction of
  \(P\) belongs to its declared grid.  Then, for every horizon \(T\in
  \mathbb N\) and every outcome \(\omega\in\Omega\), writing \(N_T\) for
  the grid size and \(n_i\) for the cardinality of the \(i\)-th prediction
  bucket,
  \[
    \sum_{i=0}^{N_T-1}n_i=T.
  \] -/)
  (proof := /-- By \(\cref{def:uses-prediction-grid}\), choose for every
  round \(t\in\operatorname{Fin}(T)\) an index \(i(t)\) whose grid point is
  the prediction at \(t\).  The positivity of the grid size in
  \(\cref{def:forecasting-process}\), together with the formula in
  \(\cref{def:grid-point}\), shows that the grid-point map is injective.
  Hence \(\cref{def:prediction-bucket, def:bucket-count}\) identify the
  \(i\)-th bucket count with the cardinality of the fiber
  \(\{t:i(t)=i\}\).  The fiberwise cardinality formula then gives
  \(\sum_i n_i=|\operatorname{Fin}(T)|=T\). -/)
  (title := /-- Prediction buckets partition the rounds -/)
  (latexEnv := "lemma")]
lemma bucket_counts_sum {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (hgrid : uses_prediction_grid P)
    (T : ℕ) (ω : Ω) :
    ∑ i : Fin (P.gridSize T), bucket_count P T ω i = T := by
  classical
  let index : Fin T → Fin (P.gridSize T) := fun t =>
    Classical.choose (hgrid T ω t)
  have hindex (t : Fin T) :
      (P.prediction T ω t : ℝ) = grid_point (P.gridSize T) (index t) :=
    Classical.choose_spec (hgrid T ω t)
  have hpoint : Function.Injective (grid_point (P.gridSize T)) := by
    intro i j hij
    apply Fin.ext
    have hN : ((P.gridSize T : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (P.gridSize_pos T))
    have hij' : (((i.1 + 1 : ℕ) : ℝ)) = (((j.1 + 1 : ℕ) : ℝ)) := by
      exact (div_left_inj' hN).mp hij
    have hij'' : i.1 + 1 = j.1 + 1 := by
      exact_mod_cast hij'
    exact Nat.add_right_cancel hij''
  calc
    ∑ i : Fin (P.gridSize T), bucket_count P T ω i =
        ∑ i : Fin (P.gridSize T),
          ((Finset.univ.filter fun t : Fin T => index t = i).card) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold bucket_count prediction_bucket
      congr 1
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ht
        apply hpoint
        rw [← hindex t]
        exact ht
      · intro ht
        rw [← ht]
        exact hindex t
    _ = (Finset.univ : Finset (Fin T)).card := by
      symm
      simpa using
        (Finset.card_eq_sum_card_fiberwise
          (s := (Finset.univ : Finset (Fin T)))
          (t := (Finset.univ : Finset (Fin (P.gridSize T))))
          (f := index) (by simp))
    _ = T := by simp

@[blueprint "lem:oracle-efficient-preoptimized-bound"
  (statement := /-- Let \(q\ge2\), and suppose that \(P\) is an
  oracle-efficient execution with learner \(A\), class \(F\), identification
  function \(V\), and parameter \(\rho\).  Then there exist \(C>0\) and
  \(k\in\mathbb N\), independent of \(\delta\), such that, for every
  \(0<\delta<1\) and all sufficiently large horizons \(T\), there is a
  measurable event \(E_{\delta,T}\) having \(P\)'s horizon-\(T\)
  probability at least \(1-\delta\), and every \(\omega\in E_{\delta,T}\)
  satisfies
  \[
    \operatorname{smcal}_{V,q}(F;T,\omega)
      \le C(\log(T+2))^k
        \operatorname{preopt}_{P,A,q,\rho}(\delta,T,\omega).
  \] -/)
  (proof := /-- By \(\cref{def:oracle-efficient-execution}\), the hypothesis
  that \(P\) is an oracle-efficient execution is definitionally the asserted
  high-probability soft bound. -/)
  (title := /-- Oracle-efficient pre-optimization estimate -/)
  (latexEnv := "lemma")]
lemma oracle_efficient_preoptimized_bound
    {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (A : online_agnostic_learner X)
    (F : Set (X → ℝ)) (V : Set.Icc (0 : ℝ) 1 → Y → ℝ)
    (q ρ : ℝ)
    (hq : 2 ≤ q)
    (hAlgorithm : oracle_efficient_execution P A F V q ρ) :
    high_probability_soft_bound P.measure
      (swap_multicalibration_error P F V q)
      (fun δ => preoptimized_rate P A q ρ δ) := by
  exact hAlgorithm

@[blueprint "lem:soft-big-o-positive-pointwise"
  (statement := /-- Let \(R:\mathbb N\to\mathbb R\) be nonnegative, let
  \(\alpha\in\mathbb R\), and let \(C>0\).  If
  \(R(n)=\widetilde{\mathcal O}(n^\alpha C)\), then there exist
  \(K>0\) and \(k\in\mathbb N\) such that, for every positive integer
  \(n\),
  \[
    R(n)\le K(\log(n+2))^k n^\alpha C.
  \] -/)
  (proof := /-- Unfold \(\cref{def:soft-big-o}\) and apply the global-bound
  characterization of big-O sequences on \(\mathbb N\).  Its comparison
  function is nonzero at every positive integer because
  \(\log(n+2)>0\), \(n^\alpha>0\), and \(C>0\).  The resulting norm
  inequality is the stated inequality because both \(R(n)\) and the
  comparison function are nonnegative. -/)
  (title := /-- Pointwise form of a nonnegative soft asymptotic bound -/)
  (latexEnv := "lemma")]
lemma soft_big_o_positive_pointwise
    (R : ℕ → ℝ) (α complexity : ℝ)
    (hcomplexity : 0 < complexity)
    (hR_nonneg : ∀ n, 0 ≤ R n)
    (hR : soft_big_o R (fun n => (n : ℝ) ^ α * complexity)) :
    ∃ K : ℝ, 0 < K ∧
      ∃ k : ℕ, ∀ n : ℕ, 0 < n →
        R n ≤ K * (Real.log ((n : ℝ) + 2)) ^ k *
          (n : ℝ) ^ α * complexity := by
  rcases hR with ⟨k, hk⟩
  rcases Asymptotics.bound_of_isBigO_nat_atTop hk with ⟨K, hKpos, hK⟩
  refine ⟨K, hKpos, k, ?_⟩
  intro n hn
  have hlog : 0 < Real.log ((n : ℝ) + 2) :=
    Real.log_pos (by exact_mod_cast (show 1 < n + 2 by omega))
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hg : (Real.log ((n : ℝ) + 2)) ^ k *
      ((n : ℝ) ^ α * complexity) ≠ 0 := by
    positivity
  have hb := hK hg
  rw [Real.norm_eq_abs, abs_of_nonneg (hR_nonneg n)] at hb
  rw [Real.norm_eq_abs,
    abs_of_pos (by positivity :
      0 < (Real.log ((n : ℝ) + 2)) ^ k *
        ((n : ℝ) ^ α * complexity))] at hb
  calc
    R n ≤ K * ((Real.log ((n : ℝ) + 2)) ^ k *
        ((n : ℝ) ^ α * complexity)) := hb
    _ = _ := by ring

@[blueprint "lem:tuned-bucket-power-sum-bound"
  (statement := /-- Let \(q\ge2\), \(0\le\alpha<1\), and let a
  grid-supported forecasting process use the tuned grid
  \(N_T=N_q(T)\).  For every positive horizon \(T\) and every outcome,
  each bucket occupancy satisfies \(n_i\le T\), and, with
  \(\beta=1+q(\alpha-1)\),
  \[
    \sum_i n_i^\beta\le4\left(
      T^{1-q+q/(q+1)+\alpha q^2/(q+1)}+T^{1/(q+1)}\right).
  \] -/)
  (proof := /-- By \(\cref{lem:bucket-counts-sum}\), the occupancies are
  nonnegative and sum to \(T\), so each is at most \(T\).  Put
  \(s=1/(q+1)\).  From \(\cref{def:tuned-grid-size}\) and the ceiling
  inequalities,
  \[
    T^s\le N_T\le2T^s.
  \]
  Since \(\beta=1+q(\alpha-1)<1\), first suppose \(\beta\ge0\) and
  set \(a=T/N_T\).  If \(n_i\le a\), then
  \(n_i^\beta\le a^\beta\); otherwise
  \(n_i^\beta=n_i n_i^{\beta-1}\le n_i a^{\beta-1}\).
  Summing the resulting bound
  \(n_i^\beta\le a^\beta+n_i a^{\beta-1}\) gives
  \(\sum_i n_i^\beta\le2N_Ta^\beta\), which is at most
  \(4T^{s+(1-s)\beta}\).  Expanding the exponent gives the first
  displayed rate.  If \(\beta\le0\), every nonzero occupancy contributes
  at most one, while the totalized zero power also contributes at most one;
  hence the sum is at most \(N_T\le2T^s\). -/)
  (title := /-- Power sum for tuned prediction buckets -/)
  (latexEnv := "lemma")]
lemma tuned_bucket_power_sum_bound
    {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (q α : ℝ)
    (hq : 2 ≤ q) (hαzero : 0 ≤ α) (hαone : α < 1)
    (hgrid : uses_prediction_grid P)
    (hsize : ∀ T, P.gridSize T = tuned_grid_size q T)
    (T : ℕ) (ω : Ω) (hTpos : 0 < T) :
    (∀ i : Fin (P.gridSize T), bucket_count P T ω i ≤ T) ∧
      (∑ i : Fin (P.gridSize T),
          (bucket_count P T ω i : ℝ) ^ (1 + q * (α - 1))) ≤
        4 * ((T : ℝ) ^
            (1 - q + q / (q + 1) + α * q ^ 2 / (q + 1)) +
          (T : ℝ) ^ (1 / (q + 1))) := by
  let β : ℝ := 1 + q * (α - 1)
  let s : ℝ := 1 / (q + 1)
  let e : ℝ :=
    1 - q + q / (q + 1) + α * q ^ 2 / (q + 1)
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hTpos
  have hTone : (1 : ℝ) ≤ T := by exact_mod_cast hTpos
  have hqone : 0 < q + 1 := by linarith
  have hspos : 0 < s := by
    dsimp [s]
    positivity
  have hsnonneg : 0 ≤ s := hspos.le
  have hxpos : 0 < (T : ℝ) ^ s := Real.rpow_pos_of_pos hTreal s
  have hxone : 1 ≤ (T : ℝ) ^ s := Real.one_le_rpow hTone hsnonneg
  have hceilone : 1 ≤ Nat.ceil ((T : ℝ) ^ s) := by
    rw [Nat.one_le_ceil_iff]
    exact hxpos
  have hNform :
      P.gridSize T = Nat.ceil ((T : ℝ) ^ s) := by
    rw [hsize T, tuned_grid_size, max_eq_right hceilone]
  have hNpos : 0 < (P.gridSize T : ℝ) := by
    exact_mod_cast P.gridSize_pos T
  have hNge : (T : ℝ) ^ s ≤ (P.gridSize T : ℝ) := by
    rw [hNform]
    exact Nat.le_ceil ((T : ℝ) ^ s)
  have hNle : (P.gridSize T : ℝ) ≤ 2 * (T : ℝ) ^ s := by
    rw [hNform]
    exact (Nat.ceil_lt_add_one hxpos.le).le.trans (by nlinarith)
  have hcount_sum :
      ∑ i : Fin (P.gridSize T), (bucket_count P T ω i : ℝ) = (T : ℝ) := by
    exact_mod_cast bucket_counts_sum P hgrid T ω
  have hcount_le (i : Fin (P.gridSize T)) :
      bucket_count P T ω i ≤ T := by
    have hsingle :
        (bucket_count P T ω i : ℝ) ≤
          ∑ j : Fin (P.gridSize T), (bucket_count P T ω j : ℝ) :=
      Finset.single_le_sum
        (fun j _ => Nat.cast_nonneg (bucket_count P T ω j))
        (Finset.mem_univ i)
    rw [hcount_sum] at hsingle
    exact_mod_cast hsingle
  refine ⟨hcount_le, ?_⟩
  have hβlt : β < 1 := by
    have hqpos : 0 < q := by linarith
    have hαneg : α - 1 < 0 := sub_neg.mpr hαone
    have hprod : q * (α - 1) < 0 := mul_neg_of_pos_of_neg hqpos hαneg
    dsimp [β]
    linarith
  have hpowersum :
      (∑ i : Fin (P.gridSize T),
          (bucket_count P T ω i : ℝ) ^ β) ≤
        4 * ((T : ℝ) ^ e + (T : ℝ) ^ s) := by
    rcases le_total 0 β with hβnonneg | hβnonpos
    · let a : ℝ := (T : ℝ) / (P.gridSize T : ℝ)
      have ha_pos : 0 < a := div_pos hTreal hNpos
      have hpointsum (i : Fin (P.gridSize T)) :
          (bucket_count P T ω i : ℝ) ^ β ≤
            a ^ β + (bucket_count P T ω i : ℝ) * a ^ (β - 1) := by
        by_cases hsmall : (bucket_count P T ω i : ℝ) ≤ a
        · exact (Real.rpow_le_rpow
            (Nat.cast_nonneg (bucket_count P T ω i)) hsmall hβnonneg).trans
              (le_add_of_nonneg_right
                (mul_nonneg (Nat.cast_nonneg _)
                  (Real.rpow_nonneg ha_pos.le _)))
        · have hlarge :
              a ≤ (bucket_count P T ω i : ℝ) := le_of_lt (lt_of_not_ge hsmall)
          have hcountpos : 0 < (bucket_count P T ω i : ℝ) :=
            ha_pos.trans_le hlarge
          have hnegative : β - 1 ≤ 0 := by linarith
          have hanti :
              (bucket_count P T ω i : ℝ) ^ (β - 1) ≤ a ^ (β - 1) :=
            Real.rpow_le_rpow_of_nonpos ha_pos hlarge hnegative
          calc
            (bucket_count P T ω i : ℝ) ^ β =
                (bucket_count P T ω i : ℝ) ^ (β - 1) *
                  (bucket_count P T ω i : ℝ) := by
              rw [← Real.rpow_add_one hcountpos.ne' (β - 1)]
              congr 1
              ring
            _ ≤ a ^ (β - 1) * (bucket_count P T ω i : ℝ) := by
              gcongr
            _ = (bucket_count P T ω i : ℝ) * a ^ (β - 1) := by
              ring
            _ ≤ a ^ β +
                (bucket_count P T ω i : ℝ) * a ^ (β - 1) :=
              le_add_of_nonneg_left (Real.rpow_nonneg ha_pos.le β)
      have hsplit :
          (∑ i : Fin (P.gridSize T),
              (bucket_count P T ω i : ℝ) ^ β) ≤
            2 * (P.gridSize T : ℝ) * a ^ β := by
        calc
          (∑ i : Fin (P.gridSize T),
              (bucket_count P T ω i : ℝ) ^ β) ≤
              ∑ i : Fin (P.gridSize T),
                (a ^ β +
                  (bucket_count P T ω i : ℝ) * a ^ (β - 1)) :=
            Finset.sum_le_sum fun i hi => hpointsum i
          _ = (P.gridSize T : ℝ) * a ^ β +
                (T : ℝ) * a ^ (β - 1) := by
            rw [Finset.sum_add_distrib, Finset.sum_const]
            simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [← Finset.sum_mul]
            rw [hcount_sum]
          _ = 2 * (P.gridSize T : ℝ) * a ^ β := by
            have haidentity : a ^ β = a ^ (β - 1) * a := by
              rw [← Real.rpow_add_one ha_pos.ne' (β - 1)]
              congr 1
              ring
            have hTa : (T : ℝ) = (P.gridSize T : ℝ) * a := by
              dsimp [a]
              field_simp [hNpos.ne']
            rw [hTa, haidentity]
            ring
      have hdiv :
          (T : ℝ) / (P.gridSize T : ℝ) ≤
            (T : ℝ) / (T : ℝ) ^ s :=
        div_le_div_of_nonneg_left hTreal.le hxpos hNge
      have hdivpow :
          ((T : ℝ) / (P.gridSize T : ℝ)) ^ β ≤
            ((T : ℝ) / (T : ℝ) ^ s) ^ β :=
        Real.rpow_le_rpow (div_nonneg hTreal.le hNpos.le) hdiv hβnonneg
      have hmain :
          (∑ i : Fin (P.gridSize T),
              (bucket_count P T ω i : ℝ) ^ β) ≤
            4 * (T : ℝ) ^ s *
              ((T : ℝ) / (T : ℝ) ^ s) ^ β := by
        calc
          (∑ i : Fin (P.gridSize T),
              (bucket_count P T ω i : ℝ) ^ β) ≤
              2 * (P.gridSize T : ℝ) * a ^ β := hsplit
          _ ≤ 4 * (T : ℝ) ^ s *
                ((T : ℝ) / (T : ℝ) ^ s) ^ β := by
            dsimp [a]
            nlinarith [mul_le_mul hNle hdivpow
              (Real.rpow_nonneg (div_nonneg hTreal.le hNpos.le) _)
              (by positivity : 0 ≤ 2 * (T : ℝ) ^ s)]
      have hrate :
          4 * (T : ℝ) ^ s * ((T : ℝ) / (T : ℝ) ^ s) ^ β =
            4 * (T : ℝ) ^ e := by
        rw [Real.div_rpow hTreal.le (Real.rpow_nonneg hTreal.le s) β]
        rw [← Real.rpow_mul hTreal.le s β]
        rw [← Real.rpow_sub hTreal β (s * β)]
        have hcombine :
            (T : ℝ) ^ s * (T : ℝ) ^ (β - s * β) =
              (T : ℝ) ^ e := by
          rw [← Real.rpow_add hTreal]
          congr 1
          dsimp [e, s, β]
          field_simp
          ring
        calc
          4 * (T : ℝ) ^ s * (T : ℝ) ^ (β - s * β) =
              4 * ((T : ℝ) ^ s * (T : ℝ) ^ (β - s * β)) := by ring
          _ = 4 * (T : ℝ) ^ e := by rw [hcombine]
      calc
        (∑ i : Fin (P.gridSize T),
            (bucket_count P T ω i : ℝ) ^ β) ≤
            4 * (T : ℝ) ^ e := hmain.trans_eq hrate
        _ ≤ 4 * ((T : ℝ) ^ e + (T : ℝ) ^ s) := by
          have hsnonnegative := Real.rpow_nonneg hTreal.le s
          linarith
    · have honeach (i : Fin (P.gridSize T)) :
          (bucket_count P T ω i : ℝ) ^ β ≤ 1 := by
        by_cases hzero : bucket_count P T ω i = 0
        · by_cases hβzero : β = 0 <;> simp [hzero, hβzero]
        · apply Real.rpow_le_one_of_one_le_of_nonpos
          · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
          · exact hβnonpos
      have hsumone :
          (∑ i : Fin (P.gridSize T),
              (bucket_count P T ω i : ℝ) ^ β) ≤
            (P.gridSize T : ℝ) := by
        calc
          (∑ i : Fin (P.gridSize T),
              (bucket_count P T ω i : ℝ) ^ β) ≤
              ∑ i : Fin (P.gridSize T), (1 : ℝ) :=
            Finset.sum_le_sum fun i hi => honeach i
          _ = (P.gridSize T : ℝ) := by simp
      calc
        (∑ i : Fin (P.gridSize T),
            (bucket_count P T ω i : ℝ) ^ β) ≤
            2 * (T : ℝ) ^ s := hsumone.trans hNle
        _ ≤ 4 * ((T : ℝ) ^ e + (T : ℝ) ^ s) := by
          have henonnegative := Real.rpow_nonneg hTreal.le e
          linarith
  simpa [β, e, s] using hpowersum

@[blueprint "lem:regret-contribution-bound"
  (statement := /-- Let \(X\), \(Y\), and \(\Omega\) be types, equip
  \(\Omega\) with a measurable space, let \(P\) be a forecasting process,
  and let \(A\) be an online agnostic learner on \(X\).  Suppose
  \(q\ge2\), \(0\le\alpha<1\), and \(C>0\).  Assume that
  \(\mathsf{Reg}(n)\ge0\) for every \(n\in\mathbb N\), that
  \(\mathsf{Reg}(n)=\widetilde{\mathcal O}(n^\alpha C)\), that every
  prediction of \(P\) belongs to its declared grid, and that
  \(N_T=N_q(T)\) for every \(T\in\mathbb N\).  Then, uniformly in the
  outcome,
  \[
  \sum_i n_i\left(\frac{\mathsf{Reg}(n_i)}{n_i}\right)^q
  =\widetilde{\mathcal O}\left(
    T^{1-q+q/(q+1)+\alpha q^2/(q+1)}C^q+
    T^{1/(q+1)}C^q\right).
  \] -/)
  (proof := /-- Apply
  \(\cref{lem:soft-big-o-positive-pointwise}\) to obtain \(K>0\) and
  \(k\in\mathbb N\) such that, for every positive integer \(n\),
  \[
    \mathsf{Reg}(n)\le K(\log(n+2))^k n^\alpha C.
  \]
  Put \(\beta=1+q(\alpha-1)\) and
  \(m=k\lceil q\rceil\).  Positivity of the factors and the laws for
  real powers then give
  \[
    n\left(\frac{\mathsf{Reg}(n)}n\right)^q
      \le K^q\bigl((\log(n+2))^k\bigr)^q C^q n^\beta
  \]
  whenever \(n>0\); the term is zero when \(n=0\).

  For all sufficiently large \(T\), one has
  \(\log(T+2)\ge1\).  If \(0\le n\le T\), monotonicity of the
  logarithm and of powers, followed by
  \(q\le\lceil q\rceil\), yields
  \[
    \bigl((\log(n+2))^k\bigr)^q
      \le(\log(T+2))^m.
  \]
  By \(\cref{lem:tuned-bucket-power-sum-bound}\), every bucket occupancy
  is at most \(T\), and
  \[
    \sum_i n_i^\beta\le4\left(
      T^{1-q+q/(q+1)+\alpha q^2/(q+1)}+T^{1/(q+1)}\right).
  \]
  Apply the pointwise estimate to every nonempty bucket, use the preceding
  common logarithmic bound, and sum.  Unfolding
  \(\cref{def:regret-contribution}\) gives
  \[
    \operatorname{RegContrib}_{P,A,q}(T,\omega)
      \le4K^q(\log(T+2))^m
      \left(T^{1-q+q/(q+1)+\alpha q^2/(q+1)}C^q
        +T^{1/(q+1)}C^q\right).
  \]
  Since \(4K^q>0\), \(\cref{def:uniform-soft-bound}\) proves the
  asserted uniform estimate. -/)
  (title := /-- Aggregation of learner-regret contributions -/)
  (latexEnv := "lemma")]
lemma regret_contribution_bound
    {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (A : online_agnostic_learner X)
    (q α complexity : ℝ)
    (hq : 2 ≤ q) (hαzero : 0 ≤ α) (hαone : α < 1)
    (hcomplexity : 0 < complexity)
    (hregret_nonneg : ∀ n, 0 ≤ A.regret n)
    (hregret :
      soft_big_o A.regret
        (fun n => (n : ℝ) ^ α * complexity))
    (hgrid : uses_prediction_grid P)
    (hsize : ∀ T, P.gridSize T = tuned_grid_size q T) :
    uniform_soft_bound
      (regret_contribution P A q)
      (fun T _ =>
        (T : ℝ) ^
            (1 - q + q / (q + 1) + α * q ^ 2 / (q + 1)) *
          complexity ^ q +
        (T : ℝ) ^ (1 / (q + 1)) * complexity ^ q) := by
  rcases soft_big_o_positive_pointwise
      A.regret α complexity hcomplexity hregret_nonneg hregret with
    ⟨K, hKpos, k, hpoint⟩
  let β : ℝ := 1 + q * (α - 1)
  have hncombine (n : ℕ) (hn : 0 < n) :
      (n : ℝ) * ((n : ℝ) ^ α) ^ q / (n : ℝ) ^ q =
        (n : ℝ) ^ β := by
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    rw [← Real.rpow_mul hnreal.le α q]
    nth_rewrite 1 [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_add hnreal, ← Real.rpow_sub hnreal]
    congr 1
    dsimp [β]
    ring
  have hterm (n : ℕ) (hn : 0 < n) :
      (n : ℝ) * (A.regret n / (n : ℝ)) ^ q ≤
        K ^ q * ((Real.log ((n : ℝ) + 2)) ^ k) ^ q *
          complexity ^ q * (n : ℝ) ^ β := by
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hlog : 0 < Real.log ((n : ℝ) + 2) :=
      Real.log_pos (by exact_mod_cast (show 1 < n + 2 by omega))
    have hnum : 0 ≤ K * (Real.log ((n : ℝ) + 2)) ^ k *
        (n : ℝ) ^ α * complexity := by
      positivity
    have hratio : A.regret n / (n : ℝ) ≤
        (K * (Real.log ((n : ℝ) + 2)) ^ k *
          (n : ℝ) ^ α * complexity) / (n : ℝ) :=
      div_le_div_of_nonneg_right (hpoint n hn) hnreal.le
    have hpow := Real.rpow_le_rpow
      (div_nonneg (hregret_nonneg n) hnreal.le) hratio
      (by linarith : 0 ≤ q)
    calc
      (n : ℝ) * (A.regret n / (n : ℝ)) ^ q ≤
          (n : ℝ) * ((K * (Real.log ((n : ℝ) + 2)) ^ k *
            (n : ℝ) ^ α * complexity) / (n : ℝ)) ^ q :=
        mul_le_mul_of_nonneg_left hpow hnreal.le
      _ = K ^ q * ((Real.log ((n : ℝ) + 2)) ^ k) ^ q *
          complexity ^ q * (n : ℝ) ^ β := by
        rw [Real.div_rpow hnum hnreal.le]
        rw [Real.mul_rpow
          (mul_nonneg
            (mul_nonneg hKpos.le (pow_nonneg hlog.le k))
            (Real.rpow_nonneg _ _))
          hcomplexity.le]
        rw [Real.mul_rpow
          (mul_nonneg hKpos.le (pow_nonneg hlog.le k))
          (Real.rpow_nonneg _ _)]
        rw [Real.mul_rpow hKpos.le
          (pow_nonneg hlog.le k)]
        rw [← hncombine n hn]
        ring
        all_goals positivity
  let m : ℕ := k * Nat.ceil q
  have hlogpow {n T : ℕ} (hnT : n ≤ T)
      (hlogT_one : 1 ≤ Real.log ((T : ℝ) + 2)) :
      ((Real.log ((n : ℝ) + 2)) ^ k) ^ q ≤
        (Real.log ((T : ℝ) + 2)) ^ m := by
    have hnarg : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hTarg : (0 : ℝ) < (T : ℝ) + 2 := by positivity
    have hargs : (n : ℝ) + 2 ≤ (T : ℝ) + 2 := by
      exact_mod_cast (Nat.add_le_add_right hnT 2)
    have hlogs :
        Real.log ((n : ℝ) + 2) ≤ Real.log ((T : ℝ) + 2) :=
      Real.log_le_log hnarg hargs
    have hlogn_zero : 0 ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_nonneg (by
        have hnzero : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
    have hnat :
        (Real.log ((n : ℝ) + 2)) ^ k ≤
          (Real.log ((T : ℝ) + 2)) ^ k := by
      exact pow_le_pow_left₀ hlogn_zero hlogs k
    calc
      ((Real.log ((n : ℝ) + 2)) ^ k) ^ q ≤
          ((Real.log ((T : ℝ) + 2)) ^ k) ^ q :=
        Real.rpow_le_rpow (pow_nonneg hlogn_zero k)
          hnat (by linarith)
      _ ≤ ((Real.log ((T : ℝ) + 2)) ^ k) ^
          (Nat.ceil q : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        · exact one_le_pow₀ hlogT_one
        · exact Nat.le_ceil q
      _ = (Real.log ((T : ℝ) + 2)) ^ m := by
        simp [m, Real.rpow_natCast, pow_mul]
  let s : ℝ := 1 / (q + 1)
  let e : ℝ :=
    1 - q + q / (q + 1) + α * q ^ 2 / (q + 1)
  unfold uniform_soft_bound
  refine ⟨4 * K ^ q, by positivity, m, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (Nat.ceil (Real.exp 1))] with T hTlarge
  intro ω
  have hceilpos : 0 < Nat.ceil (Real.exp 1) :=
    Nat.ceil_pos.mpr (Real.exp_pos 1)
  have hTpos : 0 < T := hceilpos.trans_le hTlarge
  have hexp_le : Real.exp 1 ≤ (T : ℝ) + 2 := by
    calc
      Real.exp 1 ≤ (Nat.ceil (Real.exp 1) : ℝ) := Nat.le_ceil _
      _ ≤ (T : ℝ) := by exact_mod_cast hTlarge
      _ ≤ (T : ℝ) + 2 := by linarith
  have hlogT_one : 1 ≤ Real.log ((T : ℝ) + 2) := by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log ((T : ℝ) + 2) :=
        Real.log_le_log (Real.exp_pos 1) hexp_le
  obtain ⟨hcount_le, hpowersum_helper⟩ :=
    tuned_bucket_power_sum_bound P q α hq hαzero hαone hgrid hsize T ω hTpos
  have hpowersum_from_helper :
      (∑ i : Fin (P.gridSize T),
          (bucket_count P T ω i : ℝ) ^ β) ≤
        4 * ((T : ℝ) ^ e + (T : ℝ) ^ s) := by
    simpa [β, e, s] using hpowersum_helper
  have hsumterm :
      regret_contribution P A q T ω ≤
        (K ^ q * (Real.log ((T : ℝ) + 2)) ^ m * complexity ^ q) *
          ∑ i : Fin (P.gridSize T),
            (bucket_count P T ω i : ℝ) ^ β := by
    unfold regret_contribution
    calc
      ∑ i : Fin (P.gridSize T),
          (bucket_count P T ω i : ℝ) *
            (A.regret (bucket_count P T ω i) /
              (bucket_count P T ω i : ℝ)) ^ q ≤
          ∑ i : Fin (P.gridSize T),
            K ^ q * (Real.log ((T : ℝ) + 2)) ^ m *
              complexity ^ q * (bucket_count P T ω i : ℝ) ^ β := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hzero : bucket_count P T ω i = 0
        · simp only [hzero, Nat.cast_zero, zero_div, Real.zero_rpow, zero_mul]
          positivity
        · have hpos : 0 < bucket_count P T ω i := Nat.pos_of_ne_zero hzero
          calc
            (bucket_count P T ω i : ℝ) *
                (A.regret (bucket_count P T ω i) /
                  (bucket_count P T ω i : ℝ)) ^ q ≤
                K ^ q *
                  ((Real.log ((bucket_count P T ω i : ℝ) + 2)) ^ k) ^ q *
                  complexity ^ q *
                  (bucket_count P T ω i : ℝ) ^ β :=
              hterm _ hpos
            _ ≤ K ^ q * (Real.log ((T : ℝ) + 2)) ^ m *
                  complexity ^ q *
                  (bucket_count P T ω i : ℝ) ^ β := by
              gcongr
              exact hlogpow (hcount_le i) hlogT_one
      _ = (K ^ q * (Real.log ((T : ℝ) + 2)) ^ m * complexity ^ q) *
          ∑ i : Fin (P.gridSize T),
            (bucket_count P T ω i : ℝ) ^ β := by
        rw [Finset.mul_sum]
  calc
    regret_contribution P A q T ω ≤
        (K ^ q * (Real.log ((T : ℝ) + 2)) ^ m * complexity ^ q) *
          ∑ i : Fin (P.gridSize T),
            (bucket_count P T ω i : ℝ) ^ β := hsumterm
    _ ≤ (K ^ q * (Real.log ((T : ℝ) + 2)) ^ m * complexity ^ q) *
          (4 * ((T : ℝ) ^ e + (T : ℝ) ^ s)) := by
      exact mul_le_mul_of_nonneg_left hpowersum_from_helper (by positivity)
    _ = 4 * K ^ q * (Real.log ((T : ℝ) + 2)) ^ m *
          ((T : ℝ) ^ e * complexity ^ q +
            (T : ℝ) ^ s * complexity ^ q) := by ring
    _ = 4 * K ^ q * (Real.log ((T : ℝ) + 2)) ^ m *
          ((T : ℝ) ^
              (1 - q + q / (q + 1) + α * q ^ 2 / (q + 1)) *
            complexity ^ q +
            (T : ℝ) ^ (1 / (q + 1)) * complexity ^ q) := by
      rfl

@[blueprint "lem:discretization-contribution-bound"
  (statement := /-- Let \(P\) be a forecasting process with measurable
  outcome space \(\Omega\), and let \(q,\rho\in\mathbb R\) satisfy
  \(q\ge2\) and \(\rho\ge0\).  Suppose that for every natural horizon
  \(T\), the grid size of \(P\) is \(N_T=N_q(T)\).  There exist a constant
  \(C>0\) and an exponent
  \(k\in\mathbb N\), both independent of \(\delta\), such that, for every
  \(0<\delta<1\), every outcome, and all sufficiently large \(T\),
  \[
    \rho^q\frac{T}{N_T^q}
      +N_T\left(\log\frac{N_T}{\delta}\right)^{q/2}
    \le C(\log(T+2))^k\left(
      \rho^qT^{1/(q+1)}
      +T^{1/(q+1)}\left(\log\frac1\delta\right)^{q/2}\right)
  \]
  uniformly in the outcome. -/)
  (proof := /-- Take \(C=2\) and \(k=\lceil q\rceil\).  Fix
  \(0<\delta<1\).  Since \(\log(T+2)\) tends to infinity, it is eventually
  at least both \(2\) and \(2/\log(1/\delta)\).  By
  \(\cref{def:tuned-grid-size}\), for such a positive horizon the ceiling
  bounds give
  \[
    T^{1/(q+1)}\le N_T\le2T^{1/(q+1)}
    \quad\text{and}\quad N_T\le T+2.
  \]
  Monotonicity of real powers, together with
  \(T=T^{1/(q+1)}(T^{1/(q+1)})^q\), therefore gives
  \(\rho^qT/N_T^q\le\rho^qT^{1/(q+1)}\).
  Moreover,
  \(\log(N_T/\delta)=\log N_T+\log(1/\delta)\).  The two eventual lower
  bounds on \(\log(T+2)\), and \(N_T\le T+2\), imply
  \[
    \log(N_T/\delta)
      \le (\log(T+2))^2\log(1/\delta).
  \]
  Raising this inequality to \(q/2\), multiplying by the upper bound on
  \(N_T\), and using \(q\le\lceil q\rceil\) yields
  \[
    N_T\bigl(\log(N_T/\delta)\bigr)^{q/2}
    \le2(\log(T+2))^{\lceil q\rceil}
       T^{1/(q+1)}\bigl(\log(1/\delta)\bigr)^{q/2}.
  \]
  Since the same polylogarithmic multiplier is at least one, adding the
  two estimates and unfolding
  \(\cref{def:discretization-contribution}\) proves the result uniformly
  over the outcome space. -/)
  (title := /-- Optimization of discretization terms -/)
  (latexEnv := "lemma")]
lemma discretization_contribution_bound
    {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (q ρ : ℝ)
    (hq : 2 ≤ q) (hρ : 0 ≤ ρ)
    (hsize : ∀ T, P.gridSize T = tuned_grid_size q T) :
    ∃ C : ℝ, 0 < C ∧
      ∃ k : ℕ, ∀ δ : ℝ, 0 < δ → δ < 1 →
        ∀ᶠ T in Filter.atTop,
          ∀ _ω : Ω,
            discretization_contribution P q ρ δ T ≤
              C * (Real.log ((T : ℝ) + 2)) ^ k *
                (ρ ^ q * (T : ℝ) ^ (1 / (q + 1)) +
                  (T : ℝ) ^ (1 / (q + 1)) *
                    (Real.log (1 / δ)) ^ (q / 2)) := by
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq
  have hqp : 0 < q + 1 := by linarith
  have ha : 0 < 1 / (q + 1) := one_div_pos.mpr hqp
  refine ⟨2, by norm_num, Nat.ceil q, ?_⟩
  intro δ hδ hδ1
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have hlogδ : 0 < Real.log (1 / δ) := Real.log_pos (by
    rw [one_div]
    exact (one_lt_inv₀ hδ).2 hδ1)
  have htend : Filter.Tendsto (fun T : ℕ => Real.log ((T : ℝ) + 2))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Filter.tendsto_atTop_add_const_right Filter.atTop 2 tendsto_natCast_atTop_atTop)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ),
    htend.eventually_ge_atTop (max 2 (2 / Real.log (1 / δ)))] with T hT hlarge
  have hTreal : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hTreal
  have hxpos : 0 < (T : ℝ) ^ (1 / (q + 1)) := Real.rpow_pos_of_pos hTpos _
  have hxone : 1 ≤ (T : ℝ) ^ (1 / (q + 1)) := by
    simpa using Real.one_le_rpow hTreal (le_of_lt ha)
  have hceilone : 1 ≤ Nat.ceil ((T : ℝ) ^ (1 / (q + 1))) := by
    exact_mod_cast (le_trans hxone (Nat.le_ceil _))
  have hgrid : P.gridSize T = Nat.ceil ((T : ℝ) ^ (1 / (q + 1))) := by
    rw [hsize T, tuned_grid_size, max_eq_right hceilone]
  have hgridlower : (T : ℝ) ^ (1 / (q + 1)) ≤ (P.gridSize T : ℝ) := by
    rw [hgrid]
    exact Nat.le_ceil _
  have hgridupper : (P.gridSize T : ℝ) ≤ 2 * (T : ℝ) ^ (1 / (q + 1)) := by
    rw [hgrid]
    have hc : (Nat.ceil ((T : ℝ) ^ (1 / (q + 1))) : ℝ) <
        (T : ℝ) ^ (1 / (q + 1)) + 1 := Nat.ceil_lt_add_one hxpos.le
    linarith
  have hgridpos : 0 < (P.gridSize T : ℝ) := lt_of_lt_of_le hxpos hgridlower
  have hgridT : (P.gridSize T : ℝ) ≤ (T : ℝ) + 2 := by
    rw [hgrid]
    have hc : (Nat.ceil ((T : ℝ) ^ (1 / (q + 1))) : ℝ) <
        (T : ℝ) ^ (1 / (q + 1)) + 1 := Nat.ceil_lt_add_one hxpos.le
    have ha1 : 1 / (q + 1) ≤ 1 := (div_le_one hqp).2 (by linarith)
    have hxT : (T : ℝ) ^ (1 / (q + 1)) ≤ (T : ℝ) :=
      Real.rpow_le_self_of_one_le hTreal ha1
    linarith
  have hlogone : 2 ≤ Real.log ((T : ℝ) + 2) := le_trans (le_max_left _ _) hlarge
  have hloginv : 2 / Real.log (1 / δ) ≤ Real.log ((T : ℝ) + 2) :=
    le_trans (le_max_right _ _) hlarge
  have hlogmul : 2 ≤ Real.log ((T : ℝ) + 2) * Real.log (1 / δ) :=
    (div_le_iff₀ hlogδ).1 hloginv
  have hloggrid : Real.log ((P.gridSize T : ℝ) / δ) ≤
      Real.log ((T : ℝ) + 2) ^ 2 * Real.log (1 / δ) := by
    have hlogmono : Real.log (P.gridSize T : ℝ) ≤ Real.log ((T : ℝ) + 2) := by
      rw [Real.log_le_log_iff hgridpos (by positivity)]
      exact hgridT
    have hsplit : Real.log ((P.gridSize T : ℝ) / δ) =
        Real.log (P.gridSize T : ℝ) + Real.log (1 / δ) := by
      rw [Real.log_div (ne_of_gt hgridpos) hδne, Real.log_div one_ne_zero hδne]
      simp only [Real.log_one, zero_sub]
      ring
    rw [hsplit]
    calc
      Real.log (P.gridSize T : ℝ) + Real.log (1 / δ) ≤
          Real.log ((T : ℝ) + 2) + Real.log (1 / δ) := by gcongr
      _ ≤ Real.log ((T : ℝ) + 2) ^ 2 * Real.log (1 / δ) := by
        have hA : Real.log ((T : ℝ) + 2) ≤
            Real.log ((T : ℝ) + 2) ^ 2 * Real.log (1 / δ) := by
          nlinarith [hlogmul]
        have hB : Real.log (1 / δ) ≤
            Real.log ((T : ℝ) + 2) ^ 2 * Real.log (1 / δ) := by
          nlinarith [hlogδ, hlogone]
        nlinarith
  have htermone : ρ ^ q * (T : ℝ) / (P.gridSize T : ℝ) ^ q ≤
      ρ ^ q * (T : ℝ) ^ (1 / (q + 1)) := by
    have hrho : 0 ≤ ρ ^ q := Real.rpow_nonneg hρ q
    have hpowlower : ((T : ℝ) ^ (1 / (q + 1))) ^ q ≤
        (P.gridSize T : ℝ) ^ q := Real.rpow_le_rpow hxpos.le hgridlower hq0
    have hdenpos : 0 < (P.gridSize T : ℝ) ^ q := Real.rpow_pos_of_pos hgridpos q
    have hxqpos : 0 < ((T : ℝ) ^ (1 / (q + 1))) ^ q :=
      Real.rpow_pos_of_pos hxpos q
    have hTx : (T : ℝ) = (T : ℝ) ^ (1 / (q + 1)) *
        ((T : ℝ) ^ (1 / (q + 1))) ^ q := by
      calc
        (T : ℝ) = (T : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ = (T : ℝ) ^ (1 / (q + 1) + 1 / (q + 1) * q) := by
          congr 1
          field_simp
          ring
        _ = (T : ℝ) ^ (1 / (q + 1)) * (T : ℝ) ^ (1 / (q + 1) * q) :=
          Real.rpow_add hTpos _ _
        _ = (T : ℝ) ^ (1 / (q + 1)) *
            ((T : ℝ) ^ (1 / (q + 1))) ^ q := by
          rw [Real.rpow_mul hTpos.le]
    calc
      ρ ^ q * (T : ℝ) / (P.gridSize T : ℝ) ^ q ≤
          ρ ^ q * (T : ℝ) / ((T : ℝ) ^ (1 / (q + 1))) ^ q := by
            exact div_le_div_of_nonneg_left (mul_nonneg hrho hTpos.le) hxqpos hpowlower
      _ = ρ ^ q * (T : ℝ) ^ (1 / (q + 1)) := by
        apply (div_eq_iff hxqpos.ne').2
        calc
          ρ ^ q * (T : ℝ) = ρ ^ q *
              ((T : ℝ) ^ (1 / (q + 1)) *
                ((T : ℝ) ^ (1 / (q + 1))) ^ q) :=
            congrArg (fun z : ℝ => ρ ^ q * z) hTx
          _ = ρ ^ q * (T : ℝ) ^ (1 / (q + 1)) *
              ((T : ℝ) ^ (1 / (q + 1))) ^ q := by ring
  have htermtwo : (P.gridSize T : ℝ) *
      (Real.log ((P.gridSize T : ℝ) / δ)) ^ (q / 2) ≤
      2 * Real.log ((T : ℝ) + 2) ^ Nat.ceil q *
        ((T : ℝ) ^ (1 / (q + 1)) * (Real.log (1 / δ)) ^ (q / 2)) := by
    have hs : 0 ≤ q / 2 := by positivity
    have hloggrid0 : 0 ≤ Real.log ((P.gridSize T : ℝ) / δ) := by
      apply Real.log_nonneg
      apply (one_le_div hδ).2
      have honegrid : (1 : ℝ) ≤ (P.gridSize T : ℝ) := by
        rw [hgrid]
        exact_mod_cast hceilone
      exact hδ1.le.trans honegrid
    have hrpowlog := Real.rpow_le_rpow hloggrid0 hloggrid hs
    have hpowq : (Real.log ((T : ℝ) + 2) ^ 2 * Real.log (1 / δ)) ^ (q / 2) =
        Real.log ((T : ℝ) + 2) ^ q * (Real.log (1 / δ)) ^ (q / 2) := by
      rw [Real.mul_rpow (by positivity) hlogδ.le,
        ← Real.rpow_natCast_mul (by positivity) 2 (q / 2)]
      congr 2
      ring
    have hqceil : q ≤ (Nat.ceil q : ℝ) := Nat.le_ceil q
    have hlogpow : Real.log ((T : ℝ) + 2) ^ q ≤
        Real.log ((T : ℝ) + 2) ^ Nat.ceil q := by
      have hlogone' : 1 ≤ Real.log ((T : ℝ) + 2) := by linarith
      simpa using Real.rpow_le_rpow_of_exponent_le hlogone' hqceil
    calc
      (P.gridSize T : ℝ) * (Real.log ((P.gridSize T : ℝ) / δ)) ^ (q / 2) ≤
          (2 * (T : ℝ) ^ (1 / (q + 1))) *
            (Real.log ((T : ℝ) + 2) ^ 2 * Real.log (1 / δ)) ^ (q / 2) := by
              exact mul_le_mul hgridupper hrpowlog (Real.rpow_nonneg hloggrid0 _) (by positivity)
      _ = 2 * (T : ℝ) ^ (1 / (q + 1)) *
            (Real.log ((T : ℝ) + 2) ^ q * (Real.log (1 / δ)) ^ (q / 2)) := by
              rw [hpowq]
      _ ≤ 2 * (T : ℝ) ^ (1 / (q + 1)) *
            (Real.log ((T : ℝ) + 2) ^ Nat.ceil q * (Real.log (1 / δ)) ^ (q / 2)) := by
              gcongr
      _ = 2 * Real.log ((T : ℝ) + 2) ^ Nat.ceil q *
            ((T : ℝ) ^ (1 / (q + 1)) * (Real.log (1 / δ)) ^ (q / 2)) := by ring
  rw [discretization_contribution]
  have hlogpowone : 1 ≤ Real.log ((T : ℝ) + 2) ^ Nat.ceil q :=
    one_le_pow₀ (by linarith)
  intro _ω
  have hA : ρ ^ q * (T : ℝ) ^ (1 / (q + 1)) ≤
      2 * Real.log ((T : ℝ) + 2) ^ Nat.ceil q *
        (ρ ^ q * (T : ℝ) ^ (1 / (q + 1))) := by
    have hnon : 0 ≤ ρ ^ q * (T : ℝ) ^ (1 / (q + 1)) :=
      mul_nonneg (Real.rpow_nonneg hρ q) (Real.rpow_nonneg hTpos.le _)
    nlinarith
  calc
    ρ ^ q * (T : ℝ) / (P.gridSize T : ℝ) ^ q +
        (P.gridSize T : ℝ) * (Real.log ((P.gridSize T : ℝ) / δ)) ^ (q / 2) ≤
        ρ ^ q * (T : ℝ) ^ (1 / (q + 1)) +
          2 * Real.log ((T : ℝ) + 2) ^ Nat.ceil q *
            ((T : ℝ) ^ (1 / (q + 1)) * (Real.log (1 / δ)) ^ (q / 2)) :=
      add_le_add htermone htermtwo
    _ ≤ 2 * Real.log ((T : ℝ) + 2) ^ Nat.ceil q *
          (ρ ^ q * (T : ℝ) ^ (1 / (q + 1))) +
        2 * Real.log ((T : ℝ) + 2) ^ Nat.ceil q *
          ((T : ℝ) ^ (1 / (q + 1)) * (Real.log (1 / δ)) ^ (q / 2)) :=
      add_le_add hA le_rfl
    _ = 2 * Real.log ((T : ℝ) + 2) ^ Nat.ceil q *
          (ρ ^ q * (T : ℝ) ^ (1 / (q + 1)) +
            (T : ℝ) ^ (1 / (q + 1)) * (Real.log (1 / δ)) ^ (q / 2)) := by ring

@[blueprint "lem:large-exponent-algorithm-bound"
  (statement := /-- Let \(q\ge2\).  Assume that \(\Gamma\) is identified by
  a \(\rho\)-Lipschitz function \(V\), that
  \(\mathcal F\subseteq[-1,1]^{\mathcal X}\), that \(A\) has the online
  agnostic regret guarantee with a strictly positive complexity \(C\) and
  \(\mathsf{Reg}(n)=\widetilde{\mathcal O}(n^\alpha C)\) for
  \(0\le\alpha<1\), and that the oracle-efficient process uses
  \(N_q(T)\) grid points.  Then there are a positive constant and a
  polylogarithmic exponent, both independent of \(\delta\), such that, for
  every \(0<\delta<1\),
  \[
    \operatorname{smcal}_{\Gamma,q}(\mathcal F)
      =\widetilde{\mathcal O}(R_{\ge2}(T,\delta))
  \]
  on a measurable event of probability at least \(1-\delta\). -/)
  (proof := /-- The oracle-efficient deviation estimate
  \(\cref{lem:oracle-efficient-preoptimized-bound}\) bounds the swap error
  by the sum of its discretization contribution and its learner-regret
  contribution.  Apply
  \(\cref{lem:discretization-contribution-bound}\) to the first contribution
  and \(\cref{lem:regret-contribution-bound}\) to the second.  Enlarging the
  common polylogarithmic multiplier and adding the two bounds gives exactly
  \(R_{\ge2}(T,\delta)\), while the probability of the event remains at
  least \(1-\delta\). -/)
  (title := /-- Oracle-efficient bound for exponents at least two -/)
  (latexEnv := "lemma")]
lemma large_exponent_algorithm_bound
    {X Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]
    (Γ : identified_property Y)
    (P : forecasting_process X Y Ω) (A : online_agnostic_learner X)
    (F : Set (X → ℝ)) (q ρ α complexity : ℝ)
    (hq : 2 ≤ q) (hαzero : 0 ≤ α) (hαone : α < 1)
    (hcomplexity : 0 < complexity)
    (hidentify : is_identification_function Γ)
    (hlip : lipschitz_identification Γ ρ)
    (hbounded : ∀ f ∈ F, ∀ x, |f x| ≤ 1)
    (honline : online_agnostic_regret A F)
    (hregret_nonneg : ∀ n, 0 ≤ A.regret n)
    (hregret :
      soft_big_o A.regret
        (fun n => (n : ℝ) ^ α * complexity))
    (hgrid : uses_prediction_grid P)
    (hsize : ∀ T, P.gridSize T = tuned_grid_size q T)
    (hAlgorithm :
      oracle_efficient_execution P A F Γ.identification q ρ) :
    high_probability_soft_bound P.measure
      (swap_multicalibration_error P F Γ.identification q)
      (fun δ T _ => large_exponent_rate q ρ α complexity δ T) := by
  obtain ⟨C₀, hC₀, k₀, h₀⟩ :=
    oracle_efficient_preoptimized_bound P A F Γ.identification q ρ hq hAlgorithm
  obtain ⟨C₁, hC₁, k₁, h₁⟩ :=
    discretization_contribution_bound P q ρ hq hlip.1 hsize
  obtain ⟨C₂, hC₂, k₂, h₂⟩ :=
    regret_contribution_bound P A q α complexity hq hαzero hαone hcomplexity
      hregret_nonneg hregret hgrid hsize
  have hρ : (0 : ℝ) ≤ ρ := hlip.1
  unfold high_probability_soft_bound
  refine ⟨C₀ * (C₁ + C₂),
    mul_pos hC₀ (by linarith : (0 : ℝ) < C₁ + C₂), k₀ + k₁ + k₂, ?_⟩
  intro δ hδ hδone
  filter_upwards [h₀ δ hδ hδone, h₁ δ hδ hδone, h₂,
    Filter.eventually_ge_atTop (Nat.ceil (Real.exp 1))]
    with T hTzero hTone hTtwo hTlarge
  obtain ⟨E, hEmeas, hEprob, hEbound⟩ := hTzero
  refine ⟨E, hEmeas, hEprob, ?_⟩
  intro ω hω
  have hTpos : 0 < T := (Nat.ceil_pos.mpr (Real.exp_pos 1)).trans_le hTlarge
  have hTreal : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hTpos
  have hlogone : 1 ≤ Real.log ((T : ℝ) + 2) := by
    have hexp_le : Real.exp 1 ≤ (T : ℝ) + 2 := by
      calc
        Real.exp 1 ≤ (Nat.ceil (Real.exp 1) : ℝ) := Nat.le_ceil _
        _ ≤ (T : ℝ) := by exact_mod_cast hTlarge
        _ ≤ (T : ℝ) + 2 := by linarith
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log ((T : ℝ) + 2) := Real.log_le_log (Real.exp_pos 1) hexp_le
  have hlogδ : 0 < Real.log (1 / δ) := Real.log_pos (by
    rw [one_div]
    exact (one_lt_inv₀ hδ).2 hδone)
  have hdisc := hTone ω
  have hreg := hTtwo ω
  set L : ℝ := Real.log ((T : ℝ) + 2) with hLdef
  have hLnonneg : (0 : ℝ) ≤ L := by linarith
  set U : ℝ :=
      ρ ^ q * (T : ℝ) ^ (1 / (q + 1)) +
        (T : ℝ) ^ (1 / (q + 1)) * Real.log (1 / δ) ^ (q / 2) with hUdef
  set W : ℝ :=
      (T : ℝ) ^ (1 - q + q / (q + 1) + α * q ^ 2 / (q + 1)) * complexity ^ q +
        (T : ℝ) ^ (1 / (q + 1)) * complexity ^ q with hWdef
  have hTsnonneg : (0 : ℝ) ≤ (T : ℝ) ^ (1 / (q + 1)) :=
    Real.rpow_nonneg hTreal.le _
  have hcpownonneg : (0 : ℝ) ≤ complexity ^ q := Real.rpow_nonneg hcomplexity.le q
  have hUnonneg : (0 : ℝ) ≤ U := by
    have hone : (0 : ℝ) ≤ ρ ^ q := Real.rpow_nonneg hρ q
    have htwo : (0 : ℝ) ≤ Real.log (1 / δ) ^ (q / 2) :=
      Real.rpow_nonneg hlogδ.le _
    have hthree : (0 : ℝ) ≤ ρ ^ q * (T : ℝ) ^ (1 / (q + 1)) :=
      mul_nonneg hone hTsnonneg
    have hfour : (0 : ℝ) ≤
        (T : ℝ) ^ (1 / (q + 1)) * Real.log (1 / δ) ^ (q / 2) :=
      mul_nonneg hTsnonneg htwo
    rw [hUdef]
    linarith
  have hWnonneg : (0 : ℝ) ≤ W := by
    have hone : (0 : ℝ) ≤
        (T : ℝ) ^ (1 - q + q / (q + 1) + α * q ^ 2 / (q + 1)) :=
      Real.rpow_nonneg hTreal.le _
    have htwo : (0 : ℝ) ≤
        (T : ℝ) ^ (1 - q + q / (q + 1) + α * q ^ 2 / (q + 1)) *
          complexity ^ q := mul_nonneg hone hcpownonneg
    have hthree : (0 : ℝ) ≤ (T : ℝ) ^ (1 / (q + 1)) * complexity ^ q :=
      mul_nonneg hTsnonneg hcpownonneg
    rw [hWdef]
    linarith
  have hpowone : L ^ k₁ ≤ L ^ (k₁ + k₂) :=
    pow_le_pow_right₀ hlogone (Nat.le_add_right k₁ k₂)
  have hpowtwo : L ^ k₂ ≤ L ^ (k₁ + k₂) :=
    pow_le_pow_right₀ hlogone (Nat.le_add_left k₂ k₁)
  have hKnonneg : (0 : ℝ) ≤ L ^ (k₁ + k₂) := pow_nonneg hLnonneg _
  have hmid : C₁ * L ^ k₁ * U + C₂ * L ^ k₂ * W ≤
      (C₁ + C₂) * L ^ (k₁ + k₂) * (U + W) := by
    have hone : C₁ * L ^ k₁ * U ≤ C₁ * L ^ (k₁ + k₂) * U :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpowone hC₁.le) hUnonneg
    have htwo : C₂ * L ^ k₂ * W ≤ C₂ * L ^ (k₁ + k₂) * W :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpowtwo hC₂.le) hWnonneg
    have hthree : (0 : ℝ) ≤ C₂ * L ^ (k₁ + k₂) * U :=
      mul_nonneg (mul_nonneg hC₂.le hKnonneg) hUnonneg
    have hfour : (0 : ℝ) ≤ C₁ * L ^ (k₁ + k₂) * W :=
      mul_nonneg (mul_nonneg hC₁.le hKnonneg) hWnonneg
    nlinarith [hone, htwo, hthree, hfour]
  have hprefactor : (0 : ℝ) ≤ C₀ * L ^ k₀ :=
    mul_nonneg hC₀.le (pow_nonneg hLnonneg _)
  calc
    swap_multicalibration_error P F Γ.identification q T ω ≤
        C₀ * L ^ k₀ * preoptimized_rate P A q ρ δ T ω := hEbound ω hω
    _ ≤ C₀ * L ^ k₀ * (C₁ * L ^ k₁ * U + C₂ * L ^ k₂ * W) :=
      mul_le_mul_of_nonneg_left (add_le_add hdisc hreg) hprefactor
    _ ≤ C₀ * L ^ k₀ * ((C₁ + C₂) * L ^ (k₁ + k₂) * (U + W)) :=
      mul_le_mul_of_nonneg_left hmid hprefactor
    _ = C₀ * (C₁ + C₂) * (L ^ k₀ * L ^ (k₁ + k₂)) * (U + W) := by ring
    _ = C₀ * (C₁ + C₂) * L ^ (k₀ + k₁ + k₂) * (U + W) := by
      rw [← pow_add, ← add_assoc]
    _ = C₀ * (C₁ + C₂) * L ^ (k₀ + k₁ + k₂) *
        large_exponent_rate q ρ α complexity δ T := by
      rw [large_exponent_rate, hUdef, hWdef]
      ring

@[blueprint "lem:holder-swap-error"
  (statement := /-- Let \(X\), \(Y\), and \(\Omega\) be types, equip
  \(\Omega\) with a measurable space, and let \(P\) be a forecasting
  process on these spaces whose predictions belong to its declared grid.
  Let \(\mathcal F\subseteq (X\to\mathbb R)\) be nonempty, let
  \(V:[0,1]\to Y\to\mathbb R\), and let \(r\in\mathbb R\) satisfy
  \(1\le r<2\).  Then, for every \(T\in\mathbb N\) and
  \(\omega\in\Omega\),
  \[
    \operatorname{smcal}_{P,V,r}(\mathcal F;T,\omega)
      \le T^{1-r/2}
        \bigl(\operatorname{smcal}_{P,V,2}
          (\mathcal F;T,\omega)\bigr)^{r/2}.
  \] -/)
  (proof := /-- Write \(n_i\) for the \(i\)-th bucket count and \(d_i\)
  for its normalized correlation.  By
  \(\cref{def:bucket-correlation}\), each \(d_i\) is nonnegative: it is
  either zero or the product of a nonnegative reciprocal with the supremum
  of a set of absolute values.  Put \(s=r/2\) and \(t=1-r/2\).  Both are
  positive, and \(s^{-1}\) and \(t^{-1}\) are H\"older conjugates.  Apply
  H\"older's inequality to the two finite sequences
  \((n_i d_i^2)^s\) and \(n_i^t\).  The real-power product identities give
  \[
    (n_i d_i^2)^s n_i^t=n_i d_i^r,
    \qquad ((n_i d_i^2)^s)^{s^{-1}}=n_i d_i^2,
    \qquad (n_i^t)^{t^{-1}}=n_i.
  \]
  Thus the resulting upper bound is
  \((\sum_i n_i d_i^2)^s(\sum_i n_i)^t\).  Substitute
  \(\sum_i n_i=T\) from \(\cref{lem:bucket-counts-sum}\) and unfold
  \(\cref{def:swap-multicalibration-error}\). -/)
  (title := /-- Hölder interpolation of swap errors -/)
  (latexEnv := "lemma")]
lemma holder_swap_error
    {X Y Ω : Type*} [MeasurableSpace Ω]
    (P : forecasting_process X Y Ω) (F : Set (X → ℝ))
    (V : Set.Icc (0 : ℝ) 1 → Y → ℝ) (r : ℝ)
    (hrone : 1 ≤ r) (hrtwo : r < 2)
    (hF : F.Nonempty) (hgrid : uses_prediction_grid P)
    (T : ℕ) (ω : Ω) :
    swap_multicalibration_error P F V r T ω ≤
      (T : ℝ) ^ (1 - r / 2) *
        (swap_multicalibration_error P F V 2 T ω) ^ (r / 2) := by
  classical
  let n : Fin (P.gridSize T) → ℝ := fun i => bucket_count P T ω i
  let d : Fin (P.gridSize T) → ℝ := fun i => bucket_correlation P F V T ω i
  let s : ℝ := r / 2
  let t : ℝ := 1 - r / 2
  let p : ℝ := s⁻¹
  let q : ℝ := t⁻¹
  have hn (i : Fin (P.gridSize T)) : 0 ≤ n i := by
    simp [n]
  have hd (i : Fin (P.gridSize T)) : 0 ≤ d i := by
    simp only [d]
    rw [bucket_correlation]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Real.sSup_nonneg fun a ha => by
          rcases ha with ⟨f, hf, rfl⟩
          exact abs_nonneg _)
  have hs : 0 < s := by
    simp [s]
    nlinarith
  have ht : 0 < t := by
    simp [t]
    nlinarith
  have hleft (i : Fin (P.gridSize T)) :
      (n i * d i ^ (2 : ℝ)) ^ s * n i ^ t = n i * d i ^ r := by
    rw [Real.mul_rpow (hn i) (Real.rpow_nonneg (hd i) _)]
    conv_rhs => rw [← Real.rpow_one (n i),
      show (1 : ℝ) = s + t by simp [s, t],
      Real.rpow_add' (hn i) (by simp [s, t])]
    rw [← Real.rpow_mul (hd i)]
    simp only [s]
    ring_nf
  have hfirst (i : Fin (P.gridSize T)) :
      |(n i * d i ^ (2 : ℝ)) ^ s| ^ p = n i * d i ^ (2 : ℝ) := by
    rw [abs_of_nonneg
      (Real.rpow_nonneg (mul_nonneg (hn i) (Real.rpow_nonneg (hd i) _)) _)]
    rw [← Real.rpow_mul
      (mul_nonneg (hn i) (Real.rpow_nonneg (hd i) _)) s p]
    rw [show s * p = 1 by simp [p, hs.ne'], Real.rpow_one]
  have hsecond (i : Fin (P.gridSize T)) :
      |n i ^ t| ^ q = n i := by
    rw [abs_of_nonneg (Real.rpow_nonneg (hn i) _)]
    rw [← Real.rpow_mul (hn i) t q]
    rw [show t * q = 1 by simp [q, ht.ne'], Real.rpow_one]
  have hconj : Real.HolderConjugate p q :=
    Real.HolderConjugate.inv_inv hs ht (by simp [s, t, p, q])
  have hsum : ∑ i : Fin (P.gridSize T), n i = (T : ℝ) := by
    simp only [n, ← Nat.cast_sum]
    exact_mod_cast bucket_counts_sum P hgrid T ω
  have hholder := Real.inner_le_Lp_mul_Lq
    (s := (Finset.univ : Finset (Fin (P.gridSize T))))
    (f := fun i => (n i * d i ^ (2 : ℝ)) ^ s)
    (g := fun i => n i ^ t) hconj
  simp_rw [hleft, hfirst, hsecond] at hholder
  simpa [swap_multicalibration_error, n, d, s, t, p, q, hsum,
    hs.ne', ht.ne', mul_comm] using hholder

@[blueprint "lem:small-exponent-algorithm-bound"
  (statement := /-- Let \(1\le r<2\) and make the hypotheses, including
  strict positivity of the complexity \(C\), of
  \(\cref{lem:large-exponent-algorithm-bound}\) with the quadratic tuning
  \(N_2(T)\).  Then there are a positive constant and a polylogarithmic
  exponent, both independent of \(\delta\), such that, for every
  \(0<\delta<1\),
  \[
    \operatorname{smcal}_{\Gamma,r}(\mathcal F)
      =\widetilde{\mathcal O}(R_{<2}(T,\delta))
  \]
  on a measurable event of probability at least \(1-\delta\). -/)
  (proof := /-- Apply
  \(\cref{lem:large-exponent-algorithm-bound}\) with \(q=2\).  On the
  resulting event, use \(\cref{lem:holder-swap-error}\) and raise the four
  nonnegative terms of the quadratic rate to the power \(r/2\).
  Since \(0<r/2\le1\), repeated subadditivity of \(x\mapsto x^{r/2}\)
  bounds the power of their sum by the sum of their powers.  Multiplication
  by \(T^{1-r/2}\) gives respectively the four terms in
  \(R_{<2}(T,\delta)\), and the event still has probability at least
  \(1-\delta\). -/)
  (title := /-- Oracle-efficient bound for exponents below two -/)
  (latexEnv := "lemma")]
lemma small_exponent_algorithm_bound
    {X Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]
    (Γ : identified_property Y)
    (P : forecasting_process X Y Ω) (A : online_agnostic_learner X)
    (F : Set (X → ℝ)) (r ρ α complexity : ℝ)
    (hrone : 1 ≤ r) (hrtwo : r < 2)
    (hαzero : 0 ≤ α) (hαone : α < 1)
    (hcomplexity : 0 < complexity)
    (hidentify : is_identification_function Γ)
    (hlip : lipschitz_identification Γ ρ)
    (hbounded : ∀ f ∈ F, ∀ x, |f x| ≤ 1)
    (hF : F.Nonempty)
    (honline : online_agnostic_regret A F)
    (hregret_nonneg : ∀ n, 0 ≤ A.regret n)
    (hregret :
      soft_big_o A.regret
        (fun n => (n : ℝ) ^ α * complexity))
    (hgrid : uses_prediction_grid P)
    (hsize : ∀ T, P.gridSize T = tuned_grid_size 2 T)
    (hAlgorithm :
      oracle_efficient_execution P A F Γ.identification 2 ρ) :
    high_probability_soft_bound P.measure
      (swap_multicalibration_error P F Γ.identification r)
      (fun δ T _ => small_exponent_rate r ρ α complexity δ T) := by
  obtain ⟨C₀, hC₀, k₀, h₀⟩ :=
    large_exponent_algorithm_bound Γ P A F 2 ρ α complexity le_rfl hαzero hαone
      hcomplexity hidentify hlip hbounded honline hregret_nonneg hregret hgrid
      hsize hAlgorithm
  have hρ : (0 : ℝ) ≤ ρ := hlip.1
  have hrhalfzero : (0 : ℝ) ≤ r / 2 := by linarith
  have hrhalfone : r / 2 ≤ 1 := by linarith
  unfold high_probability_soft_bound
  refine ⟨1 + C₀, by linarith, k₀, ?_⟩
  intro δ hδ hδone
  filter_upwards [h₀ δ hδ hδone,
    Filter.eventually_ge_atTop (Nat.ceil (Real.exp 1))] with T hTzero hTlarge
  obtain ⟨E, hEmeas, hEprob, hEbound⟩ := hTzero
  refine ⟨E, hEmeas, hEprob, ?_⟩
  intro ω hω
  have hTpos : 0 < T := (Nat.ceil_pos.mpr (Real.exp_pos 1)).trans_le hTlarge
  have hTreal : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hTpos
  have hlogone : 1 ≤ Real.log ((T : ℝ) + 2) := by
    have hexp_le : Real.exp 1 ≤ (T : ℝ) + 2 := by
      calc
        Real.exp 1 ≤ (Nat.ceil (Real.exp 1) : ℝ) := Nat.le_ceil _
        _ ≤ (T : ℝ) := by exact_mod_cast hTlarge
        _ ≤ (T : ℝ) + 2 := by linarith
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log ((T : ℝ) + 2) := Real.log_le_log (Real.exp_pos 1) hexp_le
  have hlogδ : 0 < Real.log (1 / δ) := Real.log_pos (by
    rw [one_div]
    exact (one_lt_inv₀ hδ).2 hδone)
  set L : ℝ := Real.log ((T : ℝ) + 2) with hLdef
  have hLnonneg : (0 : ℝ) ≤ L := by linarith
  have hTupow : (0 : ℝ) ≤ (T : ℝ) ^ (1 - r / 2) := Real.rpow_nonneg hTreal.le _
  have hcorr : ∀ i : Fin (P.gridSize T),
      0 ≤ bucket_correlation P F Γ.identification T ω i := by
    intro i
    rw [bucket_correlation]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Real.sSup_nonneg fun a ha => by
          rcases ha with ⟨f, hf, rfl⟩
          exact abs_nonneg _)
  have hswapnonneg :
      0 ≤ swap_multicalibration_error P F Γ.identification 2 T ω := by
    rw [swap_multicalibration_error]
    refine Finset.sum_nonneg fun i _ => ?_
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (hcorr i) _)
  have hsub : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d →
      (a + b + c + d) ^ (r / 2) ≤
        a ^ (r / 2) + b ^ (r / 2) + c ^ (r / 2) + d ^ (r / 2) := by
    intro a b c d ha hb hc hd
    have hthree : (a + b) ^ (r / 2) ≤ a ^ (r / 2) + b ^ (r / 2) :=
      Real.rpow_add_le_add_rpow ha hb hrhalfzero hrhalfone
    have htwo : (a + b + c) ^ (r / 2) ≤ (a + b) ^ (r / 2) + c ^ (r / 2) :=
      Real.rpow_add_le_add_rpow (by linarith) hc hrhalfzero hrhalfone
    have hone :
        (a + b + c + d) ^ (r / 2) ≤ (a + b + c) ^ (r / 2) + d ^ (r / 2) :=
      Real.rpow_add_le_add_rpow (by linarith) hd hrhalfzero hrhalfone
    linarith
  have hmul : ∀ p w z : ℝ, 0 ≤ z → 1 - r / 2 + p * (r / 2) = w →
      (T : ℝ) ^ (1 - r / 2) * ((T : ℝ) ^ p * z) ^ (r / 2) =
        (T : ℝ) ^ w * z ^ (r / 2) := by
    intro p w z hz hw
    rw [Real.mul_rpow (Real.rpow_nonneg hTreal.le p) hz,
      ← Real.rpow_mul hTreal.le p (r / 2), ← mul_assoc,
      ← Real.rpow_add hTreal, hw]
  have hsquare : ∀ z : ℝ, 0 ≤ z → (z ^ (2 : ℝ)) ^ (r / 2) = z ^ r := by
    intro z hz
    rw [← Real.rpow_mul hz]
    congr 1
    ring
  have hAnonneg : (0 : ℝ) ≤ ρ ^ (2 : ℝ) * (T : ℝ) ^ (1 / ((2 : ℝ) + 1)) :=
    mul_nonneg (Real.rpow_nonneg hρ _) (Real.rpow_nonneg hTreal.le _)
  have hBnonneg : (0 : ℝ) ≤
      (T : ℝ) ^ (1 / ((2 : ℝ) + 1)) * Real.log (1 / δ) ^ ((2 : ℝ) / 2) :=
    mul_nonneg (Real.rpow_nonneg hTreal.le _) (Real.rpow_nonneg hlogδ.le _)
  have hCnonneg : (0 : ℝ) ≤
      (T : ℝ) ^ (1 - 2 + 2 / ((2 : ℝ) + 1) +
          α * (2 : ℝ) ^ 2 / ((2 : ℝ) + 1)) * complexity ^ (2 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hTreal.le _) (Real.rpow_nonneg hcomplexity.le _)
  have hDnonneg : (0 : ℝ) ≤
      (T : ℝ) ^ (1 / ((2 : ℝ) + 1)) * complexity ^ (2 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hTreal.le _) (Real.rpow_nonneg hcomplexity.le _)
  have hR2nonneg : (0 : ℝ) ≤ large_exponent_rate 2 ρ α complexity δ T := by
    rw [large_exponent_rate]
    linarith
  have hkey :
      (T : ℝ) ^ (1 - r / 2) *
          large_exponent_rate 2 ρ α complexity δ T ^ (r / 2) ≤
        small_exponent_rate r ρ α complexity δ T := by
    rw [large_exponent_rate, small_exponent_rate]
    calc
      (T : ℝ) ^ (1 - r / 2) *
            (ρ ^ (2 : ℝ) * (T : ℝ) ^ (1 / ((2 : ℝ) + 1)) +
              (T : ℝ) ^ (1 / ((2 : ℝ) + 1)) *
                Real.log (1 / δ) ^ ((2 : ℝ) / 2) +
              (T : ℝ) ^ (1 - 2 + 2 / ((2 : ℝ) + 1) +
                  α * (2 : ℝ) ^ 2 / ((2 : ℝ) + 1)) * complexity ^ (2 : ℝ) +
              (T : ℝ) ^ (1 / ((2 : ℝ) + 1)) * complexity ^ (2 : ℝ)) ^ (r / 2) ≤
          (T : ℝ) ^ (1 - r / 2) *
            ((ρ ^ (2 : ℝ) * (T : ℝ) ^ (1 / ((2 : ℝ) + 1))) ^ (r / 2) +
              ((T : ℝ) ^ (1 / ((2 : ℝ) + 1)) *
                Real.log (1 / δ) ^ ((2 : ℝ) / 2)) ^ (r / 2) +
              ((T : ℝ) ^ (1 - 2 + 2 / ((2 : ℝ) + 1) +
                  α * (2 : ℝ) ^ 2 / ((2 : ℝ) + 1)) *
                complexity ^ (2 : ℝ)) ^ (r / 2) +
              ((T : ℝ) ^ (1 / ((2 : ℝ) + 1)) * complexity ^ (2 : ℝ)) ^
                (r / 2)) :=
        mul_le_mul_of_nonneg_left
          (hsub _ _ _ _ hAnonneg hBnonneg hCnonneg hDnonneg) hTupow
      _ = (T : ℝ) ^ (1 - r / 2) *
              (ρ ^ (2 : ℝ) * (T : ℝ) ^ (1 / ((2 : ℝ) + 1))) ^ (r / 2) +
            (T : ℝ) ^ (1 - r / 2) *
              ((T : ℝ) ^ (1 / ((2 : ℝ) + 1)) *
                Real.log (1 / δ) ^ ((2 : ℝ) / 2)) ^ (r / 2) +
            (T : ℝ) ^ (1 - r / 2) *
              ((T : ℝ) ^ (1 - 2 + 2 / ((2 : ℝ) + 1) +
                  α * (2 : ℝ) ^ 2 / ((2 : ℝ) + 1)) *
                complexity ^ (2 : ℝ)) ^ (r / 2) +
            (T : ℝ) ^ (1 - r / 2) *
              ((T : ℝ) ^ (1 / ((2 : ℝ) + 1)) * complexity ^ (2 : ℝ)) ^
                (r / 2) := by
        ring
      _ = ρ ^ r * (T : ℝ) ^ (1 - r / 3) +
            (T : ℝ) ^ (1 - r / 3) * Real.log (1 / δ) ^ (r / 2) +
            (T : ℝ) ^ (1 + 2 * r * (α - 1) / 3) * complexity ^ r +
            (T : ℝ) ^ (1 - r / 3) * complexity ^ r := by
        rw [mul_comm (ρ ^ (2 : ℝ)) ((T : ℝ) ^ (1 / ((2 : ℝ) + 1)))]
        rw [hmul (1 / ((2 : ℝ) + 1)) (1 - r / 3) (ρ ^ (2 : ℝ))
          (Real.rpow_nonneg hρ _) (by ring)]
        rw [hmul (1 / ((2 : ℝ) + 1)) (1 - r / 3)
          (Real.log (1 / δ) ^ ((2 : ℝ) / 2))
          (Real.rpow_nonneg hlogδ.le _) (by ring)]
        rw [hmul (1 - 2 + 2 / ((2 : ℝ) + 1) + α * (2 : ℝ) ^ 2 / ((2 : ℝ) + 1))
          (1 + 2 * r * (α - 1) / 3) (complexity ^ (2 : ℝ))
          (Real.rpow_nonneg hcomplexity.le _) (by ring)]
        rw [hmul (1 / ((2 : ℝ) + 1)) (1 - r / 3) (complexity ^ (2 : ℝ))
          (Real.rpow_nonneg hcomplexity.le _) (by ring)]
        rw [hsquare ρ hρ, hsquare complexity hcomplexity.le]
        have hlogrewrite : (Real.log (1 / δ) ^ ((2 : ℝ) / 2)) ^ (r / 2) =
            Real.log (1 / δ) ^ (r / 2) := by
          rw [← Real.rpow_mul hlogδ.le]
          congr 1
          ring
        rw [hlogrewrite]
        ring
  have hprefactornonneg : (0 : ℝ) ≤ C₀ * L ^ k₀ :=
    mul_nonneg hC₀.le (pow_nonneg hLnonneg _)
  have hCpow : (C₀ * L ^ k₀) ^ (r / 2) ≤ (1 + C₀) * L ^ k₀ := by
    have hone : C₀ ^ (r / 2) ≤ 1 + C₀ := by
      calc
        C₀ ^ (r / 2) ≤ (1 + C₀) ^ (r / 2) :=
          Real.rpow_le_rpow hC₀.le (by linarith) hrhalfzero
        _ ≤ (1 + C₀) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hrhalfone
        _ = 1 + C₀ := Real.rpow_one _
    have htwo : (L ^ k₀) ^ (r / 2) ≤ L ^ k₀ := by
      calc
        (L ^ k₀) ^ (r / 2) ≤ (L ^ k₀) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hlogone) hrhalfone
        _ = L ^ k₀ := Real.rpow_one _
    calc
      (C₀ * L ^ k₀) ^ (r / 2) = C₀ ^ (r / 2) * (L ^ k₀) ^ (r / 2) :=
        Real.mul_rpow hC₀.le (pow_nonneg hLnonneg _)
      _ ≤ (1 + C₀) * L ^ k₀ :=
        mul_le_mul hone htwo
          (Real.rpow_nonneg (pow_nonneg hLnonneg _) _) (by linarith)
  calc
    swap_multicalibration_error P F Γ.identification r T ω ≤
        (T : ℝ) ^ (1 - r / 2) *
          swap_multicalibration_error P F Γ.identification 2 T ω ^ (r / 2) :=
      holder_swap_error P F Γ.identification r hrone hrtwo hF hgrid T ω
    _ ≤ (T : ℝ) ^ (1 - r / 2) *
          (C₀ * L ^ k₀ * large_exponent_rate 2 ρ α complexity δ T) ^ (r / 2) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hswapnonneg (hEbound ω hω) hrhalfzero) hTupow
    _ = (T : ℝ) ^ (1 - r / 2) *
          ((C₀ * L ^ k₀) ^ (r / 2) *
            large_exponent_rate 2 ρ α complexity δ T ^ (r / 2)) := by
      rw [Real.mul_rpow hprefactornonneg hR2nonneg]
    _ ≤ (T : ℝ) ^ (1 - r / 2) *
          ((1 + C₀) * L ^ k₀ *
            large_exponent_rate 2 ρ α complexity δ T ^ (r / 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ hTupow
      exact mul_le_mul_of_nonneg_right hCpow (Real.rpow_nonneg hR2nonneg _)
    _ = (1 + C₀) * L ^ k₀ *
          ((T : ℝ) ^ (1 - r / 2) *
            large_exponent_rate 2 ρ α complexity δ T ^ (r / 2)) := by ring
    _ ≤ (1 + C₀) * L ^ k₀ * small_exponent_rate r ρ α complexity δ T :=
      mul_le_mul_of_nonneg_left hkey
        (mul_nonneg (by linarith) (pow_nonneg hLnonneg _))

@[blueprint "thm:smcal-general-result"
  (statement := /-- Fix \(r\ge1\).  Let \(\Gamma\) be an elicitable property
  with a \(\rho\)-Lipschitz identification function, let
  \(\mathcal F\subseteq[-1,1]^{\mathcal X}\), and suppose that there is an
  online agnostic learner with
  \(\mathsf{Reg}(\mathcal F,n)=
    \widetilde{\mathcal O}(n^\alpha\operatorname{comp}(\mathcal F))\),
  where \(0\le\alpha<1\) and the complexity is strictly positive and
  independent of \(n\).
  Run the oracle-efficient algorithm with
  \(N_T=N_{\max\{r,2\}}(T)\).  The hidden constant and polylogarithmic
  exponent below are independent of \(\delta\), and every success event is
  measurable.  If \(r\ge2\), then, for every \(0<\delta<1\), with
  probability at least \(1-\delta\),
  \[
    \operatorname{smcal}_{\Gamma,r}(\mathcal F)
      =\widetilde{\mathcal O}(R_{\ge2}(T,\delta)).
  \]
  If \(1\le r<2\), then, for every \(0<\delta<1\), with probability at
  least \(1-\delta\),
  \[
    \operatorname{smcal}_{\Gamma,r}(\mathcal F)
      =\widetilde{\mathcal O}(R_{<2}(T,\delta)).
  \] -/)
  (proof := /-- If \(r\ge2\), then \(\max\{r,2\}=r\), and the first
  conclusion is \(\cref{lem:large-exponent-algorithm-bound}\).  If
  \(1\le r<2\), then \(\max\{r,2\}=2\), and the second conclusion is
  \(\cref{lem:small-exponent-algorithm-bound}\).  These two implications
  give the asserted pair of regime-dependent guarantees. -/)
  (title := /-- Efficient swap multicalibration of elicitable properties -/)
  (latexEnv := "theorem")]
theorem smcal_general_result
    {X Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]
    (Γ : identified_property Y)
    (P : forecasting_process X Y Ω) (A : online_agnostic_learner X)
    (F : Set (X → ℝ)) (r ρ α complexity : ℝ)
    (hr : 1 ≤ r)
    (hαzero : 0 ≤ α) (hαone : α < 1)
    (hcomplexity : 0 < complexity)
    (helicitable : elicitable_property Γ)
    (hidentify : is_identification_function Γ)
    (hlip : lipschitz_identification Γ ρ)
    (hbounded : ∀ f ∈ F, ∀ x, |f x| ≤ 1)
    (hF : F.Nonempty)
    (honline : online_agnostic_regret A F)
    (hregret_nonneg : ∀ n, 0 ≤ A.regret n)
    (hregret :
      soft_big_o A.regret
        (fun n => (n : ℝ) ^ α * complexity))
    (hgrid : uses_prediction_grid P)
    (hsize :
      ∀ T, P.gridSize T = tuned_grid_size (max r 2) T)
    (hAlgorithm :
      oracle_efficient_execution P A F Γ.identification (max r 2) ρ) :
    (2 ≤ r →
      high_probability_soft_bound P.measure
        (swap_multicalibration_error P F Γ.identification r)
        (fun δ T _ => large_exponent_rate r ρ α complexity δ T)) ∧
    ((1 ≤ r ∧ r < 2) →
      high_probability_soft_bound P.measure
        (swap_multicalibration_error P F Γ.identification r)
        (fun δ T _ => small_exponent_rate r ρ α complexity δ T)) := by
  constructor
  · intro hrtwo
    have hmax : max r 2 = r := max_eq_left hrtwo
    have hAlgorithm' : oracle_efficient_execution P A F Γ.identification r ρ := by
      have h := hAlgorithm
      rw [hmax] at h
      exact h
    have hsize' : ∀ T, P.gridSize T = tuned_grid_size r T := by
      intro T
      rw [hsize T, hmax]
    exact large_exponent_algorithm_bound Γ P A F r ρ α complexity hrtwo hαzero
      hαone hcomplexity hidentify hlip hbounded honline hregret_nonneg hregret
      hgrid hsize' hAlgorithm'
  · rintro ⟨hrone, hrtwo⟩
    have hmax : max r 2 = 2 := max_eq_right hrtwo.le
    have hAlgorithm' : oracle_efficient_execution P A F Γ.identification 2 ρ := by
      have h := hAlgorithm
      rw [hmax] at h
      exact h
    have hsize' : ∀ T, P.gridSize T = tuned_grid_size 2 T := by
      intro T
      rw [hsize T, hmax]
    exact small_exponent_algorithm_bound Γ P A F r ρ α complexity hrone hrtwo
      hαzero hαone hcomplexity hidentify hlip hbounded hF honline hregret_nonneg
      hregret hgrid hsize' hAlgorithm'

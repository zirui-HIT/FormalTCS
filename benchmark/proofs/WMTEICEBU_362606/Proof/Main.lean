import Architect
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory ProbabilityTheory

@[blueprint "def:full-space"
  (statement := /-- The space of complete outcomes of an observational study,
    modeling a random vector $(X, T, Y(0), Y(1))$ consisting of a covariate
    vector $X \in \mathbb{R}^{d}$, a binary treatment indicator $T \in \{0,1\}$,
    and two potential outcomes $Y(0), Y(1) \in \mathbb{R}$. The Euclidean space
    $\mathbb{R}^{d}$ is represented by $\mathrm{Fin}\,d \to \mathbb{R}$ and the
    treatment $\{0,1\}$ by the Booleans, with $0$ encoded as $\mathrm{false}$ and
    $1$ as $\mathrm{true}$. -/)
  (title := /-- Complete Outcome Space -/)
  (latexEnv := "definition")]
abbrev full_space (d : ℕ) : Type := (Fin d → ℝ) × Bool × ℝ × ℝ

@[blueprint "def:observed-space"
  (statement := /-- The space of censored (observed) outcomes, modeling the
    triple $(X, T, Y(T))$ consisting of the covariate vector
    $X \in \mathbb{R}^{d}$, the treatment indicator $T \in \{0,1\}$, and the
    single observed potential outcome $Y(T) \in \mathbb{R}$. As in
    \cref{def:full-space}, $\mathbb{R}^{d}$ is $\mathrm{Fin}\,d \to \mathbb{R}$
    and $\{0,1\}$ is the Booleans. -/)
  (title := /-- Observed (Censored) Outcome Space -/)
  (latexEnv := "definition")]
abbrev observed_space (d : ℕ) : Type := (Fin d → ℝ) × Bool × ℝ

@[blueprint "def:observational-study"
  (statement := /-- An observational study $\mathcal{D}$ is a probability
    distribution over complete outcomes $(X, T, Y(0), Y(1))$. Formally it is a
    Borel probability measure on the complete outcome space of
    \cref{def:full-space}, bundled together with the proof that it has total
    mass one. -/)
  (title := /-- Observational Study -/)
  (latexEnv := "definition")]
structure observational_study (d : ℕ) where
  law : Measure (full_space d)
  isProb : IsProbabilityMeasure law

@[blueprint "def:study-law-is-probability-measure"
  (statement := /-- The underlying measure $\mathcal{D}.\mathrm{law}$ of an
    observational study $\mathcal{D}$ (\cref{def:observational-study}) is a
    probability measure. This registers the bundled proof as a typeclass
    instance so that expectations and regular conditional distributions with
    respect to $\mathcal{D}$ are well defined. -/)
  (title := /-- Study Law Is a Probability Measure -/)
  (latexEnv := "definition")]
instance study_law_is_probability_measure {d : ℕ} (D : observational_study d) :
    IsProbabilityMeasure D.law := D.isProb

@[blueprint "def:censoring-map"
  (statement := /-- The censoring map $(x, t, y_{0}, y_{1}) \mapsto (x, t, y_{t})$
    sending a complete outcome to the observed triple $(X, T, Y(T))$, where the
    revealed outcome is $y_{t} = y_{1}$ when $t = 1$ (i.e. $\mathrm{true}$) and
    $y_{t} = y_{0}$ when $t = 0$ (i.e. $\mathrm{false}$). -/)
  (title := /-- Censoring Map -/)
  (latexEnv := "definition")]
def censoring_map (d : ℕ) : full_space d → observed_space d :=
  fun w => (w.1, w.2.1, if w.2.1 then w.2.2.2 else w.2.2.1)

@[blueprint "def:censored-distribution"
  (statement := /-- The censored distribution $\mathcal{C}_{\mathcal{D}}$ induced
    by an observational study $\mathcal{D}$: the law of the observed data
    $(X, T, Y(T))$, defined as the pushforward of $\mathcal{D}.\mathrm{law}$
    (\cref{def:observational-study}) along the censoring map
    \cref{def:censoring-map}. -/)
  (title := /-- Censored Distribution -/)
  (latexEnv := "definition")]
noncomputable def censored_distribution {d : ℕ} (D : observational_study d) :
    Measure (observed_space d) :=
  D.law.map (censoring_map d)

@[blueprint "def:average-treatment-effect"
  (statement := /-- The average treatment effect of an observational study
    $\mathcal{D}$, defined as
    $\tau_{\mathcal{D}} := \mathbb{E}_{\mathcal{D}}\big[\,Y(1) - Y(0)\,\big]$,
    the Bochner integral of the difference of the two potential outcomes with
    respect to $\mathcal{D}.\mathrm{law}$ (\cref{def:observational-study}). -/)
  (title := /-- Average Treatment Effect -/)
  (latexEnv := "definition")]
noncomputable def average_treatment_effect {d : ℕ} (D : observational_study d) : ℝ :=
  ∫ w, (w.2.2.2 - w.2.2.1) ∂D.law

@[blueprint "def:induced-propensity"
  (statement := /-- For $t \in \{0,1\}$, the generalized propensity score induced
    by an observational study $\mathcal{D}$ is
    $p_{t}(x, y) := \Pr_{\mathcal{D}}[\,T = t \mid X = x,\ Y(t) = y\,]$. It is
    realized as the mass assigned to the singleton $\{t\}$ by the regular
    conditional distribution of the treatment $T$ given the pair $(X, Y(t))$
    under $\mathcal{D}.\mathrm{law}$ (\cref{def:observational-study}); this
    regular conditional distribution makes the conditioning on the
    probability-zero event $\{Y(t) = y\}$ well defined. The value is returned as
    a real number. -/)
  (title := /-- Generalized Propensity Score -/)
  (latexEnv := "definition")]
noncomputable def induced_propensity {d : ℕ} (D : observational_study d) (t : Bool) :
    (Fin d → ℝ) × ℝ → ℝ :=
  fun z =>
    ((condDistrib (fun w : full_space d => w.2.1)
      (fun w : full_space d => (w.1, if t then w.2.2.2 else w.2.2.1)) D.law) z {t}).toReal

@[blueprint "def:outcome-marginal"
  (statement := /-- For $t \in \{0,1\}$, the covariate-outcome marginal
    $\mathcal{D}_{X, Y(t)}$ of an observational study $\mathcal{D}$: the joint law
    of the pair $(X, Y(t))$ under $\mathcal{D}.\mathrm{law}$
    (\cref{def:observational-study}), i.e. the pushforward of
    $\mathcal{D}.\mathrm{law}$ along $(x, t', y_{0}, y_{1}) \mapsto (x, y_{t})$. -/)
  (title := /-- Outcome Marginal Distribution -/)
  (latexEnv := "definition")]
noncomputable def outcome_marginal {d : ℕ} (D : observational_study d) (t : Bool) :
    Measure ((Fin d → ℝ) × ℝ) :=
  D.law.map (fun w : full_space d => (w.1, if t then w.2.2.2 else w.2.2.1))

@[blueprint "def:propensity-class"
  (statement := /-- The type of concept classes $\mathcal{P}$ of generalized
    propensity scores. A concept class is a set of real-valued functions on
    $\mathbb{R}^{d} \times \mathbb{R}$ (the intended range of each function is
    the unit interval $[0,1]$). -/)
  (title := /-- Concept Class of Propensity Scores -/)
  (latexEnv := "definition")]
abbrev propensity_class (d : ℕ) : Type := Set ((Fin d → ℝ) × ℝ → ℝ)

@[blueprint "def:outcome-class"
  (statement := /-- The type of concept classes $\mathcal{H}$ of
    conditional-outcome distributions. A concept class is a set of measures on
    $\mathbb{R}^{d} \times \mathbb{R}$. -/)
  (title := /-- Concept Class of Outcome Distributions -/)
  (latexEnv := "definition")]
abbrev outcome_class (d : ℕ) : Type := Set (Measure ((Fin d → ℝ) × ℝ))

@[blueprint "def:finite-first-moment"
  (statement := /-- A covariate-outcome measure $P$ on
    $\mathbb{R}^{d} \times \mathbb{R}$ has finite first moment in the outcome
    coordinate if the map $(x,y) \mapsto y$ is Bochner integrable with respect
    to $P$. -/)
  (title := /-- Finite First Moment of the Outcome -/)
  (latexEnv := "definition")]
def finite_first_moment {d : ℕ} (P : Measure ((Fin d → ℝ) × ℝ)) : Prop :=
  Integrable (fun z : (Fin d → ℝ) × ℝ => z.2) P

@[blueprint "def:realizable"
  (statement := /-- An observational study $\mathcal{D}$ is realizable with
    respect to a pair of concept classes $(\mathcal{P}, \mathcal{H})$, where
    $\mathcal{P}$ is a propensity-score class (\cref{def:propensity-class}) and
    $\mathcal{H}$ is an outcome-distribution class (\cref{def:outcome-class}), if
    both induced propensity scores $p_{0}, p_{1}$ (\cref{def:induced-propensity})
    lie in $\mathcal{P}$ and both outcome marginals
    $\mathcal{D}_{X, Y(0)}, \mathcal{D}_{X, Y(1)}$ (\cref{def:outcome-marginal})
    lie in $\mathcal{H}$. In addition, each of these two outcome marginals has
    finite first moment in the sense of \cref{def:finite-first-moment}; thus both
    potential-outcome expectations are finite. -/)
  (title := /-- Realizability -/)
  (latexEnv := "definition")]
def realizable {d : ℕ} (D : observational_study d)
    (Pcl : propensity_class d) (Dcl : outcome_class d) : Prop :=
  induced_propensity D false ∈ Pcl ∧ induced_propensity D true ∈ Pcl ∧
    outcome_marginal D false ∈ Dcl ∧ outcome_marginal D true ∈ Dcl ∧
    finite_first_moment (outcome_marginal D false) ∧
    finite_first_moment (outcome_marginal D true)

@[blueprint "def:compatible"
  (statement := /-- A tuple $(p, P) \in \mathcal{P} \times \mathcal{H}$ is
    compatible in treatment arm $t \in \{0,1\}$ with the concept classes
    $(\mathcal{P}, \mathcal{H})$ (\cref{def:propensity-class},
    \cref{def:outcome-class}) if there is an observational study
    $\mathcal{D}$ (\cref{def:observational-study}) realizable with respect to
    $(\mathcal{P}, \mathcal{H})$ (\cref{def:realizable}) such that
    $\mathcal{D}_{X,Y(t)}=P$ (\cref{def:outcome-marginal}) and the induced
    propensity score $p_t$ (\cref{def:induced-propensity}) agrees with $p$
    almost everywhere with respect to $P$. Thus compatibility is available
    in either treatment arm and is independent of the choice of a version of
    the relevant regular conditional probability. In particular, $P$ has a
    finite first moment. -/)
  (title := /-- Compatibility -/)
  (latexEnv := "definition")]
def compatible {d : ℕ} (Pcl : propensity_class d) (Dcl : outcome_class d)
    (t : Bool) (p : (Fin d → ℝ) × ℝ → ℝ)
    (P : Measure ((Fin d → ℝ) × ℝ)) : Prop :=
  p ∈ Pcl ∧ P ∈ Dcl ∧
    ∃ D : observational_study d,
      realizable D Pcl Dcl ∧
        outcome_marginal D t = P ∧ induced_propensity D t =ᵐ[P] p

@[blueprint "def:identifiability-condition"
  (statement := /-- The concept classes $(\mathcal{P}, \mathcal{H})$
    (\cref{def:propensity-class}, \cref{def:outcome-class}) satisfy the
    Identifiability Condition if, for each treatment arm $t \in \{0,1\}$ and
    every pair of tuples $(p, P)$ and $(q, Q)$ compatible in that same arm
    (\cref{def:compatible}), at least one of the following holds: (i) equal
    outcome expectations,
    $\mathbb{E}_{(x,y) \sim P}[\,y\,] = \mathbb{E}_{(x,y) \sim Q}[\,y\,]$;
    (ii) distinct covariate marginals, $P_{X} \neq Q_{X}$, where $P_{X}$ is the
    pushforward of $P$ to its first coordinate; (iii) distinction under
    censoring, i.e. the reweighted measures $p \cdot P$ and $q \cdot Q$ differ,
    where $p \cdot P$ denotes the measure with density $p$ with respect to $P$.
    (Clause (iii) is modeled at the level of measures via densities, without the
    source's restriction of the witness to $\mathrm{supp}(P_{X}) \times
    \mathbb{R}$.) Compatibility supplies finite first moments
    (\cref{def:compatible}), so the expectations in clause (i) are genuine
    finite Bochner integrals. -/)
  (title := /-- Identifiability Condition -/)
  (latexEnv := "definition")]
def identifiability_condition {d : ℕ} (Pcl : propensity_class d) (Dcl : outcome_class d) :
    Prop :=
  ∀ (t : Bool) (p : (Fin d → ℝ) × ℝ → ℝ) (P : Measure ((Fin d → ℝ) × ℝ))
    (q : (Fin d → ℝ) × ℝ → ℝ) (Q : Measure ((Fin d → ℝ) × ℝ)),
    compatible Pcl Dcl t p P → compatible Pcl Dcl t q Q →
      (∫ z, z.2 ∂P) = (∫ z, z.2 ∂Q) ∨
        P.map Prod.fst ≠ Q.map Prod.fst ∨
        P.withDensity (fun z => ENNReal.ofReal (p z)) ≠
          Q.withDensity (fun z => ENNReal.ofReal (q z))

@[blueprint "def:ate-identifiable"
  (statement := /-- The average treatment effect is identifiable from the
    censored distribution with respect to the concept classes
    $(\mathcal{P}, \mathcal{H})$ (\cref{def:propensity-class},
    \cref{def:outcome-class}) if there exists a single mapping $f$ from censored
    distributions to real numbers such that $f(\mathcal{C}_{\mathcal{D}}) =
    \tau_{\mathcal{D}}$ for every observational study $\mathcal{D}$ realizable
    with respect to $(\mathcal{P}, \mathcal{H})$, where
    $\mathcal{C}_{\mathcal{D}}$ is the censored distribution
    (\cref{def:censored-distribution}), $\tau_{\mathcal{D}}$ is the average
    treatment effect (\cref{def:average-treatment-effect}), and realizability is
    as in \cref{def:realizable}. -/)
  (title := /-- Identifiability of the ATE -/)
  (latexEnv := "definition")]
def ate_identifiable {d : ℕ} (Pcl : propensity_class d) (Dcl : outcome_class d) : Prop :=
  ∃ f : Measure (observed_space d) → ℝ,
    ∀ D : observational_study d, realizable D Pcl Dcl →
      f (censored_distribution D) = average_treatment_effect D

@[blueprint "lem:ate-marginal-decomposition"
  (statement := /-- Fix a covariate dimension $d$, concept classes
    $(\mathcal{P},\mathcal{H})$, and an observational study $\mathcal{D}$
    realizable with respect to these classes (\cref{def:realizable}). Then
    \[
      \tau_{\mathcal{D}}
      =
      \int y\,d\mathcal{D}_{X,Y(1)}
      -
      \int y\,d\mathcal{D}_{X,Y(0)}.
    \]
    Here $\tau_{\mathcal{D}}$ is the average treatment effect
    (\cref{def:average-treatment-effect}) and the two measures on the
    right-hand side are the outcome marginals
    (\cref{def:outcome-marginal}). -/)
  (proof := /-- By realizability (\cref{def:realizable}), the second-coordinate
    map is integrable with respect to each outcome marginal. The coordinate
    projections defining the outcome marginals (\cref{def:outcome-marginal})
    are measurable. The change-of-variables formula for a pushforward measure
    therefore shows that the functions
    $(x,t,y_{0},y_{1})\mapsto y_{0}$ and
    $(x,t,y_{0},y_{1})\mapsto y_{1}$ are integrable with respect to
    $\mathcal{D}.\mathrm{law}$, and identifies their integrals with the two
    marginal integrals in the statement. Linearity of the Bochner integral for
    the difference of two integrable functions now gives the displayed
    identity after unfolding the definition of the average treatment effect
    (\cref{def:average-treatment-effect}). -/)
  (title := /-- Marginal Decomposition of the ATE -/)
  (latexEnv := "lemma")]
lemma ate_marginal_decomposition {d : ℕ} (D : observational_study d)
    (Pcl : propensity_class d) (Dcl : outcome_class d)
    (hD : realizable D Pcl Dcl) :
    average_treatment_effect D =
      (∫ z, z.2 ∂(outcome_marginal D true)) -
        ∫ z, z.2 ∂(outcome_marginal D false) := by
  rcases hD with ⟨_, _, _, _, h0, h1⟩
  have hm0 : Measurable (fun w : full_space d => (w.1, w.2.2.1)) := by
    fun_prop
  have hm1 : Measurable (fun w : full_space d => (w.1, w.2.2.2)) := by
    fun_prop
  have hy0 : Integrable (fun w : full_space d => w.2.2.1) D.law := by
    simpa [finite_first_moment, outcome_marginal, Function.comp_def] using
      h0.comp_aemeasurable hm0.aemeasurable
  have hy1 : Integrable (fun w : full_space d => w.2.2.2) D.law := by
    simpa [finite_first_moment, outcome_marginal, Function.comp_def] using
      h1.comp_aemeasurable hm1.aemeasurable
  have hi0 : (∫ z, z.2 ∂outcome_marginal D false) = ∫ w, w.2.2.1 ∂D.law := by
    simpa [outcome_marginal] using
      MeasureTheory.integral_map hm0.aemeasurable h0.aestronglyMeasurable
  have hi1 : (∫ z, z.2 ∂outcome_marginal D true) = ∫ w, w.2.2.2 ∂D.law := by
    simpa [outcome_marginal] using
      MeasureTheory.integral_map hm1.aemeasurable h1.aestronglyMeasurable
  rw [average_treatment_effect, integral_sub hy1 hy0, ← hi1, ← hi0]

@[blueprint "lem:condition-necessary-glue-potential-outcomes"
  (statement := /-- Fix a covariate dimension $d$ and two observational studies
    $\mathcal{D}_{0}$ and $\mathcal{D}_{1}$. If their joint laws of $(X,T)$
    coincide, then there exists an observational study $\mathcal{D}$ whose
    joint law of $(X,T,Y(0))$ equals that of $\mathcal{D}_{0}$ and whose joint
    law of $(X,T,Y(1))$ equals that of $\mathcal{D}_{1}$. -/)
  (proof := /-- Disintegrate the law of $(X,T,Y(0))$ under
    $\mathcal{D}_{0}$ and the law of $(X,T,Y(1))$ under $\mathcal{D}_{1}$ over
    their common $(X,T)$ marginal. At every value of $(X,T)$, take the product
    of the two resulting regular conditional distributions. Composing the
    common marginal with this product kernel gives a probability measure on
    $(X,T,Y(0),Y(1))$. The two marginal identities follow from the
    disintegration identities for the regular conditional distributions and
    the two projection identities for a product kernel. -/)
  (title := /-- Gluing Potential Outcomes over a Common Treatment Marginal -/)
  (latexEnv := "lemma")]
lemma condition_necessary_glue_potential_outcomes {d : ℕ}
    (D0 D1 : observational_study d)
    (hXT : D0.law.map (fun w : full_space d => (w.1, w.2.1)) =
      D1.law.map (fun w : full_space d => (w.1, w.2.1))) :
    ∃ D : observational_study d,
      D.law.map (fun w : full_space d => ((w.1, w.2.1), w.2.2.1)) =
        D0.law.map (fun w : full_space d => ((w.1, w.2.1), w.2.2.1)) ∧
      D.law.map (fun w : full_space d => ((w.1, w.2.1), w.2.2.2)) =
        D1.law.map (fun w : full_space d => ((w.1, w.2.1), w.2.2.2)) := by
  let XT := fun w : full_space d => (w.1, w.2.1)
  let Y0 := fun w : full_space d => w.2.2.1
  let Y1 := fun w : full_space d => w.2.2.2
  let μ := D0.law.map XT
  let κ0 := condDistrib Y0 XT D0.law
  let κ1 := condDistrib Y1 XT D1.law
  let ν := μ ⊗ₘ (κ0 ×ₖ κ1)
  let assemble := fun z : ((Fin d → ℝ) × Bool) × (ℝ × ℝ) =>
    (z.1.1, z.1.2, z.2.1, z.2.2)
  have hXTm : Measurable XT := by fun_prop
  have hY0m : Measurable Y0 := by fun_prop
  have hY1m : Measurable Y1 := by fun_prop
  have hassemblem : Measurable assemble := by fun_prop
  haveI hμ : IsProbabilityMeasure μ :=
    D0.law.isProbabilityMeasure_map hXTm.aemeasurable
  haveI hν : IsProbabilityMeasure ν := inferInstance
  let D : observational_study d :=
    { law := ν.map assemble
      isProb := Measure.isProbabilityMeasure_map hassemblem.aemeasurable }
  refine ⟨D, ?_, ?_⟩
  · dsimp [D]
    have hj0m : Measurable
        (fun w : full_space d => ((w.1, w.2.1), w.2.2.1)) := by
      fun_prop
    have hk0 : (κ0 ×ₖ κ1).map Prod.fst = κ0 := by
      rw [← Kernel.fst_eq]
      exact Kernel.fst_prod κ0 κ1
    calc
      (ν.map assemble).map
          (fun w : full_space d => ((w.1, w.2.1), w.2.2.1)) =
          ν.map ((fun w : full_space d => ((w.1, w.2.1), w.2.2.1)) ∘
            assemble) := Measure.map_map hj0m hassemblem
      _ = ν.map (Prod.map id Prod.fst) := by
        congr 1
      _ = μ ⊗ₘ ((κ0 ×ₖ κ1).map Prod.fst) := by
        simpa [ν] using
          (Measure.compProd_map (μ := μ) (κ := κ0 ×ₖ κ1)
            measurable_fst).symm
      _ = μ ⊗ₘ κ0 := by rw [hk0]
      _ = D0.law.map (fun w : full_space d => ((w.1, w.2.1), w.2.2.1)) := by
        simpa [μ, κ0, XT, Y0] using
          (compProd_map_condDistrib (μ := D0.law) (X := XT) (Y := Y0)
            hY0m.aemeasurable)
  · dsimp [D]
    have hj1m : Measurable
        (fun w : full_space d => ((w.1, w.2.1), w.2.2.2)) := by
      fun_prop
    have hk1 : (κ0 ×ₖ κ1).map Prod.snd = κ1 := by
      rw [← Kernel.snd_eq]
      exact Kernel.snd_prod κ0 κ1
    calc
      (ν.map assemble).map
          (fun w : full_space d => ((w.1, w.2.1), w.2.2.2)) =
          ν.map ((fun w : full_space d => ((w.1, w.2.1), w.2.2.2)) ∘
            assemble) := Measure.map_map hj1m hassemblem
      _ = ν.map (Prod.map id Prod.snd) := by
        congr 1
      _ = μ ⊗ₘ ((κ0 ×ₖ κ1).map Prod.snd) := by
        simpa [ν] using
          (Measure.compProd_map (μ := μ) (κ := κ0 ×ₖ κ1)
            measurable_snd).symm
      _ = μ ⊗ₘ κ1 := by rw [hk1]
      _ = D1.law.map (fun w : full_space d => ((w.1, w.2.1), w.2.2.2)) := by
        change (D0.law.map (fun w : full_space d => (w.1, w.2.1))) ⊗ₘ κ1 = _
        rw [hXT]
        simpa [κ1, XT, Y1] using
          (compProd_map_condDistrib (μ := D1.law) (X := XT) (Y := Y1)
            hY1m.aemeasurable)

@[blueprint "lem:condition-necessary-false-treatment-measure"
  (statement := /-- For an observational study $\mathcal{D}$ and every
    measurable covariate set $A$, the probability of $X\in A$ and $T=0$ equals
    the mass of $A$ under the covariate marginal of the measure obtained by
    weighting $\mathcal{D}_{X,Y(0)}$ by its induced propensity score $p_{0}$. -/)
  (proof := /-- Disintegrate the joint law of $((X,Y(0)),T)$ over the marginal
    law of $(X,Y(0))$. The disintegration identity identifies the probability
    of the rectangle $(A\times\mathbb{R})\times\{0\}$ with the integral over
    $A\times\mathbb{R}$ of the conditional mass of $\{0\}$. By the definitions
    of the induced propensity score and of a measure with density, this
    integral is precisely the asserted reweighted mass. -/)
  (title := /-- Reweighted Outcome Law of the Untreated Arm -/)
  (latexEnv := "lemma")]
lemma condition_necessary_false_treatment_measure {d : ℕ}
    (D : observational_study d) (s : Set (Fin d → ℝ)) (hs : MeasurableSet s) :
    (D.law.map (fun w : full_space d => (w.1, w.2.1))) (s ×ˢ {false}) =
      ((outcome_marginal D false).withDensity
        (fun z => ENNReal.ofReal (induced_propensity D false z))).map Prod.fst s := by
  let Z := fun w : full_space d => (w.1, w.2.2.1)
  let T := fun w : full_space d => w.2.1
  have hZm : Measurable Z := by fun_prop
  have hTm : Measurable T := by fun_prop
  have hXTm : Measurable (fun w : full_space d => (w.1, w.2.1)) := by
    fun_prop
  have hrect : MeasurableSet
      (((fun z : (Fin d → ℝ) × ℝ => z.1) ⁻¹' s) ×ˢ ({false} : Set Bool)) :=
    (hs.preimage (by fun_prop)).prod (MeasurableSet.singleton false)
  calc
    (D.law.map (fun w : full_space d => (w.1, w.2.1))) (s ×ˢ {false}) =
        D.law ((fun w : full_space d => (w.1, w.2.1)) ⁻¹' (s ×ˢ {false})) :=
      Measure.map_apply hXTm (hs.prod (MeasurableSet.singleton false))
    _ = (D.law.map (fun w : full_space d => (Z w, T w)))
        (((fun z : (Fin d → ℝ) × ℝ => z.1) ⁻¹' s) ×ˢ {false}) := by
      rw [Measure.map_apply (hZm.prod hTm) hrect]
      congr 1
    _ = ((D.law.map Z) ⊗ₘ condDistrib T Z D.law)
        (((fun z : (Fin d → ℝ) × ℝ => z.1) ⁻¹' s) ×ˢ {false}) := by
      rw [compProd_map_condDistrib hTm.aemeasurable]
    _ = ∫⁻ z in (fun z : (Fin d → ℝ) × ℝ => z.1) ⁻¹' s,
        condDistrib T Z D.law z {false} ∂D.law.map Z := by
      rw [Measure.compProd_apply_prod (hs.preimage (by fun_prop))
        (MeasurableSet.singleton false)]
    _ = ∫⁻ z in (fun z : (Fin d → ℝ) × ℝ => z.1) ⁻¹' s,
        ENNReal.ofReal ((condDistrib T Z D.law z {false}).toReal) ∂D.law.map Z := by
      congr 1
      funext z
      rw [ENNReal.ofReal_toReal]
      exact measure_ne_top _ _
    _ = ((outcome_marginal D false).withDensity
        (fun z => ENNReal.ofReal (induced_propensity D false z)))
          ((fun z : (Fin d → ℝ) × ℝ => z.1) ⁻¹' s) := by
      simp only [outcome_marginal, induced_propensity, Bool.false_eq_true,
        ↓reduceIte]
      simpa [Z, T] using
        (withDensity_apply (μ := D.law.map Z)
          (fun z => ENNReal.ofReal ((condDistrib T Z D.law z {false}).toReal))
          (hs.preimage (by fun_prop))).symm
    _ = ((outcome_marginal D false).withDensity
        (fun z => ENNReal.ofReal (induced_propensity D false z))).map Prod.fst s := by
      rw [Measure.map_apply measurable_fst hs]

@[blueprint "lem:condition-necessary-same-treatment-marginal"
  (statement := /-- Let $\mathcal{D}_{0}$ and $\mathcal{D}_{1}$ be
    observational studies. Suppose that their $X$-marginals induced by
    $\mathcal{D}_{X,Y(0)}$ coincide and that their propensity-reweighted laws
    of $(X,Y(0))$ coincide. Then the joint laws of $(X,T)$ under the two
    studies coincide. -/)
  (proof := /-- By
    \cref{lem:condition-necessary-false-treatment-measure}, equality of the
    reweighted laws gives equality of the probabilities of
    $\{X\in A,T=0\}$ for every measurable covariate set $A$. Equality of the
    covariate marginals gives equality on $A\times\{0,1\}$. Finite additivity
    and cancellation therefore give equality on $A\times\{1\}$ as well. The
    four subsets of the Boolean treatment space are
    $\varnothing,\{0\},\{1\},\{0,1\}$, so equality on measurable rectangles
    proves equality of the two finite product-space measures. -/)
  (title := /-- Equality of Covariate--Treatment Marginals -/)
  (latexEnv := "lemma")]
lemma condition_necessary_same_treatment_marginal {d : ℕ}
    (D0 D1 : observational_study d)
    (hX : (outcome_marginal D0 false).map Prod.fst =
      (outcome_marginal D1 false).map Prod.fst)
    (hfalse : (outcome_marginal D0 false).withDensity
        (fun z => ENNReal.ofReal (induced_propensity D0 false z)) =
      (outcome_marginal D1 false).withDensity
        (fun z => ENNReal.ofReal (induced_propensity D1 false z))) :
    D0.law.map (fun w : full_space d => (w.1, w.2.1)) =
      D1.law.map (fun w : full_space d => (w.1, w.2.1)) := by
  let J0 := D0.law.map (fun w : full_space d => (w.1, w.2.1))
  let J1 := D1.law.map (fun w : full_space d => (w.1, w.2.1))
  have hJ0 : IsFiniteMeasure J0 := by infer_instance
  apply Measure.ext_prod
  intro s t hs ht
  have htotal : J0 (s ×ˢ Set.univ) = J1 (s ×ˢ Set.univ) := by
    have hm0 : J0.map Prod.fst = (outcome_marginal D0 false).map Prod.fst := by
      rw [Measure.map_map measurable_fst (by fun_prop)]
      simp only [outcome_marginal, Bool.false_eq_true, ↓reduceIte]
      rw [Measure.map_map measurable_fst (by fun_prop)]
      rfl
    have hm1 : J1.map Prod.fst = (outcome_marginal D1 false).map Prod.fst := by
      rw [Measure.map_map measurable_fst (by fun_prop)]
      simp only [outcome_marginal, Bool.false_eq_true, ↓reduceIte]
      rw [Measure.map_map measurable_fst (by fun_prop)]
      rfl
    calc
      J0 (s ×ˢ Set.univ) = J0.map Prod.fst s := by
        rw [Measure.map_apply measurable_fst hs]
        congr 1
        ext z
        simp
      _ = (outcome_marginal D0 false).map Prod.fst s := by rw [hm0]
      _ = (outcome_marginal D1 false).map Prod.fst s := by rw [hX]
      _ = J1.map Prod.fst s := by rw [hm1]
      _ = J1 (s ×ˢ Set.univ) := by
        rw [Measure.map_apply measurable_fst hs]
        congr 1
        ext z
        simp
  have hzero : J0 (s ×ˢ {false}) = J1 (s ×ˢ {false}) := by
    calc
      J0 (s ×ˢ {false}) =
          ((outcome_marginal D0 false).withDensity
            (fun z => ENNReal.ofReal (induced_propensity D0 false z))).map
              Prod.fst s := condition_necessary_false_treatment_measure D0 s hs
      _ = ((outcome_marginal D1 false).withDensity
            (fun z => ENNReal.ofReal (induced_propensity D1 false z))).map
              Prod.fst s := by rw [hfalse]
      _ = J1 (s ×ˢ {false}) :=
        (condition_necessary_false_treatment_measure D1 s hs).symm
  have hsplit (J : Measure ((Fin d → ℝ) × Bool)) :
      J (s ×ˢ Set.univ) = J (s ×ˢ {false}) + J (s ×ˢ {true}) := by
    rw [← measure_union]
    · congr 1
      ext z
      rcases z with ⟨x, b⟩
      cases b <;> simp
    · simp
    · exact (hs.prod (MeasurableSet.singleton true))
  by_cases hf : false ∈ t
  · by_cases ht' : true ∈ t
    · have htuniv : t = Set.univ := by
        ext b
        cases b <;> simp [hf, ht']
      subst t
      exact htotal
    · have htfalse : t = {false} := by
        ext b
        cases b <;> simp [hf, ht']
      subst t
      exact hzero
  · by_cases ht' : true ∈ t
    · have httrue : t = {true} := by
        ext b
        cases b <;> simp [hf, ht']
      subst t
      have hadd : J0 (s ×ˢ {false}) + J0 (s ×ˢ {true}) =
          J1 (s ×ˢ {false}) + J1 (s ×ˢ {true}) := by
        rw [← hsplit J0, ← hsplit J1, htotal]
      rw [hzero] at hadd
      exact (ENNReal.add_right_inj (measure_ne_top J1 (s ×ˢ {false}))).mp hadd
    · have htempty : t = ∅ := by
        ext b
        cases b <;> simp [hf, ht']
      subst t
      simp

@[blueprint "lem:condition-necessary-observed-arm-measure"
  (statement := /-- For an observational study $\mathcal{D}$ and treatment arm
    $t\in\{0,1\}$, weighting the outcome marginal
    $\mathcal{D}_{X,Y(t)}$ by the induced propensity score $p_t$ gives the
    subprobability law of $(X,Y(t))$ on the event $T=t$. -/)
  (proof := /-- Disintegrate the joint law of $((X,Y(t)),T)$ over
    $\mathcal{D}_{X,Y(t)}$. On every measurable set $A$, the composition-product
    formula identifies the mass of $A\times\{t\}$ with the integral over $A$
    of the conditional probability of $T=t$. The latter conditional
    probability is the induced propensity score by definition. The defining
    formulas for restriction, pushforward, and density then identify this mass
    with the pushforward of the law restricted to $\{T=t\}$. -/)
  (title := /-- Propensity Weighting Recovers an Observed Arm -/)
  (latexEnv := "lemma")]
lemma condition_necessary_observed_arm_measure {d : ℕ}
    (D : observational_study d) (t : Bool) :
    (outcome_marginal D t).withDensity
        (fun z => ENNReal.ofReal (induced_propensity D t z)) =
      (D.law.restrict {w : full_space d | w.2.1 = t}).map
        (fun w : full_space d =>
          (w.1, if t then w.2.2.2 else w.2.2.1)) := by
  let Z := fun w : full_space d =>
    (w.1, if t then w.2.2.2 else w.2.2.1)
  let T := fun w : full_space d => w.2.1
  have hZm : Measurable Z := by
    cases t <;> simp [Z] <;> fun_prop
  have hTm : Measurable T := by fun_prop
  ext s hs
  calc
    ((outcome_marginal D t).withDensity
        (fun z => ENNReal.ofReal (induced_propensity D t z))) s =
        ∫⁻ z in s, ENNReal.ofReal ((condDistrib T Z D.law z {t}).toReal)
          ∂D.law.map Z := by
      simp only [outcome_marginal, induced_propensity]
      simpa [Z, T] using
        (withDensity_apply (μ := D.law.map Z)
          (fun z => ENNReal.ofReal ((condDistrib T Z D.law z {t}).toReal)) hs)
    _ = ∫⁻ z in s, condDistrib T Z D.law z {t} ∂D.law.map Z := by
      congr 1
      funext z
      rw [ENNReal.ofReal_toReal]
      exact measure_ne_top _ _
    _ = ((D.law.map Z) ⊗ₘ condDistrib T Z D.law) (s ×ˢ {t}) := by
      rw [Measure.compProd_apply_prod hs (MeasurableSet.singleton t)]
    _ = (D.law.map (fun w : full_space d => (Z w, T w))) (s ×ˢ {t}) := by
      rw [compProd_map_condDistrib hTm.aemeasurable]
    _ = D.law ((fun w : full_space d => (Z w, T w)) ⁻¹' (s ×ˢ {t})) := by
      rw [Measure.map_apply (hZm.prod hTm)
        (hs.prod (MeasurableSet.singleton t))]
    _ = (D.law.restrict {w : full_space d | w.2.1 = t}) (Z ⁻¹' s) := by
      rw [Measure.restrict_apply (hZm hs)]
      congr 1
    _ = ((D.law.restrict {w : full_space d | w.2.1 = t}).map Z) s := by
      rw [Measure.map_apply hZm hs]

@[blueprint "lem:condition-necessary-censored-decomposition"
  (statement := /-- The censored distribution of an observational study is the
    sum of two subprobability measures: the propensity-weighted law of
    $(X,Y(0))$, embedded with treatment label $0$, and the
    propensity-weighted law of $(X,Y(1))$, embedded with treatment label $1$. -/)
  (proof := /-- Apply
    \cref{lem:condition-necessary-observed-arm-measure} to each treatment arm.
    After embedding the arm law into the censored outcome space, its
    pushforward agrees with the censoring map on the corresponding measurable
    event $\{T=t\}$. The events $\{T=0\}$ and $\{T=1\}$ partition the complete
    outcome space. Additivity of restriction and pushforward therefore gives
    the asserted decomposition. -/)
  (title := /-- Decomposition of the Censored Distribution by Treatment Arm -/)
  (latexEnv := "lemma")]
lemma condition_necessary_censored_decomposition {d : ℕ}
    (D : observational_study d) :
    censored_distribution D =
      ((outcome_marginal D false).withDensity
        (fun z => ENNReal.ofReal (induced_propensity D false z))).map
          (fun z => (z.1, false, z.2)) +
      ((outcome_marginal D true).withDensity
        (fun z => ENNReal.ofReal (induced_propensity D true z))).map
          (fun z => (z.1, true, z.2)) := by
  have harm (t : Bool) :
      ((outcome_marginal D t).withDensity
        (fun z => ENNReal.ofReal (induced_propensity D t z))).map
          (fun z => (z.1, t, z.2)) =
      (D.law.restrict {w : full_space d | w.2.1 = t}).map
        (censoring_map d) := by
    rw [condition_necessary_observed_arm_measure]
    have hZm : Measurable (fun w : full_space d =>
        (w.1, if t then w.2.2.2 else w.2.2.1)) := by
      cases t <;> simp <;> fun_prop
    have hem : Measurable (fun z : (Fin d → ℝ) × ℝ => (z.1, t, z.2)) := by
      fun_prop
    rw [Measure.map_map hem hZm]
    apply Measure.map_congr
    have hEt : MeasurableSet {w : full_space d | w.2.1 = t} := by
      exact (MeasurableSet.singleton t).preimage (by fun_prop)
    filter_upwards [ae_restrict_mem hEt] with w hw
    cases t <;> simp [censoring_map] at hw ⊢ <;> simp [hw]
  have hEfalse : MeasurableSet {w : full_space d | w.2.1 = false} := by
    exact (MeasurableSet.singleton false).preimage (by fun_prop)
  have hparts :
      D.law.restrict {w : full_space d | w.2.1 = false} +
        D.law.restrict {w : full_space d | w.2.1 = true} = D.law := by
    have hcompl : {w : full_space d | w.2.1 = false}ᶜ =
        {w : full_space d | w.2.1 = true} := by
      ext w
      cases w.2.1 <;> simp
    rw [← hcompl]
    exact Measure.restrict_add_restrict_compl hEfalse
  rw [censored_distribution, ← hparts, Measure.map_add]
  · rw [← harm false, ← harm true]
  · unfold censoring_map
    have hx : Measurable (fun w : full_space d => w.1) := by fun_prop
    have ht : Measurable (fun w : full_space d => w.2.1) := by fun_prop
    have hy : Measurable (fun w : full_space d =>
        if w.2.1 then w.2.2.2 else w.2.2.1) :=
      Measurable.ite ((MeasurableSet.singleton true).preimage ht)
        (by fun_prop) (by fun_prop)
    fun_prop

@[blueprint "lem:condition-necessary-arm-data-of-joint-eq"
  (statement := /-- Let $\mathcal{D}_{0}$ and $\mathcal{D}_{1}$ be
    observational studies and let $t\in\{0,1\}$. If the joint laws of
    $(X,T,Y(t))$ under the two studies agree, then their induced propensity
    scores for arm $t$ and their outcome marginals for arm $t$ agree. -/)
  (proof := /-- Push the common law of $(X,T,Y(t))$ forward by the coordinate
    permutation $((X,T),Y(t))\mapsto((X,Y(t)),T)$. This gives equality of the
    joint measures from which the regular conditional distributions defining
    the two induced propensity scores are constructed. Pushing forward instead
    by $((X,T),Y(t))\mapsto(X,Y(t))$ gives equality of the outcome marginals. -/)
  (title := /-- Arm Data Are Determined by the Joint Treatment--Outcome Law -/)
  (latexEnv := "lemma")]
lemma condition_necessary_arm_data_of_joint_eq {d : ℕ}
    (D0 D1 : observational_study d) (t : Bool)
    (hjoint :
      D0.law.map (fun w : full_space d =>
        ((w.1, w.2.1), if t then w.2.2.2 else w.2.2.1)) =
      D1.law.map (fun w : full_space d =>
        ((w.1, w.2.1), if t then w.2.2.2 else w.2.2.1))) :
    induced_propensity D0 t = induced_propensity D1 t ∧
      outcome_marginal D0 t = outcome_marginal D1 t := by
  let J := fun w : full_space d =>
    ((w.1, w.2.1), if t then w.2.2.2 else w.2.2.1)
  have hJm : Measurable J := by
    cases t <;> simp [J] <;> fun_prop
  have hcondlaw :
      D0.law.map (fun w : full_space d =>
        ((w.1, if t then w.2.2.2 else w.2.2.1), w.2.1)) =
      D1.law.map (fun w : full_space d =>
        ((w.1, if t then w.2.2.2 else w.2.2.1), w.2.1)) := by
    calc
      D0.law.map (fun w : full_space d =>
          ((w.1, if t then w.2.2.2 else w.2.2.1), w.2.1)) =
          (D0.law.map J).map
            (fun z => ((z.1.1, z.2), z.1.2)) := by
        rw [Measure.map_map (by fun_prop) hJm]
        rfl
      _ = (D1.law.map J).map
            (fun z => ((z.1.1, z.2), z.1.2)) := by
        rw [hjoint]
      _ = D1.law.map (fun w : full_space d =>
          ((w.1, if t then w.2.2.2 else w.2.2.1), w.2.1)) := by
        rw [Measure.map_map (by fun_prop) hJm]
        rfl
  constructor
  · unfold induced_propensity
    funext z
    rw [condDistrib, condDistrib]
    simpa only [hcondlaw]
  · unfold outcome_marginal
    calc
      D0.law.map (fun w : full_space d =>
          (w.1, if t then w.2.2.2 else w.2.2.1)) =
          (D0.law.map J).map (fun z => (z.1.1, z.2)) := by
        rw [Measure.map_map (by fun_prop) hJm]
        rfl
      _ = (D1.law.map J).map (fun z => (z.1.1, z.2)) := by
        rw [hjoint]
      _ = D1.law.map (fun w : full_space d =>
          (w.1, if t then w.2.2.2 else w.2.2.1)) := by
        rw [Measure.map_map (by fun_prop) hJm]
        rfl

@[blueprint "lem:condition-necessary-treatment-measure"
  (statement := /-- For an observational study $\mathcal{D}$, a treatment arm
    $t\in\{0,1\}$, and every measurable covariate set $A$, the probability
    of $X\in A$ and $T=t$ is the mass of $A$ under the covariate marginal of
    the measure obtained by weighting $\mathcal{D}_{X,Y(t)}$ by its induced
    propensity score $p_t$. -/)
  (proof := /-- Disintegrate the joint law of $((X,Y(t)),T)$ over the outcome
    marginal \cref{def:outcome-marginal}. The composition-product identity
    expresses the mass of the rectangle
    $(A\times\mathbb{R})\times\{t\}$ as the integral over
    $A\times\mathbb{R}$ of the conditional mass of $\{t\}$. By
    \cref{def:induced-propensity}, this conditional mass is $p_t$, and the
    definitions of density and pushforward identify the integral with the
    asserted reweighted covariate mass. -/)
  (title := /-- Reweighted Outcome Law of a Selected Treatment Arm -/)
  (latexEnv := "lemma")]
lemma condition_necessary_treatment_measure {d : ℕ}
    (D : observational_study d) (t : Bool)
    (s : Set (Fin d → ℝ)) (hs : MeasurableSet s) :
    (D.law.map (fun w : full_space d => (w.1, w.2.1))) (s ×ˢ {t}) =
      ((outcome_marginal D t).withDensity
        (fun z => ENNReal.ofReal (induced_propensity D t z))).map Prod.fst s := by
  let Z := fun w : full_space d =>
    (w.1, if t then w.2.2.2 else w.2.2.1)
  let T := fun w : full_space d => w.2.1
  have hZm : Measurable Z := by
    cases t <;> simp [Z] <;> fun_prop
  have hTm : Measurable T := by fun_prop
  have hXTm : Measurable (fun w : full_space d => (w.1, w.2.1)) := by
    fun_prop
  have hrect : MeasurableSet
      (((fun z : (Fin d → ℝ) × ℝ => z.1) ⁻¹' s) ×ˢ ({t} : Set Bool)) :=
    (hs.preimage (by fun_prop)).prod (MeasurableSet.singleton t)
  calc
    (D.law.map (fun w : full_space d => (w.1, w.2.1))) (s ×ˢ {t}) =
        D.law ((fun w : full_space d => (w.1, w.2.1)) ⁻¹' (s ×ˢ {t})) :=
      Measure.map_apply hXTm (hs.prod (MeasurableSet.singleton t))
    _ = (D.law.map (fun w : full_space d => (Z w, T w)))
        (((fun z : (Fin d → ℝ) × ℝ => z.1) ⁻¹' s) ×ˢ {t}) := by
      rw [Measure.map_apply (hZm.prod hTm) hrect]
      congr 1
    _ = ((D.law.map Z) ⊗ₘ condDistrib T Z D.law)
        (((fun z : (Fin d → ℝ) × ℝ => z.1) ⁻¹' s) ×ˢ {t}) := by
      rw [compProd_map_condDistrib hTm.aemeasurable]
    _ = ∫⁻ z in (fun z : (Fin d → ℝ) × ℝ => z.1) ⁻¹' s,
        condDistrib T Z D.law z {t} ∂D.law.map Z := by
      rw [Measure.compProd_apply_prod (hs.preimage (by fun_prop))
        (MeasurableSet.singleton t)]
    _ = ∫⁻ z in (fun z : (Fin d → ℝ) × ℝ => z.1) ⁻¹' s,
        ENNReal.ofReal ((condDistrib T Z D.law z {t}).toReal) ∂D.law.map Z := by
      congr 1
      funext z
      rw [ENNReal.ofReal_toReal]
      exact measure_ne_top _ _
    _ = ((outcome_marginal D t).withDensity
        (fun z => ENNReal.ofReal (induced_propensity D t z)))
          ((fun z : (Fin d → ℝ) × ℝ => z.1) ⁻¹' s) := by
      simp only [outcome_marginal, induced_propensity]
      simpa [Z, T] using
        (withDensity_apply (μ := D.law.map Z)
          (fun z => ENNReal.ofReal ((condDistrib T Z D.law z {t}).toReal))
          (hs.preimage (by fun_prop))).symm
    _ = ((outcome_marginal D t).withDensity
        (fun z => ENNReal.ofReal (induced_propensity D t z))).map Prod.fst s := by
      rw [Measure.map_apply measurable_fst hs]

@[blueprint "lem:condition-necessary-same-treatment-marginal-true"
  (statement := /-- Let $\mathcal{D}_{0}$ and $\mathcal{D}_{1}$ be
    observational studies. If the covariate marginals induced by
    $\mathcal{D}_{X,Y(1)}$ coincide and the propensity-reweighted laws of
    $(X,Y(1))$ coincide, then the joint laws of $(X,T)$ under the two studies
    coincide. -/)
  (proof := /-- By
    \cref{lem:condition-necessary-treatment-measure}, equality of the
    reweighted laws gives equality of the probabilities of
    $\{X\in A,T=1\}$ for every measurable covariate set $A$. Equality of
    the covariate marginals gives equality on $A\times\{0,1\}$. Finite
    additivity and cancellation yield equality on $A\times\{0\}$.
    Equality on the four measurable subsets of the Boolean treatment space
    then proves equality of the two product-space measures. -/)
  (title := /-- Equality of Covariate--Treatment Marginals from the Treated Arm -/)
  (latexEnv := "lemma")]
lemma condition_necessary_same_treatment_marginal_true {d : ℕ}
    (D0 D1 : observational_study d)
    (hX : (outcome_marginal D0 true).map Prod.fst =
      (outcome_marginal D1 true).map Prod.fst)
    (htrue : (outcome_marginal D0 true).withDensity
        (fun z => ENNReal.ofReal (induced_propensity D0 true z)) =
      (outcome_marginal D1 true).withDensity
        (fun z => ENNReal.ofReal (induced_propensity D1 true z))) :
    D0.law.map (fun w : full_space d => (w.1, w.2.1)) =
      D1.law.map (fun w : full_space d => (w.1, w.2.1)) := by
  let J0 := D0.law.map (fun w : full_space d => (w.1, w.2.1))
  let J1 := D1.law.map (fun w : full_space d => (w.1, w.2.1))
  have hJ0 : IsFiniteMeasure J0 := by infer_instance
  apply Measure.ext_prod
  intro s u hs hu
  have htotal : J0 (s ×ˢ Set.univ) = J1 (s ×ˢ Set.univ) := by
    have hm0 : J0.map Prod.fst = (outcome_marginal D0 true).map Prod.fst := by
      rw [Measure.map_map measurable_fst (by fun_prop)]
      simp only [outcome_marginal, ↓reduceIte]
      rw [Measure.map_map measurable_fst (by fun_prop)]
      rfl
    have hm1 : J1.map Prod.fst = (outcome_marginal D1 true).map Prod.fst := by
      rw [Measure.map_map measurable_fst (by fun_prop)]
      simp only [outcome_marginal, ↓reduceIte]
      rw [Measure.map_map measurable_fst (by fun_prop)]
      rfl
    calc
      J0 (s ×ˢ Set.univ) = J0.map Prod.fst s := by
        rw [Measure.map_apply measurable_fst hs]
        congr 1
        ext z
        simp
      _ = (outcome_marginal D0 true).map Prod.fst s := by rw [hm0]
      _ = (outcome_marginal D1 true).map Prod.fst s := by rw [hX]
      _ = J1.map Prod.fst s := by rw [hm1]
      _ = J1 (s ×ˢ Set.univ) := by
        rw [Measure.map_apply measurable_fst hs]
        congr 1
        ext z
        simp
  have hone : J0 (s ×ˢ {true}) = J1 (s ×ˢ {true}) := by
    calc
      J0 (s ×ˢ {true}) =
          ((outcome_marginal D0 true).withDensity
            (fun z => ENNReal.ofReal (induced_propensity D0 true z))).map
              Prod.fst s := condition_necessary_treatment_measure D0 true s hs
      _ = ((outcome_marginal D1 true).withDensity
            (fun z => ENNReal.ofReal (induced_propensity D1 true z))).map
              Prod.fst s := by rw [htrue]
      _ = J1 (s ×ˢ {true}) :=
        (condition_necessary_treatment_measure D1 true s hs).symm
  have hsplit (J : Measure ((Fin d → ℝ) × Bool)) :
      J (s ×ˢ Set.univ) = J (s ×ˢ {false}) + J (s ×ˢ {true}) := by
    rw [← measure_union]
    · congr 1
      ext z
      rcases z with ⟨x, b⟩
      cases b <;> simp
    · simp
    · exact hs.prod (MeasurableSet.singleton true)
  by_cases hf : false ∈ u
  · by_cases ht : true ∈ u
    · have hu' : u = Set.univ := by
        ext b
        cases b <;> simp [hf, ht]
      subst u
      exact htotal
    · have hu' : u = {false} := by
        ext b
        cases b <;> simp [hf, ht]
      subst u
      have hadd : J0 (s ×ˢ {false}) + J0 (s ×ˢ {true}) =
          J1 (s ×ˢ {false}) + J1 (s ×ˢ {true}) := by
        rw [← hsplit J0, ← hsplit J1, htotal]
      rw [hone] at hadd
      exact (ENNReal.add_left_inj
        (measure_ne_top J1 (s ×ˢ {true}))).mp hadd
  · by_cases ht : true ∈ u
    · have hu' : u = {true} := by
        ext b
        cases b <;> simp [hf, ht]
      subst u
      exact hone
    · have hu' : u = ∅ := by
        ext b
        cases b <;> simp [hf, ht]
      subst u
      simp

@[blueprint "lem:condition-necessary"
  (statement := /-- Necessity. Fix a covariate dimension $d$ and concept classes
    $(\mathcal{P}, \mathcal{H})$ (\cref{def:propensity-class},
    \cref{def:outcome-class}). If the average treatment effect is identifiable
    from the censored distribution with respect to $(\mathcal{P}, \mathcal{H})$
    (\cref{def:ate-identifiable}), then $(\mathcal{P}, \mathcal{H})$ satisfy the
    Identifiability Condition (\cref{def:identifiability-condition}). -/)
  (proof := /-- Let $f$ witness identifiability
    (\cref{def:ate-identifiable}). Fix an arm $t \in \{0,1\}$ and two tuples
    $(p,P)$ and $(q,Q)$ compatible in that arm (\cref{def:compatible}), and
    choose corresponding realizable studies $\mathcal{D}_{P}$ and
    $\mathcal{D}_{Q}$. Suppose that all three alternatives in the
    Identifiability Condition (\cref{def:identifiability-condition}) fail.
    Then the expectations under $P$ and $Q$ differ, their covariate marginals
    agree, and the reweighted measures $p\cdot P$ and $q\cdot Q$ agree. The
    almost-everywhere propensity equalities in compatibility allow $p$ and
    $q$ to be replaced by the induced propensity scores inside these
    reweighted measures. Consequently the selected-arm reweighted outcome
    measures of $\mathcal{D}_{P}$ and $\mathcal{D}_{Q}$ agree. Together with
    equality of the covariate marginals, this implies equality of their laws
    of $(X,T)$: for $t=0$ this is
    \cref{lem:condition-necessary-same-treatment-marginal}; for $t=1$, the
    same conclusion follows by
    \cref{lem:condition-necessary-same-treatment-marginal-true}, which first
    identifies the measures of
    $A\times\{1\}$ for every measurable covariate set $A$ and then subtracting
    from the common measure of $A\times\{0,1\}$ to identify
    $A\times\{0\}$. The measurable rectangles generate the product
    $\sigma$-algebra.

    Apply \cref{lem:condition-necessary-glue-potential-outcomes}. If $t=0$,
    form a study $\mathcal{E}$ whose $(X,T,Y(0))$ law comes from
    $\mathcal{D}_{Q}$ and whose $(X,T,Y(1))$ law comes from
    $\mathcal{D}_{P}$; if $t=1$, use $\mathcal{D}_{P}$ for the first law and
    $\mathcal{D}_{Q}$ for the second. By
    \cref{lem:condition-necessary-arm-data-of-joint-eq}, the propensity score,
    outcome marginal, and finite-moment data of each arm transfer from the
    corresponding completing study, so $\mathcal{E}$ is realizable.
    The decomposition
    \cref{lem:condition-necessary-censored-decomposition} shows that
    $\mathcal{E}$ and $\mathcal{D}_{P}$ have the same censored distribution:
    the unchanged arm contributes the same term, while the selected-arm terms
    agree by $p\cdot P=q\cdot Q$. Identifiability therefore gives equal average
    treatment effects. Finally,
    \cref{lem:ate-marginal-decomposition} expresses both effects as the common
    expectation of the unchanged arm together with, respectively, the
    expectations under $P$ and $Q$ in the selected arm. The selected
    expectation enters with sign $-1$ when $t=0$ and sign $+1$ when $t=1$;
    in either case equality of effects contradicts the assumed inequality of
    those expectations. Hence one of the three alternatives holds for every
    same-arm compatible pair. -/)
  (title := /-- Necessity of the Identifiability Condition -/)
  (latexEnv := "lemma")]
lemma condition_necessary {d : ℕ} (Pcl : propensity_class d) (Dcl : outcome_class d)
    (h : ate_identifiable Pcl Dcl) : identifiability_condition Pcl Dcl := by
  rcases h with ⟨f, hf⟩
  intro t p P q Q hp hq
  by_cases hmean : (∫ z, z.2 ∂P) = ∫ z, z.2 ∂Q
  · exact Or.inl hmean
  · right
    by_cases hX : P.map Prod.fst = Q.map Prod.fst
    · right
      by_contra hweight
      have hweight' :
          P.withDensity (fun z => ENNReal.ofReal (p z)) =
            Q.withDensity (fun z => ENNReal.ofReal (q z)) := hweight
      rcases hp with ⟨_, _, DP, hDP, hDPm, hDPae⟩
      rcases hq with ⟨_, _, DQ, hDQ, hDQm, hDQae⟩
      have hDPdensity :
          (outcome_marginal DP t).withDensity
              (fun z => ENNReal.ofReal (induced_propensity DP t z)) =
            P.withDensity (fun z => ENNReal.ofReal (p z)) := by
        rw [hDPm]
        apply withDensity_congr_ae
        filter_upwards [hDPae] with z hz
        rw [hz]
      have hDQdensity :
          (outcome_marginal DQ t).withDensity
              (fun z => ENNReal.ofReal (induced_propensity DQ t z)) =
            Q.withDensity (fun z => ENNReal.ofReal (q z)) := by
        rw [hDQm]
        apply withDensity_congr_ae
        filter_upwards [hDQae] with z hz
        rw [hz]
      have hselected :
          (outcome_marginal DP t).withDensity
              (fun z => ENNReal.ofReal (induced_propensity DP t z)) =
            (outcome_marginal DQ t).withDensity
              (fun z => ENNReal.ofReal (induced_propensity DQ t z)) := by
        rw [hDPdensity, hDQdensity, hweight']
      have hXmarginal :
          (outcome_marginal DP t).map Prod.fst =
            (outcome_marginal DQ t).map Prod.fst := by
        rw [hDPm, hDQm, hX]
      have hXT :
          DP.law.map (fun w : full_space d => (w.1, w.2.1)) =
            DQ.law.map (fun w : full_space d => (w.1, w.2.1)) := by
        cases t
        · exact condition_necessary_same_treatment_marginal
            DP DQ hXmarginal hselected
        · exact condition_necessary_same_treatment_marginal_true
            DP DQ hXmarginal hselected
      cases t
      · rcases condition_necessary_glue_potential_outcomes DQ DP hXT.symm with
          ⟨E, hE0, hE1⟩
        have hE0data :=
          condition_necessary_arm_data_of_joint_eq E DQ false hE0
        have hE1data :=
          condition_necessary_arm_data_of_joint_eq E DP true hE1
        have hEreal : realizable E Pcl Dcl := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hE0data.1]
            exact hDQ.1
          · rw [hE1data.1]
            exact hDP.2.1
          · rw [hE0data.2]
            exact hDQ.2.2.1
          · rw [hE1data.2]
            exact hDP.2.2.2.1
          · rw [hE0data.2]
            exact hDQ.2.2.2.2.1
          · rw [hE1data.2]
            exact hDP.2.2.2.2.2
        have hcensored :
            censored_distribution E = censored_distribution DP := by
          rw [condition_necessary_censored_decomposition E,
            condition_necessary_censored_decomposition DP,
            hE0data.1, hE0data.2, hE1data.1, hE1data.2, ← hselected]
        have hATE :
            average_treatment_effect E = average_treatment_effect DP := by
          calc
            average_treatment_effect E = f (censored_distribution E) :=
              (hf E hEreal).symm
            _ = f (censored_distribution DP) := by rw [hcensored]
            _ = average_treatment_effect DP := hf DP hDP
        rw [ate_marginal_decomposition E Pcl Dcl hEreal,
          ate_marginal_decomposition DP Pcl Dcl hDP,
          hE0data.2, hE1data.2, hDPm, hDQm] at hATE
        apply hmean
        linarith
      · rcases condition_necessary_glue_potential_outcomes DP DQ hXT with
          ⟨E, hE0, hE1⟩
        have hE0data :=
          condition_necessary_arm_data_of_joint_eq E DP false hE0
        have hE1data :=
          condition_necessary_arm_data_of_joint_eq E DQ true hE1
        have hEreal : realizable E Pcl Dcl := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hE0data.1]
            exact hDP.1
          · rw [hE1data.1]
            exact hDQ.2.1
          · rw [hE0data.2]
            exact hDP.2.2.1
          · rw [hE1data.2]
            exact hDQ.2.2.2.1
          · rw [hE0data.2]
            exact hDP.2.2.2.2.1
          · rw [hE1data.2]
            exact hDQ.2.2.2.2.2
        have hcensored :
            censored_distribution E = censored_distribution DP := by
          rw [condition_necessary_censored_decomposition E,
            condition_necessary_censored_decomposition DP,
            hE0data.1, hE0data.2, hE1data.1, hE1data.2, ← hselected]
        have hATE :
            average_treatment_effect E = average_treatment_effect DP := by
          calc
            average_treatment_effect E = f (censored_distribution E) :=
              (hf E hEreal).symm
            _ = f (censored_distribution DP) := by rw [hcensored]
            _ = average_treatment_effect DP := hf DP hDP
        rw [ate_marginal_decomposition E Pcl Dcl hEreal,
          ate_marginal_decomposition DP Pcl Dcl hDP,
          hE0data.2, hE1data.2, hDPm, hDQm] at hATE
        apply hmean
        linarith
    · exact Or.inl hX

@[blueprint "lem:condition-sufficient-arm-observables-of-censored-eq"
  (statement := /-- Fix a covariate dimension $d$, two observational studies
    $\mathcal{D}_{0},\mathcal{D}_{1}$, and a treatment arm $t\in\{0,1\}$.
    If the two studies have the same censored distribution, then their
    covariate marginals agree and their propensity-weighted outcome measures
    in arm $t$ agree. -/)
  (proof := /-- Push the common censored distribution forward by the covariate
    projection to obtain equality of the covariate marginals. For the
    propensity-weighted measures, restrict the common censored distribution to
    observations with treatment label $t$ and then discard that label.
    Commutativity of restriction and pushforward identifies the resulting
    measure with the law of $(X,Y(t))$ on the event $T=t$.
    The propensity-weighting identity
    \cref{lem:condition-necessary-observed-arm-measure} identifies this law
    with the outcome marginal weighted by the induced propensity score. -/)
  (title := /-- Arm Observables Recovered from a Censored Distribution -/)
  (latexEnv := "lemma")]
lemma condition_sufficient_arm_observables_of_censored_eq {d : ℕ}
    (D0 D1 : observational_study d) (t : Bool)
    (hC : censored_distribution D0 = censored_distribution D1) :
    (outcome_marginal D0 t).map Prod.fst =
        (outcome_marginal D1 t).map Prod.fst ∧
      (outcome_marginal D0 t).withDensity
          (fun z => ENNReal.ofReal (induced_propensity D0 t z)) =
        (outcome_marginal D1 t).withDensity
          (fun z => ENNReal.ofReal (induced_propensity D1 t z)) := by
  have hcensor : Measurable (censoring_map d) := by
    unfold censoring_map
    have hx : Measurable (fun w : full_space d => w.1) := by fun_prop
    have ht : Measurable (fun w : full_space d => w.2.1) := by fun_prop
    have hy : Measurable (fun w : full_space d =>
        if w.2.1 then w.2.2.2 else w.2.2.1) :=
      Measurable.ite ((MeasurableSet.singleton true).preimage ht)
        (by fun_prop) (by fun_prop)
    fun_prop
  have houtcome (D : observational_study d) :
      Measurable (fun w : full_space d =>
        (w.1, if t then w.2.2.2 else w.2.2.1)) := by
    cases t <;> simp <;> fun_prop
  have hdrop : Measurable (fun z : observed_space d => (z.1, z.2.2)) := by
    fun_prop
  have hcov : Measurable (fun z : observed_space d => z.1) := by
    fun_prop
  constructor
  · calc
      (outcome_marginal D0 t).map Prod.fst =
          (censored_distribution D0).map (fun z => z.1) := by
            unfold outcome_marginal censored_distribution
            rw [Measure.map_map (by fun_prop) (houtcome D0),
              Measure.map_map hcov hcensor]
            rfl
      _ = (censored_distribution D1).map (fun z => z.1) := by rw [hC]
      _ = (outcome_marginal D1 t).map Prod.fst := by
            unfold outcome_marginal censored_distribution
            rw [Measure.map_map (by fun_prop) (houtcome D1),
              Measure.map_map hcov hcensor]
            rfl
  · have hEt : MeasurableSet {z : observed_space d | z.2.1 = t} := by
      exact (MeasurableSet.singleton t).preimage (by fun_prop)
    have hrecover (D : observational_study d) :
        ((censored_distribution D).restrict
            {z : observed_space d | z.2.1 = t}).map
              (fun z => (z.1, z.2.2)) =
          (outcome_marginal D t).withDensity
            (fun z => ENNReal.ofReal (induced_propensity D t z)) := by
      rw [condition_necessary_observed_arm_measure]
      unfold censored_distribution
      rw [Measure.restrict_map hcensor hEt]
      have hpre :
          censoring_map d ⁻¹' {z : observed_space d | z.2.1 = t} =
            {w : full_space d | w.2.1 = t} := by
        ext w
        simp [censoring_map]
      rw [hpre, Measure.map_map hdrop hcensor]
      apply Measure.map_congr
      have hE : MeasurableSet {w : full_space d | w.2.1 = t} := by
        exact (MeasurableSet.singleton t).preimage (by fun_prop)
      filter_upwards [ae_restrict_mem hE] with w hw
      cases t <;> cases w.2.1 <;> simp_all [censoring_map]
    rw [← hrecover D0, ← hrecover D1, hC]

@[blueprint "lem:condition-sufficient"
  (statement := /-- Sufficiency. Fix a covariate dimension $d$ and concept
    classes $(\mathcal{P}, \mathcal{H})$ (\cref{def:propensity-class},
    \cref{def:outcome-class}). If $(\mathcal{P}, \mathcal{H})$ satisfy the
    Identifiability Condition (\cref{def:identifiability-condition}), then the
    average treatment effect is identifiable from the censored distribution with
    respect to $(\mathcal{P}, \mathcal{H})$ (\cref{def:ate-identifiable}). -/)
  (proof := /-- Assume the Identifiability Condition
    (\cref{def:identifiability-condition}). For a censored distribution $C$
    represented by at least one realizable study, define $f(C)$ to be the
    average treatment effect of any such representative; set $f(C)=0$ when no
    realizable representative exists. It remains to prove that this definition
    is independent of the representative. Let $\mathcal{D}$ and
    $\mathcal{D}'$ be realizable studies with the same censored distribution
    (\cref{def:censored-distribution}). For each treatment arm, equality of the
    censored distributions implies equality of the corresponding covariate
    marginals and of the corresponding propensity-reweighted outcome
    measures. Each induced propensity and outcome marginal is directly a
    compatible tuple in the chosen arm (\cref{def:compatible}); no treatment
    relabeling or pointwise choice of a conditional-probability version is
    required. Apply the Identifiability Condition to the two same-arm tuples.
    Its second and third alternatives are excluded by these two equalities, so
    its first alternative yields equality of the arm's outcome expectations.
    The recovery of these two observable quantities from the censored law is
    formalized in
    \cref{lem:condition-sufficient-arm-observables-of-censored-eq}.
    Applying this argument to both arms and subtracting shows, by the marginal
    decomposition \cref{lem:ate-marginal-decomposition}, that
    $\tau_{\mathcal{D}}=\tau_{\mathcal{D}'}$. Thus $f$ is well defined and
    satisfies $f(\mathcal{C}_{\mathcal{D}})=\tau_{\mathcal{D}}$ for every
    realizable study, which is identifiability
    (\cref{def:ate-identifiable}). -/)
  (title := /-- Sufficiency of the Identifiability Condition -/)
  (latexEnv := "lemma")]
lemma condition_sufficient {d : ℕ} (Pcl : propensity_class d) (Dcl : outcome_class d)
    (h : identifiability_condition Pcl Dcl) : ate_identifiable Pcl Dcl := by
  classical
  let f : Measure (observed_space d) → ℝ := fun C =>
    if hC : ∃ D : observational_study d,
        realizable D Pcl Dcl ∧ censored_distribution D = C then
      average_treatment_effect hC.choose
    else 0
  refine ⟨f, ?_⟩
  intro D hD
  simp only [f]
  split
  · rename_i hC
    let D' := hC.choose
    have hD' : realizable D' Pcl Dcl := hC.choose_spec.1
    have hCD' : censored_distribution D' = censored_distribution D :=
      hC.choose_spec.2
    have harm (t : Bool) :
        (∫ z, z.2 ∂outcome_marginal D' t) =
          ∫ z, z.2 ∂outcome_marginal D t := by
      have hobs :=
        condition_sufficient_arm_observables_of_censored_eq D' D t hCD'
      have hcompD' : compatible Pcl Dcl t
          (induced_propensity D' t) (outcome_marginal D' t) := by
        refine ⟨?_, ?_, D', hD', rfl, Filter.EventuallyEq.rfl⟩
        · cases t
          · exact hD'.1
          · exact hD'.2.1
        · cases t
          · exact hD'.2.2.1
          · exact hD'.2.2.2.1
      have hcompD : compatible Pcl Dcl t
          (induced_propensity D t) (outcome_marginal D t) := by
        refine ⟨?_, ?_, D, hD, rfl, Filter.EventuallyEq.rfl⟩
        · cases t
          · exact hD.1
          · exact hD.2.1
        · cases t
          · exact hD.2.2.1
          · exact hD.2.2.2.1
      rcases h t (induced_propensity D' t) (outcome_marginal D' t)
          (induced_propensity D t) (outcome_marginal D t)
          hcompD' hcompD with heq | hcovneq | hweightneq
      · exact heq
      · exact False.elim (hcovneq hobs.1)
      · exact False.elim (hweightneq hobs.2)
    rw [ate_marginal_decomposition D' Pcl Dcl hD',
      ate_marginal_decomposition D Pcl Dcl hD, harm true, harm false]
  · rename_i hnone
    exfalso
    exact hnone ⟨D, hD, rfl⟩

@[blueprint "thm:ate-identifiable-iff-condition"
  (statement := /-- Identification of the ATE. Fix a covariate dimension $d$ and
    concept classes $(\mathcal{P}, \mathcal{H})$ (\cref{def:propensity-class},
    \cref{def:outcome-class}). The average treatment effect $\tau_{\mathcal{D}}$
    is identifiable from the censored distribution $\mathcal{C}_{\mathcal{D}}$
    for every observational study $\mathcal{D}$ realizable with respect to
    $(\mathcal{P}, \mathcal{H})$ (\cref{def:ate-identifiable}) if and only if
    $(\mathcal{P}, \mathcal{H})$ satisfy the Identifiability Condition
    (\cref{def:identifiability-condition}). -/)
  (proof := /-- The forward implication is the necessity direction
    \cref{lem:condition-necessary}, and the backward implication is the
    sufficiency direction \cref{lem:condition-sufficient}. Combining the two
    implications yields the stated equivalence. -/)
  (title := /-- Identification of ATE -/)
  (latexEnv := "theorem")]
theorem ate_identifiable_iff_condition {d : ℕ}
    (Pcl : propensity_class d) (Dcl : outcome_class d) :
    ate_identifiable Pcl Dcl ↔ identifiability_condition Pcl Dcl := by
  exact ⟨condition_necessary Pcl Dcl, condition_sufficient Pcl Dcl⟩

import Architect
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

set_option linter.all false
set_option maxHeartbeats 500000

open Filter MeasureTheory

@[blueprint "def:preferential-attachment-history-valid"
  (statement := /-- Fix integers $m,n\geq 0$. An attachment history on the labelled vertex set $\{0,\ldots,n-1\}$ records, for every vertex $t\geq 2$ and each of its $m$ incident edges, a previously present endpoint in $\{0,\ldots,t-1\}$. The dummy entries belonging to the two initial vertices are required to be $0$. -/)
  (title := /-- Valid Preferential-Attachment Histories -/)
  (latexEnv := "definition")]
def preferential_attachment_history_valid {m n : ℕ}
    (history : Fin n → Fin m → Fin n) : Prop :=
  ∀ t i, if t.val < 2 then (history t i).val = 0 else (history t i).val < t.val

@[blueprint "def:preferential-attachment-degree-before"
  (statement := /-- Let $h$ be an attachment history with $m$ edges per new vertex. Immediately before edge $i$ of vertex $t$ is attached, the degree of a vertex $v<t$ is the sum of its degree $m$ at birth and the number of earlier attachment choices whose endpoint is $v$. For the two initial vertices, the degree-$m$ contribution comes from the $m$ parallel edges joining them. -/)
  (title := /-- Degree Immediately Before an Attachment -/)
  (latexEnv := "definition")]
def preferential_attachment_degree_before {m n : ℕ}
    (history : Fin n → Fin m → Fin n) (t : Fin n) (i : Fin m) (v : Fin n) : ℕ :=
  (if v.val < 2 then m else 0) +
    (if 2 ≤ v.val ∧ v.val < t.val then m else 0) +
    ((Finset.univ : Finset (Fin n × Fin m)).filter fun p =>
      2 ≤ p.1.val ∧
        (p.1.val < t.val ∨ (p.1 = t ∧ p.2.val < i.val)) ∧
        history p.1 p.2 = v).card

@[blueprint "def:preferential-attachment-history-weight"
  (statement := /-- Fix $m,n$, shifts $\delta,\delta'$, and a changepoint $\tau$. The weight of a valid attachment history is the product, over vertices $t+1=3,\ldots,n$ and their $m$ edges, of
  \[
    \frac{\deg(v)+\delta_{t+1}}
         {\sum_{u<t}(\deg(u)+\delta_{t+1})},
    \qquad
    \delta_{t+1}=
      \begin{cases}
        \delta,&t+1\leq\tau,\\
        \delta',&t+1>\tau.
      \end{cases}
  \]
  Here all degrees are evaluated immediately before the corresponding edge is attached. -/)
  (title := /-- Probability Weight of an Attachment History -/)
  (latexEnv := "definition")]
noncomputable def preferential_attachment_history_weight {m n : ℕ}
    (preChangeShift postChangeShift : ℝ) (τ : ℕ)
    (history : Fin n → Fin m → Fin n) : ENNReal :=
  ∏ t : Fin n, ∏ i : Fin m,
    if 2 ≤ t.val then
      if (history t i).val < t.val then
        let shift := if t.val + 1 ≤ τ then preChangeShift else postChangeShift
        ENNReal.ofReal
          (((preferential_attachment_degree_before history t i (history t i) : ℝ) + shift) /
            ∑ v : Fin n, if v.val < t.val then
              (preferential_attachment_degree_before history t i v : ℝ) + shift
            else 0)
      else 0
    else if (history t i).val = 0 then 1 else 0

@[blueprint "def:preferential-attachment-edge-multiplicity"
  (statement := /-- The multiplicity of the unordered edge $\{u,v\}$ in the final graph encoded by an attachment history is $m$ for the initial pair $\{0,1\}$, plus the number of later attachment choices joining $u$ and $v$. -/)
  (title := /-- Edge Multiplicity Encoded by a History -/)
  (latexEnv := "definition")]
def preferential_attachment_edge_multiplicity {m n : ℕ}
    (history : Fin n → Fin m → Fin n) (u v : Fin n) : ℕ :=
  (if (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) then m else 0) +
    ((Finset.univ : Finset (Fin n × Fin m)).filter fun p =>
      2 ≤ p.1.val ∧
        ((p.1 = u ∧ history p.1 p.2 = v) ∨
          (p.1 = v ∧ history p.1 p.2 = u))).card

@[blueprint "def:preferential-attachment-ordered-post-change-list"
  (statement := /-- For integers \(0\leq\tau\leq n\), an ordered post-change list is an injective map
  \[
    a:\{0,\ldots,n-\tau-1\}\hookrightarrow\{0,\ldots,n-1\}.
  \]
  Thus \(a\) records, in latent arrival order, the distinct names assigned to the \(n-\tau\) vertices born after the changepoint. -/)
  (title := /-- Ordered Lists of Post-Change Vertex Names -/)
  (latexEnv := "definition")]
def preferential_attachment_ordered_post_change_list (n τ : ℕ) :=
  Fin (n - τ) ↪ Fin n

@[blueprint "def:preferential-attachment-randomly-labeled-component-system"
  (statement := /-- Fix snapshot laws \(\mathbb Q_{n,\tau}\), integers \(0\leq\tau\leq n\), and a constant \(B\geq1\). A randomly labeled component system consists of a finite discrete probability space \((\Xi_{n,\tau},P_n)\), a component law \(Q_a\) and likelihood ratio \(L_a=dQ_a/dP_n\) for every ordered post-change list \(a\) from \cref{def:preferential-attachment-ordered-post-change-list}, and their uniform mixture \(\widetilde Q_{n,\tau}\). A measurable projection \(\pi:\Xi_{n,\tau}\to\Omega\) satisfies
  \[
    \pi_{\#}P_n=\mathbb Q_{n,n},
    \qquad
    \pi_{\#}\widetilde Q_{n,\tau}=\mathbb Q_{n,\tau}.
  \]
  All measures and all likelihood ratios are defined on the same space \(\Xi_{n,\tau}\).

  The system also records the joint reverse-exposure law for each pair \(a,b\). For every name \(v\), outcome \(\xi\), and pair \(a,b\), the probability measure \(K^{a,b}_v(\xi,\cdot)\) is the regular conditional law of the still-unexposed attachment data given the data already revealed after \(v\). The function \(F^{a,b}_v\) is the likelihood-ratio factor revealed at that step. If \(v\) belongs to exactly one of the two lists, the defining conditional identity is
  \[
    \int_{\Xi_{n,\tau}}F^{a,b}_v(\eta)\,
      K^{a,b}_v(\xi,d\eta)=1
    \quad\text{for every conditioning state }\xi.
  \]
  Iterating these conditional laws removes all such exclusive-name factors. The residual integrand \(C_{a,b}\) contains only the factors belonging to names in both lists, and the system records the exact reverse-exposure identity
  \[
    \int L_aL_b\,dP_n=\int C_{a,b}\,dP_n
  \]
  together with
  \[
    \int C_{a,b}\,dP_n
      \leq B^{|\operatorname{range}(a)\cap\operatorname{range}(b)|}.
  \]
  These data make the cross moment meaningful even when \(a\) and \(b\) encode different latent arrival orders. -/)
  (title := /-- Common Randomly Labeled Space and Reverse-Exposure Laws -/)
  (latexEnv := "definition")]
structure preferential_attachment_randomly_labeled_component_system
    {Ω : Type*} [MeasurableSpace Ω]
    (snapshotLaw : ℕ → ℕ → ProbabilityMeasure Ω) (B : ℝ) (n τ : ℕ)
    (_hτ : τ ≤ n) where
  overlapConstant_ge_one : 1 ≤ B
  LabeledOutcome : Type
  labeledFintype : Fintype LabeledOutcome
  referenceLaw : @ProbabilityMeasure LabeledOutcome ⊤
  componentLaw :
    preferential_attachment_ordered_post_change_list n τ →
      @ProbabilityMeasure LabeledOutcome ⊤
  likelihoodRatio :
    preferential_attachment_ordered_post_change_list n τ → LabeledOutcome → ℝ
  likelihoodRatio_nonnegative :
    ∀ a x, 0 ≤ likelihoodRatio a x
  componentMass :
    ∀ a x,
      (componentLaw a : @Measure LabeledOutcome ⊤) {x} =
        ENNReal.ofReal (likelihoodRatio a x) *
          (referenceLaw : @Measure LabeledOutcome ⊤) {x}
  componentIndex :
    Finset (preferential_attachment_ordered_post_change_list n τ)
  componentIndex_complete :
    ∀ a, a ∈ componentIndex
  mixtureLaw : @ProbabilityMeasure LabeledOutcome ⊤
  mixtureMass :
    ∀ x,
      (mixtureLaw : @Measure LabeledOutcome ⊤) {x} =
        (∑ a ∈ componentIndex,
          (componentLaw a : @Measure LabeledOutcome ⊤) {x}) /
          (componentIndex.card : ENNReal)
  snapshotProjection : LabeledOutcome → Ω
  snapshotProjection_measurable :
    @Measurable LabeledOutcome Ω ⊤ _ snapshotProjection
  reference_projects :
    @Measure.map LabeledOutcome Ω ⊤ _ snapshotProjection
        (referenceLaw : @Measure LabeledOutcome ⊤) =
      (snapshotLaw n n : Measure Ω)
  mixture_projects :
    @Measure.map LabeledOutcome Ω ⊤ _ snapshotProjection
        (mixtureLaw : @Measure LabeledOutcome ⊤) =
      (snapshotLaw n τ : Measure Ω)
  reverseConditionalLaw :
    preferential_attachment_ordered_post_change_list n τ →
      preferential_attachment_ordered_post_change_list n τ →
        Fin n → LabeledOutcome → @ProbabilityMeasure LabeledOutcome ⊤
  reverseFactor :
    preferential_attachment_ordered_post_change_list n τ →
      preferential_attachment_ordered_post_change_list n τ →
        Fin n → LabeledOutcome → ℝ
  exclusiveFactorConditionalMean :
    ∀ a b v,
      (v ∈ Finset.univ.map a) ≠ (v ∈ Finset.univ.map b) →
        ∀ x,
          (∫ y, reverseFactor a b v y
            ∂(reverseConditionalLaw a b v x :
              @Measure LabeledOutcome ⊤)) = 1
  commonContribution :
    preferential_attachment_ordered_post_change_list n τ →
      preferential_attachment_ordered_post_change_list n τ →
        LabeledOutcome → ℝ
  reverseExposureIdentity :
    ∀ a b,
      (∫ x, likelihoodRatio a x * likelihoodRatio b x
        ∂(referenceLaw : @Measure LabeledOutcome ⊤)) =
      ∫ x, commonContribution a b x
        ∂(referenceLaw : @Measure LabeledOutcome ⊤)
  commonContributionIntegral_le :
    ∀ a b,
      (∫ x, commonContribution a b x
        ∂(referenceLaw : @Measure LabeledOutcome ⊤)) ≤
      B ^ ((Finset.univ.map a) ∩ (Finset.univ.map b)).card

@[blueprint "def:preferential-attachment-snapshot-model"
  (statement := /-- Let $\Omega$ be a measurable space of isomorphism classes of finite multigraphs. A preferential-attachment snapshot model consists of a fixed positive integer $m$, fixed distinct shifts $\delta,\delta'>-m$, and a map sending each valid attachment history to the isomorphism class of its final multigraph. More precisely, two valid histories have the same image if and only if there is a bijection between their finite vertex sets under which all edge multiplicities agree. For every network size $n$, changepoint $\tau$, and measurable set $A\subseteq\Omega$, the law $\mathbb Q_{n,\tau}$ is required to satisfy
  \[
    \mathbb Q_{n,\tau}(A)
      =\sum_{\substack{h\ \mathrm{valid}:\\ \operatorname{snap}(h)\in A}}
        \prod_{t=3}^{n}\prod_{i=1}^{m}
        \frac{\deg_{t,i-1}^{h}(h_{t,i})+\delta_t}
             {\sum_{v<t}(\deg_{t,i-1}^{h}(v)+\delta_t)},
  \]
  where $\delta_t=\delta$ for $t\leq\tau$ and $\delta_t=\delta'$ for $t>\tau$. Thus $\mathbb Q_{n,\tau}$ is the final unlabeled-snapshot marginal of the stated preferential-attachment construction: the arrival-time labels used to describe a history are not observable.

  The model also supplies a constant \(B\geq1\), depending only on the fixed parameters \(m,\delta,\delta'\), and, for every \(0\leq\tau\leq n\), a randomly labeled component system in the sense of \cref{def:preferential-attachment-randomly-labeled-component-system}. Consequently the reference law, every ordered-list component law, their likelihood ratios, their uniform mixture, the projection to the unlabeled snapshot, and the paired reverse-exposure conditional laws are fixed coherently on one finite probability space, with the same overlap constant \(B\) for all \(n\) and \(\tau\). -/)
  (title := /-- Preferential-Attachment Snapshot Model -/)
  (latexEnv := "definition")]
structure preferential_attachment_snapshot_model (Ω : Type*) [MeasurableSpace Ω] where
  edgesPerVertex : ℕ
  edgesPerVertex_pos : 0 < edgesPerVertex
  preChangeShift : ℝ
  postChangeShift : ℝ
  shifts_ne : preChangeShift ≠ postChangeShift
  preChangeShift_admissible : -(edgesPerVertex : ℝ) < preChangeShift
  postChangeShift_admissible : -(edgesPerVertex : ℝ) < postChangeShift
  snapshotOfHistory :
    ∀ n, (Fin n → Fin edgesPerVertex → Fin n) → Ω
  snapshot_identifies_unlabeled_multigraph :
    ∀ n history₁ history₂,
      preferential_attachment_history_valid history₁ →
      preferential_attachment_history_valid history₂ →
      snapshotOfHistory n history₁ = snapshotOfHistory n history₂ ↔
        ∃ e : Fin n ≃ Fin n, ∀ u v,
          preferential_attachment_edge_multiplicity history₁ u v =
            preferential_attachment_edge_multiplicity history₂ (e u) (e v)
  snapshotLaw : ℕ → ℕ → ProbabilityMeasure Ω
  snapshotLaw_generated :
    ∀ n τ A, MeasurableSet A →
      (snapshotLaw n τ : Measure Ω) A =
        ∑' history : {history : (Fin n → Fin edgesPerVertex → Fin n) //
            preferential_attachment_history_valid history},
          preferential_attachment_history_weight
              preChangeShift postChangeShift τ history.1 *
            Measure.dirac (snapshotOfHistory n history.1) A
  reverseExposureConstant : ℝ
  reverseExposureConstant_ge_one : 1 ≤ reverseExposureConstant
  randomlyLabeledComponentSystem :
    ∀ n τ (hτ : τ ≤ n),
      preferential_attachment_randomly_labeled_component_system
        snapshotLaw reverseExposureConstant n τ hτ

@[blueprint "def:total-variation-distance"
  (statement := /-- For probability measures $\mu$ and $\nu$ on a measurable space, define
  \[
    \operatorname{TV}(\mu,\nu)
      =\frac12\,|\mu-\nu|(\Omega),
  \]
  where $|\mu-\nu|$ is the total-variation measure of the finite signed measure $\mu-\nu$. -/)
  (title := /-- Total Variation Distance -/)
  (latexEnv := "definition")]
noncomputable def total_variation_distance {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : ProbabilityMeasure Ω) : ℝ :=
  let μ' := μ.toFiniteMeasure
  let ν' := ν.toFiniteMeasure
  (((μ' : Measure Ω).toSignedMeasure - (ν' : Measure Ω).toSignedMeasure).totalVariation).real
      Set.univ / 2

@[blueprint "lem:reverse-exposure-cross-moment-bound"
  (statement := /-- Let \(\Omega\) be a measurable space, let \(\mathbb Q_{n,\tau}\) be a family of probability measures on \(\Omega\), and fix \(n,\tau\in\mathbb N\) with \(\tau\leq n\) and \(B\in\mathbb R\) with \(B\geq1\). Let \(S\) be a randomly labeled component system for these data, with finite discrete outcome space \(\Xi\), reference law \(P\), and component likelihood ratios \(L_a\). Then, for every pair of ordered post-change lists \(a,b:\operatorname{Fin}(n-\tau)\hookrightarrow\operatorname{Fin}(n)\),
  \[
    \int_{\Xi}L_a(\xi)L_b(\xi)\,P(d\xi)
      \leq B^{|\operatorname{range}(a)\cap\operatorname{range}(b)|}.
  \] -/)
  (proof := /-- The reverse-exposure identity in \cref{def:preferential-attachment-randomly-labeled-component-system} identifies the cross moment with the integral of the common-name contribution. The common-contribution bound in the same definition bounds that integral by \(B^{|\operatorname{range}(a)\cap\operatorname{range}(b)|}\), which proves the claim. -/)
  (title := /-- Reverse Exposure Bounds Component Cross Moments -/)
  (latexEnv := "lemma")]
lemma reverse_exposure_cross_moment_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {snapshotLaw : ℕ → ℕ → ProbabilityMeasure Ω} {B : ℝ} {n τ : ℕ}
    {hτ : τ ≤ n}
    (system : preferential_attachment_randomly_labeled_component_system
      snapshotLaw B n τ hτ)
    (hB : 1 ≤ B) :
    ∀ a b,
      (∫ x, system.likelihoodRatio a x * system.likelihoodRatio b x
        ∂(system.referenceLaw :
          @Measure system.LabeledOutcome ⊤)) ≤
      B ^ ((Finset.univ.map a) ∩ (Finset.univ.map b)).card := by
  intro a b
  rw [system.reverseExposureIdentity a b]
  exact system.commonContributionIntegral_le a b

@[blueprint "lem:late-changepoint-snapshot-tv-bound"
  (statement := /-- Let $\mathbb Q$ be a preferential-attachment snapshot model with a fixed number $m>0$ of edges per arriving vertex and fixed distinct shifts $\delta,\delta'>-m$. Let $\tau:\mathbb N\to\mathbb N$ satisfy $\tau_n\leq n$ for every $n$. If
  \[
    n-\tau_n=o(\sqrt n),
  \]
  then
  \[
    \operatorname{TV}(\mathbb Q_{n,n},\mathbb Q_{n,\tau_n})=o(1)
  \]
  as $n\to\infty$, where both laws are those of the final multigraph after the vertex-arrival labels have been removed. -/)
  (proof := /-- Put \(k_n=n-\tau_n\) and
  \(B=\mathbb Q.\mathrm{reverseExposureConstant}\). By
  \cref{def:preferential-attachment-snapshot-model}, \(B\geq1\), and
  \(\tau_n\leq n\) supplies the finite randomly labeled component system
  of \cref{def:preferential-attachment-randomly-labeled-component-system}.
  Its component indices are the injective ordered lists of length \(k_n\)
  from \cref{def:preferential-attachment-ordered-post-change-list}; write
  \(P_n\) for its reference law, \(\widetilde Q_n\) for its mixture law,
  and \(L_{n,a}\) for the likelihood ratio of component \(a\).

  First reduce total variation to a finite second-moment estimate.  Apply the
  Jordan decomposition to the difference of the two snapshot probability
  measures.  Since that signed measure has total mass zero, its positive and
  negative parts have equal mass, and a Hahn set realizes the total variation
  as the difference of the two measures on the complementary measurable set.
  Pulling this set back through the snapshot projection and using the two
  projection identities of the component system reduces the difference to an
  event in its finite labeled outcome space.  If
  \[
    L_n=\frac1{|\mathcal A_n|}
      \sum_{a\in\mathcal A_n}L_{n,a},
  \]
  then the atomwise component-density and uniform-mixture identities show that
  \(L_n\) is the density of \(\widetilde Q_n\) with respect to \(P_n\).
  Cauchy--Schwarz on the pulled-back event, together with
  \(\sum_xP_n(x)=\sum_xL_n(x)P_n(x)=1\), gives
  \[
    \operatorname{TV}(\mathbb Q_{n,n},\mathbb Q_{n,\tau_n})
      \leq
      \sqrt{\sum_xP_n(x)L_n(x)^2-1}.
  \]
  Expanding the square and invoking
  \cref{lem:reverse-exposure-cross-moment-bound} for every ordered pair of
  component indices yields
  \[
    \operatorname{TV}(\mathbb Q_{n,n},\mathbb Q_{n,\tau_n})
      \leq\sqrt{H_n-1},\qquad
    H_n:=
      \frac1{|\mathcal A_n|^2}
      \sum_{a,b\in\mathcal A_n}
        B^{|\operatorname{range}(a)\cap\operatorname{range}(b)|}.
  \]

  It remains to bound \(H_n\).  The number of injective ordered lists is
  \(n^{\underline{k_n}}\), and termwise comparison in the descending
  product gives
  \[
    (\tau_n+1)^{k_n}\leq n^{\underline{k_n}}.
  \]
  For a fixed injection \(a\), enlarge the sum over injective \(b\) to a
  sum over all functions from \(\{1,\ldots,k_n\}\) to the \(n\) names.
  Every summand is nonnegative because \(B\geq1\).  The enlarged sum factors
  coordinatewise; bounding each coordinate sum by \(n+k_nB\) gives
  \[
    H_n
      \leq
      \left(
        1+\frac{(B+1)k_n}{\tau_n+1}
      \right)^{k_n}.
  \]

  The little-\(o\) hypothesis implies both \(k_n\leq\sqrt n\) eventually
  and
  \[
    \frac{k_n^2}{n}\longrightarrow0;
  \]
  the second assertion follows by multiplying the little-\(o\) relation by
  itself and dividing by \((\sqrt n)^2=n\).  Thus \(k_n\leq n/2\)
  eventually, so \(\tau_n+1\geq n/2\).  Using
  \(1+x\leq e^x\), for all sufficiently large \(n\) we obtain
  \[
    H_n
      \leq
      \exp\!\left(\frac{2(B+1)k_n^2}{n}\right).
  \]
  The exponent tends to zero, hence the square root of the exponential minus
  one tends to zero.  The preceding total-variation estimate and
  nonnegativity squeeze the asserted distance to zero, which is exactly the
  claimed little-\(o\) relation. -/)
  (title := /-- The Late-Changepoint Bound for Unlabeled Snapshots -/)
  (latexEnv := "lemma")]
lemma late_changepoint_snapshot_tv_bound {Ω : Type*} [MeasurableSpace Ω]
    (model : preferential_attachment_snapshot_model Ω) (τ : ℕ → ℕ)
    (hτ : ∀ n, τ n ≤ n)
    (hLate : (fun n : ℕ => (n : ℝ) - (τ n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ))) :
    (fun n : ℕ => total_variation_distance
      (model.snapshotLaw n n) (model.snapshotLaw n (τ n))) =o[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
  classical
  rw [Asymptotics.isLittleO_one_iff]
  have htv (n : ℕ) :
      let system :=
        model.randomlyLabeledComponentSystem n (τ n) (hτ n)
      total_variation_distance
          (model.snapshotLaw n n) (model.snapshotLaw n (τ n)) ≤
        Real.sqrt
          (((∑ a ∈ system.componentIndex,
                  ∑ b ∈ system.componentIndex,
                    model.reverseExposureConstant ^
                      ((Finset.univ.map a) ∩ (Finset.univ.map b)).card) /
                (system.componentIndex.card : ℝ) ^ 2) -
              1) := by
    let system :=
      model.randomlyLabeledComponentSystem n (τ n) (hτ n)
    let s : SignedMeasure Ω :=
      (model.snapshotLaw n n : Measure Ω).toSignedMeasure -
        (model.snapshotLaw n (τ n) : Measure Ω).toSignedMeasure
    obtain ⟨A, hA, hneg, hpos, hposA, hnegAc⟩ :=
      s.toJordanDecomposition.exists_compl_positive_negative
    have hs0 : s Set.univ = 0 := by
      simp [s, Measure.toSignedMeasure_sub_apply]
    have hmass :
        s.toJordanDecomposition.posPart.real Set.univ =
          s.toJordanDecomposition.negPart.real Set.univ := by
      have hj := congrArg (fun t : SignedMeasure Ω => t Set.univ)
        (SignedMeasure.toSignedMeasure_toJordanDecomposition s)
      rw [JordanDecomposition.toSignedMeasure,
        Measure.toSignedMeasure_sub_apply MeasurableSet.univ] at hj
      rw [hs0] at hj
      linarith
    have hposAreal :
        s.toJordanDecomposition.posPart.real A = 0 := by
      simp [measureReal_def, hposA]
    have hnegAcreal :
        s.toJordanDecomposition.negPart.real Aᶜ = 0 := by
      simp [measureReal_def, hnegAc]
    have hposuniv :
        s.toJordanDecomposition.posPart.real Set.univ =
          s.toJordanDecomposition.posPart.real Aᶜ := by
      have hsum := measureReal_add_measureReal_compl
        (μ := s.toJordanDecomposition.posPart) hA
      linarith
    have hseval :
        s Aᶜ = s.toJordanDecomposition.posPart.real Set.univ := by
      have hj := congrArg (fun t : SignedMeasure Ω => t Aᶜ)
        (SignedMeasure.toSignedMeasure_toJordanDecomposition s)
      rw [JordanDecomposition.toSignedMeasure,
        Measure.toSignedMeasure_sub_apply hA.compl] at hj
      linarith
    have htv_eq :
        total_variation_distance
            (model.snapshotLaw n n) (model.snapshotLaw n (τ n)) =
          s Aᶜ := by
      change s.totalVariation.real Set.univ / 2 = s Aᶜ
      rw [SignedMeasure.totalVariation]
      rw [measureReal_def, Measure.add_apply,
        ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      change
        (s.toJordanDecomposition.posPart.real Set.univ +
            s.toJordanDecomposition.negPart.real Set.univ) /
          2 =
        s Aᶜ
      rw [hseval]
      nlinarith [hmass]
    have hsA :
        s Aᶜ =
          (model.snapshotLaw n n : Measure Ω).real Aᶜ -
            (model.snapshotLaw n (τ n) : Measure Ω).real Aᶜ := by
      dsimp [s]
      rw [Measure.toSignedMeasure_sub_apply hA.compl]
    rw [htv_eq]
    rw [hsA]
    rw [← system.reference_projects, ← system.mixture_projects]
    rw [measureReal_def, measureReal_def,
      Measure.map_apply system.snapshotProjection_measurable hA.compl,
      Measure.map_apply system.snapshotProjection_measurable hA.compl]
    change
      (system.referenceLaw : @Measure system.LabeledOutcome ⊤).real
            (system.snapshotProjection ⁻¹' Aᶜ) -
          (system.mixtureLaw : @Measure system.LabeledOutcome ⊤).real
            (system.snapshotProjection ⁻¹' Aᶜ) ≤
        Real.sqrt
          (((∑ a ∈ system.componentIndex,
                  ∑ b ∈ system.componentIndex,
                    model.reverseExposureConstant ^
                      ((Finset.univ.map a) ∩ (Finset.univ.map b)).card) /
                (system.componentIndex.card : ℝ) ^ 2) -
              1)
    letI : Fintype system.LabeledOutcome := system.labeledFintype
    letI : MeasurableSpace system.LabeledOutcome := ⊤
    let E : Finset system.LabeledOutcome :=
      Finset.univ.filter fun x => system.snapshotProjection x ∈ Aᶜ
    have hE :
        (E : Set system.LabeledOutcome) =
          system.snapshotProjection ⁻¹' Aᶜ := by
      ext x
      simp [E]
    rw [← hE]
    let l : system.LabeledOutcome → ℝ := fun x =>
      (∑ a ∈ system.componentIndex, system.likelihoodRatio a x) /
        system.componentIndex.card
    have hcard : 0 < system.componentIndex.card := by
      rw [Finset.card_pos]
      let a : preferential_attachment_ordered_post_change_list n (τ n) :=
        Fin.castLEEmb (Nat.sub_le n (τ n))
      exact ⟨a, system.componentIndex_complete a⟩
    have hmix (x : system.LabeledOutcome) :
        (system.mixtureLaw : Measure system.LabeledOutcome).real {x} =
          l x *
            (system.referenceLaw : Measure system.LabeledOutcome).real {x} := by
      rw [measureReal_def]
      rw [measureReal_def]
      rw [system.mixtureMass]
      rw [ENNReal.toReal_div]
      rw [ENNReal.toReal_sum]
      simp_rw [system.componentMass]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal,
        system.likelihoodRatio_nonnegative, ENNReal.toReal_natCast, l]
      rw [← Finset.sum_mul]
      ring
      simp
    rw [← sum_measureReal_singleton
      (μ := (system.referenceLaw : Measure system.LabeledOutcome)) E]
    rw [← sum_measureReal_singleton
      (μ := (system.mixtureLaw : Measure system.LabeledOutcome)) E]
    simp_rw [hmix]
    let p : system.LabeledOutcome → ℝ := fun x =>
      (system.referenceLaw : Measure system.LabeledOutcome).real {x}
    have hp (x : system.LabeledOutcome) : 0 ≤ p x := by
      exact measureReal_nonneg
    have hpsum :
        (∑ x : system.LabeledOutcome, p x) = 1 := by
      simpa [p] using
        (sum_measureReal_singleton
          (μ := (system.referenceLaw : Measure system.LabeledOutcome))
          (Finset.univ : Finset system.LabeledOutcome))
    have hlpsum :
        (∑ x : system.LabeledOutcome, l x * p x) = 1 := by
      calc
        _ =
            ∑ x : system.LabeledOutcome,
              (system.mixtureLaw :
                Measure system.LabeledOutcome).real {x} := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [hmix]
        _ = 1 := by
          simpa using
            (sum_measureReal_singleton
              (μ := (system.mixtureLaw : Measure system.LabeledOutcome))
              (Finset.univ : Finset system.LabeledOutcome))
    have hcross
        (a b : preferential_attachment_ordered_post_change_list n (τ n)) :
        (∑ x : system.LabeledOutcome,
            p x *
              (system.likelihoodRatio a x *
                system.likelihoodRatio b x)) ≤
          model.reverseExposureConstant ^
            ((Finset.univ.map a) ∩ (Finset.univ.map b)).card := by
      calc
        _ =
            ∫ x,
              system.likelihoodRatio a x *
                system.likelihoodRatio b x
              ∂(system.referenceLaw :
                Measure system.LabeledOutcome) := by
                  rw [integral_fintype Integrable.of_finite]
                  apply Finset.sum_congr rfl
                  intro x hx
                  simp only [p, smul_eq_mul]
        _ ≤ _ :=
          reverse_exposure_cross_moment_bound system
            model.reverseExposureConstant_ge_one a b
    have hvar_eq :
        (∑ x : system.LabeledOutcome, p x * (1 - l x) ^ 2) =
          (∑ x : system.LabeledOutcome, p x * l x ^ 2) - 1 := by
      calc
        _ =
            ∑ x : system.LabeledOutcome,
              (p x - 2 * (l x * p x) + p x * l x ^ 2) := by
                apply Finset.sum_congr rfl
                intro x hx
                ring
        _ =
            (∑ x : system.LabeledOutcome, p x) -
                2 * (∑ x : system.LabeledOutcome, l x * p x) +
              ∑ x : system.LabeledOutcome, p x * l x ^ 2 := by
                simp only [Finset.sum_add_distrib,
                  Finset.sum_sub_distrib, Finset.mul_sum]
        _ = _ := by
          rw [hpsum, hlpsum]
          ring
    have hl2_expand :
        (∑ x : system.LabeledOutcome, p x * l x ^ 2) =
          (∑ a ∈ system.componentIndex,
              ∑ b ∈ system.componentIndex,
                ∑ x : system.LabeledOutcome,
                  p x *
                    (system.likelihoodRatio a x *
                      system.likelihoodRatio b x)) /
            (system.componentIndex.card : ℝ) ^ 2 := by
      calc
        _ =
            (∑ x : system.LabeledOutcome,
                p x *
                  (∑ a ∈ system.componentIndex,
                    system.likelihoodRatio a x) ^ 2) /
              (system.componentIndex.card : ℝ) ^ 2 := by
                simp only [l]
                rw [Finset.sum_div]
                apply Finset.sum_congr rfl
                intro x hx
                field_simp
        _ =
            (∑ x : system.LabeledOutcome,
                ∑ a ∈ system.componentIndex,
                  ∑ b ∈ system.componentIndex,
                    p x *
                      (system.likelihoodRatio a x *
                        system.likelihoodRatio b x)) /
              (system.componentIndex.card : ℝ) ^ 2 := by
                congr 1
                apply Finset.sum_congr rfl
                intro x hx
                rw [pow_two, Finset.sum_mul_sum]
                simp only [Finset.mul_sum, Finset.sum_mul]
        _ = _ := by
          congr 1
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_comm]
    have hl2_le :
        (∑ x : system.LabeledOutcome, p x * l x ^ 2) ≤
          (∑ a ∈ system.componentIndex,
              ∑ b ∈ system.componentIndex,
                model.reverseExposureConstant ^
                  ((Finset.univ.map a) ∩ (Finset.univ.map b)).card) /
            (system.componentIndex.card : ℝ) ^ 2 := by
      rw [hl2_expand]
      apply div_le_div_of_nonneg_right
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact hcross a b
      positivity
    have hvar_le :
        (∑ x : system.LabeledOutcome, p x * (1 - l x) ^ 2) ≤
          (∑ a ∈ system.componentIndex,
              ∑ b ∈ system.componentIndex,
                model.reverseExposureConstant ^
                  ((Finset.univ.map a) ∩ (Finset.univ.map b)).card) /
            (system.componentIndex.card : ℝ) ^ 2 -
          1 := by
      rw [hvar_eq]
      exact sub_le_sub_right hl2_le 1
    have hpE : (∑ x ∈ E, p x) ≤ 1 := by
      rw [sum_measureReal_singleton]
      simpa [p] using
        (measureReal_mono (μ :=
          (system.referenceLaw : Measure system.LabeledOutcome))
          (show (E : Set system.LabeledOutcome) ⊆ Set.univ by simp))
    have hvar_subset :
        (∑ x ∈ E, p x * (1 - l x) ^ 2) ≤
          ∑ x : system.LabeledOutcome, p x * (1 - l x) ^ 2 := by
      exact Finset.sum_le_univ_sum_of_nonneg
        (fun x => mul_nonneg (hp x) (sq_nonneg _))
    calc
      (∑ b ∈ E,
            (system.referenceLaw :
              Measure system.LabeledOutcome).real {b}) -
          ∑ x ∈ E,
            l x *
              (system.referenceLaw :
                Measure system.LabeledOutcome).real {x} =
          ∑ x ∈ E,
            Real.sqrt (p x) * (Real.sqrt (p x) * (1 - l x)) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro x hx
              symm
              calc
                Real.sqrt (p x) * (Real.sqrt (p x) * (1 - l x)) =
                    (Real.sqrt (p x)) ^ 2 * (1 - l x) := by ring
                _ = p x * (1 - l x) := by
                  rw [Real.sq_sqrt (hp x)]
                _ =
                    (system.referenceLaw :
                        Measure system.LabeledOutcome).real {x} -
                      l x *
                        (system.referenceLaw :
                          Measure system.LabeledOutcome).real {x} := by
                  simp only [p]
                  ring
      _ ≤
          Real.sqrt (∑ x ∈ E, (Real.sqrt (p x)) ^ 2) *
            Real.sqrt
              (∑ x ∈ E,
                (Real.sqrt (p x) * (1 - l x)) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt E _ _
      _ =
          Real.sqrt (∑ x ∈ E, p x) *
            Real.sqrt (∑ x ∈ E, p x * (1 - l x) ^ 2) := by
              congr 2
              · apply Finset.sum_congr rfl
                intro x hx
                exact Real.sq_sqrt (hp x)
              · apply Finset.sum_congr rfl
                intro x hx
                rw [mul_pow, Real.sq_sqrt (hp x)]
      _ ≤ Real.sqrt (∑ x : system.LabeledOutcome,
            p x * (1 - l x) ^ 2) := by
              have hpEsum : 0 ≤ ∑ x ∈ E, p x := by
                exact Finset.sum_nonneg fun x hx => hp x
              have hsqrtE : Real.sqrt (∑ x ∈ E, p x) ≤ 1 := by
                nlinarith [Real.sq_sqrt hpEsum,
                  Real.sqrt_nonneg (∑ x ∈ E, p x)]
              calc
                _ ≤ 1 * Real.sqrt (∑ x ∈ E, p x * (1 - l x) ^ 2) := by
                  gcongr
                _ ≤ 1 * Real.sqrt (∑ x : system.LabeledOutcome,
                      p x * (1 - l x) ^ 2) := by
                  gcongr
                _ = _ := one_mul _
      _ ≤ _ := Real.sqrt_le_sqrt hvar_le
  have hdesc (n k : ℕ) (hk : k ≤ n) :
      (n - k + 1) ^ k ≤ n.descFactorial k := by
    rw [Nat.descFactorial_eq_prod_range]
    calc
      (n - k + 1) ^ k =
          ∏ i ∈ Finset.range k, (n - k + 1) := by simp
      _ ≤ ∏ i ∈ Finset.range k, (n - i) := by
        gcongr with i hi
        simp only [Finset.mem_range] at hi
        omega
  have hoverlap (n : ℕ) :
      let system :=
        model.randomlyLabeledComponentSystem n (τ n) (hτ n)
      (∑ a ∈ system.componentIndex,
          ∑ b ∈ system.componentIndex,
            model.reverseExposureConstant ^
              ((Finset.univ.map a) ∩ (Finset.univ.map b)).card) /
          (system.componentIndex.card : ℝ) ^ 2 ≤
        (1 +
            (model.reverseExposureConstant + 1) * (n - τ n : ℝ) /
              (n - (n - τ n) + 1 : ℝ)) ^ (n - τ n) := by
    dsimp only
    let system :=
      model.randomlyLabeledComponentSystem n (τ n) (hτ n)
    letI : Fintype
        (preferential_attachment_ordered_post_change_list n (τ n)) :=
      Function.Embedding.fintype
    have hindex : system.componentIndex = Finset.univ := by
      exact Finset.eq_univ_iff_forall.mpr system.componentIndex_complete
    have hweight
        (a b : preferential_attachment_ordered_post_change_list n (τ n)) :
        model.reverseExposureConstant ^
            ((Finset.univ.map a) ∩ (Finset.univ.map b)).card =
          ∏ j : Fin (n - τ n),
            if b.toFun j ∈ Finset.univ.map a
            then model.reverseExposureConstant else 1 := by
      have hcard_eq :
          ((Finset.univ.map a) ∩ (Finset.univ.map b)).card =
            (Finset.univ.filter fun j => b.toFun j ∈ Finset.univ.map a).card := by
        rw [← Finset.card_map b]
        congr
        ext v
        simp [and_comm]
        aesop
      rw [hcard_eq]
      rw [← Finset.prod_filter]
      simp
    let embToFun :
        preferential_attachment_ordered_post_change_list n (τ n) ↪
          (Fin (n - τ n) → Fin n) :=
      { toFun := fun b => b.toFun
        inj' := by
          intro a b hab
          exact Function.Embedding.ext fun j => congrFun hab j }
    have hsum_fun
        (a : preferential_attachment_ordered_post_change_list n (τ n)) :
        (∑ b : preferential_attachment_ordered_post_change_list n (τ n),
            model.reverseExposureConstant ^
              ((Finset.univ.map a) ∩ (Finset.univ.map b)).card) ≤
          ∑ f : Fin (n - τ n) → Fin n,
            ∏ j : Fin (n - τ n),
              if f j ∈ Finset.univ.map a
              then model.reverseExposureConstant else 1 := by
      calc
        _ =
            ∑ b : preferential_attachment_ordered_post_change_list n (τ n),
              ∏ j : Fin (n - τ n),
                if b.toFun j ∈ Finset.univ.map a
                then model.reverseExposureConstant else 1 := by
                  apply Finset.sum_congr rfl
                  intro b hb
                  exact hweight a b
        _ =
            ∑ f ∈ Finset.univ.map embToFun,
              ∏ j : Fin (n - τ n),
                if f j ∈ Finset.univ.map a
                then model.reverseExposureConstant else 1 := by
                  rw [Finset.sum_map]
                  simp [embToFun]
        _ ≤ _ := by
          exact Finset.sum_le_univ_sum_of_nonneg fun f => by
            exact Finset.prod_nonneg fun j hj => by
              split
              · linarith [model.reverseExposureConstant_ge_one]
              · norm_num
    have hsum_all
        (a : preferential_attachment_ordered_post_change_list n (τ n)) :
        (∑ f : Fin (n - τ n) → Fin n,
            ∏ j : Fin (n - τ n),
              if f j ∈ Finset.univ.map
                (show Fin (n - τ n) ↪ Fin n from a)
              then model.reverseExposureConstant else 1) ≤
          ((n : ℝ) +
              (n - τ n : ℝ) * model.reverseExposureConstant) ^
            (n - τ n) := by
      let ae : Fin (n - τ n) ↪ Fin n := a
      change
        (∑ f : Fin (n - τ n) → Fin n,
            ∏ j : Fin (n - τ n),
              if f j ∈ Finset.univ.map ae
              then model.reverseExposureConstant else 1) ≤
          ((n : ℝ) +
              (n - τ n : ℝ) * model.reverseExposureConstant) ^
            (n - τ n)
      rw [show
        (∑ f : Fin (n - τ n) → Fin n,
            ∏ j : Fin (n - τ n),
              if f j ∈ Finset.univ.map ae
              then model.reverseExposureConstant else 1) =
          ∏ j : Fin (n - τ n),
            ∑ v : Fin n,
              if v ∈ Finset.univ.map ae
              then model.reverseExposureConstant else 1 from
        (Fintype.prod_sum fun (_ : Fin (n - τ n)) (v : Fin n) =>
          if v ∈ Finset.univ.map ae
          then model.reverseExposureConstant else 1).symm]
      calc
        _ ≤
            ∏ _j : Fin (n - τ n),
              ((n : ℝ) +
                (n - τ n : ℝ) * model.reverseExposureConstant) := by
                  apply Finset.prod_le_prod
                  · intro j hj
                    exact Finset.sum_nonneg fun v hv => by
                      split
                      · linarith [model.reverseExposureConstant_ge_one]
                      · norm_num
                  intro j hj
                  rw [Finset.sum_ite]
                  simp [Finset.card_map]
                  have himage :
                      (Finset.image (fun j => ae j) Finset.univ).card =
                        n - τ n := by
                    simpa using
                      (Finset.card_image_of_injective Finset.univ
                        ae.injective)
                  have hcomplement :
                      (Finset.univ.filter fun x : Fin n =>
                        ∀ j : Fin (n - τ n), ¬ae j = x).card ≤ n := by
                    calc
                      _ ≤ Finset.univ.card := Finset.card_filter_le _ _
                      _ = n := by simp
                  rw [himage]
                  have hcomplement_real :
                      ((Finset.univ.filter fun x : Fin n =>
                          ∀ j : Fin (n - τ n), ¬ae j = x).card : ℝ) ≤
                        n := by
                    exact_mod_cast hcomplement
                  have hcast :
                      ((n - τ n : ℕ) : ℝ) =
                        (n : ℝ) - (τ n : ℝ) := by
                    exact Nat.cast_sub (hτ n)
                  rw [← hcast]
                  nlinarith
        _ = _ := by simp
    have hcard_index :
        system.componentIndex.card =
          n.descFactorial (n - τ n) := by
      rw [hindex]
      simpa [preferential_attachment_ordered_post_change_list] using
        (Fintype.card_embedding_eq
          (α := Fin (n - τ n)) (β := Fin n))
    have hdouble :
        (∑ a ∈ system.componentIndex,
            ∑ b ∈ system.componentIndex,
              model.reverseExposureConstant ^
                ((Finset.univ.map a) ∩ (Finset.univ.map b)).card) ≤
          system.componentIndex.card *
            ((n : ℝ) +
              (n - τ n : ℝ) * model.reverseExposureConstant) ^
                (n - τ n) := by
      rw [hindex]
      calc
        _ ≤
            ∑ _a :
                preferential_attachment_ordered_post_change_list n (τ n),
              ((n : ℝ) +
                (n - τ n : ℝ) * model.reverseExposureConstant) ^
                  (n - τ n) := by
                    apply Finset.sum_le_sum
                    intro a ha
                    exact (hsum_fun a).trans (hsum_all a)
        _ = _ := by simp
    have hcard_pos : 0 < system.componentIndex.card := by
      rw [Finset.card_pos]
      let a : preferential_attachment_ordered_post_change_list n (τ n) :=
        Fin.castLEEmb (Nat.sub_le n (τ n))
      exact ⟨a, system.componentIndex_complete a⟩
    have hdesc_nat :
        (τ n + 1) ^ (n - τ n) ≤
          n.descFactorial (n - τ n) := by
      have hd : n - (n - τ n) + 1 = τ n + 1 := by
        have := hτ n
        omega
      rw [← hd]
      exact hdesc n (n - τ n) (Nat.sub_le n (τ n))
    have hdesc_real :
        ((τ n + 1 : ℕ) : ℝ) ^ (n - τ n) ≤
          (system.componentIndex.card : ℝ) := by
      rw [hcard_index]
      exact_mod_cast hdesc_nat
    have hcast :
        ((n - τ n : ℕ) : ℝ) =
          (n : ℝ) - (τ n : ℝ) := by
      exact Nat.cast_sub (hτ n)
    have hdenom :
        (n : ℝ) - ((n : ℝ) - (τ n : ℝ)) + 1 =
          (τ n : ℝ) + 1 := by
      ring
    have hlag : 0 ≤ (n : ℝ) - (τ n : ℝ) := by
      apply sub_nonneg.mpr
      exact_mod_cast hτ n
    have hB : 0 ≤ model.reverseExposureConstant :=
      le_trans (by norm_num) model.reverseExposureConstant_ge_one
    rw [hdenom]
    change
      (∑ a ∈ system.componentIndex,
          ∑ b ∈ system.componentIndex,
            model.reverseExposureConstant ^
              ((Finset.univ.map a) ∩ (Finset.univ.map b)).card) /
          (system.componentIndex.card : ℝ) ^ 2 ≤
        (1 +
            (model.reverseExposureConstant + 1) *
                ((n : ℝ) - (τ n : ℝ)) /
              ((τ n : ℝ) + 1)) ^ (n - τ n)
    calc
      _ ≤
          ((system.componentIndex.card : ℝ) *
              ((n : ℝ) +
                ((n : ℝ) - (τ n : ℝ)) *
                  model.reverseExposureConstant) ^ (n - τ n)) /
            (system.componentIndex.card : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hdouble (sq_nonneg _)
      _ =
          ((n : ℝ) +
              ((n : ℝ) - (τ n : ℝ)) *
                model.reverseExposureConstant) ^ (n - τ n) /
            (system.componentIndex.card : ℝ) := by
              field_simp
      _ ≤
          ((n : ℝ) +
              ((n : ℝ) - (τ n : ℝ)) *
                model.reverseExposureConstant) ^ (n - τ n) /
            ((τ n + 1 : ℕ) : ℝ) ^ (n - τ n) := by
              apply div_le_div_of_nonneg_left
              · positivity
              · positivity
              · exact hdesc_real
      _ =
          (((n : ℝ) +
                ((n : ℝ) - (τ n : ℝ)) *
                  model.reverseExposureConstant) /
              ((τ n + 1 : ℕ) : ℝ)) ^ (n - τ n) := by
              rw [div_pow]
      _ ≤
          (1 +
              (model.reverseExposureConstant + 1) *
                  ((n : ℝ) - (τ n : ℝ)) /
                ((τ n : ℝ) + 1)) ^ (n - τ n) := by
              apply pow_le_pow_left₀
              · positivity
              · apply (div_le_iff₀ (by positivity)).2
                rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
                  div_mul_cancel₀]
                nlinarith
                positivity
  have hd2 :
      Tendsto
        (fun n : ℕ =>
          ((n : ℝ) - (τ n : ℝ)) ^ 2 / (n : ℝ))
        atTop (nhds 0) := by
    simpa only [pow_two, Real.mul_self_sqrt (Nat.cast_nonneg _)] using
      (hLate.mul hLate).tendsto_div_nhds_zero
  have hhalf :
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) - (τ n : ℝ) ≤ (n : ℝ) / 2 := by
    filter_upwards [hLate.eventuallyLE, eventually_ge_atTop 4] with n hn hn4
    have hlag : 0 ≤ (n : ℝ) - (τ n : ℝ) := by
      apply sub_nonneg.mpr
      exact_mod_cast hτ n
    have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hlag,
      Real.norm_eq_abs, abs_of_nonneg hsqrt] at hn
    have hn4real : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        total_variation_distance
            (model.snapshotLaw n n) (model.snapshotLaw n (τ n)) ≤
          Real.sqrt
            (Real.exp
                (2 * (model.reverseExposureConstant + 1) *
                  (((n : ℝ) - (τ n : ℝ)) ^ 2 / (n : ℝ))) -
              1) := by
    filter_upwards [hhalf, eventually_ge_atTop 4] with n hn hn4
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    have hlag : 0 ≤ (n : ℝ) - (τ n : ℝ) := by
      apply sub_nonneg.mpr
      exact_mod_cast hτ n
    have hconstant : 0 ≤ model.reverseExposureConstant + 1 := by
      linarith [model.reverseExposureConstant_ge_one]
    have hdenom :
        (n : ℝ) - ((n : ℝ) - (τ n : ℝ)) + 1 =
          (τ n : ℝ) + 1 := by
      ring
    have htauhalf :
        (n : ℝ) / 2 ≤ (τ n : ℝ) + 1 := by
      nlinarith
    have hfrac :
        (model.reverseExposureConstant + 1) *
              ((n : ℝ) - (τ n : ℝ)) /
            ((τ n : ℝ) + 1) ≤
          2 * (model.reverseExposureConstant + 1) *
              ((n : ℝ) - (τ n : ℝ)) /
            (n : ℝ) := by
      calc
        _ ≤
            ((model.reverseExposureConstant + 1) *
                ((n : ℝ) - (τ n : ℝ))) /
              ((n : ℝ) / 2) := by
                exact div_le_div_of_nonneg_left
                  (mul_nonneg hconstant hlag) (by positivity) htauhalf
        _ = _ := by field_simp
    have hbase :
        1 +
              (model.reverseExposureConstant + 1) *
                ((n : ℝ) - (τ n : ℝ)) /
              ((n : ℝ) - ((n : ℝ) - (τ n : ℝ)) + 1) ≤
            Real.exp
              (2 * (model.reverseExposureConstant + 1) *
                ((n : ℝ) - (τ n : ℝ)) / (n : ℝ)) := by
      rw [hdenom]
      calc
        _ ≤
            1 + 2 * (model.reverseExposureConstant + 1) *
              ((n : ℝ) - (τ n : ℝ)) / (n : ℝ) := by
                simpa [add_comm] using add_le_add_left hfrac 1
        _ ≤ _ := by
          simpa [add_comm] using
            Real.add_one_le_exp
              (2 * (model.reverseExposureConstant + 1) *
                ((n : ℝ) - (τ n : ℝ)) / (n : ℝ))
    have hcast :
        ((n - τ n : ℕ) : ℝ) =
          (n : ℝ) - (τ n : ℝ) := by
      exact Nat.cast_sub (hτ n)
    have hpower :
        (1 +
              (model.reverseExposureConstant + 1) *
                ((n : ℝ) - (τ n : ℝ)) /
              ((n : ℝ) - ((n : ℝ) - (τ n : ℝ)) + 1)) ^
            (n - τ n) ≤
          Real.exp
            (2 * (model.reverseExposureConstant + 1) *
              (((n : ℝ) - (τ n : ℝ)) ^ 2 / (n : ℝ))) := by
      have hbase_nonneg :
          0 ≤
            1 +
              (model.reverseExposureConstant + 1) *
                ((n : ℝ) - (τ n : ℝ)) /
              ((n : ℝ) - ((n : ℝ) - (τ n : ℝ)) + 1) := by
        rw [hdenom]
        positivity
      calc
        _ ≤
            (Real.exp
              (2 * (model.reverseExposureConstant + 1) *
                ((n : ℝ) - (τ n : ℝ)) / (n : ℝ))) ^
                (n - τ n) := by
                  exact pow_le_pow_left₀ hbase_nonneg hbase (n - τ n)
        _ =
            Real.exp
              (((n - τ n : ℕ) : ℝ) *
                (2 * (model.reverseExposureConstant + 1) *
                  ((n : ℝ) - (τ n : ℝ)) / (n : ℝ))) := by
                    rw [Real.exp_nat_mul]
        _ = _ := by
          rw [hcast]
          congr 1
          ring
    calc
      _ ≤ _ := htv n
      _ ≤
          Real.sqrt
            ((1 +
                (model.reverseExposureConstant + 1) *
                  ((n : ℝ) - (τ n : ℝ)) /
                ((n : ℝ) - ((n : ℝ) - (τ n : ℝ)) + 1)) ^
                (n - τ n) - 1) := by
                  apply Real.sqrt_le_sqrt
                  exact sub_le_sub_right (hoverlap n) 1
      _ ≤ _ := by
        apply Real.sqrt_le_sqrt
        exact sub_le_sub_right hpower 1
  have hexponent :
      Tendsto
        (fun n : ℕ =>
          2 * (model.reverseExposureConstant + 1) *
            (((n : ℝ) - (τ n : ℝ)) ^ 2 / (n : ℝ)))
        atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hd2 :
        Tendsto
          (fun n : ℕ =>
            (2 * (model.reverseExposureConstant + 1)) *
              (((n : ℝ) - (τ n : ℝ)) ^ 2 / (n : ℝ)))
          atTop
          (nhds
            ((2 * (model.reverseExposureConstant + 1)) * 0)))
  have hexponential :
      Tendsto
        (fun n : ℕ =>
          Real.exp
            (2 * (model.reverseExposureConstant + 1) *
              (((n : ℝ) - (τ n : ℝ)) ^ 2 / (n : ℝ))))
        atTop (nhds 1) := by
    change
      Tendsto
        (Real.exp ∘
          fun n : ℕ =>
            2 * (model.reverseExposureConstant + 1) *
              (((n : ℝ) - (τ n : ℝ)) ^ 2 / (n : ℝ)))
        atTop (nhds 1)
    exact Real.tendsto_exp_nhds_zero_nhds_one.comp hexponent
  have hsqrt :
      Tendsto
        (fun n : ℕ =>
          Real.sqrt
            (Real.exp
                (2 * (model.reverseExposureConstant + 1) *
                  (((n : ℝ) - (τ n : ℝ)) ^ 2 / (n : ℝ))) -
              1))
        atTop (nhds 0) := by
    simpa using (hexponential.sub_const 1).sqrt
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun n => by
      dsimp [total_variation_distance]
      positivity)
    hupper hsqrt

@[blueprint "lem:late-changepoint-total-variation-estimate"
  (statement := /-- Let $\Omega$ be a measurable space, and let $\mathcal M$ be a preferential-attachment snapshot model on $\Omega$ with fixed $m\in\mathbb N$, $m>0$, and fixed distinct shifts $\delta,\delta'>-m$. Write $\mathbb Q_{n,t}$ for the snapshot law supplied by $\mathcal M$ at network size $n$ and changepoint $t$; this is the law of the isomorphism class of the final multigraph, with vertex arrival labels unobserved. Let $\tau:\mathbb N\to\mathbb N$ satisfy $\tau_n\le n$ for every $n$. If
  \[
    n-\tau_n=o(\sqrt n),
  \]
  then
  \[
    \operatorname{TV}(\mathbb Q_{n,n},\mathbb Q_{n,\tau_n})=o(1)
  \]
  as $n\to\infty$. -/)
  (proof := /-- Apply \cref{lem:late-changepoint-snapshot-tv-bound} to the fixed snapshot model and the sequence $\tau$. Its two hypotheses are exactly the pointwise bound $\tau_n\leq n$ and the assumed relation $n-\tau_n=o(\sqrt n)$. Its conclusion is therefore
  \[
    \operatorname{TV}(\mathbb Q_{n,n},\mathbb Q_{n,\tau_n})=o(1),
  \]
  which is the desired estimate. -/)
  (title := /-- The Isolated Late-Changepoint Estimate -/)
  (latexEnv := "lemma")]
lemma late_changepoint_total_variation_estimate {Ω : Type*} [MeasurableSpace Ω]
    (model : preferential_attachment_snapshot_model Ω) (τ : ℕ → ℕ)
    (hτ : ∀ n, τ n ≤ n)
    (hLate : (fun n : ℕ => (n : ℝ) - (τ n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ))) :
    (fun n : ℕ => total_variation_distance
      (model.snapshotLaw n n) (model.snapshotLaw n (τ n))) =o[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
  exact late_changepoint_snapshot_tv_bound model τ hτ hLate

@[blueprint "thm:changepoint-detection-threshold"
  (statement := /-- Fix a preferential-attachment model with $m\in\mathbb N$, $m>0$, and distinct attachment shifts $\delta,\delta'>-m$. For each $n$ and $\tau$, let $\mathbb Q_{n,\tau}$ denote the law of the isomorphism class of its final multigraph, with vertex arrival labels unobserved. Let $\tau_n\le n$ be a changepoint sequence. If $n-\tau_n=o(\sqrt n)$, then
  \[
    \operatorname{TV}(\mathbb Q_{n,n},\mathbb Q_{n,\tau_n})=o(1)
  \]
  as $n\to\infty$. Here $\mathbb Q_{n,n}$ is the no-changepoint law and $\operatorname{TV}$ denotes total variation distance. -/)
  (proof := /-- Apply the late-changepoint estimate of \cref{lem:late-changepoint-total-variation-estimate} to the fixed model and the sequence $\tau$. Its hypotheses are exactly the assumed pointwise bound $\tau_n\le n$ and the relation $n-\tau_n=o(\sqrt n)$, and its conclusion is the asserted $o(1)$ total-variation bound. -/)
  (title := /-- Changepoint Detection Threshold -/)
  (latexEnv := "theorem")]
theorem changepoint_detection_threshold {Ω : Type*} [MeasurableSpace Ω]
    (model : preferential_attachment_snapshot_model Ω) (τ : ℕ → ℕ)
    (hτ : ∀ n, τ n ≤ n)
    (hLate : (fun n : ℕ => (n : ℝ) - (τ n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ))) :
    (fun n : ℕ => total_variation_distance
      (model.snapshotLaw n n) (model.snapshotLaw n (τ n))) =o[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
  exact late_changepoint_total_variation_estimate model τ hτ hLate

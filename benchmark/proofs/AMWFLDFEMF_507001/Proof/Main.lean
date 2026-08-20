import Architect
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open scoped ENNReal BigOperators
open MeasureTheory

@[blueprint "def:population-model-class-risk"
  (statement := /-- Let \(\mathcal Z\) be a measurable space, let \(\mathcal F\) be a model
  class, let \(\ell:\mathcal F\times\mathcal Z\to[0,\infty]\) be a loss function, and let
  \(P\) be a measure on \(\mathcal Z\).  The population model-class risk is
  \[
    R_P(\mathcal F):=\inf_{f\in\mathcal F}\int_{\mathcal Z}\ell(f,z)\,dP(z).
  \] -/)
  (title := /-- Population model-class risk -/)
  (latexEnv := "definition")]
noncomputable def population_model_class_risk
    {Z F : Type*} [MeasurableSpace Z]
    (loss : F → Z → ℝ≥0∞) (P : Measure Z) : ℝ≥0∞ :=
  ⨅ f : F, ∫⁻ z, loss f z ∂P

@[blueprint "def:empirical-model-class-risk"
  (statement := /-- Let \(\mathcal Z\) be a data space, let \(\mathcal F\) be a model
  class, let \(\ell:\mathcal F\times\mathcal Z\to[0,\infty]\) be a loss function, and
  let \(z=(z_i)_{i\in\operatorname{Fin}(N)}\) be a sample of size \(N\).  The empirical
  model-class risk is
  \[
    \widehat R_N(\mathcal F,z):=
      \inf_{f\in\mathcal F}\frac{1}{N}\sum_{i\in\operatorname{Fin}(N)}\ell(f,z_i),
  \]
  where the value is taken in the extended nonnegative reals. -/)
  (title := /-- Empirical model-class risk -/)
  (latexEnv := "definition")]
noncomputable def empirical_model_class_risk
    {Z F : Type*} (loss : F → Z → ℝ≥0∞)
    {N : ℕ} (sample : Fin N → Z) : ℝ≥0∞ :=
  ⨅ f : F, (∑ i : Fin N, loss f (sample i)) / (N : ℝ≥0∞)

@[blueprint "def:iid-sample-law"
  (statement := /-- Let \(\mathcal Z\) be a measurable space, let \(P\) be a measure on
  \(\mathcal Z\), and let \(N\in\mathbb N\).  The law \(P^N\) of an ordered sample of
  \(N\) independent observations, each having law \(P\), is the finite product measure
  on \(\operatorname{Fin}(N)\to\mathcal Z\). -/)
  (title := /-- Finite i.i.d. sample law -/)
  (latexEnv := "definition")]
noncomputable def iid_sample_law
    {Z : Type*} [MeasurableSpace Z] (P : Measure Z) (N : ℕ) :
    Measure (Fin N → Z) :=
  Measure.pi (fun _ : Fin N ↦ P)

@[blueprint "def:valid-distribution-free-lower-bound"
  (statement := /-- Fix measurable spaces \(\mathcal Z\) and \(\Xi\), a model class
  \(\mathcal F\), a loss \(\ell:\mathcal F\times\mathcal Z\to[0,\infty]\), an error
  level \(\alpha\in\mathbb R\), a sample size \(n\in\mathbb N\), and a probability
  measure \(Q\) on \(\Xi\).  A map
  \(L:(\operatorname{Fin}(n)\to\mathcal Z)\times\Xi\to[0,\infty]\) is a valid
  randomized distribution-free lower bound for the model-class risk if, for every
  probability measure \(P\) on \(\mathcal Z\), the event
  \(\{(z,\xi):R_P(\mathcal F)\geq L(z,\xi)\}\) is measurable and
  \[
    (P^n\otimes Q)\bigl\{(z,\xi):R_P(\mathcal F)\geq L(z,\xi)\bigr\}
      \geq \operatorname{ofReal}(1-\alpha).
  \]
  Here \(R_P(\mathcal F)\) and \(P^n\) are those of
  \cref{def:population-model-class-risk,def:iid-sample-law}, and the product law
  expresses the independence of the sample and the auxiliary random seed.  Taking
  \(\Xi\) to be a one-point space recovers deterministic lower bounds. -/)
  (title := /-- Valid distribution-free lower bound -/)
  (latexEnv := "definition")]
def valid_distribution_free_lower_bound
    {Z F Ξ : Type*} [MeasurableSpace Z] [MeasurableSpace Ξ]
    (loss : F → Z → ℝ≥0∞) (α : ℝ) (n : ℕ)
    (seedLaw : Measure Ξ) (_hseed : IsProbabilityMeasure seedLaw)
    (lowerBound : (Fin n → Z) → Ξ → ℝ≥0∞) : Prop :=
  ∀ (P : Measure Z), IsProbabilityMeasure P →
    MeasurableSet
        {outcome : (Fin n → Z) × Ξ |
          population_model_class_risk loss P ≥ lowerBound outcome.1 outcome.2} ∧
      (iid_sample_law P n).prod seedLaw
          {outcome |
            population_model_class_risk loss P ≥ lowerBound outcome.1 outcome.2} ≥
        ENNReal.ofReal (1 - α)

@[blueprint "lem:index-collision-bound"
  (statement := /-- For all natural numbers \(m\) and \(j\),
  \[
    2m\,m^{j}\leq j^{2}m^{j}+2m\,(m)_{j},
  \]
  where \((m)_{j}=m(m-1)\cdots(m-j+1)\) is the falling factorial.  This is the
  arithmetic core of the birthday/collision union bound: it rearranges to
  \(m^{j}-(m)_{j}\leq \tfrac{j^{2}}{2m}\,m^{j}\), controlling the probability that a
  uniform length-\(j\) tuple over an \(m\)-element set has a repeated coordinate. -/)
  (proof := /-- Induct on \(j\).  For \(j=0\) both sides are equal.  For the successor
  step, split on whether \(k\leq m\).  If \(k\leq m\), write \(m=k+p\), expand the
  falling factorial via its successor rule and \(m^{k+1}=m^{k}\,m\), bound
  \((m)_{k}\leq m^{k}\) by the falling-factorial-versus-power estimate, and combine
  the induction hypothesis with these monotonicity facts.  If \(k>m\), then
  \((m)_{k+1}=0\), and \(2m\leq(k+1)^{2}\) gives the bound directly. -/)
  (title := /-- Collision arithmetic for the birthday bound -/)
  (latexEnv := "lemma")]
lemma index_collision_bound (m j : ℕ) :
    2 * m * m ^ j ≤ j ^ 2 * m ^ j + 2 * m * (m.descFactorial j) := by
  induction j with
  | zero => simp
  | succ k ih =>
    rcases le_or_gt k m with hk | hk
    · obtain ⟨pp, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [Nat.descFactorial_succ, Nat.add_sub_cancel_left, pow_succ]
      have hd : (k + pp).descFactorial k ≤ (k + pp) ^ k := Nat.descFactorial_le_pow (k + pp) k
      have h1 := mul_le_mul_right' ih (k + pp)
      have h2 := mul_le_mul_left' hd k
      nlinarith [h1, h2, Nat.zero_le ((k + pp).descFactorial k), Nat.zero_le ((k + pp) ^ k),
        Nat.zero_le pp]
    · have h0 : m.descFactorial (k + 1) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [h0, pow_succ]
      have hbound : 2 * m ≤ (k + 1) ^ 2 := by nlinarith [hk]
      calc 2 * m * (m ^ k * m) = (2 * m) * (m ^ k * m) := by ring
        _ ≤ (k + 1) ^ 2 * (m ^ k * m) := Nat.mul_le_mul_right _ hbound
        _ ≤ (k + 1) ^ 2 * (m ^ k * m) + 2 * m * 0 := by simp

@[blueprint "lem:card-injective-index-tuples"
  (statement := /-- For all natural numbers \(n\) and \(N\), the number of injective
  index tuples \(J:\operatorname{Fin}(n)\to\operatorname{Fin}(N)\) equals the falling
  factorial \((N)_{n}=N(N-1)\cdots(N-n+1)\):
  \[
    \#\{J:\operatorname{Fin}(n)\hookrightarrow\operatorname{Fin}(N)\}=(N)_{n}.
  \] -/)
  (proof := /-- The subtype of injective functions is in bijection with the type of
  embeddings \(\operatorname{Fin}(n)\hookrightarrow\operatorname{Fin}(N)\).  Count the
  embeddings by induction on \(n\): an embedding of \(\operatorname{Fin}(k+1)\)
  corresponds to an embedding of \(\operatorname{Fin}(k)\) together with a value
  outside its range, of which there are \(N-k\); hence the count multiplies by
  \(N-k\) at each step, yielding \((N)_{n}\). -/)
  (title := /-- Count of injective index tuples -/)
  (latexEnv := "lemma")]
lemma card_injective_index_tuples (n N : ℕ) :
    (Finset.univ.filter (fun J : Fin n → Fin N => Function.Injective J)).card
      = N.descFactorial n := by
  have hemb : ∀ m : ℕ, Fintype.card (Fin m ↪ Fin N) = N.descFactorial m := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Fintype.card_congr (Equiv.embeddingFinSucc k (Fin N)), Fintype.card_sigma,
        Nat.descFactorial_succ]
      have hcard : ∀ e : Fin k ↪ Fin N, Fintype.card {i // i ∉ Set.range e} = N - k := by
        intro e
        rw [Fintype.card_subtype_compl (fun i => i ∈ Set.range e),
          Fintype.card_fin, Set.card_range_of_injective e.injective, Fintype.card_fin]
      simp_rw [hcard]
      rw [Finset.sum_const, Finset.card_univ, ih, smul_eq_mul, mul_comm]
  rw [← Fintype.card_subtype,
    Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin n) (Fin N)), hemb]

@[blueprint "lem:sample-law-reindex-lintegral"
  (statement := /-- Let \(\mathcal Z\) be a measurable space and let \(P\) be a
  \(\sigma\)-finite measure on \(\mathcal Z\).  For every permutation \(\sigma\) of
  \(\operatorname{Fin}(N)\) and every measurable-risk-free integrand
  \(q:(\operatorname{Fin}(N)\to\mathcal Z)\to[0,\infty]\),
  \[
    \int q\bigl((z_{\sigma(k)})_k\bigr)\,dP^{N}(z)=\int q(z)\,dP^{N}(z),
  \]
  i.e. the finite i.i.d. product law is invariant under permuting coordinates. -/)
  (proof := /-- The coordinate permutation is realized by the measurable equivalence
  \(\operatorname{piCongrLeft}\) associated with \(\sigma^{-1}\), which is measure
  preserving for the product measure.  Rewriting the right-hand integral through this
  measure-preserving equivalence and matching integrands pointwise yields the claim. -/)
  (title := /-- Coordinate-permutation invariance of the i.i.d. sample law -/)
  (latexEnv := "lemma")]
lemma sample_law_reindex_lintegral
    {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [SigmaFinite P] {N : ℕ}
    (σ : Equiv.Perm (Fin N)) (q : (Fin N → Z) → ℝ≥0∞) :
    ∫⁻ z, q (fun k => z (σ k)) ∂(Measure.pi fun _ : Fin N => P)
      = ∫⁻ z, q z ∂(Measure.pi fun _ : Fin N => P) := by
  have hpt : ∀ (z : Fin N → Z) (k : Fin N),
      (MeasurableEquiv.piCongrLeft (fun _ : Fin N => Z) σ.symm) z k = z (σ k) := by
    intro z k
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin N => Z) σ.symm z (σ k)
    rwa [Equiv.symm_apply_apply] at h
  have mp := MeasureTheory.measurePreserving_piCongrLeft (fun _ : Fin N => P) σ.symm
  conv_rhs => rw [← mp.map_eq]
  rw [MeasureTheory.lintegral_map_equiv]
  refine lintegral_congr (fun z => ?_)
  congr 1; funext k; exact (hpt z k).symm

@[blueprint "lem:exists-perm-extending-injective"
  (statement := /-- For \(n\leq N\) and an injective index tuple
  \(J:\operatorname{Fin}(n)\to\operatorname{Fin}(N)\), there is a permutation
  \(\sigma\) of \(\operatorname{Fin}(N)\) with \(\sigma(J_i)=\iota(i)\) for all \(i\),
  where \(\iota=\operatorname{castLE}\) is the canonical inclusion of the first \(n\)
  coordinates.  In other words, any injective tuple can be completed to a permutation
  that sends it to the canonical first-\(n\) inclusion. -/)
  (proof := /-- The images of \(J\) and of \(\iota\) both have cardinality \(n\), so
  their complements in \(\operatorname{Fin}(N)\) have equal cardinality and admit an
  equivalence.  Combining the equivalence \(\operatorname{Fin}(n)\simeq\operatorname{range}(J)\)
  transported to \(\operatorname{range}(\iota)\) with a chosen equivalence between the
  complements, through the range/complement decomposition of \(\operatorname{Fin}(N)\),
  produces a permutation mapping \(J_i\) to \(\iota(i)\). -/)
  (title := /-- Extending an injective index tuple to a permutation -/)
  (latexEnv := "lemma")]
lemma exists_perm_extending_injective {n N : ℕ} (hnN : n ≤ N)
    (J : Fin n → Fin N) (hJ : Function.Injective J) :
    ∃ σ : Equiv.Perm (Fin N), ∀ i, σ (J i) = Fin.castLE hnN i := by
  classical
  have hcastLE_inj : Function.Injective (Fin.castLE hnN) := Fin.castLE_injective hnN
  have hcardc : Fintype.card {x // x ∈ (Set.range J)ᶜ}
      = Fintype.card {x // x ∈ (Set.range (Fin.castLE hnN))ᶜ} := by
    rw [Fintype.card_compl_set, Fintype.card_compl_set, Set.card_range_of_injective hJ,
      Set.card_range_of_injective hcastLE_inj]
  let e1 := Equiv.ofInjective J hJ
  let e2 := Equiv.ofInjective (Fin.castLE hnN) hcastLE_inj
  let ec := Fintype.equivOfCardEq hcardc
  refine ⟨(Equiv.Set.sumCompl (Set.range J)).symm.trans
    (((e1.symm.trans e2).sumCongr ec).trans
      (Equiv.Set.sumCompl (Set.range (Fin.castLE hnN)))), ?_⟩
  intro i
  have hJi : J i ∈ Set.range J := ⟨i, rfl⟩
  simp only [Equiv.trans_apply]
  rw [show (Equiv.Set.sumCompl (Set.range J)).symm (J i) = Sum.inl ⟨J i, hJi⟩ from ?_]
  · simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.Set.sumCompl_apply_inl]
    congr 1
    simp only [e1, e2, Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [show (Equiv.ofInjective J hJ).symm ⟨J i, hJi⟩ = i from Equiv.ofInjective_symm_apply hJ i]
    rfl
  · rw [Equiv.symm_apply_eq]; rfl

@[blueprint "lem:empirical-pi-eq-map-uniform"
  (statement := /-- Let \(\mathcal Z\) be a measurable space, let \(N>0\), and fix an
  \(N\)-sample \(z\).  Writing the empirical probability measure as
  \(P_z=N^{-1}\sum_{j}\delta_{z_j}\), the \(n\)-fold product \(P_z^{\,n}\) equals the
  pushforward, under the index map \(x\mapsto(z_{x_i})_i\), of the \(n\)-fold product
  of the uniform index law \(N^{-1}\,\#\) on \(\operatorname{Fin}(N)\):
  \[
    P_z^{\,n}
      =\bigl((x_i)_i\mapsto(z_{x_i})_i\bigr)_{\#}
        \bigl(N^{-1}\,\#\bigr)^{\otimes n}.
  \]
  This is the resampling identity underlying sampling with replacement. -/)
  (proof := /-- The empirical measure is the pushforward of the uniform counting law
  \(N^{-1}\,\#\) under \(j\mapsto z_j\).  Both \(N^{-1}\,\#\) and its pushforward are
  finite, hence \(\sigma\)-finite, so the pushforward commutes with finite products,
  and the product of the pushforwards equals the pushforward of the product under the
  coordinatewise index map. -/)
  (title := /-- Empirical product law as a pushforward of the uniform index law -/)
  (latexEnv := "lemma")]
lemma empirical_pi_eq_map_uniform
    {Z : Type*} [MeasurableSpace Z] {n N : ℕ} (hNpos : 0 < N) (z : Fin N → Z) :
    Measure.pi (fun _ : Fin n => (N : ℝ≥0∞)⁻¹ • ∑ j : Fin N, Measure.dirac (z j))
      = Measure.map (fun (x : Fin n → Fin N) (i : Fin n) => z (x i))
          (Measure.pi (fun _ : Fin n => (N : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.count)) := by
  have hmd : Measurable (fun j => z j : Fin N → Z) := by measurability
  have hmapemp : (N : ℝ≥0∞)⁻¹ • ∑ j : Fin N, Measure.dirac (z j)
      = Measure.map (fun j => z j) ((N : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.count) := by
    rw [MeasureTheory.Measure.map_smul]
    congr 1
    rw [MeasureTheory.Measure.count, MeasureTheory.Measure.map_sum hmd.aemeasurable,
      MeasureTheory.Measure.sum_fintype]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact (MeasureTheory.Measure.map_dirac' hmd j).symm
  haveI hfin : IsFiniteMeasure ((N : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.count : Measure (Fin N)) := by
    constructor
    rw [MeasureTheory.Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (by simp [hNpos]) (by simp [MeasureTheory.Measure.count_apply_finite])
  haveI hsig : ∀ _i : Fin n,
      SigmaFinite (((N : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.count : Measure (Fin N)).map
        (fun j => z j)) := by
    intro _i; infer_instance
  have hpmp := MeasureTheory.Measure.pi_map_pi
    (μ := fun _ : Fin n => (N : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.count)
    (f := fun _ : Fin n => (fun j => z j : Fin N → Z)) (hμ := hsig)
    (fun _ => hmd.aemeasurable)
  rw [hpmp]
  congr 1; funext i; rw [← hmapemp]

set_option maxHeartbeats 200000 in
@[blueprint "lem:source-high-complexity-probability-step"
  (statement := /-- Let \(\mathcal Z\) be a measurable space, let \(\mathcal F\) be a
  model class, and let \(\ell:\mathcal F\times\mathcal Z\to[0,\infty]\) be a loss
  satisfying \(\ell(f,z)<\infty\) for every \(f\in\mathcal F\) and
  \(z\in\mathcal Z\).  Let
  \(\Xi\) be a measurable seed space with probability law \(Q\).  Fix
  \(\alpha\in(0,1)\), integers \(1\leq n\leq N\), a probability measure \(P\) on
  \(\mathcal Z\), and a valid randomized distribution-free lower bound \(L\) at
  level \(\alpha\) in the sense of
  \cref{def:valid-distribution-free-lower-bound}.  For an \(N\)-sample \(z\), write
  \(z|_n=(z_i)_{i\in\operatorname{Fin}(n)}\), using the canonical inclusion
  \(\operatorname{Fin}(n)\hookrightarrow\operatorname{Fin}(N)\), and assume that
  the event
  \(\{(z,\xi):L(z|_n,\xi)>\widehat R_N(\mathcal F,z)\}\) is measurable.  Then
  \[
    (P^N\otimes Q)\bigl\{(z,\xi):L(z|_n,\xi)>\widehat R_N(\mathcal F,z)\bigr\}
      \leq \operatorname{ofReal}(\alpha)+\frac{n^2}{2N},
  \]
  where \(P^N\) and \(\widehat R_N\) are defined in
  \cref{def:iid-sample-law,def:empirical-model-class-risk}; in particular, the
  sample and seed are independent under the displayed product law. -/)
  (proof := /-- Write \(P_z=N^{-1}\sum_{j\in\operatorname{Fin}(N)}\delta_{z_j}\)
  for the empirical probability measure associated with an \(N\)-sample \(z\).
  Conditional on \(z\), draw indices \(J_1,\ldots,J_n\) independently and uniformly
  from \(\operatorname{Fin}(N)\).  Then
  \((z_{J_1},\ldots,z_{J_n})\) has law \(P_z^n\); this identification of the
  empirical product law with the pushforward of the uniform index law is
  \cref{lem:empirical-pi-eq-map-uniform}.  Moreover,
  \[
    R_{P_z}(\mathcal F)
      =\inf_{f\in\mathcal F}\frac1N
        \sum_{j\in\operatorname{Fin}(N)}\ell(f,z_j)
      =\widehat R_N(\mathcal F,z)
  \]
  by \cref{def:population-model-class-risk,def:empirical-model-class-risk}.
  Applying the validity condition
  \cref{def:valid-distribution-free-lower-bound} to the probability measure \(P_z\)
  therefore shows that, conditionally on \(z\), the probability over
  \(J_1,\ldots,J_n\) and the independent seed that
  \(L((z_{J_k})_{k=1}^n,\xi)>\widehat R_N(\mathcal F,z)\) is at most
  \(\operatorname{ofReal}(\alpha)\).  Integrating this conditional inequality over
  \(z\) preserves the same upper bound.

  It remains to replace sampling with replacement by the first \(n\) coordinates of
  the original sample.  Let \(I_1,\ldots,I_n\) be a uniformly ordered sample of
  distinct elements of \(\operatorname{Fin}(N)\), independent of \(z\) and the seed.
  Any such injective tuple extends to a permutation of \(\operatorname{Fin}(N)\)
  carrying it to the canonical first-\(n\) prefix, by
  \cref{lem:exists-perm-extending-injective}, and the coordinate-permutation
  invariance of the i.i.d. sample law
  \cref{lem:sample-law-reindex-lintegral}, a form of exchangeability of the product
  law in \cref{def:iid-sample-law}, identifies the joint law of
  \(((z_{I_k})_{k=1}^n,z,\xi)\), for the comparison event under consideration, with
  that obtained from the first \(n\) coordinates of \(z\).
  Couple \(I=(I_1,\ldots,I_n)\) and \(J=(J_1,\ldots,J_n)\) so that they agree whenever
  the coordinates of \(J\) are all distinct.  The number of injective index tuples
  equals \(N^{\underline n}\) by \cref{lem:card-injective-index-tuples}, and the
  resulting collision count is controlled by the birthday arithmetic of
  \cref{lem:index-collision-bound}.  A union bound over pairs of coordinates
  gives
  \[
    \mathbb P\{J\text{ has a repeated coordinate}\}
      \leq \binom n2\frac1N
      =\frac{n(n-1)}{2N}\leq\frac{n^2}{2N}.
  \]
  Hence the probabilities of every measurable event under the two index-sampling
  schemes differ by at most \(n^2/(2N)\).  Applying this estimate to the stated
  comparison event and adding it to the with-replacement bound proves the displayed
  inequality. -/)
  (title := /-- Isolated high-complexity probability step from the source -/)
  (latexEnv := "lemma")]
lemma source_high_complexity_probability_step
    {Z F Ξ : Type*} [MeasurableSpace Z] [MeasurableSpace Ξ]
    (loss : F → Z → ℝ≥0∞) (hloss_finite : ∀ f z, loss f z ≠ ⊤)
    (α : ℝ) (n N : ℕ)
    (hα_lower : 0 < α) (hα_upper : α < 1)
    (hn : 1 ≤ n) (hnN : n ≤ N)
    (seedLaw : Measure Ξ) (hseed : IsProbabilityMeasure seedLaw)
    (lowerBound : (Fin n → Z) → Ξ → ℝ≥0∞)
    (hvalid : valid_distribution_free_lower_bound loss α n seedLaw hseed lowerBound)
    (hcomparison_measurable : MeasurableSet
      {outcome : (Fin N → Z) × Ξ |
        lowerBound (fun i ↦ outcome.1 (Fin.castLE hnN i)) outcome.2 >
          empirical_model_class_risk loss outcome.1})
    (P : Measure Z) (hP : IsProbabilityMeasure P) :
    (iid_sample_law P N).prod seedLaw
        {outcome |
          lowerBound (fun i ↦ outcome.1 (Fin.castLE hnN i)) outcome.2 >
            empirical_model_class_risk loss outcome.1} ≤
      ENNReal.ofReal α +
        (n : ℝ≥0∞) ^ 2 / (2 * (N : ℝ≥0∞)) := by
  classical
  set μ := (iid_sample_law P N).prod seedLaw with hμ
  set emp : (Fin N → Z) → Measure Z :=
    fun z => (N : ℝ≥0∞)⁻¹ • ∑ j : Fin N, Measure.dirac (z j) with hemp
  have hNpos : 0 < N := lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hn) hnN
  have hNne : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hNtop : (N : ℝ≥0∞) ≠ ∞ := by simp
  have hcastLE_inj : Function.Injective (Fin.castLE hnN) := Fin.castLE_injective hnN
  have hempprob : ∀ w : Fin N → Z, IsProbabilityMeasure (emp w) := by
    intro w
    refine ⟨?_⟩
    simp only [hemp, MeasureTheory.Measure.smul_apply,
      MeasureTheory.Measure.finset_sum_apply, MeasurableSet.univ,
      MeasureTheory.Measure.dirac_apply', Set.mem_univ, Set.indicator_of_mem,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      nsmul_eq_mul, mul_one, Pi.one_apply]
    rw [ENNReal.inv_mul_cancel hNne (by simp)]
  have hmapemp : ∀ z : Fin N → Z,
      emp z = Measure.map (fun j => z j) ((N : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.count) := by
    intro z
    have hmd : Measurable (fun j => z j : Fin N → Z) := by measurability
    simp only [hemp]
    rw [MeasureTheory.Measure.map_smul]
    congr 1
    rw [MeasureTheory.Measure.count, MeasureTheory.Measure.map_sum hmd.aemeasurable,
      MeasureTheory.Measure.sum_fintype]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact (MeasureTheory.Measure.map_dirac' hmd j).symm
  have hperm : ∀ (z : Fin N → Z) (σ : Equiv.Perm (Fin N)),
      empirical_model_class_risk loss (fun k => z (σ k)) = empirical_model_class_risk loss z := by
    intro z σ
    unfold empirical_model_class_risk
    refine iInf_congr (fun f => ?_)
    rw [Equiv.sum_comp σ (fun k => loss f (z k))]
  have hpople : ∀ z : Fin N → Z,
      population_model_class_risk loss (emp z) ≤ empirical_model_class_risk loss z := by
    intro z
    simp only [hemp]
    unfold population_model_class_risk empirical_model_class_risk
    refine iInf_mono (fun f => ?_)
    rw [MeasureTheory.lintegral_smul_measure, MeasureTheory.lintegral_finsetSum_measure,
      ENNReal.div_eq_inv_mul, smul_eq_mul]
    apply mul_le_mul_left'
    apply Finset.sum_le_sum
    intro i _
    rw [MeasureTheory.lintegral]
    refine iSup₂_le (fun s hs => ?_)
    rw [MeasureTheory.SimpleFunc.lintegral, Finset.sum_eq_single (s (z i))]
    · rw [Measure.dirac_apply' _ (s.measurableSet_preimage _)]
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.indicator_of_mem,
        Pi.one_apply, mul_one]
      exact hs (z i)
    · intro b hb hbne
      rw [Measure.dirac_apply' _ (s.measurableSet_preimage _),
        Set.indicator_of_notMem (by simp [hbne.symm]), mul_zero]
    · intro h
      simp only [MeasureTheory.SimpleFunc.mem_range, Set.mem_range, not_exists] at h
      exact absurd rfl (h (z i))
  have hvalidbound : ∀ z : Fin N → Z,
      ((Measure.pi (fun _ : Fin n => emp z)).prod seedLaw)
          {o : (Fin n → Z) × Ξ |
            lowerBound o.1 o.2 > population_model_class_risk loss (emp z)} ≤ ENNReal.ofReal α := by
    intro z
    haveI := hempprob z
    obtain ⟨hmeas, hge⟩ := hvalid (emp z) (hempprob z)
    have hcompl : ((Measure.pi (fun _ : Fin n => emp z)).prod seedLaw)
        {o : (Fin n → Z) × Ξ | lowerBound o.1 o.2 > population_model_class_risk loss (emp z)}
        = 1 - ((Measure.pi (fun _ : Fin n => emp z)).prod seedLaw)
            {o : (Fin n → Z) × Ξ |
              population_model_class_risk loss (emp z) ≥ lowerBound o.1 o.2} := by
      rw [← MeasureTheory.prob_compl_eq_one_sub hmeas]
      congr 1
      ext o
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    rw [hcompl]
    have hrw : (1 : ℝ≥0∞) - ENNReal.ofReal (1 - α) = ENNReal.ofReal α := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
      congr 1; ring
    calc 1 - ((Measure.pi (fun _ : Fin n => emp z)).prod seedLaw)
            {o : (Fin n → Z) × Ξ |
              population_model_class_risk loss (emp z) ≥ lowerBound o.1 o.2}
        ≤ 1 - ENNReal.ofReal (1 - α) := by
          apply tsub_le_tsub_left
          rw [iid_sample_law] at hge
          exact hge
      _ = ENNReal.ofReal α := hrw
  have hlaw : iid_sample_law P N = Measure.pi (fun _ : Fin N => P) := rfl
  have reindex : ∀ (σ : Equiv.Perm (Fin N)) (q : (Fin N → Z) → ℝ≥0∞),
      ∫⁻ z, q (fun k => z (σ k)) ∂(Measure.pi fun _ : Fin N => P)
        = ∫⁻ z, q z ∂(Measure.pi fun _ : Fin N => P) :=
    fun σ q => sample_law_reindex_lintegral P σ q
  have hpg : ∀ (z : Fin N → Z) (J : Fin n → Fin N),
      seedLaw {ξ | lowerBound (fun i => z (J i)) ξ > empirical_model_class_risk loss z}
        ≤ seedLaw {ξ | lowerBound (fun i => z (J i)) ξ >
            population_model_class_risk loss (emp z)} := by
    intro z J
    apply measure_mono
    intro ξ hξ
    exact lt_of_le_of_lt (hpople z) hξ
  have hμS : μ {outcome : (Fin N → Z) × Ξ |
        lowerBound (fun i => outcome.1 (Fin.castLE hnN i)) outcome.2 >
          empirical_model_class_risk loss outcome.1}
      = ∫⁻ z, seedLaw {ξ | lowerBound (fun i => z (Fin.castLE hnN i)) ξ >
          empirical_model_class_risk loss z} ∂(Measure.pi fun _ : Fin N => P) := by
    rw [hμ, hlaw, MeasureTheory.Measure.prod_apply hcomparison_measurable]
    rfl
  have experm : ∀ (J : Fin n → Fin N), Function.Injective J →
      ∃ σ : Equiv.Perm (Fin N), ∀ i, σ (J i) = Fin.castLE hnN i :=
    fun J hJ => exists_perm_extending_injective hnN J hJ
  have hFinj : ∀ J : Fin n → Fin N, Function.Injective J →
      ∫⁻ z, seedLaw {ξ | lowerBound (fun i => z (J i)) ξ >
          empirical_model_class_risk loss z} ∂(Measure.pi fun _ : Fin N => P)
        = μ {outcome : (Fin N → Z) × Ξ |
            lowerBound (fun i => outcome.1 (Fin.castLE hnN i)) outcome.2 >
              empirical_model_class_risk loss outcome.1} := by
    intro J hJ
    obtain ⟨σ, hσ⟩ := experm J hJ
    rw [hμS]
    have hre := reindex σ (fun z => seedLaw {ξ | lowerBound (fun i => z (J i)) ξ >
        empirical_model_class_risk loss z})
    rw [← hre]
    refine lintegral_congr (fun z => ?_)
    have hidx : (fun i => (fun k => z (σ k)) (J i)) = (fun i => z (Fin.castLE hnN i)) := by
      funext i; simp only; rw [hσ i]
    rw [hidx, hperm z σ]
  have hpiemp : ∀ z : Fin N → Z,
      Measure.pi (fun _ : Fin n => emp z)
        = Measure.map (fun (x : Fin n → Fin N) (i : Fin n) => z (x i))
            (Measure.pi (fun _ : Fin n => (N : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.count)) :=
    fun z => empirical_pi_eq_map_uniform hNpos z
  have hkey : ∀ z : Fin N → Z,
      ∑ J : Fin n → Fin N, (((N : ℝ≥0∞)⁻¹) ^ n) *
          seedLaw {ξ | lowerBound (fun i => z (J i)) ξ >
            population_model_class_risk loss (emp z)} ≤ ENNReal.ofReal α := by
    intro z
    haveI : IsFiniteMeasure ((N : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.count : Measure (Fin N)) := by
      constructor
      rw [MeasureTheory.Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top (by simp [hNpos]) (by simp [MeasureTheory.Measure.count_apply_finite])
    have hgoodmeas : MeasurableSet
        {o : (Fin n → Z) × Ξ | lowerBound o.1 o.2 > population_model_class_risk loss (emp z)} := by
      obtain ⟨hmeas, _⟩ := hvalid (emp z) (hempprob z)
      have hcset : {o : (Fin n → Z) × Ξ |
          lowerBound o.1 o.2 > population_model_class_risk loss (emp z)}
          = {o | population_model_class_risk loss (emp z) ≥ lowerBound o.1 o.2}ᶜ := by
        ext o; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
      rw [hcset]; exact hmeas.compl
    calc ∑ J : Fin n → Fin N, (((N : ℝ≥0∞)⁻¹) ^ n) *
            seedLaw {ξ | lowerBound (fun i => z (J i)) ξ >
              population_model_class_risk loss (emp z)}
        = ((Measure.pi (fun _ : Fin n => emp z)).prod seedLaw)
            {o : (Fin n → Z) × Ξ |
              lowerBound o.1 o.2 > population_model_class_risk loss (emp z)} := by
          rw [MeasureTheory.Measure.prod_apply hgoodmeas, hpiemp z,
            MeasureTheory.lintegral_map (measurable_measure_prodMk_left hgoodmeas) (by measurability),
            MeasureTheory.lintegral_fintype]
          refine Finset.sum_congr rfl (fun J _ => ?_)
          rw [mul_comm]
          congr 1
          have hset : ({J} : Set (Fin n → Fin N)) = Set.univ.pi (fun i => {J i}) := by
            ext x; simp [funext_iff, eq_comm]
          rw [hset, MeasureTheory.Measure.pi_pi]
          simp only [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.count_singleton,
            smul_eq_mul, mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ENNReal.ofReal α := hvalidbound z
  have hsuperadd : ∀ (s : Finset (Fin n → Fin N)) (G : (Fin n → Fin N) → (Fin N → Z) → ℝ≥0∞),
      ∑ J ∈ s, (∫⁻ z, G J z ∂(Measure.pi fun _ : Fin N => P))
        ≤ ∫⁻ z, ∑ J ∈ s, G J z ∂(Measure.pi fun _ : Fin N => P) := by
    intro s G
    classical
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      calc (∫⁻ z, G a z ∂(Measure.pi fun _ : Fin N => P))
              + ∑ J ∈ s, (∫⁻ z, G J z ∂(Measure.pi fun _ : Fin N => P))
          ≤ (∫⁻ z, G a z ∂(Measure.pi fun _ : Fin N => P))
              + ∫⁻ z, ∑ J ∈ s, G J z ∂(Measure.pi fun _ : Fin N => P) := by gcongr
        _ ≤ ∫⁻ z, G a z + ∑ J ∈ s, G J z ∂(Measure.pi fun _ : Fin N => P) :=
            MeasureTheory.le_lintegral_add _ _
        _ = ∫⁻ z, ∑ J ∈ insert a s, G J z ∂(Measure.pi fun _ : Fin N => P) := by
            refine lintegral_congr (fun z => ?_); rw [Finset.sum_insert ha]
  have hcardinj :
      (Finset.univ.filter (fun J : Fin n → Fin N => Function.Injective J)).card
        = N.descFactorial n := card_injective_index_tuples n N
  set G : (Fin n → Fin N) → (Fin N → Z) → ℝ≥0∞ :=
    fun J z => seedLaw {ξ | lowerBound (fun i => z (J i)) ξ >
      population_model_class_risk loss (emp z)} with hG
  set T := μ {outcome : (Fin N → Z) × Ξ |
      lowerBound (fun i => outcome.1 (Fin.castLE hnN i)) outcome.2 >
        empirical_model_class_risk loss outcome.1} with hT
  haveI : IsProbabilityMeasure (iid_sample_law P N) := by rw [hlaw]; infer_instance
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hTle1 : T ≤ 1 := prob_le_one
  have hNpowne : (N : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero n hNne
  have hNpowtop : (N : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top hNtop
  have hdescE : (N.descFactorial n : ℝ≥0∞) ≤ (N : ℝ≥0∞) ^ n := by
    have := Nat.descFactorial_le_pow N n
    calc (N.descFactorial n : ℝ≥0∞) ≤ ((N ^ n : ℕ) : ℝ≥0∞) := by exact_mod_cast this
      _ = (N : ℝ≥0∞) ^ n := by push_cast; ring
  have hpowcancel : ((N : ℝ≥0∞) ^ n) * (((N : ℝ≥0∞)⁻¹) ^ n) = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel hNne hNtop, one_pow]
  have hGsum : ∀ z : Fin N → Z,
      ∑ J : Fin n → Fin N, G J z ≤ (N : ℝ≥0∞) ^ n * ENNReal.ofReal α := by
    intro z
    have hk := hkey z
    rw [← Finset.mul_sum] at hk
    calc ∑ J : Fin n → Fin N, G J z
        = ((N : ℝ≥0∞) ^ n * ((N : ℝ≥0∞)⁻¹) ^ n) * ∑ J : Fin n → Fin N, G J z := by
          rw [hpowcancel, one_mul]
      _ = (N : ℝ≥0∞) ^ n * (((N : ℝ≥0∞)⁻¹) ^ n * ∑ J : Fin n → Fin N, G J z) := by rw [mul_assoc]
      _ ≤ (N : ℝ≥0∞) ^ n * ENNReal.ofReal α := mul_le_mul_left' hk _
  have hInjT : ∀ J : Fin n → Fin N, Function.Injective J →
      T ≤ ∫⁻ z, G J z ∂(Measure.pi fun _ : Fin N => P) := by
    intro J hJ
    rw [← hFinj J hJ]
    exact lintegral_mono (fun z => hpg z J)
  have hA : (N.descFactorial n : ℝ≥0∞) * T ≤ (N : ℝ≥0∞) ^ n * ENNReal.ofReal α := by
    calc (N.descFactorial n : ℝ≥0∞) * T
        = ((Finset.univ.filter (fun J : Fin n → Fin N => Function.Injective J)).card : ℝ≥0∞) * T := by
          rw [hcardinj]
      _ = ∑ J ∈ Finset.univ.filter (fun J : Fin n → Fin N => Function.Injective J), T := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ J ∈ Finset.univ.filter (fun J : Fin n → Fin N => Function.Injective J),
            ∫⁻ z, G J z ∂(Measure.pi fun _ : Fin N => P) := by
          apply Finset.sum_le_sum; intro J hJmem; exact hInjT J (Finset.mem_filter.mp hJmem).2
      _ ≤ ∑ J : Fin n → Fin N, ∫⁻ z, G J z ∂(Measure.pi fun _ : Fin N => P) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro J _ _; exact zero_le'
      _ ≤ ∫⁻ z, ∑ J : Fin n → Fin N, G J z ∂(Measure.pi fun _ : Fin N => P) := hsuperadd Finset.univ G
      _ ≤ ∫⁻ _z : Fin N → Z, (N : ℝ≥0∞) ^ n * ENNReal.ofReal α ∂(Measure.pi fun _ : Fin N => P) :=
          lintegral_mono (fun z => hGsum z)
      _ = (N : ℝ≥0∞) ^ n * ENNReal.ofReal α := by
          rw [MeasureTheory.lintegral_const, measure_univ, mul_one]
  have hNT : (N : ℝ≥0∞) ^ n * T
      = (N.descFactorial n : ℝ≥0∞) * T + ((N : ℝ≥0∞) ^ n - (N.descFactorial n : ℝ≥0∞)) * T := by
    rw [← add_mul, add_tsub_cancel_of_le hdescE]
  have hsplit : (N : ℝ≥0∞) ^ n * T ≤
      (N : ℝ≥0∞) ^ n * ENNReal.ofReal α + ((N : ℝ≥0∞) ^ n - (N.descFactorial n : ℝ≥0∞)) := by
    rw [hNT]
    apply add_le_add hA
    calc ((N : ℝ≥0∞) ^ n - (N.descFactorial n : ℝ≥0∞)) * T
        ≤ ((N : ℝ≥0∞) ^ n - (N.descFactorial n : ℝ≥0∞)) * 1 := mul_le_mul_left' hTle1 _
      _ = (N : ℝ≥0∞) ^ n - (N.descFactorial n : ℝ≥0∞) := mul_one _
  have hdle : N.descFactorial n ≤ N ^ n := Nat.descFactorial_le_pow N n
  have hcolnat : 2 * N * (N ^ n - N.descFactorial n) ≤ n ^ 2 * N ^ n := by
    have hcol := index_collision_bound N n; rw [Nat.mul_sub]; omega
  have h2Nne : (2 * (N : ℝ≥0∞)) ≠ 0 := by simp [hNne]
  have h2Ntop : (2 * (N : ℝ≥0∞)) ≠ ∞ := ENNReal.mul_ne_top (by simp) hNtop
  have hcolE : ((N : ℝ≥0∞) ^ n - (N.descFactorial n : ℝ≥0∞)) * (2 * (N : ℝ≥0∞))
      ≤ (N : ℝ≥0∞) ^ n * (n : ℝ≥0∞) ^ 2 := by
    have hcast := (Nat.cast_le (α := ℝ≥0∞)).mpr hcolnat
    push_cast [Nat.cast_sub hdle] at hcast
    calc ((N : ℝ≥0∞) ^ n - (N.descFactorial n : ℝ≥0∞)) * (2 * (N : ℝ≥0∞))
        = 2 * (N : ℝ≥0∞) * ((N : ℝ≥0∞) ^ n - (N.descFactorial n : ℝ≥0∞)) := by ring
      _ ≤ (n : ℝ≥0∞) ^ 2 * (N : ℝ≥0∞) ^ n := hcast
      _ = (N : ℝ≥0∞) ^ n * (n : ℝ≥0∞) ^ 2 := by ring
  have hfrac : ((N : ℝ≥0∞) ^ n - (N.descFactorial n : ℝ≥0∞))
      ≤ (N : ℝ≥0∞) ^ n * ((n : ℝ≥0∞) ^ 2 / (2 * (N : ℝ≥0∞))) := by
    rw [← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl h2Nne) (Or.inl h2Ntop)]
    exact hcolE
  apply (ENNReal.mul_le_mul_iff_right hNpowne hNpowtop).mp
  rw [mul_add]
  calc (N : ℝ≥0∞) ^ n * T
      ≤ (N : ℝ≥0∞) ^ n * ENNReal.ofReal α + ((N : ℝ≥0∞) ^ n - (N.descFactorial n : ℝ≥0∞)) := hsplit
    _ ≤ (N : ℝ≥0∞) ^ n * ENNReal.ofReal α
          + (N : ℝ≥0∞) ^ n * ((n : ℝ≥0∞) ^ 2 / (2 * (N : ℝ≥0∞))) := by gcongr

@[blueprint "thm:high-complexity"
  (statement := /-- Fix \(\alpha\in(0,1)\), an integer \(n\geq1\), a measurable data
  space \(\mathcal Z\), a measurable random-seed space \(\Xi\) with probability law
  \(Q\), a model class \(\mathcal F\), a loss
  \(\ell:\mathcal F\times\mathcal Z\to[0,\infty]\) satisfying
  \(\ell(f,z)<\infty\) for every \(f\in\mathcal F\) and \(z\in\mathcal Z\), and a
  valid randomized
  distribution-free lower bound \(L\) on the model-class risk.  For every
  probability measure \(P\) on \(\mathcal Z\) and every integer \(N\geq n\), assume
  that the event
  \(\{(z,\xi):L(z|_n,\xi)>\widehat R_N(\mathcal F,z)\}\) is measurable.  Then
  \[
    (P^N\otimes Q)\bigl\{(z,\xi):L(z|_n,\xi)>\widehat R_N(\mathcal F,z)\bigr\}
      \leq \operatorname{ofReal}(\alpha)+\frac{n^2}{2N}.
  \]
  Here \(z|_n\) denotes the first \(n\) coordinates, and the product law makes the
  seed independent of the \(N\) observations.  A one-point seed space yields the
  deterministic formulation. -/)
  (proof := /-- All hypotheses of
  \cref{lem:source-high-complexity-probability-step} hold for the fixed pointwise
  finite loss, error level, sample sizes, seed law, randomized lower-bound procedure,
  comparison-event measurability assumption, and probability measure.  Applying
  that lemma with the canonical embedding of the first \(n\) coordinates into the
  \(N\)-sample and with the same independent seed gives the asserted inequality. -/)
  (title := /-- Fundamental limit for distribution-free empirical model falsification -/)
  (latexEnv := "theorem")]
theorem high_complexity
    {Z F Ξ : Type*} [MeasurableSpace Z] [MeasurableSpace Ξ]
    (loss : F → Z → ℝ≥0∞) (hloss_finite : ∀ f z, loss f z ≠ ⊤)
    (α : ℝ) (n N : ℕ)
    (hα_lower : 0 < α) (hα_upper : α < 1)
    (hn : 1 ≤ n) (hnN : n ≤ N)
    (seedLaw : Measure Ξ) (hseed : IsProbabilityMeasure seedLaw)
    (lowerBound : (Fin n → Z) → Ξ → ℝ≥0∞)
    (hvalid : valid_distribution_free_lower_bound loss α n seedLaw hseed lowerBound)
    (hcomparison_measurable : MeasurableSet
      {outcome : (Fin N → Z) × Ξ |
        lowerBound (fun i ↦ outcome.1 (Fin.castLE hnN i)) outcome.2 >
          empirical_model_class_risk loss outcome.1})
    (P : Measure Z) (hP : IsProbabilityMeasure P) :
    (iid_sample_law P N).prod seedLaw
        {outcome |
          lowerBound (fun i ↦ outcome.1 (Fin.castLE hnN i)) outcome.2 >
            empirical_model_class_risk loss outcome.1} ≤
      ENNReal.ofReal α +
        (n : ℝ≥0∞) ^ 2 / (2 * (N : ℝ≥0∞)) := by
  exact source_high_complexity_probability_step loss hloss_finite α n N hα_lower hα_upper
    hn hnN seedLaw hseed lowerBound hvalid hcomparison_measurable P hP

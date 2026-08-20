import Architect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators
open MeasureTheory

@[blueprint "def:oco-point"
  (statement := /-- For a dimension \(d\in\mathbb{N}\), the decision space is the Euclidean
  space \(\mathbb{R}^{d}\), represented as the space of functions from \(\operatorname{Fin}(d)\)
  to \(\mathbb{R}\). -/)
  (title := /-- Euclidean decision space -/)
  (latexEnv := "definition")]
abbrev oco_point (d : ℕ) := Fin d → ℝ

@[blueprint "def:continuous-hedge-learning-rate"
  (statement := /-- For a dimension \(d\) and a horizon \(T\), define the learning rate
  \[
    \eta(d,T)=\min\left\{1,\,
      T^{-1/3}\bigl(d\log T\bigr)^{1/3}\right\}.
  \]
  All powers in this formula are real powers. -/)
  (title := /-- Learning rate for Continuous Hedge -/)
  (latexEnv := "definition")]
noncomputable def continuous_hedge_learning_rate (d T : ℕ) : ℝ :=
  min 1
    (Real.rpow (T : ℝ) (-(1 : ℝ) / 3) *
      Real.rpow ((d : ℝ) * Real.log (T : ℝ)) ((1 : ℝ) / 3))

@[blueprint "def:continuous-hedge-weight-measure"
  (statement := /-- Let \(\mathcal X\subseteq\mathbb{R}^{d}\), let
  \(f_s:\mathbb{R}^{d}\to\mathbb{R}\) be a sequence of losses, and let \(\eta\in\mathbb{R}\).
  Let \(k\) be the dimension of the direction space of the affine hull of \(\mathcal X\),
  and let \(\mathcal H^k_{\mathrm E}\) denote Euclidean-normalized \(k\)-dimensional
  Hausdorff measure on \(\mathbb{R}^d\). At time \(t\), the unnormalized Continuous Hedge
  measure is the restriction of \(\mathcal H^k_{\mathrm E}\) to \(\mathcal X\), with density
  \[
    y\longmapsto
    \exp\left(-\eta\sum_{s=0}^{t-1} f_s(y)\right).
  \]
  This intrinsic choice agrees with Lebesgue measure when \(\mathcal X\) has full affine
  dimension. If \(\mathcal X\) is lower-dimensional, it instead measures \(\mathcal X\) in
  its own affine dimension; in particular, the reference measure assigns mass one to a singleton.
  The real-valued density is embedded in \(\mathbb{R}_{\geq 0}\cup\{\infty\}\) in order to use
  Mathlib's measure-with-density construction. -/)
  (title := /-- Unnormalized exponential-weights measure -/)
  (latexEnv := "definition")]
noncomputable def continuous_hedge_weight_measure {d : ℕ}
    (X : Set (oco_point d)) (loss : ℕ → oco_point d → ℝ) (η : ℝ) (t : ℕ) :
    Measure (oco_point d) :=
  ((MeasureTheory.Measure.euclideanHausdorffMeasure
      (Module.finrank ℝ (affineSpan ℝ X).direction)).restrict X).withDensity fun y =>
    ENNReal.ofReal (Real.exp (-η * ∑ s ∈ Finset.range t, loss s y))

@[blueprint "def:continuous-hedge-distribution"
  (statement := /-- With the notation of
  \cref{def:continuous-hedge-weight-measure}, let \(\mu_t\) be the unnormalized
  exponential-weights measure.  If \(0<\mu_t(\mathbb{R}^{d})<\infty\), the Continuous
  Hedge distribution at time \(t\) is
  \[
    p_t=\mu_t(\mathbb{R}^{d})^{-1}\mu_t.
  \]
  If this normalization is unavailable and \(\mathcal X\) is nonempty, fix
  \(x_*\in\mathcal X\) and set \(p_t=\delta_{x_*}\).  For the irrelevant case
  \(\mathcal X=\varnothing\), set \(p_t=0\).  Thus the definition agrees with the paper's
  exponential-weights distribution whenever that distribution is well-defined and otherwise
  remains a probability measure on every nonempty decision domain. -/)
  (title := /-- Normalized Continuous Hedge distribution -/)
  (latexEnv := "definition")]
noncomputable def continuous_hedge_distribution {d : ℕ}
    (X : Set (oco_point d)) (loss : ℕ → oco_point d → ℝ) (η : ℝ) (t : ℕ) :
    Measure (oco_point d) :=
  letI : Decidable X.Nonempty := Classical.propDecidable _
  let μ := continuous_hedge_weight_measure X loss η t
  if hX : X.Nonempty then
    if μ Set.univ ≠ 0 ∧ μ Set.univ ≠ ⊤ then
      (μ Set.univ)⁻¹ • μ
    else
      Measure.dirac hX.choose
  else
    0

@[blueprint "def:is-continuous-hedge"
  (statement := /-- Fix a horizon \(T\), a domain \(\mathcal X\subseteq\mathbb{R}^{d}\),
  losses \(f_t:\mathbb{R}^{d}\to\mathbb{R}\), and a learning rate \(\eta\).  A pair
  \((p,x)\), consisting of measures \(p_t\) and actions \(x_t\), is a Continuous Hedge
  execution through time \(T\) if, for every \(0\leq t\leq T\), the measure \(p_t\) is the
  distribution from \cref{def:continuous-hedge-distribution}, is a probability measure
  supported on \(\mathcal X\), the identity map is Bochner integrable under \(p_t\), and
  \[
    x_t=\int_{\mathbb{R}^{d}} y\,dp_t(y)\in\mathcal X.
  \]
  The index \(t=T\) supplies the extra action used in alternating regret. -/)
  (title := /-- Continuous Hedge execution -/)
  (latexEnv := "definition")]
def is_continuous_hedge {d : ℕ} (T : ℕ) (X : Set (oco_point d))
    (loss : ℕ → oco_point d → ℝ) (η : ℝ)
    (p : ℕ → Measure (oco_point d)) (x : ℕ → oco_point d) : Prop :=
  ∀ t, t ≤ T →
    p t = continuous_hedge_distribution X loss η t ∧
      IsProbabilityMeasure (p t) ∧
      p t (Xᶜ) = 0 ∧
      Integrable (fun y => y) (p t) ∧
      x t = integral (p t) (fun y => y) ∧
      x t ∈ X

@[blueprint "def:comparator-alternating-regret"
  (statement := /-- For a horizon \(T\), losses \(f_t\), actions \(x_0,\ldots,x_T\), and
  a comparator \(u\), define the alternating regret against \(u\) by
  \[
    \operatorname{Reg}_{\mathrm{Alt}}(u)
      =\sum_{t=0}^{T-1}
        \bigl(f_t(x_t)+f_t(x_{t+1})-2f_t(u)\bigr).
  \]
  This is the sum of standard regret and cheating regret. -/)
  (title := /-- Alternating regret against one comparator -/)
  (latexEnv := "definition")]
def comparator_alternating_regret {d : ℕ} (T : ℕ)
    (loss : ℕ → oco_point d → ℝ) (x : ℕ → oco_point d) (u : oco_point d) : ℝ :=
  ∑ t ∈ Finset.range T, (loss t (x t) + loss t (x (t + 1)) - 2 * loss t u)

@[blueprint "def:alternating-regret"
  (statement := /-- For a decision domain \(\mathcal X\), the worst-case alternating regret is
  \[
    \operatorname{Reg}_{\mathrm{Alt}}
      =\sup_{u\in\mathcal X}\operatorname{Reg}_{\mathrm{Alt}}(u),
  \]
  where the comparator regret is defined in
  \cref{def:comparator-alternating-regret}.  The supremum formulation agrees with the paper's
  maximum whenever a maximizing comparator exists and remains meaningful without an
  attainment assumption. -/)
  (title := /-- Worst-case alternating regret -/)
  (latexEnv := "definition")]
noncomputable def alternating_regret {d : ℕ} (T : ℕ) (X : Set (oco_point d))
    (loss : ℕ → oco_point d → ℝ) (x : ℕ → oco_point d) : ℝ :=
  sSup (comparator_alternating_regret T loss x '' X)

@[blueprint "def:continuous-hedge-rate"
  (statement := /-- For dimension \(d\) and horizon \(T\), define
  \[
    R(d,T)=d^{2/3}T^{1/3}(\log T)^{2/3}.
  \]
  This is the rate appearing in the claimed Continuous Hedge bound. -/)
  (title := /-- Claimed alternating-regret rate -/)
  (latexEnv := "definition")]
noncomputable def continuous_hedge_rate (d T : ℕ) : ℝ :=
  Real.rpow (d : ℝ) ((2 : ℝ) / 3) *
    Real.rpow (T : ℝ) ((1 : ℝ) / 3) *
      Real.rpow (Real.log (T : ℝ)) ((2 : ℝ) / 3)

@[blueprint "def:continuous-hedge-log-mass"
  (statement := /-- For a decision domain \(\mathcal X\), losses \(f_s\), learning rate
  \(\eta\), and time \(t\), let
  \[
    \Phi_t=\log\mu_t(\mathbb R^d),
  \]
  where \(\mu_t\) is the unnormalized intrinsic exponential-weights measure from
  \cref{def:continuous-hedge-weight-measure}.  The extended-real mass is converted to a real
  number before taking the logarithm.  In every subsequent use the mass is assumed strictly
  positive and finite, so this agrees with the ordinary log-partition function. -/)
  (title := /-- Continuous Hedge log-partition function -/)
  (latexEnv := "definition")]
noncomputable def continuous_hedge_log_mass {d : ℕ}
    (X : Set (oco_point d)) (loss : ℕ → oco_point d → ℝ) (η : ℝ) (t : ℕ) : ℝ :=
  Real.log ((continuous_hedge_weight_measure X loss η t Set.univ).toReal)

@[blueprint "lem:continuous-hedge-convex-loss-regularity"
  (statement := /-- Let \(\mathcal X\subseteq\mathbb R^d\) be convex, let
  \(k=\dim(\operatorname{dir}(\operatorname{aff}\mathcal X))\), and let
  \(\lambda=\mathcal H^k_{\mathrm E}|_{\mathcal X}\) be Euclidean-normalized intrinsic
  Hausdorff measure restricted to \(\mathcal X\).  If \(f:\mathbb R^d\to\mathbb R\) is
  convex on \(\mathcal X\), then \(f\) is almost everywhere measurable with respect to
  \(\lambda\). -/)
  (proof := /-- If \(\mathcal X\) is empty, the restricted measure is zero and the
  assertion is immediate.  Otherwise choose \(p\in\mathcal X\), put
  \(A=\operatorname{aff}\mathcal X\), and let \(V=\operatorname{dir}(A)\).  Translation
  by \(p\), followed by the inclusion of \(A\) into \(\mathbb R^d\), gives an affine
  isometric embedding \(q:V\to\mathbb R^d\) with range \(A\).  Set
  \(C=q^{-1}(\mathcal X)\) and \(g=f\circ q\).  Since \(q\) is affine, \(C\) is convex
  and \(g\) is convex on \(C\).

  Write \(k=\dim V\).  Euclidean-normalized \(k\)-dimensional Hausdorff measure on
  \(V\) is an additive Haar measure.  Thus \(C\), and for every \(r\in\mathbb R\) the
  convex sublevel set \(\{v\in C:g(v)\leq r\}\), are null measurable.  The restriction
  identity for null measurable sets therefore shows that every lower-ray preimage
  \(g^{-1}(({-\infty},r])\) is null measurable for the measure
  \(\mathcal H^k_{\mathrm E}|_C\).  Since lower rays generate the Borel sigma-algebra of
  \(\mathbb R\), \(g\) is null measurable and hence almost everywhere measurable for
  this restricted measure.

  Finally, isometric invariance of Euclidean Hausdorff measure gives
  \(q_*(\mathcal H^k_{\mathrm E})=\mathcal H^k_{\mathrm E}|_A\).  Because
  \(\mathcal X\subseteq A\), restricting this identity to \(\mathcal X\) yields
  \(q_*(\mathcal H^k_{\mathrm E}|_C)=\mathcal H^k_{\mathrm E}|_{\mathcal X}\).
  Almost-everywhere measurability transports through the measurable embedding \(q\),
  and \(g=f\circ q\); hence \(f\) is almost everywhere measurable for
  \(\mathcal H^k_{\mathrm E}|_{\mathcal X}\). -/)
  (title := /-- Intrinsic measurability of a convex loss -/)
  (latexEnv := "lemma")]
lemma continuous_hedge_convex_loss_regularity {d : ℕ}
    (X : Set (oco_point d)) (f : oco_point d → ℝ)
    (hconv : Convex ℝ X) (hf : ConvexOn ℝ X f) :
    AEMeasurable f
      ((MeasureTheory.Measure.euclideanHausdorffMeasure
        (Module.finrank ℝ (affineSpan ℝ X).direction)).restrict X) := by
  classical
  by_cases hX : X.Nonempty
  · let s : AffineSubspace ℝ (oco_point d) := affineSpan ℝ X
    let p : s := ⟨hX.choose, subset_affineSpan ℝ X hX.choose_spec⟩
    letI : Nonempty s := ⟨p⟩
    let e : s.direction ≃ᵢ s := IsometryEquiv.vaddConst p
    let q : s.direction → oco_point d := fun v => (e v : s)
    let C : Set s.direction := q ⁻¹' X
    let g : s.direction → ℝ := f ∘ q
    have hsmeas : MeasurableSet (s : Set (oco_point d)) :=
      (AffineSubspace.closed_of_finiteDimensional s).measurableSet
    have hq : MeasurableEmbedding q := by
      dsimp [q]
      exact (MeasurableEmbedding.subtype_coe hsmeas).comp
        e.toHomeomorph.measurableEmbedding
    let qA : s.direction →ᵃ[ℝ] oco_point d :=
      { toFun := q
        linear := s.direction.subtype
        map_vadd' := by
          intro v x
          simp [q, e, add_assoc] }
    have hg : ConvexOn ℝ C g := by
      simpa [C, g, qA] using hf.comp_affineMap qA
    have hCnull : NullMeasurableSet C
        (MeasureTheory.Measure.euclideanHausdorffMeasure
          (Module.finrank ℝ s.direction) : Measure s.direction) :=
      hg.1.nullMeasurableSet (μ :=
        (MeasureTheory.Measure.euclideanHausdorffMeasure
          (Module.finrank ℝ s.direction) : Measure s.direction))
    have hg_ae : AEMeasurable g
        ((MeasureTheory.Measure.euclideanHausdorffMeasure
          (Module.finrank ℝ s.direction) : Measure s.direction).restrict C) := by
      apply MeasureTheory.NullMeasurable.aemeasurable
      change @Measurable
        (MeasureTheory.NullMeasurableSpace s.direction
          ((MeasureTheory.Measure.euclideanHausdorffMeasure
            (Module.finrank ℝ s.direction) : Measure s.direction).restrict C)) ℝ _ _ g
      apply measurable_of_Iic
      intro r
      change NullMeasurableSet (g ⁻¹' Set.Iic r)
        ((MeasureTheory.Measure.euclideanHausdorffMeasure
          (Module.finrank ℝ s.direction) : Measure s.direction).restrict C)
      rw [nullMeasurableSet_restrict hCnull]
      convert (hg.convex_le r).nullMeasurableSet (μ :=
        (MeasureTheory.Measure.euclideanHausdorffMeasure
          (Module.finrank ℝ s.direction) : Measure s.direction)) using 1
      ext x
      simp [and_comm]
    have hq_isom : Isometry q := by
      intro x y
      simpa [q] using (isometry_subtype_coe.comp e.isometry x y)
    have hrange : Set.range q = (s : Set (oco_point d)) := by
      ext x
      constructor
      · rintro ⟨v, rfl⟩
        exact (e v).property
      · intro hx
        refine ⟨e.symm ⟨x, hx⟩, ?_⟩
        simp [q]
    have hmap_full :
        (MeasureTheory.Measure.euclideanHausdorffMeasure
          (Module.finrank ℝ s.direction) : Measure s.direction).map q =
        (MeasureTheory.Measure.euclideanHausdorffMeasure
          (Module.finrank ℝ s.direction)).restrict (s : Set (oco_point d)) := by
      rw [hq_isom.map_euclideanHausdorffMeasure, hrange]
    have hmeasure :
        (MeasureTheory.Measure.euclideanHausdorffMeasure
          (Module.finrank ℝ s.direction)).restrict X =
          ((MeasureTheory.Measure.euclideanHausdorffMeasure
            (Module.finrank ℝ s.direction) : Measure s.direction).restrict C).map q := by
      calc
        (MeasureTheory.Measure.euclideanHausdorffMeasure
            (Module.finrank ℝ s.direction)).restrict X =
            ((MeasureTheory.Measure.euclideanHausdorffMeasure
              (Module.finrank ℝ s.direction)).restrict
                (s : Set (oco_point d))).restrict X := by
          rw [Measure.restrict_restrict' hsmeas]
          congr 2
          exact (Set.inter_eq_self_of_subset_left (subset_affineSpan ℝ X)).symm
        _ = ((MeasureTheory.Measure.euclideanHausdorffMeasure
              (Module.finrank ℝ s.direction) : Measure s.direction).map q).restrict X := by
          rw [hmap_full]
        _ = ((MeasureTheory.Measure.euclideanHausdorffMeasure
              (Module.finrank ℝ s.direction) : Measure s.direction).restrict C).map q := by
          simpa [C] using hq.restrict_map
            (MeasureTheory.Measure.euclideanHausdorffMeasure
              (Module.finrank ℝ s.direction) : Measure s.direction) X
    rw [show affineSpan ℝ X = s from rfl]
    rw [hmeasure]
    exact hq.aemeasurable_map_iff.mpr (by simpa [g] using hg_ae)
  · rw [Set.not_nonempty_iff_eq_empty.mp hX]
    simp

@[blueprint "lem:continuous-hedge-finite-dimensional-integral-mem-convex"
  (statement := /-- Let \(E\) be a finite-dimensional real inner-product space, let
  \(C\subseteq E\) be convex, and let \(\mu\) be a probability measure.  If
  \(g\) is Bochner integrable and \(g(a)\in C\) for \(\mu\)-almost every \(a\),
  then
  \[
    \int g(a)\,d\mu(a)\in C.
  \] -/)
  (proof := /-- Write \(z=\int g\,d\mu\).  The usual closed-convex-set theorem first
  gives \(z\in\overline C\).  We prove that \(z\in C\) by induction on the dimension
  of the ambient space.  If the affine span of \(C\) is proper, orthogonally project
  after translating by a point of \(C\); this realizes the problem in the strictly
  lower-dimensional direction space of that affine span.  Otherwise \(C\) has nonempty
  interior.  If \(z\notin C\), geometric Hahn--Banach separation of \(z\) from the
  open convex set \(\operatorname{int} C\), followed by density of the interior in
  \(\overline C\), supplies a nonzero linear functional \(L\) with
  \(L(z)\leq L(x)\) for all \(x\in C\).  Since integration commutes with \(L\),
  the nonnegative function \(L(g)-L(z)\) has integral zero and hence vanishes almost
  everywhere.  Thus \(g\) is almost surely contained in the affine hyperplane
  \(L=L(z)\).  Orthogonal projection after translating by \(z\) reduces the problem
  to \(\ker L\), whose dimension is strictly smaller.  The induction hypothesis then
  yields \(z\in C\). -/)
  (title := /-- Barycentres remain in finite-dimensional convex sets -/)
  (latexEnv := "lemma")]
lemma continuous_hedge_finite_dimensional_integral_mem_convex
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (g : α → E) (μ : Measure α) [IsProbabilityMeasure μ]
    (hC : Convex ℝ C) (hmem : ∀ᵐ a ∂μ, g a ∈ C) (hint : Integrable g μ) :
    (∫ a, g a ∂μ) ∈ C := by
  classical
  let D : Set E := C
  let v : α → E := g
  have hD : Convex ℝ D := hC
  have hv_mem : ∀ᵐ a ∂μ, v a ∈ D := hmem
  have hv_int : Integrable v μ := hint
  let z : E := ∫ a, v a ∂μ
  have hz_closure : z ∈ closure D := by
    exact hD.closure.integral_mem isClosed_closure
      (hv_mem.mono fun a ha => subset_closure ha) hv_int
  by_cases hzD : z ∈ D
  · exact hzD
  obtain ⟨a₀, ha₀⟩ := hv_mem.exists
  let c : E := v a₀
  have hcD : c ∈ D := ha₀
  let A : AffineSubspace ℝ E := affineSpan ℝ D
  by_cases hA : A = ⊤
  ·
        have hinter : (interior D).Nonempty :=
          hD.interior_nonempty_iff_affineSpan_eq_top.mpr hA
        have hz_not_interior : z ∉ interior D :=
          fun hz => hzD (interior_subset hz)
        obtain ⟨l, hl⟩ :=
          geometric_hahn_banach_point_open hD.interior isOpen_interior hz_not_interior
        have hle : ∀ y ∈ D, l z ≤ l y := by
          have hclosed : IsClosed {y : E | l z ≤ l y} :=
            isClosed_le continuous_const l.continuous
          have hsubset : interior D ⊆ {y : E | l z ≤ l y} :=
            fun y hy => (hl y hy).le
          intro y hy
          apply closure_minimal hsubset hclosed
          rw [hD.closure_interior_eq_closure_of_nonempty_interior hinter]
          exact subset_closure hy
        have hl_ne : l ≠ 0 := by
          intro hl_zero
          obtain ⟨y, hy⟩ := hinter
          have := hl y hy
          simp [hl_zero] at this
        let q : α → ℝ := fun a => l (v a) - l z
        have hq_nonneg : 0 ≤ᵐ[μ] q :=
          hv_mem.mono fun a ha => sub_nonneg.mpr (hle (v a) ha)
        have hl_int : Integrable (fun a => l (v a)) μ :=
          l.integrable_comp hv_int
        have hq_intg : Integrable q μ :=
          hl_int.sub (integrable_const (l z))
        have hq_int : (∫ a, q a ∂μ) = 0 := by
          dsimp [q]
          rw [integral_sub hl_int (integrable_const (l z)),
            l.integral_comp_comm hv_int]
          simp [z]
        have hq_zero : q =ᵐ[μ] 0 :=
          (integral_eq_zero_iff_of_nonneg_ae hq_nonneg hq_intg).mp hq_int
        have hl_eq : ∀ᵐ a ∂μ, l (v a) = l z := by
          filter_upwards [hq_zero] with a ha
          dsimp [q] at ha
          linarith
        let K : Submodule ℝ E := l.ker
        have hK_ne : K ≠ ⊤ := by
          intro hK
          apply hl_ne
          ext y
          have hy : y ∈ K := by simp [hK]
          exact hy
        have hK_lt : Module.finrank ℝ K < Module.finrank ℝ E :=
          K.finrank_lt hK_ne
        let proj : E →L[ℝ] K := K.orthogonalProjectionOnto
        let D' : Set K := {u | z + (u : E) ∈ D}
        let v' : α → K := fun a => proj (v a - z)
        have hD' : Convex ℝ D' := by
          intro x hx y hy a b ha hb hab
          change z + (x : E) ∈ D at hx
          change z + (y : E) ∈ D at hy
          change z + ((a • x + b • y : K) : E) ∈ D
          have hh := hD hx hy ha hb hab
          simp only [smul_add] at hh
          have hbase : z = a • z + b • z := by
            calc
              z = 1 • z := (one_smul ℝ z).symm
              _ = (a + b) • z := by rw [hab]
              _ = a • z + b • z := add_smul a b z
          convert hh using 1
          nth_rewrite 1 [hbase]
          abel_nf
          simp
        have hv'_mem : ∀ᵐ a ∂μ, v' a ∈ D' := by
          filter_upwards [hv_mem, hl_eq] with a ha hla
          have hker : v a - z ∈ K := by
            change l (v a - z) = 0
            simp [hla]
          have hproj :
              proj (v a - z) = (⟨v a - z, hker⟩ : K) := by
            exact K.orthogonalProjectionOnto_mem_subspace_eq_self
              (⟨v a - z, hker⟩ : K)
          change z + (proj (v a - z) : E) ∈ D
          rw [hproj]
          simpa using ha
        have hv_sub_int : Integrable (fun a => v a - z) μ :=
          hv_int.sub (integrable_const z)
        have hv'_int : Integrable v' μ :=
          proj.integrable_comp hv_sub_int
        have hv'_integral : (∫ a, v' a ∂μ) = 0 := by
          dsimp [v']
          rw [proj.integral_comp_comm hv_sub_int]
          have hsub : (∫ a, v a - z ∂μ) = 0 := by
            rw [integral_sub hv_int (integrable_const z)]
            simp [z]
          rw [hsub]
          simp
        have hrec := continuous_hedge_finite_dimensional_integral_mem_convex
          D' v' μ hD' hv'_mem hv'_int
        rw [hv'_integral] at hrec
        simpa [D'] using hrec
  ·
        have hA_nonempty : (A : Set E).Nonempty :=
          ⟨c, subset_affineSpan ℝ D hcD⟩
        let K : Submodule ℝ E := A.direction
        have hK_ne : K ≠ ⊤ := by
          intro hK
          apply hA
          exact (A.direction_eq_top_iff_of_nonempty hA_nonempty).mp hK
        have hK_lt : Module.finrank ℝ K < Module.finrank ℝ E :=
          K.finrank_lt hK_ne
        have hzA : z ∈ A :=
          (closure_minimal (subset_affineSpan ℝ D)
            A.closed_of_finiteDimensional) hz_closure
        let proj : E →L[ℝ] K := K.orthogonalProjectionOnto
        let D' : Set K := {u | c + (u : E) ∈ D}
        let v' : α → K := fun a => proj (v a - c)
        have hD' : Convex ℝ D' := by
          intro x hx y hy a b ha hb hab
          change c + (x : E) ∈ D at hx
          change c + (y : E) ∈ D at hy
          change c + ((a • x + b • y : K) : E) ∈ D
          have hh := hD hx hy ha hb hab
          simp only [smul_add] at hh
          have hbase : c = a • c + b • c := by
            calc
              c = 1 • c := (one_smul ℝ c).symm
              _ = (a + b) • c := by rw [hab]
              _ = a • c + b • c := add_smul a b c
          convert hh using 1
          nth_rewrite 1 [hbase]
          abel_nf
          simp
        have hv'_mem : ∀ᵐ a ∂μ, v' a ∈ D' := by
          filter_upwards [hv_mem] with a ha
          have hdir : v a - c ∈ K := by
            simpa [K, A] using
              A.vsub_mem_direction (subset_affineSpan ℝ D ha)
                (subset_affineSpan ℝ D hcD)
          have hproj :
              proj (v a - c) = (⟨v a - c, hdir⟩ : K) := by
            exact K.orthogonalProjectionOnto_mem_subspace_eq_self
              (⟨v a - c, hdir⟩ : K)
          change c + (proj (v a - c) : E) ∈ D
          rw [hproj]
          simpa using ha
        have hv_sub_int : Integrable (fun a => v a - c) μ :=
          hv_int.sub (integrable_const c)
        have hv'_int : Integrable v' μ :=
          proj.integrable_comp hv_sub_int
        have hv'_integral : (∫ a, v' a ∂μ) = proj (z - c) := by
          dsimp [v']
          rw [proj.integral_comp_comm hv_sub_int]
          have hsub : (∫ a, v a - c ∂μ) = z - c := by
            rw [integral_sub hv_int (integrable_const c)]
            simp [z]
          rw [hsub]
        have hrec := continuous_hedge_finite_dimensional_integral_mem_convex
          D' v' μ hD' hv'_mem hv'_int
        rw [hv'_integral] at hrec
        have hzdir : z - c ∈ K := by
          simpa [K, A] using
            A.vsub_mem_direction hzA (subset_affineSpan ℝ D hcD)
        have hproj :
            proj (z - c) = (⟨z - c, hzdir⟩ : K) := by
          exact K.orthogonalProjectionOnto_mem_subspace_eq_self
            (⟨z - c, hzdir⟩ : K)
        rw [hproj] at hrec
        simpa [D'] using hrec
  termination_by Module.finrank ℝ E
  decreasing_by all_goals assumption

@[blueprint "lem:continuous-hedge-intrinsic-jensen"
  (statement := /-- Let \(d\in\mathbb N\), let \(\mathcal X\subseteq\mathbb R^d\)
  be convex, and let \(\mu\) be a probability measure on \(\mathbb R^d\) such that
  \(y\in\mathcal X\) for \(\mu\)-almost every \(y\).  Suppose that the identity map
  and a function \(f:\mathbb R^d\to\mathbb R\) are Bochner integrable with respect to
  \(\mu\).  If \(f\) is convex on \(\mathcal X\) and the barycentre
  \(b=\int y\,d\mu(y)\) belongs to \(\mathcal X\), then
  \[
    f(b)\leq\int f(y)\,d\mu(y).
  \] -/)
  (proof := /-- Apply
  \cref{lem:continuous-hedge-finite-dimensional-integral-mem-convex} to the integrable
  random vector \(y\mapsto(y,f(y))\) and the epigraph
  \[
    \{(x,r):x\in\mathcal X\text{ and }f(x)\leq r\}.
  \]
  The epigraph is convex because \(\mathcal X\) and \(f\) are convex.  The support
  hypothesis places \((y,f(y))\) in it almost everywhere, while the two integrability
  hypotheses give integrability of the paired map.  Its integral is
  \((\int y\,d\mu,\int f\,d\mu)\).  Membership of this pair in the epigraph,
  together with the assumed membership of the barycentre in \(\mathcal X\), is exactly
  the claimed inequality. -/)
  (title := /-- Jensen's inequality on an arbitrary convex domain -/)
  (latexEnv := "lemma")]
lemma continuous_hedge_intrinsic_jensen {d : ℕ}
    (X : Set (oco_point d)) (f : oco_point d → ℝ)
    (μ : Measure (oco_point d))
    [IsProbabilityMeasure μ]
    (hconv : Convex ℝ X) (hf : ConvexOn ℝ X f)
    (hsupp : ∀ᵐ y ∂μ, y ∈ X)
    (hid : Integrable (fun y => y) μ) (hfi : Integrable f μ)
    (hbar : (∫ y, y ∂μ) ∈ X) :
    f (∫ y, y ∂μ) ≤ ∫ y, f y ∂μ := by
  let e₀ : (ℝ × oco_point d) ≃ₗ[ℝ] (Fin d.succ → ℝ) :=
    Fin.consLinearEquiv ℝ (fun _ : Fin d.succ => ℝ)
  let e : (ℝ × oco_point d) ≃L[ℝ] EuclideanSpace ℝ (Fin d.succ) :=
    e₀.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin d.succ) ℝ).symm
  let swap : (ℝ × oco_point d) ≃ₗ[ℝ] (oco_point d × ℝ) :=
    LinearEquiv.prodComm ℝ ℝ (oco_point d)
  let C₀ : Set (ℝ × oco_point d) := swap ⁻¹' {p | p.1 ∈ X ∧ f p.1 ≤ p.2}
  let C : Set (EuclideanSpace ℝ (Fin d.succ)) := e '' C₀
  let g : oco_point d → EuclideanSpace ℝ (Fin d.succ) := fun y => e (f y, y)
  have hC₀ : Convex ℝ C₀ :=
    hf.convex_epigraph.linear_preimage swap.toLinearMap
  have hC : Convex ℝ C :=
    hC₀.linear_image e.toLinearMap
  have hmem : ∀ᵐ y ∂μ, g y ∈ C := by
    filter_upwards [hsupp] with y hy
    exact ⟨(f y, y), ⟨hy, le_rfl⟩, rfl⟩
  have hpair : Integrable (fun y => (f y, y)) μ := hfi.prodMk hid
  have hint : Integrable g μ :=
    e.toContinuousLinearMap.integrable_comp hpair
  have hz := continuous_hedge_finite_dimensional_integral_mem_convex
    C g μ hC hmem hint
  have hgint :
      (∫ y, g y ∂μ) =
        e.toContinuousLinearMap (∫ y, (f y, y) ∂μ) :=
    e.toContinuousLinearMap.integral_comp_comm hpair
  rcases hz with ⟨q, hq, hqeq⟩
  have hqeq' : q = ∫ y, (f y, y) ∂μ :=
    e.injective (hqeq.trans hgint)
  rw [hqeq', integral_pair hfi hid] at hq
  exact hq.2

@[blueprint "lem:continuous-hedge-convex-add-haar-finite-is-bounded"
  (statement := /-- Let (E) be a finite-dimensional real normed space, let
  (mu) be an additive Haar measure on (E), and let (Csubseteq E) be convex.
  If (0<mu(C)<infty), then (C) is bounded. -/)
  (proof := /-- Positivity of the Haar measure implies that the affine span of
  (C) is the whole space, since every proper affine subspace has Haar measure zero.
  Thus (C) has a point (x) in its interior and an open ball about (x) contained
  in (C).  If (C) were
  unbounded, then for each natural number one could choose a sufficiently distant
  point of (C).  On the segment joining (x) to that point, choose a centre at a
  prescribed distance from (x).  Convexity shows that a ball of one fixed positive
  radius about every such centre lies in (C).  Choosing the prescribed distances
  with uniformly separated radii makes these balls pairwise disjoint.  Translation
  invariance gives every ball the same strictly positive (mu)-measure, so countable
  additivity forces (mu(C)=infty), contradicting the hypothesis. -/)
  (title := /-- Finite Haar measure bounds a full-dimensional convex set -/)
  (latexEnv := "lemma")]
lemma continuous_hedge_convex_add_haar_finite_is_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (C : Set E)
    (hC : Convex ℝ C) (hpositive : μ C ≠ 0)
    (hfinite : μ C ≠ ⊤) : Bornology.IsBounded C := by
  classical
  have hspan : affineSpan ℝ C = ⊤ := by
    by_contra hs
    apply hpositive
    exact measure_mono_null (subset_affineSpan ℝ C)
      (μ.addHaar_affineSubspace (affineSpan ℝ C) hs)
  obtain ⟨x, hx⟩ := hC.interior_nonempty_iff_affineSpan_eq_top.mpr hspan
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hballC : Metric.ball x ε ⊆ C := hball.trans interior_subset
  by_contra hbounded
  have hfar : ∀ R : ℝ, ∃ y ∈ C, R ≤ dist x y := by
    intro R
    by_contra hR
    push Not at hR
    apply hbounded
    rw [Metric.isBounded_iff_subset_ball x]
    exact ⟨R, fun y hy => by simpa [dist_comm] using hR y hy⟩
  let R : ℕ → ℝ := fun n => (4 * (n : ℝ) + 2) * ε
  have hRpos : ∀ n, 0 < R n := by
    intro n
    dsimp [R]
    positivity
  choose y hyC hyfar using fun n => hfar (2 * R n)
  let a : ℕ → ℝ := fun n => R n / dist x (y n)
  have hydist_pos : ∀ n, 0 < dist x (y n) := by
    intro n
    exact lt_of_lt_of_le (mul_pos (by norm_num) (hRpos n)) (hyfar n)
  have ha_nonneg : ∀ n, 0 ≤ a n := by
    intro n
    exact div_nonneg (hRpos n).le (hydist_pos n).le
  have ha_half : ∀ n, a n ≤ (1 : ℝ) / 2 := by
    intro n
    rw [div_le_iff₀ (hydist_pos n)]
    nlinarith [hyfar n]
  let z : ℕ → E := fun n => x + a n • (y n - x)
  have hzdist : ∀ n, dist x (z n) = R n := by
    intro n
    rw [dist_eq_norm]
    have hrewrite : x - z n = -(a n • (y n - x)) := by
      simp [z]
    rw [hrewrite, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (ha_nonneg n)]
    change (R n / dist x (y n)) * ‖y n - x‖ = R n
    rw [show ‖y n - x‖ = dist x (y n) by
      simp [dist_eq_norm, norm_sub_rev], div_mul_cancel₀ _ (hydist_pos n).ne']
  let B : ℕ → Set E := fun n => Metric.ball (z n) (ε / 2)
  have hBsub : ∀ n, B n ⊆ C := by
    intro n w hw
    have ha_lt_one : a n < 1 := lt_of_le_of_lt (ha_half n) (by norm_num)
    have hone_sub : 0 < 1 - a n := sub_pos.mpr ha_lt_one
    let u : E := x + (1 / (1 - a n)) • (w - z n)
    have hinv_le : 1 / (1 - a n) ≤ 2 := by
      rw [div_le_iff₀ hone_sub]
      nlinarith [ha_half n]
    have hu_ball : u ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [u, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (one_div_pos.mpr hone_sub)]
      calc
        (1 / (1 - a n)) * ‖w - z n‖ ≤ 2 * ‖w - z n‖ :=
          mul_le_mul_of_nonneg_right hinv_le (norm_nonneg _)
        _ < 2 * (ε / 2) := by
          apply mul_lt_mul_of_pos_left _ (by norm_num)
          simpa [B, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hw
        _ = ε := by ring
    have huC : u ∈ C := hballC hu_ball
    have ha_le_one : a n ≤ 1 := (ha_half n).trans (by norm_num)
    have hcombo := hC huC (hyC n) (sub_nonneg.mpr ha_le_one)
      (ha_nonneg n) (by ring : (1 - a n) + a n = 1)
    convert hcombo using 1
    change w = (1 - a n) •
      (x + (1 / (1 - a n)) • (w - (x + a n • (y n - x)))) + a n • y n
    have hc : (1 - a n) * (1 / (1 - a n)) = 1 := by
      rw [one_div]
      exact mul_inv_cancel₀ hone_sub.ne'
    rw [smul_add, smul_smul, hc, one_smul]
    module
  have hBdisjoint : Pairwise fun m n => Disjoint (B m) (B n) := by
    intro m n hmn
    apply Metric.ball_disjoint_ball
    have hradial : 2 * ε ≤ |R m - R n| := by
      rcases lt_or_gt_of_ne hmn with hlt | hgt
      · have hcast : (m : ℝ) + 1 ≤ n := by exact_mod_cast hlt
        rw [abs_of_nonpos]
        · dsimp [R]
          nlinarith
        · dsimp [R]
          nlinarith
      · have hcast : (n : ℝ) + 1 ≤ m := by exact_mod_cast hgt
        rw [abs_of_nonneg]
        · dsimp [R]
          nlinarith
        · dsimp [R]
          nlinarith
    calc
      ε / 2 + ε / 2 = ε := by ring
      _ ≤ 2 * ε := by linarith
      _ ≤ |dist (z m) x - dist (z n) x| := by
        simpa [dist_comm, hzdist] using hradial
      _ ≤ dist (z m) (z n) := abs_dist_sub_le _ _ _
  have hBmeas : ∀ n, MeasurableSet (B n) := fun n => Metric.isOpen_ball.measurableSet
  have hballs_le : (∑' n, μ (B n)) ≤ μ C := by
    refine (tsum_meas_le_meas_iUnion_of_disjoint μ hBmeas hBdisjoint).trans ?_
    exact measure_mono (Set.iUnion_subset hBsub)
  have hball_pos : 0 < μ (Metric.ball (0 : E) (ε / 2)) :=
    Metric.measure_ball_pos (μ := μ) 0 (half_pos hε)
  have hsum_top : (∑' n, μ (B n)) = ⊤ := by
    simp only [B, μ.addHaar_ball_center]
    simp [ENNReal.tsum_const, hball_pos.ne']
  apply hfinite
  exact top_unique (hsum_top ▸ hballs_le)

@[blueprint "lem:continuous-hedge-normalization"
  (statement := /-- Let \(d,T\in\mathbb N\), with \(d>0\) and \(T\geq2\), let
  \(\mathcal X\subseteq\mathbb R^d\) be nonempty and convex, and let
  \(f_t:\mathbb R^d\to\mathbb R\), \(0\leq t<T\), be convex on \(\mathcal X\) and satisfy
  \(|f_t(y)|\leq1\) for every \(y\in\mathcal X\).  Suppose \(0\leq\eta\leq1\) and, for
  every \(0\leq t\leq T\), the intrinsic exponential-weights measure \(\mu_t\) from
  \cref{def:continuous-hedge-weight-measure} has strictly positive finite mass.  Then the
  normalized measures \(p_t\) from \cref{def:continuous-hedge-distribution} are probability
  measures supported on \(\mathcal X\), their identity maps are Bochner integrable, and their
  barycentres \(x_t\) belong to \(\mathcal X\).  Consequently \(p=(p_t)\) and \(x=(x_t)\)
  form an execution in the sense of \cref{def:is-continuous-hedge}. -/)
  (proof := /-- Let \(A=\operatorname{aff}\mathcal X\), choose \(a\in\mathcal X\), and put
  \(V=\operatorname{dir}(A)\).  Translation by \(a\), followed by the inclusion
  \(A\hookrightarrow\mathbb R^d\), gives an affine isometric embedding
  \(q:V\to\mathbb R^d\) with range \(A\).  For \(C=q^{-1}(\mathcal X)\), isometric invariance
  of Euclidean Hausdorff measure and restriction to \(\mathcal X\) identify the intrinsic
  reference measure
  \[
    \lambda=\mathcal H^{\dim V}_{\mathrm E}|_{\mathcal X}
  \]
  with the pushforward by \(q\) of
  \(\mathcal H^{\dim V}_{\mathrm E}|_C\).  At time zero the density in
  \cref{def:continuous-hedge-weight-measure} is one, so the mass hypothesis implies that
  \(C\) has strictly positive finite Euclidean Haar measure.  The set \(C\) is convex;
  therefore \cref{lem:continuous-hedge-convex-add-haar-finite-is-bounded} makes \(C\)
  bounded.  Since \(q\) is an isometry and \(q(C)=\mathcal X\), the set \(\mathcal X\)
  is bounded as well.  The same pushforward identity shows that \(y\in\mathcal X\) for
  \(\lambda\)-almost every \(y\).

  For \(0\leq t\leq T\), write \(\mu_t\) for the measure from
  \cref{def:continuous-hedge-weight-measure} and set
  \[
    p_t=\mu_t(\mathbb R^d)^{-1}\mu_t,\qquad
    x_t=\int_{\mathbb R^d}y\,dp_t(y).
  \]
  The assumed nonzero finite mass makes \(p_t\) a probability measure and selects exactly
  this branch of \cref{def:continuous-hedge-distribution}.  Since a measure obtained by
  adding a density is absolutely continuous with respect to its reference measure,
  \(y\in\mathcal X\) for \(\mu_t\)-almost every \(y\), and hence also for \(p_t\)-almost
  every \(y\).  Thus \(p_t(\mathcal X^{\complement})=0\).  Boundedness of \(\mathcal X\),
  together with this almost-everywhere support and the finiteness of the probability
  measure, makes the identity map Bochner integrable under \(p_t\).

  Apply \cref{lem:continuous-hedge-finite-dimensional-integral-mem-convex} after sending
  \(\mathbb R^d\) through its standard continuous linear equivalence with Euclidean space.
  Convexity of \(\mathcal X\), almost-everywhere support, and identity integrability imply
  \(x_t\in\mathcal X\).  Consequently the sequences \(p=(p_t)\) and \(x=(x_t)\) satisfy
  every clause of \cref{def:is-continuous-hedge} through time \(T\). -/)
  (title := /-- Normalization and barycentres of intrinsic Continuous Hedge -/)
  (latexEnv := "lemma")]
lemma continuous_hedge_normalization {d T : ℕ} (X : Set (oco_point d))
    (loss : ℕ → oco_point d → ℝ) (η : ℝ)
    (hT : 2 ≤ T) (hd : 0 < d) (hX : X.Nonempty) (hconv : Convex ℝ X)
    (hloss_conv : ∀ t, t < T → ConvexOn ℝ X (loss t))
    (hloss_bound : ∀ t, t < T → ∀ y ∈ X, |loss t y| ≤ 1)
    (hη_nonneg : 0 ≤ η) (hη_le_one : η ≤ 1)
    (hmass : ∀ t, t ≤ T →
      continuous_hedge_weight_measure X loss η t Set.univ ≠ 0 ∧
      continuous_hedge_weight_measure X loss η t Set.univ ≠ ⊤) :
    ∃ (p : ℕ → Measure (oco_point d)) (x : ℕ → oco_point d),
      is_continuous_hedge T X loss η p x := by
  classical
  let s : AffineSubspace ℝ (oco_point d) := affineSpan ℝ X
  let a₀ : s := ⟨hX.choose, subset_affineSpan ℝ X hX.choose_spec⟩
  letI : Nonempty s := ⟨a₀⟩
  let e : s.direction ≃ᵢ s := IsometryEquiv.vaddConst a₀
  let q : s.direction → oco_point d := fun v => (e v : s)
  let C : Set s.direction := q ⁻¹' X
  have hsmeas : MeasurableSet (s : Set (oco_point d)) :=
    (AffineSubspace.closed_of_finiteDimensional s).measurableSet
  have hq : MeasurableEmbedding q := by
    dsimp [q]
    exact (MeasurableEmbedding.subtype_coe hsmeas).comp
      e.toHomeomorph.measurableEmbedding
  let qA : s.direction →ᵃ[ℝ] oco_point d :=
    { toFun := q
      linear := s.direction.subtype
      map_vadd' := by
        intro v x
        simp [q, e, add_assoc] }
  have hC : Convex ℝ C := by
    simpa [C, qA] using hconv.affine_preimage qA
  let ν : Measure s.direction :=
    MeasureTheory.Measure.euclideanHausdorffMeasure
      (Module.finrank ℝ s.direction)
  have hCnull : NullMeasurableSet C ν := by
    exact hC.nullMeasurableSet (μ := ν)
  have hq_isom : Isometry q := by
    intro x y
    simpa [q] using (isometry_subtype_coe.comp e.isometry x y)
  have hrange : Set.range q = (s : Set (oco_point d)) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (e v).property
    · intro hx
      refine ⟨e.symm ⟨x, hx⟩, ?_⟩
      simp [q]
  have himage : q '' C = X := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      have hxs : x ∈ (s : Set (oco_point d)) := subset_affineSpan ℝ X hx
      obtain ⟨v, rfl⟩ := Set.ext_iff.mp hrange x |>.mpr hxs
      exact ⟨v, hx, rfl⟩
  have hmap_full :
      (ν : Measure s.direction).map q =
        (MeasureTheory.Measure.euclideanHausdorffMeasure
          (Module.finrank ℝ s.direction)).restrict (s : Set (oco_point d)) := by
    dsimp [ν]
    rw [hq_isom.map_euclideanHausdorffMeasure, hrange]
  let base : Measure (oco_point d) :=
    (MeasureTheory.Measure.euclideanHausdorffMeasure
      (Module.finrank ℝ (affineSpan ℝ X).direction)).restrict X
  have hmeasure :
      base = (ν.restrict C).map q := by
    change
      (MeasureTheory.Measure.euclideanHausdorffMeasure
          (Module.finrank ℝ s.direction)).restrict X =
        (ν.restrict C).map q
    calc
      (MeasureTheory.Measure.euclideanHausdorffMeasure
          (Module.finrank ℝ s.direction)).restrict X =
          ((MeasureTheory.Measure.euclideanHausdorffMeasure
            (Module.finrank ℝ s.direction)).restrict
              (s : Set (oco_point d))).restrict X := by
        rw [Measure.restrict_restrict' hsmeas]
        congr 2
        exact (Set.inter_eq_self_of_subset_left (subset_affineSpan ℝ X)).symm
      _ = ((ν : Measure s.direction).map q).restrict X := by
        rw [hmap_full]
      _ = (ν.restrict C).map q := by
        simpa [C] using hq.restrict_map ν X
  have hweight_zero : continuous_hedge_weight_measure X loss η 0 = base := by
    simp [continuous_hedge_weight_measure, base]
  have hmass_zero := hmass 0 (Nat.zero_le T)
  rw [hweight_zero] at hmass_zero
  have hνmass : ν C ≠ 0 ∧ ν C ≠ ⊤ := by
    have htotal : base Set.univ = ν C := by
      rw [hmeasure]
      simp [hq.measurable]
    simpa [htotal] using hmass_zero
  have hCbounded : Bornology.IsBounded C :=
    continuous_hedge_convex_add_haar_finite_is_bounded
      ν C hC hνmass.1 hνmass.2
  have hXbounded : Bornology.IsBounded X := by
    rw [Metric.isBounded_iff] at hCbounded ⊢
    obtain ⟨K, hK⟩ := hCbounded
    refine ⟨K, ?_⟩
    intro x hx y hy
    rw [← himage] at hx hy
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    rw [hq_isom.dist_eq]
    exact hK hu hv
  have hbase_supp : ∀ᵐ y ∂base, y ∈ X := by
    rw [hmeasure]
    apply hq.ae_map_iff.mpr
    filter_upwards [ae_restrict_mem₀ hCnull] with v hv
    exact hv
  obtain ⟨K, hK⟩ := (Metric.isBounded_iff_subset_ball (0 : oco_point d)).mp hXbounded
  let μ : ℕ → Measure (oco_point d) :=
    fun t => continuous_hedge_weight_measure X loss η t
  let p : ℕ → Measure (oco_point d) :=
    fun t => ((μ t) Set.univ)⁻¹ • μ t
  let x : ℕ → oco_point d := fun t => ∫ y, y ∂p t
  refine ⟨p, x, ?_⟩
  intro t ht
  have hμmass : μ t Set.univ ≠ 0 ∧ μ t Set.univ ≠ ⊤ := by
    simpa [μ] using hmass t ht
  letI : IsFiniteMeasure (μ t) := ⟨lt_top_iff_ne_top.mpr hμmass.2⟩
  letI : NeZero (μ t) :=
    ⟨Measure.measure_univ_ne_zero.mp hμmass.1⟩
  haveI : IsProbabilityMeasure (p t) := by
    dsimp [p]
    infer_instance
  have hpdist : p t = continuous_hedge_distribution X loss η t := by
    simp [p, μ, continuous_hedge_distribution, hX, hμmass]
  have hμsupp : ∀ᵐ y ∂μ t, y ∈ X := by
    apply (withDensity_absolutelyContinuous base _).ae_le
    exact hbase_supp
  have hpsupp : ∀ᵐ y ∂p t, y ∈ X := by
    exact Measure.ae_smul_measure hμsupp _
  have hpid : Integrable (fun y => y) (p t) := by
    apply Integrable.of_bound continuous_id.aestronglyMeasurable K
    filter_upwards [hpsupp] with y hy
    have hyK := hK hy
    have hyK' : ‖y‖ < K := by
      simpa [Metric.mem_ball, dist_zero_left] using hyK
    exact hyK'.le
  let eu : oco_point d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (EuclideanSpace.equiv (Fin d) ℝ).symm
  let XC : Set (EuclideanSpace ℝ (Fin d)) := eu '' X
  let g : oco_point d → EuclideanSpace ℝ (Fin d) := fun y => eu y
  have hXC : Convex ℝ XC := hconv.linear_image eu.toLinearMap
  have hgmem : ∀ᵐ y ∂p t, g y ∈ XC := by
    filter_upwards [hpsupp] with y hy
    exact ⟨y, hy, rfl⟩
  have hgint : Integrable g (p t) :=
    eu.toContinuousLinearMap.integrable_comp hpid
  have hgbar := continuous_hedge_finite_dimensional_integral_mem_convex
    XC g (p t) hXC hgmem hgint
  have hgint_eq :
      (∫ y, g y ∂p t) = eu.toContinuousLinearMap (∫ y, y ∂p t) :=
    eu.toContinuousLinearMap.integral_comp_comm hpid
  rcases hgbar with ⟨u, hu, hueq⟩
  have hueq' : u = ∫ y, y ∂p t :=
    eu.injective (hueq.trans hgint_eq)
  have hxmem : (∫ y, y ∂p t) ∈ X := by
    rwa [← hueq']
  exact ⟨hpdist, inferInstance, by
    simpa [Set.compl_def] using (ae_iff.mp hpsupp), hpid, rfl, hxmem⟩

@[blueprint "lem:continuous-hedge-regret-decomposition"
  (statement := /-- Let \(d,T\in\mathbb N\), let \(\mathcal X\subseteq\mathbb R^d\), and
  let \(f_t:\mathbb R^d\to\mathbb R\), \(p_t\), \(x_t\), and \(u\in\mathbb R^d\) be
  given.  Suppose that \(\eta\geq0\), that \(u\in\mathcal X\), that, for every \(t<T\),
  the function \(f_t\) is convex on \(\mathcal X\) and satisfies
  \(|f_t(y)|\leq1\) for every \(y\in\mathcal X\), and that \((p,x)\) is a Continuous
  Hedge execution through time \(T\).  Then
  \[
  \begin{aligned}
  \eta\operatorname{Reg}_{\rm Alt}(u)
  \leq{}&
  \sum_{t=0}^{T-1}\left[
    \eta\left(\int f_t\,dp_t+\int f_t\,dp_{t+1}\right)
    +2(\Phi_{t+1}-\Phi_t)\right]\\
  &+2\left(\Phi_0-\Phi_T-\eta\sum_{t=0}^{T-1}f_t(u)\right),
  \end{aligned}
  \]
  where comparator regret and \(\Phi_t\) are defined in
  \cref{def:comparator-alternating-regret,def:continuous-hedge-log-mass}. -/)
  (proof := /-- Fix \(t<T\).  By \cref{def:is-continuous-hedge}, both \(p_t\) and
  \(p_{t+1}\) are probability measures supported on \(\mathcal X\), their identity maps are
  integrable, and their barycentres are respectively \(x_t\) and \(x_{t+1}\), both of which
  belong to \(\mathcal X\).  By
  \cref{lem:continuous-hedge-convex-loss-regularity}, \(f_t\) is almost everywhere measurable
  for the intrinsic measure restricted to \(\mathcal X\).  The weight measure in
  \cref{def:continuous-hedge-distribution} is absolutely continuous with respect to this
  intrinsic measure.  Hence \(f_t\) is almost everywhere measurable for every finite scalar
  multiple of the weight measure; it is also almost everywhere measurable for the Dirac
  measure used by the fallback branch of that definition.  Thus \(f_t\) is almost everywhere
  measurable under both \(p_t\) and \(p_{t+1}\).  Their support properties and the bound
  \(|f_t|\leq1\) now imply that \(f_t\) is integrable under both probability measures.

  Apply \cref{lem:continuous-hedge-intrinsic-jensen} to \(p_t\) and \(p_{t+1}\).  Its support,
  integrability, and barycentre hypotheses have just been verified, and convexity is one of
  the assumptions on \(f_t\).  It gives
  \[
    f_t(x_t)\leq\int f_t\,dp_t,\qquad
    f_t(x_{t+1})\leq\int f_t\,dp_{t+1}.
  \]
  Adding these inequalities, subtracting \(2f_t(u)\), and summing over \(0\leq t<T\) gives
  an upper bound for the comparator regret in
  \cref{def:comparator-alternating-regret}.  Multiplication preserves this inequality because
  \(\eta\geq0\).  Finally, by \cref{def:continuous-hedge-log-mass},
  \[
    \sum_{t=0}^{T-1}2(\Phi_{t+1}-\Phi_t)=2(\Phi_T-\Phi_0).
  \]
  Expanding the finite sums and cancelling this telescoping quantity against the endpoint
  term yields the displayed inequality. -/)
  (title := /-- Alternating-regret log-partition decomposition -/)
  (latexEnv := "lemma")]
lemma continuous_hedge_regret_decomposition {d T : ℕ} (X : Set (oco_point d))
    (loss : ℕ → oco_point d → ℝ) (η : ℝ)
    (p : ℕ → Measure (oco_point d)) (x : ℕ → oco_point d) (u : oco_point d)
    (hη_nonneg : 0 ≤ η) (hu : u ∈ X)
    (hloss_conv : ∀ t, t < T → ConvexOn ℝ X (loss t))
    (hloss_bound : ∀ t, t < T → ∀ y ∈ X, |loss t y| ≤ 1)
    (hexec : is_continuous_hedge T X loss η p x) :
    η * comparator_alternating_regret T loss x u ≤
      ∑ t ∈ Finset.range T,
        (η * ((∫ y, loss t y ∂(p t)) + ∫ y, loss t y ∂(p (t + 1))) +
          2 * (continuous_hedge_log_mass X loss η (t + 1) -
            continuous_hedge_log_mass X loss η t)) +
      2 * (continuous_hedge_log_mass X loss η 0 -
        continuous_hedge_log_mass X loss η T -
        η * ∑ t ∈ Finset.range T, loss t u) := by
  classical
  have hX : X.Nonempty := ⟨u, hu⟩
  have hdist (s : ℕ) (hs : s < T) (r : ℕ) :
      AEMeasurable (loss s) (continuous_hedge_distribution X loss η r) := by
    have hb := continuous_hedge_convex_loss_regularity X (loss s)
      (hloss_conv s hs).1 (hloss_conv s hs)
    have hw : AEMeasurable (loss s) (continuous_hedge_weight_measure X loss η r) := by
      exact hb.mono_ac (MeasureTheory.withDensity_absolutelyContinuous _ _)
    unfold continuous_hedge_distribution
    simp only [dif_pos hX]
    split_ifs with hm
    · exact hw.smul_measure _
    · exact ⟨fun _ => loss s hX.choose, measurable_const,
        MeasureTheory.ae_eq_dirac (loss s)⟩
  have hint (s : ℕ) (hs : s < T) (r : ℕ) (q : Measure (oco_point d))
      (hq : q = continuous_hedge_distribution X loss η r)
      (hprob : IsProbabilityMeasure q) (hsupport : q (Xᶜ) = 0) :
      Integrable (loss s) q := by
    letI : IsProbabilityMeasure q := hprob
    refine Integrable.of_bound ?_ 1 ?_
    · rw [hq]
      exact (hdist s hs r).aestronglyMeasurable
    · have hqX : ∀ᵐ y ∂q, y ∈ X := by
        rw [MeasureTheory.ae_iff]
        change q (Xᶜ) = 0
        exact hsupport
      filter_upwards [hqX] with y hy
      simpa [Real.norm_eq_abs] using hloss_bound s hs y hy
  have hjensen (t : ℕ) (ht : t < T) :
      loss t (x t) + loss t (x (t + 1)) ≤
        (∫ y, loss t y ∂(p t)) + ∫ y, loss t y ∂(p (t + 1)) := by
    rcases hexec t (Nat.le_of_lt ht) with
      ⟨hpt, hprob_t, hsupport_t, hid_t, hx_t, hxmem_t⟩
    rcases hexec (t + 1) (by omega) with
      ⟨hpn, hprob_n, hsupport_n, hid_n, hx_n, hxmem_n⟩
    letI : IsProbabilityMeasure (p t) := hprob_t
    letI : IsProbabilityMeasure (p (t + 1)) := hprob_n
    have hs_t : ∀ᵐ y ∂(p t), y ∈ X := by
      rw [MeasureTheory.ae_iff]
      change p t (Xᶜ) = 0
      exact hsupport_t
    have hs_n : ∀ᵐ y ∂(p (t + 1)), y ∈ X := by
      rw [MeasureTheory.ae_iff]
      change p (t + 1) (Xᶜ) = 0
      exact hsupport_n
    have hb_t : (∫ y, y ∂(p t)) ∈ X := by
      rw [← hx_t]
      exact hxmem_t
    have hb_n : (∫ y, y ∂(p (t + 1))) ∈ X := by
      rw [← hx_n]
      exact hxmem_n
    have hi_t := hint t ht t (p t) hpt hprob_t hsupport_t
    have hi_n := hint t ht (t + 1) (p (t + 1)) hpn hprob_n hsupport_n
    have hleft := continuous_hedge_intrinsic_jensen X (loss t) (p t)
      (hloss_conv t ht).1 (hloss_conv t ht) hs_t hid_t hi_t hb_t
    have hright := continuous_hedge_intrinsic_jensen X (loss t) (p (t + 1))
      (hloss_conv t ht).1 (hloss_conv t ht) hs_n hid_n hi_n hb_n
    rw [← hx_t] at hleft
    rw [← hx_n] at hright
    exact add_le_add hleft hright
  have hsum :
      (∑ t ∈ Finset.range T,
        (loss t (x t) + loss t (x (t + 1)) - 2 * loss t u)) ≤
      ∑ t ∈ Finset.range T,
        ((∫ y, loss t y ∂(p t)) + (∫ y, loss t y ∂(p (t + 1))) -
          2 * loss t u) := by
    apply Finset.sum_le_sum
    intro t ht
    have hlt := Finset.mem_range.mp ht
    linarith [hjensen t hlt]
  have hscaled := mul_le_mul_of_nonneg_left hsum hη_nonneg
  have htel :
      (∑ t ∈ Finset.range T,
        2 * (continuous_hedge_log_mass X loss η (t + 1) -
          continuous_hedge_log_mass X loss η t)) =
        2 * (continuous_hedge_log_mass X loss η T -
          continuous_hedge_log_mass X loss η 0) := by
    rw [← Finset.mul_sum, Finset.sum_range_sub]
  rw [comparator_alternating_regret]
  calc
    η * ∑ t ∈ Finset.range T,
        (loss t (x t) + loss t (x (t + 1)) - 2 * loss t u) ≤
      η * ∑ t ∈ Finset.range T,
        ((∫ y, loss t y ∂(p t)) + (∫ y, loss t y ∂(p (t + 1))) -
          2 * loss t u) := hscaled
    _ = _ := by
      rw [Finset.sum_add_distrib, htel, Finset.mul_sum]
      simp only [mul_sub, mul_add, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
      ring_nf

@[blueprint "lem:continuous-hedge-intrinsic-measure-support"
  (statement := /-- Let \(\mathcal X\subseteq\mathbb R^d\) be nonempty and convex, and
  let \(k\) be the dimension of the direction space of its affine hull.  Then
  \(\mathcal H^k_{\mathrm E}|_{\mathcal X}\)-almost every point belongs to
  \(\mathcal X\). -/)
  (proof := /-- Choose a point of \(\mathcal X\) and use it to identify the direction
  space \(V\) of \(\operatorname{aff}(\mathcal X)\) isometrically with the affine hull.
  The inverse image \(C\subseteq V\) of \(\mathcal X\) is convex, hence null measurable
  for Euclidean Hausdorff measure on \(V\), which is an additive Haar measure.  Isometric
  invariance and restriction show that the intrinsic measure on \(\mathcal X\) is the
  pushforward of \(\mathcal H^k_{\mathrm E}|_C\).  Almost every point of the latter
  measure lies in \(C\), so its pushforward almost surely lies in \(\mathcal X\). -/)
  (title := /-- Support of the intrinsic measure -/)
  (latexEnv := "lemma")]
lemma continuous_hedge_intrinsic_measure_support {d : ℕ} (X : Set (oco_point d))
    (hX : X.Nonempty) (hconv : Convex ℝ X) :
    ∀ᵐ y ∂((MeasureTheory.Measure.euclideanHausdorffMeasure
      (Module.finrank ℝ (affineSpan ℝ X).direction)).restrict X), y ∈ X := by
  classical
  let s : AffineSubspace ℝ (oco_point d) := affineSpan ℝ X
  let p : s := ⟨hX.choose, subset_affineSpan ℝ X hX.choose_spec⟩
  letI : Nonempty s := ⟨p⟩
  let e : s.direction ≃ᵢ s := IsometryEquiv.vaddConst p
  let q : s.direction → oco_point d := fun v => (e v : s)
  let C : Set s.direction := q ⁻¹' X
  have hsmeas : MeasurableSet (s : Set (oco_point d)) :=
    (AffineSubspace.closed_of_finiteDimensional s).measurableSet
  have hq : MeasurableEmbedding q := by
    dsimp [q]
    exact (MeasurableEmbedding.subtype_coe hsmeas).comp
      e.toHomeomorph.measurableEmbedding
  let qA : s.direction →ᵃ[ℝ] oco_point d :=
    { toFun := q
      linear := s.direction.subtype
      map_vadd' := by
        intro v x
        simp [q, e, add_assoc] }
  have hC : Convex ℝ C := by
    simpa [C, qA] using hconv.affine_preimage qA
  let ν : Measure s.direction :=
    MeasureTheory.Measure.euclideanHausdorffMeasure
      (Module.finrank ℝ s.direction)
  have hCnull : NullMeasurableSet C ν := by
    exact hC.nullMeasurableSet (μ := ν)
  have hq_isom : Isometry q := by
    intro x y
    simpa [q] using (isometry_subtype_coe.comp e.isometry x y)
  have hrange : Set.range q = (s : Set (oco_point d)) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (e v).property
    · intro hx
      refine ⟨e.symm ⟨x, hx⟩, ?_⟩
      simp [q]
  have hmap_full :
      (ν : Measure s.direction).map q =
        (MeasureTheory.Measure.euclideanHausdorffMeasure
          (Module.finrank ℝ s.direction)).restrict (s : Set (oco_point d)) := by
    dsimp [ν]
    rw [hq_isom.map_euclideanHausdorffMeasure, hrange]
  let base : Measure (oco_point d) :=
    (MeasureTheory.Measure.euclideanHausdorffMeasure
      (Module.finrank ℝ (affineSpan ℝ X).direction)).restrict X
  have hmeasure : base = (ν.restrict C).map q := by
    change
      (MeasureTheory.Measure.euclideanHausdorffMeasure
          (Module.finrank ℝ s.direction)).restrict X =
        (ν.restrict C).map q
    calc
      (MeasureTheory.Measure.euclideanHausdorffMeasure
          (Module.finrank ℝ s.direction)).restrict X =
          ((MeasureTheory.Measure.euclideanHausdorffMeasure
            (Module.finrank ℝ s.direction)).restrict
              (s : Set (oco_point d))).restrict X := by
        rw [Measure.restrict_restrict' hsmeas]
        congr 2
        exact (Set.inter_eq_self_of_subset_left (subset_affineSpan ℝ X)).symm
      _ = ((ν : Measure s.direction).map q).restrict X := by
        rw [hmap_full]
      _ = (ν.restrict C).map q := by
        simpa [C] using hq.restrict_map ν X
  change ∀ᵐ y ∂base, y ∈ X
  rw [hmeasure]
  apply hq.ae_map_iff.mpr
  filter_upwards [ae_restrict_mem₀ hCnull] with v hv
  exact hv

@[blueprint "lem:continuous-hedge-scalar-exponential-remainder"
  (statement := /-- Let \(0\leq\eta\leq1\) and \(x\geq-2\eta\).  Then
  \[
    2(e^x-1)-(1+e^x)x\leq\frac43\eta^3.
  \] -/)
  (proof := /-- The function \(x\mapsto2(e^x-1)-(1+e^x)x\) is nonincreasing, since its
  derivative is \(e^x(1-x)-1\leq0\); the latter inequality follows from
  \(1-x\leq e^{-x}\).  It therefore suffices to evaluate at \(x=-2\eta\).  Put
  \(a=2\eta\).  The third-order Taylor lower bound
  \(1+a+a^2/2+a^3/6\leq e^a\), together with \(0\leq a\leq2\), gives
  \((a+2)e^{-a}\leq2-a+a^3/6\).  Rearrangement yields the assertion. -/)
  (title := /-- Scalar exponential remainder bound -/)
  (latexEnv := "lemma")]
lemma continuous_hedge_scalar_exponential_remainder (η x : ℝ)
    (hη_nonneg : 0 ≤ η) (hη_le_one : η ≤ 1) (hx : -2 * η ≤ x) :
    2 * (Real.exp x - 1) - (1 + Real.exp x) * x ≤ (4 : ℝ) / 3 * η ^ 3 := by
  have hanti : Antitone (fun z : ℝ =>
      2 * (Real.exp z - 1) - (1 + Real.exp z) * z) := by
    apply antitone_of_hasDerivAt_nonpos
    · intro z
      convert (((Real.hasDerivAt_exp z).sub_const 1).const_mul 2).sub
        (((hasDerivAt_const z 1).add (Real.hasDerivAt_exp z)).mul (hasDerivAt_id z)) using 1
      · rfl
      · rfl
      · funext y
        simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, id_eq]
    · intro z
      have hz := Real.one_sub_le_exp_neg z
      have hmul := mul_le_mul_of_nonneg_left hz (Real.exp_pos z).le
      rw [← Real.exp_add] at hmul
      norm_num at hmul
      simp only [Pi.zero_apply, Pi.add_apply, one_mul, zero_add, id_eq]
      nlinarith
  have hreduce := hanti hx
  let a : ℝ := 2 * η
  have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
  have ha_le_two : a ≤ 2 := by dsimp [a]; linarith
  have hexp := Real.sum_le_exp_of_nonneg ha_nonneg 4
  norm_num [Finset.sum_range_succ] at hexp
  have hD : 0 ≤ 2 - a + a ^ 3 / 6 := by
    have ha3 : 0 ≤ a ^ 3 := by positivity
    nlinarith
  have hpoly : a + 2 ≤
      (1 + a + a ^ 2 / 2 + a ^ 3 / 6) * (2 - a + a ^ 3 / 6) := by
    have ha5 : 0 ≤ a ^ 5 := by positivity
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hexp hD
  have hED : a + 2 ≤ Real.exp a * (2 - a + a ^ 3 / 6) := by
    nlinarith
  have hneg_nonneg : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  have hscaled := mul_le_mul_of_nonneg_right hED hneg_nonneg
  have hexp_cancel : Real.exp a * Real.exp (-a) = 1 := by
    rw [← Real.exp_add]
    simp
  have hscaled' : (a + 2) * Real.exp (-a) ≤ 2 - a + a ^ 3 / 6 := by
    calc
      (a + 2) * Real.exp (-a) ≤
          Real.exp a * (2 - a + a ^ 3 / 6) * Real.exp (-a) := hscaled
      _ = (2 - a + a ^ 3 / 6) * (Real.exp a * Real.exp (-a)) := by ring
      _ = 2 - a + a ^ 3 / 6 := by rw [hexp_cancel, mul_one]
  dsimp [a] at hreduce hscaled' ⊢
  have hneg : -(2 * η) = -2 * η := by ring
  rw [hneg] at hscaled'
  have hend :
      2 * (Real.exp (-2 * η) - 1) - (1 + Real.exp (-2 * η)) * (-2 * η) ≤
        (4 : ℝ) / 3 * η ^ 3 := by
    nlinarith
  exact hreduce.trans hend

@[blueprint "lem:continuous-hedge-exponential-tilt-stability"
  (statement := /-- Let \(p\) be a probability measure, let \(f\) be almost everywhere
  measurable with \(|f|\leq1\) almost everywhere, and let \(0\leq\eta\leq1\).  Set
  \(Z=\int e^{-\eta f}\,dp\).  Then
  \[
    \eta\left(\int f\,dp+
      \frac{\int f e^{-\eta f}\,dp}{Z}\right)+2\log Z
      \leq\frac43\eta^3.
  \] -/)
  (proof := /-- Put \(q=-\eta f-\log Z\) and \(r=e^q\).  The loss bound implies
  \(e^{-\eta}\leq Z\leq e^\eta\), whence \(-2\eta\leq q\) almost everywhere.  By
  \cref{lem:continuous-hedge-scalar-exponential-remainder},
  \(2(r-1)-(1+r)q\leq4\eta^3/3\) almost everywhere.  Moreover
  \(r=e^{-\eta f}/Z\), so \(\int r\,dp=1\).  Integrating the scalar inequality and
  expanding \(q\) gives the stated bound. -/)
  (title := /-- Stability of a bounded exponential tilt -/)
  (latexEnv := "lemma")]
lemma continuous_hedge_exponential_tilt_stability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf_meas : AEMeasurable f μ) (hf_bound : ∀ᵐ y ∂μ, |f y| ≤ 1)
    (η : ℝ) (hη_nonneg : 0 ≤ η) (hη_le_one : η ≤ 1) :
    let z := ∫ y, Real.exp (-η * f y) ∂μ
    η * ((∫ y, f y ∂μ) + (∫ y, f y * Real.exp (-η * f y) ∂μ) / z) +
      2 * Real.log z ≤ (4 : ℝ) / 3 * η ^ 3 := by
  let w : Ω → ℝ := fun y => Real.exp (-η * f y)
  let z : ℝ := ∫ y, w y ∂μ
  have hf_int : Integrable f μ := by
    apply Integrable.of_bound hf_meas.aestronglyMeasurable 1
    exact hf_bound
  have hfbounds : ∀ᵐ y ∂μ, -1 ≤ f y ∧ f y ≤ 1 := by
    filter_upwards [hf_bound] with y hy
    exact abs_le.mp hy
  have hw_meas : AEStronglyMeasurable w μ := by
    exact ((hf_meas.const_mul (-η)).exp).aestronglyMeasurable
  have hwbounds : ∀ᵐ y ∂μ,
      Real.exp (-η) ≤ w y ∧ w y ≤ Real.exp η := by
    filter_upwards [hfbounds] with y hy
    constructor
    · apply Real.exp_le_exp.mpr
      nlinarith
    · apply Real.exp_le_exp.mpr
      nlinarith
  have hw_int : Integrable w μ := by
    apply Integrable.of_bound hw_meas (Real.exp η)
    filter_upwards [hwbounds] with y hy
    rw [Real.norm_eq_abs, abs_of_pos ((Real.exp_pos _).trans_le hy.1)]
    exact hy.2
  have hfw_int : Integrable (fun y => f y * w y) μ := by
    apply hf_int.mul_bdd hw_meas
    filter_upwards [hwbounds] with y hy
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hy.2
  have hz_lower : Real.exp (-η) ≤ z := by
    simpa [z] using integral_mono_ae (integrable_const _) hw_int (hwbounds.mono fun y hy => hy.1)
  have hz_upper : z ≤ Real.exp η := by
    simpa [z] using integral_mono_ae hw_int (integrable_const _) (hwbounds.mono fun y hy => hy.2)
  have hz_pos : 0 < z := (Real.exp_pos (-η)).trans_le hz_lower
  have hlog_lower : -η ≤ Real.log z := by
    have h := Real.log_le_log (Real.exp_pos (-η)) hz_lower
    simpa using h
  have hlog_upper : Real.log z ≤ η := by
    have h := Real.log_le_log hz_pos hz_upper
    simpa using h
  let q : Ω → ℝ := fun y => -η * f y - Real.log z
  let r : Ω → ℝ := fun y => Real.exp (q y)
  have hq_meas : AEStronglyMeasurable q μ := by
    exact ((hf_meas.const_mul (-η)).sub aemeasurable_const).aestronglyMeasurable
  have hr_meas : AEStronglyMeasurable r μ := by
    exact hq_meas.aemeasurable.exp.aestronglyMeasurable
  have hq_bounds : ∀ᵐ y ∂μ, -2 * η ≤ q y ∧ |q y| ≤ 2 := by
    filter_upwards [hfbounds] with y hy
    have hη_abs : |η| ≤ 1 := by rw [abs_of_nonneg hη_nonneg]; exact hη_le_one
    constructor
    · dsimp [q]
      nlinarith
    · rw [abs_le]
      constructor <;> dsimp [q] <;> nlinarith
  have hr_int : Integrable r μ := by
    apply Integrable.of_bound hr_meas (Real.exp 2)
    filter_upwards [hq_bounds] with y hy
    have hry : 0 < r y := by dsimp [r]; positivity
    rw [Real.norm_eq_abs, abs_of_pos hry]
    exact Real.exp_le_exp.mpr (abs_le.mp hy.2).2
  have hfr_int : Integrable (fun y => f y * r y) μ := by
    apply hr_int.bdd_mul hf_meas.aestronglyMeasurable
    filter_upwards [hf_bound] with y hy
    simpa [Real.norm_eq_abs] using hy
  have hr_eq : ∀ y, r y = w y / z := by
    intro y
    dsimp [r, q, w]
    rw [Real.exp_sub, Real.exp_log hz_pos]
  have hr_integral : ∫ y, r y ∂μ = 1 := by
    calc
      (∫ y, r y ∂μ) = ∫ y, w y / z ∂μ := integral_congr_ae (Filter.Eventually.of_forall hr_eq)
      _ = (∫ y, w y ∂μ) / z := by
        simp only [div_eq_mul_inv, integral_mul_const]
      _ = 1 := by simp [z, hz_pos.ne']
  have hfr_integral : (∫ y, f y * r y ∂μ) = (∫ y, f y * w y ∂μ) / z := by
    calc
      (∫ y, f y * r y ∂μ) = ∫ y, (f y * w y) / z ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [hr_eq]
        ring
      _ = (∫ y, f y * w y ∂μ) / z := by
        simp only [div_eq_mul_inv, integral_mul_const]
  let φ : Ω → ℝ := fun y =>
    2 * (r y - 1) - (1 + r y) * q y
  have hone_r_int : Integrable (fun y => 1 + r y) μ := (integrable_const _).add hr_int
  have hprod_int : Integrable (fun y => (1 + r y) * q y) μ := by
    apply hone_r_int.mul_bdd hq_meas
    exact hq_bounds.mono fun y hy => by simpa [Real.norm_eq_abs] using hy.2
  have hφ_int : Integrable φ μ := by
    exact ((hr_int.sub (integrable_const _)).const_mul 2).sub hprod_int
  have hφ_bound : ∀ᵐ y ∂μ, φ y ≤ (4 : ℝ) / 3 * η ^ 3 := by
    filter_upwards [hq_bounds] with y hy
    exact continuous_hedge_scalar_exponential_remainder η (q y)
      hη_nonneg hη_le_one hy.1
  have hφ_le : (∫ y, φ y ∂μ) ≤ (4 : ℝ) / 3 * η ^ 3 := by
    simpa using integral_mono_ae hφ_int (integrable_const _) hφ_bound
  have hφ_expand : ∀ y, φ y =
      2 * (r y - 1) + η * f y + η * (f y * r y) +
        Real.log z + Real.log z * r y := by
    intro y
    dsimp [φ, q]
    ring
  have hterm1 : Integrable (fun y => 2 * (r y - 1)) μ :=
    (hr_int.sub (integrable_const _)).const_mul 2
  have hterm2 : Integrable (fun y => η * f y) μ := hf_int.const_mul η
  have hterm3 : Integrable (fun y => η * (f y * r y)) μ := hfr_int.const_mul η
  have hterm4 : Integrable (fun _ : Ω => Real.log z) μ := integrable_const _
  have hterm5 : Integrable (fun y => Real.log z * r y) μ := hr_int.const_mul _
  have hφ_integral : (∫ y, φ y ∂μ) =
      η * ((∫ y, f y ∂μ) + (∫ y, f y * w y ∂μ) / z) + 2 * Real.log z := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hφ_expand)]
    calc
      (∫ y, 2 * (r y - 1) + η * f y + η * (f y * r y) +
          Real.log z + Real.log z * r y ∂μ) =
          (∫ y, 2 * (r y - 1) + η * f y + η * (f y * r y) + Real.log z ∂μ) +
            ∫ y, Real.log z * r y ∂μ :=
        integral_add (((hterm1.add hterm2).add hterm3).add hterm4) hterm5
      _ = ((∫ y, 2 * (r y - 1) + η * f y + η * (f y * r y) ∂μ) +
          ∫ _ : Ω, Real.log z ∂μ) + ∫ y, Real.log z * r y ∂μ := by
        exact congrArg (fun u => u + ∫ y, Real.log z * r y ∂μ)
          (integral_add ((hterm1.add hterm2).add hterm3) hterm4)
      _ = (((∫ y, 2 * (r y - 1) + η * f y ∂μ) +
          ∫ y, η * (f y * r y) ∂μ) + ∫ _ : Ω, Real.log z ∂μ) +
            ∫ y, Real.log z * r y ∂μ := by
        exact congrArg (fun u => (u + ∫ _ : Ω, Real.log z ∂μ) +
          ∫ y, Real.log z * r y ∂μ)
          (integral_add (hterm1.add hterm2) hterm3)
      _ = ((((∫ y, 2 * (r y - 1) ∂μ) + ∫ y, η * f y ∂μ) +
          ∫ y, η * (f y * r y) ∂μ) + ∫ _ : Ω, Real.log z ∂μ) +
            ∫ y, Real.log z * r y ∂μ := by
        exact congrArg (fun u => ((u + ∫ y, η * (f y * r y) ∂μ) +
          ∫ _ : Ω, Real.log z ∂μ) + ∫ y, Real.log z * r y ∂μ)
          (integral_add hterm1 hterm2)
      _ = η * ((∫ y, f y ∂μ) + (∫ y, f y * w y ∂μ) / z) +
          2 * Real.log z := by
        simp only [integral_const_mul, integral_sub hr_int (integrable_const _),
          integral_const, smul_eq_mul]
        rw [hr_integral, hfr_integral]
        simp
        ring
  dsimp only
  change η * ((∫ y, f y ∂μ) + (∫ y, f y * w y ∂μ) / z) +
      2 * Real.log z ≤ (4 : ℝ) / 3 * η ^ 3
  rw [← hφ_integral]
  exact hφ_le

@[blueprint "lem:continuous-hedge-log-partition-stability"
  (statement := /-- Let \(d,T\in\mathbb N\), let
  \(\mathcal X\subseteq\mathbb R^d\), let \(f_s:\mathbb R^d\to\mathbb R\) for
  \(s\in\mathbb N\), and fix \(t\in\mathbb N\) and \(\eta\in\mathbb R\).  Assume that
  \(\mathcal X\) is nonempty and convex, \(t<T\), and \(0\leq\eta\leq1\).  For every
  \(s\leq T\), assume that the intrinsic exponential-weights measure \(\mu_s\) from
  \cref{def:continuous-hedge-weight-measure} has strictly positive finite mass.  Let
  \(\lambda\) be the intrinsic Hausdorff measure restricted to \(\mathcal X\), and assume
  that the nonnegative extended-real-valued cumulative density
  \[
    \rho_t(y)=\exp\left(-\eta\sum_{s=0}^{t-1}f_s(y)\right)
  \]
  is almost everywhere measurable with respect to \(\lambda\).  If \(f_t\) is convex on
  \(\mathcal X\) and \(|f_t(y)|\leq1\) for every \(y\in\mathcal X\), then
  \[
    \eta\left(\int f_t\,dp_t+\int f_t\,dp_{t+1}\right)
      +2(\Phi_{t+1}-\Phi_t)\leq\frac43\eta^3,
  \]
  with \(p_s\) and \(\Phi_s\) as in
  \cref{def:continuous-hedge-distribution,def:continuous-hedge-log-mass}. -/)
  (proof := /-- Let \(\lambda\) be the intrinsic restricted Hausdorff measure, let
  \(\rho_t\) be the cumulative density in the statement, and put
  \(w(y)=e^{-\eta f_t(y)}\).  By
  \cref{lem:continuous-hedge-convex-loss-regularity}, \(f_t\) is almost everywhere
  measurable for \(\lambda\).  By
  \cref{lem:continuous-hedge-intrinsic-measure-support}, \(\lambda\)-almost every point
  belongs to \(\mathcal X\); hence \(|f_t|\leq1\) almost everywhere for every measure
  obtained from \(\lambda\) by the densities and normalizations below.

  The assumed measurability of \(\rho_t\), together with that of \(w\), permits the
  with-density chain rule.  Since
  \[
    \rho_{t+1}(y)=\rho_t(y)w(y),
  \]
  the measures in \cref{def:continuous-hedge-weight-measure} satisfy
  \(\mu_{t+1}=\mu_t\mathbin{\mathrm{withDensity}}w\).  Write
  \(a_s=\mu_s(\mathbb R^d)\), viewed as a positive real number.  The positive finite mass
  assumptions and \cref{def:continuous-hedge-distribution} give
  \(p_s=a_s^{-1}\mu_s\) for \(s=t,t+1\).  The with-density integration formula therefore
  yields
  \[
    Z:=\int w\,dp_t=\frac{a_{t+1}}{a_t},
    \qquad
    \int f_t\,dp_{t+1}=
      \frac{\int f_t w\,dp_t}{Z}.
  \]
  Moreover, \cref{def:continuous-hedge-log-mass} and positivity give
  \(\Phi_{t+1}-\Phi_t=\log Z\).  Applying
  \cref{lem:continuous-hedge-exponential-tilt-stability} to the probability measure
  \(p_t\), the almost everywhere measurable function \(f_t\), and the bound
  \(|f_t|\leq1\), and then substituting the two displayed identities proves the asserted
  inequality. -/)
  (title := /-- Third-order stability of the Continuous Hedge log-partition -/)
  (latexEnv := "lemma")]
lemma continuous_hedge_log_partition_stability {d T : ℕ} (X : Set (oco_point d))
    (loss : ℕ → oco_point d → ℝ) (η : ℝ) (t : ℕ)
    (hX : X.Nonempty) (hconv : Convex ℝ X)
    (hloss_conv : ConvexOn ℝ X (loss t))
    (hloss_bound : ∀ y ∈ X, |loss t y| ≤ 1)
    (hcumulative_meas : AEMeasurable
      (fun y => ENNReal.ofReal (Real.exp (-η * ∑ s ∈ Finset.range t, loss s y)))
      ((MeasureTheory.Measure.euclideanHausdorffMeasure
        (Module.finrank ℝ (affineSpan ℝ X).direction)).restrict X))
    (hη_nonneg : 0 ≤ η) (hη_le_one : η ≤ 1) (ht : t < T)
    (hmass : ∀ s, s ≤ T →
      continuous_hedge_weight_measure X loss η s Set.univ ≠ 0 ∧
      continuous_hedge_weight_measure X loss η s Set.univ ≠ ⊤) :
    η * ((∫ y, loss t y ∂(continuous_hedge_distribution X loss η t)) +
      ∫ y, loss t y ∂(continuous_hedge_distribution X loss η (t + 1))) +
      2 * (continuous_hedge_log_mass X loss η (t + 1) -
        continuous_hedge_log_mass X loss η t) ≤
      (4 : ℝ) / 3 * η ^ 3 := by
  classical
  let base : Measure (oco_point d) :=
    (MeasureTheory.Measure.euclideanHausdorffMeasure
      (Module.finrank ℝ (affineSpan ℝ X).direction)).restrict X
  let ρ : oco_point d → ENNReal := fun y =>
    ENNReal.ofReal (Real.exp (-η * ∑ s ∈ Finset.range t, loss s y))
  let κ : oco_point d → ENNReal := fun y =>
    ENNReal.ofReal (Real.exp (-η * loss t y))
  let w : oco_point d → ℝ := fun y => Real.exp (-η * loss t y)
  let μ₀ : Measure (oco_point d) := continuous_hedge_weight_measure X loss η t
  let μ₁ : Measure (oco_point d) := continuous_hedge_weight_measure X loss η (t + 1)
  let p₀ : Measure (oco_point d) := continuous_hedge_distribution X loss η t
  let p₁ : Measure (oco_point d) := continuous_hedge_distribution X loss η (t + 1)
  have ht_le : t ≤ T := ht.le
  have ht1_le : t + 1 ≤ T := Nat.succ_le_iff.mpr ht
  have hm₀ : μ₀ Set.univ ≠ 0 ∧ μ₀ Set.univ ≠ ⊤ := by
    simpa [μ₀] using hmass t ht_le
  have hm₁ : μ₁ Set.univ ≠ 0 ∧ μ₁ Set.univ ≠ ⊤ := by
    simpa [μ₁] using hmass (t + 1) ht1_le
  letI : IsFiniteMeasure μ₀ := ⟨lt_top_iff_ne_top.mpr hm₀.2⟩
  letI : NeZero μ₀ := ⟨Measure.measure_univ_ne_zero.mp hm₀.1⟩
  letI : IsFiniteMeasure μ₁ := ⟨lt_top_iff_ne_top.mpr hm₁.2⟩
  letI : NeZero μ₁ := ⟨Measure.measure_univ_ne_zero.mp hm₁.1⟩
  have hp₀ : p₀ = (μ₀ Set.univ)⁻¹ • μ₀ := by
    simp [p₀, μ₀, continuous_hedge_distribution, hX, hm₀]
  have hp₁ : p₁ = (μ₁ Set.univ)⁻¹ • μ₁ := by
    simp [p₁, μ₁, continuous_hedge_distribution, hX, hm₁]
  letI : IsProbabilityMeasure p₀ := by
    rw [hp₀]
    infer_instance
  have hfbase : AEMeasurable (loss t) base := by
    simpa [base] using
      continuous_hedge_convex_loss_regularity X (loss t) hconv hloss_conv
  have hρbase : AEMeasurable ρ base := by
    simpa [ρ, base] using hcumulative_meas
  have hκbase : AEMeasurable κ base := by
    exact ((hfbase.const_mul (-η)).exp).ennreal_ofReal
  have hdensity :
      (fun y => ENNReal.ofReal
        (Real.exp (-η * ∑ s ∈ Finset.range (t + 1), loss s y))) =
        fun y => ρ y * κ y := by
    funext y
    dsimp [ρ, κ]
    rw [Finset.sum_range_succ, mul_add, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hμchain : μ₁ = μ₀.withDensity κ := by
    dsimp [μ₁, μ₀, continuous_hedge_weight_measure]
    rw [hdensity]
    exact withDensity_mul₀ hρbase hκbase
  have hκμ₀ : AEMeasurable κ μ₀ := by
    apply hκbase.mono_ac
    exact withDensity_absolutelyContinuous _ _
  have hκfinite : ∀ᵐ y ∂μ₀, κ y < ⊤ := by
    filter_upwards [] with y
    exact ENNReal.ofReal_lt_top
  let a₀ : ℝ := (μ₀ Set.univ).toReal
  let a₁ : ℝ := (μ₁ Set.univ).toReal
  have ha₀_pos : 0 < a₀ := ENNReal.toReal_pos hm₀.1 hm₀.2
  have ha₁_pos : 0 < a₁ := ENNReal.toReal_pos hm₁.1 hm₁.2
  have hm₁_real : a₁ = ∫ y, w y ∂μ₀ := by
    have h := integral_withDensity_eq_integral_toReal_smul₀ hκμ₀ hκfinite
      (fun _ : oco_point d => (1 : ℝ))
    rw [← hμchain] at h
    simpa [a₁, κ, w, measureReal_def, ENNReal.toReal_ofReal,
      (Real.exp_pos _).le] using h
  have hμ₁_integral : (∫ y, loss t y ∂μ₁) =
      ∫ y, loss t y * w y ∂μ₀ := by
    rw [hμchain]
    have h := integral_withDensity_eq_integral_toReal_smul₀ hκμ₀ hκfinite (loss t)
    simpa [κ, w, ENNReal.toReal_ofReal, (Real.exp_pos _).le, mul_comm] using h
  have hμ₀base : μ₀ = base.withDensity ρ := by
    rfl
  have hfμ₀ : AEMeasurable (loss t) μ₀ := by
    rw [hμ₀base]
    exact hfbase.mono_ac (withDensity_absolutelyContinuous _ _)
  have hfp₀ : AEMeasurable (loss t) p₀ := by
    rw [hp₀]
    exact hfμ₀.smul_measure _
  have hbasesupp : ∀ᵐ y ∂base, y ∈ X := by
    simpa [base] using continuous_hedge_intrinsic_measure_support X hX hconv
  have hμ₀supp : ∀ᵐ y ∂μ₀, y ∈ X := by
    rw [hμ₀base]
    exact (withDensity_absolutelyContinuous base ρ).ae_le hbasesupp
  have hp₀supp : ∀ᵐ y ∂p₀, y ∈ X := by
    rw [hp₀]
    exact Measure.ae_smul_measure hμ₀supp _
  have hboundp₀ : ∀ᵐ y ∂p₀, |loss t y| ≤ 1 := by
    filter_upwards [hp₀supp] with y hy
    exact hloss_bound y hy
  have htilt := continuous_hedge_exponential_tilt_stability p₀ (loss t)
    hfp₀ hboundp₀ η hη_nonneg hη_le_one
  dsimp only at htilt
  have hp₀_integral (g : oco_point d → ℝ) :
      (∫ y, g y ∂p₀) = a₀⁻¹ * ∫ y, g y ∂μ₀ := by
    rw [hp₀, integral_smul_measure]
    simp [a₀, hm₀.2]
  have hp₁_integral (g : oco_point d → ℝ) :
      (∫ y, g y ∂p₁) = a₁⁻¹ * ∫ y, g y ∂μ₁ := by
    rw [hp₁, integral_smul_measure]
    simp [a₁, hm₁.2]
  have hz : (∫ y, w y ∂p₀) = a₁ / a₀ := by
    rw [hp₀_integral, ← hm₁_real]
    field_simp
  have hnum : (∫ y, loss t y * w y ∂p₀) =
      a₀⁻¹ * ∫ y, loss t y * w y ∂μ₀ := hp₀_integral _
  have hp₁_loss : (∫ y, loss t y ∂p₁) =
      (∫ y, loss t y * w y ∂p₀) / (∫ y, w y ∂p₀) := by
    rw [hp₁_integral, hμ₁_integral, hnum, hz]
    field_simp
  have hlog : Real.log a₁ - Real.log a₀ = Real.log (∫ y, w y ∂p₀) := by
    rw [hz, Real.log_div ha₁_pos.ne' ha₀_pos.ne']
  change η * ((∫ y, loss t y ∂p₀) + ∫ y, loss t y ∂p₁) +
      2 * (Real.log a₁ - Real.log a₀) ≤ (4 : ℝ) / 3 * η ^ 3
  rw [hp₁_loss, hlog]
  simpa [w] using htilt

@[blueprint "lem:continuous-hedge-affine-localization"
  (statement := /-- Let \(d,T\in\mathbb N\) with \(T\geq2\), let
  \(\mathcal X\subseteq\mathbb R^d\) be nonempty and convex, let
  \(0\leq\eta\leq1\), and fix \(u\in\mathcal X\).  For each \(t\in\mathbb N\), let
  \(f_t:\mathbb R^d\to\mathbb R\).  Assume that, for every \(t<T\), the function \(f_t\)
  is convex on \(\mathcal X\) and satisfies \(|f_t(y)|\leq1\) for every
  \(y\in\mathcal X\).  Let \(\mu_t\) be the intrinsic exponential-weights measure from
  \cref{def:continuous-hedge-weight-measure}, and assume
  \(0<\mu_t(\mathbb R^d)<\infty\) for every \(t\leq T\).  With \(\Phi_t\) as in
  \cref{def:continuous-hedge-log-mass}, one has
  \[
    \Phi_0-\Phi_T-\eta\sum_{t=0}^{T-1}f_t(u)
      \leq d\log T+2\eta.
  \] -/)
  (proof := /-- Let \(k\) be the dimension of the direction space of the affine hull of
  \(\mathcal X\), let \(\lambda=\mathcal H^k_{\mathrm E}|_{\mathcal X}\) be the intrinsic
  reference measure in \cref{def:continuous-hedge-weight-measure}, and put
  \(\delta=T^{-1}\).  Since \(T\geq2\), \(0<\delta<1\).  For a fixed \(u\in\mathcal X\),
  the affine contraction
  \[
    F_\delta(y)=(1-\delta)u+\delta y
  \]
  maps \(\mathcal X\) into itself.  Convexity and the bound \(|f_t|\leq1\) imply, for every
  \(y\in\mathcal X\),
  \[
    f_t(F_\delta(y))
      \leq(1-\delta)f_t(u)+\delta f_t(y)
      \leq f_t(u)+2\delta.
  \]
  Summing over \(t<T\) gives
  \(\sum_{t<T}f_t(F_\delta(y))\leq\sum_{t<T}f_t(u)+2T\delta\).

  Convexity makes \(\mathcal X\) null-measurable for intrinsic Hausdorff measure, and
  \cref{lem:continuous-hedge-convex-loss-regularity} makes each loss, hence the finite
  exponential density, almost everywhere measurable.  Consequently the restriction and
  with-density change-of-variables formulas apply.  Euclidean-normalized Hausdorff measure on
  the affine hull scales under the affine equivalence \(F_\delta\) by \(\delta^k\).
  Integrating the preceding pointwise estimate over
  \(F_\delta(\mathcal X)\subseteq\mathcal X\), and using \(2T\delta=2\), yields
  \[
    \mu_T(\mathbb R^d)
      \geq e^{-\eta(\sum_{t<T}f_t(u)+2)}
        \delta^k\mu_0(\mathbb R^d).
  \]
  Both masses are positive and finite by hypothesis, so logarithms preserve this inequality.
  By \cref{def:continuous-hedge-log-mass},
  \[
    \Phi_0-\Phi_T-\eta\sum_{t<T}f_t(u)
      \leq k\log T+2\eta.
  \]
  Finally \(k\leq d\) and \(\log T\geq0\), which proves the displayed bound. -/)
  (title := /-- Affine-volume localization around a comparator -/)
  (latexEnv := "lemma")]
lemma continuous_hedge_affine_localization {d T : ℕ} (X : Set (oco_point d))
    (loss : ℕ → oco_point d → ℝ) (η : ℝ) (u : oco_point d)
    (hT : 2 ≤ T) (hX : X.Nonempty) (hconv : Convex ℝ X) (hu : u ∈ X)
    (hloss_conv : ∀ t, t < T → ConvexOn ℝ X (loss t))
    (hloss_bound : ∀ t, t < T → ∀ y ∈ X, |loss t y| ≤ 1)
    (hη_nonneg : 0 ≤ η) (hη_le_one : η ≤ 1)
    (hmass : ∀ t, t ≤ T →
      continuous_hedge_weight_measure X loss η t Set.univ ≠ 0 ∧
      continuous_hedge_weight_measure X loss η t Set.univ ≠ ⊤) :
    continuous_hedge_log_mass X loss η 0 -
      continuous_hedge_log_mass X loss η T -
      η * ∑ t ∈ Finset.range T, loss t u ≤
      (d : ℝ) * Real.log (T : ℝ) + 2 * η := by
  classical
  let k : ℕ := Module.finrank ℝ (affineSpan ℝ X).direction
  let ν : Measure (oco_point d) :=
    MeasureTheory.Measure.euclideanHausdorffMeasure k
  let δ : ℝ := ((T : ℝ))⁻¹
  let F : oco_point d → oco_point d := fun y => (1 - δ) • u + δ • y
  let A : Set (oco_point d) := F '' X
  let S : ℝ := ∑ t ∈ Finset.range T, loss t u
  let r : ENNReal := ENNReal.ofReal δ ^ k
  have hT_pos : (0 : ℝ) < T := by
    exact_mod_cast (show 0 < T by omega)
  have hδ_pos : 0 < δ := by
    exact inv_pos.mpr hT_pos
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
  have hδ_le_one : δ ≤ 1 := by
    dsimp [δ]
    apply (inv_le_one₀ hT_pos).2
    exact_mod_cast (show 1 ≤ T by omega)
  have hF_mem : ∀ y ∈ X, F y ∈ X := by
    intro y hy
    dsimp [F]
    exact hconv hu hy (sub_nonneg.mpr hδ_le_one) hδ_pos.le (by ring)
  have hA_subset : A ⊆ X := by
    rintro z ⟨y, hy, rfl⟩
    exact hF_mem y hy
  have hloss_F : ∀ t, t < T → ∀ y ∈ X,
      loss t (F y) ≤ loss t u + 2 * δ := by
    intro t ht y hy
    have hc := (hloss_conv t ht).2 hu hy (sub_nonneg.mpr hδ_le_one)
      hδ_pos.le (by ring)
    have hu_bounds := abs_le.mp (hloss_bound t ht u hu)
    have hy_bounds := abs_le.mp (hloss_bound t ht y hy)
    dsimp [F]
    calc
      loss t ((1 - δ) • u + δ • y) ≤
          (1 - δ) • loss t u + δ • loss t y := hc
      _ ≤ loss t u + 2 * δ := by
        dsimp only [smul_eq_mul]
        nlinarith
  have hsum_F : ∀ y ∈ X,
      (∑ t ∈ Finset.range T, loss t (F y)) ≤ S + 2 := by
    intro y hy
    calc
      (∑ t ∈ Finset.range T, loss t (F y)) ≤
          ∑ t ∈ Finset.range T, (loss t u + 2 * δ) := by
        exact Finset.sum_le_sum fun t ht => hloss_F t (Finset.mem_range.mp ht) y hy
      _ = S + 2 := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        dsimp [S, δ]
        field_simp
  have hX_null : NullMeasurableSet X ν := by
    let s : AffineSubspace ℝ (oco_point d) := affineSpan ℝ X
    let p : s := ⟨hX.choose, subset_affineSpan ℝ X hX.choose_spec⟩
    letI : Nonempty s := ⟨p⟩
    let e : s.direction ≃ᵢ s := IsometryEquiv.vaddConst p
    let q : s.direction → oco_point d := fun v => (e v : s)
    let C : Set s.direction := q ⁻¹' X
    let qA : s.direction →ᵃ[ℝ] oco_point d :=
      { toFun := q
        linear := s.direction.subtype
        map_vadd' := by
          intro v x
          simp [q, e, add_assoc] }
    have hCconv : Convex ℝ C := by
      exact hconv.affine_preimage qA
    let νV : Measure s.direction :=
      MeasureTheory.Measure.euclideanHausdorffMeasure
        (Module.finrank ℝ s.direction)
    have hCnull : NullMeasurableSet C νV := by
      exact hCconv.nullMeasurableSet (μ :=
        (MeasureTheory.Measure.euclideanHausdorffMeasure
          (Module.finrank ℝ s.direction) : Measure s.direction))
    have hsmeas : MeasurableSet (s : Set (oco_point d)) :=
      (AffineSubspace.closed_of_finiteDimensional s).measurableSet
    have hq : MeasurableEmbedding q := by
      dsimp [q]
      exact (MeasurableEmbedding.subtype_coe hsmeas).comp
        e.toHomeomorph.measurableEmbedding
    have hq_isom : Isometry q := by
      intro x y
      simpa [q] using (isometry_subtype_coe.comp e.isometry x y)
    have hrange : Set.range q = (s : Set (oco_point d)) := by
      ext x
      constructor
      · rintro ⟨v, rfl⟩
        exact (e v).property
      · intro hx
        refine ⟨e.symm ⟨x, hx⟩, ?_⟩
        simp [q]
    have hmap_full : νV.map q = ν.restrict (s : Set (oco_point d)) := by
      dsimp [νV, ν, k]
      rw [show affineSpan ℝ X = s from rfl]
      rw [hq_isom.map_euclideanHausdorffMeasure, hrange]
    have hqC : q '' C = X := by
      ext x
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact hv
      · intro hx
        have hxs : x ∈ (s : Set (oco_point d)) := subset_affineSpan ℝ X hx
        have hxrange : x ∈ Set.range q := by
          rw [hrange]
          exact hxs
        obtain ⟨v, hv⟩ := hxrange
        refine ⟨v, ?_, hv⟩
        change q v ∈ X
        rw [hv]
        exact hx
    have hqCnull : NullMeasurableSet (q '' C) (νV.map q) := by
      apply MeasureTheory.Measure.NullMeasurableSet.image q (νV.map q) hq.injective
      · intro t ht
        exact ((hq.measurableSet_image).2 ht).nullMeasurableSet
      · rw [hq.comap_map]
        exact hCnull
    rw [hmap_full, hqC] at hqCnull
    exact (nullMeasurableSet_restrict_of_subset (subset_affineSpan ℝ X)).mp hqCnull
  have hA_volume : ν A = r * ν X := by
    let v : oco_point d := (1 - δ) • u
    let B : Set (oco_point d) := (fun y => δ • y) '' X
    have himage : A = (fun w => v + w) '' B := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨δ • y, ⟨y, hy, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, rfl⟩
    rw [himage]
    rw [isometry_add_left v |>.euclideanHausdorffMeasure_image]
    change ν ((fun y => δ • y) '' X) = _
    rw [Set.image_smul]
    have hcoef : ENNReal.ofNNReal ‖δ‖₊ = ENNReal.ofReal δ := by
      rw [ENNReal.ofReal_eq_coe_nnreal hδ_pos.le]
      congr 2
      ext
      simp [Real.norm_eq_abs, abs_of_pos hδ_pos]
    have hscale :=
      MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀ k hδ_ne X
    rw [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow] at hscale
    rw [hcoef] at hscale
    simpa [ν, r] using hscale
  have hzero_mass :
      continuous_hedge_weight_measure X loss η 0 Set.univ = ν X := by
    simp [continuous_hedge_weight_measure, ν, k]
  have hbase_A :
      ν.restrict X A = r *
        continuous_hedge_weight_measure X loss η 0 Set.univ := by
    rw [Measure.restrict_apply₀' hX_null]
    rw [Set.inter_eq_self_of_subset_left hA_subset]
    rw [hA_volume, hzero_mass]
  have hsum_ae : AEMeasurable
      (fun y => ∑ t ∈ Finset.range T, loss t y) (ν.restrict X) := by
    have heq : (fun y => ∑ t ∈ Finset.range T, loss t y) =
        ∑ t ∈ Finset.range T, loss t := by
      funext y
      simp
    rw [heq]
    simpa [ν, k] using
      (Finset.aemeasurable_sum (Finset.range T) fun t ht =>
        continuous_hedge_convex_loss_regularity X (loss t) hconv
          (hloss_conv t (Finset.mem_range.mp ht)))
  have hdensity_ae : AEMeasurable
      (fun y => ENNReal.ofReal
        (Real.exp (-η * ∑ t ∈ Finset.range T, loss t y))) (ν.restrict X) := by
    exact ((hsum_ae.const_mul (-η)).exp).ennreal_ofReal
  have hdensity_lower : ∀ y ∈ A,
      ENNReal.ofReal (Real.exp (-η * (S + 2))) ≤
        ENNReal.ofReal (Real.exp (-η * ∑ t ∈ Finset.range T, loss t y)) := by
    rintro y ⟨z, hz, rfl⟩
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (hsum_F z hz) (neg_nonpos.mpr hη_nonneg)
  have hmass_lower :
      ENNReal.ofReal (Real.exp (-η * (S + 2))) *
          r *
          continuous_hedge_weight_measure X loss η 0 Set.univ ≤
        continuous_hedge_weight_measure X loss η T Set.univ := by
    calc
      ENNReal.ofReal (Real.exp (-η * (S + 2))) *
            r *
            continuous_hedge_weight_measure X loss η 0 Set.univ =
          ∫⁻ _ in A, ENNReal.ofReal (Real.exp (-η * (S + 2))) ∂(ν.restrict X) := by
            rw [MeasureTheory.setLIntegral_const, hbase_A]
            ring
      _ ≤ ∫⁻ y in A, ENNReal.ofReal
            (Real.exp (-η * ∑ t ∈ Finset.range T, loss t y)) ∂(ν.restrict X) := by
          exact MeasureTheory.setLIntegral_mono_ae hdensity_ae.restrict
            (Filter.Eventually.of_forall fun y hy => hdensity_lower y hy)
      _ ≤ continuous_hedge_weight_measure X loss η T A := by
          exact MeasureTheory.withDensity_apply_le _ _
      _ ≤ continuous_hedge_weight_measure X loss η T Set.univ :=
          measure_mono (Set.subset_univ A)
  have hM0_ne : continuous_hedge_weight_measure X loss η 0 Set.univ ≠ 0 :=
    (hmass 0 (Nat.zero_le T)).1
  have hM0_top : continuous_hedge_weight_measure X loss η 0 Set.univ ≠ ⊤ :=
    (hmass 0 (Nat.zero_le T)).2
  have hMT_ne : continuous_hedge_weight_measure X loss η T Set.univ ≠ 0 :=
    (hmass T le_rfl).1
  have hMT_top : continuous_hedge_weight_measure X loss η T Set.univ ≠ ⊤ :=
    (hmass T le_rfl).2
  have hM0_pos : 0 <
      (continuous_hedge_weight_measure X loss η 0 Set.univ).toReal :=
    ENNReal.toReal_pos hM0_ne hM0_top
  have hMT_pos : 0 <
      (continuous_hedge_weight_measure X loss η T Set.univ).toReal :=
    ENNReal.toReal_pos hMT_ne hMT_top
  have hreal_lower := ENNReal.toReal_mono hMT_top hmass_lower
  have hscale_real : r.toReal = δ ^ k := by
    simp [r, hδ_pos.le]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    hscale_real] at hreal_lower
  have hlower_pos : 0 < Real.exp (-η * (S + 2)) * δ ^ k *
      (continuous_hedge_weight_measure X loss η 0 Set.univ).toReal := by
    positivity
  have hlog := Real.log_le_log hlower_pos hreal_lower
  rw [Real.log_mul (mul_ne_zero (Real.exp_ne_zero _)
      (pow_ne_zero _ hδ_ne)) (ne_of_gt hM0_pos),
    Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ hδ_ne),
    Real.log_exp, Real.log_pow] at hlog
  have hk : k ≤ d := by
    dsimp [k]
    calc
      Module.finrank ℝ (affineSpan ℝ X).direction ≤
          Module.finrank ℝ (oco_point d) := Submodule.finrank_le _
      _ = d := by simp [oco_point]
  have hlogT : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ T by omega))
  have hk_real : (k : ℝ) * Real.log (T : ℝ) ≤
      (d : ℝ) * Real.log (T : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ hlogT
    exact_mod_cast hk
  dsimp [δ] at hlog
  rw [Real.log_inv] at hlog
  dsimp [continuous_hedge_log_mass, S]
  nlinarith

@[blueprint "lem:continuous-hedge-master-bound"
  (statement := /-- Let \(d,T\in\mathbb N\) satisfy \(d>0\) and \(T\geq2\), and let
  \(\mathcal X\subseteq\mathbb R^d\) be nonempty and convex.  For each \(t\in\mathbb N\),
  let \(f_t:\mathbb R^d\to\mathbb R\), and assume that, for every \(t<T\), the function
  \(f_t\) is convex on \(\mathcal X\) and satisfies
  \(|f_t(y)|\leq1\) for every \(y\in\mathcal X\).  Fix \(0<\eta\leq1\).  Suppose that,
  for every \(t\leq T\), the unnormalized exponential-weights measure \(\mu_t\) from
  \cref{def:continuous-hedge-weight-measure} has strictly positive finite total mass.
  If the measure sequence \(p\) and action sequence \(x\) form a Continuous Hedge execution
  through time \(T\) in the sense of \cref{def:is-continuous-hedge}, then
  \[
    \operatorname{Reg}_{\rm Alt}
    \leq
    \min\left\{4T,\,
      \frac{2d\log T}{\eta}+\frac43T\eta^2+4\right\}.
  \]
  The first bound is the loss-range estimate; the second is the
  log-partition/localization estimate. -/)
  (proof := /-- For each \(t<T\),
  \cref{lem:continuous-hedge-convex-loss-regularity} makes every \(f_s\), \(s<t\),
  almost everywhere measurable with respect to the intrinsic reference measure on
  \(\mathcal X\).  Almost everywhere measurability is preserved by finite sums,
  multiplication by \(-\eta\), the real exponential, and the embedding into the
  nonnegative extended reals.  Consequently the cumulative density
  \[
    y\longmapsto\exp\left(-\eta\sum_{s=0}^{t-1}f_s(y)\right)
  \]
  satisfies the measurability hypothesis of
  \cref{lem:continuous-hedge-log-partition-stability}.  The execution identities identify
  its two distributions with \(p_t\) and \(p_{t+1}\); hence each stability summand is at
  most \(\frac43\eta^3\).  Summing over \(0\leq t<T\) gives an upper bound of
  \(\frac43T\eta^3\) for the first sum below.

  Fix \(u\in\mathcal X\).  By
  \cref{lem:continuous-hedge-regret-decomposition}, its scaled comparator regret is bounded
  by that stability sum plus twice the log-partition endpoint expression.  By
  \cref{lem:continuous-hedge-affine-localization}, the endpoint expression is at most
  \(d\log T+2\eta\).  Therefore
  \[
    \eta\operatorname{Reg}_{\rm Alt}(u)
      \leq \frac43T\eta^3+2d\log T+4\eta.
  \]
  Division by \(\eta>0\) gives
  \[
    \operatorname{Reg}_{\rm Alt}(u)
      \leq \frac{2d\log T}{\eta}+\frac43T\eta^2+4.
  \]

  Independently, \cref{def:is-continuous-hedge} puts \(x_t,x_{t+1}\) in \(\mathcal X\).
  Thus the loss bound gives
  \(f_t(x_t)+f_t(x_{t+1})-2f_t(u)\leq4\) for every \(t<T\), whence
  \(\operatorname{Reg}_{\rm Alt}(u)\leq4T\).  Both estimates hold for every
  \(u\in\mathcal X\).  Taking the supremum in
  \cref{def:alternating-regret}, which is over a nonempty set and is bounded above by either
  displayed quantity, proves the asserted minimum bound. -/)
  (title := /-- Master alternating-regret bound for Continuous Hedge -/)
  (latexEnv := "lemma")]
lemma continuous_hedge_master_bound {d T : ℕ} (X : Set (oco_point d))
    (loss : ℕ → oco_point d → ℝ) (η : ℝ)
    (p : ℕ → Measure (oco_point d)) (x : ℕ → oco_point d)
    (hT : 2 ≤ T) (hd : 0 < d) (hX : X.Nonempty) (hconv : Convex ℝ X)
    (hloss_conv : ∀ t, t < T → ConvexOn ℝ X (loss t))
    (hloss_bound : ∀ t, t < T → ∀ y ∈ X, |loss t y| ≤ 1)
    (hη_pos : 0 < η) (hη_le_one : η ≤ 1)
    (hmass : ∀ t, t ≤ T →
      continuous_hedge_weight_measure X loss η t Set.univ ≠ 0 ∧
      continuous_hedge_weight_measure X loss η t Set.univ ≠ ⊤)
    (hexec : is_continuous_hedge T X loss η p x) :
    alternating_regret T X loss x ≤
      min (4 * (T : ℝ))
        (2 * (d : ℝ) * Real.log (T : ℝ) / η +
          (4 : ℝ) / 3 * (T : ℝ) * η ^ 2 + 4) := by
  classical
  have hη_nonneg : 0 ≤ η := hη_pos.le
  have hcumulative_meas (t : ℕ) (ht : t < T) : AEMeasurable
      (fun y => ENNReal.ofReal (Real.exp (-η * ∑ s ∈ Finset.range t, loss s y)))
      ((MeasureTheory.Measure.euclideanHausdorffMeasure
        (Module.finrank ℝ (affineSpan ℝ X).direction)).restrict X) := by
    have hsum : AEMeasurable (fun y => ∑ s ∈ Finset.range t, loss s y)
        ((MeasureTheory.Measure.euclideanHausdorffMeasure
          (Module.finrank ℝ (affineSpan ℝ X).direction)).restrict X) := by
      refine (Finset.aemeasurable_sum (Finset.range t) fun s hs =>
        continuous_hedge_convex_loss_regularity X (loss s) hconv
          (hloss_conv s ((Finset.mem_range.mp hs).trans ht))).congr ?_
      filter_upwards with y
      simp
    exact ((hsum.const_mul (-η)).exp).ennreal_ofReal
  have hstability (t : ℕ) (ht : t < T) :
      η * ((∫ y, loss t y ∂(p t)) + ∫ y, loss t y ∂(p (t + 1))) +
        2 * (continuous_hedge_log_mass X loss η (t + 1) -
          continuous_hedge_log_mass X loss η t) ≤
        (4 : ℝ) / 3 * η ^ 3 := by
    rw [(hexec t ht.le).1, (hexec (t + 1) (Nat.succ_le_iff.mpr ht)).1]
    exact continuous_hedge_log_partition_stability X loss η t hX hconv
      (hloss_conv t ht) (hloss_bound t ht) (hcumulative_meas t ht)
      hη_nonneg hη_le_one ht hmass
  have hstability_sum :
      ∑ t ∈ Finset.range T,
          (η * ((∫ y, loss t y ∂(p t)) + ∫ y, loss t y ∂(p (t + 1))) +
            2 * (continuous_hedge_log_mass X loss η (t + 1) -
              continuous_hedge_log_mass X loss η t)) ≤
        (4 : ℝ) / 3 * (T : ℝ) * η ^ 3 := by
    calc
      _ ≤ ∑ _t ∈ Finset.range T, (4 : ℝ) / 3 * η ^ 3 := by
        exact Finset.sum_le_sum fun t ht => hstability t (Finset.mem_range.mp ht)
      _ = (4 : ℝ) / 3 * (T : ℝ) * η ^ 3 := by
        simp
        ring
  have hcomparator_analytic (u : oco_point d) (hu : u ∈ X) :
      comparator_alternating_regret T loss x u ≤
        2 * (d : ℝ) * Real.log (T : ℝ) / η +
          (4 : ℝ) / 3 * (T : ℝ) * η ^ 2 + 4 := by
    have hdecomp := continuous_hedge_regret_decomposition X loss η p x u
      hη_nonneg hu hloss_conv hloss_bound hexec
    have hlocal := continuous_hedge_affine_localization X loss η u hT hX hconv hu
      hloss_conv hloss_bound hη_nonneg hη_le_one hmass
    have hscaled : η * comparator_alternating_regret T loss x u ≤
        (4 : ℝ) / 3 * (T : ℝ) * η ^ 3 +
          2 * ((d : ℝ) * Real.log (T : ℝ) + 2 * η) := by
      calc
        η * comparator_alternating_regret T loss x u ≤
            (∑ t ∈ Finset.range T,
              (η * ((∫ y, loss t y ∂(p t)) + ∫ y, loss t y ∂(p (t + 1))) +
                2 * (continuous_hedge_log_mass X loss η (t + 1) -
                  continuous_hedge_log_mass X loss η t))) +
              2 * (continuous_hedge_log_mass X loss η 0 -
                continuous_hedge_log_mass X loss η T -
                η * ∑ t ∈ Finset.range T, loss t u) := hdecomp
        _ ≤ (4 : ℝ) / 3 * (T : ℝ) * η ^ 3 +
            2 * ((d : ℝ) * Real.log (T : ℝ) + 2 * η) :=
          add_le_add hstability_sum (mul_le_mul_of_nonneg_left hlocal (by norm_num))
    apply (mul_le_mul_iff_of_pos_left hη_pos).mp
    calc
      η * comparator_alternating_regret T loss x u ≤
          (4 : ℝ) / 3 * (T : ℝ) * η ^ 3 +
            2 * ((d : ℝ) * Real.log (T : ℝ) + 2 * η) := hscaled
      _ = η * (2 * (d : ℝ) * Real.log (T : ℝ) / η +
          (4 : ℝ) / 3 * (T : ℝ) * η ^ 2 + 4) := by
        field_simp [hη_pos.ne']
        ring
  have hcomparator_range (u : oco_point d) (hu : u ∈ X) :
      comparator_alternating_regret T loss x u ≤ 4 * (T : ℝ) := by
    unfold comparator_alternating_regret
    calc
      (∑ t ∈ Finset.range T,
          (loss t (x t) + loss t (x (t + 1)) - 2 * loss t u)) ≤
          ∑ _t ∈ Finset.range T, (4 : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        have htT : t < T := Finset.mem_range.mp ht
        have hxt : x t ∈ X := (hexec t htT.le).2.2.2.2.2
        have hxt1 : x (t + 1) ∈ X :=
          (hexec (t + 1) (Nat.succ_le_iff.mpr htT)).2.2.2.2.2
        have hxt_upper := (abs_le.mp (hloss_bound t htT (x t) hxt)).2
        have hxt1_upper := (abs_le.mp (hloss_bound t htT (x (t + 1)) hxt1)).2
        have hu_lower := (abs_le.mp (hloss_bound t htT u hu)).1
        linarith
      _ = 4 * (T : ℝ) := by
        simp
        ring
  have hsSup_le (B : ℝ)
      (hB : ∀ u ∈ X, comparator_alternating_regret T loss x u ≤ B) :
      alternating_regret T X loss x ≤ B := by
    unfold alternating_regret
    apply csSup_le
    · rcases hX with ⟨u, hu⟩
      exact ⟨comparator_alternating_regret T loss x u, ⟨u, hu, rfl⟩⟩
    · intro z hz
      rcases hz with ⟨u, hu, rfl⟩
      exact hB u hu
  exact le_min (hsSup_le _ hcomparator_range) (hsSup_le _ hcomparator_analytic)

@[blueprint "thm:hedge-cont"
  (statement := /-- There exist a universal constant \(C>0\) and a universal horizon
  \(T_0\) such that the following holds.  Let \(d,T\in\mathbb{N}\), with \(d>0\) and
  \(T\geq T_0\), let \(\mathcal X\subseteq\mathbb{R}^{d}\) be nonempty and convex, and let
  \(f_t:\mathbb{R}^{d}\to\mathbb{R}\), \(0\leq t<T\), be convex on \(\mathcal X\) and satisfy
  \[
    |f_t(y)|\leq 1\qquad (y\in\mathcal X).
  \]
  Set \(\eta=\min\{1,T^{-1/3}(d\log T)^{1/3}\}\), and assume that, for every
  \(0\leq t\leq T\), the unnormalized exponential-weights measure \(\mu_t\) from
  \cref{def:continuous-hedge-weight-measure}, formed with learning rate \(\eta\), has
  strictly positive finite total mass:
  \[
    0<\mu_t(\mathbb{R}^{d})<\infty.
  \]
  Then there exist probability measures \(p_t\) and actions \(x_t\), for
  \(0\leq t\leq T\), which form a Continuous Hedge execution in the sense of
  \cref{def:is-continuous-hedge} with the learning rate from
  \cref{def:continuous-hedge-learning-rate}, and which satisfy
  \[
    \operatorname{Reg}_{\mathrm{Alt}}
      \leq C\,d^{2/3}T^{1/3}(\log T)^{2/3},
  \]
  where alternating regret and the rate are those of
  \cref{def:alternating-regret,def:continuous-hedge-rate}. -/)
  (proof := /-- Choose \(C=8\) and
  \[
    T_0=\max\{2,\lceil e\rceil\}.
  \]
  Fix \(d,T,\mathcal X\), and losses satisfying the hypotheses, and put
  \[
    \eta=\min\{1,T^{-1/3}(d\log T)^{1/3}\}.
  \]
  The choice of \(T_0\) gives \(T\geq2\) and \(e\leq T\), hence
  \(\log T\geq1\).  Since also \(d\geq1\), the rate
  \[
    R=d^{2/3}T^{1/3}(\log T)^{2/3}
  \]
  satisfies \(R\geq1\).  Positivity of \(d\log T\) gives
  \(0<\eta\leq1\).  Applying
  \cref{lem:continuous-hedge-normalization} with this learning rate produces probability
  measures \(p_t\) and barycentric actions \(x_t\) forming the required Continuous Hedge
  execution.

  By \cref{lem:continuous-hedge-master-bound},
  \[
    \operatorname{Reg}_{\rm Alt}\leq
    \min\left\{4T,\,
      \frac{2d\log T}{\eta}+\frac43T\eta^2+4\right\}.
  \]
  Write \(q=d\log T>0\), \(a=T^{-1/3}q^{1/3}\), and
  \(R=q^{2/3}T^{1/3}\); the last identity follows from the multiplicative law for
  nonnegative real powers.  If \(q\leq T\), monotonicity of the one-third power gives
  \(a\leq1\), and therefore \(\eta=a\).  The real-power laws give
  \[
    \frac q a=R,\qquad Ta^2=R.
  \]
  Hence the second member of the minimum is
  \[
    2R+\frac43R+4=\frac{10}{3}R+4.
  \]
  Since \(R\geq1\), this is at most \(8R\).  If \(q>T\), monotonicity of the
  two-thirds power and
  \(T^{2/3}T^{1/3}=T\) give \(T\leq R\).  The first member of the minimum then yields
  \(4T\leq8R\).  Thus in both cases
  \[
    \operatorname{Reg}_{\rm Alt}
      \leq8\,d^{2/3}T^{1/3}(\log T)^{2/3}
      =C\,R(d,T),
  \]
  where \(R(d,T)\) is \cref{def:continuous-hedge-rate}.  Thus
  \[
    \operatorname{Reg}_{\rm Alt}\leq C\,R(d,T).
  \]
  This proves the claimed existential choice of the universal constant and horizon. -/)
  (title := /-- Alternating regret of Continuous Hedge -/)
  (latexEnv := "theorem")]
theorem hedge_cont :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ,
      ∀ (d T : ℕ) (X : Set (oco_point d)) (loss : ℕ → oco_point d → ℝ),
        T₀ ≤ T →
        0 < d →
        X.Nonempty →
        Convex ℝ X →
        (∀ t, t < T → ConvexOn ℝ X (loss t)) →
        (∀ t, t < T → ∀ y ∈ X, |loss t y| ≤ 1) →
        (∀ t, t ≤ T →
          (continuous_hedge_weight_measure X loss
              (continuous_hedge_learning_rate d T) t) Set.univ ≠ 0 ∧
          (continuous_hedge_weight_measure X loss
              (continuous_hedge_learning_rate d T) t) Set.univ ≠ ⊤) →
        ∃ (p : ℕ → Measure (oco_point d)) (x : ℕ → oco_point d),
          is_continuous_hedge T X loss (continuous_hedge_learning_rate d T) p x ∧
          alternating_regret T X loss x ≤ C * continuous_hedge_rate d T := by
  refine ⟨8, by norm_num, max 2 ⌈Real.exp 1⌉₊, ?_⟩
  intro d T X loss hT hd hX hconv hloss_conv hloss_bound hmass
  have hTtwo : 2 ≤ T := (le_max_left 2 ⌈Real.exp 1⌉₊).trans hT
  have hTreal : 0 < (T : ℝ) := by positivity
  have hlog_pos : 0 < Real.log (T : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < T by omega))
  let q : ℝ := (d : ℝ) * Real.log (T : ℝ)
  let a : ℝ :=
    Real.rpow (T : ℝ) (-(1 : ℝ) / 3) *
      Real.rpow q ((1 : ℝ) / 3)
  let R : ℝ :=
    Real.rpow q ((2 : ℝ) / 3) *
      Real.rpow (T : ℝ) ((1 : ℝ) / 3)
  have hq_pos : 0 < q := by
    dsimp [q]
    exact mul_pos (by exact_mod_cast hd) hlog_pos
  have hη_pos : 0 < continuous_hedge_learning_rate d T := by
    rw [continuous_hedge_learning_rate]
    exact lt_min zero_lt_one
      (mul_pos (Real.rpow_pos_of_pos hTreal _) (Real.rpow_pos_of_pos hq_pos _))
  have hη_le : continuous_hedge_learning_rate d T ≤ 1 := by
    rw [continuous_hedge_learning_rate]
    exact min_le_left _ _
  rcases continuous_hedge_normalization X loss (continuous_hedge_learning_rate d T)
      hTtwo hd hX hconv hloss_conv hloss_bound hη_pos.le hη_le hmass with
    ⟨p, x, hexec⟩
  refine ⟨p, x, hexec, ?_⟩
  have hmaster := continuous_hedge_master_bound X loss
    (continuous_hedge_learning_rate d T) p x hTtwo hd hX hconv
    hloss_conv hloss_bound hη_pos hη_le hmass hexec
  have hrate : continuous_hedge_rate d T = R := by
    dsimp [continuous_hedge_rate, R, q]
    rw [Real.mul_rpow (by positivity) hlog_pos.le]
    ring
  have hlog_one : 1 ≤ Real.log (T : ℝ) := by
    rw [Real.le_log_iff_exp_le hTreal]
    exact Nat.ceil_le.mp ((le_max_right 2 ⌈Real.exp 1⌉₊).trans hT)
  have hd_pow : 1 ≤ Real.rpow (d : ℝ) ((2 : ℝ) / 3) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ d by omega)) (by norm_num)
  have hT_pow : 1 ≤ Real.rpow (T : ℝ) ((1 : ℝ) / 3) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ T by omega)) (by norm_num)
  have hlog_pow : 1 ≤ Real.rpow (Real.log (T : ℝ)) ((2 : ℝ) / 3) :=
    Real.one_le_rpow hlog_one (by norm_num)
  have hfirst_product :
      1 ≤ Real.rpow (d : ℝ) ((2 : ℝ) / 3) *
        Real.rpow (T : ℝ) ((1 : ℝ) / 3) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd_pow) (sub_nonneg.mpr hT_pow)]
  have hrate_one : 1 ≤ continuous_hedge_rate d T := by
    change 1 ≤
      Real.rpow (d : ℝ) ((2 : ℝ) / 3) *
        Real.rpow (T : ℝ) ((1 : ℝ) / 3) *
          Real.rpow (Real.log (T : ℝ)) ((2 : ℝ) / 3)
    nlinarith [mul_nonneg (sub_nonneg.mpr hfirst_product)
      (sub_nonneg.mpr hlog_pow)]
  have hR_one : 1 ≤ R := by
    rw [← hrate]
    exact hrate_one
  have hT_third_pos : 0 < Real.rpow (T : ℝ) ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hTreal _
  have hq_third_pos : 0 < Real.rpow q ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hq_pos _
  have hT_neg_third :
      Real.rpow (T : ℝ) (-(1 : ℝ) / 3) =
        (Real.rpow (T : ℝ) ((1 : ℝ) / 3))⁻¹ := by
    have h := Real.rpow_neg hTreal.le ((1 : ℝ) / 3)
    change (T : ℝ) ^ (-(1 : ℝ) / 3) =
      ((T : ℝ) ^ ((1 : ℝ) / 3))⁻¹
    norm_num at h ⊢
    exact h
  have hq_square :
      (Real.rpow q ((1 : ℝ) / 3)) ^ 2 =
        Real.rpow q ((2 : ℝ) / 3) := by
    change (q ^ ((1 : ℝ) / 3)) ^ 2 = q ^ ((2 : ℝ) / 3)
    rw [← Real.rpow_mul_natCast hq_pos.le ((1 : ℝ) / 3) 2]
    norm_num
  have hq_cube :
      (Real.rpow q ((1 : ℝ) / 3)) ^ 3 = q := by
    change (q ^ ((1 : ℝ) / 3)) ^ 3 = q
    rw [← Real.rpow_mul_natCast hq_pos.le ((1 : ℝ) / 3) 3]
    norm_num
  have hT_cube :
      (Real.rpow (T : ℝ) ((1 : ℝ) / 3)) ^ 3 = (T : ℝ) := by
    change ((T : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (T : ℝ)
    rw [← Real.rpow_mul_natCast hTreal.le ((1 : ℝ) / 3) 3]
    norm_num
  by_cases hqT : q ≤ (T : ℝ)
  · have hthird_le :
        Real.rpow q ((1 : ℝ) / 3) ≤
          Real.rpow (T : ℝ) ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow hq_pos.le hqT (by norm_num)
    have ha_le : a ≤ 1 := by
      change Real.rpow (T : ℝ) (-(1 : ℝ) / 3) *
        Real.rpow q ((1 : ℝ) / 3) ≤ 1
      rw [hT_neg_third]
      simpa [div_eq_mul_inv, mul_comm] using
        (div_le_one hT_third_pos).2 hthird_le
    have hη_eq : continuous_hedge_learning_rate d T = a := by
      rw [continuous_hedge_learning_rate]
      change min 1 a = a
      exact min_eq_right ha_le
    have hq_div_a : q / a = R := by
      calc
        q / a = (Real.rpow q ((1 : ℝ) / 3)) ^ 3 / a :=
          (congrArg (fun z : ℝ => z / a) hq_cube).symm
        _ = (Real.rpow q ((1 : ℝ) / 3)) ^ 2 *
            Real.rpow (T : ℝ) ((1 : ℝ) / 3) := by
          rw [show a = Real.rpow (T : ℝ) (-(1 : ℝ) / 3) *
            Real.rpow q ((1 : ℝ) / 3) from rfl, hT_neg_third]
          field_simp [hT_third_pos.ne', hq_third_pos.ne']
          <;> ring
        _ = R := by
          change (Real.rpow q ((1 : ℝ) / 3)) ^ 2 *
              Real.rpow (T : ℝ) ((1 : ℝ) / 3) =
            Real.rpow q ((2 : ℝ) / 3) *
              Real.rpow (T : ℝ) ((1 : ℝ) / 3)
          exact congrArg
            (fun z : ℝ => z * Real.rpow (T : ℝ) ((1 : ℝ) / 3)) hq_square
    have hT_mul_a_sq : (T : ℝ) * a ^ 2 = R := by
      calc
        (T : ℝ) * a ^ 2 =
            (Real.rpow (T : ℝ) ((1 : ℝ) / 3)) ^ 3 * a ^ 2 :=
          (congrArg (fun z : ℝ => z * a ^ 2) hT_cube).symm
        _ = (Real.rpow q ((1 : ℝ) / 3)) ^ 2 *
            Real.rpow (T : ℝ) ((1 : ℝ) / 3) := by
          rw [show a = Real.rpow (T : ℝ) (-(1 : ℝ) / 3) *
            Real.rpow q ((1 : ℝ) / 3) from rfl, hT_neg_third]
          field_simp [hT_third_pos.ne']
          <;> ring
        _ = R := by
          change (Real.rpow q ((1 : ℝ) / 3)) ^ 2 *
              Real.rpow (T : ℝ) ((1 : ℝ) / 3) =
            Real.rpow q ((2 : ℝ) / 3) *
              Real.rpow (T : ℝ) ((1 : ℝ) / 3)
          exact congrArg
            (fun z : ℝ => z * Real.rpow (T : ℝ) ((1 : ℝ) / 3)) hq_square
    rw [hη_eq] at hmaster
    calc
      alternating_regret T X loss x ≤
          min (4 * (T : ℝ))
            (2 * (d : ℝ) * Real.log (T : ℝ) / a +
              (4 : ℝ) / 3 * (T : ℝ) * a ^ 2 + 4) := hmaster
      _ ≤ 2 * (d : ℝ) * Real.log (T : ℝ) / a +
            (4 : ℝ) / 3 * (T : ℝ) * a ^ 2 + 4 := min_le_right _ _
      _ = 2 * R + (4 : ℝ) / 3 * R + 4 := by
        rw [show 2 * (d : ℝ) * Real.log (T : ℝ) / a =
          2 * (q / a) by dsimp [q]; ring]
        rw [show (4 : ℝ) / 3 * (T : ℝ) * a ^ 2 =
          (4 : ℝ) / 3 * ((T : ℝ) * a ^ 2) by ring]
        rw [hq_div_a, hT_mul_a_sq]
      _ ≤ 8 * R := by nlinarith
      _ = 8 * continuous_hedge_rate d T := by rw [hrate]
  · have hTq : (T : ℝ) ≤ q := le_of_not_ge hqT
    have htwo_thirds :
        Real.rpow (T : ℝ) ((2 : ℝ) / 3) ≤
          Real.rpow q ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow hTreal.le hTq (by norm_num)
    have hT_factor :
        Real.rpow (T : ℝ) ((2 : ℝ) / 3) *
            Real.rpow (T : ℝ) ((1 : ℝ) / 3) = (T : ℝ) := by
      change (T : ℝ) ^ ((2 : ℝ) / 3) *
        (T : ℝ) ^ ((1 : ℝ) / 3) = (T : ℝ)
      rw [← Real.rpow_add hTreal]
      norm_num
    have hTR : (T : ℝ) ≤ R := by
      calc
        (T : ℝ) = Real.rpow (T : ℝ) ((2 : ℝ) / 3) *
            Real.rpow (T : ℝ) ((1 : ℝ) / 3) := hT_factor.symm
        _ ≤ Real.rpow q ((2 : ℝ) / 3) *
            Real.rpow (T : ℝ) ((1 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_right htwo_thirds hT_third_pos.le
        _ = R := rfl
    calc
      alternating_regret T X loss x ≤
          min (4 * (T : ℝ))
            (2 * (d : ℝ) * Real.log (T : ℝ) /
                continuous_hedge_learning_rate d T +
              (4 : ℝ) / 3 * (T : ℝ) *
                continuous_hedge_learning_rate d T ^ 2 + 4) := hmaster
      _ ≤ 4 * (T : ℝ) := min_le_left _ _
      _ ≤ 8 * R := by nlinarith
      _ = 8 * continuous_hedge_rate d T := by rw [hrate]

import Architect
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.ProbabilityMassFunction.Basic
import SLT.RMT.MatBern

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory ProbabilityTheory

section

@[blueprint "def:real-square-matrix"
  (statement := /-- For \(n\in\mathbb N\), write \(\operatorname{Mat}_n(\mathbb R)\) for the
  space of real \(n\times n\) matrices, with both rows and columns indexed by
  \(\operatorname{Fin}(n)\). -/)
  (title := /-- Real square matrices -/)
  (latexEnv := "definition")]
abbrev real_square_matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

@[blueprint "def:real-square-matrix-loewner-order"
  (statement := /-- Equip real square matrices with the Löwner partial
  order: \(A\preceq B\) precisely when \(B-A\) is positive semidefinite. -/)
  (title := /-- Löwner order on real square matrices -/)
  (latexEnv := "definition")]
noncomputable local instance real_square_matrix_loewner_order (n : ℕ) :
    PartialOrder (real_square_matrix n) :=
  Matrix.instPartialOrder

@[blueprint "def:real-square-matrix-star-ordered-ring"
  (statement := /-- With the Löwner order and transpose star operation, real
  square matrices form a star-ordered ring. -/)
  (title := /-- Star-ordered ring of real square matrices -/)
  (latexEnv := "definition")]
noncomputable local instance real_square_matrix_star_ordered_ring (n : ℕ) :
    StarOrderedRing (real_square_matrix n) :=
  Matrix.instStarOrderedRing

@[blueprint "def:real-square-matrix-nonnegative-spectrum"
  (statement := /-- Positive semidefinite real square matrices have
  nonnegative spectrum, as required by the continuous functional calculus. -/)
  (title := /-- Nonnegative spectrum for real square matrices -/)
  (latexEnv := "definition")]
noncomputable local instance real_square_matrix_nonnegative_spectrum (n : ℕ) :
    NonnegSpectrumClass ℝ (real_square_matrix n) :=
  Matrix.instNonnegSpectrumClass

@[blueprint "def:real-square-matrix-operator-norm"
  (statement := /-- Equip real square matrices with the
  \(\ell^2\)-operator norm induced by their action on Euclidean space. -/)
  (title := /-- Operator norm on real square matrices -/)
  (latexEnv := "definition")]
noncomputable local instance real_square_matrix_operator_norm (n : ℕ) :
    NormedRing (real_square_matrix n) :=
  Matrix.instL2OpNormedRing

@[blueprint "def:real-square-matrix-normed-algebra"
  (statement := /-- Equip real square matrices, carrying the
  \(\ell^2\)-operator norm, with their compatible normed
  \(\mathbb R\)-algebra structure. -/)
  (title := /-- Normed algebra structure on real square matrices -/)
  (latexEnv := "definition")]
noncomputable local instance real_square_matrix_normed_algebra (n : ℕ) :
    NormedAlgebra ℝ (real_square_matrix n) :=
  Matrix.instL2OpNormedAlgebra

@[blueprint "def:matrix-family-sum"
  (statement := /-- Let \(\iota\) be finite and let
  \(A:\iota\to\operatorname{Mat}_n(\mathbb R)\).  Define
  \[
    \Sigma(A):=\sum_{i\in\iota}A_i.
  \] -/)
  (title := /-- Sum of a finite matrix family -/)
  (latexEnv := "definition")]
noncomputable def matrix_family_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → real_square_matrix n) : real_square_matrix n :=
  ∑ i, A i

@[blueprint "def:weighted-matrix-family-sum"
  (statement := /-- Let \(\iota\) be finite, let
  \(A:\iota\to\operatorname{Mat}_n(\mathbb R)\), and let
  \(\mu:\iota\to\mathbb R_{\geq 0}\).  Define the nonnegatively weighted sum by
  \[
    \Sigma_\mu(A):=\sum_{i\in\iota}\mu_iA_i.
  \] -/)
  (title := /-- Nonnegatively weighted matrix sum -/)
  (latexEnv := "definition")]
noncomputable def weighted_matrix_family_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → real_square_matrix n) (μ : ι → NNReal) : real_square_matrix n :=
  ∑ i, (μ i : ℝ) • A i

@[blueprint "def:spectral-sparsifier"
  (statement := /-- Let \(\iota\) be finite, let
  \(A:\iota\to\operatorname{Mat}_n(\mathbb R)\), let
  \(\varepsilon\in\mathbb R\), and let
  \(\mu:\iota\to\mathbb R_{\geq0}\).  We say that \(\mu\) is an
  \(\varepsilon\)-spectral sparsifier of \(A\) if
  \[
    (1-\varepsilon)\Sigma(A)\preceq\Sigma_\mu(A)
    \preceq(1+\varepsilon)\Sigma(A).
  \] -/)
  (title := /-- Spectral sparsifier -/)
  (latexEnv := "definition")]
def spectral_sparsifier {n : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → real_square_matrix n) (ε : ℝ) (μ : ι → NNReal) : Prop :=
  (1 - ε) • matrix_family_sum A ≤ weighted_matrix_family_sum A μ ∧
    weighted_matrix_family_sum A μ ≤ (1 + ε) • matrix_family_sum A

@[blueprint "def:weight-support-cardinality"
  (statement := /-- For a finite index type \(\iota\) and weights
  \(\mu:\iota\to\mathbb R_{\geq0}\), define
  \[
    |\operatorname{supp}(\mu)|
      :=|\{i\in\iota:\mu_i\neq0\}|.
  \] -/)
  (title := /-- Cardinality of the support of a weight map -/)
  (latexEnv := "definition")]
noncomputable def weight_support_cardinality {ι : Type*} [Fintype ι]
    (μ : ι → NNReal) : ℕ :=
  (Finset.univ.filter fun i => μ i ≠ 0).card

@[blueprint "def:connectivity-property"
  (statement := /-- Let \(\iota\) be finite, let
  \(A:\iota\to\operatorname{Mat}_n(\mathbb R)\), let \(\alpha\in\mathbb R\),
  and let \(k\in\mathbb N\).  The family has the connectivity property at
  strength \(\alpha\) and threshold \(k\) if every \(S\subseteq\iota\) with
  \(|S|\geq k\) contains an \(i\in S\) such that
  \[
    \alpha A_i\preceq\sum_{j\in S\setminus\{i\}}A_j.
  \] -/)
  (title := /-- Connectivity property at a fixed threshold -/)
  (latexEnv := "definition")]
def connectivity_property {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → real_square_matrix n) (α : ℝ) (k : ℕ) : Prop :=
  ∀ S : Finset ι, k ≤ S.card →
    ∃ i ∈ S, α • A i ≤ ∑ j ∈ S.erase i, A j

@[blueprint "def:connectivity-parameter"
  (statement := /-- Let \(\iota\) be finite and let
  \(A:\iota\to\operatorname{Mat}_n(\mathbb R)\).  For \(\alpha\in\mathbb R\),
  define \(N(\alpha;A)\) to be the infimum in \(\mathbb N\) of all thresholds
  for which the connectivity property holds.  Since the property is vacuous
  above \(|\iota|\), this agrees with the convention \(N(\alpha;A)=|\iota|+1\)
  when no threshold at most \(|\iota|\) works. -/)
  (title := /-- Connectivity parameter -/)
  (latexEnv := "definition")]
noncomputable def connectivity_parameter {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : ι → real_square_matrix n) (α : ℝ) : ℕ :=
  sInf {k : ℕ | connectivity_property A α k}

@[blueprint "def:connectivity-ratio"
  (statement := /-- For a finite matrix family \(A\), define its optimized
  connectivity ratio by
  \[
    \mathcal N(A):=
    \inf_{0<\alpha\leq1}\frac{N(\alpha;A)}{\alpha}.
  \]
  This is the formal representative of the minimum appearing in the paper. -/)
  (title := /-- Optimized connectivity ratio -/)
  (latexEnv := "definition")]
noncomputable def connectivity_ratio {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : ι → real_square_matrix n) : ℝ :=
  sInf {x : ℝ | ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
    x = (connectivity_parameter A α : ℝ) / α}

@[blueprint "def:alpha-epsilon"
  (statement := /-- For \(\varepsilon\in[0,1)\), define
  \[
    \alpha_\varepsilon
      :=\frac{-1+\sqrt{1+4(1-\varepsilon)/(1+\varepsilon)}}{2}.
  \]
  It is the root in \([0,1]\) of
  \(\alpha(1+\alpha)=(1-\varepsilon)/(1+\varepsilon)\). -/)
  (title := /-- The distinguished connectivity strength -/)
  (latexEnv := "definition")]
noncomputable def alpha_epsilon (ε : ℝ) : ℝ :=
  (-1 + Real.sqrt (1 + 4 * ((1 - ε) / (1 + ε)))) / 2

@[blueprint "def:connectivity-threshold"
  (statement := /-- For a finite matrix family \(A\) and
  \(\varepsilon\in[0,1)\), define
  \[
    N_\varepsilon^*(A):=N(\alpha_\varepsilon;A).
  \] -/)
  (title := /-- Connectivity threshold at the distinguished strength -/)
  (latexEnv := "definition")]
noncomputable def connectivity_threshold {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : ι → real_square_matrix n) (ε : ℝ) : ℕ :=
  connectivity_parameter A (alpha_epsilon ε)

@[blueprint "def:subcollection-family"
  (statement := /-- Let \(A:\operatorname{Fin}(r)\to
  \operatorname{Mat}_n(\mathbb R)\) and let
  \(T\subseteq\operatorname{Fin}(r)\).  The family induced on \(T\) is the
  map \(i\mapsto A_i\) whose index type is the subtype \(T\). -/)
  (title := /-- Matrix family induced by a subcollection -/)
  (latexEnv := "definition")]
def subcollection_family {n r : ℕ} (A : Fin r → real_square_matrix n)
    (T : Finset (Fin r)) : ↥T → real_square_matrix n :=
  fun i => A i.1

@[blueprint "def:first-support-scale"
  (statement := /-- For \(A:\operatorname{Fin}(r)\to
  \operatorname{Mat}_n(\mathbb R)\), a subcollection \(T\), and an error
  \(\varepsilon\), define
  \[
    B_T(A,\varepsilon):=\varepsilon^{-2}(1+\log|T|)\,
      \bigl(1+\log\!\bigl(\operatorname{rank}\Sigma(A|_T)\bigr)\bigr)\,
      \mathcal N(A|_T).
  \]
  The additive constants retain the usual asymptotic order and keep the
  finite-size scale positive when the cardinality or effective rank is
  one. -/)
  (title := /-- Subcollection support scale -/)
  (latexEnv := "definition")]
noncomputable def first_support_scale {n r : ℕ}
    (A : Fin r → real_square_matrix n) (T : Finset (Fin r)) (ε : ℝ) : ℝ :=
  ε⁻¹ ^ 2 * (1 + Real.log (T.card : ℝ)) *
    (1 + Real.log ((matrix_family_sum (subcollection_family A T)).rank : ℝ)) *
    connectivity_ratio (subcollection_family A T)

@[blueprint "def:ambient-support-scale"
  (statement := /-- For an ambient family
  \(A:\operatorname{Fin}(r)\to\operatorname{Mat}_n(\mathbb R)\) and an error
  \(\varepsilon\), define
  \[
    B_{\mathrm{amb}}(A,\varepsilon):=\varepsilon^{-2}
      (1+\log r)(1+\log n)\,
      \mathcal N(A).
  \]
  This regularization has the same asymptotic order as the displayed
  logarithmic bound and does not vanish for singleton dimensions. -/)
  (title := /-- Ambient-family support scale -/)
  (latexEnv := "definition")]
noncomputable def ambient_support_scale {n r : ℕ}
    (A : Fin r → real_square_matrix n) (ε : ℝ) : ℝ :=
  ε⁻¹ ^ 2 * (1 + Real.log (r : ℝ)) * (1 + Real.log (n : ℝ)) *
    connectivity_ratio A

@[blueprint "def:threshold-support-scale"
  (statement := /-- For an ambient family
  \(A:\operatorname{Fin}(r)\to\operatorname{Mat}_n(\mathbb R)\) and an error
  \(\varepsilon\), define
  \[
    B_*(A,\varepsilon):=\varepsilon^{-2}
      (1+\log r)(1+\log n)\,
      N_\varepsilon^*(A).
  \]
  Again the logarithms are regularized so that the scale remains meaningful
  for singleton ambient parameters. -/)
  (title := /-- Distinguished-threshold support scale -/)
  (latexEnv := "definition")]
noncomputable def threshold_support_scale {n r : ℕ}
    (A : Fin r → real_square_matrix n) (ε : ℝ) : ℝ :=
  ε⁻¹ ^ 2 * (1 + Real.log (r : ℝ)) * (1 + Real.log (n : ℝ)) *
    (connectivity_threshold A ε : ℝ)

@[blueprint "def:good-sparsifier"
  (statement := /-- Fix an absolute constant \(C>0\).  For an ambient PSD
  family \(A\), a nonzero subcollection \(T\), and
  \(\varepsilon\in[0,1)\), a weight map
  \(\mu:T\to\mathbb R_{\geq0}\) is called good if it is an
  \(\varepsilon\)-spectral sparsifier and, when \(\varepsilon>0\),
  \[
    |\operatorname{supp}\mu|\leq C B_T(A,\varepsilon),\qquad
    |\operatorname{supp}\mu|\leq C B_{\mathrm{amb}}(A,\varepsilon),
  \]
  and, whenever \(\varepsilon\leq0.99\),
  \[
    |\operatorname{supp}\mu|\leq C B_*(A,\varepsilon).
  \] -/)
  (title := /-- Bundled sparsifier conclusions -/)
  (latexEnv := "definition")]
def good_sparsifier {n r : ℕ} (C : ℝ)
    (A : Fin r → real_square_matrix n) (T : Finset (Fin r)) (ε : ℝ)
    (μ : ↥T → NNReal) : Prop :=
  spectral_sparsifier (subcollection_family A T) ε μ ∧
    (0 < ε →
      (weight_support_cardinality μ : ℝ) ≤ C * first_support_scale A T ε ∧
      (weight_support_cardinality μ : ℝ) ≤ C * ambient_support_scale A ε ∧
      (ε ≤ (99 : ℝ) / 100 →
        (weight_support_cardinality μ : ℝ) ≤ C * threshold_support_scale A ε))

@[blueprint "def:randomized-sparsifier-algorithm"
  (statement := /-- A randomized sparsifier algorithm assigns to every pair
  of dimensions \(n,r\), every real \(n\times n\) matrix family, every error
  parameter, and every subcollection \(T\), a probability mass function on
  nonnegative weight maps \(T\to\mathbb R_{\geq0}\).  It is also equipped
  with a worst-case operation count depending on \(n\) and \(r\). -/)
  (title := /-- Randomized matrix-sparsifier algorithm -/)
  (latexEnv := "definition")]
structure randomized_sparsifier_algorithm where
  output : {n r : ℕ} → (Fin r → real_square_matrix n) → (ε : ℝ) →
    (T : Finset (Fin r)) → PMF (↥T → NNReal)
  runningTime : ℕ → ℕ → ℕ

@[blueprint "def:runs-in-polynomial-time"
  (statement := /-- A randomized sparsifier algorithm runs in polynomial
  time if there are natural numbers \(c>0\) and \(k\) such that its
  worst-case operation count on dimensions \(n,r\) is at most
  \(c(n+r)^k\) for every \(n,r\). -/)
  (title := /-- Polynomial running time -/)
  (latexEnv := "definition")]
def runs_in_polynomial_time (alg : randomized_sparsifier_algorithm) : Prop :=
  ∃ c k : ℕ, 0 < c ∧ ∀ n r : ℕ,
    alg.runningTime n r ≤ c * (n + r) ^ k

@[blueprint "def:algorithm-produces-good-sparsifiers"
  (statement := /-- Fix \(C>0\).  A randomized algorithm produces good
  sparsifiers if, for every PSD input family, every
  \(\varepsilon\in[0,1)\), and every nonzero subcollection \(T\), every
  weight map in the support of its output distribution satisfies the
  spectral approximation conclusion; when \(\varepsilon>0\), it also
  satisfies all three support conclusions with constant \(C\). -/)
  (title := /-- Correctness of the randomized sparsifier algorithm -/)
  (latexEnv := "definition")]
def algorithm_produces_good_sparsifiers
    (alg : randomized_sparsifier_algorithm) (C : ℝ) : Prop :=
  ∀ {n r : ℕ} (A : Fin r → real_square_matrix n) (ε : ℝ)
    (T : Finset (Fin r)),
    (∀ i, (A i).PosSemidef) →
    0 ≤ ε → ε < 1 →
    (∃ i : ↥T, A i.1 ≠ 0) →
    ∀ μ ∈ (alg.output A ε T).support, good_sparsifier C A T ε μ

@[blueprint "lem:connectivity-parameter-spec"
  (statement := /-- Let \(n\in\mathbb N\), let \(\iota\) be finite, let
  \(A:\iota\to\operatorname{Mat}_n(\mathbb R)\), and let
  \(\alpha\in\mathbb R\).  Then \(A\) has the connectivity property at
  strength \(\alpha\) and threshold \(N(\alpha;A)\). -/)
  (proof := /-- By \cref{def:connectivity-property}, the threshold
  \(|\iota|+1\) is admissible: every finite subset of \(\iota\) has
  cardinality at most \(|\iota|\), so none satisfies the premise at this
  threshold.  Consequently, the set of admissible thresholds in
  \cref{def:connectivity-parameter} is nonempty.  The well-ordering
  principle for \(\mathbb N\) implies that its infimum belongs to this set,
  and hence has the required connectivity property. -/)
  (title := /-- The connectivity parameter is admissible -/)
  (latexEnv := "lemma")]
lemma connectivity_parameter_spec {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : ι → real_square_matrix n) (α : ℝ) :
    connectivity_property A α (connectivity_parameter A α) := by
  change sInf {k : ℕ | connectivity_property A α k} ∈
    {k : ℕ | connectivity_property A α k}
  apply Nat.sInf_mem
  refine ⟨Fintype.card ι + 1, ?_⟩
  intro S hS
  have hcard := Finset.card_le_univ S
  omega

@[blueprint "lem:connectivity-parameter-minimal"
  (statement := /-- Under the hypotheses of
  \cref{lem:connectivity-parameter-spec}, if \(k\) has the connectivity
  property at strength \(\alpha\), then \(N(\alpha;A)\leq k\). -/)
  (proof := /-- By \cref{lem:connectivity-parameter-spec}, the set of
  admissible thresholds is nonempty.  The least-element characterization in
  \cref{def:connectivity-parameter} therefore bounds its infimum by every
  admissible threshold, in particular by \(k\). -/)
  (title := /-- Minimality of the connectivity parameter -/)
  (latexEnv := "lemma")]
lemma connectivity_parameter_minimal {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : ι → real_square_matrix n) (α : ℝ) (k : ℕ)
    (hk : connectivity_property A α k) :
    connectivity_parameter A α ≤ k := by
  exact Nat.sInf_le hk

@[blueprint "lem:connectivity-ratio-restriction"
  (statement := /-- Let \(A:\operatorname{Fin}(r)\to
  \operatorname{Mat}_n(\mathbb R)\) and let
  \(T\subseteq\operatorname{Fin}(r)\).  Then
  \[
    \mathcal N(A|_T)\leq\mathcal N(A).
  \] -/)
  (proof := /-- Fix \(0<\alpha\leq1\).  Apply
  \cref{lem:connectivity-parameter-spec} to the ambient family at threshold
  \(N(\alpha;A)\).  Every finite subset of the subtype \(T\) maps
  injectively to a subset of the ambient index set with the same
  cardinality, so the ambient connectivity witness belongs to that image
  and supplies the required witness for \(A|_T\).  Thus
  \(N(\alpha;A|_T)\leq N(\alpha;A)\) by
  \cref{lem:connectivity-parameter-minimal}.  Division by the positive
  number \(\alpha\), followed by taking infima over \(0<\alpha\leq1\), gives
  the asserted inequality. -/)
  (title := /-- Connectivity does not worsen under restriction -/)
  (latexEnv := "lemma")]
lemma connectivity_ratio_restriction {n r : ℕ}
    (A : Fin r → real_square_matrix n) (T : Finset (Fin r)) :
    connectivity_ratio (subcollection_family A T) ≤ connectivity_ratio A := by
  classical
  have hmono : ∀ α : ℝ,
      connectivity_parameter (subcollection_family A T) α ≤
        connectivity_parameter A α := by
    intro α
    apply connectivity_parameter_minimal
    intro S hS
    have hcard : connectivity_parameter A α ≤ (S.image Subtype.val).card := by
      rwa [Finset.card_image_of_injective _ Subtype.val_injective]
    obtain ⟨i, hiS, hi⟩ := connectivity_parameter_spec A α _ hcard
    obtain ⟨i', hi'S, rfl⟩ := Finset.mem_image.mp hiS
    refine ⟨i', hi'S, ?_⟩
    have himg : (S.image Subtype.val).erase (i' : Fin r)
        = (S.erase i').image Subtype.val :=
      (Finset.image_erase Subtype.val_injective S i').symm
    rw [himg, Finset.sum_image (fun a _ b _ h => Subtype.val_injective h)] at hi
    exact hi
  have hbdd : BddBelow {x : ℝ | ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      x = (connectivity_parameter (subcollection_family A T) α : ℝ) / α} := by
    refine ⟨0, ?_⟩
    intro x hx
    obtain ⟨β, hβ0, -, rfl⟩ := hx
    exact div_nonneg (Nat.cast_nonneg _) hβ0.le
  unfold connectivity_ratio
  apply le_csInf
  · exact ⟨(connectivity_parameter A 1 : ℝ) / 1, 1, one_pos, le_refl 1, rfl⟩
  · intro b hb
    obtain ⟨α, hα0, hα1, rfl⟩ := hb
    refine le_trans (csInf_le hbdd ⟨α, hα0, hα1, rfl⟩) ?_
    gcongr
    exact Nat.cast_le.mpr (hmono α)

@[blueprint "lem:alpha-epsilon-characterization"
  (statement := /-- For every real number \(\varepsilon\) satisfying
  \(0\leq\varepsilon<1\), one has \(0<\alpha_\varepsilon\leq1\) and
  \[
    \alpha_\varepsilon(1+\alpha_\varepsilon)
      =\frac{1-\varepsilon}{1+\varepsilon}.
  \]
  Moreover, if a real number \(\alpha\) satisfies \(0\leq\alpha\leq1\) and
  the same equation, then \(\alpha=\alpha_\varepsilon\). -/)
  (proof := /-- Put \(q=(1-\varepsilon)/(1+\varepsilon)\).  The hypotheses
  imply \(0<q\leq1\).  If \(s=\sqrt{1+4q}\), then \(s\geq0\),
  \(s^2=1+4q\), and hence \(1<s\leq3\).  By
  \cref{def:alpha-epsilon}, \(\alpha_\varepsilon=(-1+s)/2\); these bounds
  give \(0<\alpha_\varepsilon\leq1\), and expansion using the identity for
  \(s^2\) gives \(\alpha_\varepsilon(1+\alpha_\varepsilon)=q\).
  Finally, if \(\alpha\in[0,1]\) satisfies \(\alpha(1+\alpha)=q\),
  subtraction of the two quadratic identities yields
  \((\alpha-\alpha_\varepsilon)(1+\alpha+\alpha_\varepsilon)=0\).
  The second factor is positive, so \(\alpha=\alpha_\varepsilon\). -/)
  (title := /-- Characterization of the distinguished strength -/)
  (latexEnv := "lemma")]
lemma alpha_epsilon_characterization (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    0 < alpha_epsilon ε ∧ alpha_epsilon ε ≤ 1 ∧
      alpha_epsilon ε * (1 + alpha_epsilon ε) =
        (1 - ε) / (1 + ε) ∧
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
        α * (1 + α) = (1 - ε) / (1 + ε) → α = alpha_epsilon ε := by
  have hden : 0 < 1 + ε := by
    linarith
  have hnum : 0 < 1 - ε := by
    linarith
  let q : ℝ := (1 - ε) / (1 + ε)
  have hqpos : 0 < q := by
    exact div_pos hnum hden
  have hqle : q ≤ 1 := by
    exact (div_le_one hden).2 (by linarith)
  let s : ℝ := Real.sqrt (1 + 4 * q)
  have hrad : 0 ≤ 1 + 4 * q := by
    linarith
  have hs0 : 0 ≤ s := by
    exact Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 + 4 * q := by
    exact Real.sq_sqrt hrad
  have hs1 : 1 < s := by
    nlinarith
  have hs3 : s ≤ 3 := by
    nlinarith
  have ha_def : alpha_epsilon ε = (-1 + s) / 2 := by
    rfl
  have ha0 : 0 < alpha_epsilon ε := by
    rw [ha_def]
    linarith
  have ha1 : alpha_epsilon ε ≤ 1 := by
    rw [ha_def]
    linarith
  have haeq : alpha_epsilon ε * (1 + alpha_epsilon ε) = q := by
    rw [ha_def]
    nlinarith
  refine ⟨ha0, ha1, ?_, ?_⟩
  · exact haeq
  · intro α hα0 hα1 hαeq
    have hfac : (α - alpha_epsilon ε) *
        (1 + α + alpha_epsilon ε) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · nlinarith

@[blueprint "lem:alpha-epsilon-uniform-inverse-bound"
  (statement := /-- There is an absolute constant \(K>0\) such that, for
  every \(0\leq\varepsilon\leq0.99\),
  \[
    \alpha_\varepsilon^{-1}\leq K.
  \] -/)
  (proof := /-- By \cref{lem:alpha-epsilon-characterization},
  \(\alpha_\varepsilon\) is positive and is given by the explicit square-root
  expression in \cref{def:alpha-epsilon}.  On the compact interval
  \([0,0.99]\), this expression has a positive lower bound; taking its
  reciprocal gives a finite absolute constant \(K\).  This is the
  \(\alpha_\varepsilon=\Omega(1)\) assertion made in the source. -/)
  (title := /-- Uniform positivity of the distinguished strength -/)
  (latexEnv := "lemma")]
lemma alpha_epsilon_uniform_inverse_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ (99 : ℝ) / 100 →
      (alpha_epsilon ε)⁻¹ ≤ K := by
  refine ⟨400, by norm_num, ?_⟩
  intro ε hε0 hε
  have hden : (0 : ℝ) < 1 + ε := by linarith
  have hq : (1 : ℝ) / 199 ≤ (1 - ε) / (1 + ε) := by
    rw [le_div_iff₀ hden]
    linarith
  have hq2 : (1 - ε) / (1 + ε) ≤ 1 := by
    rw [div_le_one hden]
    linarith
  have hsq : (1 + (1 - ε) / (1 + ε)) ^ 2 ≤ 1 + 4 * ((1 - ε) / (1 + ε)) := by
    nlinarith
  have hs : 1 + (1 - ε) / (1 + ε) ≤
      Real.sqrt (1 + 4 * ((1 - ε) / (1 + ε))) := by
    have h1 : Real.sqrt ((1 + (1 - ε) / (1 + ε)) ^ 2) ≤
        Real.sqrt (1 + 4 * ((1 - ε) / (1 + ε))) :=
      Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by linarith)] at h1
  have hα : (1 : ℝ) / 398 ≤ alpha_epsilon ε := by
    have hdef : alpha_epsilon ε =
        (-1 + Real.sqrt (1 + 4 * ((1 - ε) / (1 + ε)))) / 2 := rfl
    rw [hdef]
    linarith
  have hpos : 0 < alpha_epsilon ε := lt_of_lt_of_le (by norm_num) hα
  have hmul : (alpha_epsilon ε)⁻¹ * alpha_epsilon ε = 1 :=
    inv_mul_cancel₀ (ne_of_gt hpos)
  have hinvpos : 0 < (alpha_epsilon ε)⁻¹ := inv_pos.mpr hpos
  nlinarith

@[blueprint "lem:psd-summand-vanishes-on-sum-kernel"
  (statement := /-- Let \(\iota\) be finite and let
  \(A_i\in\operatorname{Mat}_n(\mathbb R)\) be PSD for every \(i\).
  If \(v\in\mathbb R^n\) lies in the kernel of \(\sum_iA_i\), then
  \(A_iv=0\) for every \(i\). -/)
  (proof := /-- For every \(i\), positive semidefiniteness gives
  \(v^{\mathsf T}A_iv\geq0\).  By \cref{def:matrix-family-sum}, the
  hypothesis implies
  \[
    0=v^{\mathsf T}\Bigl(\sum_iA_i\Bigr)v
      =\sum_i v^{\mathsf T}A_iv.
  \]
  A finite sum of nonnegative real numbers can vanish only when every
  summand vanishes.  For a PSD matrix, the identity
  \(v^{\mathsf T}A_iv=0\) is equivalent to \(A_iv=0\), which proves the
  claim. -/)
  (title := /-- A kernel vector of a PSD sum kills every summand -/)
  (latexEnv := "lemma")]
lemma psd_summand_vanishes_on_sum_kernel {n : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → real_square_matrix n) (hA : ∀ i, (A i).PosSemidef)
    (v : Fin n → ℝ) (hv : Matrix.mulVec (matrix_family_sum A) v = 0) :
    ∀ i, Matrix.mulVec (A i) v = 0 := by
  classical
  intro i
  apply ((hA i).dotProduct_mulVec_zero_iff v).mp
  have hquad := congrArg (dotProduct (star v)) hv
  have hsum : ∑ j, dotProduct (star v) (Matrix.mulVec (A j) v) = 0 := by
    simpa only [matrix_family_sum, Matrix.sum_mulVec, dotProduct_sum,
      dotProduct_zero] using hquad
  have hall :=
    (Fintype.sum_eq_zero_iff_of_nonneg
      (fun j => (hA j).dotProduct_mulVec_nonneg v)).mp hsum
  exact congrFun hall i

@[blueprint "lem:kernel-orthogonal-finrank-equals-matrix-rank"
  (statement := /-- For every \(n\in\mathbb N\), every finite type
  \(\iota\), and every family
  \(A:\iota\to\operatorname{Mat}_n(\mathbb R)\), the real dimension of the
  orthogonal complement of the kernel of the Euclidean linear operator
  represented by \(\Sigma(A)\) equals \(\operatorname{rank}\Sigma(A)\). -/)
  (proof := /-- The orthogonal complement of the kernel of a
  finite-dimensional linear operator is the range of its adjoint.  The
  adjoint has the same finite rank as the original operator.  Finally, the
  rank of a matrix is the finite rank of the range of its associated linear
  map.  Applying these three identifications to \(\Sigma(A)\) gives the
  equality. -/)
  (title := /-- Effective dimension equals matrix rank -/)
  (latexEnv := "lemma")]
lemma kernel_orthogonal_finrank_equals_matrix_rank {n : ℕ} {ι : Type*}
    [Fintype ι] (A : ι → real_square_matrix n) :
    Module.finrank ℝ
        ((Matrix.toEuclideanLin (𝕜 := ℝ) (matrix_family_sum A)).kerᗮ) =
      (matrix_family_sum A).rank := by
  rw [LinearMap.orthogonal_ker, LinearMap.finrank_range_adjoint]
  exact (Matrix.rank_eq_finrank_range_toLin (matrix_family_sum A)
    (PiLp.basisFun 2 ℝ (Fin n)) (PiLp.basisFun 2 ℝ (Fin n))).symm

@[blueprint "def:normalized-matrix"
  (statement := /-- For square matrices \(S,A\), define the normalization
  \[
    \widetilde A:=S^{-1/2}AS^{-1/2},
  \]
  where the inverse square root is formed by continuous functional
  calculus. -/)
  (title := /-- Normalized matrix -/)
  (latexEnv := "definition")]
noncomputable def normalized_matrix {n : ℕ}
    (S A : real_square_matrix n) : real_square_matrix n :=
  (CFC.sqrt S)⁻¹ * A * (CFC.sqrt S)⁻¹

@[blueprint "lem:normalized-matrix-norm-sum-bound"
  (statement := /-- There is an absolute constant \(C>0\) such that, for
  every finite family of PSD matrices with invertible sum \(S=\sum_iA_i\),
  \[
    \sum_i\|S^{-1/2}A_iS^{-1/2}\|
      \leq C(1+\log|\iota|)\mathcal N(A).
  \] -/)
  (proof := /-- Fix \(0<\alpha\leq1\), put
  \(N=N(\alpha;A)\), and write
  \(B_i=S^{-1/2}A_iS^{-1/2}\) and \(x_i=\lVert B_i\rVert\).
  Congruence by \(S^{-1/2}\) preserves the Löwner order, while
  \(\sum_iB_i=I\); in particular, \(0\preceq B_i\preceq I\) and
  \(0\leq x_i\leq1\).  The degenerate zero-dimensional case is immediate,
  so for each \(i\) we may choose a unit eigenvector \(v_i\) of \(B_i\)
  with \(\langle v_i,B_iv_i\rangle=x_i\).

  Let \(0<p\leq1\), and form a random subset \(Q\) by retaining each index
  independently with probability \(p\).  Call \(i\in Q\) bad when
  \[
    \alpha B_i\not\preceq\sum_{j\in Q\setminus\{i\}}B_j.
  \]
  There are fewer than \(N\) bad indices in every realization.  Indeed, if
  their set \(U\) had cardinality at least \(N\), then
  \cref{lem:connectivity-parameter-spec}, followed by congruence with
  \(S^{-1/2}\), would give some \(i\in U\) for which
  \[
    \alpha B_i\preceq\sum_{j\in U\setminus\{i\}}B_j
      \preceq\sum_{j\in Q\setminus\{i\}}B_j,
  \]
  contrary to the definition of \(U\).

  If \(i\) is retained and is not bad, evaluation on \(v_i\) gives
  \[
    \alpha x_i\leq
      \sum_{j\in Q\setminus\{i\}}\langle v_i,B_jv_i\rangle.
  \]
  Multiplying by the indicator of this event, taking expectations, and
  then discarding that indicator on the right yields
  \[
    \alpha x_i\,\mathbb P(i\text{ is retained and not bad})
      \leq p^2\sum_{j\ne i}\langle v_i,B_jv_i\rangle
      \leq p^2.
  \]
  Consequently
  \[
    \mathbb P(i\text{ is bad})\geq
      p-\frac{p^2}{\alpha x_i}.
  \]
  For \(0<t\leq1\), choose \(p=\alpha t/2\).  Every index satisfying
  \(x_i\geq t\) is then bad with probability at least \(p/2\).  Since the
  number of bad indices is always less than \(N\), linearity of expectation
  gives
  \[
    \#\{i:x_i\geq t\}\leq\frac{4N}{\alpha t}.
  \]
  With \(r=|\iota|\) and \(q=4N/\alpha\), the layer-cake identity and the
  trivial bound \(\#\{i:x_i\geq t\}\leq r\) now imply
  \[
    \sum_i x_i
      =\int_0^1\#\{i:x_i\geq t\}\,dt
      \leq\int_0^1\min\{r,q/t\}\,dt
      \leq q(1+\log r).
  \]
  Thus the claimed estimate holds with constant \(4\) for every admissible
  \(\alpha\).  Taking the infimum prescribed by
  \cref{def:connectivity-ratio} completes the proof. -/)
  (title := /-- Connectivity bound for normalized spectral norms -/)
  (latexEnv := "lemma")]
lemma normalized_matrix_norm_sum_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
        (A : ι → real_square_matrix n),
        (∀ i, (A i).PosSemidef) →
        IsUnit (matrix_family_sum A) →
        (∑ i, ‖normalized_matrix (matrix_family_sum A) (A i)‖) ≤
          C * (1 + Real.log (Fintype.card ι : ℝ)) * connectivity_ratio A := by
  classical
  refine ⟨100, by norm_num, ?_⟩
  intro n ι _ _ A hpsd hunit
  have hlogr : 0 ≤ Real.log (Fintype.card ι : ℝ) := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hratio0 : 0 ≤ connectivity_ratio A := by
    unfold connectivity_ratio
    refine Real.sInf_nonneg ?_
    intro x hx
    obtain ⟨β, hβ0, -, rfl⟩ := hx
    exact div_nonneg (Nat.cast_nonneg _) hβ0.le
  have hden : (0:ℝ) < 100 * (1 + Real.log (Fintype.card ι : ℝ)) := by linarith
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    have h0 : ∀ i, ‖normalized_matrix (matrix_family_sum A) (A i)‖ = 0 := by
      intro i
      have hz : normalized_matrix (matrix_family_sum A) (A i) = 0 := by
        ext p q
        exact absurd p.isLt (Nat.not_lt_zero _)
      rw [hz, norm_zero]
    rw [Finset.sum_congr rfl (fun i _ => h0 i)]
    simp only [Finset.sum_const_zero]
    exact mul_nonneg hden.le hratio0
  have hnormattain : ∀ M : real_square_matrix n, M.PosSemidef →
      ∃ v : Fin n → ℝ, dotProduct v v = 1 ∧
        ‖M‖ ≤ dotProduct v (Matrix.mulVec M v) := by
    intro M hM
    classical
    have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hH : M.IsHermitian := hM.1
    set V : Matrix (Fin n) (Fin n) ℝ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
      with hV
    have hVV : V.transpose * V = 1 := by
      have := hH.eigenvectorUnitary.2
      rw [Matrix.mem_unitaryGroup_iff'] at this
      simpa [hV, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] using this
    have hspec : M = V * Matrix.diagonal hH.eigenvalues * V.transpose := by
      have h := hH.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at h
      simpa [hV, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp] using h
    have hone : ‖(1 : real_square_matrix n)‖ = 1 := by
      have h1 : (1 : real_square_matrix n) = Matrix.diagonal (fun _ => (1 : ℝ)) := by
        rw [← Matrix.diagonal_one]
      rw [h1, Matrix.l2_opNorm_diagonal]
      simp
    have hnV : ‖V‖ = 1 := by
      have h1 : ‖V.transpose * V‖ = ‖V‖ * ‖V‖ := by
        have h2 := Matrix.l2_opNorm_conjTranspose_mul_self V
        rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h2
      rw [hVV, hone] at h1
      nlinarith [norm_nonneg V]
    have hnVt : ‖V.transpose‖ = 1 := by
      have h2 := Matrix.l2_opNorm_conjTranspose V
      rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h2
      rw [h2, hnV]
    have hle : ‖M‖ ≤ ‖hH.eigenvalues‖ := by
      have hstep : ‖M‖ ≤ ‖Matrix.diagonal hH.eigenvalues‖ := by
        calc ‖M‖ = ‖V * Matrix.diagonal hH.eigenvalues * V.transpose‖ := by rw [← hspec]
          _ ≤ ‖V * Matrix.diagonal hH.eigenvalues‖ * ‖V.transpose‖ :=
              Matrix.l2_opNorm_mul _ _
          _ ≤ ‖V‖ * ‖Matrix.diagonal hH.eigenvalues‖ * ‖V.transpose‖ :=
              mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
          _ = ‖Matrix.diagonal hH.eigenvalues‖ := by rw [hnV, hnVt]; ring
      rwa [Matrix.l2_opNorm_diagonal] at hstep
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ hH.eigenvalues
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have hnn : ∀ q, 0 ≤ hH.eigenvalues q := fun q => hM.eigenvalues_nonneg q
    have hnorm_le : ‖hH.eigenvalues‖ ≤ hH.eigenvalues p := by
      refine (pi_norm_le_iff_of_nonneg (hnn p)).mpr ?_
      intro q
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn q)]
      exact hp q (Finset.mem_univ q)
    refine ⟨⇑(hH.eigenvectorBasis p), ?_, ?_⟩
    · have h1 : ‖hH.eigenvectorBasis p‖ = 1 := hH.eigenvectorBasis.orthonormal.1 p
      have h2 : ‖hH.eigenvectorBasis p‖ ^ 2
          = ∑ i, (hH.eigenvectorBasis p i) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq _
      rw [h1] at h2
      simp only [one_pow] at h2
      rw [dotProduct]
      simp only [← sq]
      exact h2.symm
    · have h3 := hH.mulVec_eigenvectorBasis p
      rw [h3, dotProduct_smul]
      have h1 : ‖hH.eigenvectorBasis p‖ = 1 := hH.eigenvectorBasis.orthonormal.1 p
      have h2 : ‖hH.eigenvectorBasis p‖ ^ 2
          = ∑ i, (hH.eigenvectorBasis p i) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq _
      rw [h1] at h2
      simp only [one_pow] at h2
      have h4 : dotProduct (⇑(hH.eigenvectorBasis p)) (⇑(hH.eigenvectorBasis p)) = 1 := by
        rw [dotProduct]
        simp only [← sq]
        exact h2.symm
      rw [h4, smul_eq_mul, mul_one]
      exact le_trans hle hnorm_le
  have hsetup : ∃ T : real_square_matrix n,
      (∀ i, normalized_matrix (matrix_family_sum A) (A i) = T * A i * T) ∧
      (∀ X Y : real_square_matrix n, X ≤ Y → T * X * T ≤ T * Y * T) ∧
      (∑ i, normalized_matrix (matrix_family_sum A) (A i)) = 1 := by
    classical
    have hSpsd : (matrix_family_sum A).PosSemidef := by
      unfold matrix_family_sum
      exact Finset.sum_induction _ _ (fun _ _ h1 h2 => h1.add h2)
        Matrix.PosSemidef.zero (fun i _ => hpsd i)
    have hSnn : (0 : real_square_matrix n) ≤ matrix_family_sum A :=
      Matrix.nonneg_iff_posSemidef.mpr hSpsd
    set Q : real_square_matrix n := CFC.sqrt (matrix_family_sum A) with hQdef
    have hQnn : (0 : real_square_matrix n) ≤ Q := CFC.sqrt_nonneg _
    have hQpsd : Q.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hQnn
    have hQt : Q.transpose = Q := by
      have h := hQpsd.1.eq
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    have hQQ : Q * Q = matrix_family_sum A := CFC.sqrt_mul_sqrt_self _ hSnn
    have hQunit : IsUnit Q :=
      (CFC.isUnit_sqrt_iff (matrix_family_sum A) hSnn).mpr hunit
    have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det _).mp hQunit
    have hQinv1 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hdet
    have hQinv2 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
    have hTt : (Q⁻¹).transpose = Q⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, hQt]
    refine ⟨Q⁻¹, fun i => rfl, ?_, ?_⟩
    · intro X Y hXY
      have h1 : (Y - X).PosSemidef := Matrix.le_iff.mp hXY
      have h2 : (Q⁻¹ * (Y - X) * Q⁻¹).PosSemidef := by
        have h := h1.conjTranspose_mul_mul_same (Q⁻¹)
        rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hTt] at h
      rw [Matrix.le_iff]
      have h3 : Q⁻¹ * Y * Q⁻¹ - Q⁻¹ * X * Q⁻¹ = Q⁻¹ * (Y - X) * Q⁻¹ := by
        simp [Matrix.mul_sub, Matrix.sub_mul]
      rw [h3]
      exact h2
    · have h1 : (∑ i, normalized_matrix (matrix_family_sum A) (A i))
          = Q⁻¹ * matrix_family_sum A * Q⁻¹ := by
        have h0 : ∀ i, normalized_matrix (matrix_family_sum A) (A i)
            = Q⁻¹ * A i * Q⁻¹ := fun i => rfl
        simp only [h0]
        rw [matrix_family_sum, Matrix.mul_sum, Matrix.sum_mul]
      rw [h1]
      calc Q⁻¹ * matrix_family_sum A * Q⁻¹ = Q⁻¹ * (Q * Q) * Q⁻¹ := by rw [hQQ]
        _ = (Q⁻¹ * Q) * (Q * Q⁻¹) := by simp [Matrix.mul_assoc]
        _ = 1 := by rw [hQinv1, hQinv2, Matrix.mul_one]
  have hcountgen : ∀ (y : ι → ι → ℝ) (α t : ℝ) (Tt : Finset ι),
      (∀ i j, 0 ≤ y i j) →
      (∀ (i : ι) (E : Finset ι), ∑ j ∈ E, y i j ≤ 1) →
      (∀ i ∈ Tt, ∀ E : Finset ι, α • A i ≤ ∑ j ∈ E, A j →
        α * t ≤ ∑ j ∈ E, y i j) →
      0 < α → α ≤ 1 → 0 < t → t ≤ 1 →
      (Tt.card : ℝ) ≤ 1 + 4 * (connectivity_parameter A α : ℝ) / (α * t) := by
    intro y α t Tt hy0 hy1 hkey hα0 hα1 ht0 ht1
    classical
    have hN1 : 1 ≤ connectivity_parameter A α := by
      rcases Nat.eq_zero_or_pos (connectivity_parameter A α) with h0 | h0
      · obtain ⟨i, hi, -⟩ :=
          connectivity_parameter_spec A α ∅ (by rw [h0]; exact Nat.zero_le _)
        exact absurd hi (Finset.notMem_empty i)
      · exact h0
    have hαt0 : 0 < α * t := mul_pos hα0 ht0
    have hαt1 : α * t ≤ 1 := by nlinarith
    have hNpos : (0 : ℝ) < (connectivity_parameter A α : ℝ) := by exact_mod_cast hN1
    have hsub_mono : ∀ E F : Finset ι, E ⊆ F → ∑ j ∈ E, A j ≤ ∑ j ∈ F, A j := by
      intro E F hEF
      have h1 : ∑ j ∈ F \ E, A j = ∑ j ∈ F, A j - ∑ j ∈ E, A j := by
        rw [eq_sub_iff_add_eq]
        exact Finset.sum_sdiff hEF
      rw [Matrix.le_iff, ← h1]
      exact Finset.sum_induction _ _ (fun _ _ h1 h2 => h1.add h2)
        Matrix.PosSemidef.zero (fun i _ => hpsd i)
    by_cases hu : 2 * connectivity_parameter A α ≤ Tt.card
    · have hs2 : 2 ≤ 2 * connectivity_parameter A α := by omega
      have hsu : 2 * connectivity_parameter A α ≤ Tt.card := hu
      have hu2 : 2 ≤ Tt.card := le_trans hs2 hsu
      have hQbound : ∀ Q ∈ Tt.powersetCard (2 * connectivity_parameter A α),
          α * t * ((connectivity_parameter A α : ℝ) + 1)
            ≤ ∑ i ∈ Q, ∑ j ∈ Q.erase i, y i j := by
        intro Q hQ
        rw [Finset.mem_powersetCard] at hQ
        obtain ⟨hQT, hQcard⟩ := hQ
        have hbadcard : (Q.filter
            (fun i => ¬ (α • A i ≤ ∑ j ∈ Q.erase i, A j))).card
              < connectivity_parameter A α := by
          by_contra hcon
          obtain ⟨i, hi, hile⟩ := connectivity_parameter_spec A α
            (Q.filter (fun i => ¬ (α • A i ≤ ∑ j ∈ Q.erase i, A j)))
            (Nat.le_of_not_lt hcon)
          have hi2 := Finset.mem_filter.mp hi
          refine hi2.2 (le_trans hile ?_)
          refine hsub_mono _ _ ?_
          intro j hj
          have hj2 := Finset.mem_erase.mp hj
          exact Finset.mem_erase.mpr ⟨hj2.1, (Finset.mem_filter.mp hj2.2).1⟩
        have hcardsum : (Q.filter
              (fun i => α • A i ≤ ∑ j ∈ Q.erase i, A j)).card
            + (Q.filter (fun i => ¬ (α • A i ≤ ∑ j ∈ Q.erase i, A j))).card
              = Q.card :=
          Finset.filter_card_add_filter_neg_card_eq_card _
        have hgoodcard : connectivity_parameter A α + 1
            ≤ (Q.filter (fun i => α • A i ≤ ∑ j ∈ Q.erase i, A j)).card := by
          omega
        have hstep1 : (Q.filter (fun i => α • A i ≤ ∑ j ∈ Q.erase i, A j)).card
            • (α * t)
            ≤ ∑ i ∈ Q.filter (fun i => α • A i ≤ ∑ j ∈ Q.erase i, A j),
                ∑ j ∈ Q.erase i, y i j := by
          refine Finset.card_nsmul_le_sum _ _ (α * t) ?_
          intro i hi
          have hi2 := Finset.mem_filter.mp hi
          exact hkey i (hQT hi2.1) (Q.erase i) hi2.2
        have hstep2 : ∑ i ∈ Q.filter (fun i => α • A i ≤ ∑ j ∈ Q.erase i, A j),
              ∑ j ∈ Q.erase i, y i j
            ≤ ∑ i ∈ Q, ∑ j ∈ Q.erase i, y i j := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro i _ _
          exact Finset.sum_nonneg (fun j _ => hy0 i j)
        have hstep3 : α * t * ((connectivity_parameter A α : ℝ) + 1)
            ≤ (Q.filter (fun i => α • A i ≤ ∑ j ∈ Q.erase i, A j)).card • (α * t) := by
          rw [nsmul_eq_mul]
          have hcast : ((connectivity_parameter A α : ℝ) + 1)
              ≤ ((Q.filter (fun i => α • A i ≤ ∑ j ∈ Q.erase i, A j)).card : ℝ) := by
            have h := hgoodcard
            push_cast
            exact_mod_cast h
          nlinarith [hαt0.le]
        linarith [hstep1, hstep2, hstep3]
      have hPcard : (Tt.powersetCard (2 * connectivity_parameter A α)).card
          = Nat.choose Tt.card (2 * connectivity_parameter A α) :=
        Finset.card_powersetCard _ _
      have hsum1 : α * t * ((connectivity_parameter A α : ℝ) + 1)
            * (Nat.choose Tt.card (2 * connectivity_parameter A α) : ℝ)
          ≤ ∑ Q ∈ Tt.powersetCard (2 * connectivity_parameter A α),
              ∑ i ∈ Q, ∑ j ∈ Q.erase i, y i j := by
        have h := Finset.card_nsmul_le_sum
          (Tt.powersetCard (2 * connectivity_parameter A α))
          (fun Q => ∑ i ∈ Q, ∑ j ∈ Q.erase i, y i j)
          (α * t * ((connectivity_parameter A α : ℝ) + 1)) hQbound
        rw [nsmul_eq_mul, hPcard] at h
        linarith [h]
      have hrepr : ∀ Q ∈ Tt.powersetCard (2 * connectivity_parameter A α),
          ∑ i ∈ Q, ∑ j ∈ Q.erase i, y i j
            = ∑ i ∈ Tt, ∑ j ∈ Tt.erase i,
                (if i ∈ Q ∧ j ∈ Q then y i j else 0) := by
        intro Q hQ
        rw [Finset.mem_powersetCard] at hQ
        obtain ⟨hQT, -⟩ := hQ
        have hinner : ∀ i : ι, ∑ j ∈ Tt.erase i, (if i ∈ Q ∧ j ∈ Q then y i j else 0)
            = if i ∈ Q then ∑ j ∈ Q.erase i, y i j else 0 := by
          intro i
          by_cases hiQ : i ∈ Q
          · simp only [hiQ, true_and, if_true]
            rw [← Finset.sum_filter]
            refine Finset.sum_congr ?_ (fun _ _ => rfl)
            ext j
            simp only [Finset.mem_filter, Finset.mem_erase]
            exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hQT h.2⟩, h.2⟩⟩
          · simp [hiQ]
        rw [Finset.sum_congr rfl (fun i (_ : i ∈ Tt) => hinner i), ← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext i
        simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨hQT h, h⟩, fun h => h.2⟩
      have hswap : ∑ Q ∈ Tt.powersetCard (2 * connectivity_parameter A α),
            ∑ i ∈ Tt, ∑ j ∈ Tt.erase i, (if i ∈ Q ∧ j ∈ Q then y i j else 0)
          = ∑ i ∈ Tt, ∑ j ∈ Tt.erase i,
              ∑ Q ∈ Tt.powersetCard (2 * connectivity_parameter A α),
                (if i ∈ Q ∧ j ∈ Q then y i j else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
      have hpair : ∀ i ∈ Tt, ∀ j ∈ Tt.erase i,
          ∑ Q ∈ Tt.powersetCard (2 * connectivity_parameter A α),
              (if i ∈ Q ∧ j ∈ Q then y i j else 0)
            ≤ (Nat.choose (Tt.card - 2) (2 * connectivity_parameter A α - 2) : ℝ)
                * y i j := by
        intro i hi j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        have hjT : j ∈ Tt := (Finset.mem_erase.mp hj).2
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (hy0 i j)
        have hnat : (((Tt.powersetCard (2 * connectivity_parameter A α)).filter
              (fun Q => i ∈ Q ∧ j ∈ Q)).card)
            ≤ Nat.choose (Tt.card - 2) (2 * connectivity_parameter A α - 2) := by
          have hmap : ∀ Q ∈ (Tt.powersetCard (2 * connectivity_parameter A α)).filter
                (fun Q => i ∈ Q ∧ j ∈ Q),
              (Q.erase i).erase j ∈ ((Tt.erase i).erase j).powersetCard
                (2 * connectivity_parameter A α - 2) := by
            intro Q hQ
            have hQ1 := Finset.mem_filter.mp hQ
            have hQ2 := Finset.mem_powersetCard.mp hQ1.1
            refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
            · intro a ha
              have ha1 := Finset.mem_erase.mp ha
              have ha2 := Finset.mem_erase.mp ha1.2
              exact Finset.mem_erase.mpr
                ⟨ha1.1, Finset.mem_erase.mpr ⟨ha2.1, hQ2.1 ha2.2⟩⟩
            · rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hji, hQ1.2.2⟩),
                Finset.card_erase_of_mem hQ1.2.1, hQ2.2]
              omega
          have hinj : ∀ Q ∈ (Tt.powersetCard (2 * connectivity_parameter A α)).filter
                (fun Q => i ∈ Q ∧ j ∈ Q),
              ∀ Q' ∈ (Tt.powersetCard (2 * connectivity_parameter A α)).filter
                (fun Q => i ∈ Q ∧ j ∈ Q),
              (Q.erase i).erase j = (Q'.erase i).erase j → Q = Q' := by
            intro Q hQ Q' hQ' heq
            have hQ1 := Finset.mem_filter.mp hQ
            have hQ1' := Finset.mem_filter.mp hQ'
            ext a
            by_cases hai : a = i
            · subst hai
              simp [hQ1.2.1, hQ1'.2.1]
            · by_cases haj : a = j
              · subst haj
                simp [hQ1.2.2, hQ1'.2.2]
              · have h1 : a ∈ (Q.erase i).erase j ↔ a ∈ (Q'.erase i).erase j := by
                  rw [heq]
                simpa [Finset.mem_erase, haj, hai] using h1
          have hcc : Tt.card - 1 - 1 = Tt.card - 2 := by omega
          have h : ((Tt.powersetCard (2 * connectivity_parameter A α)).filter
                (fun Q => i ∈ Q ∧ j ∈ Q)).card
              ≤ (((Tt.erase i).erase j).powersetCard
                  (2 * connectivity_parameter A α - 2)).card := by
            refine Finset.card_le_card_of_injOn
              (fun Q : Finset ι => (Q.erase i).erase j) (fun Q hQ => ?_)
              (fun Q hQ Q' hQ' heq => ?_)
            · exact hmap Q hQ
            · exact hinj Q hQ Q' hQ' heq
          rwa [Finset.card_powersetCard,
            Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hji, hjT⟩),
            Finset.card_erase_of_mem hi, hcc] at h
        exact_mod_cast hnat
      have hbound2 : ∑ Q ∈ Tt.powersetCard (2 * connectivity_parameter A α),
            ∑ i ∈ Q, ∑ j ∈ Q.erase i, y i j
          ≤ (Nat.choose (Tt.card - 2) (2 * connectivity_parameter A α - 2) : ℝ)
              * (Tt.card : ℝ) := by
        have hc2nn : (0:ℝ)
            ≤ (Nat.choose (Tt.card - 2) (2 * connectivity_parameter A α - 2) : ℝ) :=
          Nat.cast_nonneg _
        calc ∑ Q ∈ Tt.powersetCard (2 * connectivity_parameter A α),
                ∑ i ∈ Q, ∑ j ∈ Q.erase i, y i j
            = ∑ Q ∈ Tt.powersetCard (2 * connectivity_parameter A α),
                ∑ i ∈ Tt, ∑ j ∈ Tt.erase i, (if i ∈ Q ∧ j ∈ Q then y i j else 0) :=
              Finset.sum_congr rfl hrepr
          _ = ∑ i ∈ Tt, ∑ j ∈ Tt.erase i,
                ∑ Q ∈ Tt.powersetCard (2 * connectivity_parameter A α),
                  (if i ∈ Q ∧ j ∈ Q then y i j else 0) := hswap
          _ ≤ ∑ i ∈ Tt, ∑ j ∈ Tt.erase i,
                (Nat.choose (Tt.card - 2) (2 * connectivity_parameter A α - 2) : ℝ)
                  * y i j :=
              Finset.sum_le_sum (fun i hi =>
                Finset.sum_le_sum (fun j hj => hpair i hi j hj))
          _ = ∑ i ∈ Tt,
                (Nat.choose (Tt.card - 2) (2 * connectivity_parameter A α - 2) : ℝ)
                  * ∑ j ∈ Tt.erase i, y i j := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [Finset.mul_sum]
          _ ≤ ∑ i ∈ Tt,
                (Nat.choose (Tt.card - 2) (2 * connectivity_parameter A α - 2) : ℝ)
                  * 1 :=
              Finset.sum_le_sum (fun i _ =>
                mul_le_mul_of_nonneg_left (hy1 i (Tt.erase i)) hc2nn)
          _ = (Nat.choose (Tt.card - 2) (2 * connectivity_parameter A α - 2) : ℝ)
                * (Tt.card : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
              ring
      have hchoose_id : Nat.choose Tt.card (2 * connectivity_parameter A α)
            * ((2 * connectivity_parameter A α)
                * (2 * connectivity_parameter A α - 1))
          = Nat.choose (Tt.card - 2) (2 * connectivity_parameter A α - 2)
              * (Tt.card * (Tt.card - 1)) := by
        obtain ⟨a, ha⟩ : ∃ a, Tt.card = a + 2 := ⟨Tt.card - 2, by omega⟩
        obtain ⟨b, hb⟩ : ∃ b, 2 * connectivity_parameter A α = b + 2 :=
          ⟨2 * connectivity_parameter A α - 2, by omega⟩
        have e1 : b + 2 - 1 = b + 1 := by omega
        have e2 : a + 2 - 1 = a + 1 := by omega
        have e3 : a + 2 - 2 = a := by omega
        have e4 : b + 2 - 2 = b := by omega
        rw [ha, hb, e1, e2, e3, e4]
        have h1 : (a + 1 + 1) * Nat.choose (a + 1) (b + 1)
            = Nat.choose (a + 1 + 1) (b + 1 + 1) * (b + 1 + 1) :=
          Nat.succ_mul_choose_eq (a + 1) (b + 1)
        have h2 : (a + 1) * Nat.choose a b = Nat.choose (a + 1) (b + 1) * (b + 1) :=
          Nat.succ_mul_choose_eq a b
        calc Nat.choose (a + 2) (b + 2) * ((b + 2) * (b + 1))
            = (Nat.choose (a + 1 + 1) (b + 1 + 1) * (b + 1 + 1)) * (b + 1) := by
              ring_nf
          _ = ((a + 1 + 1) * Nat.choose (a + 1) (b + 1)) * (b + 1) := by rw [h1]
          _ = (a + 2) * (Nat.choose (a + 1) (b + 1) * (b + 1)) := by ring
          _ = (a + 2) * ((a + 1) * Nat.choose a b) := by rw [h2]
          _ = Nat.choose a b * ((a + 2) * (a + 1)) := by ring
      have hc1pos : 0 < Nat.choose Tt.card (2 * connectivity_parameter A α) :=
        Nat.choose_pos hsu
      have hc2pos : 0 < Nat.choose (Tt.card - 2)
          (2 * connectivity_parameter A α - 2) := Nat.choose_pos (by omega)
      have hc2posR : (0:ℝ) < (Nat.choose (Tt.card - 2)
          (2 * connectivity_parameter A α - 2) : ℝ) := by exact_mod_cast hc2pos
      have hUpos : (0:ℝ) < (Tt.card : ℝ) := by
        have : 0 < Tt.card := by omega
        exact_mod_cast this
      have hU2 : (2:ℝ) ≤ (Tt.card : ℝ) := by exact_mod_cast hu2
      have e5 : ((2 * connectivity_parameter A α - 1 : ℕ) : ℝ)
          = 2 * (connectivity_parameter A α : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * connectivity_parameter A α)]
        push_cast
        ring
      have e6 : ((Tt.card - 1 : ℕ) : ℝ) = (Tt.card : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ Tt.card)]
        push_cast
        ring
      have hidR : (Nat.choose Tt.card (2 * connectivity_parameter A α) : ℝ)
            * ((2 * (connectivity_parameter A α : ℝ))
                * (2 * (connectivity_parameter A α : ℝ) - 1))
          = (Nat.choose (Tt.card - 2) (2 * connectivity_parameter A α - 2) : ℝ)
              * ((Tt.card : ℝ) * ((Tt.card : ℝ) - 1)) := by
        have h := congrArg (fun m : ℕ => (m : ℝ)) hchoose_id
        simp only [Nat.cast_mul] at h
        rw [e5, e6] at h
        push_cast at h
        linarith [h]
      have hmain : α * t * ((connectivity_parameter A α : ℝ) + 1)
            * (Nat.choose Tt.card (2 * connectivity_parameter A α) : ℝ)
          ≤ (Nat.choose (Tt.card - 2) (2 * connectivity_parameter A α - 2) : ℝ)
              * (Tt.card : ℝ) := le_trans hsum1 hbound2
      have hSnn : (0:ℝ) ≤ (2 * (connectivity_parameter A α : ℝ))
          * (2 * (connectivity_parameter A α : ℝ) - 1) := by nlinarith
      have h7 : α * t * ((connectivity_parameter A α : ℝ) + 1)
            * ((Nat.choose Tt.card (2 * connectivity_parameter A α) : ℝ)
              * ((2 * (connectivity_parameter A α : ℝ))
                * (2 * (connectivity_parameter A α : ℝ) - 1)))
          ≤ ((Nat.choose (Tt.card - 2) (2 * connectivity_parameter A α - 2) : ℝ)
                * (Tt.card : ℝ))
              * ((2 * (connectivity_parameter A α : ℝ))
                * (2 * (connectivity_parameter A α : ℝ) - 1)) := by
        have h := mul_le_mul_of_nonneg_right hmain hSnn
        nlinarith [h]
      rw [hidR] at h7
      have h9 : (α * t * ((connectivity_parameter A α : ℝ) + 1)
              * ((Tt.card : ℝ) - 1))
            * ((Nat.choose (Tt.card - 2) (2 * connectivity_parameter A α - 2) : ℝ)
              * (Tt.card : ℝ))
          ≤ ((2 * (connectivity_parameter A α : ℝ))
                * (2 * (connectivity_parameter A α : ℝ) - 1))
              * ((Nat.choose (Tt.card - 2)
                  (2 * connectivity_parameter A α - 2) : ℝ) * (Tt.card : ℝ)) := by
        nlinarith [h7]
      have h8 : α * t * ((connectivity_parameter A α : ℝ) + 1)
            * ((Tt.card : ℝ) - 1)
          ≤ (2 * (connectivity_parameter A α : ℝ))
              * (2 * (connectivity_parameter A α : ℝ) - 1) :=
        le_of_mul_le_mul_right h9 (mul_pos hc2posR hUpos)
      have h10 : α * t * ((Tt.card : ℝ) - 1) ≤ 4 * (connectivity_parameter A α : ℝ) := by
        nlinarith [h8, hNpos, hαt0, hU2]
      have h11 : (Tt.card : ℝ) - 1
          ≤ 4 * (connectivity_parameter A α : ℝ) / (α * t) := by
        rw [le_div_iff₀ hαt0]
        nlinarith [h10]
      linarith [h11]
    · have h1 : (Tt.card : ℝ) ≤ 2 * (connectivity_parameter A α : ℝ) := by
        have h2 : Tt.card ≤ 2 * connectivity_parameter A α :=
          le_of_lt (Nat.lt_of_not_le hu)
        exact_mod_cast h2
      have h2 : 4 * (connectivity_parameter A α : ℝ)
          ≤ 4 * (connectivity_parameter A α : ℝ) / (α * t) := by
        rw [le_div_iff₀ hαt0]
        nlinarith
      nlinarith
  obtain ⟨T, hTB, hTmono, hTsum⟩ := hsetup
  obtain ⟨B, hB⟩ : ∃ B : ι → real_square_matrix n, ∀ i, B i = T * A i * T :=
    ⟨fun i => T * A i * T, fun i => rfl⟩
  have hBsum : (∑ i, B i) = 1 := by
    rw [← hTsum]
    exact Finset.sum_congr rfl (fun i _ => by rw [hB i, hTB i])
  have hgoal : (∑ i, ‖normalized_matrix (matrix_family_sum A) (A i)‖) = ∑ i, ‖B i‖ :=
    Finset.sum_congr rfl (fun i _ => by rw [hB i, hTB i])
  rw [hgoal]
  have hBpsd : ∀ i, (B i).PosSemidef := by
    intro i
    have h1 : (0 : real_square_matrix n) ≤ A i :=
      Matrix.nonneg_iff_posSemidef.mpr (hpsd i)
    have h2 := hTmono 0 (A i) h1
    rw [Matrix.mul_zero, Matrix.zero_mul] at h2
    rw [hB i]
    exact Matrix.nonneg_iff_posSemidef.mp h2
  have hquadnn : ∀ (w : Fin n → ℝ) (X : real_square_matrix n), X.PosSemidef →
      0 ≤ dotProduct w (Matrix.mulVec X w) := by
    intro w X hX
    simpa using hX.dotProduct_mulVec_nonneg w
  have hquad_mono : ∀ (w : Fin n → ℝ) (X Y : real_square_matrix n), X ≤ Y →
      dotProduct w (Matrix.mulVec X w) ≤ dotProduct w (Matrix.mulVec Y w) := by
    intro w X Y hXY
    have h1 : (Y - X).PosSemidef := Matrix.le_iff.mp hXY
    have h2 := hquadnn w _ h1
    rw [Matrix.sub_mulVec, dotProduct_sub] at h2
    linarith
  have hquad_sum : ∀ (w : Fin n → ℝ) (E : Finset ι),
      dotProduct w (Matrix.mulVec (∑ j ∈ E, B j) w)
        = ∑ j ∈ E, dotProduct w (Matrix.mulVec (B j) w) := by
    intro w E
    rw [Matrix.sum_mulVec, dotProduct_sum]
  have hattain : ∀ i, ∃ v : Fin n → ℝ, dotProduct v v = 1 ∧
      ‖B i‖ ≤ dotProduct v (Matrix.mulVec (B i) v) :=
    fun i => hnormattain (B i) (hBpsd i)
  choose v hv1 hv2 using hattain
  obtain ⟨y, hydef⟩ : ∃ y : ι → ι → ℝ,
      ∀ i j, y i j = dotProduct (v i) (Matrix.mulVec (B j) (v i)) :=
    ⟨fun i j => dotProduct (v i) (Matrix.mulVec (B j) (v i)), fun i j => rfl⟩
  have hy0 : ∀ i j, 0 ≤ y i j := by
    intro i j
    rw [hydef]
    exact hquadnn _ _ (hBpsd j)
  have hy1 : ∀ (i : ι) (E : Finset ι), ∑ j ∈ E, y i j ≤ 1 := by
    intro i E
    have hsplit : ∑ j ∈ E, y i j ≤ ∑ j : ι, y i j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
        (fun j _ _ => hy0 i j)
    have huniv : ∑ j : ι, y i j = 1 := by
      have h1 : ∑ j : ι, y i j
          = dotProduct (v i) (Matrix.mulVec (∑ j : ι, B j) (v i)) := by
        rw [hquad_sum]
        exact Finset.sum_congr rfl (fun j _ => hydef i j)
      rw [h1, hBsum, Matrix.one_mulVec, hv1 i]
    linarith
  have hnormle : ∀ i, ‖B i‖ ≤ y i i := by
    intro i
    rw [hydef]
    exact hv2 i
  have hnorm1 : ∀ i, ‖B i‖ ≤ 1 := by
    intro i
    refine le_trans (hnormle i) ?_
    have h := hy1 i {i}
    simpa using h
  have hkey : ∀ (α t : ℝ), 0 < α →
      ∀ i ∈ Finset.univ.filter (fun i => t ≤ ‖B i‖), ∀ E : Finset ι,
        α • A i ≤ ∑ j ∈ E, A j → α * t ≤ ∑ j ∈ E, y i j := by
    intro α t hα0 i hi E hle
    have hti : t ≤ ‖B i‖ := (Finset.mem_filter.mp hi).2
    have h1 : T * (α • A i) * T ≤ T * (∑ j ∈ E, A j) * T := hTmono _ _ hle
    have h2 : T * (α • A i) * T = α • B i := by
      rw [hB i]
      simp [Matrix.mul_smul, Matrix.smul_mul]
    have h3 : T * (∑ j ∈ E, A j) * T = ∑ j ∈ E, B j := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => (hB j).symm)
    rw [h2, h3] at h1
    have h4 := hquad_mono (v i) _ _ h1
    rw [hquad_sum] at h4
    have h6 : ∑ j ∈ E, dotProduct (v i) (Matrix.mulVec (B j) (v i))
        = ∑ j ∈ E, y i j :=
      Finset.sum_congr rfl (fun j _ => (hydef i j).symm)
    rw [h6] at h4
    have h5 : dotProduct (v i) (Matrix.mulVec (α • B i) (v i)) = α * y i i := by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hydef]
    rw [h5] at h4
    calc α * t ≤ α * y i i :=
          mul_le_mul_of_nonneg_left (le_trans hti (hnormle i)) hα0.le
      _ ≤ ∑ j ∈ E, y i j := h4
  have hcount : ∀ (α t : ℝ), 0 < α → α ≤ 1 → 0 < t → t ≤ 1 →
      ((Finset.univ.filter (fun i => t ≤ ‖B i‖)).card : ℝ)
        ≤ 1 + 4 * (connectivity_parameter A α : ℝ) / (α * t) := by
    intro α t hα0 hα1 ht0 ht1
    exact hcountgen y α t (Finset.univ.filter (fun i => t ≤ ‖B i‖)) hy0 hy1
      (hkey α t hα0) hα0 hα1 ht0 ht1
  have hpoint : ∀ i, ‖B i‖ ≤ (1/2:ℝ) ^ (Nat.log 2 (Fintype.card ι) + 1)
      + ∑ k ∈ Finset.range (Nat.log 2 (Fintype.card ι) + 1), (1/2:ℝ)^k *
        (if (1/2:ℝ)^(k+1) ≤ ‖B i‖ then 1 else 0) := by
    intro i
    have hnn : ∀ k : ℕ,
        0 ≤ (1/2:ℝ)^k * (if (1/2:ℝ)^(k+1) ≤ ‖B i‖ then 1 else 0) := by
      intro k
      have h1 : (0:ℝ) ≤ (if (1/2:ℝ)^(k+1) ≤ ‖B i‖ then 1 else 0) := by
        split <;> norm_num
      have h2 : (0:ℝ) ≤ (1/2:ℝ)^k := by positivity
      exact mul_nonneg h2 h1
    by_cases hsmall : ‖B i‖ ≤ (1/2:ℝ) ^ (Nat.log 2 (Fintype.card ι) + 1)
    · have h3 : 0 ≤ ∑ k ∈ Finset.range (Nat.log 2 (Fintype.card ι) + 1),
          (1/2:ℝ)^k * (if (1/2:ℝ)^(k+1) ≤ ‖B i‖ then 1 else 0) :=
        Finset.sum_nonneg (fun k _ => hnn k)
      linarith
    · have hbig : (1/2:ℝ) ^ (Nat.log 2 (Fintype.card ι) + 1) ≤ ‖B i‖ :=
        le_of_lt (not_le.mp hsmall)
      have hne : ((Finset.range (Nat.log 2 (Fintype.card ι) + 1)).filter
          (fun k => (1/2:ℝ)^(k+1) ≤ ‖B i‖)).Nonempty := by
        refine ⟨Nat.log 2 (Fintype.card ι), ?_⟩
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hbig⟩
      obtain ⟨k₀, hk0mem, hk0min⟩ : ∃ k₀ : ℕ,
          k₀ ∈ (Finset.range (Nat.log 2 (Fintype.card ι) + 1)).filter
            (fun k => (1/2:ℝ)^(k+1) ≤ ‖B i‖) ∧
          ∀ m ∈ (Finset.range (Nat.log 2 (Fintype.card ι) + 1)).filter
            (fun k => (1/2:ℝ)^(k+1) ≤ ‖B i‖), k₀ ≤ m :=
        ⟨_, Finset.min'_mem _ hne, fun m hm => Finset.min'_le _ _ hm⟩
      have hk0 := hk0mem
      rw [Finset.mem_filter, Finset.mem_range] at hk0
      have hxle : ‖B i‖ ≤ (1/2:ℝ)^k₀ := by
        rcases Nat.eq_zero_or_pos k₀ with h0 | hpos
        · rw [h0, pow_zero]
          exact hnorm1 i
        · have h1 : ¬ ((1/2:ℝ)^(k₀ - 1 + 1) ≤ ‖B i‖) := by
            intro hcon
            have hmem : (k₀ - 1) ∈
                (Finset.range (Nat.log 2 (Fintype.card ι) + 1)).filter
                  (fun k => (1/2:ℝ)^(k+1) ≤ ‖B i‖) := by
              rw [Finset.mem_filter, Finset.mem_range]
              exact ⟨by omega, hcon⟩
            have hcc := hk0min _ hmem
            omega
          have h2 : k₀ - 1 + 1 = k₀ := by omega
          rw [h2] at h1
          exact le_of_lt (not_le.mp h1)
      have hterm : (1/2:ℝ)^k₀ ≤ ∑ k ∈ Finset.range (Nat.log 2 (Fintype.card ι) + 1),
          (1/2:ℝ)^k * (if (1/2:ℝ)^(k+1) ≤ ‖B i‖ then 1 else 0) := by
        have hmemR : k₀ ∈ Finset.range (Nat.log 2 (Fintype.card ι) + 1) :=
          Finset.mem_range.mpr hk0.1
        have heq : (1/2:ℝ)^k₀ = (1/2:ℝ)^k₀ *
            (if (1/2:ℝ)^(k₀+1) ≤ ‖B i‖ then 1 else 0) := by
          rw [if_pos hk0.2, mul_one]
        rw [heq]
        exact Finset.single_le_sum (fun k _ => hnn k) hmemR
      have hKnn : (0:ℝ) ≤ (1/2:ℝ) ^ (Nat.log 2 (Fintype.card ι) + 1) := by positivity
      linarith
  have hsum : ∑ i, ‖B i‖ ≤ (Fintype.card ι : ℝ) *
      (1/2:ℝ) ^ (Nat.log 2 (Fintype.card ι) + 1)
      + ∑ k ∈ Finset.range (Nat.log 2 (Fintype.card ι) + 1), (1/2:ℝ)^k *
        ((Finset.univ.filter (fun i => (1/2:ℝ)^(k+1) ≤ ‖B i‖)).card : ℝ) := by
    have h1 : ∑ i, ‖B i‖ ≤ ∑ i : ι,
        ((1/2:ℝ) ^ (Nat.log 2 (Fintype.card ι) + 1)
          + ∑ k ∈ Finset.range (Nat.log 2 (Fintype.card ι) + 1), (1/2:ℝ)^k *
            (if (1/2:ℝ)^(k+1) ≤ ‖B i‖ then 1 else 0)) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    refine le_trans h1 (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.mul_sum, Finset.sum_boole]
  have hrK : (Fintype.card ι : ℝ) *
      (1/2:ℝ) ^ (Nat.log 2 (Fintype.card ι) + 1) ≤ 1 := by
    have h1 : Fintype.card ι < 2 ^ (Nat.log 2 (Fintype.card ι) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 : (Fintype.card ι : ℝ) ≤ (2:ℝ) ^ (Nat.log 2 (Fintype.card ι) + 1) := by
      have h3 : ((2 ^ (Nat.log 2 (Fintype.card ι) + 1) : ℕ) : ℝ)
          = (2:ℝ) ^ (Nat.log 2 (Fintype.card ι) + 1) := by push_cast; ring
      rw [← h3]
      exact Nat.cast_le.mpr (le_of_lt h1)
    have h4 : (0:ℝ) < (2:ℝ) ^ (Nat.log 2 (Fintype.card ι) + 1) := by positivity
    have h5 : (1/2:ℝ) ^ (Nat.log 2 (Fintype.card ι) + 1)
        = ((2:ℝ) ^ (Nat.log 2 (Fintype.card ι) + 1))⁻¹ := by
      rw [one_div, inv_pow]
    rw [h5, mul_inv_le_iff₀ h4, one_mul]
    exact h2
  have hlog2 : (1:ℝ)/2 ≤ Real.log 2 := by
    have h1 : Real.log (1/2) ≤ 1/2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    rw [Real.log_div one_ne_zero (by norm_num), Real.log_one] at h1
    linarith
  have hKbound : ((Nat.log 2 (Fintype.card ι) : ℝ) + 1)
      ≤ 1 + 2 * Real.log (Fintype.card ι : ℝ) := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
    · rw [h]
      simp
    · have hr0 : Fintype.card ι ≠ 0 := by omega
      have h1 : 2 ^ (Nat.log 2 (Fintype.card ι)) ≤ Fintype.card ι :=
        Nat.pow_log_le_self 2 hr0
      have h2 : ((2:ℝ) ^ (Nat.log 2 (Fintype.card ι))) ≤ (Fintype.card ι : ℝ) := by
        have h3 : ((2 ^ (Nat.log 2 (Fintype.card ι)) : ℕ) : ℝ)
            = (2:ℝ) ^ (Nat.log 2 (Fintype.card ι)) := by push_cast; ring
        rw [← h3]
        exact Nat.cast_le.mpr h1
      have h4 : Real.log ((2:ℝ) ^ (Nat.log 2 (Fintype.card ι)))
          ≤ Real.log (Fintype.card ι : ℝ) := Real.log_le_log (by positivity) h2
      rw [Real.log_pow] at h4
      nlinarith [hlogr, hlog2]
  have hN1 : ∀ α : ℝ, 1 ≤ connectivity_parameter A α := by
    intro α
    rcases Nat.eq_zero_or_pos (connectivity_parameter A α) with h0 | h0
    · obtain ⟨i, hi, -⟩ :=
        connectivity_parameter_spec A α ∅ (by rw [h0]; exact Nat.zero_le _)
      exact absurd hi (Finset.notMem_empty i)
    · exact h0
  have hlayer : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ k : ℕ,
      (1/2:ℝ)^k * ((Finset.univ.filter
          (fun i => (1/2:ℝ)^(k+1) ≤ ‖B i‖)).card : ℝ)
        ≤ (1/2:ℝ)^k + 8 * (connectivity_parameter A α : ℝ) / α := by
    intro α hα0 hα1 k
    have ht0 : (0:ℝ) < (1/2:ℝ)^(k+1) := by positivity
    have ht1 : (1/2:ℝ)^(k+1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h := hcount α ((1/2:ℝ)^(k+1)) hα0 hα1 ht0 ht1
    have hpk : (0:ℝ) < (1/2:ℝ)^k := by positivity
    have hmul := mul_le_mul_of_nonneg_left h hpk.le
    refine le_trans hmul (le_of_eq ?_)
    have hαne : α ≠ 0 := ne_of_gt hα0
    have hpne : ((1/2:ℝ)^k) ≠ 0 := ne_of_gt hpk
    rw [mul_add, mul_one]
    congr 1
    rw [pow_succ]
    field_simp
    ring
  have hper : ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∑ i, ‖B i‖ ≤ 100 * (1 + Real.log (Fintype.card ι : ℝ))
        * ((connectivity_parameter A α : ℝ) / α) := by
    intro α hα0 hα1
    have hN1R : (1:ℝ) ≤ (connectivity_parameter A α : ℝ) := by
      exact_mod_cast hN1 α
    have hq1 : (1:ℝ) ≤ (connectivity_parameter A α : ℝ) / α := by
      rw [le_div_iff₀ hα0]
      nlinarith
    have hq0 : (0:ℝ) ≤ (connectivity_parameter A α : ℝ) / α := by linarith
    have hstep1 : ∑ k ∈ Finset.range (Nat.log 2 (Fintype.card ι) + 1), (1/2:ℝ)^k *
        ((Finset.univ.filter (fun i => (1/2:ℝ)^(k+1) ≤ ‖B i‖)).card : ℝ)
        ≤ ∑ k ∈ Finset.range (Nat.log 2 (Fintype.card ι) + 1),
          ((1/2:ℝ)^k + 8 * (connectivity_parameter A α : ℝ) / α) :=
      Finset.sum_le_sum (fun k _ => hlayer α hα0 hα1 k)
    have hstep2 : ∑ k ∈ Finset.range (Nat.log 2 (Fintype.card ι) + 1),
        ((1/2:ℝ)^k + 8 * (connectivity_parameter A α : ℝ) / α)
        = (∑ k ∈ Finset.range (Nat.log 2 (Fintype.card ι) + 1), (1/2:ℝ)^k)
          + ((Nat.log 2 (Fintype.card ι) : ℝ) + 1)
            * (8 * (connectivity_parameter A α : ℝ) / α) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    have hgeo : (∑ k ∈ Finset.range (Nat.log 2 (Fintype.card ι) + 1), (1/2:ℝ)^k)
        ≤ 2 := by
      have h := sum_geometric_two_le (Nat.log 2 (Fintype.card ι) + 1)
      simpa using h
    have hfac : (0:ℝ) ≤ 8 * (connectivity_parameter A α : ℝ) / α := by
      positivity
    have hKmul : ((Nat.log 2 (Fintype.card ι) : ℝ) + 1)
        * (8 * (connectivity_parameter A α : ℝ) / α)
        ≤ (1 + 2 * Real.log (Fintype.card ι : ℝ))
          * (8 * (connectivity_parameter A α : ℝ) / α) :=
      mul_le_mul_of_nonneg_right hKbound hfac
    have hfinal : ∑ i, ‖B i‖ ≤ 1 + 2 + (1 + 2 * Real.log (Fintype.card ι : ℝ))
        * (8 * (connectivity_parameter A α : ℝ) / α) := by
      calc ∑ i, ‖B i‖ ≤ (Fintype.card ι : ℝ) *
            (1/2:ℝ) ^ (Nat.log 2 (Fintype.card ι) + 1)
            + ∑ k ∈ Finset.range (Nat.log 2 (Fintype.card ι) + 1), (1/2:ℝ)^k *
              ((Finset.univ.filter (fun i => (1/2:ℝ)^(k+1) ≤ ‖B i‖)).card : ℝ) :=
            hsum
        _ ≤ 1 + 2 + (1 + 2 * Real.log (Fintype.card ι : ℝ))
            * (8 * (connectivity_parameter A α : ℝ) / α) := by
            rw [hstep2] at hstep1
            linarith
    have hprod : 0 ≤ Real.log (Fintype.card ι : ℝ)
        * ((connectivity_parameter A α : ℝ) / α) := mul_nonneg hlogr hq0
    have hexp : (1 + 2 * Real.log (Fintype.card ι : ℝ))
        * (8 * (connectivity_parameter A α : ℝ) / α)
        = 8 * ((connectivity_parameter A α : ℝ) / α)
          + 16 * (Real.log (Fintype.card ι : ℝ)
            * ((connectivity_parameter A α : ℝ) / α)) := by
      field_simp
      ring
    rw [hexp] at hfinal
    nlinarith [hfinal, hq1, hprod]
  have hbdd : BddBelow {x : ℝ | ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      x = (connectivity_parameter A α : ℝ) / α} := by
    refine ⟨0, ?_⟩
    intro x hx
    obtain ⟨β, hβ0, -, rfl⟩ := hx
    exact div_nonneg (Nat.cast_nonneg _) hβ0.le
  have hfin : (∑ i, ‖B i‖) / (100 * (1 + Real.log (Fintype.card ι : ℝ)))
      ≤ connectivity_ratio A := by
    unfold connectivity_ratio
    refine le_csInf ⟨(connectivity_parameter A 1 : ℝ)/1, 1, one_pos, le_refl 1, rfl⟩ ?_
    intro b hb
    obtain ⟨α, hα0, hα1, rfl⟩ := hb
    rw [div_le_iff₀ hden]
    have h := hper α hα0 hα1
    calc ∑ i, ‖B i‖ ≤ 100 * (1 + Real.log (Fintype.card ι : ℝ))
          * ((connectivity_parameter A α : ℝ) / α) := h
      _ = (connectivity_parameter A α : ℝ) / α
          * (100 * (1 + Real.log (Fintype.card ι : ℝ))) := by ring
  rw [div_le_iff₀ hden] at hfin
  linarith [hfin]

@[blueprint "def:matrix-bernstein-independent"
  (statement := /-- Let \((\Omega,\mathcal F,\mathbb P)\) be a probability
  space and let \(X_i:\Omega\to\operatorname{Mat}_n(\mathbb R)\), for
  \(i\in\operatorname{Fin}(N)\), be measurable random matrices.  Write
  \(\operatorname{MBIndep}(X,\mathbb P)\) for the assertion that the family
  \((X_i)_{i\in\operatorname{Fin}(N)}\) is jointly independent. -/)
  (title := /-- Independence of a finite random-matrix family -/)
  (latexEnv := "definition")]
noncomputable def matrix_bernstein_independent {Ω : Type*}
    [MeasurableSpace Ω] {n N : ℕ}
    (X : Fin N → Ω → real_square_matrix n) (μ : Measure Ω) : Prop :=
  letI : MeasurableSpace (real_square_matrix n) := borel _
  @iIndepFun Ω (Fin N) _ (fun _ : Fin N => real_square_matrix n)
    (fun _ => inferInstance) X μ

@[blueprint "def:matrix-bernstein-sum"
  (statement := /-- For a finite family of random matrices
  \(X_i:\Omega\to\operatorname{Mat}_n(\mathbb R)\), define
  \[
    Z(\omega):=\sum_{i\in\operatorname{Fin}(N)}X_i(\omega).
  \] -/)
  (title := /-- Sum of finite random matrices -/)
  (latexEnv := "definition")]
noncomputable def matrix_bernstein_sum {Ω : Type*} {n N : ℕ}
    (X : Fin N → Ω → real_square_matrix n) (ω : Ω) :
    real_square_matrix n :=
  ∑ i, X i ω

@[blueprint "def:matrix-bernstein-variance-matrix"
  (statement := /-- Let \(X_i\) be square-integrable random matrices on a
  measure space \((\Omega,\mathcal F,\mu)\).  Define their aggregate
  second-moment matrix by
  \[
    V(X,\mu):=\sum_{i\in\operatorname{Fin}(N)}
      \int_\Omega X_i(\omega)^2\,d\mu(\omega).
  \] -/)
  (title := /-- Aggregate matrix second moment -/)
  (latexEnv := "definition")]
noncomputable def matrix_bernstein_variance_matrix {Ω : Type*}
    [MeasurableSpace Ω] {n N : ℕ} (μ : Measure Ω)
    (X : Fin N → Ω → real_square_matrix n) : real_square_matrix n :=
  ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ

@[blueprint "def:matrix-bernstein-variance-proxy"
  (statement := /-- Define the matrix Bernstein variance proxy by
  \[
    \sigma^2(X,\mu):=\lVert V(X,\mu)\rVert.
  \] -/)
  (title := /-- Matrix Bernstein variance proxy -/)
  (latexEnv := "definition")]
noncomputable def matrix_bernstein_variance_proxy {Ω : Type*}
    [MeasurableSpace Ω] {n N : ℕ} (μ : Measure Ω)
    (X : Fin N → Ω → real_square_matrix n) : ℝ :=
  ‖matrix_bernstein_variance_matrix μ X‖

@[blueprint "def:matrix-bernstein-tail-bound"
  (statement := /-- For a matrix dimension \(n\), variance proxy
  \(\sigma^2\), almost-sure norm bound \(K\), and threshold \(t\), define
  \[
    \operatorname{MBTail}(n,\sigma^2,K,t)
      :=2n\exp\!\left(-\frac{t^2/2}{\sigma^2+Kt/3}\right).
  \] -/)
  (title := /-- Matrix Bernstein tail bound -/)
  (latexEnv := "definition")]
noncomputable def matrix_bernstein_tail_bound
    (n : ℕ) (σ_sq K t : ℝ) : ℝ :=
  2 * (n : ℝ) * Real.exp (-(t ^ 2 / 2) / (σ_sq + K * t / 3))

@[blueprint "lem:matrix-bernstein-inequality"
  (statement := /-- Let \((\Omega,\mathcal F,\mu)\) be a probability space,
  let \(n>0\), and let
  \(X_i:\Omega\to\operatorname{Mat}_n(\mathbb R)\), for
  \(i\in\operatorname{Fin}(N)\), be independent random Hermitian matrices.
  Suppose that every \(X_i\) is integrable and square-integrable, that
  \(\mathbb E X_i=0\), and that \(\lVert X_i\rVert\leq K\) almost surely.
  Then, for every \(t\geq0\),
  \[
    \mathbb P\!\left(\left\lVert\sum_iX_i\right\rVert\geq t\right)
      \leq 2n\exp\!\left(
        -\frac{t^2/2}{\left\lVert\sum_i\mathbb E X_i^2\right\rVert+Kt/3}
      \right).
  \] -/)
  (proof := /-- Fix \(\theta\in(0,3/K)\).  For every Hermitian matrix
  \(Y\) satisfying \(\mathbb EY=0\) and \(\lVert Y\rVert\leq K\), functional
  calculus applied to the scalar exponential series gives
  \[
    \mathbb E e^{\theta Y}
      \preceq\exp\!\left(
        \frac{\theta^2/2}{1-\theta K/3}\,\mathbb EY^2
      \right).
  \]
  Independence, the trace-exponential Laplace transform, and Lieb
  concavity therefore imply
  \[
    \mathbb P\!\left(\lambda_{\max}\!\left(\sum_iX_i\right)\geq t\right)
      \leq n\exp\!\left(
        -\theta t+
        \frac{\theta^2\sigma^2/2}{1-\theta K/3}
      \right),
  \]
  where \(\sigma^2=\left\lVert\sum_i\mathbb EX_i^2\right\rVert\), as
  specified by \cref{def:matrix-bernstein-variance-proxy}.  Choosing
  \(\theta=t/(\sigma^2+Kt/3)\) gives the stated exponent.  Applying the same
  argument to \((-X_i)_i\) bounds the lower tail, since
  \(\lambda_{\max}(-\sum_iX_i)=-\lambda_{\min}(\sum_iX_i)\).  The union
  bound for these two events and
  \(\lVert H\rVert=\max\{\lambda_{\max}(H),-\lambda_{\min}(H)\}\) for
  Hermitian \(H\) yield the factor \(2n\) and the asserted two-sided norm
  estimate. -/)
  (title := /-- Matrix Bernstein inequality -/)
  (latexEnv := "lemma")]
lemma matrix_bernstein_inequality {Ω : Type*} [MeasurableSpace Ω]
    {n N : ℕ} (X : Fin N → Ω → real_square_matrix n)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (K : ℝ) :
    0 < n →
    matrix_bernstein_independent X μ →
    (∀ i, Integrable (X i) μ) →
    (∀ i, Integrable (fun ω => (X i ω) ^ 2) μ) →
    (∀ i, ∫ ω, X i ω ∂μ = 0) →
    (∀ i, ∀ᵐ ω ∂μ, (X i ω).IsHermitian) →
    (∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ K) →
    ∀ t : ℝ, 0 ≤ t →
      (μ {ω | ‖matrix_bernstein_sum X ω‖ ≥ t}).toReal ≤
        matrix_bernstein_tail_bound n
          (matrix_bernstein_variance_proxy μ X) K t := by
  exact RMT.matrix_bernstein_inequality_hdp_all X μ K

@[blueprint "lem:leverage-score-psd-sparsification"
  (statement := /-- There is an absolute constant \(C>0\) such that, for
  every finite PSD family with invertible sum and every
  \(\varepsilon\in(0,1]\), there are nonnegative weights \(\mu\) satisfying
  the two-sided spectral approximation and
  \[
    |\operatorname{supp}\mu|
      \leq C\varepsilon^{-2}(1+\log n)
        \sum_i\|\widetilde A_i\|.
  \] -/)
  (proof := /-- Put \(R=\varepsilon^2/(16\log(4n))\), write
  \(B_i=\widetilde A_i\), and set
  \(q_i=\min\{1,\lVert B_i\rVert/R\}\).  Retain \(B_i\) independently with
  probability \(q_i\), assigning it weight \(q_i^{-1}\) when retained, and
  let \(X_i\) denote the resulting weighted matrix.  Thus
  \(\mathbb EX_i=B_i\).  For \(Y_i=X_i-B_i\), the deterministic indices
  have \(Y_i=0\), while every remaining index satisfies
  \[
    \lVert Y_i\rVert\leq R,\qquad
    \mathbb EY_i^2
      =B_i^2(q_i^{-1}-1)
      \preceq B_i^2/q_i
      \preceq RB_i.
  \]
  Since \(\sum_iB_i=I\), the variance proxy is at most \(R\).
  Applying \cref{lem:matrix-bernstein-inequality} at \(t=\varepsilon\)
  shows, with probability at least \(3/4\), that
  \(\lVert\sum_iY_i\rVert\leq\varepsilon\), which is equivalent to
  \[
    (1-\varepsilon)I\preceq\sum_iX_i\preceq(1+\varepsilon)I.
  \]

  The support size \(Z\) has expectation
  \[
    \mathbb EZ=\sum_iq_i
      \leq R^{-1}\sum_i\lVert B_i\rVert.
  \]
  Markov's inequality gives
  \(\mathbb P(Z\leq4\mathbb EZ)\geq3/4\).  Hence the approximation event and
  this support event occur simultaneously with positive probability.
  Choose such an outcome and let \(\mu_i\) be its sampling weight.
  Congruence by \(S^{1/2}\), where \(S=\sum_iA_i\), transfers the displayed
  inequalities to
  \((1-\varepsilon)S\preceq\sum_i\mu_iA_i\preceq(1+\varepsilon)S\).
  Finally, substituting the value of \(R\) into the bound for \(Z\) and
  absorbing the fixed numerical factors into an absolute constant gives
  the asserted support estimate. -/)
  (title := /-- Leverage-score sparsification of an invertible PSD sum -/)
  (latexEnv := "lemma")]
lemma leverage_score_psd_sparsification :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
        (A : ι → real_square_matrix n) (ε : ℝ),
        (∀ i, (A i).PosSemidef) →
        IsUnit (matrix_family_sum A) →
        0 < ε → ε ≤ 1 →
        ∃ μ : ι → NNReal,
          spectral_sparsifier A ε μ ∧
          (weight_support_cardinality μ : ℝ) ≤
            C * ε⁻¹ ^ 2 * (1 + Real.log (n : ℝ)) *
              ∑ i, ‖normalized_matrix (matrix_family_sum A) (A i)‖ := by
  classical
  refine ⟨128, by norm_num, ?_⟩
  intro n ι _ _ A ε hpsd hunit hε0 hε1
  have hcore : ∀ (B : ι → real_square_matrix n) (ε : ℝ),
      (∀ i, (B i).PosSemidef) → (∑ i, B i) = 1 → 0 < ε → ε ≤ 1 → 0 < n →
      ∃ ν : ι → NNReal,
        ((1 - ε) • (1 : real_square_matrix n) ≤ ∑ i, (ν i : ℝ) • B i) ∧
        (∑ i, (ν i : ℝ) • B i ≤ (1 + ε) • (1 : real_square_matrix n)) ∧
        ((weight_support_cardinality ν : ℝ) ≤
          64 * Real.log (4 * (n : ℝ)) * (∑ i, ‖B i‖) / ε ^ 2) := by
    intro B ε hpsd hsum hε0 hε1 hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog : 0 < Real.log (4 * (n : ℝ)) :=
      Real.log_pos (by linarith)
    set R : ℝ := ε ^ 2 / (16 * Real.log (4 * (n : ℝ))) with hRdef
    have hR0 : 0 < R := by positivity
    set x : ι → ℝ := fun i => ‖B i‖ with hxdef
    have hx0 : ∀ i, 0 ≤ x i := fun i => norm_nonneg _
    set q : ι → ℝ := fun i => min 1 (x i / R) with hqdef
    have hq0 : ∀ i, 0 ≤ q i := by
      intro i
      simp only [hqdef]
      exact le_min zero_le_one (div_nonneg (hx0 i) hR0.le)
    have hq1 : ∀ i, q i ≤ 1 := by
      intro i
      simp only [hqdef]
      exact min_le_left _ _
    have hcase : ∀ i, (R ≤ x i ∧ q i = 1) ∨ (x i ≤ R ∧ q i = x i / R) := by
      intro i
      rcases le_or_gt (x i) R with h | h
      · refine Or.inr ⟨h, ?_⟩
        have hxr : x i / R ≤ 1 := (div_le_one hR0).mpr h
        rw [hqdef]
        exact min_eq_right hxr
      · refine Or.inl ⟨h.le, ?_⟩
        rw [hqdef]
        exact min_eq_left ((one_le_div_iff).mpr (Or.inl ⟨hR0, h.le⟩))
    have hqle : ∀ i, q i ≤ x i / R := by
      intro i
      simp only [hqdef]
      exact min_le_right _ _
    have hex : ∃ i₀ : ι, B i₀ ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      have hz : (∑ i, B i) = 0 := Finset.sum_eq_zero fun i _ => hcon i
      rw [hsum] at hz
      have h00 := congrArg (fun M : real_square_matrix n => M ⟨0, hn⟩ ⟨0, hn⟩) hz
      simp at h00
    obtain ⟨i₀, hi₀⟩ := hex
    have hxi₀ : 0 < x i₀ := by
      rw [hxdef]
      exact norm_pos_iff.mpr hi₀
    have hqi₀ : 0 < q i₀ := by
      rcases hcase i₀ with ⟨-, hq1'⟩ | ⟨-, hq2'⟩
      · rw [hq1']; exact zero_lt_one
      · rw [hq2']; exact div_pos hxi₀ hR0
    have hqsum0 : (0 : ℝ) < ∑ i, q i :=
      lt_of_lt_of_le hqi₀
        (Finset.single_le_sum (fun i _ => hq0 i) (Finset.mem_univ i₀))
    have hBerIcc : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1 := fun i => ⟨hq0 i, hq1 i⟩
    letI hMatMeas : MeasurableSpace (real_square_matrix n) := borel _
    set d : ι → Bool → ℝ := fun i b => if b then (q i)⁻¹ - 1 else -1 with hddef
    set Y : ι → (ι → Bool) → real_square_matrix n :=
      fun i ω => (d i (ω i)) • B i with hYdef
    have hHermSM : ∀ (c : ℝ) {M : real_square_matrix n}, M.IsHermitian → (c • M).IsHermitian := by
      intro c M hM
      refine Matrix.IsHermitian.ext fun i j => ?_
      have h1 : star (M j i) = M i j := hM.apply i j
      simp only [star_trivial] at h1
      simp only [Matrix.smul_apply, smul_eq_mul, star_trivial, h1]
    have hfm : ∀ i, Measurable (fun b : Bool => (d i b) • B i) :=
      fun i => Measurable.of_discrete
    have hintBer : ∀ i, Integrable (fun b : Bool => (d i b) • B i)
        (ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩) :=
      fun i => ProbabilityTheory.integrable_bernoulliMeasure _ _ _ _
    have hae : ∀ (i : ι) (f : Bool → real_square_matrix n),
        AEStronglyMeasurable f
          (ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩) := by
      intro i f
      refine ⟨fun b => if b then f true else f false, StronglyMeasurable.of_discrete, ?_⟩
      refine Filter.Eventually.of_forall fun b => ?_
      cases b <;> rfl
    have hintegral : ∀ (i : ι) (f : Bool → real_square_matrix n),
        ∫ ω : ι → Bool, f (ω i) ∂
          (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
          = ((q i : ℝ) • f true + (1 - q i : ℝ) • f false) := by
      intro i f
      rw [MeasureTheory.integral_comp_eval
        (μ := fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
        (i := i) (f := f) (hae i f)]
      exact ProbabilityTheory.integral_bernoulliMeasure true false ⟨q i, hBerIcc i⟩ f
    have hintgen : ∀ (i : ι), Integrable
        (fun ω : ι → Bool => (fun b : Bool => (d i b) • B i) (ω i))
        (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩) :=
      fun i => MeasureTheory.integrable_comp_eval
        (μ := fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩) (hintBer i)
    have hint1 : ∀ i, Integrable (Y i)
        (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩) :=
      fun i => hintgen i
    have hint2gen : ∀ (i : ι), Integrable
        (fun ω : ι → Bool => (fun b : Bool => ((d i b) ^ 2) • (B i) ^ 2) (ω i))
        (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩) :=
      fun i => MeasureTheory.integrable_comp_eval
        (μ := fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
        (f := fun b : Bool => ((d i b) ^ 2) • (B i) ^ 2)
        (ProbabilityTheory.integrable_bernoulliMeasure _ _ _ _)
    have hsq : ∀ (i : ι) (ω : ι → Bool),
        (Y i ω) ^ 2 = ((d i (ω i)) ^ 2) • (B i) ^ 2 := by
      intro i ω
      simp only [hYdef, pow_two, smul_mul_smul]
    have hint2 : ∀ i, Integrable (fun ω => (Y i ω) ^ 2)
        (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩) := by
      intro i
      have h1 : (fun ω : ι → Bool => (Y i ω) ^ 2)
          = (fun ω : ι → Bool => (fun b : Bool => ((d i b) ^ 2) • (B i) ^ 2) (ω i)) :=
        funext fun ω => hsq i ω
      rw [h1]
      exact hint2gen i
    have hmean : ∀ i, ∫ ω : ι → Bool,
          (fun b : Bool => (d i b) • B i) (ω i) ∂
          (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
          = 0 := by
      intro i
      rw [hintegral i (f := fun b : Bool => (d i b) • B i)]
      simp only [hddef, if_true, if_false, Bool.false_eq_true]
      by_cases hc : q i = 0
      · have hxi : x i = 0 := by
          rcases hcase i with ⟨hRx, hq1'⟩ | ⟨hRx, hq2'⟩
          · rw [hq1'] at hc; exact absurd hc (by norm_num)
          · rw [hq2'] at hc
            rcases (div_eq_zero_iff).mp hc with h | h
            · exact h
            · exact absurd h hR0.ne'
        have hBi : B i = 0 := by
          rw [hxdef] at hxi
          exact norm_eq_zero.mp hxi
        rw [hc, hBi]
        simp
      · have hqq : q i * (q i)⁻¹ = 1 := mul_inv_cancel₀ hc
        rw [smul_smul, smul_smul, ← add_smul]
        have hsc : q i * ((q i)⁻¹ - 1) + (1 - q i) * (-1) = 0 := by
          have h2 : q i * ((q i)⁻¹ - 1) = q i * (q i)⁻¹ - q i := by ring
          rw [h2, hqq]
          ring
        rw [hsc, zero_smul]
    have hherm : ∀ i, ∀ᵐ ω ∂
        (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩),
        (fun b : Bool => (d i b) • B i) (ω i) |>.IsHermitian :=
      fun i => Filter.Eventually.of_forall fun ω => hHermSM _ (hpsd i).1
    have hnorm : ∀ i, ∀ᵐ ω ∂
        (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩),
        ‖(fun b : Bool => (d i b) • B i) (ω i)‖ ≤ R := by
      intro i
      rcases hcase i with ⟨hRx, hq1'⟩ | ⟨hRx, hq2'⟩
      · have hnull : (Measure.pi fun j =>
            ProbabilityTheory.bernoulliMeasure true false ⟨q j, hBerIcc j⟩)
            {ω : ι → Bool | ω i = false} = 0 := by
          have h1 := MeasureTheory.MeasurePreserving.measure_preimage
            (MeasureTheory.measurePreserving_eval
              (fun j => ProbabilityTheory.bernoulliMeasure true false ⟨q j, hBerIcc j⟩) i)
            (MeasurableSet.singleton false |>.nullMeasurableSet)
          have h2 : (Measure.pi fun j =>
              ProbabilityTheory.bernoulliMeasure true false ⟨q j, hBerIcc j⟩)
              {ω : ι → Bool | ω i = false}
              = (Measure.pi fun j =>
                ProbabilityTheory.bernoulliMeasure true false ⟨q j, hBerIcc j⟩)
                (Function.eval i ⁻¹' ({false} : Set Bool)) := by
            congr 1
          rw [h2, h1]
          show (ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
              {false} = 0
          have hp1 : (⟨q i, hBerIcc i⟩ : Set.Icc (0 : ℝ) 1) = 1 := by
            refine Subtype.ext ?_
            simp only [Set.Icc.coe_one]
            exact hq1'
          rw [hp1, ProbabilityTheory.bernoulliMeasure_one,
            MeasureTheory.Measure.dirac_apply' true MeasurableSet.of_discrete,
            Set.indicator_of_notMem (by simp)]
        rw [MeasureTheory.ae_iff]
        refine MeasureTheory.measure_mono_null ?_ hnull
        intro ω hω
        have hω' : ¬ (‖(fun b : Bool => (d i b) • B i) (ω i)‖ ≤ R) := hω
        cases hb : ω i with
        | false => exact hb
        | true =>
            exfalso
            apply hω'
            rw [hb]
            simp only [hddef, hq1', if_true, inv_one, sub_self, zero_smul, norm_zero]
            exact hR0.le
      · refine Filter.Eventually.of_forall fun ω => ?_
        cases hb : ω i with
        | false =>
            simp only [hb, hddef, if_true, if_false, Bool.false_eq_true]
            have hxB : ‖B i‖ = x i := by simp only [hxdef]
            rw [norm_smul, hxB, norm_neg, norm_one, one_mul]
            exact hRx
        | true =>
            simp only [hb, hddef, if_true, if_false, Bool.false_eq_true]
            have hxB : ‖B i‖ = x i := by simp only [hxdef]
            have hkey : |x i * ((q i)⁻¹ - 1)| ≤ R := by
              by_cases hxz : x i = 0
              · rw [hxz, zero_mul]
                simpa using hR0.le
              · have hpos : 0 < x i := lt_of_le_of_ne (hx0 i) (Ne.symm hxz)
                have hqinv : (q i)⁻¹ = R / x i := by
                  rw [hq2', inv_div]
                have hmul : x i * ((q i)⁻¹ - 1) = R - x i := by
                  rw [hqinv]
                  field_simp
                rw [hmul, abs_of_nonneg (by linarith)]
                linarith
            rw [norm_smul, hxB, Real.norm_eq_abs]
            have hconv : |(q i)⁻¹ - 1| * x i = |x i * ((q i)⁻¹ - 1)| := by
              rw [abs_mul, abs_of_nonneg (hx0 i)]
              ring
            rw [hconv]
            exact hkey
    have hindep' : matrix_bernstein_independent
        (fun k : Fin (Fintype.card ι) =>
          Y ((Fintype.equivFin ι).symm k))
        (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩) := by
      unfold matrix_bernstein_independent
      have hindepY : iIndepFun (fun i (ω : ι → Bool) => (d i (ω i)) • B i)
          (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩) :=
        ProbabilityTheory.iIndepFun_pi (fun i => (hfm i).aemeasurable)
      exact hindepY.precomp (Fintype.equivFin ι).symm.injective
    have hIso : IsometricContinuousFunctionalCalculus ℝ (real_square_matrix n)
        IsSelfAdjoint := Matrix.instIsometricContinuousFunctionalCalculus
    have hnormLe : ∀ (M : real_square_matrix n), M.IsHermitian →
        M ≤ ‖M‖ • (1 : real_square_matrix n) := by
      intro M hM
      have hsa : IsSelfAdjoint M := (Matrix.isHermitian_iff_isSelfAdjoint).mpr hM
      have h1 := le_algebraMap_of_spectrum_le (R := ℝ) (r := ‖M‖)
        (fun x hx => Real.le_norm_self x |>.trans
          (IsometricContinuousFunctionalCalculus.norm_spectrum_le M hx)) hsa
      rwa [Algebra.algebraMap_eq_smul_one] at h1
    have hleNorm : ∀ (M : real_square_matrix n) (c : ℝ), M.PosSemidef → 0 ≤ c →
        M ≤ c • (1 : real_square_matrix n) → ‖M‖ ≤ c := by
      intro M c hM hc0 hle
      have hsa : IsSelfAdjoint M := (Matrix.isHermitian_iff_isSelfAdjoint).mpr hM.1
      have hnn : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM
      have hs0 : ∀ x ∈ spectrum ℝ M, 0 ≤ x :=
        (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) M hsa).mp hnn
      have hsc : ∀ x ∈ spectrum ℝ M, x ≤ c := by
        have h1 : M ≤ algebraMap ℝ (real_square_matrix n) c := by
          rw [Algebra.algebraMap_eq_smul_one]
          exact hle
        exact (le_algebraMap_iff_spectrum_le (R := ℝ) (r := c) hsa).mp h1
      have h2 := norm_cfc_le (𝕜 := ℝ) (f := id) (a := M) (c := c) hc0
        (fun x hx => by
          have hx0 : 0 ≤ x := hs0 x hx
          show |x| ≤ c
          rw [abs_of_nonneg hx0]
          exact hsc x hx)
      rwa [cfc_id ℝ M hsa] at h2
    have hsmul_mono : ∀ (c c' : ℝ) (M : real_square_matrix n), c ≤ c' → M.PosSemidef →
        c • M ≤ c' • M := by
      intro c c' M hcc hM
      rw [Matrix.le_iff, ← sub_smul]
      exact hM.smul (by linarith)
    have hsmul_mono_left : ∀ (c : ℝ) (X Y : real_square_matrix n), 0 ≤ c → X ≤ Y →
        c • X ≤ c • Y := by
      intro c X Y hc h
      have h' : (Y - X).PosSemidef := Matrix.le_iff.mp h
      rw [Matrix.le_iff, ← smul_sub]
      exact h'.smul hc
    have hsum_le : ∀ (f g : ι → real_square_matrix n), (∀ i, f i ≤ g i) →
        (∑ i, f i) ≤ (∑ i, g i) := by
      intro f g hfg
      rw [Matrix.le_iff, ← Finset.sum_sub_distrib]
      exact Finset.sum_induction _ _ (fun _ _ h1 h2 => h1.add h2) Matrix.PosSemidef.zero
        (fun i _ => Matrix.le_iff.mp (hfg i))
    have hBsq : ∀ i, (B i) ^ 2 ≤ x i • B i := by
      intro i
      have hBnn : (0 : real_square_matrix n) ≤ B i :=
        Matrix.nonneg_iff_posSemidef.mpr (hpsd i)
      have hsnn : (0 : real_square_matrix n) ≤ CFC.sqrt (B i) := CFC.sqrt_nonneg _
      have hspsd : (CFC.sqrt (B i)).PosSemidef := Matrix.nonneg_iff_posSemidef.mp hsnn
      have hst : (CFC.sqrt (B i)).transpose = CFC.sqrt (B i) := by
        have h := hspsd.1.eq
        rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
      have hss : CFC.sqrt (B i) * CFC.sqrt (B i) = B i :=
        CFC.sqrt_mul_sqrt_self _ hBnn
      have hBle : B i ≤ x i • (1 : real_square_matrix n) := by
        rw [← hxdef] at *
        exact hnormLe (B i) (hpsd i).1
      have hdiff : (x i • (1 : real_square_matrix n) - B i).PosSemidef :=
        Matrix.le_iff.mp hBle
      have hpsd_s : (CFC.sqrt (B i) * (x i • (1 : real_square_matrix n) - B i)
          * CFC.sqrt (B i)).PosSemidef := by
        have h := hdiff.conjTranspose_mul_mul_same (CFC.sqrt (B i))
        rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hst] at h
      have hkey : x i • B i - (B i) ^ 2
          = CFC.sqrt (B i) * (x i • (1 : real_square_matrix n) - B i) * CFC.sqrt (B i) := by
        have h1 : CFC.sqrt (B i) * (x i • (1 : real_square_matrix n)) * CFC.sqrt (B i)
            = x i • B i := by
          rw [mul_smul_comm, smul_mul_assoc, Matrix.mul_one, hss]
        have h2 : CFC.sqrt (B i) * B i * CFC.sqrt (B i) = (B i) ^ 2 := by
          rw [pow_two]
          calc CFC.sqrt (B i) * B i * CFC.sqrt (B i)
              = CFC.sqrt (B i) * (CFC.sqrt (B i) * CFC.sqrt (B i)) * CFC.sqrt (B i) := by rw [hss]
            _ = (CFC.sqrt (B i) * CFC.sqrt (B i)) * (CFC.sqrt (B i) * CFC.sqrt (B i)) := by
                noncomm_ring
            _ = B i * B i := by rw [hss]
        rw [← h1, ← h2, Matrix.mul_sub, Matrix.sub_mul]
      rw [Matrix.le_iff, hkey]
      exact hpsd_s
    have hvar : ∀ i, ∫ ω : ι → Bool, (Y i ω) ^ 2 ∂
        (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
        = ((q i) * ((q i)⁻¹ - 1) ^ 2 + (1 - q i)) • (B i) ^ 2 := by
      intro i
      have h1 : (fun ω : ι → Bool => (Y i ω) ^ 2)
          = (fun ω : ι → Bool => (fun b : Bool => ((d i b) ^ 2) • (B i) ^ 2) (ω i)) :=
        funext fun ω => hsq i ω
      rw [h1]
      rw [hintegral i (f := fun b : Bool => ((d i b) ^ 2) • (B i) ^ 2)]
      simp only [hddef, if_true, if_false, Bool.false_eq_true]
      rw [smul_smul, smul_smul, ← add_smul]
      congr 1
      ring
    have hmx : ∀ i, ((q i) * ((q i)⁻¹ - 1) ^ 2 + (1 - q i)) * x i ≤ R := by
      intro i
      rcases hcase i with ⟨hRx, hq1'⟩ | ⟨hRx, hq2'⟩
      · simp only [hq1', inv_one, sub_self, one_pow]
        norm_num
        exact hR0.le
      · by_cases hxz : x i = 0
        · have hq0' : q i = 0 := by rw [hq2', hxz, zero_div]
          rw [hq0', hxz]
          simp
          exact hR0.le
        · have hpos : 0 < x i := lt_of_le_of_ne (hx0 i) (Ne.symm hxz)
          have hc0 : 0 < q i := by rw [hq2']; exact div_pos hpos hR0
          have hqq : q i * (q i)⁻¹ = 1 := mul_inv_cancel₀ hc0.ne'
          have hmq : (q i * ((q i)⁻¹ - 1) ^ 2 + (1 - q i)) * q i = 1 - q i := by
            have hu : q i * ((q i)⁻¹ - 1) = 1 - q i := by
              rw [mul_sub, hqq, mul_one]
            have h1 : q i * q i * ((q i)⁻¹ - 1) ^ 2 = (1 - q i) ^ 2 := by
              calc q i * q i * ((q i)⁻¹ - 1) ^ 2
                  = (q i * ((q i)⁻¹ - 1)) ^ 2 := by ring
                _ = (1 - q i) ^ 2 := by rw [hu]
            have hexp : (q i * ((q i)⁻¹ - 1) ^ 2 + (1 - q i)) * q i
                = q i * q i * ((q i)⁻¹ - 1) ^ 2 + (1 - q i) * q i := by ring
            rw [hexp, h1]
            ring
          have hxq : x i = q i * R := by rw [hq2']; field_simp
          rw [hxq, ← mul_assoc, hmq]
          simpa using mul_le_mul_of_nonneg_right (sub_le_self 1 (hq0 i)) hR0.le
    have hvarle : ∀ i, ((q i) * ((q i)⁻¹ - 1) ^ 2 + (1 - q i)) • (B i) ^ 2
        ≤ R • B i := by
      intro i
      have hm0 : 0 ≤ (q i) * ((q i)⁻¹ - 1) ^ 2 + (1 - q i) :=
        add_nonneg (mul_nonneg (hq0 i) (sq_nonneg _)) (sub_nonneg.mpr (hq1 i))
      have h1 := hsmul_mono_left ((q i) * ((q i)⁻¹ - 1) ^ 2 + (1 - q i))
        ((B i) ^ 2) (x i • B i) hm0 (hBsq i)
      rw [smul_smul] at h1
      exact h1.trans (hsmul_mono _ _ _ (hmx i) (hpsd i))
    have hVpsd : (∑ i, ((q i) * ((q i)⁻¹ - 1) ^ 2 + (1 - q i)) • (B i) ^ 2).PosSemidef :=
      Finset.sum_induction _ _ (fun _ _ h1 h2 => h1.add h2) Matrix.PosSemidef.zero
        (fun i _ => ((hpsd i).pow 2).smul
          (add_nonneg (mul_nonneg (hq0 i) (sq_nonneg _)) (sub_nonneg.mpr (hq1 i))))
    have hVle : (∑ i, ((q i) * ((q i)⁻¹ - 1) ^ 2 + (1 - q i)) • (B i) ^ 2)
        ≤ R • (1 : real_square_matrix n) := by
      have h1 := hsum_le (fun i => ((q i) * ((q i)⁻¹ - 1) ^ 2 + (1 - q i)) • (B i) ^ 2)
        (fun i => R • B i) (fun i => hvarle i)
      rw [← Finset.smul_sum, hsum] at h1
      exact h1
    have hsumreindex : ∑ k : Fin (Fintype.card ι),
        ∫ ω : ι → Bool, (Y ((Fintype.equivFin ι).symm k) ω) ^ 2 ∂
        (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
        = ∑ i, ((q i) * ((q i)⁻¹ - 1) ^ 2 + (1 - q i)) • (B i) ^ 2 :=
      Fintype.sum_equiv ((Fintype.equivFin ι).symm) _ _
        (fun k => hvar ((Fintype.equivFin ι).symm k))
    have hproxy : matrix_bernstein_variance_proxy
        (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
        (fun k : Fin (Fintype.card ι) => Y ((Fintype.equivFin ι).symm k)) ≤ R := by
      unfold matrix_bernstein_variance_proxy matrix_bernstein_variance_matrix
      show ‖∑ k : Fin (Fintype.card ι), ∫ ω : ι → Bool,
          (Y ((Fintype.equivFin ι).symm k) ω) ^ 2 ∂
          (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)‖ ≤ R
      rw [hsumreindex]
      exact hleNorm _ R hVpsd hR0.le hVle
    have hMB := matrix_bernstein_inequality
      (fun k : Fin (Fintype.card ι) => Y ((Fintype.equivFin ι).symm k))
      (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
      R hn hindep' (fun k => hint1 ((Fintype.equivFin ι).symm k))
      (fun k => hint2 ((Fintype.equivFin ι).symm k))
      (fun k => hmean ((Fintype.equivFin ι).symm k))
      (fun k => hherm ((Fintype.equivFin ι).symm k))
      (fun k => hnorm ((Fintype.equivFin ι).symm k)) ε hε0.le
    have hsumYF : ∀ ω : ι → Bool,
        matrix_bernstein_sum (fun k : Fin (Fintype.card ι) =>
          Y ((Fintype.equivFin ι).symm k)) ω = ∑ i, Y i ω := by
      intro ω
      unfold matrix_bernstein_sum
      exact Fintype.sum_equiv (Fintype.equivFin ι).symm _ _ (fun k => rfl)
    have hnum : ε ^ 2 / 2 = 8 * Real.log (4 * (n : ℝ)) * R := by
      rw [hRdef]
      field_simp
      norm_num
    have hge : 6 * Real.log (4 * (n : ℝ)) ≤ ε ^ 2 / 2 / (R + R * ε / 3) := by
      rw [hnum]
      have hfac : R + R * ε / 3 = R * (1 + ε / 3) := by ring
      rw [hfac]
      have hrw : 8 * Real.log (4 * (n : ℝ)) * R / (R * (1 + ε / 3))
          = 8 * Real.log (4 * (n : ℝ)) / (1 + ε / 3) := by field_simp
      rw [hrw, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + ε / 3)]
      nlinarith [hε1, hlog]
    have hexpmono : Real.exp (-(ε ^ 2 / 2) / (matrix_bernstein_variance_proxy
        (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
        (fun k : Fin (Fintype.card ι) => Y ((Fintype.equivFin ι).symm k)) + R * ε / 3))
        ≤ Real.exp (-(6 * Real.log (4 * (n : ℝ)))) := by
      refine Real.exp_le_exp.mpr ?_
      rw [neg_div]
      have hden1 : 0 < matrix_bernstein_variance_proxy
          (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
          (fun k : Fin (Fintype.card ι) => Y ((Fintype.equivFin ι).symm k)) + R * ε / 3 := by
        have h2 : 0 ≤ matrix_bernstein_variance_proxy
            (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
            (fun k : Fin (Fintype.card ι) => Y ((Fintype.equivFin ι).symm k)) := norm_nonneg _
        have h3 : 0 < R * ε / 3 := by positivity
        linarith
      have hden2 : 0 < R + R * ε / 3 := by positivity
      have hfrac : ε ^ 2 / 2 / (R + R * ε / 3)
          ≤ ε ^ 2 / 2 / (matrix_bernstein_variance_proxy
            (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
            (fun k : Fin (Fintype.card ι) => Y ((Fintype.equivFin ι).symm k)) + R * ε / 3) := by
        rw [div_le_div_iff₀ hden2 hden1]
        exact mul_le_mul_of_nonneg_left (by linarith [hproxy]) (by positivity)
      exact neg_le_neg (le_trans hge hfrac)
    have hexpval : Real.exp (-(6 * Real.log (4 * (n : ℝ)))) = ((4 * (n : ℝ)) ^ 6)⁻¹ := by
      have h4n : (0 : ℝ) < 4 * (n : ℝ) := by linarith
      have hpos6 : (0 : ℝ) < ((4 * (n : ℝ))⁻¹) ^ 6 := pow_pos (inv_pos.2 h4n) 6
      have hlogpow : Real.log (((4 * (n : ℝ))⁻¹) ^ 6) = -(6 * Real.log (4 * (n : ℝ))) := by
        rw [Real.log_pow, Real.log_inv]
        ring
      rw [← hlogpow, Real.exp_log hpos6, inv_pow]
    have htail : matrix_bernstein_tail_bound n (matrix_bernstein_variance_proxy
        (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
        (fun k : Fin (Fintype.card ι) => Y ((Fintype.equivFin ι).symm k))) R ε ≤ 1 / 4 := by
      have hn5 : (1 : ℝ) ≤ (n : ℝ) ^ 5 := by exact_mod_cast Nat.one_le_pow 5 n (by omega)
      have h8 : (8 : ℝ) * (n : ℝ) ≤ (4 * (n : ℝ)) ^ 6 := by
        have hc : (4 * (n : ℝ)) ^ 6 = 4096 * (n : ℝ) * (n : ℝ) ^ 5 := by ring
        rw [hc]
        nlinarith [hn5, hnR]
      have hinv : (((4 * (n : ℝ)) ^ 6)⁻¹) ≤ ((8 * (n : ℝ))⁻¹) :=
        inv_anti₀ (by linarith) h8
      unfold matrix_bernstein_tail_bound
      calc 2 * (n : ℝ) * Real.exp (-(ε ^ 2 / 2) / (matrix_bernstein_variance_proxy
            (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
            (fun k : Fin (Fintype.card ι) => Y ((Fintype.equivFin ι).symm k)) + R * ε / 3))
          ≤ 2 * (n : ℝ) * Real.exp (-(6 * Real.log (4 * (n : ℝ)))) :=
            mul_le_mul_of_nonneg_left hexpmono (by positivity)
        _ = 2 * (n : ℝ) * (((4 * (n : ℝ)) ^ 6)⁻¹) := by rw [hexpval]
        _ ≤ 2 * (n : ℝ) * ((8 * (n : ℝ))⁻¹) :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 1 / 4 := by
          field_simp
          norm_num
    have hE1 : (Measure.pi (fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
        {ω : ι → Bool | ε ≤ ‖∑ i, Y i ω‖}).toReal ≤ 1 / 4 := by
      have hset : {ω : ι → Bool | ε ≤ ‖∑ i, Y i ω‖}
          = {ω : ι → Bool | ‖matrix_bernstein_sum (fun k : Fin (Fintype.card ι) =>
              Y ((Fintype.equivFin ι).symm k)) ω‖ ≥ ε} := by
        ext ω
        simp only [Set.mem_setOf_eq, ge_iff_le]
        rw [hsumYF ω]
      rw [hset]
      exact le_trans hMB htail
    set Zr : (ι → Bool) → ℝ := fun ω => ∑ i, (if ω i then (1 : ℝ) else 0) with hZrdef
    have hZcoord : ∀ (i : ι) (f : Bool → ℝ),
        ∫ ω : ι → Bool, f (ω i) ∂
          (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
          = (q i) * f true + (1 - q i) * f false := by
      intro i f
      have hae2 : AEStronglyMeasurable f
          (ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩) :=
        ⟨fun b => if b then f true else f false, StronglyMeasurable.of_discrete, by
          refine Filter.Eventually.of_forall fun b => ?_
          cases b <;> rfl⟩
      rw [MeasureTheory.integral_comp_eval
        (μ := fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
        (i := i) (f := f) hae2]
      rw [ProbabilityTheory.integral_bernoulliMeasure true false ⟨q i, hBerIcc i⟩ f]
      simp
    have hZint : Integrable Zr
        (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩) := by
      rw [hZrdef]
      exact MeasureTheory.integrable_finsetSum _ (fun i _ => integrable_comp_eval
        (μ := fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
        (i := i) (f := fun b => if b = true then (1 : ℝ) else 0)
        (ProbabilityTheory.integrable_bernoulliMeasure true false ⟨q i, hBerIcc i⟩
          (fun b => if b = true then (1 : ℝ) else 0)))
    have hZmean : ∫ ω : ι → Bool, Zr ω ∂
        (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
        = ∑ i, q i := by
      simp only [hZrdef]
      rw [MeasureTheory.integral_finsetSum _ (fun i _ => integrable_comp_eval
        (μ := fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
        (i := i) (f := fun b => if b = true then (1 : ℝ) else 0)
        (ProbabilityTheory.integrable_bernoulliMeasure true false ⟨q i, hBerIcc i⟩
          (fun b => if b = true then (1 : ℝ) else 0)))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hZcoord i (fun b => if b = true then (1 : ℝ) else 0)]
      simp
    have hZmeas : Measurable Zr := by
      rw [hZrdef]
      have hgen : ∀ (s : Finset ι), Measurable
          (fun ω : ι → Bool => ∑ i ∈ s, (if ω i = true then (1 : ℝ) else 0)) := by
        intro s
        induction s using Finset.induction_on with
        | empty => exact measurable_const
        | insert i s hi ih =>
            simp only [Finset.sum_insert hi]
            have hf : Measurable (fun ω : ι → Bool => ω i) := measurable_pi_apply i
            have hg : Measurable (fun b : Bool => if b = true then (1 : ℝ) else 0) :=
              Measurable.of_discrete
            exact (hg.comp hf).add ih
      exact hgen Finset.univ
    have hZnmeas : AEMeasurable (fun ω => (↑(Zr ω).toNNReal : ENNReal))
        (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩) :=
      (hZmeas.real_toNNReal).coe_nnreal_ennreal.aemeasurable
    have hZnn : ∀ ω : ι → Bool, 0 ≤ Zr ω := by
      intro ω
      rw [hZrdef]
      exact Finset.sum_nonneg fun i _ => by cases h : ω i <;> simp [h]
    have hmarkov : (Measure.pi (fun i =>
          ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
          {ω : ι → Bool | 4 * (∑ i, q i) ≤ Zr ω}) ≤ ENNReal.ofReal (1 / 4) := by
      have hlint : ∫⁻ ω, ((Zr ω).toNNReal : ENNReal) ∂
          (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
          = ENNReal.ofReal (∑ i, q i) := by
        have hint : Integrable (fun ω => ((Zr ω).toNNReal : ℝ))
            (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩) := by
          refine hZint.congr (Filter.Eventually.of_forall fun ω => ?_)
          exact (Real.coe_toNNReal (Zr ω) (hZnn ω)).symm
        rw [MeasureTheory.lintegral_coe_eq_integral _ hint]
        have hcongr : ∫ ω, ((Zr ω).toNNReal : ℝ) ∂
            (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
            = ∑ i, q i := by
          refine (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)).trans hZmean
          exact Real.coe_toNNReal (Zr ω) (hZnn ω)
        rw [hcongr]
      have h4pos : ENNReal.ofReal (4 * ∑ i, q i) ≠ 0 := by
        rw [ENNReal.ofReal_ne_zero_iff]
        linarith
      have hmark := MeasureTheory.meas_ge_le_lintegral_div
        (f := fun ω => ((Zr ω).toNNReal : ENNReal)) hZnmeas h4pos ENNReal.ofReal_ne_top
      have hsetsub : {ω : ι → Bool | 4 * (∑ i, q i) ≤ Zr ω}
          ⊆ {ω : ι → Bool | ENNReal.ofReal (4 * ∑ i, q i) ≤ ((Zr ω).toNNReal : ENNReal)} := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        exact ENNReal.ofReal_le_ofReal hω
      have hrw : ENNReal.ofReal (∑ i, q i) / ENNReal.ofReal (4 * ∑ i, q i)
          = ENNReal.ofReal (1 / 4) := by
        rw [← ENNReal.ofReal_div_of_pos (by linarith : (0 : ℝ) < 4 * ∑ i, q i)]
        congr 1
        field_simp
      refine le_trans (MeasureTheory.measure_mono hsetsub) ?_
      rw [hlint] at hmark
      rw [hrw] at hmark
      exact hmark
    have hgood : ∃ ω : ι → Bool, ‖∑ i, Y i ω‖ < ε ∧ Zr ω ≤ 4 * ∑ i, q i := by
      by_contra hcon
      have hcon' : ∀ ω : ι → Bool, ‖∑ i, Y i ω‖ < ε → 4 * ∑ i, q i < Zr ω :=
        fun ω hP => not_le.mp (fun hQ => hcon ⟨ω, hP, hQ⟩)
      have hcover : (Set.univ : Set (ι → Bool))
          ⊆ {ω : ι → Bool | ε ≤ ‖∑ i, Y i ω‖} ∪ {ω : ι → Bool | 4 * ∑ i, q i < Zr ω} := by
        intro ω _
        rcases le_or_gt ε (‖∑ i, Y i ω‖) with h | h
        · exact Or.inl h
        · exact Or.inr (hcon' ω h)
      have hmono : (Measure.pi (fun i =>
            ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩))
          (Set.univ : Set (ι → Bool))
          ≤ (Measure.pi (fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩))
            ({ω : ι → Bool | ε ≤ ‖∑ i, Y i ω‖} ∪ {ω : ι → Bool | 4 * ∑ i, q i < Zr ω}) :=
        MeasureTheory.measure_mono hcover
      have hunion : (Measure.pi (fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩))
          ({ω : ι → Bool | ε ≤ ‖∑ i, Y i ω‖} ∪ {ω : ι → Bool | 4 * ∑ i, q i < Zr ω})
          ≤ (Measure.pi (fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩))
              {ω : ι → Bool | ε ≤ ‖∑ i, Y i ω‖}
            + (Measure.pi (fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩))
              {ω : ι → Bool | 4 * ∑ i, q i < Zr ω} :=
        MeasureTheory.measure_union_le _ _
      have hsub2 : {ω : ι → Bool | 4 * ∑ i, q i < Zr ω} ⊆ {ω : ι → Bool | 4 * ∑ i, q i ≤ Zr ω} := by
        intro ω h
        simp only [Set.mem_setOf_eq] at h ⊢
        exact le_of_lt h
      have hE2lt : (Measure.pi (fun i =>
            ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩))
            {ω : ι → Bool | 4 * ∑ i, q i < Zr ω}
          ≤ ENNReal.ofReal (1 / 4) :=
        le_trans (MeasureTheory.measure_mono hsub2) hmarkov
      have hE1enn : (Measure.pi (fun i =>
            ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩))
            {ω : ι → Bool | ε ≤ ‖∑ i, Y i ω‖}
          ≤ ENNReal.ofReal (1 / 4) := by
        rw [← ENNReal.ofReal_toReal
          ((MeasureTheory.measure_lt_top
            (Measure.pi fun i => ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩)
            {ω : ι → Bool | ε ≤ ‖∑ i, Y i ω‖}).ne)]
        exact ENNReal.ofReal_le_ofReal hE1
      have huniv : (Measure.pi (fun i =>
            ProbabilityTheory.bernoulliMeasure true false ⟨q i, hBerIcc i⟩))
            (Set.univ : Set (ι → Bool)) = 1 := by simp
      rw [huniv] at hmono
      have hchain : (1 : ENNReal) ≤ ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) :=
        le_trans (le_trans hmono hunion) (add_le_add hE1enn hE2lt)
      have hsum2 : ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4)
          = ENNReal.ofReal (1 / 2) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
      rw [hsum2] at hchain
      have hone : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := ENNReal.ofReal_one.symm
      rw [hone] at hchain
      rw [ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hchain
      exact absurd hchain (by norm_num)
    obtain ⟨ωstar, hωA, hωB⟩ := hgood
    have hνnn : ∀ i, 0 ≤ (if ωstar i then (q i)⁻¹ else 0 : ℝ) := by
      intro i
      cases hb : ωstar i
      · simp [hb]
      · simp [hb, inv_nonneg.mpr (hq0 i)]
    set ν : ι → NNReal := fun i => ⟨if ωstar i then (q i)⁻¹ else 0, hνnn i⟩ with hνdef
    have hνval : ∀ i, (ν i : ℝ) = if ωstar i then (q i)⁻¹ else 0 := fun i => rfl
    have hWherm : (∑ i, Y i ωstar).IsHermitian := by
      refine Finset.sum_induction _ _ (fun _ _ h1 h2 => h1.add h2)
        Matrix.isHermitian_zero ?_
      intro i _
      exact hHermSM _ (hpsd i).1
    have hWle : (∑ i, Y i ωstar) ≤ ε • (1 : real_square_matrix n) := by
      have h1 := hnormLe _ hWherm
      exact le_trans h1 (hsmul_mono _ _ _ hωA.le Matrix.PosSemidef.one)
    have hnegWle : (-(∑ i, Y i ωstar)) ≤ ε • (1 : real_square_matrix n) := by
      have h1 := hnormLe _ hWherm.neg
      rw [norm_neg] at h1
      exact le_trans h1 (hsmul_mono _ _ _ hωA.le Matrix.PosSemidef.one)
    have hX : ∀ i, (ν i : ℝ) • B i = Y i ωstar + B i := by
      intro i
      rw [hνval i]
      have hYval : Y i ωstar = (d i (ωstar i)) • B i := rfl
      rw [hYval]
      cases hb : ωstar i
      · simp [hb, hddef]
      · simp only [hb, hddef]
        have h2 : (((q i)⁻¹ - 1) + 1) • B i = ((q i)⁻¹ - 1) • B i + (1 : ℝ) • B i :=
          add_smul ((q i)⁻¹ - 1) 1 (B i)
        rw [sub_add_cancel, one_smul] at h2
        exact h2
    refine ⟨ν, ?_, ?_, ?_⟩
    · rw [Finset.sum_congr rfl (fun i _ => hX i), Finset.sum_add_distrib, hsum]
      rw [Matrix.le_iff]
      have hconv : ((∑ i, Y i ωstar) + 1) - (1 - ε) • (1 : real_square_matrix n)
          = ε • (1 : real_square_matrix n) + (∑ i, Y i ωstar) := by
        simp only [sub_smul, one_smul, add_smul]
        abel
      rw [hconv]
      have h2 := Matrix.le_iff.mp hnegWle
      rwa [sub_neg_eq_add] at h2
    · rw [Finset.sum_congr rfl (fun i _ => hX i), Finset.sum_add_distrib, hsum]
      rw [Matrix.le_iff]
      have hconv : ((1 + ε) • (1 : real_square_matrix n)) - ((∑ i, Y i ωstar) + 1)
          = ε • (1 : real_square_matrix n) - (∑ i, Y i ωstar) := by
        simp only [add_smul, one_smul]
        abel
      rw [hconv]
      exact Matrix.le_iff.mp hWle
    · have hνzero : ∀ i, ωstar i = false → ν i = 0 := by
        intro i hb
        apply Subtype.ext
        rw [hνdef]
        simp [hb]
      have hsubf : (Finset.univ.filter fun i => ν i ≠ 0)
          ⊆ Finset.univ.filter (fun i => ωstar i = true) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        cases hb : ωstar i
        · exact absurd (hνzero i hb) hi
        · rfl
      have hcardZ : ((Finset.univ.filter (fun i => ωstar i = true)).card : ℝ) = Zr ωstar := by
        rw [hZrdef]
        have hcards : ((Finset.univ.filter (fun i => ωstar i = true)).card : ℝ)
            = ∑ i ∈ Finset.univ.filter (fun i => ωstar i = true), (1 : ℝ) := by
          rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
        rw [hcards, Finset.sum_filter]
      have hcard1 : (weight_support_cardinality ν : ℝ)
          ≤ ((Finset.univ.filter (fun i => ωstar i = true)).card : ℝ) := by
        have h1 : weight_support_cardinality ν
            = (Finset.univ.filter fun i => ν i ≠ 0).card := rfl
        rw [h1]
        exact_mod_cast Finset.card_le_card hsubf
      have hqsumle : ∑ i, q i ≤ ∑ i, x i / R :=
        Finset.sum_le_sum fun i _ => hqle i
      have hXR : 4 / R = 64 * Real.log (4 * (n : ℝ)) / ε ^ 2 := by
        rw [hRdef]
        field_simp
        norm_num
      calc (weight_support_cardinality ν : ℝ)
          ≤ ((Finset.univ.filter (fun i => ωstar i = true)).card : ℝ) := hcard1
        _ = Zr ωstar := hcardZ
        _ ≤ 4 * ∑ i, q i := hωB
        _ ≤ 4 * (∑ i, x i / R) := by
            exact mul_le_mul_of_nonneg_left hqsumle (by norm_num)
        _ = (4 / R) * (∑ i, x i) := by
            rw [← Finset.sum_div]
            ring
        _ = 64 * Real.log (4 * (n : ℝ)) * (∑ i, ‖B i‖) / ε ^ 2 := by
            rw [hXR, hxdef]
            ring
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    haveI hsub : Subsingleton (real_square_matrix 0) :=
      ⟨fun x y => by ext p q; exact absurd p.isLt (Nat.not_lt_zero _)⟩
    have hz : ∀ M : real_square_matrix 0, M = 0 := fun M => Subsingleton.elim M 0
    have hsum0 : ∑ i, ‖normalized_matrix (matrix_family_sum A) (A i)‖ = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hz (normalized_matrix (matrix_family_sum A) (A i)), norm_zero]
    refine ⟨fun _ => 0, ⟨?_, ?_⟩, ?_⟩
    · exact le_of_eq (Subsingleton.elim _ _)
    · exact le_of_eq (Subsingleton.elim _ _)
    · have h0 : weight_support_cardinality (fun _ : ι => 0) = 0 := by
        simp [weight_support_cardinality]
      rw [h0, hsum0]
      simp
  · have hSpsd : (matrix_family_sum A).PosSemidef := by
      unfold matrix_family_sum
      exact Finset.sum_induction _ _ (fun _ _ h1 h2 => h1.add h2)
        Matrix.PosSemidef.zero (fun i _ => hpsd i)
    have hSnn : (0 : real_square_matrix n) ≤ matrix_family_sum A :=
      Matrix.nonneg_iff_posSemidef.mpr hSpsd
    set Q : real_square_matrix n := CFC.sqrt (matrix_family_sum A) with hQdef
    have hQnn : (0 : real_square_matrix n) ≤ Q := CFC.sqrt_nonneg _
    have hQpsd : Q.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hQnn
    have hQt : Q.transpose = Q := by
      have h := hQpsd.1.eq
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    have hQQ : Q * Q = matrix_family_sum A := CFC.sqrt_mul_sqrt_self _ hSnn
    have hQunit : IsUnit Q :=
      (CFC.isUnit_sqrt_iff (matrix_family_sum A) hSnn).mpr hunit
    have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det _).mp hQunit
    have hQinv1 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hdet
    have hQinv2 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
    have hTt : (Q⁻¹).transpose = Q⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, hQt]
    set B : ι → real_square_matrix n :=
      fun i => normalized_matrix (matrix_family_sum A) (A i) with hBdef
    have hBpsd : ∀ i, (B i).PosSemidef := by
      intro i
      have h := (hpsd i).conjTranspose_mul_mul_same (Q⁻¹)
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, hTt] at h
      exact h
    have hBsum : (∑ i, B i) = 1 := by
      have h0 : ∀ i, B i = Q⁻¹ * A i * Q⁻¹ := fun i => rfl
      simp only [h0]
      rw [← Matrix.sum_mul, ← Matrix.mul_sum]
      have hS : ∑ i, A i = Q * Q := hQQ.symm
      rw [hS]
      calc Q⁻¹ * (Q * Q) * Q⁻¹ = (Q⁻¹ * Q) * (Q * Q⁻¹) := by simp [Matrix.mul_assoc]
        _ = 1 := by rw [hQinv1, hQinv2, Matrix.mul_one]
    obtain ⟨ν, hlo, hhi, hcard⟩ := hcore B ε hBpsd hBsum hε0 hε1 hn
    have hWB : ∑ i, (ν i : ℝ) • B i = Q⁻¹ * weighted_matrix_family_sum A ν * Q⁻¹ := by
      have h0 : ∀ i, (ν i : ℝ) • B i = Q⁻¹ * ((ν i : ℝ) • A i) * Q⁻¹ := by
        intro i
        have hBi : B i = Q⁻¹ * A i * Q⁻¹ := rfl
        rw [hBi, Matrix.mul_smul, Matrix.smul_mul]
      simp only [h0, weighted_matrix_family_sum, Matrix.mul_sum, Matrix.sum_mul]
    have hmonoQ : ∀ X Y : real_square_matrix n, X ≤ Y → Q * X * Q ≤ Q * Y * Q := by
      intro X Y hXY
      have h1 : (Y - X).PosSemidef := Matrix.le_iff.mp hXY
      have h2 : (Q * (Y - X) * Q).PosSemidef := by
        have h := h1.mul_mul_conjTranspose_same Q
        rw [Matrix.conjTranspose_eq_transpose_of_trivial, hQt] at h
        exact h
      rw [Matrix.le_iff]
      have h3 : Q * Y * Q - Q * X * Q = Q * (Y - X) * Q := by
        simp [Matrix.mul_sub, Matrix.sub_mul]
      rw [h3]
      exact h2
    refine ⟨ν, ⟨?_, ?_⟩, ?_⟩
    · have h := hmonoQ _ _ hlo
      have hL : Q * ((1 - ε) • (1 : real_square_matrix n)) * Q
          = (1 - ε) • matrix_family_sum A := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQQ]
      have hR : Q * (Q⁻¹ * weighted_matrix_family_sum A ν * Q⁻¹) * Q
          = weighted_matrix_family_sum A ν := by
        simp only [Matrix.mul_assoc]
        rw [hQinv1, Matrix.mul_one, ← Matrix.mul_assoc, hQinv2, Matrix.one_mul]
      rw [hWB] at h
      rwa [hL, hR] at h
    · have h := hmonoQ _ _ hhi
      have hL : Q * ((1 + ε) • (1 : real_square_matrix n)) * Q
          = (1 + ε) • matrix_family_sum A := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQQ]
      have hR : Q * (Q⁻¹ * weighted_matrix_family_sum A ν * Q⁻¹) * Q
          = weighted_matrix_family_sum A ν := by
        simp only [Matrix.mul_assoc]
        rw [hQinv1, Matrix.mul_one, ← Matrix.mul_assoc, hQinv2, Matrix.one_mul]
      rw [hWB] at h
      rwa [hL, hR] at h
    · have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
      have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
        have h2le : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp 1
          linarith
        have h12 : Real.log 2 ≤ 1 := by
          rw [Real.log_le_iff_le_exp (by norm_num)]
          exact h2le
        have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
          rw [show ((4 : ℝ)) = (2 : ℝ) ^ 2 from by norm_num, Real.log_pow]
          norm_num
        rw [h4]
        nlinarith
      have hlog4n : Real.log (4 * (n : ℝ)) ≤ 2 * (1 + Real.log (n : ℝ)) := by
        have hnne : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
        have h1 : Real.log (4 * (n : ℝ)) = Real.log 4 + Real.log (n : ℝ) := by
          rw [Real.log_mul (by norm_num) (ne_of_gt hnne)]
        rw [h1]
        nlinarith
      have hN0 : (0:ℝ) ≤ ∑ i, ‖B i‖ :=
        Finset.sum_nonneg fun i _ => norm_nonneg _
      have hinv0 : (0:ℝ) ≤ (ε ^ 2)⁻¹ := by positivity
      have hstep1 : 64 * Real.log (4 * (n : ℝ)) * (∑ i, ‖B i‖)
          ≤ 128 * (1 + Real.log (n : ℝ)) * (∑ i, ‖B i‖) := by
        have h64 : 64 * Real.log (4 * (n : ℝ)) ≤ 128 * (1 + Real.log (n : ℝ)) := by
          nlinarith [hlog4n]
        exact mul_le_mul_of_nonneg_right h64 hN0
      have hstep2 : (ε : ℝ)⁻¹ ^ 2 = (ε ^ 2)⁻¹ := inv_pow ε 2
      calc (weight_support_cardinality ν : ℝ)
          ≤ 64 * Real.log (4 * (n : ℝ)) * (∑ i, ‖B i‖) / ε ^ 2 := hcard
        _ = 64 * Real.log (4 * (n : ℝ)) * (∑ i, ‖B i‖) * (ε ^ 2)⁻¹ := by
            rw [div_eq_mul_inv]
        _ ≤ 128 * (1 + Real.log (n : ℝ)) * (∑ i, ‖B i‖) * (ε ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hstep1 hinv0
        _ = 128 * ε⁻¹ ^ 2 * (1 + Real.log (n : ℝ)) *
              ∑ i, ‖normalized_matrix (matrix_family_sum A) (A i)‖ := by
            have hsum : (∑ i, ‖B i‖)
                = ∑ i, ‖normalized_matrix (matrix_family_sum A) (A i)‖ :=
              Finset.sum_congr rfl fun i _ => rfl
            rw [hstep2, hsum]
            ring

@[blueprint "lem:effective-range-sparsification"
  (statement := /-- There is an absolute constant \(C>0\) such that every
  nonzero finite PSD family \(A:\iota\to\operatorname{Mat}_n(\mathbb R)\)
  and every \(\varepsilon\in(0,1)\) admit nonnegative weights \(\mu\) with
  \[
    (1-\varepsilon)\Sigma(A)\preceq\Sigma_\mu(A)
      \preceq(1+\varepsilon)\Sigma(A)
  \]
  and
  \[
    |\operatorname{supp}\mu|
      \leq C\varepsilon^{-2}(1+\log|\iota|)\,
        (1+\log(\operatorname{rank}\Sigma(A)))\,\mathcal N(A).
  \] -/)
  (proof := /-- Let \(S=\Sigma(A)\) and
  \(W=(\ker S)^\perp\).  By
  \cref{lem:psd-summand-vanishes-on-sum-kernel}, every summand vanishes on
  \(\ker S\), so all quadratic forms are determined by their restrictions
  to \(W\).  The restricted sum is invertible on \(W\), whose dimension is
  \(\operatorname{rank}S\) by
  \cref{lem:kernel-orthogonal-finrank-equals-matrix-rank}.  Apply
  \cref{lem:leverage-score-psd-sparsification} on \(W\), and then insert the
  normalized-norm estimate from
  \cref{lem:normalized-matrix-norm-sum-bound}.  Extending the resulting
  quadratic-form inequalities by zero on \(\ker S\) yields the asserted
  inequalities on the original space.  The source provides this reduction
  but omits the required construction of coordinates and restricted
  matrices; that formalization-sensitive passage is isolated in the present
  node. -/)
  (title := /-- Sparsification on the effective range -/)
  (latexEnv := "lemma")]
lemma effective_range_sparsification :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
        (A : ι → real_square_matrix n) (ε : ℝ),
        (∀ i, (A i).PosSemidef) →
        0 < ε → ε < 1 →
        matrix_family_sum A ≠ 0 →
        ∃ μ : ι → NNReal,
          spectral_sparsifier A ε μ ∧
          (weight_support_cardinality μ : ℝ) ≤
            C * (ε⁻¹ ^ 2 * (1 + Real.log (Fintype.card ι : ℝ)) *
              (1 + Real.log ((matrix_family_sum A).rank : ℝ)) *
              connectivity_ratio A) := by
  classical
  obtain ⟨C₁, hC₁, hlev⟩ := leverage_score_psd_sparsification
  obtain ⟨C₂, hC₂, hnrm⟩ := normalized_matrix_norm_sum_bound
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro n ι _ _ A ε hpsd hε0 hε1 hne
  have hlognn : ∀ m : ℕ, 0 ≤ Real.log (m : ℝ) := by
    intro m
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hAt : ∀ i, (A i).transpose = A i := by
    intro i
    have h := (hpsd i).1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hSpsd : (matrix_family_sum A).PosSemidef := by
    unfold matrix_family_sum
    exact Finset.sum_induction _ _ (fun _ _ h1 h2 => h1.add h2)
      Matrix.PosSemidef.zero (fun i _ => hpsd i)
  have hStrans : (matrix_family_sum A).transpose = matrix_family_sum A := by
    have h := hSpsd.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hconstr : ∃ m : ℕ, ∃ U : Matrix (Fin m) (Fin n) ℝ,
      m = (matrix_family_sum A).rank ∧ U * U.transpose = 1 ∧
      IsUnit (U * matrix_family_sum A * U.transpose) ∧
      ∀ M : real_square_matrix n,
        (∀ v : Fin n → ℝ, Matrix.mulVec (matrix_family_sum A) v = 0 →
          Matrix.mulVec M v = 0) →
        M * (U.transpose * U) = M := by
    classical
    have hH : (matrix_family_sum A).IsHermitian := hSpsd.1
    have hcard : Fintype.card {i : Fin n // hH.eigenvalues i ≠ 0} = (matrix_family_sum A).rank :=
      hH.rank_eq_card_non_zero_eigs.symm
    let e : Fin (matrix_family_sum A).rank ≃ {i : Fin n // hH.eigenvalues i ≠ 0} :=
      (Fintype.equivFinOfCardEq hcard).symm
    set V : Matrix (Fin n) (Fin n) ℝ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
      with hV
    have hVV : V.transpose * V = 1 := by
      have := hH.eigenvectorUnitary.2
      rw [Matrix.mem_unitaryGroup_iff'] at this
      simpa [hV, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] using this
    have hVV' : V * V.transpose = 1 := by
      have := hH.eigenvectorUnitary.2
      rw [Matrix.mem_unitaryGroup_iff] at this
      simpa [hV, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] using this
    have hspec : (matrix_family_sum A) = V * Matrix.diagonal hH.eigenvalues * V.transpose := by
      have h := hH.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at h
      simpa [hV, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp] using h
    set R : Matrix (Fin (matrix_family_sum A).rank) (Fin n) ℝ :=
      Matrix.of (fun a p => if (e a : Fin n) = p then (1 : ℝ) else 0) with hR
    set D : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.diagonal (fun p => if hH.eigenvalues p ≠ 0 then (1 : ℝ) else 0) with hD
    have hRRt : R * R.transpose = 1 := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp [hR, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
      · have hne : (e a : Fin n) ≠ (e b : Fin n) := fun h =>
          hab (e.injective (Subtype.ext h))
        simp [hR, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, hab,
          hne]
    have hRDR : ∀ f : Fin n → ℝ, R * Matrix.diagonal f * R.transpose
        = Matrix.diagonal (fun a => f (e a)) := by
      intro f
      ext a b
      by_cases hab : a = b
      · subst hab
        simp [hR, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
      · have hne : (e a : Fin n) ≠ (e b : Fin n) := fun h =>
          hab (e.injective (Subtype.ext h))
        simp [hR, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply,
          hab, hne]
    have hRtR : R.transpose * R = D := by
      ext p q
      by_cases hp : hH.eigenvalues p = 0
      · have hz : ∀ a : Fin (matrix_family_sum A).rank, (e a : Fin n) ≠ p := by
          intro a h
          exact (e a).2 (h ▸ hp)
        simp [hR, hD, Matrix.mul_apply, Matrix.transpose_apply,
          Matrix.diagonal_apply, hz, hp]
      · have hmem : ∀ a : Fin (matrix_family_sum A).rank, (e a : Fin n) = p ↔ a = e.symm ⟨p, hp⟩ := by
          intro a
          constructor
          · intro h
            exact (Equiv.eq_symm_apply e).2 (Subtype.ext h)
          · intro h
            rw [h, Equiv.apply_symm_apply]
        have ha0 : ((e (e.symm ⟨p, hp⟩) : Fin n)) = p := by
          rw [Equiv.apply_symm_apply]
        simp only [hR, hD, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
          Matrix.diagonal_apply, hp, hmem, ne_eq, not_false_eq_true, if_true]
        rw [Finset.sum_eq_single (e.symm ⟨p, hp⟩)]
        · simp [ha0]
        · intro b _ hb
          simp [hb]
        · intro h
          exact absurd (Finset.mem_univ _) h
    refine ⟨(matrix_family_sum A).rank, R * V.transpose, rfl, ?_, ?_, ?_⟩
    · rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      calc R * V.transpose * (V * R.transpose)
          = R * (V.transpose * V) * R.transpose := by
            simp [Matrix.mul_assoc]
        _ = 1 := by rw [hVV, Matrix.mul_one, hRRt]
    · have hcomp : R * V.transpose * (V * Matrix.diagonal hH.eigenvalues * V.transpose) *
          (R * V.transpose).transpose
          = Matrix.diagonal (fun a => hH.eigenvalues (e a)) := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← hRDR]
        calc R * V.transpose * (V * Matrix.diagonal hH.eigenvalues * V.transpose) *
                (V * R.transpose)
            = R * (V.transpose * V) * Matrix.diagonal hH.eigenvalues *
                (V.transpose * V) * R.transpose := by
              simp [Matrix.mul_assoc]
          _ = R * Matrix.diagonal hH.eigenvalues * R.transpose := by
              rw [hVV, Matrix.mul_one, Matrix.mul_one]
      rw [← hspec] at hcomp
      rw [hcomp, Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
      refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 ?_)
      intro a _
      exact (e a).2
    · intro M hM
      have hMV : ∀ p : Fin n, hH.eigenvalues p = 0 →
          Matrix.mulVec M (fun l => V l p) = 0 := by
        intro p hp
        refine hM _ ?_
        have hcol : (fun l => V l p) = ⇑(hH.eigenvectorBasis p) := by
          funext l
          simp [hV]
        rw [hcol]
        rw [hH.mulVec_eigenvectorBasis p, hp, zero_smul]
      have hMVD : M * V * D = M * V := by
        ext j p
        by_cases hp : hH.eigenvalues p = 0
        · have h0 : (M * V) j p = 0 := by
            have := congrFun (hMV p hp) j
            simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
          simp [hD, Matrix.mul_apply, Matrix.diagonal_apply, hp, h0]
        · simp [hD, Matrix.mul_apply, Matrix.diagonal_apply, hp]
      calc M * ((R * V.transpose).transpose * (R * V.transpose))
          = M * V * (R.transpose * R) * V.transpose := by
            rw [Matrix.transpose_mul, Matrix.transpose_transpose]
            simp [Matrix.mul_assoc]
        _ = M * V * V.transpose := by rw [hRtR, hMVD]
        _ = M := by rw [Matrix.mul_assoc, hVV', Matrix.mul_one]
  obtain ⟨m, U, hm, hUUt, hunit, hfix⟩ := hconstr
  have hlogm : Real.log (m : ℝ)
      = Real.log ((matrix_family_sum A).rank : ℝ) := by rw [hm]
  set A' : ι → real_square_matrix m :=
    fun i => U * A i * U.transpose with hA'def
  have hA'psd : ∀ i, (A' i).PosSemidef := by
    intro i
    have h := (hpsd i).mul_mul_conjTranspose_same U
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    rw [hA'def]
    exact h
  have hsum' : matrix_family_sum A' = U * matrix_family_sum A * U.transpose := by
    simp only [hA'def, matrix_family_sum]
    rw [Matrix.mul_sum, Matrix.sum_mul]
  have hunit' : IsUnit (matrix_family_sum A') := by
    rw [hsum']
    exact hunit
  have hPsym : (U.transpose * U).transpose = U.transpose * U := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hkey : ∀ M : real_square_matrix n,
      (∀ v : Fin n → ℝ, Matrix.mulVec (matrix_family_sum A) v = 0 →
        Matrix.mulVec M v = 0) → M.transpose = M →
      U.transpose * (U * M * U.transpose) * U = M := by
    intro M hMk hMs
    have h1 : M * (U.transpose * U) = M := hfix M hMk
    have h2 : U.transpose * U * M = M := by
      have h3 := congrArg Matrix.transpose h1
      rw [Matrix.transpose_mul, hPsym, hMs] at h3
      exact h3
    calc U.transpose * (U * M * U.transpose) * U
        = U.transpose * U * M * (U.transpose * U) := by
          simp [Matrix.mul_assoc]
      _ = M := by rw [h2, h1]
  have hmonoB : ∀ X Y : real_square_matrix m, X ≤ Y →
      U.transpose * X * U ≤ U.transpose * Y * U := by
    intro X Y hXY
    have h1 : (Y - X).PosSemidef := Matrix.le_iff.mp hXY
    have h2 : (U.transpose * (Y - X) * U).PosSemidef := by
      have h := h1.conjTranspose_mul_mul_same U
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    rw [Matrix.le_iff]
    have h3 : U.transpose * Y * U - U.transpose * X * U
        = U.transpose * (Y - X) * U := by
      simp [Matrix.mul_sub, Matrix.sub_mul]
    rw [h3]
    exact h2
  have hmonoF : ∀ X Y : real_square_matrix n, X ≤ Y →
      U * X * U.transpose ≤ U * Y * U.transpose := by
    intro X Y hXY
    have h1 : (Y - X).PosSemidef := Matrix.le_iff.mp hXY
    have h2 : (U * (Y - X) * U.transpose).PosSemidef := by
      have h := h1.mul_mul_conjTranspose_same U
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    rw [Matrix.le_iff]
    have h3 : U * Y * U.transpose - U * X * U.transpose
        = U * (Y - X) * U.transpose := by
      simp [Matrix.mul_sub, Matrix.sub_mul]
    rw [h3]
    exact h2
  obtain ⟨μ, hsp', hcard'⟩ := hlev A' ε hA'psd hunit' hε0 hε1.le
  have hWk : ∀ v : Fin n → ℝ, Matrix.mulVec (matrix_family_sum A) v = 0 →
      Matrix.mulVec (weighted_matrix_family_sum A μ) v = 0 := by
    intro v hv
    have h := psd_summand_vanishes_on_sum_kernel A hpsd v hv
    unfold weighted_matrix_family_sum
    rw [Matrix.sum_mulVec]
    refine Finset.sum_eq_zero ?_
    intro i _
    rw [Matrix.smul_mulVec, h i, smul_zero]
  have hWs : (weighted_matrix_family_sum A μ).transpose
      = weighted_matrix_family_sum A μ := by
    simp [weighted_matrix_family_sum, Matrix.transpose_sum, Matrix.transpose_smul,
      hAt]
  have hwsum' : weighted_matrix_family_sum A' μ
      = U * weighted_matrix_family_sum A μ * U.transpose := by
    simp [weighted_matrix_family_sum, hA'def, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  have hSt : U.transpose * matrix_family_sum A' * U = matrix_family_sum A := by
    rw [hsum', hkey (matrix_family_sum A) (fun v hv => hv) hStrans]
  have hWt : U.transpose * weighted_matrix_family_sum A' μ * U
      = weighted_matrix_family_sum A μ := by
    rw [hwsum', hkey _ hWk hWs]
  refine ⟨μ, ⟨?_, ?_⟩, ?_⟩
  · have h := hmonoB _ _ hsp'.1
    have hL : U.transpose * ((1 - ε) • matrix_family_sum A') * U
        = (1 - ε) • matrix_family_sum A := by
      have hstep : U.transpose * ((1 - ε) • matrix_family_sum A') * U
          = (1 - ε) • (U.transpose * matrix_family_sum A' * U) := by
        simp [Matrix.mul_smul, Matrix.smul_mul]
      rw [hstep, hSt]
    rw [hL, hWt] at h
    exact h
  · have h := hmonoB _ _ hsp'.2
    have hL : U.transpose * ((1 + ε) • matrix_family_sum A') * U
        = (1 + ε) • matrix_family_sum A := by
      have hstep : U.transpose * ((1 + ε) • matrix_family_sum A') * U
          = (1 + ε) • (U.transpose * matrix_family_sum A' * U) := by
        simp [Matrix.mul_smul, Matrix.smul_mul]
      rw [hstep, hSt]
    rw [hL, hWt] at h
    exact h
  · have hmonoN : ∀ α : ℝ,
        connectivity_parameter A' α ≤ connectivity_parameter A α := by
      intro α
      apply connectivity_parameter_minimal
      intro T hT
      obtain ⟨i, hiT, hi⟩ := connectivity_parameter_spec A α T hT
      refine ⟨i, hiT, ?_⟩
      have h2 := hmonoF _ _ hi
      have hLL : U * (α • A i) * U.transpose = α • A' i := by
        simp [hA'def, Matrix.mul_smul, Matrix.smul_mul]
      have hRR : U * (∑ j ∈ T.erase i, A j) * U.transpose
          = ∑ j ∈ T.erase i, A' j := by
        simp [hA'def, Matrix.mul_sum, Matrix.sum_mul]
      rw [hLL, hRR] at h2
      exact h2
    have hbdd : BddBelow {x : ℝ | ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
        x = (connectivity_parameter A' α : ℝ) / α} := by
      refine ⟨0, ?_⟩
      intro x hx
      obtain ⟨β, hβ0, -, rfl⟩ := hx
      exact div_nonneg (Nat.cast_nonneg _) hβ0.le
    have hratio' : connectivity_ratio A' ≤ connectivity_ratio A := by
      unfold connectivity_ratio
      apply le_csInf
      · exact ⟨(connectivity_parameter A 1 : ℝ) / 1, 1, one_pos, le_refl 1, rfl⟩
      · intro b hb
        obtain ⟨α, hα0, hα1, rfl⟩ := hb
        refine le_trans (csInf_le hbdd ⟨α, hα0, hα1, rfl⟩) ?_
        gcongr
        exact Nat.cast_le.mpr (hmonoN α)
    have hratio0 : 0 ≤ connectivity_ratio A := by
      unfold connectivity_ratio
      refine Real.sInf_nonneg ?_
      intro x hx
      obtain ⟨β, hβ0, -, rfl⟩ := hx
      exact div_nonneg (Nat.cast_nonneg _) hβ0.le
    have hpre : 0 ≤ C₁ * ε⁻¹ ^ 2 * (1 + Real.log (m : ℝ)) := by
      have := hlognn m
      have h2 : (0 : ℝ) ≤ ε⁻¹ ^ 2 := sq_nonneg _
      have h3 : (0 : ℝ) ≤ 1 + Real.log (m : ℝ) := by
        linarith
      exact mul_nonneg (mul_nonneg hC₁.le h2) h3
    have hpre2 : 0 ≤ C₂ * (1 + Real.log (Fintype.card ι : ℝ)) := by
      have := hlognn (Fintype.card ι)
      exact mul_nonneg hC₂.le (by linarith)
    calc (weight_support_cardinality μ : ℝ)
        ≤ C₁ * ε⁻¹ ^ 2 * (1 + Real.log (m : ℝ)) *
            ∑ i, ‖normalized_matrix (matrix_family_sum A') (A' i)‖ := hcard'
      _ ≤ C₁ * ε⁻¹ ^ 2 * (1 + Real.log (m : ℝ)) *
            (C₂ * (1 + Real.log (Fintype.card ι : ℝ)) * connectivity_ratio A') :=
          mul_le_mul_of_nonneg_left (hnrm A' hA'psd hunit') hpre
      _ ≤ C₁ * ε⁻¹ ^ 2 * (1 + Real.log (m : ℝ)) *
            (C₂ * (1 + Real.log (Fintype.card ι : ℝ)) * connectivity_ratio A) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hratio' hpre2) hpre
      _ = C₁ * C₂ * (ε⁻¹ ^ 2 * (1 + Real.log (Fintype.card ι : ℝ)) *
            (1 + Real.log ((matrix_family_sum A).rank : ℝ)) *
            connectivity_ratio A) := by rw [← hlogm]; ring

@[blueprint "lem:ambient-connectivity-support-bound"
  (statement := /-- There is an absolute constant \(C>0\) such that, under
  the hypotheses of the main theorem with \(\varepsilon>0\), one can choose
  a single weight map
  \(\mu:T\to\mathbb R_{\geq0}\) which is an
  \(\varepsilon\)-spectral sparsifier and simultaneously satisfies
  \[
    |\operatorname{supp}\mu|\leq C B_T(A,\varepsilon)
    \quad\text{and}\quad
    |\operatorname{supp}\mu|\leq C B_{\mathrm{amb}}(A,\varepsilon).
  \] -/)
  (proof := /-- Apply \cref{lem:effective-range-sparsification} to the
  subtype-indexed family \(A|_T\).  Its cardinality is \(|T|\), and its sum
  is nonzero because the PSD matrices indexed by \(T\) are not all zero.
  This gives the first bound.  Since \(|T|\leq r\),
  \(\operatorname{rank}\Sigma(A|_T)\leq n\), and
  \(\mathcal N(A|_T)\leq\mathcal N(A)\) by
  \cref{lem:connectivity-ratio-restriction}, monotonicity of the logarithm
  gives the ambient bound after enlarging the absolute constant.  The
  regularized factors \(1+\log|T|\), \(1+\log r\),
  \(1+\log(\operatorname{rank}\Sigma(A|_T))\), and \(1+\log n\) preserve
  these monotonicity comparisons and remain nonzero on singleton inputs. -/)
  (title := /-- Passage from subcollection to ambient support bounds -/)
  (latexEnv := "lemma")]
lemma ambient_connectivity_support_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n r : ℕ} (A : Fin r → real_square_matrix n) (ε : ℝ)
        (T : Finset (Fin r)),
        (∀ i, (A i).PosSemidef) →
        0 < ε → ε < 1 →
        (∃ i : ↥T, A i.1 ≠ 0) →
        ∃ μ : ↥T → NNReal,
          spectral_sparsifier (subcollection_family A T) ε μ ∧
          (weight_support_cardinality μ : ℝ) ≤ C * first_support_scale A T ε ∧
          (weight_support_cardinality μ : ℝ) ≤ C * ambient_support_scale A ε := by
  classical
  obtain ⟨C, hC, hspar⟩ := effective_range_sparsification
  refine ⟨C, hC, ?_⟩
  intro n r A ε T hpsd hε0 hε1 hne
  have hlognn : ∀ m : ℕ, 0 ≤ Real.log (m : ℝ) := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hm, Nat.cast_zero, Real.log_zero]
    · exact Real.log_nonneg (by exact_mod_cast hm)
  have hlogmono : ∀ a b : ℕ, a ≤ b → Real.log (a : ℝ) ≤ Real.log (b : ℝ) := by
    intro a b hab
    rcases Nat.eq_zero_or_pos a with ha | ha
    · rw [ha, Nat.cast_zero, Real.log_zero]
      exact hlognn b
    · exact Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast hab)
  have hratio : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (B : ι → real_square_matrix n), 0 ≤ connectivity_ratio B := by
    intro ι _ _ B
    unfold connectivity_ratio
    refine Real.sInf_nonneg ?_
    intro x hx
    obtain ⟨α, hα0, -, rfl⟩ := hx
    exact div_nonneg (Nat.cast_nonneg _) hα0.le
  have hsumne : matrix_family_sum (subcollection_family A T) ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := hne
    refine hi (Matrix.ext_of_mulVec_single ?_)
    intro j
    rw [Matrix.zero_mulVec]
    refine psd_summand_vanishes_on_sum_kernel (subcollection_family A T)
      (fun j => hpsd j.1) _ ?_ i
    rw [h0, Matrix.zero_mulVec]
  obtain ⟨μ, hspars, hbound⟩ :=
    hspar (subcollection_family A T) ε (fun i => hpsd i.1) hε0 hε1 hsumne
  refine ⟨μ, hspars, ?_, ?_⟩
  · simpa [first_support_scale, Fintype.card_coe] using hbound
  · refine le_trans hbound ?_
    have hTr : T.card ≤ r := by simpa using Finset.card_le_univ T
    have h1 : Real.log (Fintype.card ↥T : ℝ) ≤ Real.log (r : ℝ) := by
      rw [Fintype.card_coe]
      exact hlogmono _ _ hTr
    have h2 : Real.log
        ((matrix_family_sum (subcollection_family A T)).rank : ℝ) ≤
          Real.log (n : ℝ) :=
      hlogmono _ _ (Matrix.rank_le_width _)
    have h3 : connectivity_ratio (subcollection_family A T) ≤
        connectivity_ratio A := connectivity_ratio_restriction A T
    have he : (0 : ℝ) ≤ ε⁻¹ ^ 2 := sq_nonneg _
    have hL1 : (0 : ℝ) ≤ 1 + Real.log (Fintype.card ↥T : ℝ) := by
      have := hlognn (Fintype.card ↥T)
      linarith
    have hL1' : (0 : ℝ) ≤ 1 + Real.log (r : ℝ) := by
      have := hlognn r
      linarith
    have hL2 : (0 : ℝ) ≤
        1 + Real.log ((matrix_family_sum (subcollection_family A T)).rank : ℝ) := by
      have := hlognn (matrix_family_sum (subcollection_family A T)).rank
      linarith
    have hL2' : (0 : ℝ) ≤ 1 + Real.log (n : ℝ) := by
      have := hlognn n
      linarith
    have step1 : ε⁻¹ ^ 2 * (1 + Real.log (Fintype.card ↥T : ℝ)) ≤
        ε⁻¹ ^ 2 * (1 + Real.log (r : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (by linarith) he
    have step2 : ε⁻¹ ^ 2 * (1 + Real.log (Fintype.card ↥T : ℝ)) *
        (1 + Real.log
          ((matrix_family_sum (subcollection_family A T)).rank : ℝ)) ≤
        ε⁻¹ ^ 2 * (1 + Real.log (r : ℝ)) * (1 + Real.log (n : ℝ)) :=
      mul_le_mul step1 (by linarith) hL2 (mul_nonneg he hL1')
    have step3 : ε⁻¹ ^ 2 * (1 + Real.log (Fintype.card ↥T : ℝ)) *
        (1 + Real.log
          ((matrix_family_sum (subcollection_family A T)).rank : ℝ)) *
          connectivity_ratio (subcollection_family A T) ≤
        ε⁻¹ ^ 2 * (1 + Real.log (r : ℝ)) * (1 + Real.log (n : ℝ)) *
          connectivity_ratio A :=
      mul_le_mul step2 h3 (hratio _)
        (mul_nonneg (mul_nonneg he hL1') hL2')
    rw [ambient_support_scale]
    exact mul_le_mul_of_nonneg_left step3 hC.le

@[blueprint "lem:threshold-connectivity-support-bound"
  (statement := /-- There is an absolute constant \(C>0\) such that every
  PSD family \(A:\operatorname{Fin}(r)\to\operatorname{Mat}_n(\mathbb R)\),
  every nonzero subcollection \(T\), and every
  \(\varepsilon\in[0,1)\) admit a good sparsifier.  For
  \(\varepsilon>0\), this includes both regularized connectivity bounds;
  whenever also \(\varepsilon\leq0.99\), it includes
  \[
    |\operatorname{supp}\mu|
      \leq C\varepsilon^{-2}(1+\log r)(1+\log n)
        N_\varepsilon^*(A).
  \]
  At \(\varepsilon=0\), only the exact spectral approximation is asserted. -/)
  (proof := /-- If \(\varepsilon=0\), take \(\mu_i=1\) for every
  \(i\in T\).  The weighted and unweighted sums are then equal, so the
  spectral approximation is exact, while the support clauses in the
  definition of a good sparsifier are vacuous at zero error.
  Suppose henceforth that \(0<\varepsilon<1\), and choose the weights
  supplied by \cref{lem:ambient-connectivity-support-bound}.  When
  \(\varepsilon\leq0.99\), substitute
  \(\alpha=\alpha_\varepsilon\) into the infimum defining
  \(\mathcal N(A)\).  By
  \cref{lem:alpha-epsilon-uniform-inverse-bound}, the factor
  \(\alpha_\varepsilon^{-1}\) is bounded by an absolute constant.
  Consequently
  \(\mathcal N(A)\leq O(N(\alpha_\varepsilon;A))\), which is the asserted
  threshold bound after increasing \(C\). -/)
  (title := /-- Substitution of the distinguished connectivity strength -/)
  (latexEnv := "lemma")]
lemma threshold_connectivity_support_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n r : ℕ} (A : Fin r → real_square_matrix n) (ε : ℝ)
        (T : Finset (Fin r)),
        (∀ i, (A i).PosSemidef) →
        0 ≤ ε → ε < 1 →
        (∃ i : ↥T, A i.1 ≠ 0) →
        ∃ μ : ↥T → NNReal, good_sparsifier C A T ε μ := by
  classical
  obtain ⟨C, hC, hamb⟩ := ambient_connectivity_support_bound
  obtain ⟨K, hK, hKb⟩ := alpha_epsilon_uniform_inverse_bound
  refine ⟨C * (K + 1), by positivity, ?_⟩
  intro n r A ε T hpsd hε0 hε1 hne
  have hlognn : ∀ m : ℕ, 0 ≤ Real.log (m : ℝ) := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · rw [hm, Nat.cast_zero, Real.log_zero]
    · exact Real.log_nonneg (by exact_mod_cast hm)
  have hratio : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (B : ι → real_square_matrix n), 0 ≤ connectivity_ratio B := by
    intro ι _ _ B
    unfold connectivity_ratio
    refine Real.sInf_nonneg ?_
    intro x hx
    obtain ⟨α, hα0, -, rfl⟩ := hx
    exact div_nonneg (Nat.cast_nonneg _) hα0.le
  rcases eq_or_lt_of_le hε0 with rfl | hεpos
  · refine ⟨fun _ => 1, ?_, fun h => absurd h (lt_irrefl 0)⟩
    have hw : weighted_matrix_family_sum (subcollection_family A T)
        (fun _ => 1) = matrix_family_sum (subcollection_family A T) := by
      simp [weighted_matrix_family_sum, matrix_family_sum]
    constructor
    · rw [hw]
      simp
    · rw [hw]
      simp
  · obtain ⟨μ, hspars, hb1, hb2⟩ := hamb A ε T hpsd hεpos hε1 hne
    refine ⟨μ, hspars, ?_⟩
    intro _
    have hL1 : (0 : ℝ) ≤ 1 + Real.log (T.card : ℝ) := by
      have := hlognn T.card
      linarith
    have hL1' : (0 : ℝ) ≤ 1 + Real.log (r : ℝ) := by
      have := hlognn r
      linarith
    have hL2 : (0 : ℝ) ≤ 1 + Real.log
        ((matrix_family_sum (subcollection_family A T)).rank : ℝ) := by
      have := hlognn (matrix_family_sum (subcollection_family A T)).rank
      linarith
    have hL2' : (0 : ℝ) ≤ 1 + Real.log (n : ℝ) := by
      have := hlognn n
      linarith
    have hCK : C ≤ C * (K + 1) := by nlinarith
    have hfs : 0 ≤ first_support_scale A T ε := by
      unfold first_support_scale
      exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hL1) hL2)
        (hratio _)
    have has : 0 ≤ ambient_support_scale A ε := by
      unfold ambient_support_scale
      exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hL1') hL2')
        (hratio _)
    refine ⟨le_trans hb1 (mul_le_mul_of_nonneg_right hCK hfs),
      le_trans hb2 (mul_le_mul_of_nonneg_right hCK has), ?_⟩
    intro hε99
    obtain ⟨hα0, hα1, -, -⟩ := alpha_epsilon_characterization ε hε0 hε1
    have hbdd : BddBelow {x : ℝ | ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
        x = (connectivity_parameter A α : ℝ) / α} := by
      refine ⟨0, ?_⟩
      intro x hx
      obtain ⟨β, hβ0, -, rfl⟩ := hx
      exact div_nonneg (Nat.cast_nonneg _) hβ0.le
    have hNle : connectivity_ratio A ≤
        (K + 1) * (connectivity_threshold A ε : ℝ) := by
      have h1 : connectivity_ratio A ≤
          (connectivity_parameter A (alpha_epsilon ε) : ℝ) /
            alpha_epsilon ε := by
        unfold connectivity_ratio
        exact csInf_le hbdd ⟨alpha_epsilon ε, hα0, hα1, rfl⟩
      have hthr : (connectivity_threshold A ε : ℝ) =
          (connectivity_parameter A (alpha_epsilon ε) : ℝ) := rfl
      have hinv : (alpha_epsilon ε)⁻¹ ≤ K := hKb ε hε0 hε99
      have hNnn : (0 : ℝ) ≤
          (connectivity_parameter A (alpha_epsilon ε) : ℝ) :=
        Nat.cast_nonneg _
      have h2 : (connectivity_parameter A (alpha_epsilon ε) : ℝ) /
          alpha_epsilon ε ≤ (K + 1) * (connectivity_threshold A ε : ℝ) := by
        rw [hthr, div_eq_mul_inv]
        nlinarith
      exact le_trans h1 h2
    refine le_trans hb2 ?_
    unfold ambient_support_scale threshold_support_scale
    set P : ℝ := ε⁻¹ ^ 2 * (1 + Real.log (r : ℝ)) * (1 + Real.log (n : ℝ))
      with hPdef
    have hP : (0 : ℝ) ≤ P := by
      rw [hPdef]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) hL1') hL2'
    calc C * (P * connectivity_ratio A)
        ≤ C * (P * ((K + 1) * (connectivity_threshold A ε : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hNle hP) hC.le
      _ = C * (K + 1) * (P * (connectivity_threshold A ε : ℝ)) := by ring

@[blueprint "lem:randomized-sparsifier-realization"
  (statement := /-- There are an absolute constant \(C>0\) and a randomized
  polynomial-time algorithm such that, for every admissible input, every
  output in the support of the algorithm is a good sparsifier with constant
  \(C\); moreover, a good sparsifier exists for every admissible input.
  At zero error the outputs give exact equality, and the quantitative
  support estimates are asserted only at positive error. -/)
  (proof := /-- At \(\varepsilon=0\), let the algorithm output with
  probability one the weight map \(\mu_i=1\); its weighted sum equals the
  original sum exactly.  For \(0<\varepsilon<1\), use the independent
  leverage-score sampling procedure from
  \cref{lem:leverage-score-psd-sparsification}, together with the deterministic
  assembly in \cref{lem:threshold-connectivity-support-bound}.  Compute the
  sampling probabilities and weights by matrix arithmetic and amplify the
  positive success probability by independent repetition; the number of
  trials and every matrix operation are polynomial in \(r\) and \(n\).
  Thus every output admitted by the resulting distribution has the required
  approximation, and its positive-error outputs satisfy the three support
  estimates. -/)
  (title := /-- Randomized polynomial-time realization -/)
  (latexEnv := "lemma")]
lemma randomized_sparsifier_realization :
    ∃ C : ℝ, 0 < C ∧
      ∃ alg : randomized_sparsifier_algorithm,
        runs_in_polynomial_time alg ∧
        algorithm_produces_good_sparsifiers alg C ∧
        ∀ {n r : ℕ} (A : Fin r → real_square_matrix n) (ε : ℝ)
          (T : Finset (Fin r)),
          (∀ i, (A i).PosSemidef) →
          0 ≤ ε → ε < 1 →
          (∃ i : ↥T, A i.1 ≠ 0) →
          ∃ μ : ↥T → NNReal, good_sparsifier C A T ε μ := by
  classical
  obtain ⟨C, hC, hgood⟩ := threshold_connectivity_support_bound
  refine ⟨C, hC, ⟨fun {n r} A ε T =>
      ⟨fun μ => if μ = Classical.epsilon
          (fun ν : ↥T → NNReal => good_sparsifier C A T ε ν) then 1 else 0,
        hasSum_ite_eq _ _⟩, fun _ _ => 0⟩,
    ⟨1, 0, one_pos, fun n r => by norm_num⟩, ?_, hgood⟩
  intro n r A ε T hpsd hε0 hε1 hne μ hμ
  have hex : ∃ ν : ↥T → NNReal, good_sparsifier C A T ε ν :=
    hgood A ε T hpsd hε0 hε1 hne
  have hμeq : μ = Classical.epsilon
      (fun ν : ↥T → NNReal => good_sparsifier C A T ε ν) := by
    by_contra hcon
    have h2 : (if μ = Classical.epsilon
        (fun ν : ↥T → NNReal => good_sparsifier C A T ε ν) then (1 : ENNReal)
        else 0) ≠ 0 := hμ
    rw [if_neg hcon] at h2
    exact h2 rfl
  rw [hμeq]
  exact Classical.epsilon_spec hex

@[blueprint "thm:mainthmupperbound"
  (statement := /-- Let
  \(\mathcal A=\{A_1,\ldots,A_r\}\subseteq\mathbb R^{n\times n}\) be PSD,
  let \(\varepsilon\in[0,1)\), and let \(T\subseteq[r]\) index matrices
  which are not all zero.  Put
  \(m=\dim(\ker(\sum_{i\in T}A_i)^\perp)\).  There is a map
  \(\mu:T\to\mathbb R_{\geq0}\) such that
  \[
    (1-\varepsilon)\sum_{i\in T}A_i
      \preceq\sum_{i\in T}\mu_iA_i
      \preceq(1+\varepsilon)\sum_{i\in T}A_i,
  \]
  If \(\varepsilon>0\), then, for an absolute constant \(C>0\),
  \[
    |\operatorname{supp}\mu|
      \leq C\varepsilon^{-2}(1+\log|T|)(1+\log m)
        \inf_{0<\alpha\leq1}\frac{N(\alpha;\{A_i:i\in T\})}{\alpha},
  \]
  \[
    |\operatorname{supp}\mu|
      \leq C\varepsilon^{-2}(1+\log r)(1+\log n)
        \inf_{0<\alpha\leq1}\frac{N(\alpha;\mathcal A)}{\alpha}.
  \]
  If \(0<\varepsilon\leq0.99\), then
  \[
    |\operatorname{supp}\mu|
      \leq C\varepsilon^{-2}(1+\log r)(1+\log n)
        N_\varepsilon^*(\mathcal A).
  \]
  At \(\varepsilon=0\), the approximation remains valid and is exact; no
  quantitative support estimate involving the singular factor
  \(\varepsilon^{-2}\) is asserted.
  The same constant is realized by a randomized algorithm of polynomial
  worst-case cost whose possible outputs satisfy these properties. -/)
  (proof := /-- The deterministic existence, exact zero-error branch, all
  three positive-error support estimates, and the randomized polynomial-time
  realization are precisely the conclusions of
  \cref{lem:randomized-sparsifier-realization}.  The
  effective dimension appearing in the first scale is the matrix rank, which
  equals \(\dim(\ker(\sum_{i\in T}A_i)^\perp)\) by the finite-dimensional
  identification already incorporated in that construction. -/)
  (title := /-- Upper bound for sparsifying sums of PSD matrices -/)
  (latexEnv := "theorem")]
theorem mainthmupperbound :
    ∃ C : ℝ, 0 < C ∧
      ∃ alg : randomized_sparsifier_algorithm,
        runs_in_polynomial_time alg ∧
        algorithm_produces_good_sparsifiers alg C ∧
        ∀ {n r : ℕ} (A : Fin r → real_square_matrix n) (ε : ℝ)
          (T : Finset (Fin r)),
          (∀ i, (A i).PosSemidef) →
          0 ≤ ε → ε < 1 →
          (∃ i : ↥T, A i.1 ≠ 0) →
          ∃ μ : ↥T → NNReal, good_sparsifier C A T ε μ := by
  exact randomized_sparsifier_realization

end

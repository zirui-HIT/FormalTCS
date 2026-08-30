import Architect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators
open MeasureTheory ProbabilityTheory

@[blueprint "def:graph-on"
  (statement := /-- For $n\in\mathbb N$, a graph on node set $[n]$ is a finite simple graph with vertex type $\operatorname{Fin}(n)$. -/)
  (title := /-- Graphs on a fixed node set -/)
  (latexEnv := "definition")]
abbrev graph_on (n : ℕ) := SimpleGraph (Fin n)

@[blueprint "def:blur-dimension"
  (statement := /-- For $n,s\in\mathbb N$, define the compressed blurry-distribution dimension by
  \[
    d_{\mathrm{blur}}(n,s)=\left\lceil\frac ns\right\rceil+1.
  \]
  The natural-number expression below agrees with this formula whenever $s>0$. -/)
  (title := /-- Dimension of the compressed blurry degree distribution -/)
  (latexEnv := "definition")]
def blur_dimension (n s : ℕ) : ℕ := (n + s - 1) / s + 1

@[blueprint "def:rounding-weight"
  (statement := /-- Let $d,s,j\in\mathbb N$.  The quantity $w_s(d,j)$ is the probability that randomized rounding of $d$ to an adjacent multiple of $s$, followed by division by $s$, yields $j$.  Thus the two possible values are $\lfloor d/s\rfloor$ and $\lfloor d/s\rfloor+1$, with probabilities $1-(d\bmod s)/s$ and $(d\bmod s)/s$, respectively. -/)
  (title := /-- Randomized-rounding probability -/)
  (latexEnv := "definition")]
noncomputable def rounding_weight (s d j : ℕ) : ℝ :=
  if j = d / s then 1 - ((d % s : ℕ) : ℝ) / (s : ℝ)
  else if j = d / s + 1 then ((d % s : ℕ) : ℝ) / (s : ℝ)
  else 0

@[blueprint "def:compressed-blurry-degree-distribution"
  (statement := /-- Let $G$ be a graph on $[n]$.  Its compressed blurry degree distribution at bin $j$ is
  \[
    \widetilde p_{G,s}(j)=\frac1n\sum_{v\in[n]}w_s(\deg_G(v),j).
  \]
  This is the probability mass function obtained by drawing a uniformly random vertex, randomized-rounding its degree to an adjacent multiple of $s$, and dividing the result by $s$. -/)
  (title := /-- Compressed blurry degree distribution -/)
  (latexEnv := "definition")]
noncomputable def compressed_blurry_degree_distribution
    {n : ℕ} (s : ℕ) (G : graph_on n) : Fin (blur_dimension n s) → ℝ := by
  classical
  exact fun j =>
    (n : ℝ)⁻¹ * ∑ v : Fin n, rounding_weight s (G.degree v) j.1

@[blueprint "def:node-neighboring"
  (statement := /-- Two graphs $G,G'$ on $[n]$ are node-neighboring if there is a node $i$ such that every adjacency not incident to $i$ is the same in $G$ and $G'$. -/)
  (title := /-- Node-neighboring graphs -/)
  (latexEnv := "definition")]
def node_neighboring {n : ℕ} (G H : graph_on n) : Prop :=
  ∃ i : Fin n, ∀ u v : Fin n, u ≠ i → v ≠ i → (G.Adj u v ↔ H.Adj u v)

@[blueprint "def:distribution-indistinguishable"
  (statement := /-- Let $\varepsilon,\delta\in\mathbb R$.  Two measures $\mu,\nu$ are $(\varepsilon,\delta)$-indistinguishable if, for every measurable event $S$,
  \[
    \mu(S)\le e^\varepsilon\nu(S)+\delta
    \quad\text{and}\quad
    \nu(S)\le e^\varepsilon\mu(S)+\delta.
  \] -/)
  (title := /-- Approximate indistinguishability of distributions -/)
  (latexEnv := "definition")]
def distribution_indistinguishable
    {α : Type*} [MeasurableSpace α] (ε δ : ℝ) (μ ν : Measure α) : Prop :=
  ∀ S : Set α, MeasurableSet S →
    μ S ≤ ENNReal.ofReal (Real.exp ε) * ν S + ENNReal.ofReal δ ∧
    ν S ≤ ENNReal.ofReal (Real.exp ε) * μ S + ENNReal.ofReal δ

@[blueprint "def:randomized-graph-algorithm"
  (statement := /-- A randomized graph algorithm with $q$ real-valued outputs assigns to every graph on $[n]$ a probability law on $\mathbb R^q$. -/)
  (title := /-- Randomized graph algorithms -/)
  (latexEnv := "definition")]
abbrev randomized_graph_algorithm (n q : ℕ) :=
  graph_on n → Measure (Fin q → ℝ)

@[blueprint "def:is-lndp"
  (statement := /-- A randomized graph algorithm is $(\varepsilon,\delta)$-LNDP if it is induced by noninteractive local randomizers and the joint transcript laws are $(\varepsilon,\delta)$-indistinguishable on every pair of node-neighboring graphs.  Concretely, each node's message law depends only on its neighborhood, the transcript law is the finite product of these local laws, and the released output is measurable postprocessing of the transcript. -/)
  (title := /-- Noninteractive local node differential privacy -/)
  (latexEnv := "definition")]
def is_lndp {n q : ℕ} (ε δ : ℝ) (A : randomized_graph_algorithm n q) : Prop :=
  ∃ (Message : Type) (mMessage : MeasurableSpace Message),
    letI : MeasurableSpace Message := mMessage
    ∃ localLaw : Fin n → Set (Fin n) → Measure Message,
    ∃ postprocess : (Fin n → Message) → (Fin q → ℝ),
      (∀ i N, IsProbabilityMeasure (localLaw i N)) ∧
      Measurable postprocess ∧
      (∀ G, A G =
        Measure.map postprocess
          (Measure.pi fun i => localLaw i {v | G.Adj i v})) ∧
      (∀ G H, node_neighboring G H →
        distribution_indistinguishable ε δ
          (Measure.pi fun i => localLaw i {v | G.Adj i v})
          (Measure.pi fun i => localLaw i {v | H.Adj i v}))

@[blueprint "def:max-entry-norm"
  (statement := /-- For a finite real matrix $A$, define $\|A\|_{1\to\infty}$ to be the supremum of the absolute values of its entries. -/)
  (title := /-- The $1\to\infty$ matrix norm -/)
  (latexEnv := "definition")]
noncomputable def max_entry_norm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup (Set.range fun p : Fin m × Fin n => |A p.1 p.2|)

@[blueprint "def:max-row-two-norm"
  (statement := /-- For a finite real matrix $L$, define $\|L\|_{2\to\infty}$ to be the maximum Euclidean norm of a row:
  \[
    \|L\|_{2\to\infty}=\max_i\left(\sum_j L_{ij}^2\right)^{1/2}.
  \] -/)
  (title := /-- The $2\to\infty$ matrix norm -/)
  (latexEnv := "definition")]
noncomputable def max_row_two_norm {m n : ℕ}
    (L : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup (Set.range fun i : Fin m => Real.sqrt (∑ j : Fin n, (L i j) ^ 2))

@[blueprint "def:max-column-two-norm"
  (statement := /-- For a finite real matrix $R$, define $\|R\|_{1\to2}$ to be the maximum Euclidean norm of a column:
  \[
    \|R\|_{1\to2}=\max_j\left(\sum_i R_{ij}^2\right)^{1/2}.
  \] -/)
  (title := /-- The $1\to2$ matrix norm -/)
  (latexEnv := "definition")]
noncomputable def max_column_two_norm {m n : ℕ}
    (R : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup (Set.range fun j : Fin n => Real.sqrt (∑ i : Fin m, (R i j) ^ 2))

@[blueprint "def:approximate-factorization-norm"
  (statement := /-- For a workload $W\in\mathbb R^{k\times d}$ and $\alpha\ge0$, its $\alpha$-approximate factorization norm is
  \[
    \gamma_\alpha(W)=
    \inf\left\{\|L\|_{2\to\infty}\|R\|_{1\to2}:
    \ell\in\mathbb N,\ L\in\mathbb R^{k\times\ell},\
    R\in\mathbb R^{\ell\times d},\
    \|LR-W\|_{1\to\infty}\le\alpha\right\}.
  \] -/)
  (title := /-- Approximate factorization norm -/)
  (latexEnv := "definition")]
noncomputable def approximate_factorization_norm {k d : ℕ}
    (W : Matrix (Fin k) (Fin d) ℝ) (α : ℝ) : ℝ :=
  sInf {c : ℝ | ∃ (l : ℕ)
      (L : Matrix (Fin k) (Fin l) ℝ)
      (R : Matrix (Fin l) (Fin d) ℝ),
      max_entry_norm (L * R - W) ≤ α ∧
      c = max_row_two_norm L * max_column_two_norm R}

@[blueprint "def:privacy-scale"
  (statement := /-- Define the Gaussian privacy scale by
  \[
    c_{\varepsilon,\delta}=
    \frac{\sqrt{2\log(1.25/\delta)}}{\varepsilon}.
  \] -/)
  (title := /-- Gaussian privacy scale -/)
  (latexEnv := "definition")]
noncomputable def privacy_scale (ε δ : ℝ) : ℝ :=
  Real.sqrt (2 * Real.log (1.25 / δ)) / ε

@[blueprint "def:all-epsilon-privacy-scale"
  (statement := /-- For $\varepsilon,\delta\in\mathbb R$, define the all-$\varepsilon$ Gaussian privacy scale by
  \[
    c^*_{\varepsilon,\delta}
    =\frac{\sqrt{2\log(1.25/\delta)}}{\varepsilon}
      +\sqrt{\frac1\varepsilon}.
  \]
  For $0<\varepsilon\le1$ and $0<\delta\le1$ this is within an absolute
  constant factor of $c_{\varepsilon,\delta}$, whereas the second term
  supplies the Gaussian privacy-loss correction required when
  $\varepsilon>1$. -/)
  (title := /-- All-$\varepsilon$ Gaussian privacy scale -/)
  (latexEnv := "definition")]
noncomputable def all_epsilon_privacy_scale (ε δ : ℝ) : ℝ :=
  privacy_scale ε δ + Real.sqrt (ε⁻¹)

@[blueprint "def:is-isotropic-gaussian-vector"
  (statement := /-- A probability measure $\mu$ on $\mathbb R^d$ is the centered isotropic Gaussian law of scale $\sigma$ if every linear functional $a\cdot Z$ has law
  \[
    \mathcal N\!\left(0,\sigma^2\sum_i a_i^2\right).
  \]
  This characterization permits correlated linear images to be handled without choosing coordinates for a covariance operator. -/)
  (title := /-- Centered isotropic Gaussian vectors -/)
  (latexEnv := "definition")]
def is_isotropic_gaussian_vector {d : ℕ}
    (μ : Measure (Fin d → ℝ)) (σ : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
  ∀ a : Fin d → ℝ,
    Measure.map (fun z => ∑ i : Fin d, a i * z i) μ =
      gaussianReal 0
        (Real.toNNReal (σ ^ 2 * ∑ i : Fin d, (a i) ^ 2))

@[blueprint "def:has-uniform-linear-image-bound"
  (statement := /-- A probability law $\mu$ on $\mathbb R^d$ has the uniform linear-image bound with scale $\sigma$ if, for every $k\in\mathbb N$ and every matrix $L\in\mathbb R^{k\times d}$, the function $z\mapsto\|Lz\|_\infty$ is integrable and
  \[
    \mathbb E_{Z\sim\mu}\|LZ\|_\infty
    \le \sigma\|L\|_{2\to\infty}\sqrt{2\log(2k)}.
  \]
  The definition also requires $\mu$ to be a probability measure. -/)
  (title := /-- Uniform control of linear images of a noise law -/)
  (latexEnv := "definition")]
def has_uniform_linear_image_bound {d : ℕ}
    (μ : Measure (Fin d → ℝ)) (σ : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
  ∀ (k : ℕ) (L : Matrix (Fin k) (Fin d) ℝ),
    Integrable (fun z => ‖Matrix.mulVec L z‖) μ ∧
      (∫ z, ‖Matrix.mulVec L z‖ ∂μ) ≤
        σ * max_row_two_norm L *
          Real.sqrt (2 * Real.log (2 * (k : ℝ)))

@[blueprint "def:expected-workload-error"
  (statement := /-- For a workload $W$, graph $G$, and output law $\mu$, define the expected workload error to be
  \[
    \mathbb E_{Y\sim\mu}\left[
      \left\|Y-W\widetilde p_{G,s}\right\|_\infty
    \right].
  \] -/)
  (title := /-- Expected workload error -/)
  (latexEnv := "definition")]
noncomputable def expected_workload_error {n k : ℕ} (s : ℕ)
    (W : Matrix (Fin k) (Fin (blur_dimension n s)) ℝ)
    (G : graph_on n) (μ : Measure (Fin k → ℝ)) : ℝ :=
  ∫ y, ‖y - Matrix.mulVec W (compressed_blurry_degree_distribution s G)‖ ∂μ

@[blueprint "lem:compressed-blurry-degree-distribution-normalized"
  (statement := /-- Let $n,s\in\mathbb N$ satisfy $n>0$ and $s>0$, and let $G$ be a graph on $[n]$.  The compressed blurry degree distribution has unit total absolute mass:
  \[
    \sum_j\left|\widetilde p_{G,s}(j)\right|=1.
  \] -/)
  (proof := /-- For each degree $d$, the two randomized-rounding weights in \cref{def:rounding-weight} are nonnegative and sum to one.  The positivity of $s$ ensures that these two weights occur in the bins indexed by $\lfloor d/s\rfloor$ and $\lfloor d/s\rfloor+1$, both of which lie in the range specified by \cref{def:blur-dimension}.  Interchanging the two finite sums in \cref{def:compressed-blurry-degree-distribution} therefore gives total mass
  \[
    \frac1n\sum_{v\in[n]}1=1,
  \]
  where the last equality uses $n>0$.  Since every coordinate is nonnegative, replacing each coordinate by its absolute value leaves this sum unchanged. -/)
  (title := /-- Normalization of the compressed blurry distribution -/)
  (latexEnv := "lemma")]
lemma compressed_blurry_degree_distribution_normalized
    {n s : ℕ} (hn : 0 < n) (hs : 0 < s) (G : graph_on n) :
    ∑ j : Fin (blur_dimension n s),
      |compressed_blurry_degree_distribution s G j| = 1 := by
  classical
  have hs_real : (0 : ℝ) < (s : ℝ) := by
    exact_mod_cast hs
  have hweight_nonnegative (d j : ℕ) : 0 ≤ rounding_weight s d j := by
    unfold rounding_weight
    split_ifs
    · have hmod : ((d % s : ℕ) : ℝ) ≤ (s : ℝ) := by
        exact_mod_cast Nat.le_of_lt (Nat.mod_lt d hs)
      have hdiv : ((d % s : ℕ) : ℝ) / (s : ℝ) ≤ 1 :=
        (div_le_one hs_real).2 hmod
      linarith
    · positivity
    · positivity
  have hdegree_lt (v : Fin n) : G.degree v < n := by
    simpa using G.degree_lt_card_verts v
  have hindex_bound (d : ℕ) (hd : d < n) :
      d / s + 1 < blur_dimension n s := by
    unfold blur_dimension
    have hsle : s ≤ n + s - 1 := by
      rw [Nat.add_sub_assoc (by omega : 1 ≤ s) n]
      omega
    have hmul := Nat.lt_div_mul_self hs hsle
    have hx : n + s - 1 - s = n - 1 := by omega
    rw [hx] at hmul
    have hd_pred : d ≤ n - 1 := by omega
    have hq : d / s < (n + s - 1) / s :=
      (Nat.div_lt_iff_lt_mul hs).2 (lt_of_le_of_lt hd_pred hmul)
    exact Nat.add_lt_add_right hq 1
  have hweight_sum (d : ℕ) (hd : d < n) :
      ∑ j : Fin (blur_dimension n s), rounding_weight s d j = 1 := by
    let j₀ : Fin (blur_dimension n s) :=
      ⟨d / s, lt_trans (Nat.lt_succ_self _) (hindex_bound d hd)⟩
    let j₁ : Fin (blur_dimension n s) :=
      ⟨d / s + 1, hindex_bound d hd⟩
    have hj₀ (j : Fin (blur_dimension n s)) :
        (j : ℕ) = d / s ↔ j = j₀ := by
      simp [j₀, Fin.ext_iff]
    have hj₁ (j : Fin (blur_dimension n s)) :
        (j : ℕ) = d / s + 1 ↔ j = j₁ := by
      simp [j₁, Fin.ext_iff]
    have hne : j₀ ≠ j₁ := by
      intro h
      have hval := congrArg Fin.val h
      simp [j₀, j₁] at hval
    simp only [rounding_weight]
    simp_rw [hj₀, hj₁]
    calc
      (∑ x, if x = j₀ then 1 - ((d % s : ℕ) : ℝ) / (s : ℝ)
        else if x = j₁ then ((d % s : ℕ) : ℝ) / (s : ℝ) else 0) =
          ∑ x, ((if x = j₀ then 1 - ((d % s : ℕ) : ℝ) / (s : ℝ) else 0) +
            if x = j₁ then ((d % s : ℕ) : ℝ) / (s : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = j₀
        · subst x
          simp [hne]
        · simp [hx]
      _ = 1 := by
        rw [Finset.sum_add_distrib]
        simp
  have hcoordinate_nonnegative (j : Fin (blur_dimension n s)) :
      0 ≤ compressed_blurry_degree_distribution s G j := by
    rw [compressed_blurry_degree_distribution]
    exact mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun v _ => hweight_nonnegative (G.degree v) j)
  simp_rw [abs_of_nonneg (hcoordinate_nonnegative _)]
  simp only [compressed_blurry_degree_distribution]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [hweight_sum _ (hdegree_lt _)]
  simp [hn.ne']

@[blueprint "lem:finite-ssup-eq-pi-norm"
  (statement := /-- Let $I$ be a finite type and let $f:I\to\mathbb R$ be nonnegative.  Then the supremum of the finite range of $f$ equals the supremum norm of $f$:
  \[
    \sup_{i\in I} f(i)=\lVert f\rVert.
  \] -/)
  (proof := /-- Every value $f(i)$ is bounded above by the supremum norm of $f$, so the range supremum is at most that norm.  Conversely, the range supremum is nonnegative and bounds every $f(i)$ by the defining property of the supremum; the pointwise characterization of the finite-product norm then gives the reverse inequality. -/)
  (title := /-- A finite nonnegative supremum as a product norm -/)
  (latexEnv := "lemma")]
lemma finite_ssup_eq_pi_norm {I : Type} [Fintype I]
    (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) :
    sSup (Set.range f) = ‖f‖ := by
  apply le_antisymm
  · apply Real.sSup_le
    · rintro x ⟨i, rfl⟩
      simpa [Real.norm_eq_abs, abs_of_nonneg (hf i)] using norm_le_pi_norm f i
    · exact norm_nonneg f
  · rw [pi_norm_le_iff_of_nonneg (Real.sSup_nonneg fun x hx => by
      rcases hx with ⟨i, rfl⟩
      exact hf i)]
    intro i
    simpa [Real.norm_eq_abs, abs_of_nonneg (hf i)] using
      (le_csSup
        (show BddAbove (Set.range f) from ⟨‖f‖, by
          rintro x ⟨j, rfl⟩
          simpa [Real.norm_eq_abs, abs_of_nonneg (hf j)] using norm_le_pi_norm f j⟩)
        (Set.mem_range_self i))

@[blueprint "lem:max-row-two-norm-eq-pi-norm"
  (statement := /-- For every finite real matrix $L$, its maximum row Euclidean norm is the supremum norm of the function assigning to each row its Euclidean norm. -/)
  (proof := /-- Apply \cref{lem:finite-ssup-eq-pi-norm} to the nonnegative function of row Euclidean norms. -/)
  (title := /-- The maximum row norm as a finite product norm -/)
  (latexEnv := "lemma")]
lemma max_row_two_norm_eq_pi_norm {m n : ℕ}
    (L : Matrix (Fin m) (Fin n) ℝ) :
    max_row_two_norm L = ‖fun i => Real.sqrt (∑ j, (L i j) ^ 2)‖ := by
  exact finite_ssup_eq_pi_norm _ fun i => Real.sqrt_nonneg _

@[blueprint "lem:max-column-two-norm-eq-pi-norm"
  (statement := /-- For every finite real matrix $R$, its maximum column Euclidean norm is the supremum norm of the function assigning to each column its Euclidean norm. -/)
  (proof := /-- Apply \cref{lem:finite-ssup-eq-pi-norm} to the nonnegative function of column Euclidean norms. -/)
  (title := /-- The maximum column norm as a finite product norm -/)
  (latexEnv := "lemma")]
lemma max_column_two_norm_eq_pi_norm {m n : ℕ}
    (R : Matrix (Fin m) (Fin n) ℝ) :
    max_column_two_norm R = ‖fun j => Real.sqrt (∑ i, (R i j) ^ 2)‖ := by
  exact finite_ssup_eq_pi_norm _ fun j => Real.sqrt_nonneg _

@[blueprint "lem:max-entry-norm-eq-pi-norm"
  (statement := /-- For every finite real matrix $A$, its maximum absolute entry is the supremum norm of the function on pairs of row and column indices given by the absolute value of the corresponding entry. -/)
  (proof := /-- Apply \cref{lem:finite-ssup-eq-pi-norm} to the nonnegative function of absolute entry values. -/)
  (title := /-- The maximum entry norm as a finite product norm -/)
  (latexEnv := "lemma")]
lemma max_entry_norm_eq_pi_norm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    max_entry_norm A = ‖fun p : Fin m × Fin n => |A p.1 p.2|‖ := by
  exact finite_ssup_eq_pi_norm _ fun p => abs_nonneg _

@[blueprint "lem:max-row-two-norm-smul"
  (statement := /-- For every finite real matrix $L$ and scalar $c\in\mathbb R$,
  \[
    \lVert cL\rVert_{2\to\infty}=|c|\,\lVert L\rVert_{2\to\infty}.
  \] -/)
  (proof := /-- By \cref{lem:max-row-two-norm-eq-pi-norm}, the left side is a finite product norm.  Pull $c^2$ out of each squared row sum, use $\sqrt{c^2}=|c|$, and then use absolute homogeneity of the product norm. -/)
  (title := /-- Homogeneity of the maximum row norm -/)
  (latexEnv := "lemma")]
lemma max_row_two_norm_smul {m n : ℕ} (c : ℝ)
    (L : Matrix (Fin m) (Fin n) ℝ) :
    max_row_two_norm (c • L) = |c| * max_row_two_norm L := by
  rw [max_row_two_norm_eq_pi_norm, max_row_two_norm_eq_pi_norm]
  have h : (fun i => Real.sqrt (∑ j, ((c • L) i j) ^ 2)) =
      fun i => |c| * Real.sqrt (∑ j, (L i j) ^ 2) := by
    funext i
    change Real.sqrt (∑ j, (c * L i j) ^ 2) =
      |c| * Real.sqrt (∑ j, (L i j) ^ 2)
    rw [show (∑ j, (c * L i j) ^ 2) = c ^ 2 * ∑ j, (L i j) ^ 2 by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]]
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  rw [h]
  change ‖(|c| : ℝ) • (fun i => Real.sqrt (∑ j, (L i j) ^ 2))‖ = _
  rw [norm_smul]
  simp

@[blueprint "lem:max-column-two-norm-smul"
  (statement := /-- For every finite real matrix $R$ and scalar $c\in\mathbb R$,
  \[
    \lVert cR\rVert_{1\to2}=|c|\,\lVert R\rVert_{1\to2}.
  \] -/)
  (proof := /-- By \cref{lem:max-column-two-norm-eq-pi-norm}, the left side is a finite product norm.  Pull $c^2$ out of each squared column sum, use $\sqrt{c^2}=|c|$, and then use absolute homogeneity of the product norm. -/)
  (title := /-- Homogeneity of the maximum column norm -/)
  (latexEnv := "lemma")]
lemma max_column_two_norm_smul {m n : ℕ} (c : ℝ)
    (R : Matrix (Fin m) (Fin n) ℝ) :
    max_column_two_norm (c • R) = |c| * max_column_two_norm R := by
  rw [max_column_two_norm_eq_pi_norm, max_column_two_norm_eq_pi_norm]
  have h : (fun j => Real.sqrt (∑ i, ((c • R) i j) ^ 2)) =
      fun j => |c| * Real.sqrt (∑ i, (R i j) ^ 2) := by
    funext j
    change Real.sqrt (∑ i, (c * R i j) ^ 2) =
      |c| * Real.sqrt (∑ i, (R i j) ^ 2)
    rw [show (∑ i, (c * R i j) ^ 2) = c ^ 2 * ∑ i, (R i j) ^ 2 by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]]
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  rw [h]
  change ‖(|c| : ℝ) • (fun j => Real.sqrt (∑ i, (R i j) ^ 2))‖ = _
  rw [norm_smul]
  simp

@[blueprint "lem:max-row-two-norm-eq-zero"
  (statement := /-- A finite real matrix has maximum row Euclidean norm zero if and only if it is the zero matrix. -/)
  (proof := /-- By \cref{lem:max-row-two-norm-eq-pi-norm}, vanishing of the maximum row norm makes every row's sum of squares vanish.  Each individual square is nonnegative and bounded above by that sum, so every entry vanishes.  The converse follows directly. -/)
  (title := /-- Vanishing of the maximum row norm -/)
  (latexEnv := "lemma")]
lemma max_row_two_norm_eq_zero {m n : ℕ}
    (L : Matrix (Fin m) (Fin n) ℝ) :
    max_row_two_norm L = 0 ↔ L = 0 := by
  rw [max_row_two_norm_eq_pi_norm, norm_eq_zero]
  constructor
  · intro h
    ext i j
    have hs := congrArg (fun x : ℝ => x ^ 2) (congr_fun h i)
    have hsum : (∑ a, (L i a) ^ 2) = 0 := by
      simpa [Real.sq_sqrt (Finset.sum_nonneg fun a ha => sq_nonneg _)] using hs
    have hle : (L i j) ^ 2 ≤ ∑ a, (L i a) ^ 2 :=
      Finset.single_le_sum (fun a ha => sq_nonneg (L i a)) (Finset.mem_univ j)
    change L i j = 0
    nlinarith
  · rintro rfl
    ext i
    simp

@[blueprint "lem:max-column-two-norm-eq-zero"
  (statement := /-- A finite real matrix has maximum column Euclidean norm zero if and only if it is the zero matrix. -/)
  (proof := /-- By \cref{lem:max-column-two-norm-eq-pi-norm}, vanishing of the maximum column norm makes every column's sum of squares vanish.  Each individual square is nonnegative and bounded above by that sum, so every entry vanishes.  The converse follows directly. -/)
  (title := /-- Vanishing of the maximum column norm -/)
  (latexEnv := "lemma")]
lemma max_column_two_norm_eq_zero {m n : ℕ}
    (R : Matrix (Fin m) (Fin n) ℝ) :
    max_column_two_norm R = 0 ↔ R = 0 := by
  rw [max_column_two_norm_eq_pi_norm, norm_eq_zero]
  constructor
  · intro h
    ext i j
    have hs := congrArg (fun x : ℝ => x ^ 2) (congr_fun h j)
    have hsum : (∑ a, (R a j) ^ 2) = 0 := by
      simpa [Real.sq_sqrt (Finset.sum_nonneg fun a ha => sq_nonneg _)] using hs
    have hle : (R i j) ^ 2 ≤ ∑ a, (R a j) ^ 2 :=
      Finset.single_le_sum (fun a ha => sq_nonneg (R a j)) (Finset.mem_univ i)
    change R i j = 0
    nlinarith
  · rintro rfl
    ext j
    simp

@[blueprint "lem:factorization-balancing"
  (statement := /-- Let $L\in\mathbb R^{k\times\ell}$ and $R\in\mathbb R^{\ell\times d}$.  There are matrices $L'$ and $R'$ of the same respective shapes such that $L'R'=LR$, their row-norm/column-norm product is unchanged, and
  \[
    \lVert L'\rVert_{2\to\infty},\ \lVert R'\rVert_{1\to2}
    \le \sqrt{\lVert L\rVert_{2\to\infty}\lVert R\rVert_{1\to2}}.
  \] -/)
  (proof := /-- Write $a=\lVert L\rVert_{2\to\infty}$ and $b=\lVert R\rVert_{1\to2}$.  The identities \cref{lem:max-row-two-norm-eq-pi-norm, lem:max-column-two-norm-eq-pi-norm} show that $a,b\ge0$.  If $ab=0$, \cref{lem:max-row-two-norm-eq-zero, lem:max-column-two-norm-eq-zero} shows that $LR=0$, so take both new factors to be zero.  If $ab>0$, put $c=\sqrt{ab}$ and rescale the factors by $c/a$ and its reciprocal.  The product is unchanged, and \cref{lem:max-row-two-norm-smul, lem:max-column-two-norm-smul} shows that both new norms equal $c$. -/)
  (title := /-- Balancing the two norms of a factorization -/)
  (latexEnv := "lemma")]
lemma factorization_balancing {k d l : ℕ}
    (L : Matrix (Fin k) (Fin l) ℝ) (R : Matrix (Fin l) (Fin d) ℝ) :
    ∃ (L' : Matrix (Fin k) (Fin l) ℝ)
      (R' : Matrix (Fin l) (Fin d) ℝ),
      L' * R' = L * R ∧
      max_row_two_norm L' * max_column_two_norm R' =
        max_row_two_norm L * max_column_two_norm R ∧
      max_row_two_norm L' ≤ Real.sqrt
        (max_row_two_norm L * max_column_two_norm R) ∧
      max_column_two_norm R' ≤ Real.sqrt
        (max_row_two_norm L * max_column_two_norm R) := by
  classical
  let a := max_row_two_norm L
  let b := max_column_two_norm R
  have ha : 0 ≤ a := by
    dsimp [a]
    rw [max_row_two_norm_eq_pi_norm]
    positivity
  have hb : 0 ≤ b := by
    dsimp [b]
    rw [max_column_two_norm_eq_pi_norm]
    positivity
  by_cases hp : a * b = 0
  · rcases mul_eq_zero.mp hp with ha0 | hb0
    · have hL : L = 0 := (max_row_two_norm_eq_zero L).mp ha0
      have hzL : max_row_two_norm (0 : Matrix (Fin k) (Fin l) ℝ) = 0 :=
        (max_row_two_norm_eq_zero 0).mpr rfl
      have hzR : max_column_two_norm (0 : Matrix (Fin l) (Fin d) ℝ) = 0 :=
        (max_column_two_norm_eq_zero 0).mpr rfl
      refine ⟨0, 0, ?_, ?_, ?_, ?_⟩
      · simp [hL]
      · simp [hzL, hzR, a, b, hp]
      · simp [hzL, a, b, hp]
      · simp [hzR, a, b, hp]
    · have hR : R = 0 := (max_column_two_norm_eq_zero R).mp hb0
      have hzL : max_row_two_norm (0 : Matrix (Fin k) (Fin l) ℝ) = 0 :=
        (max_row_two_norm_eq_zero 0).mpr rfl
      have hzR : max_column_two_norm (0 : Matrix (Fin l) (Fin d) ℝ) = 0 :=
        (max_column_two_norm_eq_zero 0).mpr rfl
      refine ⟨0, 0, ?_, ?_, ?_, ?_⟩
      · simp [hR]
      · simp [hzL, hzR, a, b, hp]
      · simp [hzL, a, b, hp]
      · simp [hzR, a, b, hp]
  · have hp' : 0 < a * b := lt_of_le_of_ne (mul_nonneg ha hb) (Ne.symm hp)
    have ha' : 0 < a := pos_of_mul_pos_left hp' hb
    have hb' : 0 < b := pos_of_mul_pos_right hp' ha
    let c := Real.sqrt (a * b)
    let t := c / a
    have hc : 0 < c := Real.sqrt_pos.2 hp'
    have ht : 0 < t := div_pos hc ha'
    let L' : Matrix (Fin k) (Fin l) ℝ := t • L
    let R' : Matrix (Fin l) (Fin d) ℝ := t⁻¹ • R
    have hprod : L' * R' = L * R := by
      ext i j
      simp only [L', R', Matrix.mul_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro x hx
      change (t * L i x) * (t⁻¹ * R x j) = L i x * R x j
      field_simp [ne_of_gt ht]
    have hLn : max_row_two_norm L' = c := by
      change max_row_two_norm (t • L) = c
      rw [max_row_two_norm_smul, abs_of_pos ht]
      change t * a = c
      dsimp [t]
      field_simp [ne_of_gt ha']
    have hRn : max_column_two_norm R' = c := by
      change max_column_two_norm (t⁻¹ • R) = c
      rw [max_column_two_norm_smul, abs_of_pos (inv_pos.mpr ht)]
      change t⁻¹ * b = c
      dsimp [t]
      rw [inv_div]
      field_simp [ne_of_gt hc]
      nlinarith [Real.sq_sqrt (le_of_lt hp')]
    refine ⟨L', R', hprod, ?_, ?_, ?_⟩
    · rw [hLn, hRn]
      change c * c = a * b
      dsimp [c]
      rw [← pow_two, Real.sq_sqrt (le_of_lt hp')]
    · rw [hLn]
    · rw [hRn]

@[blueprint "lem:factorization-compression"
  (statement := /-- Let $k,d,\ell\in\mathbb N$, $L\in\mathbb R^{k\times\ell}$, and $R\in\mathbb R^{\ell\times d}$.  There are matrices $L'\in\mathbb R^{k\times(k+d)}$ and $R'\in\mathbb R^{(k+d)\times d}$ such that
  \[
    L'R'=LR,
    \qquad \lVert L'\rVert_{2\to\infty}=\lVert L\rVert_{2\to\infty},
    \qquad \lVert R'\rVert_{1\to2}=\lVert R\rVert_{1\to2}.
  \] -/)
  (proof := /-- Regard the rows of $L$ and the columns of $R$ as $k+d$ vectors in Euclidean space and form their Gram matrix.  Its positive semidefinite square root is itself a Gram factor with inner dimension $k+d$.  Splitting its rows and columns according to the two summands preserves all cross inner products and all squared vector norms.  The cross inner products give $L'R'=LR$, and the pointwise norm equalities give the asserted row- and column-norm equalities. -/)
  (title := /-- Compression of a Euclidean matrix factorization -/)
  (latexEnv := "lemma")]
lemma factorization_compression {k d l : ℕ}
    (L : Matrix (Fin k) (Fin l) ℝ) (R : Matrix (Fin l) (Fin d) ℝ) :
    ∃ (L' : Matrix (Fin k) (Fin (k + d)) ℝ)
      (R' : Matrix (Fin (k + d)) (Fin d) ℝ),
      L' * R' = L * R ∧
      max_row_two_norm L' = max_row_two_norm L ∧
      max_column_two_norm R' = max_column_two_norm R := by
  classical
  let e : (Fin k ⊕ Fin d) ≃ Fin (k + d) := finSumFinEquiv
  let v : Fin (k + d) → EuclideanSpace ℝ (Fin l) := fun a =>
    Sum.elim (fun i => WithLp.toLp 2 (L i))
      (fun j => WithLp.toLp 2 (fun b => R b j)) (e.symm a)
  let G : Matrix (Fin (k + d)) (Fin (k + d)) ℝ := Matrix.gram ℝ v
  letI : PartialOrder (Matrix (Fin (k + d)) (Fin (k + d)) ℝ) :=
    Matrix.instPartialOrder
  letI : StarOrderedRing (Matrix (Fin (k + d)) (Fin (k + d)) ℝ) :=
    Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Matrix (Fin (k + d)) (Fin (k + d)) ℝ) :=
    Matrix.instNonnegSpectrumClass
  let B : Matrix (Fin (k + d)) (Fin (k + d)) ℝ := CFC.sqrt G
  let L' : Matrix (Fin k) (Fin (k + d)) ℝ := fun i a => B (e (Sum.inl i)) a
  let R' : Matrix (Fin (k + d)) (Fin d) ℝ := fun a j => B a (e (Sum.inr j))
  have hG : 0 ≤ G := (Matrix.posSemidef_gram ℝ v).nonneg
  have hBB : B * B = G := by
    simpa [B] using CFC.sqrt_mul_sqrt_self G hG
  have hBsym (i j : Fin (k + d)) : B j i = B i j := by
    have h := (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg G)).isHermitian.apply i j
    simpa [B] using h
  have hprod : L' * R' = L * R := by
    ext i j
    calc
      (L' * R') i j = ∑ a : Fin (k + d),
          B (e (Sum.inl i)) a * B a (e (Sum.inr j)) := by
            simp [L', R', Matrix.mul_apply]
      _ = G (e (Sum.inl i)) (e (Sum.inr j)) := by
            rw [← Matrix.mul_apply, hBB]
      _ = (L * R) i j := by
            simp [G, v, Matrix.gram_apply, PiLp.inner_apply, Matrix.mul_apply, mul_comm]
  have hrow_sq (i : Fin k) :
      (∑ a : Fin (k + d), (L' i a) ^ 2) = ∑ a : Fin l, (L i a) ^ 2 := by
    calc
      (∑ a : Fin (k + d), (L' i a) ^ 2) =
          ∑ a : Fin (k + d), B (e (Sum.inl i)) a * B a (e (Sum.inl i)) := by
            apply Finset.sum_congr rfl
            intro a ha
            simp [L', pow_two, hBsym]
      _ = G (e (Sum.inl i)) (e (Sum.inl i)) := by
            rw [← Matrix.mul_apply, hBB]
      _ = ∑ a : Fin l, (L i a) ^ 2 := by
            simp [G, v, Matrix.gram_apply, PiLp.inner_apply, pow_two, mul_comm]
            rw [EuclideanSpace.norm_eq, ← pow_two, Real.sq_sqrt (by positivity)]
            simp [pow_two]
  have hcol_sq (j : Fin d) :
      (∑ a : Fin (k + d), (R' a j) ^ 2) = ∑ a : Fin l, (R a j) ^ 2 := by
    calc
      (∑ a : Fin (k + d), (R' a j) ^ 2) =
          ∑ a : Fin (k + d), B (e (Sum.inr j)) a * B a (e (Sum.inr j)) := by
            apply Finset.sum_congr rfl
            intro a ha
            simp [R', pow_two, hBsym]
      _ = G (e (Sum.inr j)) (e (Sum.inr j)) := by
            rw [← Matrix.mul_apply, hBB]
      _ = ∑ a : Fin l, (R a j) ^ 2 := by
            simp [G, v, Matrix.gram_apply, PiLp.inner_apply, pow_two, mul_comm]
            rw [EuclideanSpace.norm_eq, ← pow_two, Real.sq_sqrt (by positivity)]
            simp [pow_two]
  refine ⟨L', R', hprod, ?_, ?_⟩
  · unfold max_row_two_norm
    congr 1
    ext x
    simp only [Set.mem_range]
    constructor <;> rintro ⟨i, rfl⟩ <;> exact ⟨i, by rw [hrow_sq]⟩
  · unfold max_column_two_norm
    congr 1
    ext x
    simp only [Set.mem_range]
    constructor <;> rintro ⟨j, rfl⟩ <;> exact ⟨j, by rw [hcol_sq]⟩

@[blueprint "lem:approximate-factorization-attained"
  (statement := /-- Let $k,d\in\mathbb N$, let $W\in\mathbb R^{k\times d}$, and let $\alpha\in\mathbb R$ satisfy $\alpha\ge0$.  There exist $\ell\in\mathbb N$ and matrices $L\in\mathbb R^{k\times\ell}$ and $R\in\mathbb R^{\ell\times d}$ such that
  \[
    \|LR-W\|_{1\to\infty}\le\alpha
    \quad\text{and}\quad
    \|L\|_{2\to\infty}\|R\|_{1\to2}=\gamma_\alpha(W).
  \] -/)
  (proof := /-- Set $N=k+d$.  By \cref{lem:factorization-compression}, every admissible factorization has an $N$-dimensional factorization with the same product and the same two norms.  By \cref{lem:factorization-balancing}, it may moreover be rescaled, without changing its product or objective value, so that both norms are bounded by the square root of their product.  Fix an exact factorization of $W$ and a bound larger than its two norms and its objective's square root.  The identities in \cref{lem:max-entry-norm-eq-pi-norm, lem:max-row-two-norm-eq-pi-norm, lem:max-column-two-norm-eq-pi-norm} show that the approximation constraint and objective are continuous and that the set of $N$-dimensional admissible factors satisfying this bound is closed and bounded, hence compact.  The objective therefore attains a minimum on this nonempty set.  For any admissible factorization whose objective is below that of the fixed exact factorization, compression and balancing place an equal-valued factorization in the compact set; for every other admissible factorization, the compact-set minimum is already bounded by the fixed exact factorization's value.  Thus the compact-set minimum is the least element of the set defining \cref{def:approximate-factorization-norm}, and its factors give the required equality with the infimum. -/)
  (title := /-- Attainment of the approximate factorization norm -/)
  (latexEnv := "lemma")]
lemma approximate_factorization_attained {k d : ℕ}
    (W : Matrix (Fin k) (Fin d) ℝ) (α : ℝ) (hα : 0 ≤ α) :
    ∃ (l : ℕ)
      (L : Matrix (Fin k) (Fin l) ℝ)
      (R : Matrix (Fin l) (Fin d) ℝ),
      max_entry_norm (L * R - W) ≤ α ∧
      max_row_two_norm L * max_column_two_norm R =
        approximate_factorization_norm W α := by
  classical
  let I : Matrix (Fin d) (Fin d) ℝ := 1
  obtain ⟨L₀, R₀, hprod₀, hrow₀, hcol₀⟩ := factorization_compression W I
  have hWI : W * I = W := by
    simp [I]
  have hprod₀' : L₀ * R₀ = W := hprod₀.trans hWI
  let a₀ := max_row_two_norm L₀
  let b₀ := max_column_two_norm R₀
  let C₀ := a₀ * b₀
  have ha₀ : 0 ≤ a₀ := by
    dsimp [a₀]
    rw [max_row_two_norm_eq_pi_norm]
    positivity
  have hb₀ : 0 ≤ b₀ := by
    dsimp [b₀]
    rw [max_column_two_norm_eq_pi_norm]
    positivity
  have hC₀ : 0 ≤ C₀ := mul_nonneg ha₀ hb₀
  let B := max a₀ b₀ + Real.sqrt C₀ + 1
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  let ML : ((Fin k → Fin (k + d) → ℝ) × (Fin (k + d) → Fin d → ℝ)) →
      Matrix (Fin k) (Fin (k + d)) ℝ := fun x i j => x.1 i j
  let MR : ((Fin k → Fin (k + d) → ℝ) × (Fin (k + d) → Fin d → ℝ)) →
      Matrix (Fin (k + d)) (Fin d) ℝ := fun x i j => x.2 i j
  let F : ((Fin k → Fin (k + d) → ℝ) × (Fin (k + d) → Fin d → ℝ)) → ℝ :=
    fun x => max_row_two_norm (ML x) * max_column_two_norm (MR x)
  let K : Set ((Fin k → Fin (k + d) → ℝ) × (Fin (k + d) → Fin d → ℝ)) := {x |
    max_entry_norm (ML x * MR x - W) ≤ α ∧
    max_row_two_norm (ML x) ≤ B ∧
    max_column_two_norm (MR x) ≤ B}
  have hcont_entry : Continuous (fun x : ((Fin k → Fin (k + d) → ℝ) ×
      (Fin (k + d) → Fin d → ℝ)) => max_entry_norm (ML x * MR x - W)) := by
    simp_rw [max_entry_norm_eq_pi_norm]
    fun_prop
  have hcont_row : Continuous (fun x : ((Fin k → Fin (k + d) → ℝ) ×
      (Fin (k + d) → Fin d → ℝ)) => max_row_two_norm (ML x)) := by
    simp_rw [max_row_two_norm_eq_pi_norm]
    fun_prop
  have hcont_col : Continuous (fun x : ((Fin k → Fin (k + d) → ℝ) ×
      (Fin (k + d) → Fin d → ℝ)) => max_column_two_norm (MR x)) := by
    simp_rw [max_column_two_norm_eq_pi_norm]
    fun_prop
  have hcont_F : Continuous F := by
    dsimp [F]
    fun_prop
  have hK_closed : IsClosed K := by
    dsimp [K]
    change IsClosed ({x | max_entry_norm (ML x * MR x - W) ≤ α} ∩
      ({x | max_row_two_norm (ML x) ≤ B} ∩
      {x | max_column_two_norm (MR x) ≤ B}))
    exact (isClosed_le hcont_entry continuous_const).inter
      ((isClosed_le hcont_row continuous_const).inter
        (isClosed_le hcont_col continuous_const))
  have hK_bounded : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall
      (0 : (Fin k → Fin (k + d) → ℝ) × (Fin (k + d) → Fin d → ℝ))]
    refine ⟨B, ?_⟩
    intro x hx
    rcases hx with ⟨hxfeas, hxrow, hxcol⟩
    have hleft : ‖x.1‖ ≤ B := by
      rw [pi_norm_le_iff_of_nonneg hB]
      intro i
      rw [pi_norm_le_iff_of_nonneg hB]
      intro j
      rw [Real.norm_eq_abs]
      calc
        |x.1 i j| = Real.sqrt ((x.1 i j) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt (∑ q, (x.1 i q) ^ 2) := by
          exact Real.sqrt_le_sqrt
            (Finset.single_le_sum (fun q hq => sq_nonneg (x.1 i q)) (Finset.mem_univ j))
        _ ≤ max_row_two_norm (ML x) := by
          rw [max_row_two_norm_eq_pi_norm]
          simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), ML] using
            norm_le_pi_norm (fun i => Real.sqrt (∑ j, (ML x i j) ^ 2)) i
        _ ≤ B := hxrow
    have hright : ‖x.2‖ ≤ B := by
      rw [pi_norm_le_iff_of_nonneg hB]
      intro i
      rw [pi_norm_le_iff_of_nonneg hB]
      intro j
      rw [Real.norm_eq_abs]
      calc
        |x.2 i j| = Real.sqrt ((x.2 i j) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt (∑ q, (x.2 q j) ^ 2) := by
          exact Real.sqrt_le_sqrt
            (Finset.single_le_sum (fun q hq => sq_nonneg (x.2 q j)) (Finset.mem_univ i))
        _ ≤ max_column_two_norm (MR x) := by
          rw [max_column_two_norm_eq_pi_norm]
          simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), MR] using
            norm_le_pi_norm (fun j => Real.sqrt (∑ i, (MR x i j) ^ 2)) j
        _ ≤ B := hxcol
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    exact max_le hleft hright
  have hK_compact : IsCompact K :=
    Metric.isCompact_iff_isClosed_bounded.2 ⟨hK_closed, hK_bounded⟩
  let x₀ : (Fin k → Fin (k + d) → ℝ) × (Fin (k + d) → Fin d → ℝ) := (L₀, R₀)
  have hx₀ : x₀ ∈ K := by
    refine ⟨?_, ?_, ?_⟩
    · dsimp [x₀, ML, MR]
      rw [hprod₀', sub_self, max_entry_norm_eq_pi_norm]
      have hz : (fun p : Fin k × Fin d => |(0 : Matrix (Fin k) (Fin d) ℝ) p.1 p.2|) = 0 := by
        ext p
        simp
      rw [hz, norm_zero]
      exact hα
    · change a₀ ≤ B
      dsimp [B]
      nlinarith [le_max_left a₀ b₀, Real.sqrt_nonneg C₀]
    · change b₀ ≤ B
      dsimp [B]
      nlinarith [le_max_right a₀ b₀, Real.sqrt_nonneg C₀]
  obtain ⟨xₘ, hxₘ, hmin⟩ := hK_compact.exists_isMinOn ⟨x₀, hx₀⟩ hcont_F.continuousOn
  have hF₀ : F x₀ = C₀ := by
    rfl
  have hmin₀ : F xₘ ≤ C₀ := by
    rw [← hF₀]
    exact hmin hx₀
  have hleast : ∀ c ∈ {c : ℝ | ∃ (l : ℕ)
      (L : Matrix (Fin k) (Fin l) ℝ)
      (R : Matrix (Fin l) (Fin d) ℝ),
      max_entry_norm (L * R - W) ≤ α ∧
      c = max_row_two_norm L * max_column_two_norm R}, F xₘ ≤ c := by
    intro c hc
    rcases hc with ⟨l, L, R, hfeas, rfl⟩
    let q := max_row_two_norm L * max_column_two_norm R
    by_cases hq : q < C₀
    · obtain ⟨Lc, Rc, hprod_c, hrow_c, hcol_c⟩ := factorization_compression L R
      obtain ⟨Lb, Rb, hprod_b, hnorm_b, hLb, hRb⟩ := factorization_balancing Lc Rc
      let xb : (Fin k → Fin (k + d) → ℝ) × (Fin (k + d) → Fin d → ℝ) := (Lb, Rb)
      have hq_nonneg : 0 ≤ q := by
        dsimp [q]
        apply mul_nonneg
        · rw [max_row_two_norm_eq_pi_norm]
          positivity
        · rw [max_column_two_norm_eq_pi_norm]
          positivity
      have hsqrt : Real.sqrt q ≤ Real.sqrt C₀ :=
        Real.sqrt_le_sqrt (le_of_lt hq)
      have hsqrtB : Real.sqrt q ≤ B := by
        calc
          Real.sqrt q ≤ Real.sqrt C₀ := hsqrt
          _ ≤ B := by
            dsimp [B]
            nlinarith [le_max_left a₀ b₀, ha₀]
      have hxb : xb ∈ K := by
        refine ⟨?_, ?_, ?_⟩
        · dsimp [xb, ML, MR]
          rw [hprod_b, hprod_c]
          exact hfeas
        · dsimp [xb, ML]
          rw [hrow_c, hcol_c] at hLb
          exact hLb.trans hsqrtB
        · dsimp [xb, MR]
          rw [hrow_c, hcol_c] at hRb
          exact hRb.trans hsqrtB
      calc
        F xₘ ≤ F xb := hmin hxb
        _ = q := by
          dsimp [F, xb, ML, MR, q]
          rw [hnorm_b, hrow_c, hcol_c]
    · exact hmin₀.trans (le_of_not_gt hq)
  have hxₘ_set : F xₘ ∈ {c : ℝ | ∃ (l : ℕ)
      (L : Matrix (Fin k) (Fin l) ℝ)
      (R : Matrix (Fin l) (Fin d) ℝ),
      max_entry_norm (L * R - W) ≤ α ∧
      c = max_row_two_norm L * max_column_two_norm R} := by
    refine ⟨k + d, ML xₘ, MR xₘ, hxₘ.1, ?_⟩
    rfl
  have hinf : approximate_factorization_norm W α = F xₘ := by
    unfold approximate_factorization_norm
    exact (show IsLeast
      {c : ℝ | ∃ (l : ℕ)
        (L : Matrix (Fin k) (Fin l) ℝ)
        (R : Matrix (Fin l) (Fin d) ℝ),
        max_entry_norm (L * R - W) ≤ α ∧
        c = max_row_two_norm L * max_column_two_norm R}
      (F xₘ) from ⟨hxₘ_set, hleast⟩).csInf_eq
  refine ⟨k + d, ML xₘ, MR xₘ, hxₘ.1, ?_⟩
  rw [hinf]

@[blueprint "lem:linear-queries-blurry-gaussian-sum"
  (statement := /-- Let $d\in\mathbb N$, let $a\in\mathbb R^d$, and let $v\ge0$.  If the coordinates of $Z\in\mathbb R^d$ are independent centered Gaussian variables of variance $v$, then $\sum_i a_iZ_i$ is centered Gaussian with variance $v\sum_i a_i^2$. -/)
  (proof := /-- Compare characteristic functions.  Finite-product Fubini factors the characteristic function of the weighted sum into the product of the scalar Gaussian characteristic functions.  Their exponents add to $-vt^2\sum_i a_i^2/2$, which is exactly the characteristic function of the centered Gaussian with variance $v\sum_i a_i^2$.  Uniqueness of characteristic functions gives the measure identity. -/)
  (title := /-- Weighted sums of independent centered Gaussians -/)
  (latexEnv := "lemma")]
lemma linear_queries_blurry_gaussian_sum {d : ℕ} (a : Fin d → ℝ) (v : NNReal) :
    Measure.map (fun z : Fin d → ℝ => ∑ i, a i * z i)
        (Measure.pi fun _ : Fin d => gaussianReal 0 v) =
      gaussianReal 0 (Real.toNNReal ((v : ℝ) * ∑ i, (a i) ^ 2)) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun, integral_map]
  · simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial,
      Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul,
      Complex.exp_sum]
    have hprod := integral_fintype_prod_eq_prod
      (μ := fun _ : Fin d => gaussianReal 0 v)
      (f := fun i (x : ℝ) =>
        Complex.exp ((t : ℂ) * ((a i : ℂ) * (x : ℂ)) * Complex.I))
    rw [hprod]
    have hi (i : Fin d) :
        (∫ x : ℝ, Complex.exp
          ((t : ℂ) * ((a i : ℂ) * (x : ℂ)) * Complex.I) ∂gaussianReal 0 v) =
          charFun (gaussianReal 0 v) (t * a i) := by
      rw [charFun]
      congr 1
      funext x
      simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial,
        Complex.ofReal_mul]
      congr 1 <;> ring
    simp_rw [hi, charFun_gaussianReal]
    rw [← Complex.exp_sum]
    have hvsum : 0 ≤ (v : ℝ) * ∑ i, (a i) ^ 2 :=
      mul_nonneg v.coe_nonneg (Finset.sum_nonneg fun i hi => sq_nonneg (a i))
    rw [show (∑ i, (v : ℝ) * (a i) ^ 2) =
      (v : ℝ) * ∑ i, (a i) ^ 2 by rw [Finset.mul_sum]]
    simp only [Real.coe_toNNReal _ hvsum, Complex.ofReal_zero, zero_mul, zero_sub,
      Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_pow]
    congr 1
    push_cast
    simp only [mul_zero, zero_mul, zero_sub, div_eq_mul_inv]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · exact (Finset.measurable_fun_sum Finset.univ fun i _ =>
      measurable_const.mul (measurable_pi_apply i)).aemeasurable
  · fun_prop

@[blueprint "lem:linear-queries-blurry-gaussian-product-density"
  (statement := /-- Let $d\in\mathbb N$, let $m\in\mathbb R^d$, and let $v>0$.  The product of the one-dimensional Gaussian laws with means $m_i$ and common variance $v$ has, with respect to Lebesgue measure on $\mathbb R^d$, density equal to the product of their scalar Gaussian densities. -/)
  (proof := /-- Evaluate both measures on measurable rectangles.  The product-measure formula gives the product of the scalar Gaussian probabilities.  Express every scalar probability as the integral of its Gaussian density, use finite-dimensional Fubini to identify the product of these integrals with the integral of the product density over the rectangle, and invoke uniqueness of finite product measures. -/)
  (title := /-- Density of a finite product of Gaussian laws -/)
  (latexEnv := "lemma")]
lemma linear_queries_blurry_gaussian_product_density {d : ℕ}
    (m : Fin d → ℝ) (v : NNReal) (hv : v ≠ 0) :
    Measure.pi (fun i : Fin d => gaussianReal (m i) v) =
      volume.withDensity (fun x : Fin d → ℝ =>
        ENNReal.ofReal (∏ i, gaussianPDFReal (m i) v (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  simp_rw [gaussianReal_apply_eq_integral _ hv]
  let f : Fin d → ℝ → ℝ := fun i x =>
    (s i).indicator (gaussianPDFReal (m i) v) x
  have hf : ∀ i, Integrable (f i) := fun i =>
    (integrable_gaussianPDFReal (m i) v).indicator (hs i)
  have hfprod : Integrable (fun x : Fin d → ℝ => ∏ i, f i (x i))
      (Measure.pi fun _ : Fin d => volume) :=
    Integrable.fintype_prod hf
  have hfnn : ∀ x i, 0 ≤ f i x := by
    intro x i
    exact Set.indicator_nonneg (fun y hy => gaussianPDFReal_nonneg _ _ _) x
  have hind : (Set.univ.pi s).indicator
      (fun x : Fin d → ℝ =>
        ENNReal.ofReal (∏ i, gaussianPDFReal (m i) v (x i))) =
      (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
    funext x
    by_cases hx : ∀ i, x i ∈ s i
    · simp [Set.mem_univ_pi.mpr hx, f, hx]
    · have hnot : x ∉ Set.univ.pi s := by
        simpa [Set.mem_univ_pi] using hx
      simp only [Set.indicator, hnot, if_false, ENNReal.ofReal_eq_zero]
      push Not at hx
      obtain ⟨i, hi⟩ := hx
      have hpzero : ∏ j, f j (x j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [f, hi])
      rw [hpzero]
      simp
  rw [volume_pi]
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs), hind]
  rw [← ofReal_integral_eq_lintegral_ofReal hfprod
    (ae_of_all _ fun x => Finset.prod_nonneg fun i hi => hfnn (x i) i)]
  rw [integral_fintype_prod_eq_prod]
  have hint (i : Fin d) :
      (∫ x, f i x) = ∫ x in s i, gaussianPDFReal (m i) v x := by
    simp [f, integral_indicator, hs i]
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun i hi => integral_nonneg (fun x => hfnn x i))]
  simp_rw [hint]

@[blueprint "lem:linear-queries-blurry-density-privacy-bound"
  (statement := /-- Let $\mu$ and $\nu$ have densities $f$ and $g$ with respect to a common measure.  If $f\le cg$ off a measurable bad set $B$ and $\mu(B)\le\eta$, then, for every measurable set $S$, $\mu(S)\le c\nu(S)+\eta$. -/)
  (proof := /-- Decompose $S$ into its part outside $B$ and its part inside $B$.  On the first part, monotonicity of the lower integral and the pointwise density comparison bound the $\mu$-mass by $c$ times the corresponding $\nu$-mass, hence by $c\nu(S)$.  The second part has mass at most $\mu(B)\le\eta$.  Adding the two estimates gives the claim. -/)
  (title := /-- Privacy bound from a density ratio outside a bad set -/)
  (latexEnv := "lemma")]
lemma linear_queries_blurry_density_privacy_bound
    {α : Type} [MeasurableSpace α] (ρ : Measure α)
    (f g : α → ENNReal) (c η : ENNReal) (B : Set α)
    (hf : Measurable f) (hg : Measurable g) (hB : MeasurableSet B)
    (hfg : ∀ x ∉ B, f x ≤ c * g x)
    (hbad : ρ.withDensity f B ≤ η) :
    ∀ S, MeasurableSet S →
      ρ.withDensity f S ≤ c * ρ.withDensity g S + η := by
  intro S hS
  calc
    ρ.withDensity f S ≤ ρ.withDensity f (S \ B) + ρ.withDensity f B := by
      apply (measure_mono (show S ⊆ (S \ B) ∪ B by
        intro x hx
        by_cases hxb : x ∈ B <;> simp [hx, hxb])).trans
      exact measure_union_le _ _
    _ ≤ c * ρ.withDensity g S + η := add_le_add (by
      rw [withDensity_apply _ (hS.diff hB), withDensity_apply _ hS]
      calc
        (∫⁻ x in S \ B, f x ∂ρ) ≤ ∫⁻ x in S \ B, c * g x ∂ρ :=
          setLIntegral_mono (measurable_const.mul hg)
            (fun x hx => hfg x hx.2)
        _ = c * ∫⁻ x in S \ B, g x ∂ρ := by
          rw [lintegral_const_mul c hg]
        _ ≤ c * ∫⁻ x in S, g x ∂ρ :=
          mul_le_mul_left' (lintegral_mono_set (Set.diff_subset)) c) hbad

@[blueprint "lem:linear-queries-blurry-nested-gaussian-sum"
  (statement := /-- Let $a_{ij}$ be a finite rectangular array and let $v\ge0$.  Under the iterated product law of independent centered Gaussian variables of variance $v$, the sum $\sum_{i,j}a_{ij}Z_{ij}$ is centered Gaussian with variance $v\sum_{i,j}a_{ij}^2$. -/)
  (proof := /-- Apply the characteristic-function argument of \cref{lem:linear-queries-blurry-gaussian-sum} first inside each row and then across the finite product of rows.  The characteristic functions multiply, and their exponents add to $-vt^2\sum_{i,j}a_{ij}^2/2$, which is the characteristic function of the asserted centered Gaussian law. -/)
  (title := /-- Weighted sums under an iterated Gaussian product -/)
  (latexEnv := "lemma")]
lemma linear_queries_blurry_nested_gaussian_sum {n l : ℕ}
    (a : Fin n → Fin l → ℝ) (v : NNReal) :
    Measure.map (fun z : Fin n → Fin l → ℝ =>
        ∑ i, ∑ j, a i j * z i j)
        (Measure.pi fun _ : Fin n =>
          Measure.pi fun _ : Fin l => gaussianReal 0 v) =
      gaussianReal 0
        (Real.toNNReal ((v : ℝ) * ∑ i, ∑ j, (a i j) ^ 2)) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun, integral_map]
  · simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial,
      Complex.ofReal_sum, Complex.ofReal_mul]
    have hexp :
        (fun x : Fin n → Fin l → ℝ =>
          Complex.exp ((t : ℂ) *
            (∑ i, ∑ j, (a i j : ℂ) * (x i j : ℂ)) * Complex.I)) =
        fun x => ∏ i, Complex.exp ((t : ℂ) *
          (∑ j, (a i j : ℂ) * (x i j : ℂ)) * Complex.I) := by
      funext x
      rw [← Complex.exp_sum]
      congr 1
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [hexp]
    have hprod := integral_fintype_prod_eq_prod
      (μ := fun _ : Fin n =>
        Measure.pi fun _ : Fin l => gaussianReal 0 v)
      (f := fun i (x : Fin l → ℝ) =>
        Complex.exp ((t : ℂ) *
          (∑ j, (a i j : ℂ) * (x j : ℂ)) * Complex.I))
    rw [hprod]
    have hi (i : Fin n) :
        (∫ x : Fin l → ℝ, Complex.exp
          ((t : ℂ) * (∑ j, (a i j : ℂ) * (x j : ℂ)) * Complex.I)
          ∂Measure.pi fun _ : Fin l => gaussianReal 0 v) =
          charFun
            (gaussianReal 0
              (Real.toNNReal ((v : ℝ) * ∑ j, (a i j) ^ 2))) t := by
      rw [← linear_queries_blurry_gaussian_sum (a i) v, charFun, integral_map]
      · congr 1
        funext x
        simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial,
          Complex.ofReal_sum, Complex.ofReal_mul]
      · exact (Finset.measurable_fun_sum Finset.univ fun j _ =>
          measurable_const.mul (measurable_pi_apply j)).aemeasurable
      · fun_prop
    simp_rw [hi, charFun_gaussianReal]
    rw [← Complex.exp_sum]
    have hvsum : 0 ≤ (v : ℝ) * ∑ i, ∑ j, (a i j) ^ 2 :=
      mul_nonneg v.coe_nonneg
        (Finset.sum_nonneg fun i hi =>
          Finset.sum_nonneg fun j hj => sq_nonneg (a i j))
    simp only [Real.coe_toNNReal _ hvsum, Complex.ofReal_zero, zero_mul,
      zero_sub, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_pow]
    congr 1
    push_cast
    simp only [mul_zero, zero_mul, zero_sub, div_eq_mul_inv]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi_mem
    have hvi : 0 ≤ (v : ℝ) * ∑ j, (a i j) ^ 2 :=
      mul_nonneg v.coe_nonneg
        (Finset.sum_nonneg fun j hj => sq_nonneg (a i j))
    rw [Real.coe_toNNReal _ hvi]
    push_cast
    rw [Finset.mul_sum]
  · exact (Finset.measurable_fun_sum Finset.univ fun i _ =>
      Finset.measurable_fun_sum Finset.univ fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).comp
          (measurable_pi_apply i))).aemeasurable
  · fun_prop

@[blueprint "lem:linear-queries-blurry-nested-gaussian-product-density"
  (statement := /-- Let $m_{ij}$ be a finite rectangular array and let $v>0$.  The iterated product of the scalar Gaussian laws with means $m_{ij}$ and variance $v$ has, relative to the iterated product of Lebesgue measures, density $\prod_{i,j}\varphi_{m_{ij},v}(x_{ij})$. -/)
  (proof := /-- By \cref{lem:linear-queries-blurry-gaussian-product-density}, each row law has the product Gaussian density.  Evaluate the outer product law on measurable rectangles, express each row probability by its density integral, and apply finite-product Fubini to identify the product of those integrals with the integral of the product density.  Uniqueness of finite product measures gives the claimed identity. -/)
  (title := /-- Density of an iterated finite product of Gaussian laws -/)
  (latexEnv := "lemma")]
lemma linear_queries_blurry_nested_gaussian_product_density {n l : ℕ}
    (m : Fin n → Fin l → ℝ) (v : NNReal) (hv : v ≠ 0) :
    Measure.pi (fun i : Fin n =>
        Measure.pi fun j : Fin l => gaussianReal (m i j) v) =
      (Measure.pi fun _ : Fin n => (volume : Measure (Fin l → ℝ))).withDensity
        (fun x : Fin n → Fin l → ℝ =>
          ENNReal.ofReal (∏ i, ∏ j, gaussianPDFReal (m i j) v (x i j))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  simp_rw [linear_queries_blurry_gaussian_product_density (v := v) (hv := hv)]
  let f : Fin n → (Fin l → ℝ) → ℝ := fun i x =>
    (s i).indicator (fun y => ∏ j, gaussianPDFReal (m i j) v (y j)) x
  have hrow (i : Fin n) :
      Integrable (fun x : Fin l → ℝ =>
        ∏ j, gaussianPDFReal (m i j) v (x j)) := by
    exact Integrable.fintype_prod fun j =>
      integrable_gaussianPDFReal (m i j) v
  have hf : ∀ i, Integrable (f i) := fun i => (hrow i).indicator (hs i)
  have hfprod : Integrable (fun x : Fin n → Fin l → ℝ => ∏ i, f i (x i))
      (Measure.pi fun _ : Fin n => (volume : Measure (Fin l → ℝ))) :=
    Integrable.fintype_prod hf
  have hfnn : ∀ x i, 0 ≤ f i x := by
    intro x i
    exact Set.indicator_nonneg
      (fun y hy => Finset.prod_nonneg fun j hj =>
        gaussianPDFReal_nonneg _ _ _) x
  have hind : (Set.univ.pi s).indicator
      (fun x : Fin n → Fin l → ℝ =>
        ENNReal.ofReal (∏ i, ∏ j, gaussianPDFReal (m i j) v (x i j))) =
      (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
    funext x
    by_cases hx : ∀ i, x i ∈ s i
    · simp [Set.mem_univ_pi.mpr hx, f, hx]
    · have hnot : x ∉ Set.univ.pi s := by
        simpa [Set.mem_univ_pi] using hx
      simp only [Set.indicator, hnot, if_false, ENNReal.ofReal_eq_zero]
      push Not at hx
      obtain ⟨i, hi⟩ := hx
      have hpzero : ∏ j, f j (x j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [f, hi])
      rw [hpzero]
      simp
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs), hind]
  rw [← ofReal_integral_eq_lintegral_ofReal hfprod
    (ae_of_all _ fun x => Finset.prod_nonneg fun i hi => hfnn (x i) i)]
  rw [integral_fintype_prod_eq_prod]
  have hint (i : Fin n) :
      (∫ x, f i x) =
        ∫ x in s i, ∏ j, gaussianPDFReal (m i j) v (x j) := by
    simp [f, integral_indicator, hs i]
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun i hi => integral_nonneg (fun x => hfnn x i))]
  simp_rw [hint, withDensity_apply _ (hs _)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((hrow i).mono_measure Measure.restrict_le_self)
    (ae_of_all _ fun x => Finset.prod_nonneg fun j hj =>
      gaussianPDFReal_nonneg _ _ _)]

@[blueprint "lem:linear-queries-blurry-nested-gaussian-product-privacy-one-sided"
  (statement := /-- Let $m,m'$ be finite rectangular arrays and let $v>0$.  Put $q=v^{-1}\sum_{i,j}(m_{ij}-m'_{ij})^2$.  If a Gaussian variable with mean $q/2$ and variance $q$ exceeds $\varepsilon$ with probability at most $\delta$, then every measurable event under the iterated product Gaussian law with mean $m$ has probability at most $e^\varepsilon$ times its probability under the law with mean $m'$, plus $\delta$. -/)
  (proof := /-- Use the iterated product densities from \cref{lem:linear-queries-blurry-nested-gaussian-product-density}.  Their log-density ratio is the affine privacy-loss functional $L(x)=(2v)^{-1}\sum_{i,j}((x_{ij}-m'_{ij})^2-(x_{ij}-m_{ij})^2)$.  Translating the law with mean $m$ to centered coordinates and applying \cref{lem:linear-queries-blurry-nested-gaussian-sum} shows that $L$ has Gaussian law with mean $q/2$ and variance $q$.  The assumed tail bound controls the set where $L>\varepsilon$; off that set the density ratio is at most $e^\varepsilon$.  Apply \cref{lem:linear-queries-blurry-density-privacy-bound}. -/)
  (title := /-- One-sided privacy of iterated shifted Gaussian products -/)
  (latexEnv := "lemma")]
lemma linear_queries_blurry_nested_gaussian_product_privacy_one_sided
    {n l : ℕ} (m m' : Fin n → Fin l → ℝ)
    (v : NNReal) (hv : v ≠ 0) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 ≤ δ)
    (htail : gaussianReal
      (((v : ℝ)⁻¹ * ∑ i, ∑ j, (m i j - m' i j) ^ 2) / 2)
      (Real.toNNReal ((v : ℝ)⁻¹ *
        ∑ i, ∑ j, (m i j - m' i j) ^ 2))
      (Set.Ioi ε) ≤ ENNReal.ofReal δ) :
    ∀ S, MeasurableSet S →
      (Measure.pi fun i : Fin n =>
        Measure.pi fun j : Fin l => gaussianReal (m i j) v) S ≤
        ENNReal.ofReal (Real.exp ε) *
          (Measure.pi fun i : Fin n =>
            Measure.pi fun j : Fin l => gaussianReal (m' i j) v) S +
          ENNReal.ofReal δ := by
  intro S hS
  rw [linear_queries_blurry_nested_gaussian_product_density m v hv,
    linear_queries_blurry_nested_gaussian_product_density m' v hv]
  let ρ : Measure (Fin n → Fin l → ℝ) :=
    Measure.pi fun _ : Fin n => (volume : Measure (Fin l → ℝ))
  let f : (Fin n → Fin l → ℝ) → ENNReal := fun x =>
    ENNReal.ofReal (∏ i, ∏ j, gaussianPDFReal (m i j) v (x i j))
  let g : (Fin n → Fin l → ℝ) → ENNReal := fun x =>
    ENNReal.ofReal (∏ i, ∏ j, gaussianPDFReal (m' i j) v (x i j))
  let L : (Fin n → Fin l → ℝ) → ℝ := fun x =>
    (v : ℝ)⁻¹ / 2 *
      ∑ i, ∑ j, ((x i j - m' i j) ^ 2 - (x i j - m i j) ^ 2)
  let B : Set (Fin n → Fin l → ℝ) := {x | ε < L x}
  apply linear_queries_blurry_density_privacy_bound ρ f g
    (ENNReal.ofReal (Real.exp ε)) (ENNReal.ofReal δ) B
  · dsimp [f]
    fun_prop
  · dsimp [g]
    fun_prop
  · dsimp [B, L]
    exact measurableSet_lt measurable_const (by fun_prop)
  · intro x hx
    dsimp [f, g, B] at hx ⊢
    push Not at hx
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg ε)]
    apply ENNReal.ofReal_le_ofReal
    simp_rw [gaussianPDFReal_def]
    simp_rw [Finset.prod_mul_distrib]
    simp_rw [← Real.exp_sum]
    have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    have hid :
        (∑ i, ∑ j, -(x i j - m i j) ^ 2 / (2 * (v : ℝ))) -
            ∑ i, ∑ j, -(x i j - m' i j) ^ 2 / (2 * (v : ℝ)) =
          L x := by
      dsimp [L]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      field_simp
      ring
    have hexp :
        Real.exp (∑ i, ∑ j,
            -(x i j - m i j) ^ 2 / (2 * (v : ℝ))) ≤
          Real.exp ε *
            Real.exp (∑ i, ∑ j,
              -(x i j - m' i j) ^ 2 / (2 * (v : ℝ))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    apply (mul_le_mul_of_nonneg_left hexp
      (Finset.prod_nonneg fun i hi =>
        Finset.prod_nonneg fun j hj =>
          inv_nonneg.mpr (Real.sqrt_nonneg _))).trans_eq
    ring
  · dsimp [f]
    rw [← linear_queries_blurry_nested_gaussian_product_density m v hv]
    let μ₀ : Measure (Fin n → Fin l → ℝ) :=
      Measure.pi fun _ : Fin n =>
        Measure.pi fun _ : Fin l => gaussianReal 0 v
    have hshift :
        Measure.map
          (fun z : Fin n → Fin l → ℝ => fun i j => m i j + z i j) μ₀ =
          Measure.pi fun i : Fin n =>
            Measure.pi fun j : Fin l => gaussianReal (m i j) v := by
      dsimp [μ₀]
      rw [Measure.pi_map_pi
        (f := fun i (x : Fin l → ℝ) => fun j => m i j + x j)]
      · congr 1
        funext i
        rw [Measure.pi_map_pi]
        · congr 1
          funext j
          rw [gaussianReal_map_const_add]
          simp
        · intro j
          exact (measurable_const.add measurable_id).aemeasurable
      · intro i
        exact (measurable_pi_lambda _ fun j =>
          measurable_const.add (measurable_pi_apply j)).aemeasurable
    have hmap :
        Measure.map L
            (Measure.pi fun i : Fin n =>
              Measure.pi fun j : Fin l => gaussianReal (m i j) v) =
          gaussianReal
            (((v : ℝ)⁻¹ * ∑ i, ∑ j, (m i j - m' i j) ^ 2) / 2)
            (Real.toNNReal ((v : ℝ)⁻¹ *
              ∑ i, ∑ j, (m i j - m' i j) ^ 2)) := by
      rw [← hshift, Measure.map_map (by dsimp [L]; fun_prop) (by fun_prop)]
      have hL :
          L ∘ (fun z : Fin n → Fin l → ℝ =>
            fun i j => m i j + z i j) =
          fun z =>
            ((v : ℝ)⁻¹ * ∑ i, ∑ j, (m i j - m' i j) ^ 2) / 2 +
              ∑ i, ∑ j, (v : ℝ)⁻¹ *
                (m i j - m' i j) * z i j := by
        funext z
        dsimp [L]
        rw [Finset.mul_sum]
        calc
          (∑ i, (v : ℝ)⁻¹ / 2 *
              ∑ j, ((m i j + z i j - m' i j) ^ 2 -
                (m i j + z i j - m i j) ^ 2)) =
              ∑ i, ∑ j,
                ((v : ℝ)⁻¹ * (m i j - m' i j) ^ 2 / 2 +
                  (v : ℝ)⁻¹ * (m i j - m' i j) * z i j) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
          _ = (∑ i, ∑ j,
                (v : ℝ)⁻¹ * (m i j - m' i j) ^ 2 / 2) +
              ∑ i, ∑ j,
                (v : ℝ)⁻¹ * (m i j - m' i j) * z i j := by
                  simp_rw [Finset.sum_add_distrib]
          _ = ((v : ℝ)⁻¹ * ∑ i, ∑ j,
                (m i j - m' i j) ^ 2) / 2 +
              ∑ i, ∑ j,
                (v : ℝ)⁻¹ * (m i j - m' i j) * z i j := by
                  congr 1
                  simp only [div_eq_mul_inv]
                  rw [mul_comm ((v : ℝ)⁻¹ *
                    ∑ i, ∑ j, (m i j - m' i j) ^ 2) (2 : ℝ)⁻¹,
                    Finset.mul_sum, Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [Finset.mul_sum, Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
      rw [hL]
      rw [show Measure.map
          (fun z : Fin n → Fin l → ℝ =>
            ((v : ℝ)⁻¹ * ∑ i, ∑ j, (m i j - m' i j) ^ 2) / 2 +
              ∑ i, ∑ j, (v : ℝ)⁻¹ *
                (m i j - m' i j) * z i j) μ₀ =
          Measure.map
            (fun y => ((v : ℝ)⁻¹ *
              ∑ i, ∑ j, (m i j - m' i j) ^ 2) / 2 + y)
            (Measure.map
              (fun z : Fin n → Fin l → ℝ =>
                ∑ i, ∑ j, ((v : ℝ)⁻¹ *
                  (m i j - m' i j)) * z i j) μ₀) by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl]
      dsimp [μ₀]
      rw [linear_queries_blurry_nested_gaussian_sum,
        gaussianReal_map_const_add]
      simp only [zero_add]
      congr 1
      apply congrArg Real.toNNReal
      have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      field_simp
    calc
      (Measure.pi fun i : Fin n =>
          Measure.pi fun j : Fin l => gaussianReal (m i j) v) B =
          Measure.map L
            (Measure.pi fun i : Fin n =>
              Measure.pi fun j : Fin l => gaussianReal (m i j) v)
            (Set.Ioi ε) := by
              rw [Measure.map_apply (by dsimp [L]; fun_prop) measurableSet_Ioi]
              rfl
      _ = gaussianReal
            (((v : ℝ)⁻¹ * ∑ i, ∑ j, (m i j - m' i j) ^ 2) / 2)
            (Real.toNNReal ((v : ℝ)⁻¹ *
              ∑ i, ∑ j, (m i j - m' i j) ^ 2))
            (Set.Ioi ε) := by rw [hmap]
      _ ≤ ENNReal.ofReal δ := htail
  · exact hS

@[blueprint "lem:linear-queries-blurry-nested-gaussian-product-private"
  (statement := /-- Under the hypotheses of the one-sided iterated Gaussian privacy estimate, the two iterated product Gaussian laws are $(\varepsilon,\delta)$-indistinguishable. -/)
  (proof := /-- Apply \cref{lem:linear-queries-blurry-nested-gaussian-product-privacy-one-sided} in both orders.  Interchanging the two mean arrays leaves the sum of squared coordinate displacements, and therefore the Gaussian tail hypothesis, unchanged. -/)
  (title := /-- Privacy of shifted iterated Gaussian products -/)
  (latexEnv := "lemma")]
lemma linear_queries_blurry_nested_gaussian_product_private {n l : ℕ}
    (m m' : Fin n → Fin l → ℝ)
    (v : NNReal) (hv : v ≠ 0) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 ≤ δ)
    (htail : gaussianReal
      (((v : ℝ)⁻¹ * ∑ i, ∑ j, (m i j - m' i j) ^ 2) / 2)
      (Real.toNNReal ((v : ℝ)⁻¹ *
        ∑ i, ∑ j, (m i j - m' i j) ^ 2))
      (Set.Ioi ε) ≤ ENNReal.ofReal δ) :
    distribution_indistinguishable ε δ
      (Measure.pi fun i : Fin n =>
        Measure.pi fun j : Fin l => gaussianReal (m i j) v)
      (Measure.pi fun i : Fin n =>
        Measure.pi fun j : Fin l => gaussianReal (m' i j) v) := by
  unfold distribution_indistinguishable
  intro S hS
  constructor
  · exact linear_queries_blurry_nested_gaussian_product_privacy_one_sided
      m m' v hv ε δ hε hδ htail S hS
  · have hsum :
        (∑ i, ∑ j, (m' i j - m i j) ^ 2) =
          ∑ i, ∑ j, (m i j - m' i j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    apply linear_queries_blurry_nested_gaussian_product_privacy_one_sided
      m' m v hv ε δ hε hδ
    · simpa [hsum] using htail
    · exact hS

@[blueprint "lem:linear-queries-blurry-rounding-mass"
  (statement := /-- Let $n,s,d$ be positive-range natural numbers with $s>0$ and $d<n$.  The rounding weights $w_s(d,j)$ in the $d_{\mathrm{blur}}(n,s)$ bins are nonnegative and have total mass one. -/)
  (proof := /-- The two possible bins are $\lfloor d/s\rfloor$ and $\lfloor d/s\rfloor+1$; both lie below the dimension from \cref{def:blur-dimension}.  By \cref{def:rounding-weight}, their weights are $1-(d\bmod s)/s$ and $(d\bmod s)/s$, which are nonnegative because $d\bmod s<s$, and all other weights vanish.  Their sum is one. -/)
  (title := /-- Mass and positivity of the rounding weights -/)
  (latexEnv := "lemma")]
lemma linear_queries_blurry_rounding_mass {n s d : ℕ}
    (hs : 0 < s) (hd : d < n) :
    (∀ j : Fin (blur_dimension n s), 0 ≤ rounding_weight s d j) ∧
      ∑ j : Fin (blur_dimension n s), rounding_weight s d j = 1 := by
  have hs_real : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hindex_bound (x : ℕ) (hx : x < n) :
      x / s + 1 < blur_dimension n s := by
    unfold blur_dimension
    have hsle : s ≤ n + s - 1 := by
      rw [Nat.add_sub_assoc (by omega : 1 ≤ s) n]
      omega
    have hmul := Nat.lt_div_mul_self hs hsle
    have hxsub : n + s - 1 - s = n - 1 := by omega
    rw [hxsub] at hmul
    have hxpred : x ≤ n - 1 := by omega
    have hq : x / s < (n + s - 1) / s :=
      (Nat.div_lt_iff_lt_mul hs).2 (lt_of_le_of_lt hxpred hmul)
    exact Nat.add_lt_add_right hq 1
  constructor
  · intro j
    unfold rounding_weight
    split_ifs
    · have hmod : ((d % s : ℕ) : ℝ) ≤ (s : ℝ) := by
        exact_mod_cast Nat.le_of_lt (Nat.mod_lt d hs)
      have hdiv : ((d % s : ℕ) : ℝ) / (s : ℝ) ≤ 1 :=
        (div_le_one hs_real).2 hmod
      linarith
    · positivity
    · positivity
  · let j₀ : Fin (blur_dimension n s) :=
      ⟨d / s, lt_trans (Nat.lt_succ_self _) (hindex_bound d hd)⟩
    let j₁ : Fin (blur_dimension n s) :=
      ⟨d / s + 1, hindex_bound d hd⟩
    have hj₀ (j : Fin (blur_dimension n s)) :
        (j : ℕ) = d / s ↔ j = j₀ := by
      simp [j₀, Fin.ext_iff]
    have hj₁ (j : Fin (blur_dimension n s)) :
        (j : ℕ) = d / s + 1 ↔ j = j₁ := by
      simp [j₁, Fin.ext_iff]
    have hne : j₀ ≠ j₁ := by
      intro h
      have hval := congrArg Fin.val h
      simp [j₀, j₁] at hval
    simp only [rounding_weight]
    simp_rw [hj₀, hj₁]
    calc
      (∑ x, if x = j₀ then 1 - ((d % s : ℕ) : ℝ) / (s : ℝ)
        else if x = j₁ then ((d % s : ℕ) : ℝ) / (s : ℝ) else 0) =
          ∑ x, ((if x = j₀ then
              1 - ((d % s : ℕ) : ℝ) / (s : ℝ) else 0) +
            if x = j₁ then ((d % s : ℕ) : ℝ) / (s : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h : x = j₀
        · subst x
          simp [hne]
        · simp [h]
      _ = 1 := by
        rw [Finset.sum_add_distrib]
        simp

@[blueprint "lem:linear-queries-blurry-rounding-step"
  (statement := /-- Let $s>0$ and let both $d$ and $d+1$ be valid degrees below $n$.  The $\ell_1$-distance between their randomized-rounding weight vectors is exactly $2/s$. -/)
  (proof := /-- Use \cref{def:rounding-weight} and split according to whether adding one crosses a multiple of $s$.  Without a crossing, the two common nonzero bins transfer mass $1/s$ from the lower bin to the upper bin.  At a crossing, the lower bin has residual mass $1/s$ and the upper bin gains that mass.  Thus in either case the two absolute coordinate changes sum to $2/s$.  The bin bounds follow from \cref{def:blur-dimension}. -/)
  (title := /-- Lipschitz bound for one rounding step -/)
  (latexEnv := "lemma")]
lemma linear_queries_blurry_rounding_step {n s d : ℕ}
    (hs : 0 < s) (hd : d + 1 < n) :
    ∑ j : Fin (blur_dimension n s),
        |rounding_weight s d j - rounding_weight s (d + 1) j| =
      2 / (s : ℝ) := by
  have hindex_bound (x : ℕ) (hx : x < n) :
      x / s + 1 < blur_dimension n s := by
    unfold blur_dimension
    have hsle : s ≤ n + s - 1 := by
      rw [Nat.add_sub_assoc (by omega : 1 ≤ s) n]
      omega
    have hmul := Nat.lt_div_mul_self hs hsle
    have hxsub : n + s - 1 - s = n - 1 := by omega
    rw [hxsub] at hmul
    have hxpred : x ≤ n - 1 := by omega
    have hq : x / s < (n + s - 1) / s :=
      (Nat.div_lt_iff_lt_mul hs).2 (lt_of_le_of_lt hxpred hmul)
    exact Nat.add_lt_add_right hq 1
  have hdlt : d < n := by omega
  by_cases hsone : s = 1
  · subst s
    let j₀ : Fin (blur_dimension n 1) :=
      ⟨d, by simpa using
        (lt_trans (Nat.lt_succ_self (d / 1)) (hindex_bound d hdlt))⟩
    let j₁ : Fin (blur_dimension n 1) :=
      ⟨d + 1, by simpa using
        (lt_trans (Nat.lt_succ_self ((d + 1) / 1))
          (hindex_bound (d + 1) hd))⟩
    have hj₀ (j : Fin (blur_dimension n 1)) :
        (j : ℕ) = d ↔ j = j₀ := by simp [j₀, Fin.ext_iff]
    have hj₁ (j : Fin (blur_dimension n 1)) :
        (j : ℕ) = d + 1 ↔ j = j₁ := by simp [j₁, Fin.ext_iff]
    have hne : j₀ ≠ j₁ := by
      intro h
      have := congrArg Fin.val h
      simp [j₀, j₁] at this
    have hne' : j₁ ≠ j₀ := Ne.symm hne
    have hsum_two (A B C D : ℝ) :
        (∑ x : Fin (blur_dimension n 1),
          |(if x = j₀ then A else if x = j₁ then B else 0) -
            (if x = j₀ then C else if x = j₁ then D else 0)|) =
          |A - C| + |B - D| := by
      have hp (x : Fin (blur_dimension n 1)) :
          |(if x = j₀ then A else if x = j₁ then B else 0) -
            (if x = j₀ then C else if x = j₁ then D else 0)| =
          (if x = j₀ then |A - C| else 0) +
            (if x = j₁ then |B - D| else 0) := by
        by_cases hx₀ : x = j₀
        · subst x
          simp [hne]
        · by_cases hx₁ : x = j₁
          · subst x
            simp [hx₀]
          · simp [hx₀, hx₁]
      simp_rw [hp, Finset.sum_add_distrib]
      simp
    simp only [rounding_weight, Nat.div_one, Nat.mod_one, Nat.cast_zero,
      zero_div, sub_zero]
    simp_rw [hj₀, hj₁]
    rw [show
      (∑ x : Fin (blur_dimension n 1),
        |(if x = j₀ then (1 : ℝ) else if x = j₁ then 0 else 0) -
          (if x = j₁ then 1
            else if (x : ℕ) = d + 1 + 1 then 0 else 0)|) =
      ∑ x,
        |(if x = j₀ then (1 : ℝ) else if x = j₁ then 0 else 0) -
          (if x = j₀ then (0 : ℝ) else if x = j₁ then 1 else 0)| by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hx₀ : x = j₀
        · subst x
          simp [hne] <;> rfl
        · by_cases hx₁ : x = j₁ <;>
            simp [hne, hne', hx₀, hx₁] <;> rfl]
    rw [hsum_two]
    norm_num
  · have hslt : 1 < s := by omega
    have hone_div : 1 / s = 0 := Nat.div_eq_of_lt hslt
    have hone_mod : 1 % s = 1 := Nat.mod_eq_of_lt hslt
    let q₀ : Fin (blur_dimension n s) :=
      ⟨d / s, lt_trans (Nat.lt_succ_self _) (hindex_bound d hdlt)⟩
    let q₁ : Fin (blur_dimension n s) :=
      ⟨d / s + 1, hindex_bound d hdlt⟩
    have hq₀ (j : Fin (blur_dimension n s)) :
        (j : ℕ) = d / s ↔ j = q₀ := by simp [q₀, Fin.ext_iff]
    have hq₁ (j : Fin (blur_dimension n s)) :
        (j : ℕ) = d / s + 1 ↔ j = q₁ := by simp [q₁, Fin.ext_iff]
    have hne : q₀ ≠ q₁ := by
      intro h
      have := congrArg Fin.val h
      simp [q₀, q₁] at this
    have hsum_two (A B C D : ℝ) :
        (∑ x : Fin (blur_dimension n s),
          |(if x = q₀ then A else if x = q₁ then B else 0) -
            (if x = q₀ then C else if x = q₁ then D else 0)|) =
          |A - C| + |B - D| := by
      have hp (x : Fin (blur_dimension n s)) :
          |(if x = q₀ then A else if x = q₁ then B else 0) -
            (if x = q₀ then C else if x = q₁ then D else 0)| =
          (if x = q₀ then |A - C| else 0) +
            (if x = q₁ then |B - D| else 0) := by
        by_cases hx₀ : x = q₀
        · subst x
          simp [hne]
        · by_cases hx₁ : x = q₁
          · subst x
            simp [hx₀]
          · simp [hx₀, hx₁]
      simp_rw [hp, Finset.sum_add_distrib]
      simp
    by_cases hcross : s ≤ d % s + 1
    · have hrem : d % s + 1 = s := by
        have hlt := Nat.mod_lt d hs
        omega
      have hdiv : (d + 1) / s = d / s + 1 := by
        rw [Nat.add_div hs]
        simp [hone_div, hone_mod, hcross]
      have hmod : (d + 1) % s = 0 := by
        rw [Nat.add_mod, hone_mod, hrem, Nat.mod_self]
      simp only [rounding_weight, hdiv, hmod, Nat.cast_zero, zero_div,
        sub_zero]
      simp_rw [hq₀, hq₁]
      have hsreal : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
      have hcast : (((d % s : ℕ) : ℝ) / (s : ℝ)) =
          1 - 1 / (s : ℝ) := by
        have : ((d % s : ℕ) : ℝ) + 1 = (s : ℝ) := by
          exact_mod_cast hrem
        field_simp
        linarith
      rw [hcast]
      rw [show
        (∑ x : Fin (blur_dimension n s),
          |(if x = q₀ then 1 - (1 - 1 / (s : ℝ))
              else if x = q₁ then 1 - 1 / (s : ℝ) else 0) -
            (if x = q₁ then 1
              else if (x : ℕ) = d / s + 1 + 1 then 0 else 0)|) =
        ∑ x,
          |(if x = q₀ then 1 / (s : ℝ)
              else if x = q₁ then 1 - 1 / (s : ℝ) else 0) -
            (if x = q₀ then 0 else if x = q₁ then 1 else 0)| by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hx₀ : x = q₀
          · subst x
            simp [hne]
          · by_cases hx₁ : x = q₁
            · subst x
              simp [hx₀]
            · simp [hx₀, hx₁]]
      rw [hsum_two]
      have hnonneg : 0 ≤ (1 : ℝ) / s := by positivity
      simp only [sub_zero]
      rw [abs_of_nonneg hnonneg]
      have hnonpos : 1 - 1 / (s : ℝ) - 1 ≤ 0 := by linarith
      rw [abs_of_nonpos hnonpos]
      ring
    · have hlt : d % s + 1 < s := by omega
      have hdiv : (d + 1) / s = d / s := by
        rw [Nat.add_div hs]
        simp [hone_div, hone_mod, hcross]
      have hmod : (d + 1) % s = d % s + 1 := by
        rw [Nat.add_mod, hone_mod, Nat.mod_eq_of_lt hlt]
      simp only [rounding_weight, hdiv, hmod]
      simp_rw [hq₀, hq₁]
      have hsreal : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
      rw [hsum_two]
      have habs₀ :
          |(1 - ((d % s : ℕ) : ℝ) / (s : ℝ)) -
              (1 - (((d % s + 1 : ℕ) : ℝ) / (s : ℝ)))| =
            1 / (s : ℝ) := by
        rw [show (((d % s + 1 : ℕ) : ℝ)) =
          ((d % s : ℕ) : ℝ) + 1 by norm_num]
        have heq :
            (1 - ((d % s : ℕ) : ℝ) / (s : ℝ)) -
                (1 - (((d % s : ℕ) : ℝ) + 1) / (s : ℝ)) =
              1 / (s : ℝ) := by
                field_simp
                norm_num
        rw [heq, abs_of_nonneg (by positivity)]
      have habs₁ :
          |((d % s : ℕ) : ℝ) / (s : ℝ) -
              (((d % s + 1 : ℕ) : ℝ) / (s : ℝ))| =
            1 / (s : ℝ) := by
        rw [show (((d % s + 1 : ℕ) : ℝ)) =
          ((d % s : ℕ) : ℝ) + 1 by norm_num]
        have heq :
            ((d % s : ℕ) : ℝ) / (s : ℝ) -
                (((d % s : ℕ) : ℝ) + 1) / (s : ℝ) =
              -(1 / (s : ℝ)) := by
                field_simp
                norm_num
        rw [heq, abs_neg, abs_of_nonneg (by positivity)]
      rw [habs₀, habs₁]
      ring

@[blueprint "lem:linear-queries-blurry-rounding-adjacent"
  (statement := /-- For valid degrees $d,e<n$ with $|d-e|\le1$ and $s>0$, the $\ell_1$-distance between their randomized-rounding weight vectors is at most $2/s$. -/)
  (proof := /-- If $d=e$, the distance is zero.  Otherwise the two natural-number inequalities imply that one degree is the successor of the other.  Apply \cref{lem:linear-queries-blurry-rounding-step}; reversing the two vectors does not change the coordinatewise absolute differences. -/)
  (title := /-- Adjacent degrees have close rounding laws -/)
  (latexEnv := "lemma")]
lemma linear_queries_blurry_rounding_adjacent {n s d e : ℕ}
    (hs : 0 < s) (hd : d < n) (he : e < n)
    (hde : d ≤ e + 1 ∧ e ≤ d + 1) :
    ∑ j : Fin (blur_dimension n s),
        |rounding_weight s d j - rounding_weight s e j| ≤
      2 / (s : ℝ) := by
  by_cases h : d = e
  · subst e
    simp
    positivity
  · have hcases : e = d + 1 ∨ d = e + 1 := by omega
    rcases hcases with hsucc | hsucc
    · subst e
      exact (linear_queries_blurry_rounding_step hs he).le
    · subst d
      rw [show (∑ j : Fin (blur_dimension n s),
          |rounding_weight s (e + 1) j - rounding_weight s e j|) =
          ∑ j : Fin (blur_dimension n s), |rounding_weight s e j -
            rounding_weight s (e + 1) j| by
        apply Finset.sum_congr rfl
        intro j hj
        rw [abs_sub_comm]]
      exact (linear_queries_blurry_rounding_step hs hd).le

@[blueprint "lem:linear-queries-blurry-mulvec-l1-bound"
  (statement := /-- For a finite real matrix $R$ and vector $x$, the squared Euclidean norm of $Rx$ is at most $\|R\|_{1\to2}^2\|x\|_1^2$. -/)
  (proof := /-- For each row, apply the weighted Cauchy--Schwarz inequality with weights $|x_j|$ to obtain $(\sum_jR_{ij}x_j)^2\le(\sum_j|x_j|)(\sum_j|x_j|R_{ij}^2)$.  Sum over rows and interchange the finite sums.  By \cref{lem:max-column-two-norm-eq-pi-norm}, every column squared norm is at most $\|R\|_{1\to2}^2$.  Multiplication by the nonnegative weights $|x_j|$ gives the result. -/)
  (title := /-- The maximum column norm controls the $1$-to-$2$ action -/)
  (latexEnv := "lemma")]
lemma linear_queries_blurry_mulvec_l1_bound {l d : ℕ}
    (R : Matrix (Fin l) (Fin d) ℝ) (x : Fin d → ℝ) :
    ∑ i, (Matrix.mulVec R x i) ^ 2 ≤
      (max_column_two_norm R) ^ 2 * (∑ j, |x j|) ^ 2 := by
  let S : ℝ := ∑ j, |x j|
  have hS : 0 ≤ S := Finset.sum_nonneg fun j hj => abs_nonneg _
  have hrow (i : Fin l) :
      (∑ j, R i j * x j) ^ 2 ≤
        S * ∑ j, |x j| * (R i j) ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun j hj => abs_nonneg (x j))
      (fun j hj => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    intro j hj
    rw [mul_pow]
    nlinarith [sq_abs (x j), sq_nonneg (R i j)]
  have hcols (j : Fin d) :
      ∑ i, (R i j) ^ 2 ≤ (max_column_two_norm R) ^ 2 := by
    rw [max_column_two_norm_eq_pi_norm]
    have hnorm :
        Real.sqrt (∑ i, (R i j) ^ 2) ≤
          ‖fun j => Real.sqrt (∑ i, (R i j) ^ 2)‖ :=
      by
        simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
          (norm_le_pi_norm
            (fun j : Fin d => Real.sqrt (∑ i, (R i j) ^ 2)) j)
    have hsum_nonneg : 0 ≤ ∑ i, (R i j) ^ 2 :=
      Finset.sum_nonneg fun i hi => sq_nonneg _
    have hnorm_nonneg :
        0 ≤ ‖fun j => Real.sqrt (∑ i, (R i j) ^ 2)‖ := norm_nonneg _
    have hsquare := mul_self_le_mul_self (Real.sqrt_nonneg _) hnorm
    rw [Real.mul_self_sqrt hsum_nonneg] at hsquare
    simpa [pow_two] using hsquare
  calc
    (∑ i, (Matrix.mulVec R x i) ^ 2) =
        ∑ i, (∑ j, R i j * x j) ^ 2 := by
          rfl
    _ ≤ ∑ i, S * ∑ j, |x j| * (R i j) ^ 2 :=
      Finset.sum_le_sum fun i hi => hrow i
    _ = S * ∑ j, |x j| * ∑ i, (R i j) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      apply congrArg (fun y : ℝ => S * y)
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum]
    _ ≤ S * ∑ j, |x j| * (max_column_two_norm R) ^ 2 := by
      gcongr with j hj
      exact hcols j
    _ = (max_column_two_norm R) ^ 2 * (∑ j, |x j|) ^ 2 := by
      dsimp [S]
      rw [← Finset.sum_mul]
      ring

@[blueprint "lem:linear-queries-blurry-neighbor-degree"
  (statement := /-- Suppose graphs $G,H$ are node-neighboring with distinguished node $k$.  For every $i\ne k$, their degrees at $i$ differ by at most one. -/)
  (proof := /-- Away from $k$, the two neighbor sets of $i$ agree at every vertex except possibly $k$.  Hence each neighbor finset is contained in the other with $k$ adjoined.  Monotonicity of cardinality and the one-element bound for insertion give both degree inequalities. -/)
  (title := /-- Degrees away from the changed node differ by one -/)
  (latexEnv := "lemma")]
lemma linear_queries_blurry_neighbor_degree {n : ℕ}
    (G H : graph_on n)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (k i : Fin n)
    (hN : ∀ u v : Fin n, u ≠ k → v ≠ k →
      (G.Adj u v ↔ H.Adj u v))
    (hik : i ≠ k) :
    G.degree i ≤ H.degree i + 1 ∧ H.degree i ≤ G.degree i + 1 := by
  classical
  have hsubGH : G.neighborFinset i ⊆ insert k (H.neighborFinset i) := by
    intro v hv
    by_cases hvk : v = k
    · simp [hvk]
    · have hadjG : G.Adj i v := by simpa using hv
      have hadjH : H.Adj i v := (hN i v hik hvk).mp hadjG
      simp [hadjH]
  have hsubHG : H.neighborFinset i ⊆ insert k (G.neighborFinset i) := by
    intro v hv
    by_cases hvk : v = k
    · simp [hvk]
    · have hadjH : H.Adj i v := by simpa using hv
      have hadjG : G.Adj i v := (hN i v hik hvk).mpr hadjH
      simp [hadjG]
  constructor
  · calc
      G.degree i = (G.neighborFinset i).card := rfl
      _ ≤ (insert k (H.neighborFinset i)).card :=
        Finset.card_le_card hsubGH
      _ ≤ (H.neighborFinset i).card + 1 :=
        Finset.card_insert_le k (H.neighborFinset i)
      _ = H.degree i + 1 := rfl
  · calc
      H.degree i = (H.neighborFinset i).card := rfl
      _ ≤ (insert k (G.neighborFinset i)).card :=
        Finset.card_le_card hsubHG
      _ ≤ (G.neighborFinset i).card + 1 :=
        Finset.card_insert_le k (G.neighborFinset i)
      _ = G.degree i + 1 := rfl

@[blueprint "lem:linear-queries-blurry-message-sensitivity"
  (statement := /-- Let $G,H$ be node-neighboring graphs on $[n]$, let $s>0$, and let $R$ be a finite matrix.  The sum, over nodes and output coordinates, of the squared changes in the noiseless local messages $R w_s(\deg(i),\cdot)$ is at most $4\|R\|_{1\to2}^2(1+n/s^2)$. -/)
  (proof := /-- Choose the distinguished node $k$ from node-neighboringness.  At $k$, \cref{lem:linear-queries-blurry-rounding-mass} and positivity bound the $\ell_1$-distance of the two probability vectors by two.  At every other node, \cref{lem:linear-queries-blurry-neighbor-degree} and \cref{lem:linear-queries-blurry-rounding-adjacent} bound it by $2/s$.  Apply \cref{lem:linear-queries-blurry-mulvec-l1-bound} to every local difference and sum.  Bounding the distinguished term by $4\|R\|_{1\to2}^2$ and all $n$ terms by the additional $4\|R\|_{1\to2}^2/s^2$ gives the displayed estimate. -/)
  (title := /-- Sensitivity of all noiseless local linear messages -/)
  (latexEnv := "lemma")]
lemma linear_queries_blurry_message_sensitivity {n s l : ℕ}
    (hs : 0 < s)
    (R : Matrix (Fin l) (Fin (blur_dimension n s)) ℝ)
    (G H : graph_on n)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : node_neighboring G H) :
    ∑ i : Fin n, ∑ j : Fin l,
        (Matrix.mulVec R
            (fun b => rounding_weight s (G.degree i) b) j -
          Matrix.mulVec R
            (fun b => rounding_weight s (H.degree i) b) j) ^ 2 ≤
      4 * (max_column_two_norm R) ^ 2 *
        (1 + (n : ℝ) / (s : ℝ) ^ 2) := by
  classical
  rcases hGH with ⟨k, hk⟩
  have hdegG (i : Fin n) : G.degree i < n := by
    simpa using G.degree_lt_card_verts i
  have hdegH (i : Fin n) : H.degree i < n := by
    simpa using H.degree_lt_card_verts i
  have hRnonneg : 0 ≤ (max_column_two_norm R) ^ 2 := sq_nonneg _
  have hsreal : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hlocal (i : Fin n) :
      ∑ j : Fin l,
          (Matrix.mulVec R
              (fun b => rounding_weight s (G.degree i) b) j -
            Matrix.mulVec R
              (fun b => rounding_weight s (H.degree i) b) j) ^ 2 ≤
        4 / (s : ℝ) ^ 2 * (max_column_two_norm R) ^ 2 +
          if i = k then 4 * (max_column_two_norm R) ^ 2 else 0 := by
    let x : Fin (blur_dimension n s) → ℝ := fun b =>
      rounding_weight s (G.degree i) b -
        rounding_weight s (H.degree i) b
    have hrewrite :
        (∑ j : Fin l,
          (Matrix.mulVec R
              (fun b => rounding_weight s (G.degree i) b) j -
            Matrix.mulVec R
              (fun b => rounding_weight s (H.degree i) b) j) ^ 2) =
          ∑ j : Fin l, (Matrix.mulVec R x j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      simp only [Matrix.mulVec, dotProduct, x, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    rw [hrewrite]
    refine (linear_queries_blurry_mulvec_l1_bound R x).trans ?_
    by_cases hik : i = k
    · subst i
      have hmG := linear_queries_blurry_rounding_mass hs (hdegG k)
      have hmH := linear_queries_blurry_rounding_mass hs (hdegH k)
      have hl1 :
          ∑ b : Fin (blur_dimension n s), |x b| ≤ 2 := by
        calc
          (∑ b : Fin (blur_dimension n s), |x b|) ≤
              ∑ b : Fin (blur_dimension n s),
                (rounding_weight s (G.degree k) b +
                rounding_weight s (H.degree k) b) := by
            apply Finset.sum_le_sum
            intro b hb
            dsimp [x]
            exact abs_sub_le_iff.mpr
              ⟨by linarith [hmG.1 b, hmH.1 b],
                by linarith [hmG.1 b, hmH.1 b]⟩
          _ = 2 := by
            rw [Finset.sum_add_distrib, hmG.2, hmH.2]
            norm_num
      simp only [if_pos rfl]
      have hsq :
          (∑ b : Fin (blur_dimension n s), |x b|) ^ 2 ≤ 4 := by
        have hxnonneg :
            0 ≤ ∑ b : Fin (blur_dimension n s), |x b| :=
          Finset.sum_nonneg fun b hb => abs_nonneg _
        nlinarith
      calc
        (max_column_two_norm R) ^ 2 * (∑ b, |x b|) ^ 2 ≤
            (max_column_two_norm R) ^ 2 * 4 :=
          mul_le_mul_of_nonneg_left hsq hRnonneg
        _ ≤ 4 / (s : ℝ) ^ 2 * (max_column_two_norm R) ^ 2 +
            4 * (max_column_two_norm R) ^ 2 := by
              have hbase :
                  0 ≤ 4 / (s : ℝ) ^ 2 *
                    (max_column_two_norm R) ^ 2 := by positivity
              nlinarith
    · have hadj := linear_queries_blurry_neighbor_degree G H k i hk hik
      have hl1 :
          ∑ b : Fin (blur_dimension n s), |x b| ≤
            2 / (s : ℝ) := by
        exact linear_queries_blurry_rounding_adjacent hs
          (hdegG i) (hdegH i) hadj
      simp only [if_neg hik, add_zero]
      have hxnonneg :
          0 ≤ ∑ b : Fin (blur_dimension n s), |x b| :=
        Finset.sum_nonneg fun b hb => abs_nonneg _
      have hbound_nonneg : 0 ≤ 2 / (s : ℝ) := by positivity
      have hsq :
          (∑ b : Fin (blur_dimension n s), |x b|) ^ 2 ≤
            (2 / (s : ℝ)) ^ 2 :=
        (sq_le_sq₀ hxnonneg hbound_nonneg).mpr hl1
      calc
        (max_column_two_norm R) ^ 2 * (∑ b, |x b|) ^ 2 ≤
            (max_column_two_norm R) ^ 2 * (2 / (s : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hRnonneg
        _ = 4 / (s : ℝ) ^ 2 * (max_column_two_norm R) ^ 2 := by ring
  calc
    (∑ i : Fin n, ∑ j : Fin l,
        (Matrix.mulVec R
            (fun b => rounding_weight s (G.degree i) b) j -
          Matrix.mulVec R
            (fun b => rounding_weight s (H.degree i) b) j) ^ 2) ≤
      ∑ i : Fin n,
        (4 / (s : ℝ) ^ 2 * (max_column_two_norm R) ^ 2 +
          if i = k then 4 * (max_column_two_norm R) ^ 2 else 0) :=
        Finset.sum_le_sum fun i hi => hlocal i
    _ = (n : ℝ) * (4 / (s : ℝ) ^ 2 *
          (max_column_two_norm R) ^ 2) +
        4 * (max_column_two_norm R) ^ 2 := by
      rw [Finset.sum_add_distrib]
      simp
    _ = 4 * (max_column_two_norm R) ^ 2 *
        (1 + (n : ℝ) / (s : ℝ) ^ 2) := by ring

@[blueprint "lem:linear-queries-blurry-calibration-tail"
  (statement := /-- Let $0<\varepsilon\le 1$, $0<\delta\le 1$, and $q\ge 0$.  If
  [
    q\le \frac{1}{16c_{\varepsilon,\delta}^2},
  ]
  then a Gaussian random variable with mean $q/2$ and variance $q$ exceeds
  $\varepsilon$ with probability at most $\delta$. -/)
  (proof := /-- Apply the exponential-moment bound to the Gaussian law with parameter
  $t=8\log(1.25/\delta)/\varepsilon$.  The definition of
  $c_{\varepsilon,\delta}$ in \cref{def:privacy-scale} turns the hypothesis
  into $q\le \varepsilon^2/(32\log(1.25/\delta))$.  The two positive
  terms in the Chernoff exponent are then at most $\varepsilon/8$ and
  $\log(1.25/\delta)$, respectively.  Finally,
  $2/9<\log(5/4)\le\log(1.25/\delta)$ and $\varepsilon\le1$ make the
  resulting exponent at most $\log\delta$. -/)
  (title := /-- A calibrated Gaussian privacy-loss tail bound -/)
  (latexEnv := "lemma")]
lemma linear_queries_blurry_calibration_tail
    (ε δ q : ℝ) (hε : 0 < ε) (hε_one : ε ≤ 1)
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) (hq_nonneg : 0 ≤ q)
    (hq : q ≤ (16 * (privacy_scale ε δ) ^ 2)⁻¹) :
    gaussianReal (q / 2) (Real.toNNReal q) (Set.Ioi ε) ≤
      ENNReal.ofReal δ := by
  let L : ℝ := Real.log (1.25 / δ)
  have hratio : 1 < (1.25 : ℝ) / δ :=
    (lt_div_iff₀ hδ).2 (by nlinarith)
  have hL_pos : 0 < L := by
    exact Real.log_pos hratio
  have hq' : q ≤ ε ^ 2 / (32 * L) := by
    calc
      q ≤ (16 * (privacy_scale ε δ) ^ 2)⁻¹ := hq
      _ = ε ^ 2 / (32 * L) := by
        dsimp [L]
        unfold privacy_scale
        rw [div_pow, Real.sq_sqrt (by positivity)]
        field_simp
        ring
  have hq_mul : 32 * L * q ≤ ε ^ 2 :=
    by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (le_div_iff₀ (by positivity : 0 < 32 * L)).mp hq'
  let t : ℝ := 8 * L / ε
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have hterm_one : q * t / 2 ≤ ε / 8 := by
    dsimp [t]
    rw [show q * (8 * L / ε) / 2 = (4 * L * q) / ε by ring]
    exact (div_le_iff₀ hε).2 (by nlinarith)
  have hterm_two : q * t ^ 2 / 2 ≤ L := by
    dsimp [t]
    rw [show q * (8 * L / ε) ^ 2 / 2 =
        (32 * L ^ 2 * q) / ε ^ 2 by ring]
    apply (div_le_iff₀ (sq_pos_of_pos hε)).2
    nlinarith [mul_le_mul_of_nonneg_left hq_mul hL_pos.le]
  have hlog_const : (2 : ℝ) / 9 < Real.log 1.25 := by
    have h := Real.lt_log_one_add_of_pos (x := (1 : ℝ) / 4) (by norm_num)
    norm_num at h ⊢
    exact h
  have hlog_delta : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ_one
  have hL_eq : L = Real.log 1.25 - Real.log δ := by
    dsimp [L]
    rw [Real.log_div (by norm_num : (1.25 : ℝ) ≠ 0) hδ.ne']
  have hexponent :
      -t * ε + q / 2 * t + q * t ^ 2 / 2 ≤ Real.log δ := by
    have htε : t * ε = 8 * L := by
      dsimp [t]
      field_simp
    nlinarith
  have hchernoff :=
    measure_ge_le_exp_mul_mgf
      (μ := gaussianReal (q / 2) (Real.toNNReal q))
      (X := id) (t := t) ε ht_pos.le
      (integrable_exp_mul_gaussianReal t)
  have hreal :
      (gaussianReal (q / 2) (Real.toNNReal q) (Set.Ioi ε)).toReal ≤ δ := by
    calc
      (gaussianReal (q / 2) (Real.toNNReal q) (Set.Ioi ε)).toReal ≤
          (gaussianReal (q / 2) (Real.toNNReal q)
            {x | ε ≤ id x}).toReal := by
              apply ENNReal.toReal_mono (measure_ne_top _ _)
              exact measure_mono (by
                intro x hx
                simpa only [Set.mem_Ioi, Set.mem_setOf_eq] using hx.le)
      _ ≤ Real.exp (-t * ε) *
          mgf id (gaussianReal (q / 2) (Real.toNNReal q)) t := hchernoff
      _ = Real.exp (-t * ε + q / 2 * t + q * t ^ 2 / 2) := by
        rw [mgf_id_gaussianReal, ← Real.exp_add]
        congr 1
        rw [Real.coe_toNNReal q hq_nonneg]
        ring
      _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hexponent
      _ = δ := Real.exp_log hδ
  rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)]
  simpa [ENNReal.toReal_ofReal hδ.le] using hreal

@[blueprint "lem:linear-queries-blurry-calibration"
  (statement := /-- There is an absolute constant $C_{\mathrm{cal}}>0$ with the following property.  For every $\varepsilon\in(0,1]$, every $\delta\in(0,1]$, positive natural numbers $n,s$, every $\ell\in\mathbb N$, and every $R\in\mathbb R^{\ell\times d_{\mathrm{blur}}}$, there exist an $(\varepsilon,\delta)$-LNDP algorithm $\mathcal A_R$, a probability law $Z$ on $\mathbb R^\ell$, and $\sigma\ge0$ such that
  \[
    \mathcal A_R(G)\stackrel{\mathrm{law}}=
    R\widetilde p_{G,s}+Z
  \]
  for every graph $G$ on $[n]$.  The law $Z$ is either centered isotropic Gaussian of scale $\sigma$ or has the uniform linear-image bound of scale $\sigma$, and
  \[
    \sigma\le C_{\mathrm{cal}}\,
    \|R\|_{1\to2}
    \sqrt{\frac1n+\frac1{s^2}}\,
    c_{\varepsilon,\delta},
  \]
  where $c_{\varepsilon,\delta}=\sqrt{2\log(1.25/\delta)}/\varepsilon$
  is the Gaussian privacy scale from \cref{def:privacy-scale}. -/)
  (proof := /-- The nonnegativity of the maximum column norm follows from
  \cref{lem:max-column-two-norm-eq-pi-norm}.  If this norm vanishes, then
  \cref{lem:max-column-two-norm-eq-zero} gives $R=0$; constant Dirac local
  laws, constant zero postprocessing, $Z=\delta_0$, and $\sigma=0$ satisfy
  every assertion.

  Suppose now that $\|R\|_{1\to2}>0$.  Put
  \[
    B=1+\frac{n}{s^2},\qquad
    \tau=8\|R\|_{1\to2}\sqrt B\,c_{\varepsilon,\delta},
  \]
  where $c_{\varepsilon,\delta}$ is defined in
  \cref{def:privacy-scale}.  For a neighborhood $N$ define the noiseless
  local message by applying $R$ to the vector of weights from
  \cref{def:rounding-weight}, and let its local law be the translate of an
  independent coordinatewise Gaussian vector of variance $\tau^2$.  The
  released vector is the average of the $n$ local messages.  These local laws
  are probability measures, and their product followed by averaging gives a
  witness for \cref{def:is-lndp} once transcript privacy is established.

  For node-neighboring graphs $G,H$, let $q$ be the sum of the squared
  coordinate displacements of their noiseless local transcripts divided by
  $\tau^2$.  By \cref{lem:linear-queries-blurry-message-sensitivity},
  \[
    q\le \frac{1}{16c_{\varepsilon,\delta}^2}.
  \]
  The privacy-loss variable is Gaussian with mean $q/2$ and variance $q$.
  The calibrated Chernoff estimate
  \cref{lem:linear-queries-blurry-calibration-tail} bounds its upper tail at
  $\varepsilon$ by $\delta$.  Consequently
  \cref{lem:linear-queries-blurry-nested-gaussian-product-private} makes the
  two local transcript laws $(\varepsilon,\delta)$-indistinguishable.

  Let $Z$ be the law obtained by averaging the corresponding centered local
  Gaussian vectors and set $\sigma=\tau/\sqrt n$.
  The coordinatewise Gaussian translation identity and linearity show that
  the output law is the translate of $Z$ by
  $R\widetilde p_{G,s}$, where the identification of the averaged noiseless
  message uses \cref{def:compressed-blurry-degree-distribution}.
  Applying \cref{lem:linear-queries-blurry-nested-gaussian-sum} to every
  linear functional proves that $Z$ is centered isotropic Gaussian of scale
  $\sigma$.  Finally,
  \[
    \sigma
      =8\|R\|_{1\to2}
        \sqrt{\frac1n+\frac1{s^2}}\,
        c_{\varepsilon,\delta},
  \]
  so $C_{\mathrm{cal}}=8$ has all the required properties. -/)
  (title := /-- Calibration for blurry linear queries in the standard privacy regime -/)
  (latexEnv := "lemma")]
lemma linear_queries_blurry_calibration :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε δ : ℝ) (n s l : ℕ)
        (R : Matrix (Fin l) (Fin (blur_dimension n s)) ℝ),
        0 < ε → ε ≤ 1 → 0 < δ → δ ≤ 1 →
        0 < n → 0 < s →
        ∃ (A : randomized_graph_algorithm n l)
          (Z : Measure (Fin l → ℝ)) (σ : ℝ),
          0 ≤ σ ∧
          is_lndp ε δ A ∧
          (is_isotropic_gaussian_vector Z σ ∨
            has_uniform_linear_image_bound Z σ) ∧
          (∀ G : graph_on n,
            A G = Measure.map
              (fun z => Matrix.mulVec R (compressed_blurry_degree_distribution s G) + z) Z) ∧
          σ ≤ C * max_column_two_norm R *
            Real.sqrt ((n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2) *
            privacy_scale ε δ := by
  classical
  refine ⟨8, by norm_num, ?_⟩
  intro ε δ n s l R hε hε_one hδ hδ_one hn hs
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have hs_real : (0 : ℝ) < s := by exact_mod_cast hs
  have hR_nonneg : 0 ≤ max_column_two_norm R := by
    rw [max_column_two_norm_eq_pi_norm]
    exact norm_nonneg _
  by_cases hR_zero : max_column_two_norm R = 0
  · have hR : R = 0 := (max_column_two_norm_eq_zero R).mp hR_zero
    subst R
    let A : randomized_graph_algorithm n l := fun _ => Measure.dirac 0
    let Z : Measure (Fin l → ℝ) := Measure.dirac 0
    refine ⟨A, Z, 0, le_rfl, ?_, ?_, ?_, ?_⟩
    · refine ⟨PUnit, inferInstance, fun _ _ => Measure.dirac PUnit.unit,
          fun _ => 0, ?_, ?_, ?_, ?_⟩
      · intro i N
        infer_instance
      · fun_prop
      · intro G
        dsimp [A]
        simp
      · intro G H hGH
        unfold distribution_indistinguishable
        intro S hS
        constructor <;>
          calc
            (Measure.pi fun i : Fin n => Measure.dirac PUnit.unit) S =
                1 * (Measure.pi fun i : Fin n => Measure.dirac PUnit.unit) S := by
                  simp
            _ ≤ ENNReal.ofReal (Real.exp ε) *
                (Measure.pi fun i : Fin n => Measure.dirac PUnit.unit) S := by
                  gcongr
                  simp [Real.one_le_exp hε.le]
            _ ≤ ENNReal.ofReal (Real.exp ε) *
                  (Measure.pi fun i : Fin n => Measure.dirac PUnit.unit) S +
                ENNReal.ofReal δ := le_add_right le_rfl
    · left
      constructor
      · infer_instance
      · intro a
        dsimp [Z]
        simp [gaussianReal_zero_var]
    · intro G
      dsimp [A, Z]
      simp
    · rw [hR_zero]
      simp
  · have hR_pos : 0 < max_column_two_norm R :=
      lt_of_le_of_ne hR_nonneg (Ne.symm hR_zero)
    let c : ℝ := privacy_scale ε δ
    have hratio : 1 < (1.25 : ℝ) / δ :=
      (lt_div_iff₀ hδ).2 (by nlinarith)
    have hc_pos : 0 < c := by
      dsimp [c]
      unfold privacy_scale
      have : 0 < Real.log (1.25 / δ) := Real.log_pos hratio
      positivity
    let B : ℝ := 1 + (n : ℝ) / (s : ℝ) ^ 2
    have hB_pos : 0 < B := by
      dsimp [B]
      positivity
    let τ : ℝ := 8 * max_column_two_norm R * Real.sqrt B * c
    have hτ_pos : 0 < τ := by
      dsimp [τ]
      positivity
    let v : NNReal := Real.toNNReal (τ ^ 2)
    have hv_coe : (v : ℝ) = τ ^ 2 := by
      dsimp [v]
      exact max_eq_left (sq_nonneg τ)
    have hv_ne : v ≠ 0 := by
      intro hv
      have : (v : ℝ) = 0 := by simp [hv]
      rw [hv_coe] at this
      nlinarith
    let rowNoise : Measure (Fin l → ℝ) :=
      Measure.pi fun _ : Fin l => gaussianReal 0 v
    let localMean (N : Set (Fin n)) : Fin l → ℝ := fun j =>
      Matrix.mulVec R
        (fun b => rounding_weight s N.ncard b) j
    let localLaw : Fin n → Set (Fin n) → Measure (Fin l → ℝ) :=
      fun _ N => Measure.map (fun z => localMean N + z) rowNoise
    let postprocess : (Fin n → Fin l → ℝ) → (Fin l → ℝ) :=
      fun z j => (n : ℝ)⁻¹ * ∑ i, z i j
    let centeredTranscript : Measure (Fin n → Fin l → ℝ) :=
      Measure.pi fun _ : Fin n => rowNoise
    let A : randomized_graph_algorithm n l := fun G =>
      Measure.map postprocess
        (Measure.pi fun i => localLaw i {u | G.Adj i u})
    let Z : Measure (Fin l → ℝ) :=
      Measure.map postprocess centeredTranscript
    let σ : ℝ := τ / Real.sqrt n
    have hncard (G : graph_on n) (i : Fin n) :
        Set.ncard {u | G.Adj i u} = G.degree i := by
      change (G.neighborSet i).ncard = G.degree i
      calc
        (G.neighborSet i).ncard = Fintype.card (G.neighborSet i) :=
          (Set.fintypeCard_eq_ncard (s := G.neighborSet i)).symm
        _ = G.degree i := G.card_neighborSet_eq_degree (v := i)
    have hlocal_gaussian (N : Set (Fin n)) :
        Measure.map (fun z => localMean N + z) rowNoise =
          Measure.pi fun j : Fin l => gaussianReal (localMean N j) v := by
      dsimp [rowNoise]
      change Measure.map (fun z j => localMean N j + z j)
          (Measure.pi fun _ : Fin l => gaussianReal 0 v) = _
      rw [Measure.pi_map_pi]
      · congr 1
        funext j
        simpa using
          (gaussianReal_map_const_add (μ := 0) (v := v) (localMean N j))
      · intro j
        fun_prop
    have havg_mean (G : graph_on n) :
        postprocess (fun i => localMean {u | G.Adj i u}) =
          Matrix.mulVec R (compressed_blurry_degree_distribution s G) := by
      funext j
      dsimp [postprocess, localMean]
      simp_rw [hncard G]
      change (n : ℝ)⁻¹ *
          ∑ i : Fin n, ∑ b : Fin (blur_dimension n s),
            R j b * rounding_weight s (G.degree i) b =
        ∑ b : Fin (blur_dimension n s),
          R j b * ((n : ℝ)⁻¹ *
            ∑ i : Fin n, rounding_weight s (G.degree i) b)
      calc
        (n : ℝ)⁻¹ *
            ∑ i : Fin n, ∑ b : Fin (blur_dimension n s),
              R j b * rounding_weight s (G.degree i) b =
            ∑ i : Fin n, ∑ b : Fin (blur_dimension n s),
              (n : ℝ)⁻¹ *
                (R j b * rounding_weight s (G.degree i) b) := by
                  simp_rw [Finset.mul_sum]
        _ = ∑ b : Fin (blur_dimension n s), ∑ i : Fin n,
              (n : ℝ)⁻¹ *
                (R j b * rounding_weight s (G.degree i) b) :=
          Finset.sum_comm
        _ = ∑ b : Fin (blur_dimension n s),
              R j b * ((n : ℝ)⁻¹ *
                ∑ i : Fin n, rounding_weight s (G.degree i) b) := by
          apply Finset.sum_congr rfl
          intro b hb
          calc
            (∑ i : Fin n, (n : ℝ)⁻¹ *
                (R j b * rounding_weight s (G.degree i) b)) =
                ∑ i : Fin n, R j b *
                  ((n : ℝ)⁻¹ * rounding_weight s (G.degree i) b) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = R j b * ((n : ℝ)⁻¹ *
                ∑ i : Fin n, rounding_weight s (G.degree i) b) := by
              rw [← mul_assoc, Finset.mul_sum]
              simp only [mul_assoc]
    have htranscript_shift (G : graph_on n) :
        Measure.pi (fun i => localLaw i {u | G.Adj i u}) =
          Measure.map
            (fun z i => localMean {u | G.Adj i u} + z i)
            centeredTranscript := by
      symm
      dsimp [centeredTranscript]
      rw [Measure.pi_map_pi]
      intro i
      fun_prop
    refine ⟨A, Z, σ, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [σ]
      positivity
    · refine ⟨Fin l → ℝ, inferInstance, localLaw, postprocess, ?_, ?_, ?_, ?_⟩
      · intro i N
        dsimp [localLaw]
        exact Measure.isProbabilityMeasure_map (by fun_prop)
      · fun_prop
      · intro G
        rfl
      · intro G H hGH
        let mG : Fin n → Fin l → ℝ := fun i j =>
          Matrix.mulVec R
            (fun b => rounding_weight s (G.degree i) b) j
        let mH : Fin n → Fin l → ℝ := fun i j =>
          Matrix.mulVec R
            (fun b => rounding_weight s (H.degree i) b) j
        have hmeasureG :
            Measure.pi (fun i => localLaw i {u | G.Adj i u}) =
              Measure.pi fun i : Fin n =>
                Measure.pi fun j : Fin l => gaussianReal (mG i j) v := by
          congr 1
          funext i
          dsimp [localLaw]
          rw [hlocal_gaussian]
          congr 1
          funext j
          simp [localMean, mG, hncard G i]
        have hmeasureH :
            Measure.pi (fun i => localLaw i {u | H.Adj i u}) =
              Measure.pi fun i : Fin n =>
                Measure.pi fun j : Fin l => gaussianReal (mH i j) v := by
          congr 1
          funext i
          dsimp [localLaw]
          rw [hlocal_gaussian]
          congr 1
          funext j
          simp [localMean, mH, hncard H i]
        rw [hmeasureG, hmeasureH]
        apply linear_queries_blurry_nested_gaussian_product_private
            mG mH v hv_ne ε δ hε hδ.le
        let q : ℝ := (v : ℝ)⁻¹ *
          ∑ i, ∑ j, (mG i j - mH i j) ^ 2
        have hsum_nonneg :
            0 ≤ ∑ i, ∑ j, (mG i j - mH i j) ^ 2 :=
          Finset.sum_nonneg fun i hi =>
            Finset.sum_nonneg fun j hj => sq_nonneg _
        have hq_nonneg : 0 ≤ q := by
          dsimp [q]
          positivity
        have hsensitivity :
            ∑ i, ∑ j, (mG i j - mH i j) ^ 2 ≤
              4 * (max_column_two_norm R) ^ 2 * B := by
          simpa [mG, mH, B] using
            linear_queries_blurry_message_sensitivity hs R G H hGH
        have hq_bound : q ≤ (16 * c ^ 2)⁻¹ := by
          calc
            q ≤ (τ ^ 2)⁻¹ *
                (4 * (max_column_two_norm R) ^ 2 * B) := by
              dsimp [q]
              rw [hv_coe]
              exact mul_le_mul_of_nonneg_left hsensitivity
                (inv_nonneg.mpr (sq_nonneg τ))
            _ = (16 * c ^ 2)⁻¹ := by
              have hτ_sq :
                  τ ^ 2 = 64 * (max_column_two_norm R) ^ 2 * B * c ^ 2 := by
                dsimp [τ]
                nlinarith [Real.sq_sqrt hB_pos.le]
              rw [hτ_sq]
              field_simp [hR_pos.ne', hB_pos.ne', hc_pos.ne']
              norm_num
        simpa [q, c] using
          linear_queries_blurry_calibration_tail
            ε δ q hε hε_one hδ hδ_one hq_nonneg hq_bound
    · left
      constructor
      · dsimp [Z]
        exact Measure.isProbabilityMeasure_map (by fun_prop)
      · intro a
        dsimp [Z]
        rw [Measure.map_map]
        · convert linear_queries_blurry_nested_gaussian_sum
              (a := fun i j => (n : ℝ)⁻¹ * a j) v using 1
          · congr 1
            funext z
            dsimp [postprocess]
            calc
              (∑ j : Fin l, a j * ((n : ℝ)⁻¹ * ∑ i : Fin n, z i j)) =
                  ∑ j : Fin l, ∑ i : Fin n,
                    (n : ℝ)⁻¹ * a j * z i j := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [← mul_assoc, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                ring
              _ = ∑ i : Fin n, ∑ j : Fin l,
                    (n : ℝ)⁻¹ * a j * z i j := Finset.sum_comm
          · congr 2
            dsimp [σ]
            rw [hv_coe]
            have hsqrt_n : (Real.sqrt (n : ℝ)) ^ 2 = n := by
              rw [Real.sq_sqrt hn_real.le]
            rw [show (∑ i : Fin n, ∑ j : Fin l,
                  ((n : ℝ)⁻¹ * a j) ^ 2) =
                (n : ℝ) * (n : ℝ)⁻¹ ^ 2 *
                  ∑ j : Fin l, (a j) ^ 2 by
              simp_rw [mul_pow, Finset.mul_sum]
              simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
              rw [Finset.mul_sum]
              ring_nf]
            rw [div_pow, hsqrt_n]
            field_simp
        · fun_prop
        · fun_prop
    · intro G
      dsimp [A, Z]
      rw [htranscript_shift]
      rw [Measure.map_map, Measure.map_map]
      · congr 1
        funext z
        funext j
        dsimp [postprocess]
        simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
        rw [show (n : ℝ)⁻¹ *
              ∑ i, localMean {u | G.Adj i u} j =
            postprocess (fun i => localMean {u | G.Adj i u}) j by rfl]
        rw [havg_mean G]
      all_goals fun_prop
    · have harg_nonneg :
          0 ≤ (n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2 := by positivity
      have hB_eq :
          B = (n : ℝ) *
            ((n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2) := by
        dsimp [B]
        field_simp
      have hsqrt_B :
          Real.sqrt B = Real.sqrt n *
            Real.sqrt ((n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2) := by
        rw [hB_eq, Real.sqrt_mul hn_real.le]
      dsimp [σ, τ, c]
      rw [hsqrt_B]
      field_simp [Real.sqrt_ne_zero'.mpr hn_real]
      rfl

@[blueprint "lem:linear-queries-blurry"
  (statement := /-- There is an absolute constant $C_{\mathrm{lin}}>0$ with the following property.  For every $\varepsilon\in(0,1]$, every $\delta\in(0,1]$, positive natural numbers $n,s$, every $\ell\in\mathbb N$, and every $R\in\mathbb R^{\ell\times d_{\mathrm{blur}}}$, there exist an $(\varepsilon,\delta)$-LNDP algorithm $\mathcal A_R$, a probability law $Z$ on $\mathbb R^\ell$, and $\sigma\ge0$ such that $\mathcal A_R(G)$ has the law of $R\widetilde p_{G,s}+Z$ for every graph $G$ on $[n]$.  The law $Z$ is either centered isotropic Gaussian of scale $\sigma$ or has the uniform linear-image bound of scale $\sigma$, and
  \[
    \sigma\le C_{\mathrm{lin}}\|R\|_{1\to2}
      \sqrt{\frac1n+\frac1{s^2}}\,c_{\varepsilon,\delta},
  \]
  where $c_{\varepsilon,\delta}=\sqrt{2\log(1.25/\delta)}/\varepsilon$
  is the Gaussian privacy scale from \cref{def:privacy-scale}. -/)
  (proof := /-- Apply \cref{lem:linear-queries-blurry-calibration} with the hypotheses $0<\varepsilon\le1$ and $0<\delta\le1$.  Its algorithm, noise law, scale, and absolute constant satisfy each asserted conclusion verbatim. -/)
  (title := /-- Linear queries of the compressed blurry degree distribution -/)
  (latexEnv := "lemma")]
lemma linear_queries_blurry :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε δ : ℝ) (n s l : ℕ)
        (R : Matrix (Fin l) (Fin (blur_dimension n s)) ℝ),
        0 < ε → ε ≤ 1 → 0 < δ → δ ≤ 1 →
        0 < n → 0 < s →
        ∃ (A : randomized_graph_algorithm n l)
          (Z : Measure (Fin l → ℝ)) (σ : ℝ),
          0 ≤ σ ∧
          is_lndp ε δ A ∧
          (is_isotropic_gaussian_vector Z σ ∨
            has_uniform_linear_image_bound Z σ) ∧
          (∀ G : graph_on n,
            A G = Measure.map
              (fun z => Matrix.mulVec R (compressed_blurry_degree_distribution s G) + z) Z) ∧
          σ ≤ C * max_column_two_norm R *
            Real.sqrt ((n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2) *
            privacy_scale ε δ := by
  exact linear_queries_blurry_calibration

@[blueprint "lem:all-epsilon-staircase-privacy-tail"
  (statement := /-- Let $1<\varepsilon$, $0<\delta\le 1$, and $q\ge0$.  If
  \[
    q\le \frac{1}{16(c^*_{\varepsilon,\delta})^2},
  \]
  then a Gaussian random variable with mean $q/2$ and variance $q$ exceeds
  $\varepsilon$ with probability at most $\delta$. -/)
  (proof := /-- Put $L=\log(1.25/\delta)$.  The two nonnegative summands in
  \cref{def:all-epsilon-privacy-scale} imply respectively
  $q\le\varepsilon^2/(32L)$ and $q\le\varepsilon/16$.  Apply the
  exponential-moment bound with $t=8L/\varepsilon$.  The quadratic term in
  the exponent is at most $L$, while the mean-shift term is at most $L/4$.
  Since $L=\log(1.25)-\log\delta$, the resulting exponent is at most
  $\log\delta$, and exponentiation gives the claimed tail bound. -/)
  (title := /-- Gaussian privacy-loss tail bound in the high-$\varepsilon$ regime -/)
  (latexEnv := "lemma")]
lemma all_epsilon_staircase_privacy_tail
    (ε δ q : ℝ) (hε : 1 < ε)
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) (hq_nonneg : 0 ≤ q)
    (hq : q ≤ (16 * (all_epsilon_privacy_scale ε δ) ^ 2)⁻¹) :
    gaussianReal (q / 2) (Real.toNNReal q) (Set.Ioi ε) ≤
      ENNReal.ofReal δ := by
  let L : ℝ := Real.log (1.25 / δ)
  let c : ℝ := all_epsilon_privacy_scale ε δ
  have hε_pos : 0 < ε := lt_trans (by norm_num) hε
  have hratio : 1 < (1.25 : ℝ) / δ :=
    (lt_div_iff₀ hδ).2 (by nlinarith)
  have hL_pos : 0 < L := by
    exact Real.log_pos hratio
  have hprivacy_pos : 0 < privacy_scale ε δ := by
    unfold privacy_scale
    positivity
  have hc_pos : 0 < c := by
    dsimp [c, all_epsilon_privacy_scale]
    positivity
  have hc_privacy : privacy_scale ε δ ≤ c := by
    dsimp [c, all_epsilon_privacy_scale]
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hc_sqrt : Real.sqrt ε⁻¹ ≤ c := by
    dsimp [c, all_epsilon_privacy_scale]
    exact le_add_of_nonneg_left hprivacy_pos.le
  have hq_log : q ≤ ε ^ 2 / (32 * L) := by
    calc
      q ≤ (16 * c ^ 2)⁻¹ := hq
      _ ≤ (16 * (privacy_scale ε δ) ^ 2)⁻¹ := by
        exact (inv_le_inv₀ (by positivity) (by positivity)).2 (by
          nlinarith)
      _ = ε ^ 2 / (32 * L) := by
        dsimp [L]
        unfold privacy_scale
        rw [div_pow, Real.sq_sqrt (by positivity)]
        field_simp
        ring
  have hq_epsilon : q ≤ ε / 16 := by
    calc
      q ≤ (16 * c ^ 2)⁻¹ := hq
      _ ≤ (16 * (Real.sqrt ε⁻¹) ^ 2)⁻¹ := by
        exact (inv_le_inv₀ (by positivity) (by positivity)).2 (by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          simpa only [pow_two] using
            mul_self_le_mul_self (Real.sqrt_nonneg _) hc_sqrt)
      _ = ε / 16 := by
        rw [Real.sq_sqrt (inv_nonneg.mpr hε_pos.le)]
        field_simp
  have hq_mul : 32 * L * q ≤ ε ^ 2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (le_div_iff₀ (by positivity : 0 < 32 * L)).mp hq_log
  let t : ℝ := 8 * L / ε
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have hterm_one : q * t / 2 ≤ L / 4 := by
    dsimp [t]
    rw [show q * (8 * L / ε) / 2 = (4 * L * q) / ε by ring]
    exact (div_le_iff₀ hε_pos).2 (by
      nlinarith [mul_le_mul_of_nonneg_left hq_epsilon hL_pos.le])
  have hterm_two : q * t ^ 2 / 2 ≤ L := by
    dsimp [t]
    rw [show q * (8 * L / ε) ^ 2 / 2 =
        (32 * L ^ 2 * q) / ε ^ 2 by ring]
    apply (div_le_iff₀ (sq_pos_of_pos hε_pos)).2
    nlinarith [mul_le_mul_of_nonneg_left hq_mul hL_pos.le]
  have hlog_const : 0 < Real.log 1.25 := Real.log_pos (by norm_num)
  have hlog_delta : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ_one
  have hL_eq : L = Real.log 1.25 - Real.log δ := by
    dsimp [L]
    rw [Real.log_div (by norm_num : (1.25 : ℝ) ≠ 0) hδ.ne']
  have hexponent :
      -t * ε + q / 2 * t + q * t ^ 2 / 2 ≤ Real.log δ := by
    have htε : t * ε = 8 * L := by
      dsimp [t]
      field_simp
    nlinarith
  have hchernoff :=
    measure_ge_le_exp_mul_mgf
      (μ := gaussianReal (q / 2) (Real.toNNReal q))
      (X := id) (t := t) ε ht_pos.le
      (integrable_exp_mul_gaussianReal t)
  have hreal :
      (gaussianReal (q / 2) (Real.toNNReal q) (Set.Ioi ε)).toReal ≤ δ := by
    calc
      (gaussianReal (q / 2) (Real.toNNReal q) (Set.Ioi ε)).toReal ≤
          (gaussianReal (q / 2) (Real.toNNReal q)
            {x | ε ≤ id x}).toReal := by
              apply ENNReal.toReal_mono (measure_ne_top _ _)
              exact measure_mono (by
                intro x hx
                simpa only [Set.mem_Ioi, Set.mem_setOf_eq] using hx.le)
      _ ≤ Real.exp (-t * ε) *
          mgf id (gaussianReal (q / 2) (Real.toNNReal q)) t := hchernoff
      _ = Real.exp (-t * ε + q / 2 * t + q * t ^ 2 / 2) := by
        rw [mgf_id_gaussianReal, ← Real.exp_add]
        congr 1
        rw [Real.coe_toNNReal q hq_nonneg]
        ring
      _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hexponent
      _ = δ := Real.exp_log hδ
  rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)]
  simpa [ENNReal.toReal_ofReal hδ.le] using hreal

@[blueprint "lem:all-epsilon-staircase-gaussian-uniform-linear-image"
  (statement := /-- Every centered isotropic Gaussian probability law of
  nonnegative scale $\sigma$ has the uniform linear-image bound of scale
  $\sigma$. -/)
  (proof := /-- Fix a finite matrix $L$.  By
  \cref{def:is-isotropic-gaussian-vector}, each signed coordinate of $LZ$
  is centered Gaussian, with variance at most
  $\sigma^2\|L\|_{2\to\infty}^2$ by
  \cref{def:max-row-two-norm}.  Exponential integrability of these finitely
  many coordinates gives integrability of $\|LZ\|_\infty$.  If the common
  variance bound vanishes, every coordinate is almost surely zero.
  Otherwise, the exponential soft-maximum bound, the exact Gaussian
  moment-generating function, and Jensen's inequality give
  \[
    t\,\mathbb E\|LZ\|_\infty
      \le \log(2k)+\frac{t^2\sigma^2\|L\|_{2\to\infty}^2}{2}.
  \]
  Choosing
  $t=\sqrt{2\log(2k)}/(\sigma\|L\|_{2\to\infty})$ proves precisely the
  integrability and expectation estimate in
  \cref{def:has-uniform-linear-image-bound}; the case $k=0$ is immediate. -/)
  (title := /-- Isotropic Gaussian laws have uniform linear-image bounds -/)
  (latexEnv := "lemma")]
lemma all_epsilon_staircase_gaussian_uniform_linear_image {l : ℕ}
    (Z : Measure (Fin l → ℝ)) (σ : ℝ)
    (hσ : 0 ≤ σ) (hZ : is_isotropic_gaussian_vector Z σ) :
    has_uniform_linear_image_bound Z σ := by
  refine ⟨hZ.1, ?_⟩
  intro k L
  classical
  by_cases hk : k = 0
  · subst k
    have hfun : (fun z => ‖Matrix.mulVec L z‖) = (fun _ => (0 : ℝ)) := by
      funext z
      have hz : Matrix.mulVec L z = 0 := Subsingleton.elim _ _
      rw [hz]
      simp
    rw [hfun]
    simp [max_row_two_norm]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    let i0 : Fin k := ⟨0, hkpos⟩
    have huniv : (Finset.univ : Finset (Fin k)).Nonempty :=
      ⟨i0, Finset.mem_univ i0⟩
    rcases hZ with ⟨hprob, hgauss⟩
    letI : IsProbabilityMeasure Z := hprob
    have hmeas (i : Fin k) :
        Measurable (fun z => Matrix.mulVec L z i) := by
      fun_prop
    have hmap (i : Fin k) :
        Measure.map (fun z => Matrix.mulVec L z i) Z =
          gaussianReal 0
            (Real.toNNReal (σ ^ 2 * ∑ j : Fin l, (L i j) ^ 2)) := by
      simpa [Matrix.mulVec, dotProduct] using hgauss (L i)
    have hexp (i : Fin k) (t : ℝ) :
        Integrable (fun z => Real.exp (t * Matrix.mulVec L z i)) Z := by
      have hg_meas : Measurable (fun x : ℝ => Real.exp (t * x)) := by
        fun_prop
      have hg : Integrable (fun x : ℝ => Real.exp (t * x))
          (Measure.map (fun z => Matrix.mulVec L z i) Z) := by
        rw [hmap i]
        exact ProbabilityTheory.integrable_exp_mul_gaussianReal t
      simpa [Function.comp_def] using
        (MeasureTheory.integrable_map_measure hg_meas.aestronglyMeasurable
          (hmeas i).aemeasurable).mp hg
    have hcoord_int (i : Fin k) :
        Integrable (fun z => Matrix.mulVec L z i) Z := by
      refine Integrable.mono' ((hexp i 1).add (hexp i (-1)))
        (hmeas i).aestronglyMeasurable ?_
      refine ae_of_all Z (fun z => ?_)
      simp only [Pi.add_apply, one_mul, neg_mul, Real.norm_eq_abs]
      rw [abs_le]
      constructor <;>
        linarith [Real.add_one_le_exp (Matrix.mulVec L z i),
          Real.add_one_le_exp (-Matrix.mulVec L z i),
          Real.exp_pos (Matrix.mulVec L z i),
          Real.exp_pos (-Matrix.mulVec L z i)]
    have hnorm_eq (x : Fin k → ℝ) : ∃ i : Fin k, ‖x‖ = |x i| := by
      obtain ⟨i, hi, heq⟩ :=
        Finset.exists_mem_eq_sup Finset.univ huniv
          (fun i : Fin k => ‖x i‖₊)
      refine ⟨i, ?_⟩
      rw [Pi.norm_def, heq]
      simp
    have hnorm_int : Integrable (fun z => ‖Matrix.mulVec L z‖) Z := by
      have hsum_int :
          Integrable (fun z => ∑ i : Fin k, |Matrix.mulVec L z i|) Z :=
        integrable_finsetSum Finset.univ (fun i hi => (hcoord_int i).abs)
      refine Integrable.mono hsum_int (by fun_prop) ?_
      refine ae_of_all Z (fun z => ?_)
      obtain ⟨i, hi⟩ := hnorm_eq (Matrix.mulVec L z)
      rw [hi]
      have hs := Finset.single_le_sum
        (fun j _ => abs_nonneg (Matrix.mulVec L z j)) (Finset.mem_univ i)
      have hsum_nonneg : 0 ≤ ∑ j : Fin k, |Matrix.mulVec L z j| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      simpa only [Real.norm_eq_abs, abs_abs, abs_of_nonneg hsum_nonneg] using hs
    have hrow_le (i : Fin k) :
        Real.sqrt (∑ j : Fin l, (L i j) ^ 2) ≤ max_row_two_norm L := by
      unfold max_row_two_norm
      exact le_csSup (Set.finite_range _).bddAbove ⟨i, rfl⟩
    have hM_nonneg : 0 ≤ max_row_two_norm L :=
      le_trans (Real.sqrt_nonneg _) (hrow_le i0)
    have hvar_le (i : Fin k) :
        (Real.toNNReal (σ ^ 2 * ∑ j : Fin l, (L i j) ^ 2) : ℝ) ≤
          (σ * max_row_two_norm L) ^ 2 := by
      rw [Real.coe_toNNReal]
      · have hr : 0 ≤ ∑ j : Fin l, (L i j) ^ 2 :=
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        have hrle : (∑ j : Fin l, (L i j) ^ 2) ≤
            (max_row_two_norm L) ^ 2 := by
          nlinarith [Real.sq_sqrt hr,
            Real.sqrt_nonneg (∑ j : Fin l, (L i j) ^ 2), hrow_le i]
        calc
          σ ^ 2 * (∑ j : Fin l, (L i j) ^ 2) ≤
              σ ^ 2 * (max_row_two_norm L) ^ 2 :=
            mul_le_mul_of_nonneg_left hrle (sq_nonneg σ)
          _ = (σ * max_row_two_norm L) ^ 2 := by ring
      · positivity
    have hmoment (i : Fin k) (t : ℝ) :
        (∫ z, Real.exp (t * Matrix.mulVec L z i) ∂Z) =
          Real.exp ((Real.toNNReal
            (σ ^ 2 * ∑ j : Fin l, (L i j) ^ 2) : ℝ) * t ^ 2 / 2) := by
      simpa [ProbabilityTheory.mgf] using
        ProbabilityTheory.mgf_gaussianReal (hmap i) t
    have hsoft (t : ℝ) (ht : 0 ≤ t) (x : Fin k → ℝ) :
        Real.exp (t * ‖x‖) ≤
          ∑ i : Fin k, (Real.exp (t * x i) + Real.exp ((-t) * x i)) := by
      obtain ⟨i, hi⟩ := hnorm_eq x
      rw [hi]
      calc
        Real.exp (t * |x i|) ≤
            Real.exp (t * x i) + Real.exp ((-t) * x i) := by
          by_cases hx : 0 ≤ x i
          · rw [abs_of_nonneg hx]
            exact le_add_of_nonneg_right (Real.exp_nonneg _)
          · rw [abs_of_neg (lt_of_not_ge hx)]
            simpa only [mul_neg, neg_mul] using
              le_add_of_nonneg_left (Real.exp_nonneg (t * x i))
        _ ≤ ∑ j : Fin k,
            (Real.exp (t * x j) + Real.exp ((-t) * x j)) := by
          exact Finset.single_le_sum
            (f := fun j : Fin k =>
              Real.exp (t * x j) + Real.exp ((-t) * x j))
            (fun j _ => add_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
            (Finset.mem_univ i)
    have hsumexp_int (t : ℝ) : Integrable
        (fun z => ∑ i : Fin k,
          (Real.exp (t * Matrix.mulVec L z i) +
            Real.exp ((-t) * Matrix.mulVec L z i))) Z :=
      integrable_finsetSum Finset.univ
        (fun i hi => (hexp i t).add (hexp i (-t)))
    have hnormexp_int (t : ℝ) (ht : 0 ≤ t) :
        Integrable (fun z => Real.exp (t * ‖Matrix.mulVec L z‖)) Z := by
      refine Integrable.mono' (hsumexp_int t) (by fun_prop) ?_
      refine ae_of_all Z (fun z => ?_)
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _),
        Pi.add_apply]
      exact hsoft t ht (Matrix.mulVec L z)
    have hjensen (t : ℝ) (ht : 0 ≤ t) :
        Real.exp (t * ∫ z, ‖Matrix.mulVec L z‖ ∂Z) ≤
          ∫ z, Real.exp (t * ‖Matrix.mulVec L z‖) ∂Z := by
      let X : (Fin l → ℝ) → ℝ := fun z => t * ‖Matrix.mulVec L z‖
      let m : ℝ := ∫ z, X z ∂Z
      have hX : Integrable X Z := hnorm_int.const_mul t
      have hexpX : Integrable (fun z => Real.exp (X z)) Z :=
        hnormexp_int t ht
      have hone : Integrable (fun _ : Fin l → ℝ => (1 : ℝ)) Z :=
        integrable_const 1
      have hm : Integrable (fun _ : Fin l → ℝ => m) Z :=
        integrable_const m
      have hlin : Integrable (fun z => Real.exp m * (1 + X z - m)) Z :=
        ((hone.add hX).sub hm).const_mul (Real.exp m)
      have hpw : ∀ z, Real.exp m * (1 + X z - m) ≤ Real.exp (X z) := by
        intro z
        calc
          Real.exp m * (1 + X z - m) ≤
              Real.exp m * Real.exp (X z - m) := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg m)
            simpa only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
              Real.add_one_le_exp (X z - m)
          _ = Real.exp (X z) := by
            rw [← Real.exp_add]
            congr 1
            ring
      have hi := integral_mono hlin hexpX hpw
      have hcenter : (∫ z, (1 + X z - m) ∂Z) = 1 := by
        calc
          (∫ z, (1 + X z - m) ∂Z) =
              (∫ z, (1 + X z) ∂Z) - ∫ _z, m ∂Z := by
            simpa only [Pi.add_apply] using
              integral_sub (hone.add hX) hm
          _ = ((∫ _z, (1 : ℝ) ∂Z) + ∫ z, X z ∂Z) -
              ∫ _z, m ∂Z := by
            rw [integral_add hone hX]
          _ = 1 := by simp [m]
      have heq : (∫ z, Real.exp m * (1 + X z - m) ∂Z) =
          Real.exp m := by
        rw [integral_const_mul, hcenter]
        ring
      rw [heq] at hi
      simpa [X, m, integral_const_mul] using hi
    have hsum_bound (t : ℝ) :
        (∫ z, ∑ i : Fin k,
          (Real.exp (t * Matrix.mulVec L z i) +
            Real.exp ((-t) * Matrix.mulVec L z i)) ∂Z) ≤
          (2 * (k : ℝ)) *
            Real.exp ((σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2) := by
      have hsplit :
          (∫ z, ∑ i : Fin k,
            (Real.exp (t * Matrix.mulVec L z i) +
              Real.exp ((-t) * Matrix.mulVec L z i)) ∂Z) =
            ∑ i : Fin k, (∫ z,
              (Real.exp (t * Matrix.mulVec L z i) +
                Real.exp ((-t) * Matrix.mulVec L z i)) ∂Z) := by
        simpa only [Finset.sum_apply, Pi.add_apply] using
          integral_finsetSum Finset.univ
            (fun i hi => (hexp i t).add (hexp i (-t)))
      rw [hsplit]
      calc
        ∑ i : Fin k, (∫ z, (Real.exp (t * Matrix.mulVec L z i) +
            Real.exp ((-t) * Matrix.mulVec L z i)) ∂Z) =
            ∑ i : Fin k, ((∫ z, Real.exp (t * Matrix.mulVec L z i) ∂Z) +
              (∫ z, Real.exp ((-t) * Matrix.mulVec L z i) ∂Z)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [integral_add (hexp i t) (hexp i (-t))]
        _ ≤ ∑ i : Fin k,
            (Real.exp ((σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2) +
              Real.exp ((σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2)) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [hmoment i t, hmoment i (-t)]
          apply add_le_add <;> apply Real.exp_le_exp.mpr
          · exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hvar_le i) (sq_nonneg t))
              (by norm_num)
          · simpa only [neg_sq] using
              (div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right (hvar_le i) (sq_nonneg t))
                (by norm_num))
        _ = (2 * (k : ℝ)) *
            Real.exp ((σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2) := by
          simp [Finset.sum_const]
          ring
    have hexp_bound (t : ℝ) (ht : 0 ≤ t) :
        (∫ z, Real.exp (t * ‖Matrix.mulVec L z‖) ∂Z) ≤
          (2 * (k : ℝ)) *
            Real.exp ((σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2) := by
      calc
        (∫ z, Real.exp (t * ‖Matrix.mulVec L z‖) ∂Z) ≤
            ∫ z, ∑ i : Fin k,
              (Real.exp (t * Matrix.mulVec L z i) +
                Real.exp ((-t) * Matrix.mulVec L z i)) ∂Z :=
          integral_mono (hnormexp_int t ht) (hsumexp_int t)
            (fun z => hsoft t ht (Matrix.mulVec L z))
        _ ≤ (2 * (k : ℝ)) *
            Real.exp ((σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2) :=
          hsum_bound t
    by_cases hS : σ * max_row_two_norm L = 0
    · have hvar_zero (i : Fin k) :
          σ ^ 2 * ∑ j : Fin l, (L i j) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hS with hσ0 | hM0
        · rw [hσ0]
          norm_num
        · have hr : 0 ≤ ∑ j : Fin l, (L i j) ^ 2 :=
            Finset.sum_nonneg (fun _ _ => sq_nonneg _)
          have hsqrt0 : Real.sqrt (∑ j : Fin l, (L i j) ^ 2) = 0 :=
            le_antisymm (by simpa [hM0] using hrow_le i) (Real.sqrt_nonneg _)
          have hr0 : (∑ j : Fin l, (L i j) ^ 2) = 0 := by
            nlinarith [Real.sq_sqrt hr]
          rw [hr0]
          ring
      have hzero (i : Fin k) : ∀ᵐ z ∂Z, Matrix.mulVec L z i = 0 := by
        have hm0 : Measure.map (fun z => Matrix.mulVec L z i) Z =
            Measure.dirac 0 := by
          rw [hmap i, hvar_zero i]
          simp
        apply (ae_map_iff (hmeas i).aemeasurable
          (measurableSet_singleton 0)).mp
        rw [hm0]
        exact (ae_dirac_iff (measurableSet_singleton 0)).2
          (Set.mem_singleton 0)
      have hall : ∀ᵐ z ∂Z, ∀ i : Fin k, Matrix.mulVec L z i = 0 :=
        ae_all_iff.mpr hzero
      have hnorm_zero : ∀ᵐ z ∂Z, ‖Matrix.mulVec L z‖ = 0 := by
        filter_upwards [hall] with z hz
        have hv : Matrix.mulVec L z = 0 := funext hz
        simp [hv]
      have hint_zero : (∫ z, ‖Matrix.mulVec L z‖ ∂Z) = 0 := by
        rw [integral_congr_ae hnorm_zero]
        simp
      exact ⟨hnorm_int, by rw [hint_zero, hS]; simp⟩
    · have hSpos : 0 < σ * max_row_two_norm L :=
        lt_of_le_of_ne (mul_nonneg hσ hM_nonneg) (Ne.symm hS)
      have hn_gt : 1 < 2 * (k : ℝ) := by
        exact_mod_cast (show 1 < 2 * k by omega)
      have hlogpos : 0 < Real.log (2 * (k : ℝ)) := Real.log_pos hn_gt
      let q : ℝ := Real.sqrt (2 * Real.log (2 * (k : ℝ)))
      have hqpos : 0 < q :=
        Real.sqrt_pos.2 (mul_pos (by norm_num) hlogpos)
      have hq_sq : q ^ 2 = 2 * Real.log (2 * (k : ℝ)) :=
        Real.sq_sqrt (by positivity)
      let t : ℝ := q / (σ * max_row_two_norm L)
      have htpos : 0 < t := div_pos hqpos hSpos
      have htS : t * (σ * max_row_two_norm L) = q := by
        dsimp [t]
        exact div_mul_cancel₀ q (ne_of_gt hSpos)
      have hchain :
          Real.exp (t * ∫ z, ‖Matrix.mulVec L z‖ ∂Z) ≤
            (2 * (k : ℝ)) *
              Real.exp ((σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2) :=
        (hjensen t htpos.le).trans (hexp_bound t htpos.le)
      have hlog : t * (∫ z, ‖Matrix.mulVec L z‖ ∂Z) ≤
          Real.log (2 * (k : ℝ)) +
            (σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2 := by
        calc
          t * (∫ z, ‖Matrix.mulVec L z‖ ∂Z) =
              Real.log (Real.exp
                (t * ∫ z, ‖Matrix.mulVec L z‖ ∂Z)) :=
            (Real.log_exp _).symm
          _ ≤ Real.log ((2 * (k : ℝ)) *
              Real.exp ((σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2)) :=
            Real.log_le_log (Real.exp_pos _) hchain
          _ = Real.log (2 * (k : ℝ)) +
              (σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2 := by
            rw [Real.log_mul
              (ne_of_gt (show 0 < 2 * (k : ℝ) by positivity))
              (ne_of_gt (Real.exp_pos _)), Real.log_exp]
      have hprod : (σ * max_row_two_norm L) ^ 2 * t ^ 2 = q ^ 2 := by
        calc
          (σ * max_row_two_norm L) ^ 2 * t ^ 2 =
              (t * (σ * max_row_two_norm L)) ^ 2 := by ring
          _ = q ^ 2 := by rw [htS]
      have hlog_eq : Real.log (2 * (k : ℝ)) = q ^ 2 / 2 := by
        nlinarith [hq_sq]
      have hopt : Real.log (2 * (k : ℝ)) +
          (σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2 = q ^ 2 := by
        rw [hlog_eq, hprod]
        ring
      refine ⟨hnorm_int, ?_⟩
      apply le_of_mul_le_mul_left _ htpos
      calc
        t * (∫ z, ‖Matrix.mulVec L z‖ ∂Z) ≤
            Real.log (2 * (k : ℝ)) +
              (σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2 := hlog
        _ = q ^ 2 := hopt
        _ = t * (σ * max_row_two_norm L *
            Real.sqrt (2 * Real.log (2 * (k : ℝ)))) := by
          rw [show Real.sqrt (2 * Real.log (2 * (k : ℝ))) = q by rfl,
            ← htS]
          ring

@[blueprint "lem:all-epsilon-staircase-linear-queries"
  (statement := /-- There is an absolute constant $C_{\mathrm{st}}>0$ with the following property.  Let $\varepsilon>1$, let $\delta\in(0,1]$, let $n,s$ be positive natural numbers, let $\ell\in\mathbb N$, and let
  $R\in\mathbb R^{\ell\times d_{\mathrm{blur}}}$.  Then there exist an
  $(\varepsilon,\delta)$-LNDP algorithm $\mathcal A_R$, a probability law
  $Z$ on $\mathbb R^\ell$, and a number $\sigma\ge0$ such that
  $\mathcal A_R(G)$ has the law of
  $R\widetilde p_{G,s}+Z$ for every graph $G$ on $[n]$, the law $Z$ has the
  uniform linear-image bound of scale $\sigma$, and
  \[
    \sigma\le C_{\mathrm{st}}\|R\|_{1\to2}
      \sqrt{\frac1n+\frac1{s^2}}\,
      c^*_{\varepsilon,\delta},
  \] -/)
  (proof := /-- Take the absolute constant to be $8$.  By
  \cref{lem:max-column-two-norm-eq-pi-norm}, the maximum column norm is
  nonnegative.  If it is zero,
  \cref{lem:max-column-two-norm-eq-zero} gives $R=0$.  Constant Dirac local
  laws, constant zero postprocessing, $Z=\delta_0$, and $\sigma=0$ then
  satisfy LNDP and the output identity; the uniform bound follows from
  \cref{lem:all-epsilon-staircase-gaussian-uniform-linear-image}.

  Assume henceforth that $\|R\|_{1\to2}>0$, and set
  \[
    B=1+\frac{n}{s^2},\qquad
    \tau=8\|R\|_{1\to2}\sqrt B\,c^*_{\varepsilon,\delta}.
  \]
  For a neighborhood $N$, let the noiseless local message be $R$ applied to
  the randomized-rounding weight vector with degree $|N|$, and let its law
  be the translate of a product of centered coordinatewise Gaussians of
  variance $\tau^2$.  Define the server postprocessing to average the $n$
  local messages.  These probability laws and this measurable
  postprocessing give the required local-model representation.

  For node-neighboring graphs $G,H$, write $m_G,m_H$ for their arrays of
  noiseless local messages and put
  \[
    q=\tau^{-2}\sum_{i,j}(m_G(i,j)-m_H(i,j))^2.
  \]
  The sensitivity estimate
  \cref{lem:linear-queries-blurry-message-sensitivity} gives
  $q\le 1/(16(c^*_{\varepsilon,\delta})^2)$.  Hence
  \cref{lem:all-epsilon-staircase-privacy-tail} bounds the corresponding
  Gaussian privacy-loss tail by $\delta$, and
  \cref{lem:linear-queries-blurry-nested-gaussian-product-private} yields
  both $(\varepsilon,\delta)$-indistinguishability inequalities for the
  transcript laws.

  Let $Z$ be the law obtained by averaging the centered transcript and put
  $\sigma=\tau/\sqrt n$.  Linearity of averaging identifies the output law
  on every graph $G$ with the translate of $Z$ by
  $R\widetilde p_{G,s}$.  Applying
  \cref{lem:linear-queries-blurry-nested-gaussian-sum} to every linear
  functional shows that $Z$ is centered isotropic Gaussian of scale
  $\sigma$; then
  \cref{lem:all-epsilon-staircase-gaussian-uniform-linear-image} gives the
  required uniform linear-image bound.  Finally,
  \[
    \sigma
      =8\|R\|_{1\to2}
        \sqrt{\frac1n+\frac1{s^2}}\,
        c^*_{\varepsilon,\delta},
  \]
  which is the asserted estimate. -/)
  (title := /-- All-$\varepsilon$ Gaussian calibration for blurry linear queries -/)
  (latexEnv := "lemma")]
lemma all_epsilon_staircase_linear_queries :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε δ : ℝ) (n s l : ℕ)
        (R : Matrix (Fin l) (Fin (blur_dimension n s)) ℝ),
        1 < ε → 0 < δ → δ ≤ 1 →
        0 < n → 0 < s →
        ∃ (A : randomized_graph_algorithm n l)
          (Z : Measure (Fin l → ℝ)) (σ : ℝ),
          0 ≤ σ ∧
          is_lndp ε δ A ∧
          has_uniform_linear_image_bound Z σ ∧
          (∀ G : graph_on n,
            A G = Measure.map
              (fun z => Matrix.mulVec R (compressed_blurry_degree_distribution s G) + z) Z) ∧
          σ ≤ C * max_column_two_norm R *
            Real.sqrt ((n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2) *
            all_epsilon_privacy_scale ε δ := by
  classical
  refine ⟨8, by norm_num, ?_⟩
  intro ε δ n s l R hε hδ hδ_one hn hs
  have hε_pos : 0 < ε := lt_trans (by norm_num) hε
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have hs_real : (0 : ℝ) < s := by exact_mod_cast hs
  have hR_nonneg : 0 ≤ max_column_two_norm R := by
    rw [max_column_two_norm_eq_pi_norm]
    exact norm_nonneg _
  by_cases hR_zero : max_column_two_norm R = 0
  · have hR : R = 0 := (max_column_two_norm_eq_zero R).mp hR_zero
    subst R
    let A : randomized_graph_algorithm n l := fun _ => Measure.dirac 0
    let Z : Measure (Fin l → ℝ) := Measure.dirac 0
    refine ⟨A, Z, 0, le_rfl, ?_, ?_, ?_, ?_⟩
    · refine ⟨PUnit, inferInstance, fun _ _ => Measure.dirac PUnit.unit,
          fun _ => 0, ?_, ?_, ?_, ?_⟩
      · intro i N
        infer_instance
      · fun_prop
      · intro G
        dsimp [A]
        simp
      · intro G H hGH
        unfold distribution_indistinguishable
        intro S hS
        constructor <;>
          calc
            (Measure.pi fun i : Fin n => Measure.dirac PUnit.unit) S =
                1 * (Measure.pi fun i : Fin n => Measure.dirac PUnit.unit) S := by
                  simp
            _ ≤ ENNReal.ofReal (Real.exp ε) *
                (Measure.pi fun i : Fin n => Measure.dirac PUnit.unit) S := by
                  gcongr
                  simp [Real.one_le_exp hε_pos.le]
            _ ≤ ENNReal.ofReal (Real.exp ε) *
                  (Measure.pi fun i : Fin n => Measure.dirac PUnit.unit) S +
                ENNReal.ofReal δ := le_add_right le_rfl
    · exact all_epsilon_staircase_gaussian_uniform_linear_image Z 0 le_rfl (by
        constructor
        · infer_instance
        · intro a
          dsimp [Z]
          simp [gaussianReal_zero_var])
    · intro G
      dsimp [A, Z]
      simp
    · rw [hR_zero]
      simp
  · have hR_pos : 0 < max_column_two_norm R :=
      lt_of_le_of_ne hR_nonneg (Ne.symm hR_zero)
    let c : ℝ := all_epsilon_privacy_scale ε δ
    have hratio : 1 < (1.25 : ℝ) / δ :=
      (lt_div_iff₀ hδ).2 (by nlinarith)
    have hc_pos : 0 < c := by
      dsimp [c, all_epsilon_privacy_scale]
      unfold privacy_scale
      have : 0 < Real.log (1.25 / δ) := Real.log_pos hratio
      positivity
    let B : ℝ := 1 + (n : ℝ) / (s : ℝ) ^ 2
    have hB_pos : 0 < B := by
      dsimp [B]
      positivity
    let τ : ℝ := 8 * max_column_two_norm R * Real.sqrt B * c
    have hτ_pos : 0 < τ := by
      dsimp [τ]
      positivity
    let v : NNReal := Real.toNNReal (τ ^ 2)
    have hv_coe : (v : ℝ) = τ ^ 2 := by
      dsimp [v]
      exact max_eq_left (sq_nonneg τ)
    have hv_ne : v ≠ 0 := by
      intro hv
      have : (v : ℝ) = 0 := by simp [hv]
      rw [hv_coe] at this
      nlinarith
    let rowNoise : Measure (Fin l → ℝ) :=
      Measure.pi fun _ : Fin l => gaussianReal 0 v
    let localMean (N : Set (Fin n)) : Fin l → ℝ := fun j =>
      Matrix.mulVec R
        (fun b => rounding_weight s N.ncard b) j
    let localLaw : Fin n → Set (Fin n) → Measure (Fin l → ℝ) :=
      fun _ N => Measure.map (fun z => localMean N + z) rowNoise
    let postprocess : (Fin n → Fin l → ℝ) → (Fin l → ℝ) :=
      fun z j => (n : ℝ)⁻¹ * ∑ i, z i j
    let centeredTranscript : Measure (Fin n → Fin l → ℝ) :=
      Measure.pi fun _ : Fin n => rowNoise
    let A : randomized_graph_algorithm n l := fun G =>
      Measure.map postprocess
        (Measure.pi fun i => localLaw i {u | G.Adj i u})
    let Z : Measure (Fin l → ℝ) :=
      Measure.map postprocess centeredTranscript
    let σ : ℝ := τ / Real.sqrt n
    have hσ_nonneg : 0 ≤ σ := by
      dsimp [σ]
      positivity
    have hncard (G : graph_on n) (i : Fin n) :
        Set.ncard {u | G.Adj i u} = G.degree i := by
      change (G.neighborSet i).ncard = G.degree i
      calc
        (G.neighborSet i).ncard = Fintype.card (G.neighborSet i) :=
          (Set.fintypeCard_eq_ncard (s := G.neighborSet i)).symm
        _ = G.degree i := G.card_neighborSet_eq_degree (v := i)
    have hlocal_gaussian (N : Set (Fin n)) :
        Measure.map (fun z => localMean N + z) rowNoise =
          Measure.pi fun j : Fin l => gaussianReal (localMean N j) v := by
      dsimp [rowNoise]
      change Measure.map (fun z j => localMean N j + z j)
          (Measure.pi fun _ : Fin l => gaussianReal 0 v) = _
      rw [Measure.pi_map_pi]
      · congr 1
        funext j
        simpa using
          (gaussianReal_map_const_add (μ := 0) (v := v) (localMean N j))
      · intro j
        fun_prop
    have havg_mean (G : graph_on n) :
        postprocess (fun i => localMean {u | G.Adj i u}) =
          Matrix.mulVec R (compressed_blurry_degree_distribution s G) := by
      funext j
      dsimp [postprocess, localMean]
      simp_rw [hncard G]
      change (n : ℝ)⁻¹ *
          ∑ i : Fin n, ∑ b : Fin (blur_dimension n s),
            R j b * rounding_weight s (G.degree i) b =
        ∑ b : Fin (blur_dimension n s),
          R j b * ((n : ℝ)⁻¹ *
            ∑ i : Fin n, rounding_weight s (G.degree i) b)
      calc
        (n : ℝ)⁻¹ *
            ∑ i : Fin n, ∑ b : Fin (blur_dimension n s),
              R j b * rounding_weight s (G.degree i) b =
            ∑ i : Fin n, ∑ b : Fin (blur_dimension n s),
              (n : ℝ)⁻¹ *
                (R j b * rounding_weight s (G.degree i) b) := by
                  simp_rw [Finset.mul_sum]
        _ = ∑ b : Fin (blur_dimension n s), ∑ i : Fin n,
              (n : ℝ)⁻¹ *
                (R j b * rounding_weight s (G.degree i) b) :=
          Finset.sum_comm
        _ = ∑ b : Fin (blur_dimension n s),
              R j b * ((n : ℝ)⁻¹ *
                ∑ i : Fin n, rounding_weight s (G.degree i) b) := by
          apply Finset.sum_congr rfl
          intro b hb
          calc
            (∑ i : Fin n, (n : ℝ)⁻¹ *
                (R j b * rounding_weight s (G.degree i) b)) =
                ∑ i : Fin n, R j b *
                  ((n : ℝ)⁻¹ * rounding_weight s (G.degree i) b) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = R j b * ((n : ℝ)⁻¹ *
                ∑ i : Fin n, rounding_weight s (G.degree i) b) := by
              rw [← mul_assoc, Finset.mul_sum]
              simp only [mul_assoc]
    have htranscript_shift (G : graph_on n) :
        Measure.pi (fun i => localLaw i {u | G.Adj i u}) =
          Measure.map
            (fun z i => localMean {u | G.Adj i u} + z i)
            centeredTranscript := by
      symm
      dsimp [centeredTranscript]
      rw [Measure.pi_map_pi]
      intro i
      fun_prop
    refine ⟨A, Z, σ, hσ_nonneg, ?_, ?_, ?_, ?_⟩
    · refine ⟨Fin l → ℝ, inferInstance, localLaw, postprocess, ?_, ?_, ?_, ?_⟩
      · intro i N
        dsimp [localLaw]
        exact Measure.isProbabilityMeasure_map (by fun_prop)
      · fun_prop
      · intro G
        rfl
      · intro G H hGH
        let mG : Fin n → Fin l → ℝ := fun i j =>
          Matrix.mulVec R
            (fun b => rounding_weight s (G.degree i) b) j
        let mH : Fin n → Fin l → ℝ := fun i j =>
          Matrix.mulVec R
            (fun b => rounding_weight s (H.degree i) b) j
        have hmeasureG :
            Measure.pi (fun i => localLaw i {u | G.Adj i u}) =
              Measure.pi fun i : Fin n =>
                Measure.pi fun j : Fin l => gaussianReal (mG i j) v := by
          congr 1
          funext i
          dsimp [localLaw]
          rw [hlocal_gaussian]
          congr 1
          funext j
          simp [localMean, mG, hncard G i]
        have hmeasureH :
            Measure.pi (fun i => localLaw i {u | H.Adj i u}) =
              Measure.pi fun i : Fin n =>
                Measure.pi fun j : Fin l => gaussianReal (mH i j) v := by
          congr 1
          funext i
          dsimp [localLaw]
          rw [hlocal_gaussian]
          congr 1
          funext j
          simp [localMean, mH, hncard H i]
        rw [hmeasureG, hmeasureH]
        apply linear_queries_blurry_nested_gaussian_product_private
            mG mH v hv_ne ε δ hε_pos hδ.le
        let q : ℝ := (v : ℝ)⁻¹ *
          ∑ i, ∑ j, (mG i j - mH i j) ^ 2
        have hsum_nonneg :
            0 ≤ ∑ i, ∑ j, (mG i j - mH i j) ^ 2 :=
          Finset.sum_nonneg fun i hi =>
            Finset.sum_nonneg fun j hj => sq_nonneg _
        have hq_nonneg : 0 ≤ q := by
          dsimp [q]
          positivity
        have hsensitivity :
            ∑ i, ∑ j, (mG i j - mH i j) ^ 2 ≤
              4 * (max_column_two_norm R) ^ 2 * B := by
          simpa [mG, mH, B] using
            linear_queries_blurry_message_sensitivity hs R G H hGH
        have hq_bound : q ≤ (16 * c ^ 2)⁻¹ := by
          calc
            q ≤ (τ ^ 2)⁻¹ *
                (4 * (max_column_two_norm R) ^ 2 * B) := by
              dsimp [q]
              rw [hv_coe]
              exact mul_le_mul_of_nonneg_left hsensitivity
                (inv_nonneg.mpr (sq_nonneg τ))
            _ = (16 * c ^ 2)⁻¹ := by
              have hτ_sq :
                  τ ^ 2 = 64 * (max_column_two_norm R) ^ 2 * B * c ^ 2 := by
                dsimp [τ]
                nlinarith [Real.sq_sqrt hB_pos.le]
              rw [hτ_sq]
              field_simp [hR_pos.ne', hB_pos.ne', hc_pos.ne']
              norm_num
        simpa [q, c] using
          all_epsilon_staircase_privacy_tail
            ε δ q hε hδ hδ_one hq_nonneg hq_bound
    · apply all_epsilon_staircase_gaussian_uniform_linear_image Z σ hσ_nonneg
      constructor
      · dsimp [Z]
        exact Measure.isProbabilityMeasure_map (by fun_prop)
      · intro a
        dsimp [Z]
        rw [Measure.map_map]
        · convert linear_queries_blurry_nested_gaussian_sum
              (a := fun i j => (n : ℝ)⁻¹ * a j) v using 1
          · congr 1
            funext z
            dsimp [postprocess]
            calc
              (∑ j : Fin l, a j * ((n : ℝ)⁻¹ * ∑ i : Fin n, z i j)) =
                  ∑ j : Fin l, ∑ i : Fin n,
                    (n : ℝ)⁻¹ * a j * z i j := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [← mul_assoc, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                ring
              _ = ∑ i : Fin n, ∑ j : Fin l,
                    (n : ℝ)⁻¹ * a j * z i j := Finset.sum_comm
          · congr 2
            dsimp [σ]
            rw [hv_coe]
            have hsqrt_n : (Real.sqrt (n : ℝ)) ^ 2 = n := by
              rw [Real.sq_sqrt hn_real.le]
            rw [show (∑ i : Fin n, ∑ j : Fin l,
                  ((n : ℝ)⁻¹ * a j) ^ 2) =
                (n : ℝ) * (n : ℝ)⁻¹ ^ 2 *
                  ∑ j : Fin l, (a j) ^ 2 by
              simp_rw [mul_pow, Finset.mul_sum]
              simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
              rw [Finset.mul_sum]
              ring_nf]
            rw [div_pow, hsqrt_n]
            field_simp
        · fun_prop
        · fun_prop
    · intro G
      dsimp [A, Z]
      rw [htranscript_shift]
      rw [Measure.map_map, Measure.map_map]
      · congr 1
        funext z
        funext j
        dsimp [postprocess]
        simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
        rw [show (n : ℝ)⁻¹ *
              ∑ i, localMean {u | G.Adj i u} j =
            postprocess (fun i => localMean {u | G.Adj i u}) j by rfl]
        rw [havg_mean G]
      all_goals fun_prop
    · have harg_nonneg :
          0 ≤ (n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2 := by positivity
      have hB_eq :
          B = (n : ℝ) *
            ((n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2) := by
        dsimp [B]
        field_simp
      have hsqrt_B :
          Real.sqrt B = Real.sqrt n *
            Real.sqrt ((n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2) := by
        rw [hB_eq, Real.sqrt_mul hn_real.le]
      dsimp [σ, τ, c]
      rw [hsqrt_B]
      field_simp [Real.sqrt_ne_zero'.mpr hn_real]
      rfl

@[blueprint "lem:linear-queries-blurry-all-epsilon"
  (statement := /-- There is an absolute constant $C_{\mathrm{lin}}>0$ with the following property.  For every $\varepsilon>0$, every $\delta\in(0,1]$, positive natural numbers $n,s$, every $\ell\in\mathbb N$, and every $R\in\mathbb R^{\ell\times d_{\mathrm{blur}}}$, there exist an $(\varepsilon,\delta)$-LNDP algorithm $\mathcal A_R$, a probability law $Z$ on $\mathbb R^\ell$, and $\sigma\ge0$ such that $\mathcal A_R(G)$ has the law of $R\widetilde p_{G,s}+Z$ for every graph $G$ on $[n]$.  The law $Z$ is either centered isotropic Gaussian of scale $\sigma$ or has the uniform linear-image bound of scale $\sigma$, and
  \[
    \sigma\le C_{\mathrm{lin}}\|R\|_{1\to2}
      \sqrt{\frac1n+\frac1{s^2}}\,c^*_{\varepsilon,\delta},
  \]
  where
  \[
    c^*_{\varepsilon,\delta}
      =\frac{\sqrt{2\log(1.25/\delta)}}{\varepsilon}
        +\sqrt{\frac1\varepsilon}
  \]
  is the all-$\varepsilon$ Gaussian privacy scale from
  \cref{def:all-epsilon-privacy-scale}. -/)
  (proof := /-- Let $C_0>0$ and $C_1>0$ be the absolute constants supplied
  by \cref{lem:linear-queries-blurry} and
  \cref{lem:all-epsilon-staircase-linear-queries}, respectively, and set
  $C_{\mathrm{lin}}=\max\{C_0,C_1\}$.  Fix admissible parameters.  If
  $\varepsilon\le1$, apply the former lemma.  It supplies all the asserted
  algorithmic and distributional conclusions with noise bounded using
  $c_{\varepsilon,\delta}$.  Since $\varepsilon>0$, the quantity
  $\sqrt{1/\varepsilon}$ is nonnegative, and hence
  $c_{\varepsilon,\delta}\le c^*_{\varepsilon,\delta}$; the nonnegativity
  of $\|R\|_{1\to2}$ and of the square-root factor then gives the displayed
  bound with $C_{\mathrm{lin}}$.  If $\varepsilon>1$, apply the latter
  lemma, which supplies the same conclusions with noise bounded directly
  using $c^*_{\varepsilon,\delta}$ and the constant $C_1\le
  C_{\mathrm{lin}}$.  These two cases exhaust every $\varepsilon>0$. -/)
  (title := /-- Linear queries for all privacy parameters -/)
  (latexEnv := "lemma")]
lemma linear_queries_blurry_all_epsilon :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε δ : ℝ) (n s l : ℕ)
        (R : Matrix (Fin l) (Fin (blur_dimension n s)) ℝ),
        0 < ε → 0 < δ → δ ≤ 1 →
        0 < n → 0 < s →
        ∃ (A : randomized_graph_algorithm n l)
          (Z : Measure (Fin l → ℝ)) (σ : ℝ),
          0 ≤ σ ∧
          is_lndp ε δ A ∧
          (is_isotropic_gaussian_vector Z σ ∨
            has_uniform_linear_image_bound Z σ) ∧
          (∀ G : graph_on n,
            A G = Measure.map
              (fun z => Matrix.mulVec R (compressed_blurry_degree_distribution s G) + z) Z) ∧
          σ ≤ C * max_column_two_norm R *
            Real.sqrt ((n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2) *
            all_epsilon_privacy_scale ε δ := by
  classical
  obtain ⟨C₀, hC₀, h₀⟩ := linear_queries_blurry
  obtain ⟨C₁, hC₁, h₁⟩ := all_epsilon_staircase_linear_queries
  refine ⟨max C₀ C₁, lt_of_lt_of_le hC₀ (le_max_left C₀ C₁), ?_⟩
  intro ε δ n s l R hε hδ hδ_one hn hs
  have hR_nonneg : 0 ≤ max_column_two_norm R := by
    rw [max_column_two_norm_eq_pi_norm]
    exact norm_nonneg _
  have hsq_nonneg : 0 ≤ Real.sqrt ((n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2) := Real.sqrt_nonneg _
  have hscale_nonneg : 0 ≤ privacy_scale ε δ := by
    show (0 : ℝ) ≤ Real.sqrt (2 * Real.log (1.25 / δ)) / ε
    exact div_nonneg (Real.sqrt_nonneg _) hε.le
  have hscale_le : privacy_scale ε δ ≤ all_epsilon_privacy_scale ε δ := by
    have hroot : (0 : ℝ) ≤ Real.sqrt ε⁻¹ := Real.sqrt_nonneg _
    show privacy_scale ε δ ≤ privacy_scale ε δ + Real.sqrt ε⁻¹
    linarith
  rcases le_or_gt ε 1 with hle | hgt
  · obtain ⟨A, Z, σ, hσ, hlndp, hnoise, hmap, hbound⟩ :=
      h₀ ε δ n s l R hε hle hδ hδ_one hn hs
    refine ⟨A, Z, σ, hσ, hlndp, hnoise, hmap, hbound.trans ?_⟩
    refine mul_le_mul ?_ hscale_le hscale_nonneg ?_
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C₀ C₁) hR_nonneg) hsq_nonneg
    · exact mul_nonneg
        (mul_nonneg (le_trans hC₀.le (le_max_left C₀ C₁)) hR_nonneg) hsq_nonneg
  · obtain ⟨A, Z, σ, hσ, hlndp, hnoise, hmap, hbound⟩ :=
      h₁ ε δ n s l R hgt hδ hδ_one hn hs
    refine ⟨A, Z, σ, hσ, hlndp, Or.inr hnoise, hmap, hbound.trans ?_⟩
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right C₀ C₁) hR_nonneg) hsq_nonneg)
      (le_trans hscale_nonneg hscale_le)

@[blueprint "lem:lndp-linear-postprocessing"
  (statement := /-- Let $n,\ell,k\in\mathbb N$ and $\varepsilon,\delta\in\mathbb R$.  If $\mathcal A$ is an $(\varepsilon,\delta)$-LNDP algorithm on graphs on $[n]$ with outputs in $\mathbb R^\ell$, then, for every $L\in\mathbb R^{k\times\ell}$, there exists an $(\varepsilon,\delta)$-LNDP algorithm $\mathcal B$ with outputs in $\mathbb R^k$ such that, for every graph $G$ on $[n]$, the law $\mathcal B(G)$ is the pushforward of $\mathcal A(G)$ under $x\mapsto Lx$. -/)
  (proof := /-- Unpack the local laws and measurable postprocessing map witnessing \cref{def:is-lndp}.  The linear map $f(x)=Lx$ is continuous and hence measurable, so the composite of $f$ with the original postprocessing map is measurable.  Retain the original local laws: their probability-measure property and the $(\varepsilon,\delta)$-indistinguishability of their transcript laws are therefore unchanged.  Define $\mathcal B(G)$ to be the pushforward of $\mathcal A(G)$ under $f$.  The representation of $\mathcal A(G)$ as the pushforward of its transcript law, together with functoriality of pushforwards, identifies $\mathcal B(G)$ with the pushforward under the composite postprocessing map.  These data witness that $\mathcal B$ is $(\varepsilon,\delta)$-LNDP and give the required identity for every $G$. -/)
  (title := /-- Linear postprocessing preserves LNDP -/)
  (latexEnv := "lemma")]
lemma lndp_linear_postprocessing {n l k : ℕ} {ε δ : ℝ}
    (A : randomized_graph_algorithm n l) (hA : is_lndp ε δ A)
    (L : Matrix (Fin k) (Fin l) ℝ) :
    ∃ B : randomized_graph_algorithm n k,
      is_lndp ε δ B ∧
      ∀ G : graph_on n,
        B G = Measure.map (fun x => Matrix.mulVec L x) (A G) := by
  let f : (Fin l → ℝ) → (Fin k → ℝ) := fun x => Matrix.mulVec L x
  have hf : Measurable f := (continuous_const.matrix_mulVec continuous_id).measurable
  refine ⟨fun G => Measure.map f (A G), ?_, fun G => rfl⟩
  rcases hA with
    ⟨Message, mMessage, localLaw, postprocess, hlocal, hpostprocess,
      hrepresentation, hprivate⟩
  refine
    ⟨Message, mMessage, localLaw, f ∘ postprocess, hlocal,
      hf.comp hpostprocess, ?_, hprivate⟩
  intro G
  simp only [hrepresentation G, Measure.map_map hf hpostprocess]

@[blueprint "lem:approximate-factorization-error"
  (statement := /-- Let $n,s,k\in\mathbb N$ satisfy $n>0$ and $s>0$, let $\alpha\in\mathbb R$, and let $E\in\mathbb R^{k\times d_{\mathrm{blur}}}$ satisfy $\|E\|_{1\to\infty}\le\alpha$.  Then, for every graph $G$ on $[n]$,
  \[
    \|E\widetilde p_{G,s}\|_\infty\le\alpha.
  \] -/)
  (proof := /-- By \cref{lem:max-entry-norm-eq-pi-norm}, every entry of $E$ has absolute value at most $\|E\|_{1\to\infty}$; in particular, the hypothesis implies $\alpha\ge 0$.  Fix a row $i$.  The triangle inequality for the finite dot product gives
  \[
    |(E\widetilde p_{G,s})_i|
    \le \sum_j |E_{ij}|\,|\widetilde p_{G,s}(j)|
    \le \|E\|_{1\to\infty}
       \sum_j |\widetilde p_{G,s}(j)|.
  \]
  The final sum equals one by \cref{lem:compressed-blurry-degree-distribution-normalized}, so every coordinate is at most $\|E\|_{1\to\infty}\le\alpha$.  The characterization of the finite product norm by its coordinate bounds now yields the claim. -/)
  (title := /-- Error from approximate factorization -/)
  (latexEnv := "lemma")]
lemma approximate_factorization_error {n s k : ℕ}
    (hn : 0 < n) (hs : 0 < s)
    (E : Matrix (Fin k) (Fin (blur_dimension n s)) ℝ)
    (α : ℝ) (hE : max_entry_norm E ≤ α) (G : graph_on n) :
    ‖Matrix.mulVec E (compressed_blurry_degree_distribution s G)‖ ≤ α := by
  classical
  have hα : 0 ≤ α := by
    calc
      0 ≤ max_entry_norm E := by
        rw [max_entry_norm_eq_pi_norm]
        exact norm_nonneg _
      _ ≤ α := hE
  apply (pi_norm_le_iff_of_nonneg hα).2
  intro i
  rw [Real.norm_eq_abs, Matrix.mulVec_apply]
  unfold dotProduct
  calc
    |∑ j, E i j * compressed_blurry_degree_distribution s G j| ≤
        ∑ j, |E i j * compressed_blurry_degree_distribution s G j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |E i j| * |compressed_blurry_degree_distribution s G j| := by
      simp only [abs_mul]
    _ ≤ ∑ j, max_entry_norm E *
        |compressed_blurry_degree_distribution s G j| := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right
      · rw [max_entry_norm_eq_pi_norm]
        simpa only [Real.norm_eq_abs, abs_abs] using
          (norm_le_pi_norm
            (f := fun p : Fin k × Fin (blur_dimension n s) => |E p.1 p.2|)
            (i, j))
      · exact abs_nonneg _
    _ = max_entry_norm E *
        ∑ j, |compressed_blurry_degree_distribution s G j| := by
      rw [Finset.mul_sum]
    _ = max_entry_norm E := by
      rw [compressed_blurry_degree_distribution_normalized hn hs G, mul_one]
    _ ≤ α := hE

@[blueprint "lem:gaussian-linear-image-expected-sup-norm"
  (statement := /-- Let $k,\ell\in\mathbb N$, let $Z$ be a centered isotropic Gaussian vector of scale $\sigma\ge0$ in $\mathbb R^\ell$, and let $L\in\mathbb R^{k\times\ell}$.  The function $z\mapsto\|Lz\|_\infty$ is integrable with respect to the law of $Z$, and
  \[
    \mathbb E\|LZ\|_\infty
    \le
    \sigma\|L\|_{2\to\infty}\sqrt{2\log(2k)}.
  \] -/)
  (proof := /-- If $k=0$, every vector in $\mathbb R^k$ is zero, so the integrand and its integral vanish.  Suppose $k>0$, and put $S=\sigma\|L\|_{2\to\infty}$.  By \cref{def:is-isotropic-gaussian-vector}, for every row $i$ the coordinate $X_i(z)=(Lz)_i$ has centered Gaussian law with variance $\sigma^2\sum_jL_{ij}^2$.  Its positive and negative exponential moments are therefore finite, which implies that each $X_i$, and hence the finite maximum $\|Lz\|_\infty$, is integrable.  By \cref{def:max-row-two-norm}, every coordinate variance is at most $S^2$.

  If $S=0$, every coordinate law is the Dirac measure at zero.  Thus $Lz=0$ almost everywhere and the asserted bound follows.  Assume $S>0$.  For $t\ge0$, attainment of the supremum norm in finite dimension gives the pointwise soft-maximum inequality
  \[
    \exp\!\bigl(t\|Lz\|_\infty\bigr)
    \le \sum_{i=1}^k\bigl(\exp(tX_i(z))+\exp(-tX_i(z))\bigr).
  \]
  Integrating and using the exact Gaussian moment-generating function and the variance bound yields
  \[
    \mathbb E\exp\!\bigl(t\|LZ\|_\infty\bigr)
    \le 2k\exp(t^2S^2/2).
  \]
  The inequality $1+u\le e^u$, applied pointwise with $u=t\|Lz\|_\infty-\mathbb E[t\|LZ\|_\infty]$ and then integrated, gives
  \[
    \exp\!\bigl(t\,\mathbb E\|LZ\|_\infty\bigr)
    \le \mathbb E\exp\!\bigl(t\|LZ\|_\infty\bigr).
  \]
  Taking logarithms therefore shows
  \[
    t\,\mathbb E\|LZ\|_\infty
    \le \log(2k)+t^2S^2/2.
  \]
  Choosing $t=\sqrt{2\log(2k)}/S$ proves the claimed estimate. -/)
  (title := /-- Expected supremum norm of a Gaussian linear image -/)
  (latexEnv := "lemma")]
lemma gaussian_linear_image_expected_sup_norm {l k : ℕ}
    (Z : Measure (Fin l → ℝ)) (σ : ℝ)
    (hσ : 0 ≤ σ) (hZ : is_isotropic_gaussian_vector Z σ)
    (L : Matrix (Fin k) (Fin l) ℝ) :
    Integrable (fun z => ‖Matrix.mulVec L z‖) Z ∧
      (∫ z, ‖Matrix.mulVec L z‖ ∂Z) ≤
        σ * max_row_two_norm L *
          Real.sqrt (2 * Real.log (2 * (k : ℝ))) := by
  classical
  by_cases hk : k = 0
  · subst k
    have hfun : (fun z => ‖Matrix.mulVec L z‖) = (fun _ => (0 : ℝ)) := by
      funext z
      have hz : Matrix.mulVec L z = 0 := Subsingleton.elim _ _
      rw [hz]
      simp
    rw [hfun]
    simp [max_row_two_norm]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    let i0 : Fin k := ⟨0, hkpos⟩
    have huniv : (Finset.univ : Finset (Fin k)).Nonempty :=
      ⟨i0, Finset.mem_univ i0⟩
    rcases hZ with ⟨hprob, hgauss⟩
    letI : IsProbabilityMeasure Z := hprob
    have hmeas (i : Fin k) :
        Measurable (fun z => Matrix.mulVec L z i) := by
      fun_prop
    have hmap (i : Fin k) :
        Measure.map (fun z => Matrix.mulVec L z i) Z =
          gaussianReal 0
            (Real.toNNReal (σ ^ 2 * ∑ j : Fin l, (L i j) ^ 2)) := by
      simpa [Matrix.mulVec, dotProduct] using hgauss (L i)
    have hexp (i : Fin k) (t : ℝ) :
        Integrable (fun z => Real.exp (t * Matrix.mulVec L z i)) Z := by
      have hg_meas : Measurable (fun x : ℝ => Real.exp (t * x)) := by
        fun_prop
      have hg : Integrable (fun x : ℝ => Real.exp (t * x))
          (Measure.map (fun z => Matrix.mulVec L z i) Z) := by
        rw [hmap i]
        exact ProbabilityTheory.integrable_exp_mul_gaussianReal t
      simpa [Function.comp_def] using
        (MeasureTheory.integrable_map_measure hg_meas.aestronglyMeasurable
          (hmeas i).aemeasurable).mp hg
    have hcoord_int (i : Fin k) :
        Integrable (fun z => Matrix.mulVec L z i) Z := by
      refine Integrable.mono' ((hexp i 1).add (hexp i (-1)))
        (hmeas i).aestronglyMeasurable ?_
      refine ae_of_all Z (fun z => ?_)
      simp only [Pi.add_apply, one_mul, neg_mul, Real.norm_eq_abs]
      rw [abs_le]
      constructor <;>
        linarith [Real.add_one_le_exp (Matrix.mulVec L z i),
          Real.add_one_le_exp (-Matrix.mulVec L z i),
          Real.exp_pos (Matrix.mulVec L z i),
          Real.exp_pos (-Matrix.mulVec L z i)]
    have hnorm_eq (x : Fin k → ℝ) : ∃ i : Fin k, ‖x‖ = |x i| := by
      obtain ⟨i, hi, heq⟩ :=
        Finset.exists_mem_eq_sup Finset.univ huniv
          (fun i : Fin k => ‖x i‖₊)
      refine ⟨i, ?_⟩
      rw [Pi.norm_def, heq]
      simp
    have hnorm_int : Integrable (fun z => ‖Matrix.mulVec L z‖) Z := by
      have hsum_int :
          Integrable (fun z => ∑ i : Fin k, |Matrix.mulVec L z i|) Z :=
        integrable_finsetSum Finset.univ (fun i hi => (hcoord_int i).abs)
      refine Integrable.mono hsum_int (by fun_prop) ?_
      refine ae_of_all Z (fun z => ?_)
      obtain ⟨i, hi⟩ := hnorm_eq (Matrix.mulVec L z)
      rw [hi]
      have hs := Finset.single_le_sum
        (fun j _ => abs_nonneg (Matrix.mulVec L z j)) (Finset.mem_univ i)
      have hsum_nonneg : 0 ≤ ∑ j : Fin k, |Matrix.mulVec L z j| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      simpa only [Real.norm_eq_abs, abs_abs, abs_of_nonneg hsum_nonneg] using hs
    have hrow_le (i : Fin k) :
        Real.sqrt (∑ j : Fin l, (L i j) ^ 2) ≤ max_row_two_norm L := by
      unfold max_row_two_norm
      exact le_csSup (Set.finite_range _).bddAbove ⟨i, rfl⟩
    have hM_nonneg : 0 ≤ max_row_two_norm L :=
      le_trans (Real.sqrt_nonneg _) (hrow_le i0)
    have hvar_le (i : Fin k) :
        (Real.toNNReal (σ ^ 2 * ∑ j : Fin l, (L i j) ^ 2) : ℝ) ≤
          (σ * max_row_two_norm L) ^ 2 := by
      rw [Real.coe_toNNReal]
      · have hr : 0 ≤ ∑ j : Fin l, (L i j) ^ 2 :=
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        have hrle : (∑ j : Fin l, (L i j) ^ 2) ≤
            (max_row_two_norm L) ^ 2 := by
          nlinarith [Real.sq_sqrt hr,
            Real.sqrt_nonneg (∑ j : Fin l, (L i j) ^ 2), hrow_le i]
        calc
          σ ^ 2 * (∑ j : Fin l, (L i j) ^ 2) ≤
              σ ^ 2 * (max_row_two_norm L) ^ 2 :=
            mul_le_mul_of_nonneg_left hrle (sq_nonneg σ)
          _ = (σ * max_row_two_norm L) ^ 2 := by ring
      · positivity
    have hmoment (i : Fin k) (t : ℝ) :
        (∫ z, Real.exp (t * Matrix.mulVec L z i) ∂Z) =
          Real.exp ((Real.toNNReal
            (σ ^ 2 * ∑ j : Fin l, (L i j) ^ 2) : ℝ) * t ^ 2 / 2) := by
      simpa [ProbabilityTheory.mgf] using
        ProbabilityTheory.mgf_gaussianReal (hmap i) t
    have hsoft (t : ℝ) (ht : 0 ≤ t) (x : Fin k → ℝ) :
        Real.exp (t * ‖x‖) ≤
          ∑ i : Fin k, (Real.exp (t * x i) + Real.exp ((-t) * x i)) := by
      obtain ⟨i, hi⟩ := hnorm_eq x
      rw [hi]
      calc
        Real.exp (t * |x i|) ≤
            Real.exp (t * x i) + Real.exp ((-t) * x i) := by
          by_cases hx : 0 ≤ x i
          · rw [abs_of_nonneg hx]
            exact le_add_of_nonneg_right (Real.exp_nonneg _)
          · rw [abs_of_neg (lt_of_not_ge hx)]
            simpa only [mul_neg, neg_mul] using
              le_add_of_nonneg_left (Real.exp_nonneg (t * x i))
        _ ≤ ∑ j : Fin k,
            (Real.exp (t * x j) + Real.exp ((-t) * x j)) := by
          exact Finset.single_le_sum
            (f := fun j : Fin k =>
              Real.exp (t * x j) + Real.exp ((-t) * x j))
            (fun j _ => add_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
            (Finset.mem_univ i)
    have hsumexp_int (t : ℝ) : Integrable
        (fun z => ∑ i : Fin k,
          (Real.exp (t * Matrix.mulVec L z i) +
            Real.exp ((-t) * Matrix.mulVec L z i))) Z :=
      integrable_finsetSum Finset.univ
        (fun i hi => (hexp i t).add (hexp i (-t)))
    have hnormexp_int (t : ℝ) (ht : 0 ≤ t) :
        Integrable (fun z => Real.exp (t * ‖Matrix.mulVec L z‖)) Z := by
      refine Integrable.mono' (hsumexp_int t) (by fun_prop) ?_
      refine ae_of_all Z (fun z => ?_)
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _),
        Pi.add_apply]
      exact hsoft t ht (Matrix.mulVec L z)
    have hjensen (t : ℝ) (ht : 0 ≤ t) :
        Real.exp (t * ∫ z, ‖Matrix.mulVec L z‖ ∂Z) ≤
          ∫ z, Real.exp (t * ‖Matrix.mulVec L z‖) ∂Z := by
      let X : (Fin l → ℝ) → ℝ := fun z => t * ‖Matrix.mulVec L z‖
      let m : ℝ := ∫ z, X z ∂Z
      have hX : Integrable X Z := hnorm_int.const_mul t
      have hexpX : Integrable (fun z => Real.exp (X z)) Z :=
        hnormexp_int t ht
      have hone : Integrable (fun _ : Fin l → ℝ => (1 : ℝ)) Z :=
        integrable_const 1
      have hm : Integrable (fun _ : Fin l → ℝ => m) Z :=
        integrable_const m
      have hlin : Integrable (fun z => Real.exp m * (1 + X z - m)) Z :=
        ((hone.add hX).sub hm).const_mul (Real.exp m)
      have hpw : ∀ z, Real.exp m * (1 + X z - m) ≤ Real.exp (X z) := by
        intro z
        calc
          Real.exp m * (1 + X z - m) ≤
              Real.exp m * Real.exp (X z - m) := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg m)
            simpa only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
              Real.add_one_le_exp (X z - m)
          _ = Real.exp (X z) := by
            rw [← Real.exp_add]
            congr 1
            ring
      have hi := integral_mono hlin hexpX hpw
      have hcenter : (∫ z, (1 + X z - m) ∂Z) = 1 := by
        calc
          (∫ z, (1 + X z - m) ∂Z) =
              (∫ z, (1 + X z) ∂Z) - ∫ _z, m ∂Z := by
            simpa only [Pi.add_apply] using
              integral_sub (hone.add hX) hm
          _ = ((∫ _z, (1 : ℝ) ∂Z) + ∫ z, X z ∂Z) -
              ∫ _z, m ∂Z := by
            rw [integral_add hone hX]
          _ = 1 := by simp [m]
      have heq : (∫ z, Real.exp m * (1 + X z - m) ∂Z) =
          Real.exp m := by
        rw [integral_const_mul, hcenter]
        ring
      rw [heq] at hi
      simpa [X, m, integral_const_mul] using hi
    have hsum_bound (t : ℝ) :
        (∫ z, ∑ i : Fin k,
          (Real.exp (t * Matrix.mulVec L z i) +
            Real.exp ((-t) * Matrix.mulVec L z i)) ∂Z) ≤
          (2 * (k : ℝ)) *
            Real.exp ((σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2) := by
      have hsplit :
          (∫ z, ∑ i : Fin k,
            (Real.exp (t * Matrix.mulVec L z i) +
              Real.exp ((-t) * Matrix.mulVec L z i)) ∂Z) =
            ∑ i : Fin k, (∫ z,
              (Real.exp (t * Matrix.mulVec L z i) +
                Real.exp ((-t) * Matrix.mulVec L z i)) ∂Z) := by
        simpa only [Finset.sum_apply, Pi.add_apply] using
          integral_finsetSum Finset.univ
            (fun i hi => (hexp i t).add (hexp i (-t)))
      rw [hsplit]
      calc
        ∑ i : Fin k, (∫ z, (Real.exp (t * Matrix.mulVec L z i) +
            Real.exp ((-t) * Matrix.mulVec L z i)) ∂Z) =
            ∑ i : Fin k, ((∫ z, Real.exp (t * Matrix.mulVec L z i) ∂Z) +
              (∫ z, Real.exp ((-t) * Matrix.mulVec L z i) ∂Z)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [integral_add (hexp i t) (hexp i (-t))]
        _ ≤ ∑ i : Fin k,
            (Real.exp ((σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2) +
              Real.exp ((σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2)) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [hmoment i t, hmoment i (-t)]
          apply add_le_add <;> apply Real.exp_le_exp.mpr
          · exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hvar_le i) (sq_nonneg t))
              (by norm_num)
          · simpa only [neg_sq] using
              (div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right (hvar_le i) (sq_nonneg t))
                (by norm_num))
        _ = (2 * (k : ℝ)) *
            Real.exp ((σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2) := by
          simp [Finset.sum_const]
          ring
    have hexp_bound (t : ℝ) (ht : 0 ≤ t) :
        (∫ z, Real.exp (t * ‖Matrix.mulVec L z‖) ∂Z) ≤
          (2 * (k : ℝ)) *
            Real.exp ((σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2) := by
      calc
        (∫ z, Real.exp (t * ‖Matrix.mulVec L z‖) ∂Z) ≤
            ∫ z, ∑ i : Fin k,
              (Real.exp (t * Matrix.mulVec L z i) +
                Real.exp ((-t) * Matrix.mulVec L z i)) ∂Z :=
          integral_mono (hnormexp_int t ht) (hsumexp_int t)
            (fun z => hsoft t ht (Matrix.mulVec L z))
        _ ≤ (2 * (k : ℝ)) *
            Real.exp ((σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2) :=
          hsum_bound t
    by_cases hS : σ * max_row_two_norm L = 0
    · have hvar_zero (i : Fin k) :
          σ ^ 2 * ∑ j : Fin l, (L i j) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hS with hσ0 | hM0
        · rw [hσ0]
          norm_num
        · have hr : 0 ≤ ∑ j : Fin l, (L i j) ^ 2 :=
            Finset.sum_nonneg (fun _ _ => sq_nonneg _)
          have hsqrt0 : Real.sqrt (∑ j : Fin l, (L i j) ^ 2) = 0 :=
            le_antisymm (by simpa [hM0] using hrow_le i) (Real.sqrt_nonneg _)
          have hr0 : (∑ j : Fin l, (L i j) ^ 2) = 0 := by
            nlinarith [Real.sq_sqrt hr]
          rw [hr0]
          ring
      have hzero (i : Fin k) : ∀ᵐ z ∂Z, Matrix.mulVec L z i = 0 := by
        have hm0 : Measure.map (fun z => Matrix.mulVec L z i) Z =
            Measure.dirac 0 := by
          rw [hmap i, hvar_zero i]
          simp
        apply (ae_map_iff (hmeas i).aemeasurable
          (measurableSet_singleton 0)).mp
        rw [hm0]
        exact (ae_dirac_iff (measurableSet_singleton 0)).2
          (Set.mem_singleton 0)
      have hall : ∀ᵐ z ∂Z, ∀ i : Fin k, Matrix.mulVec L z i = 0 :=
        ae_all_iff.mpr hzero
      have hnorm_zero : ∀ᵐ z ∂Z, ‖Matrix.mulVec L z‖ = 0 := by
        filter_upwards [hall] with z hz
        have hv : Matrix.mulVec L z = 0 := funext hz
        simp [hv]
      have hint_zero : (∫ z, ‖Matrix.mulVec L z‖ ∂Z) = 0 := by
        rw [integral_congr_ae hnorm_zero]
        simp
      exact ⟨hnorm_int, by rw [hint_zero, hS]; simp⟩
    · have hSpos : 0 < σ * max_row_two_norm L :=
        lt_of_le_of_ne (mul_nonneg hσ hM_nonneg) (Ne.symm hS)
      have hn_gt : 1 < 2 * (k : ℝ) := by
        exact_mod_cast (show 1 < 2 * k by omega)
      have hlogpos : 0 < Real.log (2 * (k : ℝ)) := Real.log_pos hn_gt
      let q : ℝ := Real.sqrt (2 * Real.log (2 * (k : ℝ)))
      have hqpos : 0 < q :=
        Real.sqrt_pos.2 (mul_pos (by norm_num) hlogpos)
      have hq_sq : q ^ 2 = 2 * Real.log (2 * (k : ℝ)) :=
        Real.sq_sqrt (by positivity)
      let t : ℝ := q / (σ * max_row_two_norm L)
      have htpos : 0 < t := div_pos hqpos hSpos
      have htS : t * (σ * max_row_two_norm L) = q := by
        dsimp [t]
        exact div_mul_cancel₀ q (ne_of_gt hSpos)
      have hchain :
          Real.exp (t * ∫ z, ‖Matrix.mulVec L z‖ ∂Z) ≤
            (2 * (k : ℝ)) *
              Real.exp ((σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2) :=
        (hjensen t htpos.le).trans (hexp_bound t htpos.le)
      have hlog : t * (∫ z, ‖Matrix.mulVec L z‖ ∂Z) ≤
          Real.log (2 * (k : ℝ)) +
            (σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2 := by
        calc
          t * (∫ z, ‖Matrix.mulVec L z‖ ∂Z) =
              Real.log (Real.exp
                (t * ∫ z, ‖Matrix.mulVec L z‖ ∂Z)) :=
            (Real.log_exp _).symm
          _ ≤ Real.log ((2 * (k : ℝ)) *
              Real.exp ((σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2)) :=
            Real.log_le_log (Real.exp_pos _) hchain
          _ = Real.log (2 * (k : ℝ)) +
              (σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2 := by
            rw [Real.log_mul
              (ne_of_gt (show 0 < 2 * (k : ℝ) by positivity))
              (ne_of_gt (Real.exp_pos _)), Real.log_exp]
      have hprod : (σ * max_row_two_norm L) ^ 2 * t ^ 2 = q ^ 2 := by
        calc
          (σ * max_row_two_norm L) ^ 2 * t ^ 2 =
              (t * (σ * max_row_two_norm L)) ^ 2 := by ring
          _ = q ^ 2 := by rw [htS]
      have hlog_eq : Real.log (2 * (k : ℝ)) = q ^ 2 / 2 := by
        nlinarith [hq_sq]
      have hopt : Real.log (2 * (k : ℝ)) +
          (σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2 = q ^ 2 := by
        rw [hlog_eq, hprod]
        ring
      refine ⟨hnorm_int, ?_⟩
      apply le_of_mul_le_mul_left _ htpos
      calc
        t * (∫ z, ‖Matrix.mulVec L z‖ ∂Z) ≤
            Real.log (2 * (k : ℝ)) +
              (σ * max_row_two_norm L) ^ 2 * t ^ 2 / 2 := hlog
        _ = q ^ 2 := hopt
        _ = t * (σ * max_row_two_norm L *
            Real.sqrt (2 * Real.log (2 * (k : ℝ)))) := by
          rw [show Real.sqrt (2 * Real.log (2 * (k : ℝ))) = q by rfl,
            ← htS]
          ring

@[blueprint "lem:factorization-accuracy-from-noise"
  (statement := /-- Let $n,s\in\mathbb N$ satisfy $n>0$ and $s>0$, let $k,\ell\in\mathbb N$, let $\alpha\in\mathbb R$ and $\sigma\ge0$, and let $W$, $L$, and $R$ be matrices of dimensions $k\times d_{\mathrm{blur}}$, $k\times\ell$, and $\ell\times d_{\mathrm{blur}}$, respectively, such that $\|LR-W\|_{1\to\infty}\le\alpha$.  Suppose that $Z$ is either centered isotropic Gaussian noise of scale $\sigma$ or a noise law with the uniform linear-image bound of scale $\sigma$, that $\mathcal A_R(G)$ has law $R\widetilde p_{G,s}+Z$ for every graph $G$ on $[n]$, and that $\mathcal B(G)$ is the law obtained by applying $L$ to $\mathcal A_R(G)$.  Then, for every graph $G$ on $[n]$,
  the function $y\mapsto\|y-W\widetilde p_{G,s}\|_\infty$ is integrable with respect to the output law $\mathcal B(G)$, and
  \[
    \mathbb E\!\left[
      \|\mathcal B(G)-W\widetilde p_{G,s}\|_\infty
    \right]
    \le
    \alpha+
    \sigma\|L\|_{2\to\infty}\sqrt{2\log(2k)}.
  \] -/)
  (proof := /-- Put $E=LR-W$.  The two pushforward identities and associativity of matrix multiplication identify the output error with
  $E\widetilde p_{G,s}+LZ$.  If $Z$ is Gaussian, \cref{lem:gaussian-linear-image-expected-sup-norm} shows that $\|LZ\|_\infty$ is integrable and bounds its expectation by $\sigma\|L\|_{2\to\infty}\sqrt{2\log(2k)}$; in the other case these two conclusions are exactly the uniform linear-image hypothesis.  Translation by the fixed vector $E\widetilde p_{G,s}$ therefore gives integrability of the output-error norm.  The triangle inequality and monotonicity of the integral split its expectation into the deterministic term and the noise term.  The deterministic term is at most $\alpha$ by \cref{lem:approximate-factorization-error}.  Adding the two estimates proves the asserted bound. -/)
  (title := /-- Accuracy of a postprocessed factorization mechanism -/)
  (latexEnv := "lemma")]
lemma factorization_accuracy_from_noise {n s k l : ℕ}
    (hn : 0 < n) (hs : 0 < s)
    (W : Matrix (Fin k) (Fin (blur_dimension n s)) ℝ)
    (L : Matrix (Fin k) (Fin l) ℝ)
    (R : Matrix (Fin l) (Fin (blur_dimension n s)) ℝ)
    (α σ : ℝ)
    (hfactor : max_entry_norm (L * R - W) ≤ α)
    (Z : Measure (Fin l → ℝ))
    (hσ : 0 ≤ σ)
    (hZ : is_isotropic_gaussian_vector Z σ ∨
      has_uniform_linear_image_bound Z σ)
    (A : randomized_graph_algorithm n l)
    (hA : ∀ G : graph_on n,
      A G = Measure.map
        (fun z => Matrix.mulVec R (compressed_blurry_degree_distribution s G) + z) Z)
    (B : randomized_graph_algorithm n k)
    (hB : ∀ G : graph_on n,
      B G = Measure.map (fun x => Matrix.mulVec L x) (A G))
    (G : graph_on n) :
    Integrable
        (fun y => ‖y - Matrix.mulVec W
          (compressed_blurry_degree_distribution s G)‖) (B G) ∧
      expected_workload_error s W G (B G) ≤
        α + σ * max_row_two_norm L *
          Real.sqrt (2 * Real.log (2 * (k : ℝ))) := by
  classical
  let p := compressed_blurry_degree_distribution s G
  let e := Matrix.mulVec (L * R - W) p
  have hprob : IsProbabilityMeasure Z := by
    exact hZ.elim (fun hz => hz.1) (fun hz => hz.1)
  letI : IsProbabilityMeasure Z := hprob
  have hnoise :
      Integrable (fun z => ‖Matrix.mulVec L z‖) Z ∧
        (∫ z, ‖Matrix.mulVec L z‖ ∂Z) ≤
          σ * max_row_two_norm L *
            Real.sqrt (2 * Real.log (2 * (k : ℝ))) := by
    exact hZ.elim
      (fun hz => gaussian_linear_image_expected_sup_norm Z σ hσ hz L)
      (fun hz => hz.2 k L)
  have he_bound : ‖e‖ ≤ α := by
    dsimp [e, p]
    exact approximate_factorization_error hn hs (L * R - W) α hfactor G
  have hout_meas : Measurable (fun z : Fin l → ℝ =>
      Matrix.mulVec L (Matrix.mulVec R p + z)) := by
    fun_prop
  have herr_meas : Measurable (fun y : Fin k → ℝ =>
      ‖y - Matrix.mulVec W p‖) := by
    fun_prop
  have hidentity (z : Fin l → ℝ) :
      Matrix.mulVec L (Matrix.mulVec R p + z) - Matrix.mulVec W p =
        e + Matrix.mulVec L z := by
    dsimp [e]
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.sub_mulVec]
    abel
  have hBG : B G = Measure.map (fun z =>
      Matrix.mulVec L (Matrix.mulVec R p + z)) Z := by
    rw [hB G, hA G, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hshift_int :
      Integrable (fun z => ‖e + Matrix.mulVec L z‖) Z := by
    refine Integrable.mono' ((integrable_const ‖e‖).add hnoise.1)
      (by fun_prop) ?_
    filter_upwards with z
    simpa only [Pi.add_apply, norm_norm] using
      (norm_add_le e (Matrix.mulVec L z))
  have houtput_int :
      Integrable (fun y => ‖y - Matrix.mulVec W p‖) (B G) := by
    rw [hBG]
    refine (MeasureTheory.integrable_map_measure
      herr_meas.aestronglyMeasurable hout_meas.aemeasurable).2 ?_
    change Integrable (fun z =>
      ‖Matrix.mulVec L (Matrix.mulVec R p + z) - Matrix.mulVec W p‖) Z
    simpa only [hidentity] using hshift_int
  refine ⟨houtput_int, ?_⟩
  change (∫ y, ‖y - Matrix.mulVec W p‖ ∂B G) ≤
    α + σ * max_row_two_norm L *
      Real.sqrt (2 * Real.log (2 * (k : ℝ)))
  rw [hBG,
    integral_map hout_meas.aemeasurable herr_meas.aestronglyMeasurable]
  simp_rw [hidentity]
  calc
    (∫ z, ‖e + Matrix.mulVec L z‖ ∂Z) ≤
        ∫ z, (‖e‖ + ‖Matrix.mulVec L z‖) ∂Z :=
      integral_mono hshift_int ((integrable_const ‖e‖).add hnoise.1)
        (fun z => norm_add_le e (Matrix.mulVec L z))
    _ = ‖e‖ + ∫ z, ‖Matrix.mulVec L z‖ ∂Z := by
      rw [integral_add (integrable_const ‖e‖) hnoise.1]
      simp
    _ ≤ α + σ * max_row_two_norm L *
        Real.sqrt (2 * Real.log (2 * (k : ℝ))) :=
      add_le_add he_bound hnoise.2

@[blueprint "thm:fact-mech-blurry"
  (statement := /-- There is an absolute constant $C>0$ such that the following holds.  Let $\varepsilon>0$, let $\delta\in(0,1]$, let $n,s$ be positive natural numbers, and let $k$ be a natural number.  Put $d_{\mathrm{blur}}=\lceil n/s\rceil+1$, let $\alpha\ge0$, and let $W\in\mathbb R^{k\times d_{\mathrm{blur}}}$.  There exists an $(\varepsilon,\delta)$-LNDP algorithm $\mathcal A_{\mathrm{fact}}^{W,\alpha}$ such that, for every graph $G$ on node set $[n]$, the function
  \[
    y\longmapsto\left\|y-W\widetilde p_{G,s}\right\|_\infty
  \]
  is integrable with respect to the output law of $\mathcal A_{\mathrm{fact}}^{W,\alpha}(G)$, and
  \[
    \mathbb E\!\left[
      \left\|\mathcal A_{\mathrm{fact}}^{W,\alpha}(G)
      -W\widetilde p_{G,s}\right\|_\infty
    \right]
    \le C\left(
      \alpha+\gamma_\alpha(W)
      \sqrt{\left(\frac1n+\frac1{s^2}\right)\log(2k)}\,
      c^*_{\varepsilon,\delta}\right),
  \]
  where
  \[
    c^*_{\varepsilon,\delta}
      =\frac{\sqrt{2\log(1.25/\delta)}}{\varepsilon}
        +\sqrt{\frac1\varepsilon}
  \]
  is the all-$\varepsilon$ Gaussian privacy scale from
  \cref{def:all-epsilon-privacy-scale}. -/)
  (proof := /-- Apply \cref{lem:approximate-factorization-attained} to choose $\ell,L,R$ with
  $\|LR-W\|_{1\to\infty}\le\alpha$ and
  $\|L\|_{2\to\infty}\|R\|_{1\to2}=\gamma_\alpha(W)$.
  Apply \cref{lem:linear-queries-blurry-all-epsilon} to $R$ using $\varepsilon>0$ and $\delta\in(0,1]$.  This gives an $(\varepsilon,\delta)$-LNDP algorithm whose output law on $G$ is that of
  $R\widetilde p_{G,s}+Z$, where $Z$ is either centered isotropic Gaussian or has the uniform linear-image bound, in either case with scale at most an absolute constant times
  \[
    \|R\|_{1\to2}
    \sqrt{\frac1n+\frac1{s^2}}\,c_{\varepsilon,\delta}.
  \]
  By \cref{lem:lndp-linear-postprocessing}, applying $L$ gives an $(\varepsilon,\delta)$-LNDP algorithm with the required output dimension.  For every graph $G$, \cref{lem:factorization-accuracy-from-noise} proves integrability of the output-error norm and bounds its expectation by
  \[
    \alpha+\sigma\|L\|_{2\to\infty}\sqrt{2\log(2k)}.
  \]
  Substitute the preceding estimate for $\sigma$ and the identity
  $\|L\|_{2\to\infty}\|R\|_{1\to2}=\gamma_\alpha(W)$.  If $k=0$, the output and workload vectors lie in the zero-dimensional space and hence the expected error is zero.  If $k\geq1$, then $\log(2k)>0$; together with the positivity of $n$ and $s$, this permits the nonnegative square-root factors to be combined.  Enlarging the absolute constant to absorb the factor $\sqrt2$ and to dominate the coefficient of $\alpha$ yields
  \[
    C\left(\alpha+\gamma_\alpha(W)
    \sqrt{\left(\frac1n+\frac1{s^2}\right)\log(2k)}\,
    c_{\varepsilon,\delta}\right),
  \]
  as required. -/)
  (title := /-- Applying the factorization mechanism to the compressed blurry degree distribution -/)
  (latexEnv := "theorem")]
theorem fact_mech_blurry :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε δ : ℝ) (n k s : ℕ) (α : ℝ)
        (W : Matrix (Fin k) (Fin (blur_dimension n s)) ℝ),
        0 < ε → 0 < δ → δ ≤ 1 →
        0 < n → 0 < s → 0 ≤ α →
        ∃ A : randomized_graph_algorithm n k,
          is_lndp ε δ A ∧
          ∀ G : graph_on n,
            Integrable
                (fun y => ‖y - Matrix.mulVec W
                  (compressed_blurry_degree_distribution s G)‖) (A G) ∧
              expected_workload_error s W G (A G) ≤
                C * (α + approximate_factorization_norm W α *
                  Real.sqrt (((n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2) *
                    Real.log (2 * (k : ℝ))) *
                  all_epsilon_privacy_scale ε δ) := by
  classical
  obtain ⟨Clin, hClin, hlin⟩ := linear_queries_blurry_all_epsilon
  refine ⟨max 1 (Clin * Real.sqrt 2),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro ε δ n k s α W hε hδ hδ_one hn hs hα
  obtain ⟨l, L, R, hfactor, hnorm⟩ := approximate_factorization_attained W α hα
  obtain ⟨A₀, Z, σ, hσ, hlndp, hZ, hmap, hbound⟩ :=
    hlin ε δ n s l R hε hδ hδ_one hn hs
  obtain ⟨B, hBlndp, hBmap⟩ := lndp_linear_postprocessing A₀ hlndp L
  refine ⟨B, hBlndp, fun G => ?_⟩
  obtain ⟨hint, hbd⟩ :=
    factorization_accuracy_from_noise hn hs W L R α σ hfactor Z hσ hZ A₀ hmap B hBmap G
  refine ⟨hint, hbd.trans ?_⟩
  have hrow : (0 : ℝ) ≤ max_row_two_norm L := by
    rw [max_row_two_norm_eq_pi_norm]
    exact norm_nonneg _
  have hcol : (0 : ℝ) ≤ max_column_two_norm R := by
    rw [max_column_two_norm_eq_pi_norm]
    exact norm_nonneg _
  have hargs : (0 : ℝ) ≤ (n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2 :=
    add_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (sq_nonneg _)
  have hscale : (0 : ℝ) ≤ all_epsilon_privacy_scale ε δ := by
    have hbase : (0 : ℝ) ≤ privacy_scale ε δ := by
      show (0 : ℝ) ≤ Real.sqrt (2 * Real.log (1.25 / δ)) / ε
      exact div_nonneg (Real.sqrt_nonneg _) hε.le
    have hroot : (0 : ℝ) ≤ Real.sqrt ε⁻¹ := Real.sqrt_nonneg _
    show (0 : ℝ) ≤ privacy_scale ε δ + Real.sqrt ε⁻¹
    linarith
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (Real.log (2 * (k : ℝ))),
    Real.sqrt_mul hargs (Real.log (2 * (k : ℝ))), ← hnorm]
  have hP : (0 : ℝ) ≤ max_row_two_norm L * max_column_two_norm R *
      (Real.sqrt ((n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2) *
        Real.sqrt (Real.log (2 * (k : ℝ)))) *
      all_epsilon_privacy_scale ε δ :=
    mul_nonneg (mul_nonneg (mul_nonneg hrow hcol)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) hscale
  have hstep : σ * max_row_two_norm L *
      (Real.sqrt 2 * Real.sqrt (Real.log (2 * (k : ℝ)))) ≤
      max 1 (Clin * Real.sqrt 2) *
        (max_row_two_norm L * max_column_two_norm R *
          (Real.sqrt ((n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2) *
            Real.sqrt (Real.log (2 * (k : ℝ)))) *
          all_epsilon_privacy_scale ε δ) := by
    calc σ * max_row_two_norm L *
          (Real.sqrt 2 * Real.sqrt (Real.log (2 * (k : ℝ))))
        ≤ Clin * max_column_two_norm R *
            Real.sqrt ((n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2) *
            all_epsilon_privacy_scale ε δ * max_row_two_norm L *
            (Real.sqrt 2 * Real.sqrt (Real.log (2 * (k : ℝ)))) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hbound hrow)
            (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = Clin * Real.sqrt 2 *
            (max_row_two_norm L * max_column_two_norm R *
              (Real.sqrt ((n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2) *
                Real.sqrt (Real.log (2 * (k : ℝ)))) *
              all_epsilon_privacy_scale ε δ) := by ring
      _ ≤ max 1 (Clin * Real.sqrt 2) *
            (max_row_two_norm L * max_column_two_norm R *
              (Real.sqrt ((n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2) *
                Real.sqrt (Real.log (2 * (k : ℝ)))) *
              all_epsilon_privacy_scale ε δ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hP
  have halpha : α ≤ max 1 (Clin * Real.sqrt 2) * α :=
    le_mul_of_one_le_left hα (le_max_left _ _)
  calc α + σ * max_row_two_norm L *
        (Real.sqrt 2 * Real.sqrt (Real.log (2 * (k : ℝ))))
      ≤ max 1 (Clin * Real.sqrt 2) * α +
          max 1 (Clin * Real.sqrt 2) *
            (max_row_two_norm L * max_column_two_norm R *
              (Real.sqrt ((n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2) *
                Real.sqrt (Real.log (2 * (k : ℝ)))) *
              all_epsilon_privacy_scale ε δ) := add_le_add halpha hstep
    _ = max 1 (Clin * Real.sqrt 2) *
          (α + max_row_two_norm L * max_column_two_norm R *
            (Real.sqrt ((n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2) *
              Real.sqrt (Real.log (2 * (k : ℝ)))) *
            all_epsilon_privacy_scale ε δ) := by ring

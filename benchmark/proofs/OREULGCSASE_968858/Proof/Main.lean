import Architect
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:robust-point"
  (statement := /-- For a dimension $d\in\mathbb N$, a point is an element of the Euclidean space
  $\mathbb R^d$, represented by coordinates indexed by $\operatorname{Fin}(d)$. -/)
  (title := /-- Euclidean points -/)
  (latexEnv := "definition")]
abbrev robust_point (d : ℕ) := EuclideanSpace ℝ (Fin d)

@[blueprint "def:robust-dataset"
  (statement := /-- For $n,d\in\mathbb N$, a dataset of cardinality $n$ in $\mathbb R^d$ is an
  indexed family $S=(x_i)_{i\in\operatorname{Fin}(n)}$. The indexing retains repetitions and
  therefore represents a finite multiset. -/)
  (title := /-- Indexed finite datasets -/)
  (latexEnv := "definition")]
abbrev robust_dataset (n d : ℕ) := Fin n → robust_point d

@[blueprint "def:empirical-mean-on"
  (statement := /-- Let $S=(x_i)_{i\in\operatorname{Fin}(n)}$ be a dataset and let
  $I\subseteq\operatorname{Fin}(n)$ be finite. Its empirical mean on $I$ is
  \[
    \mu_{S,I}=|I|^{-1}\sum_{i\in I}x_i.
  \]
  When $I$ is empty, this convention gives the zero vector. -/)
  (title := /-- Empirical mean on an index set -/)
  (latexEnv := "definition")]
noncomputable def empirical_mean_on {n d : ℕ}
    (S : robust_dataset n d) (I : Finset (Fin n)) : robust_point d :=
  (I.card : ℝ)⁻¹ • ∑ i ∈ I, S i

@[blueprint "def:empirical-covariance-on"
  (statement := /-- Let $S=(x_i)_{i\in\operatorname{Fin}(n)}$ and
  $I\subseteq\operatorname{Fin}(n)$. The centered empirical covariance matrix on $I$ is the
  $d\times d$ matrix whose $(j,k)$ entry is
  \[
    |I|^{-1}\sum_{i\in I}
    (x_i-\mu_{S,I})_j(x_i-\mu_{S,I})_k.
  \]
  The empty-index convention is again the zero matrix. -/)
  (title := /-- Centered empirical covariance -/)
  (latexEnv := "definition")]
noncomputable def empirical_covariance_on {n d : ℕ}
    (S : robust_dataset n d) (I : Finset (Fin n)) : Matrix (Fin d) (Fin d) ℝ :=
  fun j k =>
    (I.card : ℝ)⁻¹ *
      ∑ i ∈ I,
        ((S i - empirical_mean_on S I) j) * ((S i - empirical_mean_on S I) k)

@[blueprint "def:stable-dataset"
  (statement := /-- Let $0<\varepsilon<1/2$, let $\delta\geq\varepsilon$, and let
  $\mu\in\mathbb R^d$. A dataset $S$ of cardinality $n$ is
  $(\varepsilon,\delta)$-stable with respect to $\mu$ if, for every
  $I\subseteq\operatorname{Fin}(n)$ satisfying
  $|I|\geq(1-\varepsilon)n$, one has
  \[
    \|\mu_{S,I}-\mu\|_2\leq\delta
    \quad\text{and}\quad
    \|\Sigma_{S,I}-I_d\|_{\mathrm{op}}\leq\delta^2/\varepsilon.
  \]
  Here the operator norm is the Euclidean operator norm of the matrix regarded as a linear map. -/)
  (title := /-- Stability of a finite dataset -/)
  (latexEnv := "definition")]
def stable_dataset {n d : ℕ}
    (S : robust_dataset n d) (ε δ : ℝ) (μ : robust_point d) : Prop :=
  0 < ε ∧ ε < (1 / 2 : ℝ) ∧ ε ≤ δ ∧
    ∀ I : Finset (Fin n), (1 - ε) * (n : ℝ) ≤ (I.card : ℝ) →
      ‖empirical_mean_on S I - μ‖ ≤ δ ∧
        ‖(empirical_covariance_on S I - 1).toEuclideanLin.toContinuousLinearMap‖ ≤ δ ^ 2 / ε

@[blueprint "def:strong-local-corruption"
  (statement := /-- Let $S_0=(x_i)_{i=1}^n$ and $S=(\widetilde x_i)_{i=1}^n$ be datasets in
  $\mathbb R^d$. We say that $S$ is a $\rho$-strong local corruption of $S_0$ if, for every unit
  vector $v\in\mathbb R^d$,
  \[
    \frac1n\sum_{i=1}^n
      |\langle v,\widetilde x_i-x_i\rangle|\leq\rho.
  \]
  Thus the first absolute directional moment of the displacement is controlled uniformly over
  the unit sphere. -/)
  (title := /-- Strong local corruption -/)
  (latexEnv := "definition")]
def strong_local_corruption {n d : ℕ}
    (S₀ S : robust_dataset n d) (ρ : ℝ) : Prop :=
  ∀ v : robust_point d, ‖v‖ = 1 →
    (n : ℝ)⁻¹ * ∑ i : Fin n, |inner ℝ v (S i - S₀ i)| ≤ ρ

@[blueprint "def:global-corruption"
  (statement := /-- Let $S,T$ be datasets of the same cardinality $n$. We say that $T$ is an
  $\varepsilon$-global corruption of $S$ if there are a permutation $\sigma$ of
  $\operatorname{Fin}(n)$ and an index set $I\subseteq\operatorname{Fin}(n)$ with
  $|I|\geq(1-\varepsilon)n$ such that $T_{\sigma(i)}=S_i$ for every $i\in I$. Equivalently,
  the multisets represented by $S$ and $T$ overlap in at least $(1-\varepsilon)n$
  observations; thus the definition is invariant under reordering either dataset. -/)
  (title := /-- Global outlier contamination -/)
  (latexEnv := "definition")]
def global_corruption {n d : ℕ}
    (S T : robust_dataset n d) (ε : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∃ I : Finset (Fin n),
    (1 - ε) * (n : ℝ) ≤ (I.card : ℝ) ∧ ∀ i ∈ I, T (σ i) = S i

@[blueprint "def:combined-corruption"
  (statement := /-- A dataset $T$ is obtained from $S_0$ by combined
  $(\varepsilon,\rho)$-corruption if there exists an intermediate dataset $S$ which is a
  $\rho$-strong local corruption of $S_0$ and for which $T$ is an
  $\varepsilon$-global corruption of $S$. -/)
  (title := /-- Combined local and global corruption -/)
  (latexEnv := "definition")]
def combined_corruption {n d : ℕ}
    (S₀ T : robust_dataset n d) (ε ρ : ℝ) : Prop :=
  ∃ S : robust_dataset n d,
    strong_local_corruption S₀ S ρ ∧ global_corruption S T ε

@[blueprint "def:stability-estimator"
  (statement := /-- Given a randomness space $\Omega$, a stability estimator takes a dataset
  $T$, a contamination rate $\varepsilon$, a stability parameter $\delta$, and an internal
  random seed $\omega\in\Omega$, and returns a point of $\mathbb R^d$. -/)
  (title := /-- Randomized stability estimators -/)
  (latexEnv := "definition")]
abbrev stability_estimator (n d : ℕ) (Ω : Type*) :=
  robust_dataset n d → ℝ → ℝ → Ω → robust_point d

@[blueprint "def:stability-based-algorithm"
  (statement := /-- Fix an event predicate $\mathsf{HP}$ on the randomness space $\Omega$ and an
  absolute constant $K>0$. An estimator $\mathcal A$ is stability-based if it runs in polynomial
  time and has the following uniform guarantee. Let $S$ be
  $(\varepsilon,\eta)$-stable with respect to $\mu\in\mathbb R^d$, let $T_0$ be an
  $\varepsilon$-global corruption of $S$, and let $T$ be a $\rho$-strong local corruption of
  $T_0$, where $\rho\leq\eta$. Then
  \[
    \mathsf{HP}\!\left(
      \|\mathcal A(T,\varepsilon,\eta;\omega)-\mu\|_2\leq K\eta
    \right)
  \].
  Thus the single stability-based contract is uniform over the factorized form of the combined
  contamination model; no additional estimator-specific transport assumption is imposed. -/)
  (title := /-- Stability-based algorithm contract -/)
  (latexEnv := "definition")]
def stability_based_algorithm {n d : ℕ} {Ω : Type*}
    (highProbability : (Ω → Prop) → Prop) (runsInPolynomialTime : Prop)
    (A : stability_estimator n d Ω) (K : ℝ) : Prop :=
  runsInPolynomialTime ∧ 0 < K ∧
    ∀ (S T₀ T : robust_dataset n d) (μ : robust_point d) (ε η ρ : ℝ),
      stable_dataset S ε η μ →
      global_corruption S T₀ ε →
      strong_local_corruption T₀ T ρ →
      ρ ≤ η →
      highProbability (fun ω => ‖A T ε η ω - μ‖ ≤ K * η)

@[blueprint "def:strong-local-robust-algorithm"
  (statement := /-- Fix an event predicate $\mathsf{HP}$ on a randomness space $\Omega$ and
  $L\geq0$. An estimator $\mathcal A$ is strongly local robust with modulus $L$ if the following
  event-transport property holds. For every pair of datasets $X,Y$ of the same cardinality, every
  center $\mu\in\mathbb R^d$, every pair of algorithmic inputs
  $\varepsilon,\eta\in\mathbb R$, and
  every $r,\rho\in\mathbb R$, if $Y$ is a $\rho$-strong local corruption of $X$, then
  \[
    \mathsf{HP}\!\left(
      \|\mathcal A(X,\varepsilon,\eta;\omega)-\mu\|_2\leq r
    \right)
    \quad\Longrightarrow\quad
    \mathsf{HP}\!\left(
      \|\mathcal A(Y,\varepsilon,\eta;\omega)-\mu\|_2\leq r+L\rho
    \right).
  \]
  The definition uses exactly the first-moment corruption relation of
  \cref{def:strong-local-corruption}; it imposes no second-moment condition on the adversary. -/)
  (title := /-- Robustness of an estimator under strong local corruption -/)
  (latexEnv := "definition")]
def strong_local_robust_algorithm {n d : ℕ} {Ω : Type*}
    (highProbability : (Ω → Prop) → Prop) (A : stability_estimator n d Ω) (L : ℝ) : Prop :=
  0 ≤ L ∧
    ∀ (X Y : robust_dataset n d) (μ : robust_point d) (ε η r ρ : ℝ),
      strong_local_corruption X Y ρ →
      highProbability (fun ω => ‖A X ε η ω - μ‖ ≤ r) →
      highProbability (fun ω => ‖A Y ε η ω - μ‖ ≤ r + L * ρ)

@[blueprint "lem:combined-corruption-factorization"
  (statement := /-- Let $n,d\in\mathbb N$, let $S_0,T$ be indexed datasets of cardinality $n$
  in $\mathbb R^d$, and let $\varepsilon,\rho\in\mathbb R$. If $T$ is an
  $(\varepsilon,\rho)$-combined corruption of $S_0$, then there exists an indexed dataset $T_0$
  of cardinality $n$ in $\mathbb R^d$ such that $T_0$ is an $\varepsilon$-global corruption of
  $S_0$ and $T$ is a $\rho$-strong local corruption of $T_0$. -/)
  (proof := /-- By \cref{def:combined-corruption}, choose a dataset $S$, a permutation $\sigma$,
  and an index set $I$ such that $S$ is a $\rho$-strong local corruption of $S_0$,
  $|I|\geq(1-\varepsilon)n$, and $T_{\sigma(i)}=S_i$ for every $i\in I$. Define $T_0$ by
  setting $T_{0,j}=S_{0,\sigma^{-1}(j)}$ when $\sigma^{-1}(j)\in I$ and $T_{0,j}=T_j$
  otherwise. The same permutation and index set show, by \cref{def:global-corruption}, that
  $T_0$ is an $\varepsilon$-global corruption of $S_0$.

  Fix a unit vector $v$ and reindex the displacement sum from $T_0$ to $T$ by $\sigma$. If
  $i\in I$, then $T_{\sigma(i)}=S_i$ and $T_{0,\sigma(i)}=S_{0,i}$, so the summand at
  $\sigma(i)$ equals $|\langle v,S_i-S_{0,i}\rangle|$. If $i\notin I$, then
  $T_{0,\sigma(i)}=T_{\sigma(i)}$, so that summand is zero and is therefore at most
  $|\langle v,S_i-S_{0,i}\rangle|$. Summing these pointwise inequalities and multiplying by
  the nonnegative factor $n^{-1}$ gives
  \[
    \frac1n\sum_{j=1}^n |\langle v,T_j-T_{0,j}\rangle|
    \leq \frac1n\sum_{i=1}^n |\langle v,S_i-S_{0,i}\rangle|
    \leq \rho,
  \]
  where the final inequality is the local-corruption hypothesis. Since this holds for every
  unit $v$, \cref{def:strong-local-corruption} shows that $T$ is a $\rho$-strong local
  corruption of $T_0$. -/)
  (title := /-- Factorization of combined corruption -/)
  (latexEnv := "lemma")]
lemma combined_corruption_factorization {n d : ℕ}
    (S₀ T : robust_dataset n d) (ε ρ : ℝ) :
    combined_corruption S₀ T ε ρ →
      ∃ T₀ : robust_dataset n d,
        global_corruption S₀ T₀ ε ∧ strong_local_corruption T₀ T ρ := by
  rintro ⟨S, hlocal, σ, I, hcard, hagree⟩
  let T₀ : robust_dataset n d :=
    fun j => if σ.symm j ∈ I then S₀ (σ.symm j) else T j
  refine ⟨T₀, ?_, ?_⟩
  · refine ⟨σ, I, hcard, ?_⟩
    intro i hi
    simp [T₀, hi]
  · intro v hv
    calc
      (n : ℝ)⁻¹ * ∑ j : Fin n, |inner ℝ v (T j - T₀ j)| =
          (n : ℝ)⁻¹ * ∑ i : Fin n, |inner ℝ v (T (σ i) - T₀ (σ i))| := by
        apply congrArg (fun x : ℝ => (n : ℝ)⁻¹ * x)
        exact (Equiv.sum_comp σ
          (fun j => |inner ℝ v (T j - T₀ j)|)).symm
      _ ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, |inner ℝ v (S i - S₀ i)| := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        apply Finset.sum_le_sum
        intro i hiuniv
        by_cases hi : i ∈ I
        · rw [hagree i hi]
          simp [T₀, hi]
        · simp [T₀, hi]
      _ ≤ ρ := hlocal v hv

@[blueprint "lem:stability-monotone"
  (statement := /-- For every $n,d\in\mathbb N$, every indexed dataset
  $S\colon\operatorname{Fin}(n)\to\mathbb R^d$, every $\mu\in\mathbb R^d$, and all
  $\varepsilon,\delta,\delta'\in\mathbb R$, if $S$ is $(\varepsilon,\delta)$-stable with
  respect to $\mu$ and $\delta\leq\delta'$, then $S$ is $(\varepsilon,\delta')$-stable with
  respect to $\mu$. -/)
  (proof := /-- Unpack \cref{def:stable-dataset}. Its parameter conditions give
  $0<\varepsilon<1/2$ and $0\leq\varepsilon\leq\delta\leq\delta'$. For every admissible
  index set, the original mean estimate is at most $\delta$ and therefore at most $\delta'$.
  Moreover, nonnegativity and $\delta\leq\delta'$ imply $\delta^2\leq(\delta')^2$; division
  by the positive number $\varepsilon$ preserves this inequality. Thus the original covariance
  estimate is at most $(\delta')^2/\varepsilon$. These are exactly the parameter, mean, and
  covariance clauses of $(\varepsilon,\delta')$-stability. -/)
  (title := /-- Monotonicity of stability in its error parameter -/)
  (latexEnv := "lemma")]
lemma stability_monotone {n d : ℕ} (S : robust_dataset n d) (μ : robust_point d)
    (ε δ δ' : ℝ) :
    stable_dataset S ε δ μ → δ ≤ δ' → stable_dataset S ε δ' μ := by
  rintro ⟨hε, hεhalf, hεδ, hstable⟩ hδδ'
  refine ⟨hε, hεhalf, hεδ.trans hδδ', ?_⟩
  intro I hI
  rcases hstable I hI with ⟨hmean, hcov⟩
  refine ⟨hmean.trans hδδ', hcov.trans ?_⟩
  exact (div_le_div_iff_of_pos_right hε).2 (by nlinarith)

@[blueprint "lem:combined-corruption-algorithm-reduction"
  (statement := /-- Let $n,d\in\mathbb N$, let $\Omega$ be a type, and fix an event functional
  $\mathsf{HP}\colon(\Omega\to\mathsf{Prop})\to\mathsf{Prop}$, a proposition
  $\mathsf{PolyTime}$, a stability estimator $\mathcal A$, and $K\in\mathbb R$. Let $S_0,T$
  be datasets indexed by $\operatorname{Fin}(n)$ in $\mathbb R^d$, let
  $\mu\in\mathbb R^d$, and let $\varepsilon,\delta,\eta,\rho\in\mathbb R$. Suppose that
  $\mathcal A$ is stability-based relative to $\mathsf{HP}$ and $\mathsf{PolyTime}$ with
  accuracy constant $K$ in the sense of \cref{def:stability-based-algorithm}, that
  $\delta\leq\eta$ and $\rho\leq\eta$, that $S_0$ is
  $(\varepsilon,\delta)$-stable with respect to $\mu$, and that $T$ is an
  $(\varepsilon,\rho)$-combined corruption of $S_0$. Then
  \[
    \mathsf{HP}\!\left(
      \left\{\omega:
      \|\mathcal A(T,\varepsilon,\eta;\omega)-\mu\|_2
      \leq K\eta\right\}\right).
  \] -/)
  (proof := /-- By \cref{lem:combined-corruption-factorization}, there is a dataset $T_0$
  which is an $\varepsilon$-global corruption of $S_0$ and such that $T$ is a
  $\rho$-strong local corruption of $T_0$. Since $\delta\leq\eta$,
  \cref{lem:stability-monotone} shows that $S_0$ is
  $(\varepsilon,\eta)$-stable with respect to $\mu$. The stability-based algorithm contract
  applies uniformly to the factorized chain from $S_0$ through $T_0$ to $T$: the first link is
  an $\varepsilon$-global corruption, the second is a $\rho$-strong local corruption, and the
  required radius inequality is the hypothesis $\rho\leq\eta$. It therefore gives
  \[
    \mathsf{HP}\!\left(
      \|\mathcal A(T,\varepsilon,\eta;\omega)-\mu\|_2\leq K\eta
    \right).
  \] -/)
  (title := /-- Algorithmic reduction for combined corruption -/)
  (latexEnv := "lemma")]
lemma combined_corruption_algorithm_reduction {n d : ℕ} {Ω : Type*}
    (highProbability : (Ω → Prop) → Prop) (runsInPolynomialTime : Prop)
    (A : stability_estimator n d Ω) (K : ℝ)
    (S₀ T : robust_dataset n d) (μ : robust_point d) (ε δ η ρ : ℝ) :
    stability_based_algorithm highProbability runsInPolynomialTime A K →
    δ ≤ η →
    ρ ≤ η →
    stable_dataset S₀ ε δ μ →
    combined_corruption S₀ T ε ρ →
    highProbability (fun ω => ‖A T ε η ω - μ‖ ≤ K * η) := by
  rintro hA hδη hρη hstable hcombined
  obtain ⟨T₀, hglobal, hlocal⟩ :=
    combined_corruption_factorization S₀ T ε ρ hcombined
  exact hA.2.2 S₀ T₀ T μ ε η ρ
    (stability_monotone S₀ μ ε δ η hstable hδη) hglobal hlocal hρη

@[blueprint "thm:mean-estimation"
  (statement := /-- There exist absolute constants $c_0,C_0>0$ such that the following holds.
  Let $0<c\leq c_0$, $C\geq C_0$, $0<\varepsilon<c$, $\rho>0$, and
  $\delta>\varepsilon$. Let $S_0$ be $(\varepsilon,\delta)$-stable with respect to an unknown
  $\mu\in\mathbb R^d$, and let $T$ be obtained from $S_0$ by an
  $(\varepsilon,\rho)$-combined corruption. Suppose that $\mathcal A$ is a stability-based
  algorithm with absolute accuracy constant $K$. Then, when run with
  stability parameter $\widetilde\delta=C(\delta+\rho)$, it satisfies
  \[
    \mathsf{HP}\!\left(
      \left\{\omega:
      \|\mathcal A(T,\varepsilon,\widetilde\delta;\omega)-\mu\|_2
      \leq KC(\delta+\rho)\right\}\right).
  \]
  Thus the estimation error is $\lesssim\delta+\rho$ with high probability over the internal
  randomness of the algorithm. -/)
  (proof := /-- Take $c_0=1/2$ and $C_0=1$, and fix the data and parameters in the statement.
  Since $\varepsilon<\delta$ and $\rho>0$, one has $0<\delta<\delta+\rho$. The hypothesis
  $C\geq C_0=1$ consequently gives both
  \[
    \delta\leq C(\delta+\rho)
    \quad\text{and}\quad
    \rho\leq C(\delta+\rho).
  \]
  Apply \cref{lem:combined-corruption-algorithm-reduction} with
  $\eta=C(\delta+\rho)$. The two displayed inequalities verify its stability and local-radius
  bounds, while its sole algorithmic hypothesis is exactly the stability-based contract in the
  statement. It yields
  \[
    \mathsf{HP}\!\left(
      \|\mathcal A(T,\varepsilon,C(\delta+\rho);\omega)-\mu\|_2
      \leq KC(\delta+\rho)
    \right).
  \] -/)
  (title := /-- Main result for robust mean estimation -/)
  (latexEnv := "theorem")]
theorem mean_estimation :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧
      ∀ {n d : ℕ} {Ω : Type*}
        (highProbability : (Ω → Prop) → Prop) (runsInPolynomialTime : Prop)
        (A : stability_estimator n d Ω) (K : ℝ)
        (S₀ T : robust_dataset n d) (μ : robust_point d)
        (c C ε δ ρ : ℝ),
        stability_based_algorithm highProbability runsInPolynomialTime A K →
        0 < c → c ≤ c₀ → C₀ ≤ C → 0 < ε → ε < c → 0 < ρ → ε < δ →
        stable_dataset S₀ ε δ μ →
        combined_corruption S₀ T ε ρ →
        highProbability
          (fun ω =>
            ‖A T ε (C * (δ + ρ)) ω - μ‖ ≤
              K * (C * (δ + ρ))) := by
  refine ⟨1 / 2, 1, by norm_num, by norm_num, ?_⟩
  intro n d Ω highProbability runsInPolynomialTime A K S₀ T μ c C ε δ ρ
    hA hc hc₀ hC₀ hε hεc hρ hεδ hstable hcombined
  have hδpos : 0 < δ := lt_trans hε hεδ
  have hδ : δ ≤ C * (δ + ρ) := by
    have h1 : δ ≤ 1 * (δ + ρ) := by linarith
    exact h1.trans (mul_le_mul_of_nonneg_right hC₀ (by linarith))
  have hρ' : ρ ≤ C * (δ + ρ) := by
    have h1 : ρ ≤ 1 * (δ + ρ) := by linarith
    exact h1.trans (mul_le_mul_of_nonneg_right hC₀ (by linarith))
  exact combined_corruption_algorithm_reduction
    highProbability runsInPolynomialTime A K S₀ T μ ε δ (C * (δ + ρ)) ρ
    hA hδ hρ' hstable hcombined

import Architect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:mdl-concept-class"
  (statement := /-- For types $X$ and $Y$, a concept class is a set of functions from $X$ to $Y$. -/)
  (title := /-- Concept classes -/)
  (latexEnv := "definition")]
abbrev mdl_concept_class (X Y : Type*) := Set (X → Y)

@[blueprint "def:mdl-set-shatters"
  (statement := /-- A binary concept class $\mathcal F$ shatters a set $W\subseteq X$ if every subset $W'\subseteq W$ is the restriction to $W$ of the positive set of some $f\in\mathcal F$. -/)
  (title := /-- Shattering by a binary concept class -/)
  (latexEnv := "definition")]
def mdl_set_shatters {X : Type*} (C : mdl_concept_class X Bool) (W : Set X) : Prop :=
  ∀ W' ⊆ W, ∃ f ∈ C, f ⁻¹' {true} ∩ W = W'

@[blueprint "def:mdl-vc-dim"
  (statement := /-- The VC dimension of a binary concept class $\mathcal F$ is the supremum of the cardinalities of finite sets shattered by $\mathcal F$. -/)
  (title := /-- Vapnik--Chervonenkis dimension -/)
  (latexEnv := "definition")]
noncomputable def mdl_vc_dim {X : Type*} (C : mdl_concept_class X Bool) : ℕ :=
  sSup {n : ℕ | ∃ W : Finset X, W.card = n ∧ mdl_set_shatters C (↑W)}

@[blueprint "def:mdl-has-finite-vc-dim"
  (statement := /-- A binary concept class has finite VC dimension if the cardinalities of its finite shattered sets are bounded above. -/)
  (title := /-- Finiteness of VC dimension -/)
  (latexEnv := "definition")]
def mdl_has_finite_vc_dim {X : Type*} (C : mdl_concept_class X Bool) : Prop :=
  BddAbove {n : ℕ | ∃ W : Finset X, W.card = n ∧ mdl_set_shatters C (↑W)}

@[blueprint "def:mdl-sampling-tree"
  (statement := /-- Let $I$ be a set of data sources, let $S$ be the sample space, and let $O$ be the output space.  An MDL sampling tree with budget $m$ is a randomized adaptive decision tree which either returns an element of $O$, queries one source $i\in I$ and continues after observing a sample in $S$, or performs an internal randomization.  Every branch contains at most $m$ source queries; internal randomization does not consume a sample. -/)
  (title := /-- Randomized adaptive sampling trees -/)
  (latexEnv := "definition")]
inductive mdl_sampling_tree (I S O : Type*) : ℕ → Type _ where
  | output {m : ℕ} (result : O) : mdl_sampling_tree I S O m
  | query {m : ℕ} (source : I) (next : S → mdl_sampling_tree I S O m) :
      mdl_sampling_tree I S O (m + 1)
  | randomize {m : ℕ} (coin : PMF Bool) (next : Bool → mdl_sampling_tree I S O m) :
      mdl_sampling_tree I S O m

@[blueprint "def:mdl-sampling-tree-eval"
  (statement := /-- Given a probability mass function $D_i$ on $S$ for every source $i\in I$, evaluation of a sampling tree recursively draws each requested observation from the corresponding $D_i$, draws each internal random bit from the probability mass function stored at that node, and returns the induced probability mass function on $O$. -/)
  (title := /-- Evaluation of a sampling tree -/)
  (latexEnv := "definition")]
noncomputable def mdl_sampling_tree_eval {I S O : Type*} (D : I → PMF S) :
    {m : ℕ} → mdl_sampling_tree I S O m → PMF O
  | _, .output result => PMF.pure result
  | _, .query source next =>
      PMF.bind (D source) (fun sample => mdl_sampling_tree_eval D (next sample))
  | _, .randomize coin next =>
      PMF.bind coin (fun bit => mdl_sampling_tree_eval D (next bit))

@[blueprint "def:fixed-rcn-distribution"
  (statement := /-- Let $\mu$ be a probability mass function on $X$ and let $f^*:X\to\{0,1\}$.  The fixed random-classification-noise distribution associated with $(\mu,f^*)$ first draws $x\sim\mu$, independently flips a Bernoulli bit of parameter $1/4$, and returns $(x,f^*(x)\mathbin{\mathsf{xor}}b)$.  Thus, conditionally on every $x$, the observed label differs from $f^*(x)$ with probability exactly $1/4$. -/)
  (title := /-- Random classification noise at rate one quarter -/)
  (latexEnv := "definition")]
noncomputable def fixed_rcn_distribution {X : Type*} (μ : PMF X) (target : X → Bool) :
    PMF (X × Bool) :=
  PMF.bind μ (fun x =>
    PMF.map (fun noise => (x, Bool.xor (target x) noise))
      (PMF.bernoulli (1 / 4) (by
        apply (div_le_one (show (0 : NNReal) < 4 by norm_num)).2
        norm_num)))

@[blueprint "def:source-indexed-fixed-rcn-family"
  (statement := /-- Let $\mathcal F\subseteq\{0,1\}^X$ and let $D_1,\ldots,D_k$ be joint probability mass functions on $X\times\{0,1\}$.  The family $(D_i)_{i\in[k]}$ is a source-indexed fixed-RCN family for $\mathcal F$ if there are classifiers $f_i^*\in\mathcal F$ and arbitrary feature marginals $\mu_i$ such that $D_i$ is the fixed random-classification-noise distribution generated from $(\mu_i,f_i^*)$ at noise rate $1/4$ for every $i$. -/)
  (title := /-- Source-indexed families under fixed random classification noise -/)
  (latexEnv := "definition")]
def source_indexed_fixed_rcn_family {X : Type*} {k : ℕ}
    (C : mdl_concept_class X Bool) (D : Fin k → PMF (X × Bool)) : Prop :=
  ∃ targets : Fin k → X → Bool, (∀ i, targets i ∈ C) ∧
    ∃ features : Fin k → PMF X,
      ∀ i, D i = fixed_rcn_distribution (features i) (targets i)

@[blueprint "def:pmf-prediction-error"
  (statement := /-- For a joint probability mass function $D$ on $X\times\{0,1\}$ and a classifier $h:X\to\{0,1\}$, define $\operatorname{err}(h;D)$ to be the $D$-mass of the set of pairs $(x,y)$ for which $h(x)\ne y$. -/)
  (title := /-- Prediction error under a discrete distribution -/)
  (latexEnv := "definition")]
noncomputable def pmf_prediction_error {X : Type*} (D : PMF (X × Bool))
    (h : X → Bool) : ENNReal :=
  D.toOuterMeasure {z | h z.1 ≠ z.2}

@[blueprint "def:pmf-optimal-error"
  (statement := /-- For a concept class $\mathcal F\subseteq\{0,1\}^X$ and a joint probability mass function $D$, define $\operatorname{OPT}(\mathcal F;D)$ as the infimum of $\operatorname{err}(f;D)$ over all $f\in\mathcal F$. -/)
  (title := /-- Optimal error of a concept class -/)
  (latexEnv := "definition")]
noncomputable def pmf_optimal_error {X : Type*} (D : PMF (X × Bool))
    (C : mdl_concept_class X Bool) : ENNReal :=
  ⨅ f ∈ C, pmf_prediction_error D f

@[blueprint "def:personalized-mdl-objective"
  (statement := /-- Let $D_1,\ldots,D_k$ be joint distributions, let $\mathcal F$ be a concept class, and let $\widehat f_1,\ldots,\widehat f_k$ be the returned classifiers.  The personalized MDL objective at accuracy $\epsilon$ is the assertion that, for every $i\in[k]$, $\operatorname{err}(\widehat f_i;D_i)\leq \operatorname{OPT}(\mathcal F;D_i)+\epsilon$. -/)
  (title := /-- Personalized multi-distribution learning objective -/)
  (latexEnv := "definition")]
def personalized_mdl_objective {X : Type*} {k : ℕ} (C : mdl_concept_class X Bool)
    (D : Fin k → PMF (X × Bool)) (ε : ℝ) (output : Fin k → X → Bool) : Prop :=
  ∀ i, pmf_prediction_error (D i) (output i) ≤
    pmf_optimal_error (D i) C + ENNReal.ofReal ε

@[blueprint "def:mdl-algorithm"
  (statement := /-- Fix a domain $X$ and a binary concept class $\mathcal F$.  An MDL algorithm consists, for every number $k$ of distributions and parameters $(\epsilon,\delta)$, of a randomized adaptive sampling tree whose output is one classifier for each distribution.  Its depth is the advertised total sample complexity $T_{\mathcal A}(k,\epsilon,\delta)$.  The tree may depend on $(k,\mathcal F,\epsilon,\delta)$ but not on the hidden target or the hidden feature marginals. -/)
  (title := /-- Multi-distribution learning algorithms -/)
  (latexEnv := "definition")]
structure mdl_algorithm (X : Type*) (C : mdl_concept_class X Bool) where
  sampleComplexity : ℕ → ℝ → ℝ → ℕ
  run : (k : ℕ) → (ε δ : ℝ) →
    mdl_sampling_tree (Fin k) (X × Bool) (Fin k → X → Bool)
      (sampleComplexity k ε δ)

@[blueprint "def:is-mdl-algorithm"
  (statement := /-- An algorithm $\mathcal A$ for $\mathcal F$ is a valid MDL algorithm under fixed RCN noise if, for every $k\geq1$, every source-indexed fixed-RCN family $(D_i)_{i\in[k]}$ with $f_i^*\in\mathcal F$, and every $\epsilon,\delta\in(0,1)$, evaluating its tree against the sources $D_1,\ldots,D_k$ yields outputs satisfying the personalized MDL objective simultaneously for all sources with probability at least $1-\delta$. -/)
  (title := /-- Validity of an MDL algorithm under fixed RCN noise -/)
  (latexEnv := "definition")]
def is_mdl_algorithm {X : Type*} {C : mdl_concept_class X Bool}
    (A : mdl_algorithm X C) : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ (D : Fin k → PMF (X × Bool)),
    source_indexed_fixed_rcn_family C D →
    ∀ (ε δ : ℝ),
      0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ENNReal.ofReal (1 - δ) ≤
        (mdl_sampling_tree_eval D (A.run k ε δ)).toOuterMeasure
          {output | personalized_mdl_objective C D ε output}

@[blueprint "def:admissible-mdl-parameters"
  (statement := /-- The parameters $(d,k,\epsilon,\delta)$ are admissible when $k\geq1$, $0<\epsilon<1$, $0<\delta\leq0.01/3$, $d\geq384\epsilon$, and $\min\{d,1/\epsilon\}\geq4\cdot10^7$. -/)
  (title := /-- Parameter regime of the MDL lower bound -/)
  (latexEnv := "definition")]
def admissible_mdl_parameters (d k : ℕ) (ε δ : ℝ) : Prop :=
  0 < k ∧ 0 < ε ∧ ε < 1 ∧ 0 < δ ∧ δ ≤ 0.01 / 3 ∧
    384 * ε ≤ (d : ℝ) ∧ 4 * 10 ^ 7 ≤ min (d : ℝ) (1 / ε)

@[blueprint "def:mdl-lower-bound-rate"
  (statement := /-- For $d,k\in\mathbb N$ and $\epsilon>0$, define the asserted MDL lower-bound rate by
  \[
    R(d,k,\epsilon)=\frac d\epsilon
      +k\min\left\{\frac1{\epsilon^2},\frac d\epsilon\right\}.
  \] -/)
  (title := /-- The MDL lower-bound rate -/)
  (latexEnv := "definition")]
noncomputable def mdl_lower_bound_rate (d k : ℕ) (ε : ℝ) : ℝ :=
  (d : ℝ) / ε + (k : ℝ) * min (1 / ε ^ 2) ((d : ℝ) / ε)

@[blueprint "def:has-mdl-rate-lower-bound"
  (statement := /-- Let $c\in\mathbb R$, and let $\mathcal A$ be an MDL algorithm for a class of VC dimension $d$.  The algorithm has the MDL rate lower bound with constant $c$ if every admissible parameter tuple satisfies
  \[
    T_{\mathcal A}(k,\epsilon,\delta)\geq cR(d,k,\epsilon).
  \] -/)
  (title := /-- The MDL rate lower bound with a prescribed constant -/)
  (latexEnv := "definition")]
def has_mdl_rate_lower_bound {X : Type*} {C : mdl_concept_class X Bool}
    (c : ℝ) (A : mdl_algorithm X C) (d : ℕ) : Prop :=
  ∀ (k : ℕ) (ε δ : ℝ),
    admissible_mdl_parameters d k ε δ →
      c * mdl_lower_bound_rate d k ε ≤ (A.sampleComplexity k ε δ : ℝ)

@[blueprint "lem:mdl-vc-dim-shattered-finset"
  (statement := /-- Let $\mathcal F\subseteq\{0,1\}^X$ have bounded finite shattered-set cardinalities and positive VC dimension $d$.  Then some finite set $W\subseteq X$ of cardinality $d$ is shattered by $\mathcal F$. -/)
  (proof := /-- By the definitions in \cref{def:mdl-vc-dim,def:mdl-has-finite-vc-dim}, the set of cardinalities of finite sets shattered by $\mathcal F$ is bounded above and has supremum $d$.  It is nonempty because its supremum is positive.  The supremum of a nonempty bounded set of natural numbers belongs to that set, which supplies the required $W$. -/)
  (title := /-- Attainment of a finite positive VC dimension -/)
  (latexEnv := "lemma")]
lemma mdl_vc_dim_shattered_finset {X : Type*} {C : mdl_concept_class X Bool} {d : ℕ}
    (hfinite : mdl_has_finite_vc_dim C) (hdim : mdl_vc_dim C = d) (hdpos : 0 < d) :
    ∃ W : Finset X, W.card = d ∧ mdl_set_shatters C (↑W) := by
  let S : Set ℕ := {n : ℕ | ∃ W : Finset X, W.card = n ∧ mdl_set_shatters C (↑W)}
  have hnonempty : S.Nonempty := by
    by_contra h
    have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hz : mdl_vc_dim C = 0 := by
      simp [mdl_vc_dim, S, hempty]
    omega
  have hmem : d ∈ S := by
    rw [← hdim]
    exact Nat.sSup_mem hnonempty hfinite
  exact hmem

@[blueprint "lem:fixed-rcn-prediction-error"
  (statement := /-- For a feature law $\mu$, target $f$, and classifier $h$, the prediction error under fixed RCN of rate $1/4$ equals $1/4$ plus one half of the $\mu$-mass on which $h$ and $f$ disagree. -/)
  (proof := /-- Expand the fixed-RCN law and prediction error using \cref{def:fixed-rcn-distribution,def:pmf-prediction-error}.  Conditional on each feature value, the noise bit has mass $1/4$ on the label opposite the target and mass $3/4$ on the target label.  Thus agreement of $h$ with the target contributes $1/4$, disagreement contributes $3/4$, and summing over $\mu$ gives $1/4+(3/4-1/4)\mu\{h\ne f\}$. -/)
  (title := /-- Prediction error under fixed one-quarter RCN -/)
  (latexEnv := "lemma")]
lemma fixed_rcn_prediction_error {X : Type*} (μ : PMF X) (target h : X → Bool) :
    pmf_prediction_error (fixed_rcn_distribution μ target) h =
      (1 / 4 : ENNReal) + (1 / 2 : ENNReal) * μ.toOuterMeasure {x | h x ≠ target x} := by
  classical
  simp [pmf_prediction_error, fixed_rcn_distribution, PMF.toOuterMeasure_apply,
    Set.indicator_apply, PMF.bernoulli_apply]
  rw [ENNReal.tsum_prod']
  have hinner (a : X) (b : Bool) :
      (∑' a₁ : X, μ a₁ *
        ((if (a, b) = (a₁, !target a₁) then (4 : ENNReal)⁻¹ else 0) +
          if (a, b) = (a₁, target a₁) then 1 - (4 : ENNReal)⁻¹ else 0)) =
        μ a * ((if b = !target a then (4 : ENNReal)⁻¹ else 0) +
          if b = target a then 1 - (4 : ENNReal)⁻¹ else 0) := by
    rw [tsum_eq_single a]
    · simp
    · intro a' ha'
      simp [ha', Ne.symm ha']
  simp_rw [hinner]
  have hq : (1 - (4 : ENNReal)⁻¹) = (4 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
    rw [ENNReal.toReal_add (by norm_num) (by norm_num)]
    norm_num
  trans ∑' a, (μ a * (4 : ENNReal)⁻¹ +
    if h a = target a then 0 else μ a * (2 : ENNReal)⁻¹)
  · apply tsum_congr
    intro a
    cases ha : h a <;> cases hta : target a <;>
      simp [ha, hta, hq, mul_add]
  · rw [ENNReal.tsum_add]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    congr 1
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro a
    by_cases ha : h a = target a <;> simp [ha, mul_comm]

@[blueprint "lem:fixed-rcn-objective-disagreement"
  (statement := /-- Suppose a target $f\in\mathcal F$ and an output family satisfy the personalized MDL objective at accuracy $\epsilon\geq0$ for fixed one-quarter RCN laws generated from feature marginals $\mu_i$.  Then, for every source $i$, the $\mu_i$-mass on which the returned classifier disagrees with $f$ is at most $2\epsilon$. -/)
  (proof := /-- Since $f\in\mathcal F$, the optimal noisy prediction error is at most the error of $f$.  Apply \cref{lem:fixed-rcn-prediction-error} to both $f$ and the returned classifier.  The former has disagreement mass zero, while the personalized objective bounds the latter by the former plus $\epsilon$.  Cancelling the finite baseline $1/4$ and the positive factor $1/2$ gives disagreement mass at most $2\epsilon$. -/)
  (title := /-- Disagreement forced by the fixed-RCN objective -/)
  (latexEnv := "lemma")]
lemma fixed_rcn_objective_disagreement {X : Type*} {k : ℕ}
    {C : mdl_concept_class X Bool} (features : Fin k → PMF X) (target : X → Bool)
    (ε : ℝ) (output : Fin k → X → Bool) (htarget : target ∈ C) (hε : 0 ≤ ε)
    (hobj : personalized_mdl_objective C
      (fun i => fixed_rcn_distribution (features i) target) ε output) :
    ∀ i, (features i).toOuterMeasure {x | output i x ≠ target x} ≤
      ENNReal.ofReal (2 * ε) := by
  intro i
  have hopt : pmf_optimal_error (fixed_rcn_distribution (features i) target) C ≤
      pmf_prediction_error (fixed_rcn_distribution (features i) target) target := by
    unfold pmf_optimal_error
    exact iInf_le_of_le target (iInf_le_of_le htarget le_rfl)
  have hopt' : pmf_optimal_error (fixed_rcn_distribution (features i) target) C +
      ENNReal.ofReal ε ≤
      pmf_prediction_error (fixed_rcn_distribution (features i) target) target +
        ENNReal.ofReal ε := by
    simpa [add_comm] using add_le_add_right hopt (ENNReal.ofReal ε)
  have herr := (hobj i).trans hopt'
  rw [fixed_rcn_prediction_error, fixed_rcn_prediction_error] at herr
  simp only [ne_eq, not_true_eq_false, Set.setOf_false] at herr
  simp at herr
  have hhalf : (1 / 2 : ENNReal) *
      (features i).toOuterMeasure {x | output i x ≠ target x} ≤ ENNReal.ofReal ε :=
    by simpa only [one_div, ne_eq] using herr
  apply (ENNReal.mul_le_mul_iff_left (c := (1 / 2 : ENNReal)) (by norm_num) (by norm_num)).mp
  rw [mul_comm]
  calc
    (1 / 2 : ENNReal) * (features i).toOuterMeasure {x | output i x ≠ target x}
        ≤ ENNReal.ofReal ε := hhalf
    _ = ENNReal.ofReal (2 * ε) * (1 / 2 : ENNReal) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
      rw [mul_comm (2 : ENNReal) (ENNReal.ofReal ε)]
      rw [mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

@[blueprint "lem:mdl-sampling-tree-binary-testing"
  (statement := /-- Let $D_0,D_1$ be sample laws which agree outside a bad event $B$, with $D_0(B)\leq q$.  If two Boolean parameters $b_0\ne b_1$ are decoded from the output of a sampling tree of depth at most $m$, then the sum of the two decoding-error probabilities is at least $1-mq$, provided $mq\leq1$. -/)
  (proof := /-- Induct on the sampling tree from \cref{def:mdl-sampling-tree,def:mdl-sampling-tree-eval}.  At an output leaf, one of the two distinct Boolean parameters is decoded incorrectly.  Internal randomization averages the induction hypothesis with the same coin law.  At a query, discard the nonnegative contribution from $B$; on $B^c$ the two sample laws agree, so the induction hypothesis applies to the common continuation.  The surviving mass is at least $1-q$, and $(1-q)(1-mq)\geq1-(m+1)q$. -/)
  (title := /-- Binary testing lower bound for bounded-depth sampling trees -/)
  (latexEnv := "lemma")]
lemma mdl_sampling_tree_binary_testing {I S O : Type*} (D₀ D₁ : PMF S)
    (bad : Set S) (q : ENNReal) (observe : O → Bool) (b₀ b₁ : Bool)
    (hbits : b₀ ≠ b₁) (hagree : ∀ s, s ∉ bad → D₀ s = D₁ s)
    (hbad : D₀.toOuterMeasure bad ≤ q) {m : ℕ}
    (tree : mdl_sampling_tree I S O m) (hqtop : q ≠ ⊤)
    (hmq : (m : ENNReal) * q ≤ 1) :
    1 - (m : ENNReal) * q ≤
      (mdl_sampling_tree_eval (fun _ => D₀) tree).toOuterMeasure
          {o | observe o ≠ b₀} +
        (mdl_sampling_tree_eval (fun _ => D₁) tree).toOuterMeasure
          {o | observe o ≠ b₁} := by
  classical
  rw [tsub_le_iff_right]
  induction tree with
  | output result =>
      cases b₀ <;> cases b₁ <;> cases ho : observe result <;>
        simp_all [mdl_sampling_tree_eval, PMF.toOuterMeasure_pure_apply, ho]
  | @query n source next ih =>
      simp only [mdl_sampling_tree_eval, PMF.toOuterMeasure_bind_apply]
      have hnq : (n : ENNReal) * q ≤ 1 := by
        apply le_trans _ hmq
        gcongr
        norm_num
      have hpoint (s : S) :
          (if s ∈ bad then 0 else D₀ s) ≤
            D₀ s * (mdl_sampling_tree_eval (fun _ => D₀) (next s)).toOuterMeasure
                {o | observe o ≠ b₀} +
              D₁ s * (mdl_sampling_tree_eval (fun _ => D₁) (next s)).toOuterMeasure
                {o | observe o ≠ b₁} +
              D₀ s * ((n : ENNReal) * q) := by
        by_cases hs : s ∈ bad
        · simp [hs]
        · have hi := ih s hnq
          have hw := mul_le_mul_left' hi (D₀ s)
          calc
            (if s ∈ bad then 0 else D₀ s) = D₀ s := by simp [hs]
            _ ≤ D₀ s * (mdl_sampling_tree_eval (fun _ => D₀) (next s)).toOuterMeasure
                  {o | observe o ≠ b₀} +
                D₀ s * (mdl_sampling_tree_eval (fun _ => D₁) (next s)).toOuterMeasure
                  {o | observe o ≠ b₁} + D₀ s * ((n : ENNReal) * q) := by
              simpa [mul_add, mul_assoc] using hw
            _ = D₀ s * (mdl_sampling_tree_eval (fun _ => D₀) (next s)).toOuterMeasure
                  {o | observe o ≠ b₀} +
                D₁ s * (mdl_sampling_tree_eval (fun _ => D₁) (next s)).toOuterMeasure
                  {o | observe o ≠ b₁} + D₀ s * ((n : ENNReal) * q) := by
              rw [← hagree s hs]
      have hgood :
          (∑' s : S, if s ∈ bad then 0 else D₀ s) ≤
            (∑' s : S, D₀ s *
              (mdl_sampling_tree_eval (fun _ => D₀) (next s)).toOuterMeasure
                {o | observe o ≠ b₀}) +
            (∑' s : S, D₁ s *
              (mdl_sampling_tree_eval (fun _ => D₁) (next s)).toOuterMeasure
                {o | observe o ≠ b₁}) + (n : ENNReal) * q := by
        calc
          (∑' s : S, if s ∈ bad then 0 else D₀ s) ≤
              ∑' s : S,
                (D₀ s * (mdl_sampling_tree_eval (fun _ => D₀) (next s)).toOuterMeasure
                    {o | observe o ≠ b₀} +
                  D₁ s * (mdl_sampling_tree_eval (fun _ => D₁) (next s)).toOuterMeasure
                    {o | observe o ≠ b₁} + D₀ s * ((n : ENNReal) * q)) :=
            ENNReal.tsum_le_tsum hpoint
          _ = _ := by
            rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
              PMF.tsum_coe, one_mul]
      have hsplit :
          (∑' s : S, if s ∈ bad then 0 else D₀ s) + D₀.toOuterMeasure bad = 1 := by
        rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_add, ← PMF.tsum_coe D₀]
        apply tsum_congr
        intro s
        simp only [Set.indicator_apply]
        by_cases hs : s ∈ bad <;> simp [hs]
      calc
        1 = (∑' s : S, if s ∈ bad then 0 else D₀ s) +
            D₀.toOuterMeasure bad := hsplit.symm
        _ ≤ ((∑' s : S, D₀ s *
                (mdl_sampling_tree_eval (fun _ => D₀) (next s)).toOuterMeasure
                  {o | observe o ≠ b₀}) +
              (∑' s : S, D₁ s *
                (mdl_sampling_tree_eval (fun _ => D₁) (next s)).toOuterMeasure
                  {o | observe o ≠ b₁}) + (n : ENNReal) * q) + q :=
            add_le_add hgood hbad
        _ = (∑' s : S, D₀ s *
                (mdl_sampling_tree_eval (fun _ => D₀) (next s)).toOuterMeasure
                  {o | observe o ≠ b₀}) +
              (∑' s : S, D₁ s *
                (mdl_sampling_tree_eval (fun _ => D₁) (next s)).toOuterMeasure
                  {o | observe o ≠ b₁}) + ((n + 1 : ℕ) : ENNReal) * q := by
            norm_num [Nat.cast_add]
            rw [add_mul, one_mul]
            ac_rfl
  | @randomize n coin next ih =>
      simp only [mdl_sampling_tree_eval, PMF.toOuterMeasure_bind_apply]
      have hcoin : coin true + coin false = 1 := by
        simpa only [tsum_bool, add_comm] using PMF.tsum_coe coin
      have hweighted :
          coin true * 1 + coin false * 1 ≤
            coin true *
                ((mdl_sampling_tree_eval (fun _ => D₀) (next true)).toOuterMeasure
                    {o | observe o ≠ b₀} +
                  (mdl_sampling_tree_eval (fun _ => D₁) (next true)).toOuterMeasure
                    {o | observe o ≠ b₁} + (n : ENNReal) * q) +
              coin false *
                ((mdl_sampling_tree_eval (fun _ => D₀) (next false)).toOuterMeasure
                    {o | observe o ≠ b₀} +
                  (mdl_sampling_tree_eval (fun _ => D₁) (next false)).toOuterMeasure
                    {o | observe o ≠ b₁} + (n : ENNReal) * q) :=
        add_le_add (mul_le_mul_left' (ih true hmq) (coin true))
          (mul_le_mul_left' (ih false hmq) (coin false))
      calc
        1 = coin true * 1 + coin false * 1 := by rw [mul_one, mul_one, hcoin]
        _ ≤ coin true *
                ((mdl_sampling_tree_eval (fun _ => D₀) (next true)).toOuterMeasure
                    {o | observe o ≠ b₀} +
                  (mdl_sampling_tree_eval (fun _ => D₁) (next true)).toOuterMeasure
                    {o | observe o ≠ b₁} + (n : ENNReal) * q) +
              coin false *
                ((mdl_sampling_tree_eval (fun _ => D₀) (next false)).toOuterMeasure
                    {o | observe o ≠ b₀} +
                  (mdl_sampling_tree_eval (fun _ => D₁) (next false)).toOuterMeasure
                    {o | observe o ≠ b₁} + (n : ENNReal) * q) := hweighted
        _ = coin true *
                (mdl_sampling_tree_eval (fun _ => D₀) (next true)).toOuterMeasure
                  {o | observe o ≠ b₀} +
              coin false *
                (mdl_sampling_tree_eval (fun _ => D₀) (next false)).toOuterMeasure
                  {o | observe o ≠ b₀} +
              (coin true *
                  (mdl_sampling_tree_eval (fun _ => D₁) (next true)).toOuterMeasure
                    {o | observe o ≠ b₁} +
                coin false *
                  (mdl_sampling_tree_eval (fun _ => D₁) (next false)).toOuterMeasure
                    {o | observe o ≠ b₁}) +
              (coin true + coin false) * ((n : ENNReal) * q) := by
            simp only [mul_add]
            rw [add_mul]
            ac_rfl
        _ = (∑' a : Bool, coin a *
                (mdl_sampling_tree_eval (fun _ => D₀) (next a)).toOuterMeasure
                  {o | observe o ≠ b₀}) +
              (∑' a : Bool, coin a *
                (mdl_sampling_tree_eval (fun _ => D₁) (next a)).toOuterMeasure
                  {o | observe o ≠ b₁}) + (n : ENNReal) * q := by
            rw [hcoin, one_mul]
            simp only [tsum_bool]
            ac_rfl

@[blueprint "lem:mdl-sampling-tree-uniform-bit-error"
  (statement := /-- Fix a coordinate $j$ of a uniformly varying Boolean parameter $\theta\in\{0,1\}^d$.  Suppose that flipping $\theta_j$ changes the sample law only on an event of mass at most $q$.  For any depth-$m$ sampling tree, the sum over all parameters of the probability of decoding $\theta_j$ incorrectly is at least $2^{d-1}(1-mq)$, provided $mq\leq1$. -/)
  (proof := /-- Pair every parameter $\theta$ with the parameter obtained by flipping its $j$th bit.  Apply \cref{lem:mdl-sampling-tree-binary-testing} to each pair.  Summing the resulting inequalities over all $\theta$, the flip is an involutive permutation, so the two error sums coincide.  This gives twice the total error on the right and $2^d(1-mq)$ on the left. -/)
  (title := /-- Average error for a uniformly varying hidden bit -/)
  (latexEnv := "lemma")]
lemma mdl_sampling_tree_uniform_bit_error {I S O : Type*} {d : ℕ}
    (D : (Fin d → Bool) → PMF S) (bad : Set S) (q : ENNReal)
    (observe : O → Bool) (j : Fin d)
    (hagree : ∀ θ s, s ∉ bad →
      D θ s = D (Function.update θ j (!θ j)) s)
    (hbad : ∀ θ, (D θ).toOuterMeasure bad ≤ q) {m : ℕ}
    (tree : mdl_sampling_tree I S O m) (hqtop : q ≠ ⊤)
    (hmq : (m : ENNReal) * q ≤ 1) :
    (Fintype.card (Fin d → Bool) : ENNReal) * (1 - (m : ENNReal) * q) ≤
      2 * ∑ θ : Fin d → Bool,
        (mdl_sampling_tree_eval (fun _ => D θ) tree).toOuterMeasure
          {o | observe o ≠ θ j} := by
  classical
  let flip : (Fin d → Bool) → (Fin d → Bool) :=
    fun θ => Function.update θ j (!θ j)
  have hflip_apply (θ : Fin d → Bool) : flip θ j = !θ j := by
    simp [flip]
  have hflip_involutive : Function.Involutive flip := by
    intro θ
    funext i
    by_cases hi : i = j
    · subst i
      simp [flip]
    · simp [flip, hi]
  let flipEquiv : (Fin d → Bool) ≃ (Fin d → Bool) :=
    ⟨flip, flip, hflip_involutive, hflip_involutive⟩
  let err : (Fin d → Bool) → ENNReal := fun θ =>
    (mdl_sampling_tree_eval (fun _ => D θ) tree).toOuterMeasure
      {o | observe o ≠ θ j}
  have hpair (θ : Fin d → Bool) :
      1 - (m : ENNReal) * q ≤ err θ + err (flip θ) := by
    have hb : θ j ≠ flip θ j := by
      rw [hflip_apply]
      cases θ j <;> simp
    simpa [err, flip] using
      mdl_sampling_tree_binary_testing (D θ) (D (flip θ)) bad q observe
        (θ j) (flip θ j) hb (hagree θ) (hbad θ) tree hqtop hmq
  have hsum := Finset.sum_le_sum (fun θ (_ : θ ∈ (Finset.univ : Finset (Fin d → Bool))) =>
    hpair θ)
  have hflip_sum : ∑ θ : Fin d → Bool, err (flip θ) = ∑ θ : Fin d → Bool, err θ := by
    exact flipEquiv.sum_comp err
  simpa [Finset.sum_const, Finset.sum_add_distrib, hflip_sum, nsmul_eq_mul,
    two_mul, mul_comm] using hsum

@[blueprint "lem:fixed-rcn-feature-event"
  (statement := /-- Under a fixed-RCN joint law generated from a feature marginal $\mu$, the probability that the feature belongs to a set $E$ is exactly $\mu(E)$. -/)
  (proof := /-- Expand the bind and map in \cref{def:fixed-rcn-distribution}.  For each feature value $x$, both possible noisy labels have first coordinate $x$, so the conditional probability of the event is one when $x\in E$ and zero otherwise.  Summing over $\mu$ gives $\mu(E)$. -/)
  (title := /-- Feature marginal of a fixed-RCN law -/)
  (latexEnv := "lemma")]
lemma fixed_rcn_feature_event {X : Type*} (μ : PMF X) (target : X → Bool)
    (E : Set X) :
    (fixed_rcn_distribution μ target).toOuterMeasure {z | z.1 ∈ E} =
      μ.toOuterMeasure E := by
  classical
  rw [fixed_rcn_distribution, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ E <;> simp [ha, PMF.toOuterMeasure_map_apply]
  rw [add_comm, ← tsum_bool, PMF.tsum_coe, mul_one]

@[blueprint "lem:pmf-weighted-loss-high-probability-bound"
  (statement := /-- Let $P$ be a probability mass function, let $G$ have probability at least $1-\delta$, and let a nonnegative loss be at most $a$ on $G$ and at most $b$ everywhere.  Then its $P$-weighted sum is at most $a+\delta b$. -/)
  (proof := /-- Split the weighted sum over $G$ and $G^c$.  The first part is at most $aP(G)\leq a$.  Since $P(G)\geq1-\delta$ and $P(G)+P(G^c)=1$, cancellation gives $P(G^c)\leq\delta$, so the second part is at most $b\delta$.  Adding the two estimates proves the claim. -/)
  (title := /-- Expected loss from a high-probability bound -/)
  (latexEnv := "lemma")]
lemma pmf_weighted_loss_high_probability_bound {O : Type*} (P : PMF O)
    (good : Set O) (loss : O → ENNReal) (a b δ : ENNReal)
    (hprob : 1 - δ ≤ P.toOuterMeasure good)
    (hgood : ∀ o ∈ good, loss o ≤ a) (hall : ∀ o, loss o ≤ b) :
    (∑' o, P o * loss o) ≤ a + δ * b := by
  classical
  have hsplit : P.toOuterMeasure good + P.toOuterMeasure goodᶜ = 1 := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
      ← ENNReal.tsum_add, ← PMF.tsum_coe P]
    apply tsum_congr
    intro o
    simp only [Set.indicator_apply, Set.mem_compl_iff]
    by_cases ho : o ∈ good <;> simp [ho]
  have hgood_le : P.toOuterMeasure good ≤ 1 := by
    rw [← hsplit]
    exact le_add_right le_rfl
  have hgood_top : P.toOuterMeasure good ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by norm_num) hgood_le
  have hcomp : P.toOuterMeasure goodᶜ ≤ δ := by
    have hpadd : 1 ≤ P.toOuterMeasure good + δ :=
      tsub_le_iff_right.mp hprob
    apply (ENNReal.add_le_add_iff_left hgood_top).mp
    calc
      P.toOuterMeasure good + P.toOuterMeasure goodᶜ = 1 := hsplit
      _ ≤ P.toOuterMeasure good + δ := hpadd
  calc
    (∑' o, P o * loss o) =
        (∑' o, if o ∈ good then P o * loss o else 0) +
          (∑' o, if o ∈ good then 0 else P o * loss o) := by
      rw [← ENNReal.tsum_add]
      apply tsum_congr
      intro o
      by_cases ho : o ∈ good <;> simp [ho]
    _ ≤ (∑' o, if o ∈ good then P o * a else 0) +
          (∑' o, if o ∈ good then 0 else P o * b) := by
      apply add_le_add <;> apply ENNReal.tsum_le_tsum <;> intro o
      · by_cases ho : o ∈ good
        · simpa [ho] using mul_le_mul_left' (hgood o ho) (P o)
        · simp [ho]
      · by_cases ho : o ∈ good
        · simp [ho]
        · simpa [ho] using mul_le_mul_left' (hall o) (P o)
    _ = P.toOuterMeasure good * a + P.toOuterMeasure goodᶜ * b := by
      rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
      congr 1
      · rw [← ENNReal.tsum_mul_right]
        apply tsum_congr
        intro o
        simp only [Set.indicator_apply]
        by_cases ho : o ∈ good <;> simp [ho]
      · rw [← ENNReal.tsum_mul_right]
        apply tsum_congr
        intro o
        simp only [Set.indicator_apply, Set.mem_compl_iff]
        by_cases ho : o ∈ good <;> simp [ho]
    _ ≤ 1 * a + δ * b := by
      exact add_le_add (mul_le_mul_right' hgood_le a)
        (mul_le_mul_right' hcomp b)
    _ = a + δ * b := by rw [one_mul]

@[blueprint "lem:mdl-pac-component-lower-bound"
  (statement := /-- There is an absolute numerical constant $c_{\mathrm{PAC}}>0$ such that the following holds.  Let $X$ be a domain, let $\mathcal F\subseteq\{0,1\}^X$ have finite VC dimension $d\in\mathbb N$, and let $\mathcal A$ be a valid MDL algorithm for $\mathcal F$ under fixed RCN noise of rate $1/4$.  For every $k\in\mathbb N$ and $\epsilon,\delta\in\mathbb R$ satisfying $k>0$, $0<\epsilon<1$, $0<\delta\leq0.01/3$, $384\epsilon\leq d$, and $4\cdot10^7\leq\min\{d,1/\epsilon\}$,
  \[
    T_{\mathcal A}(k,\epsilon,\delta)\geq
    c_{\mathrm{PAC}}\frac d\epsilon.
  \] -/)
  (proof := /-- Set $c_{\mathrm{PAC}}=1/4096$, and fix all the quantified data.  Unpack the inequalities in \cref{def:admissible-mdl-parameters}.  By \cref{lem:mdl-vc-dim-shattered-finset}, there is a shattered finite set $W$ of cardinality $d$.  Enumerate $W$ by $\operatorname{Fin}(d)$, and for every Boolean vector $\theta$ choose, by shattering, a target $f_\theta\in\mathcal F$ whose values on the enumeration are the coordinates of $\theta$.

  Fix one coordinate $j_0$.  Define a feature law by choosing, with probability $16\epsilon$, a uniform coordinate of $W$, and otherwise choosing $j_0$.  Thus every coordinate $j\ne j_0$ has mass $q=16\epsilon/d$.  Flipping $\theta_j$ changes the fixed-RCN law of \cref{def:fixed-rcn-distribution} only when the sampled feature is the point indexed by $j$; by \cref{lem:fixed-rcn-feature-event}, that exceptional event has probability $q$.  Suppose for contradiction that the tree depth $m=T_{\mathcal A}(k,\epsilon,\delta)$ is smaller than $d/(4096\epsilon)$.  Then $mq<1/256$.  Apply \cref{lem:mdl-sampling-tree-uniform-bit-error} to the tree in \cref{def:mdl-sampling-tree-eval} and sum over the $r=d-1$ coordinates distinct from $j_0$.  Writing $N=2^d$ and $e_{\theta,j}$ for the probability that the output misclassifies the point indexed by $j$, this gives
  \[
    rN(1-mq)\leq 2\sum_{j\ne j_0}\sum_\theta e_{\theta,j}.
  \]

  For an output $h$, let $L_\theta(h)$ be its feature-law mass of errors on those $r$ coordinates.  The validity condition in \cref{def:is-mdl-algorithm} and the objective in \cref{def:personalized-mdl-objective} hold with probability at least $1-\delta$.  On that event, \cref{lem:fixed-rcn-objective-disagreement} gives $L_\theta(h)\leq2\epsilon$, while the coarser uniform bound $L_\theta(h)\leq dq=16\epsilon$ holds for every output.  Hence \cref{lem:pmf-weighted-loss-high-probability-bound} yields
  \[
    \mathbb E L_\theta\leq2\epsilon+\delta dq.
  \]
  Expanding the finite feature law shows $\mathbb E L_\theta=q\sum_{j\ne j_0}e_{\theta,j}$.  Sum this identity over $\theta$, interchange the two finite sums, multiply the testing inequality by $q$, and cancel $N>0$ to obtain
  \[
    rq(1-mq)\leq2(2\epsilon+\delta dq).
  \]
  The admissibility bounds imply $15\epsilon\leq rq\leq16\epsilon$, $dq=16\epsilon$, and $\delta\leq1/300$.  Together with $mq<1/256$ and $\epsilon>0$, the last display is impossible.  Therefore $m\geq d/(4096\epsilon)$, which is the required bound. -/)
  (title := /-- The ordinary PAC contribution -/)
  (latexEnv := "lemma")]
lemma mdl_pac_component_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ {X : Type*} {C : mdl_concept_class X Bool} (d : ℕ),
        mdl_has_finite_vc_dim C → mdl_vc_dim C = d →
          ∀ (A : mdl_algorithm X C), is_mdl_algorithm A →
            ∀ (k : ℕ) (ε δ : ℝ), admissible_mdl_parameters d k ε δ →
              c * ((d : ℝ) / ε) ≤ (A.sampleComplexity k ε δ : ℝ) := by
  refine ⟨(1 : ℝ) / 4096, by norm_num, ?_⟩
  intro X C d hfinite hdim A hA k ε δ hadm
  rcases hadm with ⟨hk, hε, hε_one, hδ, hδ_max, hdε, hlarge⟩
  classical
  have hdlarge : (4 * 10 ^ 7 : ℝ) ≤ d := (le_min_iff.mp hlarge).1
  have hdpos : 0 < d := by
    exact_mod_cast (show (0 : ℝ) < d by nlinarith)
  rcases mdl_vc_dim_shattered_finset hfinite hdim hdpos with ⟨W, hWcard, hW⟩
  let eW : (↥W) ≃ Fin d := Finset.equivFinOfCardEq hWcard
  let point : Fin d → X := fun j => (eW.symm j : X)
  have hpoint_mem (j : Fin d) : point j ∈ W := (eW.symm j).property
  have hpoint_injective : Function.Injective point := by
    intro i j hij
    apply eW.symm.injective
    apply Subtype.ext
    simpa [point] using hij
  let j₀ : Fin d := ⟨0, hdpos⟩
  letI : Nonempty (Fin d) := ⟨j₀⟩
  have hlarge_eps : (4 * 10 ^ 7 : ℝ) ≤ 1 / ε := (le_min_iff.mp hlarge).2
  have hscaled_eps : (4 * 10 ^ 7 : ℝ) * ε ≤ 1 := by
    apply (le_div_iff₀ hε).mp
    simpa [div_eq_mul_inv] using hlarge_eps
  let α : NNReal := ⟨16 * ε, by positivity⟩
  have hα : α ≤ 1 := by
    change 16 * ε ≤ 1
    nlinarith [hscaled_eps]
  let coin : PMF Bool := PMF.bernoulli α hα
  let uniform : PMF (Fin d) := PMF.ofFintype
    (fun _ => (d : ENNReal)⁻¹) (by
      simp [Finset.sum_const, nsmul_eq_mul, ENNReal.mul_inv_cancel,
        Nat.ne_of_gt hdpos])
  let ν : PMF (Fin d) := PMF.bind coin (fun b =>
    if b then uniform else PMF.pure j₀)
  let μ : PMF X := PMF.map point ν
  let q : ENNReal := (α : ENNReal) * (d : ENNReal)⁻¹
  have hν (j : Fin d) (hj : j ≠ j₀) : ν j = q := by
    simp [ν, coin, uniform, q, PMF.bind_apply, PMF.bernoulli_apply,
      PMF.ofFintype_apply, PMF.pure_apply, tsum_bool, hj]
  let V (θ : Fin d → Bool) : Set X := point '' {j | θ j = true}
  have hVsub (θ : Fin d → Bool) : V θ ⊆ (↑W : Set X) := by
    rintro x ⟨j, -, rfl⟩
    exact hpoint_mem j
  have htarget_exists (θ : Fin d → Bool) :
      ∃ f ∈ C, f ⁻¹' {true} ∩ (↑W : Set X) = V θ :=
    hW (V θ) (hVsub θ)
  let target (θ : Fin d → Bool) : X → Bool :=
    Classical.choose (htarget_exists θ)
  have htarget_mem (θ : Fin d → Bool) : target θ ∈ C :=
    (Classical.choose_spec (htarget_exists θ)).1
  have htarget_set (θ : Fin d → Bool) :
      target θ ⁻¹' {true} ∩ (↑W : Set X) = V θ :=
    (Classical.choose_spec (htarget_exists θ)).2
  have htarget_point (θ : Fin d → Bool) (j : Fin d) :
      target θ (point j) = θ j := by
    have htrue : target θ (point j) = true ↔ θ j = true := by
      constructor
      · intro ht
        have hp : point j ∈ target θ ⁻¹' {true} ∩ (↑W : Set X) := by
          exact ⟨by simpa using ht, hpoint_mem j⟩
        rw [htarget_set θ] at hp
        rcases hp with ⟨i, hi, hij⟩
        have : i = j := hpoint_injective hij
        simpa [this] using hi
      · intro hj
        have hp : point j ∈ V θ := ⟨j, hj, rfl⟩
        rw [← htarget_set θ] at hp
        simpa using hp.1
    cases ht : target θ (point j) <;> cases hb : θ j <;> simp_all
  let D (θ : Fin d → Bool) : PMF (X × Bool) :=
    fixed_rcn_distribution μ (target θ)
  have hμ_zero (x : X) (hx : x ∉ Set.range point) : μ x = 0 := by
    have hj (j : Fin d) : x ≠ point j := by
      intro h
      exact hx ⟨j, h.symm⟩
    simp [μ, PMF.map_apply, hj]
  have hfixed_eq (f g : X → Bool) (z : X × Bool)
      (hfg : μ z.1 = 0 ∨ f z.1 = g z.1) :
      fixed_rcn_distribution μ f z = fixed_rcn_distribution μ g z := by
    unfold fixed_rcn_distribution
    simp only [PMF.bind_apply]
    apply tsum_congr
    intro x
    by_cases hx : x = z.1
    · subst x
      rcases hfg with hz | hz
      · simp [hz]
      · rw [hz]
    · have hzpair (b : Bool) : z ≠ (x, b) := by
        intro h
        exact hx (congrArg Prod.fst h).symm
      simp [PMF.map_apply, hzpair]
  have hD_agree (j : Fin d) (θ : Fin d → Bool) (z : X × Bool)
      (hz : z ∉ {z | z.1 = point j}) :
      D θ z = D (Function.update θ j (!θ j)) z := by
    apply hfixed_eq
    by_cases hrange : z.1 ∈ Set.range point
    · rcases hrange with ⟨i, hi⟩
      right
      have hij : i ≠ j := by
        intro hij
        subst i
        exact hz (by simpa using hi.symm)
      rw [← hi, htarget_point, htarget_point]
      simp [Function.update, hij]
    · exact Or.inl (hμ_zero z.1 hrange)
  have hμ_point (j : Fin d) (hj : j ≠ j₀) :
      μ.toOuterMeasure {x | x = point j} = q := by
    simp only [μ, PMF.toOuterMeasure_map_apply]
    have hpre : point ⁻¹' {x | x = point j} = ({j} : Set (Fin d)) := by
      ext i
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact hpoint_injective.eq_iff
    rw [hpre, PMF.toOuterMeasure_apply_singleton, hν j hj]
  have hD_bad (j : Fin d) (hj : j ≠ j₀) (θ : Fin d → Bool) :
      (D θ).toOuterMeasure {z | z.1 = point j} = q := by
    calc
      (D θ).toOuterMeasure {z | z.1 = point j} =
          μ.toOuterMeasure {x | x = point j} := by
            exact fixed_rcn_feature_event μ (target θ) {x | x = point j}
      _ = q := hμ_point j hj
  have hqtop : q ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · simp
    · simp [hdpos.ne']
  have hqreal : q.toReal = 16 * ε / d := by
    simp only [q, ENNReal.toReal_mul, ENNReal.toReal_inv]
    change (16 * ε) * (d : ℝ)⁻¹ = 16 * ε / d
    rw [div_eq_mul_inv]
  let m := A.sampleComplexity k ε δ
  change (1 / 4096 : ℝ) * (d / ε) ≤ (m : ℝ)
  by_contra hbound
  have hmreal : (m : ℝ) < d / (4096 * ε) := by
    rw [not_le] at hbound
    calc
      (m : ℝ) < (1 / 4096 : ℝ) * (d / ε) := hbound
      _ = d / (4096 * ε) := by field_simp
  have hmprod : (m : ℝ) * (4096 * ε) < d :=
    (lt_div_iff₀ (by positivity)).mp hmreal
  have hmq : (m : ENNReal) * q ≤ 1 := by
    apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by simp) hqtop) (by simp)).mp
    rw [ENNReal.toReal_mul, hqreal]
    simp only [ENNReal.toReal_natCast, ENNReal.toReal_one]
    have hεd : 0 < (d : ℝ) := by positivity
    calc
      (m : ℝ) * (16 * ε / d) = (16 * m * ε) / d := by ring
      _ ≤ 1 := (div_le_one hεd).2 (by nlinarith [hmprod])
  let i₀ : Fin k := ⟨0, hk⟩
  let sources (θ : Fin d → Bool) : Fin k → PMF (X × Bool) := fun _ => D θ
  have hsources (θ : Fin d → Bool) :
      source_indexed_fixed_rcn_family C (sources θ) := by
    refine ⟨fun _ => target θ, ?_, fun _ => μ, ?_⟩
    · intro i
      exact htarget_mem θ
    · intro i
      rfl
  have hδ_one : δ < 1 := by nlinarith [hδ_max]
  let P (θ : Fin d → Bool) : PMF (Fin k → X → Bool) :=
    mdl_sampling_tree_eval (sources θ) (A.run k ε δ)
  let good (θ : Fin d → Bool) : Set (Fin k → X → Bool) :=
    {o | personalized_mdl_objective C (sources θ) ε o}
  have hvalid (θ : Fin d → Bool) :
      ENNReal.ofReal (1 - δ) ≤ (P θ).toOuterMeasure (good θ) := by
    exact hA k hk (sources θ) (hsources θ) ε δ hε hε_one hδ hδ_one
  have hbit (j : Fin d) (hj : j ≠ j₀) :
      (Fintype.card (Fin d → Bool) : ENNReal) * (1 - (m : ENNReal) * q) ≤
        2 * ∑ θ : Fin d → Bool,
          (P θ).toOuterMeasure {o | o i₀ (point j) ≠ θ j} := by
    simpa [P, sources, m] using
      mdl_sampling_tree_uniform_bit_error D {z | z.1 = point j} q
        (fun o => o i₀ (point j)) j (hD_agree j)
        (fun θ => (hD_bad j hj θ).le) (A.run k ε δ) hqtop hmq
  let J : Finset (Fin d) := Finset.univ.erase j₀
  let loss (θ : Fin d → Bool) (o : Fin k → X → Bool) : ENNReal :=
    ∑ j ∈ J, if o i₀ (point j) ≠ θ j then ν j else 0
  have hloss_disagree (θ : Fin d → Bool) (o : Fin k → X → Bool) :
      loss θ o ≤ μ.toOuterMeasure {x | o i₀ x ≠ target θ x} := by
    simp only [μ, PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_apply_fintype, loss]
    calc
      (∑ j ∈ J, if o i₀ (point j) ≠ θ j then ν j else 0) ≤
          ∑ j : Fin d, if o i₀ (point j) ≠ θ j then ν j else 0 := by
            apply Finset.sum_le_sum_of_subset
            simp [J]
      _ = ∑ j : Fin d,
          (point ⁻¹' {x | o i₀ x ≠ target θ x}).indicator ν j := by
            apply Finset.sum_congr rfl
            intro j hj
            simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_setOf_eq]
            rw [htarget_point]
  have hloss_good (θ : Fin d → Bool) (o : Fin k → X → Bool)
      (ho : o ∈ good θ) : loss θ o ≤ ENNReal.ofReal (2 * ε) := by
    apply (hloss_disagree θ o).trans
    have hobj : personalized_mdl_objective C
        (fun _ : Fin k => fixed_rcn_distribution μ (target θ)) ε o := by
      simpa [good, sources, D] using ho
    exact fixed_rcn_objective_disagreement (fun _ : Fin k => μ) (target θ)
      ε o (htarget_mem θ) hε.le hobj i₀
  have hloss_all (θ : Fin d → Bool) (o : Fin k → X → Bool) :
      loss θ o ≤ (d : ENNReal) * q := by
    calc
      loss θ o ≤ ∑ j ∈ J, q := by
        apply Finset.sum_le_sum
        intro j hj
        have hj₀ : j ≠ j₀ := Finset.ne_of_mem_erase hj
        by_cases he : o i₀ (point j) ≠ θ j
        · simp [loss, he, hν j hj₀]
        · simp [loss, he]
      _ ≤ ∑ j : Fin d, q := by
        apply Finset.sum_le_sum_of_subset
        simp [J]
      _ = (d : ENNReal) * q := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hweighted (θ : Fin d → Bool) :
      (∑' o, P θ o * loss θ o) ≤
        ENNReal.ofReal (2 * ε) + ENNReal.ofReal δ * ((d : ENNReal) * q) := by
    have hprob : 1 - ENNReal.ofReal δ ≤ (P θ).toOuterMeasure (good θ) := by
      have heq : (1 : ENNReal) - ENNReal.ofReal δ = ENNReal.ofReal (1 - δ) := by
        rw [ENNReal.ofReal_sub 1 hδ.le]
        simp
      rw [heq]
      exact hvalid θ
    exact pmf_weighted_loss_high_probability_bound (P θ) (good θ) (loss θ)
      (ENNReal.ofReal (2 * ε)) ((d : ENNReal) * q) (ENNReal.ofReal δ)
      hprob (hloss_good θ) (hloss_all θ)
  let err (θ : Fin d → Bool) (j : Fin d) : ENNReal :=
    (P θ).toOuterMeasure {o | o i₀ (point j) ≠ θ j}
  have hterm (θ : Fin d → Bool) (j : Fin d) (hj : j ∈ J) :
      (∑' o, P θ o * (if o i₀ (point j) ≠ θ j then ν j else 0)) =
        q * err θ j := by
    have hj₀ : j ≠ j₀ := Finset.ne_of_mem_erase hj
    simp only [err]
    rw [← hν j hj₀, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro o
    by_cases he : o i₀ (point j) ≠ θ j <;>
      simp [Set.indicator_apply, he, mul_comm]
  have htsum_sum (θ : Fin d → Bool) (s : Finset (Fin d)) :
      (∑' o, P θ o * ∑ j ∈ s,
          if o i₀ (point j) ≠ θ j then ν j else 0) =
        ∑ j ∈ s, ∑' o, P θ o *
          (if o i₀ (point j) ≠ θ j then ν j else 0) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
        simp only [Finset.mem_insert, Finset.sum_insert hj]
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ih]
  have hexpect (θ : Fin d → Bool) :
      (∑' o, P θ o * loss θ o) = ∑ j ∈ J, q * err θ j := by
    simp only [loss]
    rw [htsum_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact hterm θ j hj
  let N : ENNReal := Fintype.card (Fin d → Bool)
  let B : ENNReal :=
    ENNReal.ofReal (2 * ε) + ENNReal.ofReal δ * ((d : ENNReal) * q)
  have hθbound (θ : Fin d → Bool) : ∑ j ∈ J, q * err θ j ≤ B := by
    rw [← hexpect θ]
    exact hweighted θ
  have hupper :
      (∑ θ : Fin d → Bool, ∑ j ∈ J, q * err θ j) ≤ N * B := by
    have h := Finset.sum_le_sum (fun θ (_ : θ ∈
        (Finset.univ : Finset (Fin d → Bool))) => hθbound θ)
    simpa [N, Finset.sum_const, nsmul_eq_mul] using h
  have hlower :
      (∑ j ∈ J, N * (1 - (m : ENNReal) * q)) ≤
        ∑ j ∈ J, 2 * ∑ θ : Fin d → Bool, err θ j := by
    apply Finset.sum_le_sum
    intro j hj
    have hj₀ : j ≠ j₀ := Finset.ne_of_mem_erase hj
    simpa [N, err] using hbit j hj₀
  have hcombined :
      N * ((J.card : ENNReal) * q * (1 - (m : ENNReal) * q)) ≤
        N * (2 * B) := by
    calc
      N * ((J.card : ENNReal) * q * (1 - (m : ENNReal) * q)) =
          q * (∑ j ∈ J, N * (1 - (m : ENNReal) * q)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
            ac_rfl
      _ ≤ q * (∑ j ∈ J, 2 * ∑ θ : Fin d → Bool, err θ j) :=
        mul_le_mul_left' hlower q
      _ = 2 * (∑ θ : Fin d → Bool, ∑ j ∈ J, q * err θ j) := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
        ac_rfl
      _ ≤ 2 * (N * B) := mul_le_mul_left' hupper 2
      _ = N * (2 * B) := by ac_rfl
  have hmaster :
      (J.card : ENNReal) * q * (1 - (m : ENNReal) * q) ≤ 2 * B := by
    apply (ENNReal.mul_le_mul_iff_left (c := N) (by simp [N]) (by simp [N])).mp
    simpa [mul_comm] using hcombined
  have hBtop : B ≠ ⊤ := by
    simp only [B]
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.ofReal_ne_top
    · apply ENNReal.mul_ne_top
      · simp
      · apply ENNReal.mul_ne_top
        · simp
        · exact hqtop
  have hBreal : B.toReal = 2 * ε + δ * ((d : ℝ) * (16 * ε / d)) := by
    simp only [B]
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (by simp) hqtop))]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, hqreal]
    simp [hε.le, hδ.le]
  have hmasterR :
      (J.card : ℝ) * (16 * ε / d) *
          (1 - (m : ℝ) * (16 * ε / d)) ≤
        2 * (2 * ε + δ * ((d : ℝ) * (16 * ε / d))) := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by simp) hBtop) hmaster
    simpa [hqreal, hBreal, ENNReal.toReal_sub_of_le hmq] using h
  have hJcard : J.card = d - 1 := by
    simp [J]
  have hJcardR : (J.card : ℝ) = (d : ℝ) - 1 := by
    rw [hJcard, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hdpos.ne')]
    norm_num
  have hd16 : (16 : ℝ) ≤ d := by nlinarith [hdlarge]
  have hqRpos : 0 < 16 * ε / d := by positivity
  have hmqR : (m : ℝ) * (16 * ε / d) < 1 / 256 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 256)).2
    calc
      (m : ℝ) * (16 * ε / d) * 256 =
          ((m : ℝ) * (4096 * ε)) / d := by ring
      _ < 1 := (div_lt_one (show (0 : ℝ) < d by positivity)).2 hmprod
  have hrq : 15 * ε ≤ ((J.card : ℝ) * (16 * ε / d)) := by
    rw [hJcardR]
    calc
      15 * ε ≤ ((d : ℝ) - 1) * (16 * ε) / d := by
        apply (le_div_iff₀ (show (0 : ℝ) < d by positivity)).2
        nlinarith [hd16, hε]
      _ = ((d : ℝ) - 1) * (16 * ε / d) := by ring
  have hdq : (d : ℝ) * (16 * ε / d) = 16 * ε := by
    field_simp
  have hδ300 : δ ≤ 1 / 300 := by
    norm_num at hδ_max ⊢
    exact hδ_max
  have hfactor : (255 : ℝ) / 256 < 1 - (m : ℝ) * (16 * ε / d) := by
    nlinarith [hmqR]
  have hleft :
      15 * ε * ((255 : ℝ) / 256) <
        (J.card : ℝ) * (16 * ε / d) *
          (1 - (m : ℝ) * (16 * ε / d)) := by
    calc
      15 * ε * ((255 : ℝ) / 256) ≤
          ((J.card : ℝ) * (16 * ε / d)) * ((255 : ℝ) / 256) :=
        mul_le_mul_of_nonneg_right hrq (by norm_num)
      _ < (J.card : ℝ) * (16 * ε / d) *
          (1 - (m : ℝ) * (16 * ε / d)) :=
        mul_lt_mul_of_pos_left hfactor (lt_of_lt_of_le (by positivity) hrq)
  have hδterm : δ * (16 * ε) ≤ (1 / 300 : ℝ) * (16 * ε) :=
    mul_le_mul_of_nonneg_right hδ300 (by positivity)
  rw [hdq] at hmasterR
  nlinarith [hmasterR, hleft, hδterm, hε]

@[blueprint "def:fixed-rcn-msht-problem"
  (statement := /-- Fix a concept class $\mathcal F$ and $k$ sources.  A fixed-RCN multi-source hypothesis-testing problem consists of a type of hidden hypotheses, a type of decisions, feature marginals $\mu_{\theta,i}$ and targets $f^*_{\theta,i}\in\mathcal F$ for every hidden hypothesis $\theta$ and source $i$, and a set of correct decisions for each $\theta$.  Conditional on $\theta$, source $i$ supplies samples from the fixed-RCN law generated by $(\mu_{\theta,i},f^*_{\theta,i})$. -/)
  (title := /-- Multi-source testing problems with source-indexed RCN targets -/)
  (latexEnv := "definition")]
structure fixed_rcn_msht_problem (X : Type*) (C : mdl_concept_class X Bool) (k : ℕ) where
  Hypothesis : Type
  Decision : Type
  features : Hypothesis → Fin k → PMF X
  target : Hypothesis → Fin k → X → Bool
  target_mem : ∀ θ i, target θ i ∈ C
  correct : Hypothesis → Set Decision

@[blueprint "def:fixed-rcn-msht-sources"
  (statement := /-- For a fixed-RCN multi-source testing problem and a hidden hypothesis $\theta$, the $i$th source is the joint law obtained from its feature marginal $\mu_{\theta,i}$ and its in-class target $f^*_{\theta,i}$. -/)
  (title := /-- Source family associated with an MSHT hypothesis -/)
  (latexEnv := "definition")]
noncomputable def fixed_rcn_msht_sources {X : Type*} {C : mdl_concept_class X Bool}
    {k : ℕ} (P : fixed_rcn_msht_problem X C k) (θ : P.Hypothesis) :
    Fin k → PMF (X × Bool) :=
  fun i => fixed_rcn_distribution (P.features θ i) (P.target θ i)

@[blueprint "def:solves-fixed-rcn-msht"
  (statement := /-- Let $P$ be a fixed-RCN multi-source testing problem.  An adaptive testing tree with sample budget $m$ solves $P$ at confidence parameter $\delta$ if, under every hidden hypothesis $\theta$, evaluation against the corresponding $k$ RCN sources returns a decision in the prescribed correct set with probability at least $1-\delta$. -/)
  (title := /-- Validity of an adaptive multi-source hypothesis test -/)
  (latexEnv := "definition")]
def solves_fixed_rcn_msht {X : Type*} {C : mdl_concept_class X Bool}
    {k m : ℕ} (P : fixed_rcn_msht_problem X C k)
    (test : mdl_sampling_tree (Fin k) (X × Bool) P.Decision m) (δ : ℝ) : Prop :=
  ∀ θ, ENNReal.ofReal (1 - δ) ≤
    (mdl_sampling_tree_eval (fixed_rcn_msht_sources P θ) test).toOuterMeasure
      (P.correct θ)

@[blueprint "def:msht-signal-tree"
  (statement := /-- Given a source index and a distinguished feature value, the length-$n$ signal tree queries that source until the distinguished value appears, returns true when it appears, and returns false after $n$ unsuccessful queries. -/)
  (title := /-- Repeated-query signal detector -/)
  (latexEnv := "definition")]
def msht_signal_tree {I X : Type*} [DecidableEq X] (source : I) (signal : X) :
    (n : ℕ) → mdl_sampling_tree I (X × Bool) Bool n
  | 0 => .output false
  | n + 1 => .query source (fun z =>
      if z.1 = signal then .output true else msht_signal_tree source signal n)

@[blueprint "lem:msht-signal-tree-failure"
  (statement := /-- Let $D$ be a sample law and let $p$ be the probability that its feature coordinate equals a prescribed signal.  The probability that the length-$n$ signal tree returns false is $(1-p)^n$. -/)
  (proof := /-- Induct on $n$.  At depth zero the tree returns false.  At a positive depth, expand the evaluation using \cref{def:mdl-sampling-tree-eval,def:msht-signal-tree}.  The signal branch contributes zero to the probability of returning false, while every nonsignal branch contributes the depth-$n$ failure probability.  The total mass of the nonsignal samples is one minus the signal mass, so the induction hypothesis gives the required power. -/)
  (title := /-- Failure probability of the signal detector -/)
  (latexEnv := "lemma")]
lemma msht_signal_tree_failure {I X : Type*} [DecidableEq X] (D : PMF (X × Bool))
    (source : I) (signal : X) (n : ℕ) :
    (mdl_sampling_tree_eval (fun _ => D) (msht_signal_tree source signal n)).toOuterMeasure
        ({false} : Set Bool) =
      (1 - D.toOuterMeasure {z | z.1 = signal}) ^ n := by
  induction n with
  | zero =>
      simp [msht_signal_tree, mdl_sampling_tree_eval, PMF.toOuterMeasure_pure_apply]
  | succ n ih =>
      rw [msht_signal_tree, mdl_sampling_tree_eval, PMF.toOuterMeasure_bind_apply]
      have hsplit :
          (∑' z : X × Bool, if z.1 = signal then 0 else D z) +
              D.toOuterMeasure {z | z.1 = signal} = 1 := by
        rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_add, ← PMF.tsum_coe D]
        apply tsum_congr
        intro z
        simp only [Set.indicator_apply, Set.mem_setOf_eq]
        by_cases hz : z.1 = signal <;> simp [hz]
      have houtside :
          (∑' z : X × Bool, if z.1 = signal then 0 else D z) =
            1 - D.toOuterMeasure {z | z.1 = signal} := by
        exact ENNReal.eq_sub_of_add_eq (by
          intro htop
          rw [htop] at hsplit
          simp at hsplit) hsplit
      calc
        (∑' z : X × Bool, D z *
            (mdl_sampling_tree_eval (fun _ => D)
              (if z.1 = signal then mdl_sampling_tree.output true
                else msht_signal_tree source signal n)).toOuterMeasure {false}) =
            ∑' z : X × Bool,
              (if z.1 = signal then 0 else D z) *
                (1 - D.toOuterMeasure {z | z.1 = signal}) ^ n := by
                  apply tsum_congr
                  intro z
                  by_cases hz : z.1 = signal
                  · simp [hz, mdl_sampling_tree_eval, PMF.toOuterMeasure_pure_apply]
                  · simp [hz, ih]
        _ = (∑' z : X × Bool, if z.1 = signal then 0 else D z) *
              (1 - D.toOuterMeasure {z | z.1 = signal}) ^ n := by
                rw [ENNReal.tsum_mul_right]
        _ = (1 - D.toOuterMeasure {z | z.1 = signal}) ^ (n + 1) := by
              rw [houtside, pow_succ]
              ac_rfl

@[blueprint "lem:msht-real-signal-power-bound"
  (statement := /-- For every positive integer $N$, if a signal occurs independently with probability $1/(100N)$ on each query, then the probability of seeing no signal in $10000N$ queries is at most $0.01$. -/)
  (proof := /-- Put $x=1/(100N)$, $n=10000N$, and $y=x/(1-x)$.  Positivity of $N$ gives $0<x<1$ and $ygeq0$.  Bernoulli's inequality yields $1+ny\leq(1+y)^n=(1-x)^{-n}$.  Taking reciprocals gives $(1-x)^n\leq(1+ny)^{-1}$.  Since $ny>100$, the latter reciprocal is smaller than $1/101<0.01$. -/)
  (title := /-- Quantitative failure bound for repeated rare signals -/)
  (latexEnv := "lemma")]
lemma msht_real_signal_power_bound (N : ℕ) (hN : 0 < N) :
    (1 - 1 / (100 * (N : ℝ))) ^ (10000 * N) ≤ (0.01 : ℝ) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let x : ℝ := 1 / (100 * (N : ℝ))
  let n : ℕ := 10000 * N
  let y : ℝ := x / (1 - x)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hx_one : x < 1 := by
    dsimp [x]
    apply (div_lt_one (by positivity : (0 : ℝ) < 100 * N)).2
    nlinarith
  have hy : 0 ≤ y := by
    dsimp [y]
    positivity
  have hbern : 1 + (n : ℝ) * y ≤ (1 + y) ^ n := by
    exact one_add_mul_le_pow (by nlinarith [hy]) n
  have hbase : 1 + y = (1 - x)⁻¹ := by
    dsimp [y]
    field_simp [ne_of_gt (sub_pos.mpr hx_one)]
    ring
  rw [hbase] at hbern
  have hpowpos : 0 < ((1 - x)⁻¹) ^ n := by positivity
  have hsumpos : 0 < 1 + (n : ℝ) * y := by positivity
  have hinv :
      (((1 - x)⁻¹) ^ n)⁻¹ ≤ (1 + (n : ℝ) * y)⁻¹ :=
    (inv_le_inv₀ hpowpos hsumpos).2 hbern
  have hpow : (1 - x) ^ n ≤ (1 + (n : ℝ) * y)⁻¹ := by
    simpa [inv_pow] using hinv
  have hdenpos : (0 : ℝ) < 100 * N - 1 := by nlinarith
  have hyform : y = 1 / (100 * (N : ℝ) - 1) := by
    dsimp [y, x]
    field_simp [ne_of_gt (show (0 : ℝ) < N by positivity), ne_of_gt hdenpos]
  have hny : (100 : ℝ) < (n : ℝ) * y := by
    rw [hyform]
    dsimp [n]
    norm_num [Nat.cast_mul]
    apply (lt_div_iff₀ hdenpos).2
    nlinarith
  have hden : (101 : ℝ) < 1 + (n : ℝ) * y := by nlinarith
  have hinv_small : (1 + (n : ℝ) * y)⁻¹ < (101 : ℝ)⁻¹ :=
    (inv_lt_inv₀ hsumpos (by norm_num)).2 hden
  dsimp [x, n] at hpow ⊢
  exact hpow.trans (hinv_small.le.trans (by norm_num))

@[blueprint "thm:msht-lower-bound"
  (statement := /-- Let $\mathcal F\subseteq\{0,1\}^X$ have finite VC dimension $d$.  If $k\geq1$, $0<\alpha<1$, $d\geq8\alpha$, and
  \[
    4\cdot10^7\leq\min\left\{d,\frac{48}{\alpha}\right\},
  \]
  then there is a fixed-RCN multi-source testing problem $P$ whose source-indexed targets all belong to $\mathcal F$ and which has the following two properties.  First, $P$ is nonvacuous: some adaptive test with a finite sample budget solves $P$ with error probability at most $0.01$.  Second, every adaptive test solving $P$ with error probability at most $0.01$ and using $m$ samples satisfies
  \[
    \frac{0.015k}{4}\min\left\{\frac1{\alpha^2},\frac d\alpha\right\}
      \leq m.
  \] -/)
  (proof := /-- Put
  \[
    L=\frac{0.015k}{4}\min\left\{\frac1{\alpha^2},\frac d\alpha\right\}.
  \]
  The large-regime hypothesis gives $d\geq4\cdot10^7$, hence $d\geq3$.  By \cref{lem:mdl-vc-dim-shattered-finset}, choose a shattered set of cardinality $d$ and three distinct points in it: a baseline point and two signal points.  Shattering the empty labeling also supplies a target $f\in\mathcal F$.  Since $k>0$, $\alpha>0$, and $d>0$, one has $L>0$; choose a positive integer $N>L$ and set $q=1/(100N)$.

  Define a problem as in \cref{def:fixed-rcn-msht-problem} with hidden-hypothesis and decision types both equal to $\{0,1\}$ and correct set $\{\theta\}$ under hypothesis $\theta$.  Under either hypothesis and at every source, use the same target $f$ in \cref{def:fixed-rcn-distribution}.  Its feature marginal equals the baseline point with probability $1-q$ and the signal point indexed by $\theta$ with probability $q$.  Thus the two sample laws agree pointwise outside the event that the feature is not the baseline, while \cref{lem:fixed-rcn-feature-event} shows that this event has probability $q$ under the false hypothesis.

  Let a depth-$m$ test solve this problem in the sense of \cref{def:solves-fixed-rcn-msht}.  Under each hypothesis its error probability is at most $0.01$.  If $mq\leq1$, apply \cref{lem:mdl-sampling-tree-binary-testing} to the two sample laws.  The sum of the two error probabilities is at least $1-mq$ and at most $0.02$, so $mq\geq0.98$ and therefore $m\geq98N\geq N>L$.  If $mq>1$, then $m>100N>N>L$.  In either case $L\leq m$, which is the asserted universal lower bound.

  It remains to show that the problem is nonvacuous.  Query one fixed source $10000N$ times with the tree in \cref{def:msht-signal-tree}, returning true when the true-hypothesis signal point is observed and false otherwise.  Under the false hypothesis that signal point has probability zero, so the tree is always correct.  Under the true hypothesis, \cref{lem:msht-signal-tree-failure} identifies its error probability with $(1-q)^{10000N}$, and \cref{lem:msht-real-signal-power-bound} bounds this quantity by $0.01$.  Hence this finite tree solves the same problem. -/)
  (title := /-- Multi-source hypothesis-testing lower bound -/)
  (latexEnv := "theorem")]
theorem msht_lower_bound :
    ∀ {X : Type*} {C : mdl_concept_class X Bool} (d : ℕ),
      mdl_has_finite_vc_dim C → mdl_vc_dim C = d →
        ∀ (k : ℕ) (α : ℝ), 0 < k → 0 < α → α < 1 → 8 * α ≤ (d : ℝ) →
          4 * 10 ^ 7 ≤ min (d : ℝ) (48 / α) →
          ∃ P : fixed_rcn_msht_problem X C k,
            (∀ {m : ℕ}
                (test : mdl_sampling_tree (Fin k) (X × Bool) P.Decision m),
                  solves_fixed_rcn_msht P test 0.01 →
                    (0.015 * (k : ℝ) / 4) *
                        min (1 / α ^ 2) ((d : ℝ) / α) ≤ (m : ℝ)) ∧
            ∃ (m₀ : ℕ) (test₀ : mdl_sampling_tree (Fin k) (X × Bool) P.Decision m₀),
              solves_fixed_rcn_msht P test₀ 0.01 := by
  intro X C d hfinite hdim k α hk hα hα_one hdα hlarge
  classical
  have hdlarge : (4 * 10 ^ 7 : ℝ) ≤ d := (le_min_iff.mp hlarge).1
  have hdpos : 0 < d := by
    exact_mod_cast (show (0 : ℝ) < d by nlinarith)
  have hdthree : 3 ≤ d := by
    exact_mod_cast (show (3 : ℝ) ≤ d by nlinarith)
  rcases mdl_vc_dim_shattered_finset hfinite hdim hdpos with ⟨W, hWcard, hW⟩
  let eW : (↥W) ≃ Fin d := Finset.equivFinOfCardEq hWcard
  let point : Fin d → X := fun j => (eW.symm j : X)
  have hpoint_injective : Function.Injective point := by
    intro i j hij
    apply eW.symm.injective
    apply Subtype.ext
    simpa [point] using hij
  let j₀ : Fin d := ⟨0, by omega⟩
  let j₁ : Fin d := ⟨1, by omega⟩
  let j₂ : Fin d := ⟨2, by omega⟩
  have hj₀₁ : j₀ ≠ j₁ := by
    intro h
    have := congrArg Fin.val h
    norm_num [j₀, j₁] at this
  have hj₀₂ : j₀ ≠ j₂ := by
    intro h
    have := congrArg Fin.val h
    norm_num [j₀, j₂] at this
  have hj₁₂ : j₁ ≠ j₂ := by
    intro h
    have := congrArg Fin.val h
    norm_num [j₁, j₂] at this
  let base : X := point j₀
  let signal : Bool → X := fun θ => if θ then point j₂ else point j₁
  have hsignal_base (θ : Bool) : signal θ ≠ base := by
    cases θ
    · simpa [signal, base] using hpoint_injective.ne hj₀₁.symm
    · simpa [signal, base] using hpoint_injective.ne hj₀₂.symm
  have hsignal_ne : signal false ≠ signal true := by
    simpa [signal] using hpoint_injective.ne hj₁₂
  obtain ⟨target, htarget_mem, -⟩ :=
    hW (∅ : Set X) (Set.empty_subset (↑W : Set X))
  let L : ℝ :=
    (0.015 * (k : ℝ) / 4) * min (1 / α ^ 2) ((d : ℝ) / α)
  have hminpos : 0 < min (1 / α ^ 2) ((d : ℝ) / α) := by
    apply lt_min
    · positivity
    · positivity
  have hLpos : 0 < L := by
    dsimp [L]
    positivity
  obtain ⟨N, hLN⟩ := exists_nat_gt L
  have hN : 0 < N := by
    exact_mod_cast (show (0 : ℝ) < N by nlinarith)
  let qn : NNReal := ⟨1 / (100 * (N : ℝ)), by positivity⟩
  have hqn_le : qn ≤ 1 := by
    change 1 / (100 * (N : ℝ)) ≤ 1
    apply (div_le_one (by positivity : (0 : ℝ) < 100 * N)).2
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  let coin : PMF Bool := PMF.bernoulli qn hqn_le
  let feature (θ : Bool) : PMF X :=
    PMF.map (fun b => if b then signal θ else base) coin
  let D (θ : Bool) : PMF (X × Bool) :=
    fixed_rcn_distribution (feature θ) target
  let P : fixed_rcn_msht_problem X C k :=
    { Hypothesis := Bool
      Decision := Bool
      features := fun θ _ => feature θ
      target := fun _ _ => target
      target_mem := fun _ _ => htarget_mem
      correct := fun θ => {θ} }
  have hfeature_signal (θ : Bool) :
      (feature θ).toOuterMeasure {x | x = signal θ} = (qn : ENNReal) := by
    simp [feature, coin, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply,
      PMF.bernoulli_apply, tsum_bool, hsignal_base]
  have hfeature_cross :
      (feature false).toOuterMeasure {x | x = signal true} = 0 := by
    simp [feature, coin, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply,
      PMF.bernoulli_apply, tsum_bool, hsignal_base, hsignal_ne, hsignal_ne.symm]
  have hD_signal (θ : Bool) :
      (D θ).toOuterMeasure {z | z.1 = signal θ} = (qn : ENNReal) := by
    calc
      (D θ).toOuterMeasure {z | z.1 = signal θ} =
          (feature θ).toOuterMeasure {x | x = signal θ} := by
            exact fixed_rcn_feature_event (feature θ) target {x | x = signal θ}
      _ = (qn : ENNReal) := hfeature_signal θ
  have hD_cross :
      (D false).toOuterMeasure {z | z.1 = signal true} = 0 := by
    calc
      (D false).toOuterMeasure {z | z.1 = signal true} =
          (feature false).toOuterMeasure {x | x = signal true} := by
            exact fixed_rcn_feature_event (feature false) target
              {x | x = signal true}
      _ = 0 := hfeature_cross
  let bad : Set (X × Bool) := {z | z.1 ≠ base}
  have hD_bad : (D false).toOuterMeasure bad = (qn : ENNReal) := by
    calc
      (D false).toOuterMeasure bad =
          (feature false).toOuterMeasure {x | x ≠ base} := by
            exact fixed_rcn_feature_event (feature false) target {x | x ≠ base}
      _ = (qn : ENNReal) := by
        rw [PMF.toOuterMeasure_map_apply]
        have hpre :
            (fun b : Bool => if b then signal false else base) ⁻¹'
                {x | x ≠ base} = ({true} : Set Bool) := by
          ext b
          cases b <;> simp [hsignal_base]
        rw [hpre, PMF.toOuterMeasure_apply_singleton]
        simp [coin, PMF.bernoulli_apply]
  have hfixed_feature_eq (μ₀ μ₁ : PMF X) (z : X × Bool)
      (hz : μ₀ z.1 = μ₁ z.1) :
      fixed_rcn_distribution μ₀ target z = fixed_rcn_distribution μ₁ target z := by
    unfold fixed_rcn_distribution
    simp only [PMF.bind_apply]
    apply tsum_congr
    intro x
    by_cases hx : x = z.1
    · subst x
      rw [hz]
    · have hzpair (b : Bool) : z ≠ (x, b) := by
        intro h
        exact hx (congrArg Prod.fst h).symm
      simp [PMF.map_apply, hzpair]
  have hfeature_base (θ : Bool) :
      feature θ base = (1 - (qn : NNReal) : NNReal) := by
    simp [feature, coin, PMF.map_apply, PMF.bernoulli_apply, hsignal_base,
      (hsignal_base θ).symm]
  have hD_agree (z : X × Bool) (hz : z ∉ bad) :
      D false z = D true z := by
    apply hfixed_feature_eq
    have hzbase : z.1 = base := by simpa [bad] using hz
    rw [hzbase]
    rw [hfeature_base false, hfeature_base true]
  refine ⟨P, ?_, ?_⟩
  · intro m test hsolve
    change mdl_sampling_tree (Fin k) (X × Bool) Bool m at test
    have herror (θ : Bool) :
        (mdl_sampling_tree_eval (fun _ => D θ) test).toOuterMeasure
            {o | o ≠ θ} ≤ ENNReal.ofReal 0.01 := by
      have hsuccess := hsolve θ
      change ENNReal.ofReal (1 - 0.01) ≤
        (mdl_sampling_tree_eval (fun _ => D θ) test).toOuterMeasure {θ} at hsuccess
      let Q := mdl_sampling_tree_eval (fun _ => D θ) test
      have htotal :
          Q.toOuterMeasure {θ} + Q.toOuterMeasure {o | o ≠ θ} = 1 := by
        cases θ
        · have hset : {o : Bool | o ≠ false} = ({true} : Set Bool) := by
            ext o
            cases o <;> simp
          rw [hset, PMF.toOuterMeasure_apply_singleton,
            PMF.toOuterMeasure_apply_singleton]
          have hsum : Q false + Q true = 1 := by
            simpa only [tsum_bool] using PMF.tsum_coe Q
          exact hsum
        · have hset : {o : Bool | o ≠ true} = ({false} : Set Bool) := by
            ext o
            cases o <;> simp
          rw [hset, PMF.toOuterMeasure_apply_singleton,
            PMF.toOuterMeasure_apply_singleton]
          have hsum : Q false + Q true = 1 := by
            simpa only [tsum_bool] using PMF.tsum_coe Q
          simpa [add_comm] using hsum
      have hadd :
          ENNReal.ofReal (1 - 0.01) + Q.toOuterMeasure {o | o ≠ θ} ≤ 1 := by
        calc
          ENNReal.ofReal (1 - 0.01) + Q.toOuterMeasure {o | o ≠ θ} ≤
              Q.toOuterMeasure {θ} + Q.toOuterMeasure {o | o ≠ θ} :=
            add_le_add hsuccess (le_refl _)
          _ = 1 := htotal
      have hsub := ENNReal.le_sub_of_add_le_left (by simp) hadd
      have hvalue :
          (1 : ENNReal) - ENNReal.ofReal (1 - 0.01) =
            ENNReal.ofReal 0.01 := by
        calc
          (1 : ENNReal) - ENNReal.ofReal (1 - 0.01) =
              ENNReal.ofReal 1 - ENNReal.ofReal (1 - 0.01) := by norm_num
          _ = ENNReal.ofReal (1 - (1 - 0.01)) :=
            (ENNReal.ofReal_sub 1
              (by norm_num : (0 : ℝ) ≤ 1 - 0.01)).symm
          _ = ENNReal.ofReal 0.01 := by norm_num
      rw [hvalue] at hsub
      simpa [Q] using hsub
    have hqtop : (qn : ENNReal) ≠ ⊤ := by simp
    have hqreal : (qn : ENNReal).toReal = 1 / (100 * (N : ℝ)) := by
      change (qn : ℝ) = 1 / (100 * (N : ℝ))
      rfl
    by_cases hmq : (m : ENNReal) * (qn : ENNReal) ≤ 1
    · have hbinary :=
        mdl_sampling_tree_binary_testing (D false) (D true) bad (qn : ENNReal)
          id false true (by decide) hD_agree hD_bad.le test hqtop hmq
      have herrsum :
          (mdl_sampling_tree_eval (fun _ => D false) test).toOuterMeasure
                {o | o ≠ false} +
              (mdl_sampling_tree_eval (fun _ => D true) test).toOuterMeasure
                {o | o ≠ true} ≤ ENNReal.ofReal 0.02 := by
        calc
          _ ≤ ENNReal.ofReal 0.01 + ENNReal.ofReal 0.01 :=
            add_le_add (herror false) (herror true)
          _ = ENNReal.ofReal 0.02 := by
            rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 0.01)
              (by norm_num : (0 : ℝ) ≤ 0.01)]
            norm_num
      have hsmall :
          1 - (m : ENNReal) * (qn : ENNReal) ≤ ENNReal.ofReal 0.02 :=
        hbinary.trans herrsum
      have hsmallR := ENNReal.toReal_mono (by simp) hsmall
      rw [ENNReal.toReal_sub_of_le hmq (by simp), ENNReal.toReal_mul, hqreal]
        at hsmallR
      simp only [ENNReal.toReal_one, ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 0.02)] at hsmallR
      change L ≤ (m : ℝ)
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      calc
        L ≤ N := hLN.le
        _ ≤ (m : ℝ) := by
          field_simp [ne_of_gt hNR] at hsmallR
          nlinarith
    · have hlargeq : (1 : ENNReal) ≤ (m : ENNReal) * (qn : ENNReal) :=
        le_of_lt (not_le.mp hmq)
      have hlargeqR := ENNReal.toReal_mono
        (ENNReal.mul_ne_top (by simp) hqtop) hlargeq
      rw [ENNReal.toReal_mul, hqreal] at hlargeqR
      simp only [ENNReal.toReal_one, ENNReal.toReal_natCast] at hlargeqR
      change L ≤ (m : ℝ)
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      calc
        L ≤ N := hLN.le
        _ ≤ (m : ℝ) := by
          field_simp at hlargeqR
          nlinarith
  · let i₀ : Fin k := ⟨0, hk⟩
    let n₀ : ℕ := 10000 * N
    let test₀ : mdl_sampling_tree (Fin k) (X × Bool) Bool n₀ :=
      msht_signal_tree i₀ (signal true) n₀
    refine ⟨n₀, test₀, ?_⟩
    intro θ
    cases θ
    · change ENNReal.ofReal (1 - 0.01) ≤
        (mdl_sampling_tree_eval (fun _ => D false) test₀).toOuterMeasure {false}
      have hfail := msht_signal_tree_failure (D false) i₀ (signal true) n₀
      rw [hD_cross] at hfail
      simp at hfail
      rw [PMF.toOuterMeasure_apply_singleton]
      change ENNReal.ofReal (1 - 0.01) ≤
        (mdl_sampling_tree_eval (fun _ => D false) test₀) false
      rw [show test₀ = msht_signal_tree i₀ (signal true) n₀ by rfl, hfail]
      norm_num
    · change ENNReal.ofReal (1 - 0.01) ≤
        (mdl_sampling_tree_eval (fun _ => D true) test₀).toOuterMeasure {true}
      let Q := mdl_sampling_tree_eval (fun _ => D true) test₀
      have hfail_eq :
          Q.toOuterMeasure {false} =
            (1 - (qn : ENNReal)) ^ n₀ := by
        simpa [Q, test₀, hD_signal true] using
          msht_signal_tree_failure (D true) i₀ (signal true) n₀
      have hpowerR := msht_real_signal_power_bound N hN
      have hqreal' : (qn : ENNReal).toReal = 1 / (100 * (N : ℝ)) := by
        change (qn : ℝ) = 1 / (100 * (N : ℝ))
        rfl
      have hpowtop :
          (1 - (qn : ENNReal)) ^ n₀ ≠ ⊤ := by simp
      have hpower :
          (1 - (qn : ENNReal)) ^ n₀ ≤ ENNReal.ofReal 0.01 := by
        apply (ENNReal.toReal_le_toReal hpowtop ENNReal.ofReal_ne_top).mp
        have hqn_leE : (qn : ENNReal) ≤ 1 := by exact_mod_cast hqn_le
        rw [ENNReal.toReal_pow,
          ENNReal.toReal_sub_of_le hqn_leE (by simp), hqreal',
          ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 0.01)]
        simpa [n₀] using hpowerR
      have hfail : Q.toOuterMeasure {false} ≤ ENNReal.ofReal 0.01 := by
        rw [hfail_eq]
        exact hpower
      have htotal : Q.toOuterMeasure {true} + Q.toOuterMeasure {false} = 1 := by
        rw [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton]
        have hsum : Q false + Q true = 1 := by
          simpa only [tsum_bool] using PMF.tsum_coe Q
        simpa [add_comm] using hsum
      have hsuccess : Q.toOuterMeasure {true} =
          1 - Q.toOuterMeasure {false} := by
        exact ENNReal.eq_sub_of_add_eq (by
          intro htop
          rw [htop] at htotal
          simp at htotal) htotal
      rw [hsuccess]
      have hfail_one : Q.toOuterMeasure {false} ≤ 1 :=
        hfail.trans (by norm_num)
      have hsub :
          (1 : ENNReal) - ENNReal.ofReal 0.01 ≤
            1 - Q.toOuterMeasure {false} :=
        (ENNReal.sub_le_sub_iff_left hfail_one (by simp)).2 hfail
      have hvalue :
          ENNReal.ofReal (1 - 0.01) =
            (1 : ENNReal) - ENNReal.ofReal 0.01 := by
        simpa using ENNReal.ofReal_sub 1
          (by norm_num : (0 : ℝ) ≤ 0.01)
      rw [hvalue]
      exact hsub

@[blueprint "def:mdl-expected-source-queries"
  (statement := /-- For a family of sample laws, a source index, and an adaptive sampling tree, define the expected number of queries made to that source. -/)
  (title := /-- Expected number of queries to one source -/)
  (latexEnv := "definition")]
noncomputable def mdl_expected_source_queries {I S O : Type*} [DecidableEq I]
    (D : I → PMF S) (i : I) : {m : ℕ} → mdl_sampling_tree I S O m → ENNReal
  | _, .output _ => 0
  | _, .query source next =>
      (if source = i then 1 else 0) +
        ∑' s, D source s * mdl_expected_source_queries D i (next s)
  | _, .randomize coin next =>
      ∑' b, coin b * mdl_expected_source_queries D i (next b)

@[blueprint "lem:mdl-expected-source-queries-sum"
  (statement := /-- For a finite source set, the sum of the expected numbers of queries to all sources is at most the depth of the adaptive sampling tree. -/)
  (proof := /-- Induct on the tree in \cref{def:mdl-sampling-tree}.  An output makes no queries.  At a query node, the indicator terms sum to one, and the induction bounds for the continuations average to at most the remaining depth.  At a randomization node, the same bounds average to at most the unchanged depth.  The recursive expectations are those of \cref{def:mdl-expected-source-queries}. -/)
  (title := /-- Total expected query count is bounded by depth -/)
  (latexEnv := "lemma")]
lemma mdl_expected_source_queries_sum {I S O : Type*} [Fintype I] [DecidableEq I]
    (D : I → PMF S) {m : ℕ} (tree : mdl_sampling_tree I S O m) :
    ∑ i, mdl_expected_source_queries D i tree ≤ (m : ENNReal) := by
  induction tree with
  | output result => simp [mdl_expected_source_queries]
  | @query n source next ih =>
      simp only [mdl_expected_source_queries, Finset.sum_add_distrib]
      have hinterchange :
          (∑ i, ∑' s, D source s * mdl_expected_source_queries D i (next s)) =
            ∑' s, D source s *
              ∑ i, mdl_expected_source_queries D i (next s) := by
        calc
          (∑ i, ∑' s, D source s * mdl_expected_source_queries D i (next s)) =
              ∑' i : I, ∑' s, D source s *
                mdl_expected_source_queries D i (next s) := by
                  rw [tsum_fintype]
          _ = ∑' s, ∑' i : I, D source s *
                mdl_expected_source_queries D i (next s) := ENNReal.tsum_comm
          _ = ∑' s, D source s *
                ∑ i, mdl_expected_source_queries D i (next s) := by
                  apply tsum_congr
                  intro s
                  rw [tsum_fintype, Finset.mul_sum]
      rw [hinterchange]
      calc
        (∑ i, if source = i then 1 else 0) +
              ∑' s, D source s *
                ∑ i, mdl_expected_source_queries D i (next s) ≤
            1 + ∑' s, D source s * (n : ENNReal) := by
              apply add_le_add
              · simp
              · apply ENNReal.tsum_le_tsum
                intro s
                exact mul_le_mul_left' (ih s) (D source s)
        _ = (n + 1 : ℕ) := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
          norm_num [Nat.cast_add, add_comm]
  | @randomize n coin next ih =>
      simp only [mdl_expected_source_queries]
      calc
        ∑ i, ∑' b, coin b * mdl_expected_source_queries D i (next b) =
            ∑' b, coin b * ∑ i,
              mdl_expected_source_queries D i (next b) := by
                calc
                  _ = ∑' i : I, ∑' b, coin b *
                        mdl_expected_source_queries D i (next b) := by
                          rw [tsum_fintype]
                  _ = ∑' b, ∑' i : I, coin b *
                        mdl_expected_source_queries D i (next b) := ENNReal.tsum_comm
                  _ = _ := by
                    apply tsum_congr
                    intro b
                    rw [tsum_fintype, Finset.mul_sum]
        _ ≤
            ∑' b, coin b * (n : ENNReal) := by
              apply ENNReal.tsum_le_tsum
              intro b
              exact mul_le_mul_left' (ih b) (coin b)
        _ = (n : ENNReal) := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

@[blueprint "lem:mdl-sampling-tree-indexed-binary-testing"
  (statement := /-- Let two source-indexed sample families differ only at one source $i$, and at that source only on an event of probability at most $q$ under the first family.  For any adaptive test, the sum of its two decoding-error probabilities plus $q$ times its expected number of queries to $i$ is at least one. -/)
  (proof := /-- Induct on the tree using \cref{def:mdl-sampling-tree-eval,def:mdl-expected-source-queries}.  Output and randomization nodes follow by direct averaging.  At a query to a source other than $i$, the two laws coincide and the induction inequalities average without loss.  At a query to $i$, average only off the exceptional event, where the laws coincide, and charge its omitted probability to the new query. -/)
  (title := /-- Binary testing bound charged to queries of one source -/)
  (latexEnv := "lemma")]
lemma mdl_sampling_tree_indexed_binary_testing {I S O : Type*} [DecidableEq I]
    (D₀ D₁ : I → PMF S) (i : I) (bad : Set S) (q : ENNReal)
    (observe : O → Bool) (b₀ b₁ : Bool) (hbits : b₀ ≠ b₁)
    (hother : ∀ j, j ≠ i → D₀ j = D₁ j)
    (hagree : ∀ s, s ∉ bad → D₀ i s = D₁ i s)
    (hbad : (D₀ i).toOuterMeasure bad ≤ q) {m : ℕ}
    (tree : mdl_sampling_tree I S O m) :
    1 ≤
      (mdl_sampling_tree_eval D₀ tree).toOuterMeasure {o | observe o ≠ b₀} +
        (mdl_sampling_tree_eval D₁ tree).toOuterMeasure {o | observe o ≠ b₁} +
          q * mdl_expected_source_queries D₀ i tree := by
  classical
  induction tree with
  | output result =>
      cases b₀ <;> cases b₁ <;> cases ho : observe result <;>
        simp_all [mdl_sampling_tree_eval, mdl_expected_source_queries,
          PMF.toOuterMeasure_pure_apply, ho]
  | @query n source next ih =>
      simp only [mdl_sampling_tree_eval, PMF.toOuterMeasure_bind_apply,
        mdl_expected_source_queries]
      by_cases hsi : source = i
      · subst source
        have hpoint (s : S) :
            (if s ∈ bad then 0 else D₀ i s) ≤
              D₀ i s *
                  (mdl_sampling_tree_eval D₀ (next s)).toOuterMeasure
                    {o | observe o ≠ b₀} +
                D₁ i s *
                  (mdl_sampling_tree_eval D₁ (next s)).toOuterMeasure
                    {o | observe o ≠ b₁} +
                D₀ i s *
                  (q * mdl_expected_source_queries D₀ i (next s)) := by
          by_cases hs : s ∈ bad
          · simp [hs]
          · have hw := mul_le_mul_left' (ih s) (D₀ i s)
            calc
              (if s ∈ bad then 0 else D₀ i s) = D₀ i s := by simp [hs]
              _ ≤ D₀ i s *
                    (mdl_sampling_tree_eval D₀ (next s)).toOuterMeasure
                      {o | observe o ≠ b₀} +
                  D₀ i s *
                    (mdl_sampling_tree_eval D₁ (next s)).toOuterMeasure
                      {o | observe o ≠ b₁} +
                  D₀ i s *
                    (q * mdl_expected_source_queries D₀ i (next s)) := by
                simpa [mul_add, mul_assoc] using hw
              _ = D₀ i s *
                    (mdl_sampling_tree_eval D₀ (next s)).toOuterMeasure
                      {o | observe o ≠ b₀} +
                  D₁ i s *
                    (mdl_sampling_tree_eval D₁ (next s)).toOuterMeasure
                      {o | observe o ≠ b₁} +
                  D₀ i s *
                    (q * mdl_expected_source_queries D₀ i (next s)) := by
                rw [← hagree s hs]
        have hgood :
            (∑' s : S, if s ∈ bad then 0 else D₀ i s) ≤
              (∑' s : S, D₀ i s *
                (mdl_sampling_tree_eval D₀ (next s)).toOuterMeasure
                  {o | observe o ≠ b₀}) +
              (∑' s : S, D₁ i s *
                (mdl_sampling_tree_eval D₁ (next s)).toOuterMeasure
                  {o | observe o ≠ b₁}) +
              q * ∑' s : S,
                D₀ i s * mdl_expected_source_queries D₀ i (next s) := by
          calc
            (∑' s : S, if s ∈ bad then 0 else D₀ i s) ≤
                ∑' s : S,
                  (D₀ i s *
                      (mdl_sampling_tree_eval D₀ (next s)).toOuterMeasure
                        {o | observe o ≠ b₀} +
                    D₁ i s *
                      (mdl_sampling_tree_eval D₁ (next s)).toOuterMeasure
                        {o | observe o ≠ b₁} +
                    D₀ i s *
                      (q * mdl_expected_source_queries D₀ i (next s))) :=
              ENNReal.tsum_le_tsum hpoint
            _ = _ := by
              rw [ENNReal.tsum_add, ENNReal.tsum_add]
              congr 1
              rw [← ENNReal.tsum_mul_left]
              apply tsum_congr
              intro s
              ac_rfl
        have hsplit :
            (∑' s : S, if s ∈ bad then 0 else D₀ i s) +
                (D₀ i).toOuterMeasure bad = 1 := by
          rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_add,
            ← PMF.tsum_coe (D₀ i)]
          apply tsum_congr
          intro s
          simp only [Set.indicator_apply]
          by_cases hs : s ∈ bad <;> simp [hs]
        calc
          1 = (∑' s : S, if s ∈ bad then 0 else D₀ i s) +
              (D₀ i).toOuterMeasure bad := hsplit.symm
          _ ≤ ((∑' s : S, D₀ i s *
                  (mdl_sampling_tree_eval D₀ (next s)).toOuterMeasure
                    {o | observe o ≠ b₀}) +
                (∑' s : S, D₁ i s *
                  (mdl_sampling_tree_eval D₁ (next s)).toOuterMeasure
                    {o | observe o ≠ b₁}) +
                q * ∑' s : S,
                  D₀ i s * mdl_expected_source_queries D₀ i (next s)) + q :=
            add_le_add hgood hbad
          _ = (∑' s : S, D₀ i s *
                  (mdl_sampling_tree_eval D₀ (next s)).toOuterMeasure
                    {o | observe o ≠ b₀}) +
                (∑' s : S, D₁ i s *
                  (mdl_sampling_tree_eval D₁ (next s)).toOuterMeasure
                    {o | observe o ≠ b₁}) +
                q * (1 + ∑' s : S,
                  D₀ i s * mdl_expected_source_queries D₀ i (next s)) := by
            rw [mul_add, mul_one]
            ac_rfl
          _ = _ := by simp
      · have hsource := hother source hsi
        have hpoint (s : S) :
            D₀ source s ≤
              D₀ source s *
                  (mdl_sampling_tree_eval D₀ (next s)).toOuterMeasure
                    {o | observe o ≠ b₀} +
                D₁ source s *
                  (mdl_sampling_tree_eval D₁ (next s)).toOuterMeasure
                    {o | observe o ≠ b₁} +
                D₀ source s *
                  (q * mdl_expected_source_queries D₀ i (next s)) := by
          have hw := mul_le_mul_left' (ih s) (D₀ source s)
          calc
            D₀ source s ≤
                D₀ source s *
                    (mdl_sampling_tree_eval D₀ (next s)).toOuterMeasure
                      {o | observe o ≠ b₀} +
                  D₀ source s *
                    (mdl_sampling_tree_eval D₁ (next s)).toOuterMeasure
                      {o | observe o ≠ b₁} +
                  D₀ source s *
                    (q * mdl_expected_source_queries D₀ i (next s)) := by
              simpa [mul_add, mul_assoc] using hw
            _ = _ := by rw [hsource]
        calc
          1 = ∑' s : S, D₀ source s := (PMF.tsum_coe (D₀ source)).symm
          _ ≤ ∑' s : S,
              (D₀ source s *
                  (mdl_sampling_tree_eval D₀ (next s)).toOuterMeasure
                    {o | observe o ≠ b₀} +
                D₁ source s *
                  (mdl_sampling_tree_eval D₁ (next s)).toOuterMeasure
                    {o | observe o ≠ b₁} +
                D₀ source s *
                  (q * mdl_expected_source_queries D₀ i (next s))) :=
            ENNReal.tsum_le_tsum hpoint
          _ = (∑' s : S, D₀ source s *
                  (mdl_sampling_tree_eval D₀ (next s)).toOuterMeasure
                    {o | observe o ≠ b₀}) +
                (∑' s : S, D₁ source s *
                  (mdl_sampling_tree_eval D₁ (next s)).toOuterMeasure
                    {o | observe o ≠ b₁}) +
                q * ∑' s : S,
                  D₀ source s * mdl_expected_source_queries D₀ i (next s) := by
            rw [ENNReal.tsum_add, ENNReal.tsum_add]
            congr 1
            rw [← ENNReal.tsum_mul_left]
            apply tsum_congr
            intro s
            ac_rfl
          _ = _ := by simp [hsi]
  | @randomize n coin next ih =>
      simp only [mdl_sampling_tree_eval, PMF.toOuterMeasure_bind_apply,
        mdl_expected_source_queries]
      calc
        1 = ∑' b : Bool, coin b := (PMF.tsum_coe coin).symm
        _ ≤ ∑' b : Bool, coin b *
            ((mdl_sampling_tree_eval D₀ (next b)).toOuterMeasure
                {o | observe o ≠ b₀} +
              (mdl_sampling_tree_eval D₁ (next b)).toOuterMeasure
                {o | observe o ≠ b₁} +
              q * mdl_expected_source_queries D₀ i (next b)) := by
          apply ENNReal.tsum_le_tsum
          intro b
          simpa only [mul_one] using mul_le_mul_left' (ih b) (coin b)
        _ = (∑' b : Bool, coin b *
                (mdl_sampling_tree_eval D₀ (next b)).toOuterMeasure
                  {o | observe o ≠ b₀}) +
              (∑' b : Bool, coin b *
                (mdl_sampling_tree_eval D₁ (next b)).toOuterMeasure
                  {o | observe o ≠ b₁}) +
              q * ∑' b : Bool, coin b *
                mdl_expected_source_queries D₀ i (next b) := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_add]
          congr 1
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro b
          ac_rfl

@[blueprint "lem:mdl-sampling-tree-indexed-uniform-bit-error"
  (statement := /-- Let a finite hidden-parameter space carry a fixed-point-free bit flip, and suppose the corresponding source families change only at one source and there only on an event of probability at most $q$.  The total decoding error for that bit, plus the aggregate expected-query charge at the affected source, is at least half the number of hidden parameters. -/)
  (proof := /-- Pair each parameter with its image under the involutive equivalence.  Apply \cref{lem:mdl-sampling-tree-indexed-binary-testing} to every pair.  Summing over the finite parameter space, the equivalence permutes the second error sum onto the first, while the expected-query charge remains oriented under the original parameter. -/)
  (title := /-- Average hidden-bit error with a source-specific query charge -/)
  (latexEnv := "lemma")]
lemma mdl_sampling_tree_indexed_uniform_bit_error
    {I S O Θ : Type*} [DecidableEq I] [Fintype Θ]
    (D : Θ → I → PMF S) (bit : Θ → Bool) (flip : Θ ≃ Θ)
    (hbit : ∀ θ, bit (flip θ) = !bit θ) (i : I) (bad : Set S) (q : ENNReal)
    (observe : O → Bool)
    (hother : ∀ θ j, j ≠ i → D θ j = D (flip θ) j)
    (hagree : ∀ θ s, s ∉ bad → D θ i s = D (flip θ) i s)
    (hbad : ∀ θ, (D θ i).toOuterMeasure bad ≤ q) {m : ℕ}
    (tree : mdl_sampling_tree I S O m) :
    (Fintype.card Θ : ENNReal) ≤
      2 * ∑ θ : Θ,
        (mdl_sampling_tree_eval (D θ) tree).toOuterMeasure
          {o | observe o ≠ bit θ} +
      q * ∑ θ : Θ, mdl_expected_source_queries (D θ) i tree := by
  classical
  let err : Θ → ENNReal := fun θ =>
    (mdl_sampling_tree_eval (D θ) tree).toOuterMeasure
      {o | observe o ≠ bit θ}
  let cost : Θ → ENNReal := fun θ =>
    mdl_expected_source_queries (D θ) i tree
  have hpair (θ : Θ) : 1 ≤ err θ + err (flip θ) + q * cost θ := by
    have hb : bit θ ≠ bit (flip θ) := by
      rw [hbit]
      cases bit θ <;> simp
    simpa [err, cost] using
      mdl_sampling_tree_indexed_binary_testing (D θ) (D (flip θ)) i bad q
        observe (bit θ) (bit (flip θ)) hb (hother θ) (hagree θ)
        (hbad θ) tree
  have hsum := Finset.sum_le_sum
    (fun θ (_ : θ ∈ (Finset.univ : Finset Θ)) => hpair θ)
  have hflip_sum : ∑ θ : Θ, err (flip θ) = ∑ θ : Θ, err θ := by
    exact flip.sum_comp err
  simpa [Finset.sum_const, Finset.sum_add_distrib, hflip_sum,
    nsmul_eq_mul, two_mul, Finset.mul_sum, err, cost, mul_comm, mul_left_comm,
    mul_assoc] using hsum

@[blueprint "lem:fixed-rcn-indexed-objective-disagreement"
  (statement := /-- If a source-indexed family of in-class targets and an output family satisfy the personalized MDL objective at nonnegative accuracy $\epsilon$, then at every source the returned classifier disagrees with that source's target on feature mass at most $2\epsilon$. -/)
  (proof := /-- Fix a source.  Its target belongs to the class, so the optimal error is at most the target's error.  Apply \cref{lem:fixed-rcn-prediction-error} to the target and returned classifier at that source, then cancel the finite one-quarter baseline and the positive factor one half. -/)
  (title := /-- Indexed-target disagreement forced by the MDL objective -/)
  (latexEnv := "lemma")]
lemma fixed_rcn_indexed_objective_disagreement {X : Type*} {k : ℕ}
    {C : mdl_concept_class X Bool} (features : Fin k → PMF X)
    (target : Fin k → X → Bool) (ε : ℝ) (output : Fin k → X → Bool)
    (htarget : ∀ i, target i ∈ C) (hε : 0 ≤ ε)
    (hobj : personalized_mdl_objective C
      (fun i => fixed_rcn_distribution (features i) (target i)) ε output) :
    ∀ i, (features i).toOuterMeasure {x | output i x ≠ target i x} ≤
      ENNReal.ofReal (2 * ε) := by
  intro i
  have hopt : pmf_optimal_error
      (fixed_rcn_distribution (features i) (target i)) C ≤
      pmf_prediction_error (fixed_rcn_distribution (features i) (target i))
        (target i) := by
    unfold pmf_optimal_error
    exact iInf_le_of_le (target i) (iInf_le_of_le (htarget i) le_rfl)
  have hopt' : pmf_optimal_error
      (fixed_rcn_distribution (features i) (target i)) C + ENNReal.ofReal ε ≤
      pmf_prediction_error (fixed_rcn_distribution (features i) (target i))
          (target i) + ENNReal.ofReal ε := by
    simpa [add_comm] using add_le_add_right hopt (ENNReal.ofReal ε)
  have herr := (hobj i).trans hopt'
  rw [fixed_rcn_prediction_error, fixed_rcn_prediction_error] at herr
  simp only [ne_eq, not_true_eq_false, Set.setOf_false] at herr
  simp at herr
  have hhalf : (1 / 2 : ENNReal) *
      (features i).toOuterMeasure {x | output i x ≠ target i x} ≤
      ENNReal.ofReal ε := by
    simpa only [one_div, ne_eq] using herr
  apply (ENNReal.mul_le_mul_iff_left (c := (1 / 2 : ENNReal))
    (by norm_num) (by norm_num)).mp
  rw [mul_comm]
  calc
    (1 / 2 : ENNReal) *
        (features i).toOuterMeasure {x | output i x ≠ target i x} ≤
      ENNReal.ofReal ε := hhalf
    _ = ENNReal.ofReal (2 * ε) * (1 / 2 : ENNReal) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
      rw [mul_comm (2 : ENNReal) (ENNReal.ofReal ε)]
      rw [mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

@[blueprint "def:mdl-sampling-tree-map"
  (statement := /-- Postcompose every output leaf of an adaptive sampling tree with a fixed function, without changing its sample budget. -/)
  (title := /-- Mapping the output of a sampling tree -/)
  (latexEnv := "definition")]
def mdl_sampling_tree_map {I S O O' : Type*} (f : O → O') :
    {m : ℕ} → mdl_sampling_tree I S O m → mdl_sampling_tree I S O' m
  | _, .output result => .output (f result)
  | _, .query source next => .query source (fun s => mdl_sampling_tree_map f (next s))
  | _, .randomize coin next =>
      .randomize coin (fun b => mdl_sampling_tree_map f (next b))

@[blueprint "lem:mdl-sampling-tree-eval-map"
  (statement := /-- Evaluating a sampling tree after mapping its output gives the pushforward of the original output law under the same map. -/)
  (proof := /-- Induct on the tree using \cref{def:mdl-sampling-tree-eval,def:mdl-sampling-tree-map}.  The output case is the pushforward of a point mass, while query and randomization nodes follow because pushforward commutes with probability-mass-function bind. -/)
  (title := /-- Evaluation commutes with mapping tree outputs -/)
  (latexEnv := "lemma")]
lemma mdl_sampling_tree_eval_map {I S O O' : Type*} (D : I → PMF S)
    (f : O → O') {m : ℕ} (tree : mdl_sampling_tree I S O m) :
    mdl_sampling_tree_eval D (mdl_sampling_tree_map f tree) =
      PMF.map f (mdl_sampling_tree_eval D tree) := by
  induction tree with
  | output result =>
      simp only [mdl_sampling_tree_map, mdl_sampling_tree_eval]
      ext o
      simp only [PMF.map_apply, PMF.pure_apply]
      rw [tsum_eq_single result]
      · simp
      · intro a ha
        simp [ha]
  | query source next ih =>
      simp only [mdl_sampling_tree_map, mdl_sampling_tree_eval]
      rw [PMF.map_bind]
      congr 1
      funext s
      exact ih s
  | randomize coin next ih =>
      simp only [mdl_sampling_tree_map, mdl_sampling_tree_eval]
      rw [PMF.map_bind]
      congr 1
      funext b
      exact ih b

@[blueprint "lem:mdl-to-msht-upper-bound"
  (statement := /-- Let $\mathcal F\subseteq\{0,1\}^X$ have finite VC dimension $d$, let $\mathcal A$ be valid for every source-indexed fixed-RCN family with targets in $\mathcal F$, and let $(d,k,\epsilon,\delta)$ be admissible.  There exists a fixed-RCN multi-source testing problem $P$ with $k$ sources such that every depth-$m$ adaptive test solving $P$ with error probability at most $0.01$ satisfies
  \[
    \frac{0.015k}{4}\min\left\{\frac1{(48\epsilon)^2},
      \frac d{48\epsilon}\right\}\leq m.
  \]
  Moreover, for this same problem $P$, there exist a nonnegative integer $m$ and a depth-$m$ adaptive test solving $P$ with error probability at most $0.01$ such that
  \[
    m\leq T_{\mathcal A}(k,\epsilon,\delta)
      +\frac{192k\log 600}{48\epsilon}.
  \] -/)
  (proof := /-- By \cref{lem:mdl-vc-dim-shattered-finset}, choose a shattered set of cardinality $d$ and enumerate it by $\operatorname{Fin}(d)$.  Fix one baseline coordinate $j_0$.  Put total mass $16\epsilon$ uniformly on the $d$ coordinates and the remaining mass on $j_0$; every $j\ne j_0$ then has mass $q=16\epsilon/d$.  A hidden parameter is a Boolean array $\theta=(\theta_{i,j})_{i\in[k],j\in[d]}$.  Shattering supplies, at source $i$, an in-class target whose value at coordinate $j$ is $\theta_{i,j}$.  A decision is another Boolean array, declared correct when its $q$-weighted coordinate error is at most $2\epsilon$ at every source.

  Let a depth-$m$ tree solve this problem with error at most $0.01$.  For every source $i$ and every $j\ne j_0$, pair each hidden array with the array obtained by flipping $\theta_{i,j}$.  The paired source families coincide at sources other than $i$ and, at source $i$, coincide off coordinate $j$; by \cref{lem:fixed-rcn-feature-event}, the exceptional event has probability $q$.  Hence \cref{lem:mdl-sampling-tree-indexed-uniform-bit-error} bounds the aggregate error in estimating $\theta_{i,j}$ in terms of the expected number of queries to source $i$.  Sum these inequalities over $i$ and $j\ne j_0$.  The sum of the expected query counts is at most $m$ by \cref{lem:mdl-expected-source-queries-sum}.

  For a hidden array and a decision, sum the $q$-weighted coordinate errors over all sources.  On the correct-decision event this loss is at most $2k\epsilon$, and it is always at most $16k\epsilon$.  Applying \cref{lem:pmf-weighted-loss-high-probability-bound} at failure probability $0.01$, and then averaging over all hidden arrays, yields
  \[
    k(d-1)q\leq
      2\bigl(2k\epsilon+0.01\cdot16k\epsilon\bigr)
        +q^2(d-1)m.
  \]
  Since $d\geq4\cdot10^7$, the left side is at least $15k\epsilon$.  If $m$ were smaller than the asserted lower bound, the inequality $\min\{(48\epsilon)^{-2},d/(48\epsilon)\}\leq d/(48\epsilon)$ would make the final term smaller than $0.02k\epsilon$, contradicting the preceding display.

  Finally, map each classifier returned by $\mathcal A$ to its Boolean values on the enumerated shattered set.  By \cref{lem:fixed-rcn-indexed-objective-disagreement}, every output satisfying the personalized MDL objective maps to a correct decision.  The learner succeeds with probability at least $1-\delta\geq0.99$, and \cref{lem:mdl-sampling-tree-eval-map} transfers this guarantee to the mapped tree without changing its depth.  Thus the mapped learner tree solves the constructed problem with $m=T_{\mathcal A}(k,\epsilon,\delta)$; the additional displayed term is nonnegative, so the required upper budget follows. -/)
  (title := /-- MDL-to-MSHT reduction with an explicit hard problem -/)
  (latexEnv := "lemma")]
lemma mdl_to_msht_upper_bound {X : Type*} {C : mdl_concept_class X Bool} (d : ℕ)
    (hfinite : mdl_has_finite_vc_dim C) (hvc : mdl_vc_dim C = d) (A : mdl_algorithm X C)
    (hA : is_mdl_algorithm A) (k : ℕ) (ε δ : ℝ)
    (hadm : admissible_mdl_parameters d k ε δ) :
    ∃ P : fixed_rcn_msht_problem X C k,
      (∀ {m : ℕ}
        (test : mdl_sampling_tree (Fin k) (X × Bool) P.Decision m),
          solves_fixed_rcn_msht P test 0.01 →
            (0.015 * (k : ℝ) / 4) *
                min (1 / (48 * ε) ^ 2) ((d : ℝ) / (48 * ε)) ≤ (m : ℝ)) ∧
      ∃ (m : ℕ) (test : mdl_sampling_tree (Fin k) (X × Bool) P.Decision m),
        solves_fixed_rcn_msht P test 0.01 ∧
          (m : ℝ) ≤ (A.sampleComplexity k ε δ : ℝ) +
            192 * (k : ℝ) * Real.log 600 / (48 * ε) := by
  rcases hadm with ⟨hk, hε, hε_one, hδ, hδ_max, hdε, hlarge⟩
  classical
  have hdlarge : (4 * 10 ^ 7 : ℝ) ≤ d := (le_min_iff.mp hlarge).1
  have hdpos : 0 < d := by
    exact_mod_cast (show (0 : ℝ) < d by nlinarith)
  rcases mdl_vc_dim_shattered_finset hfinite hvc hdpos with ⟨W, hWcard, hW⟩
  let eW : (↥W) ≃ Fin d := Finset.equivFinOfCardEq hWcard
  let point : Fin d → X := fun j => (eW.symm j : X)
  have hpoint_mem (j : Fin d) : point j ∈ W := (eW.symm j).property
  have hpoint_injective : Function.Injective point := by
    intro i j hij
    apply eW.symm.injective
    apply Subtype.ext
    simpa [point] using hij
  let j₀ : Fin d := ⟨0, hdpos⟩
  letI : Nonempty (Fin d) := ⟨j₀⟩
  have hlarge_eps : (4 * 10 ^ 7 : ℝ) ≤ 1 / ε := (le_min_iff.mp hlarge).2
  have hscaled_eps : (4 * 10 ^ 7 : ℝ) * ε ≤ 1 := by
    apply (le_div_iff₀ hε).mp
    simpa [div_eq_mul_inv] using hlarge_eps
  let α : NNReal := ⟨16 * ε, by positivity⟩
  have hα : α ≤ 1 := by
    change 16 * ε ≤ 1
    nlinarith [hscaled_eps]
  let coin : PMF Bool := PMF.bernoulli α hα
  let uniform : PMF (Fin d) := PMF.ofFintype
    (fun _ => (d : ENNReal)⁻¹) (by
      simp [Finset.sum_const, nsmul_eq_mul, ENNReal.mul_inv_cancel,
        Nat.ne_of_gt hdpos])
  let ν : PMF (Fin d) := PMF.bind coin (fun b =>
    if b then uniform else PMF.pure j₀)
  let μ : PMF X := PMF.map point ν
  let q : ENNReal := (α : ENNReal) * (d : ENNReal)⁻¹
  have hν (j : Fin d) (hj : j ≠ j₀) : ν j = q := by
    simp [ν, coin, uniform, q, PMF.bind_apply, PMF.bernoulli_apply,
      PMF.ofFintype_apply, PMF.pure_apply, tsum_bool, hj]
  let V (β : Fin d → Bool) : Set X := point '' {j | β j = true}
  have hVsub (β : Fin d → Bool) : V β ⊆ (↑W : Set X) := by
    rintro x ⟨j, -, rfl⟩
    exact hpoint_mem j
  have htarget_exists (β : Fin d → Bool) :
      ∃ f ∈ C, f ⁻¹' {true} ∩ (↑W : Set X) = V β :=
    hW (V β) (hVsub β)
  let target (β : Fin d → Bool) : X → Bool :=
    Classical.choose (htarget_exists β)
  have htarget_mem (β : Fin d → Bool) : target β ∈ C :=
    (Classical.choose_spec (htarget_exists β)).1
  have htarget_set (β : Fin d → Bool) :
      target β ⁻¹' {true} ∩ (↑W : Set X) = V β :=
    (Classical.choose_spec (htarget_exists β)).2
  have htarget_point (β : Fin d → Bool) (j : Fin d) :
      target β (point j) = β j := by
    have htrue : target β (point j) = true ↔ β j = true := by
      constructor
      · intro ht
        have hp : point j ∈ target β ⁻¹' {true} ∩ (↑W : Set X) := by
          exact ⟨by simpa using ht, hpoint_mem j⟩
        rw [htarget_set β] at hp
        rcases hp with ⟨i, hi, hij⟩
        have : i = j := hpoint_injective hij
        simpa [this] using hi
      · intro hj
        have hp : point j ∈ V β := ⟨j, hj, rfl⟩
        rw [← htarget_set β] at hp
        simpa using hp.1
    cases ht : target β (point j) <;> cases hb : β j <;> simp_all
  let Θ := Fin k → Fin d → Bool
  let D (θ : Θ) (i : Fin k) : PMF (X × Bool) :=
    fixed_rcn_distribution μ (target (θ i))
  let J : Finset (Fin d) := Finset.univ.erase j₀
  let decode (o : Fin k → X → Bool) : Θ := fun i j => o i (point j)
  let good (θ : Θ) : Set Θ :=
    {β | ∀ i, (∑ j ∈ J, if β i j ≠ θ i j then ν j else 0) ≤
      ENNReal.ofReal (2 * ε)}
  have hloss_disagree (θ : Θ) (o : Fin k → X → Bool) (i : Fin k) :
      (∑ j ∈ J, if decode o i j ≠ θ i j then ν j else 0) ≤
        μ.toOuterMeasure {x | o i x ≠ target (θ i) x} := by
    simp only [μ, PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_apply_fintype, decode]
    calc
      (∑ j ∈ J, if o i (point j) ≠ θ i j then ν j else 0) ≤
          ∑ j : Fin d, if o i (point j) ≠ θ i j then ν j else 0 := by
            apply Finset.sum_le_sum_of_subset
            simp [J]
      _ = ∑ j : Fin d,
          (point ⁻¹' {x | o i x ≠ target (θ i) x}).indicator ν j := by
            apply Finset.sum_congr rfl
            intro j hj
            simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_setOf_eq]
            rw [htarget_point]
  have hμ_zero (x : X) (hx : x ∉ Set.range point) : μ x = 0 := by
    have hj (j : Fin d) : x ≠ point j := by
      intro h
      exact hx ⟨j, h.symm⟩
    simp [μ, PMF.map_apply, hj]
  have hfixed_eq (f g : X → Bool) (z : X × Bool)
      (hfg : μ z.1 = 0 ∨ f z.1 = g z.1) :
      fixed_rcn_distribution μ f z = fixed_rcn_distribution μ g z := by
    unfold fixed_rcn_distribution
    simp only [PMF.bind_apply]
    apply tsum_congr
    intro x
    by_cases hx : x = z.1
    · subst x
      rcases hfg with hz | hz
      · simp [hz]
      · rw [hz]
    · have hzpair (b : Bool) : z ≠ (x, b) := by
        intro h
        exact hx (congrArg Prod.fst h).symm
      simp [PMF.map_apply, hzpair]
  let flip (i : Fin k) (j : Fin d) (θ : Θ) : Θ :=
    Function.update θ i (Function.update (θ i) j (!θ i j))
  have hflip_involutive (i : Fin k) (j : Fin d) : Function.Involutive (flip i j) := by
    intro θ
    funext i' j'
    by_cases hi : i' = i
    · subst i'
      by_cases hj : j' = j
      · subst j'
        simp [flip]
      · simp [flip, hj]
    · simp [flip, hi]
  let flipEquiv (i : Fin k) (j : Fin d) : Θ ≃ Θ :=
    ⟨flip i j, flip i j, hflip_involutive i j, hflip_involutive i j⟩
  have hflip_bit (i : Fin k) (j : Fin d) (θ : Θ) :
      (flipEquiv i j θ) i j = !θ i j := by
    simp [flipEquiv, flip]
  have hD_other (θ : Θ) (i : Fin k) (j : Fin d) (i' : Fin k)
      (hi : i' ≠ i) : D θ i' = D (flipEquiv i j θ) i' := by
    simp [D, flipEquiv, flip, hi]
  have hD_agree (θ : Θ) (i : Fin k) (j : Fin d) (z : X × Bool)
      (hz : z ∉ {z | z.1 = point j}) : D θ i z = D (flipEquiv i j θ) i z := by
    apply hfixed_eq
    by_cases hrange : z.1 ∈ Set.range point
    · rcases hrange with ⟨r, hr⟩
      right
      have hrj : r ≠ j := by
        intro hrj
        subst r
        exact hz (by simpa using hr.symm)
      rw [← hr, htarget_point, htarget_point]
      simp [flipEquiv, flip, hrj]
    · exact Or.inl (hμ_zero z.1 hrange)
  have hμ_point (j : Fin d) (hj : j ≠ j₀) :
      μ.toOuterMeasure {x | x = point j} = q := by
    simp only [μ, PMF.toOuterMeasure_map_apply]
    have hpre : point ⁻¹' {x | x = point j} = ({j} : Set (Fin d)) := by
      ext i
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact hpoint_injective.eq_iff
    rw [hpre, PMF.toOuterMeasure_apply_singleton, hν j hj]
  have hD_bad (θ : Θ) (i : Fin k) (j : Fin d) (hj : j ≠ j₀) :
      (D θ i).toOuterMeasure {z | z.1 = point j} = q := by
    calc
      (D θ i).toOuterMeasure {z | z.1 = point j} =
          μ.toOuterMeasure {x | x = point j} := by
            exact fixed_rcn_feature_event μ (target (θ i)) {x | x = point j}
      _ = q := hμ_point j hj
  let P : fixed_rcn_msht_problem X C k :=
    { Hypothesis := Θ
      Decision := Θ
      features := fun _ _ => μ
      target := fun θ i => target (θ i)
      target_mem := fun θ i => htarget_mem (θ i)
      correct := good }
  refine ⟨P, ?_, ?_⟩
  · intro m test hsolve
    change mdl_sampling_tree (Fin k) (X × Bool) Θ m at test
    change (0.015 * (k : ℝ) / 4) *
      min (1 / (48 * ε) ^ 2) ((d : ℝ) / (48 * ε)) ≤ (m : ℝ)
    by_contra hbound
    rw [not_le] at hbound
    let Q (θ : Θ) : PMF Θ := mdl_sampling_tree_eval (D θ) test
    let err (θ : Θ) (i : Fin k) (j : Fin d) : ENNReal :=
      (Q θ).toOuterMeasure {β | β i j ≠ θ i j}
    let cost (θ : Θ) (i : Fin k) : ENNReal :=
      mdl_expected_source_queries (D θ) i test
    let loss (θ β : Θ) : ENNReal :=
      ∑ i, ∑ j ∈ J, if β i j ≠ θ i j then ν j else 0
    let N : ENNReal := Fintype.card Θ
    let B : ENNReal :=
      (k : ENNReal) * ENNReal.ofReal (2 * ε) +
        ENNReal.ofReal 0.01 * ((k : ENNReal) * (d : ENNReal) * q)
    have hvalid (θ : Θ) :
        ENNReal.ofReal (1 - 0.01) ≤ (Q θ).toOuterMeasure (good θ) := by
      have hv := hsolve θ
      change ENNReal.ofReal (1 - 0.01) ≤
        (mdl_sampling_tree_eval (fixed_rcn_msht_sources P θ) test).toOuterMeasure
          (good θ) at hv
      have hsources : fixed_rcn_msht_sources P θ = D θ := by
        funext i
        rfl
      rw [hsources] at hv
      exact hv
    have hbit (i : Fin k) (j : Fin d) (hj : j ∈ J) :
        N ≤ 2 * ∑ θ : Θ, err θ i j + q * ∑ θ : Θ, cost θ i := by
      have hj₀ : j ≠ j₀ := Finset.ne_of_mem_erase hj
      simpa [N, err, cost, Q] using
        mdl_sampling_tree_indexed_uniform_bit_error D (fun θ => θ i j)
          (flipEquiv i j) (hflip_bit i j) i {z | z.1 = point j} q
          (fun β => β i j) (fun θ i' hi => hD_other θ i j i' hi)
          (fun θ z hz => hD_agree θ i j z hz)
          (fun θ => (hD_bad θ i j hj₀).le) test
    have hloss_good (θ β : Θ) (hβ : β ∈ good θ) :
        loss θ β ≤ (k : ENNReal) * ENNReal.ofReal (2 * ε) := by
      have hs := Finset.sum_le_sum
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hβ i)
      simpa [loss, Finset.sum_const, nsmul_eq_mul] using hs
    have hloss_all (θ β : Θ) :
        loss θ β ≤ (k : ENNReal) * (d : ENNReal) * q := by
      calc
        loss θ β ≤ ∑ i : Fin k, ∑ j ∈ J, q := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          have hj₀ : j ≠ j₀ := Finset.ne_of_mem_erase hj
          by_cases he : β i j ≠ θ i j
          · simp [loss, he, hν j hj₀]
          · simp [loss, he]
        _ ≤ ∑ i : Fin k, ∑ j : Fin d, q := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum_of_subset
          simp [J]
        _ = (k : ENNReal) * (d : ENNReal) * q := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ac_rfl
    have hweighted (θ : Θ) :
        (∑' β, Q θ β * loss θ β) ≤ B := by
      have hprob : 1 - ENNReal.ofReal 0.01 ≤ (Q θ).toOuterMeasure (good θ) := by
        have heq : (1 : ENNReal) - ENNReal.ofReal 0.01 =
            ENNReal.ofReal (1 - 0.01) := by
          rw [ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 0.01)]
          simp
        rw [heq]
        exact hvalid θ
      exact pmf_weighted_loss_high_probability_bound (Q θ) (good θ) (loss θ)
        ((k : ENNReal) * ENNReal.ofReal (2 * ε))
        ((k : ENNReal) * (d : ENNReal) * q) (ENNReal.ofReal 0.01)
        hprob (hloss_good θ) (hloss_all θ)
    have hterm (θ : Θ) (i : Fin k) (j : Fin d) (hj : j ∈ J) :
        (∑' β, Q θ β * (if β i j ≠ θ i j then ν j else 0)) =
          q * err θ i j := by
      have hj₀ : j ≠ j₀ := Finset.ne_of_mem_erase hj
      simp only [err]
      rw [← hν j hj₀, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro β
      by_cases he : β i j ≠ θ i j <;>
        simp [Set.indicator_apply, he, mul_comm]
    have htsum_sum (θ : Θ) {γ : Type} (s : Finset γ) (f : Θ → γ → ENNReal) :
        (∑' β, Q θ β * ∑ a ∈ s, f β a) =
          ∑ a ∈ s, ∑' β, Q θ β * f β a := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          simp only [Finset.mem_insert, Finset.sum_insert ha]
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, ih]
    have hexpect (θ : Θ) :
        (∑' β, Q θ β * loss θ β) =
          ∑ i, ∑ j ∈ J, q * err θ i j := by
      simp only [loss]
      calc
        (∑' β, Q θ β * ∑ i, ∑ j ∈ J,
            if β i j ≠ θ i j then ν j else 0) =
            ∑ i, ∑' β, Q θ β * ∑ j ∈ J,
              if β i j ≠ θ i j then ν j else 0 :=
          htsum_sum θ Finset.univ
            (fun β i => ∑ j ∈ J, if β i j ≠ θ i j then ν j else 0)
        _ = ∑ i, ∑ j ∈ J, q * err θ i j := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            (∑' β, Q θ β * ∑ j ∈ J,
                if β i j ≠ θ i j then ν j else 0) =
                ∑ j ∈ J, ∑' β, Q θ β *
                  (if β i j ≠ θ i j then ν j else 0) :=
              htsum_sum θ J
                (fun β j => if β i j ≠ θ i j then ν j else 0)
            _ = ∑ j ∈ J, q * err θ i j := by
              apply Finset.sum_congr rfl
              intro j hj
              exact hterm θ i j hj
    have hθbound (θ : Θ) :
        ∑ i, ∑ j ∈ J, q * err θ i j ≤ B := by
      rw [← hexpect θ]
      exact hweighted θ
    have herror_upper' :
        (∑ θ : Θ, ∑ i, ∑ j ∈ J, q * err θ i j) ≤ N * B := by
      have hs := Finset.sum_le_sum
        (fun θ (_ : θ ∈ (Finset.univ : Finset Θ)) => hθbound θ)
      simpa [N, Finset.sum_const, nsmul_eq_mul] using hs
    have hcost_each (θ : Θ) : ∑ i, cost θ i ≤ (m : ENNReal) := by
      simpa [cost] using mdl_expected_source_queries_sum (D θ) test
    have hcost_upper' :
        (∑ θ : Θ, ∑ i, cost θ i) ≤ N * (m : ENNReal) := by
      have hs := Finset.sum_le_sum
        (fun θ (_ : θ ∈ (Finset.univ : Finset Θ)) => hcost_each θ)
      simpa [N, Finset.sum_const, nsmul_eq_mul] using hs
    have hsum_comm3 (f : Θ → Fin k → Fin d → ENNReal) :
        (∑ θ : Θ, ∑ i, ∑ j ∈ J, f θ i j) =
          ∑ i, ∑ j ∈ J, ∑ θ : Θ, f θ i j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    have herror_order :
        (∑ i, ∑ j ∈ J, q * ∑ θ : Θ, err θ i j) =
          ∑ θ : Θ, ∑ i, ∑ j ∈ J, q * err θ i j := by
      simp_rw [Finset.mul_sum]
      exact (hsum_comm3 (fun θ i j => q * err θ i j)).symm
    have herror_upper :
        (∑ i, ∑ j ∈ J, q * ∑ θ : Θ, err θ i j) ≤ N * B := by
      rw [herror_order]
      exact herror_upper'
    have hcost_order :
        (∑ i, ∑ θ : Θ, cost θ i) = ∑ θ : Θ, ∑ i, cost θ i := by
      rw [Finset.sum_comm]
    have hcost_upper :
        (∑ i, ∑ θ : Θ, cost θ i) ≤ N * (m : ENNReal) := by
      rw [hcost_order]
      exact hcost_upper'
    have htesting :
        (∑ i : Fin k, ∑ j ∈ J, N) ≤
          ∑ i : Fin k, ∑ j ∈ J,
            (2 * ∑ θ : Θ, err θ i j + q * ∑ θ : Θ, cost θ i) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hbit i j hj
    have hcombined :
        N * ((k : ENNReal) * (J.card : ENNReal) * q) ≤
          2 * (∑ i, ∑ j ∈ J, q * ∑ θ : Θ, err θ i j) +
            q * q * (J.card : ENNReal) * (∑ i, ∑ θ : Θ, cost θ i) := by
      calc
        N * ((k : ENNReal) * (J.card : ENNReal) * q) =
            q * (∑ i : Fin k, ∑ j ∈ J, N) := by
              simp [Finset.sum_const, nsmul_eq_mul]
              ac_rfl
        _ ≤ q * (∑ i : Fin k, ∑ j ∈ J,
              (2 * ∑ θ : Θ, err θ i j + q * ∑ θ : Θ, cost θ i)) :=
          mul_le_mul_left' htesting q
        _ = 2 * (∑ i, ∑ j ∈ J, q * ∑ θ : Θ, err θ i j) +
              q * q * (J.card : ENNReal) * (∑ i, ∑ θ : Θ, cost θ i) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
            nsmul_eq_mul]
          ring_nf
          simp_rw [Finset.mul_sum]
          ring_nf
    have hmasterN :
        N * ((k : ENNReal) * (J.card : ENNReal) * q) ≤
          N * (2 * B + q * q * (J.card : ENNReal) * (m : ENNReal)) := by
      calc
        N * ((k : ENNReal) * (J.card : ENNReal) * q) ≤
            2 * (∑ i, ∑ j ∈ J, q * ∑ θ : Θ, err θ i j) +
              q * q * (J.card : ENNReal) * (∑ i, ∑ θ : Θ, cost θ i) := hcombined
        _ ≤ 2 * (N * B) + q * q * (J.card : ENNReal) * (N * (m : ENNReal)) :=
          add_le_add (mul_le_mul_left' herror_upper 2)
            (mul_le_mul_left' hcost_upper (q * q * (J.card : ENNReal)))
        _ = N * (2 * B + q * q * (J.card : ENNReal) * (m : ENNReal)) := by
          ring
    have hmaster :
        (k : ENNReal) * (J.card : ENNReal) * q ≤
          2 * B + q * q * (J.card : ENNReal) * (m : ENNReal) := by
      apply (ENNReal.mul_le_mul_iff_left (c := N) (by simp [N]) (by simp [N])).mp
      simpa [mul_comm] using hmasterN
    have hqtop : q ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · simp
      · simp [hdpos.ne']
    have hqreal : q.toReal = 16 * ε / d := by
      simp only [q, ENNReal.toReal_mul, ENNReal.toReal_inv]
      change (16 * ε) * (d : ℝ)⁻¹ = 16 * ε / d
      rw [div_eq_mul_inv]
    have hBtop : B ≠ ⊤ := by
      simp only [B]
      apply ENNReal.add_ne_top.mpr
      constructor
      · exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
      · apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top <;> simp
        · exact hqtop
    have hBreal : B.toReal =
        (k : ℝ) * (2 * ε) + 0.01 * ((k : ℝ) * (d : ℝ) * (16 * ε / d)) := by
      simp only [B]
      rw [ENNReal.toReal_add
        (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) hqtop))]
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_mul, hqreal]
      rw [ENNReal.toReal_natCast, ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * ε),
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 0.01)]
    have h2top : 2 * B ≠ ⊤ := ENNReal.mul_ne_top (by simp) hBtop
    have hcosttop : q * q * (J.card : ENNReal) * (m : ENNReal) ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.mul_ne_top hqtop hqtop
        · simp
      · simp
    have hRtop : 2 * B + q * q * (J.card : ENNReal) * (m : ENNReal) ≠ ⊤ := by
      apply ENNReal.add_ne_top.mpr
      exact ⟨h2top, hcosttop⟩
    have hmasterR :
        (k : ℝ) * (J.card : ℝ) * (16 * ε / d) ≤
          2 * ((k : ℝ) * (2 * ε) +
            0.01 * ((k : ℝ) * (d : ℝ) * (16 * ε / d))) +
          (16 * ε / d) * (16 * ε / d) * (J.card : ℝ) * (m : ℝ) := by
      have h := ENNReal.toReal_mono hRtop hmaster
      have hraw :
          (k : ℝ) * (J.card : ℝ) * q.toReal ≤
            2 * B.toReal + q.toReal * q.toReal * (J.card : ℝ) * (m : ℝ) := by
        simpa only [ENNReal.toReal_add h2top hcosttop, ENNReal.toReal_mul,
          ENNReal.toReal_natCast, ENNReal.toReal_ofNat] using h
      simpa only [hqreal, hBreal] using hraw
    have hJcard : J.card = d - 1 := by
      simp [J]
    have hJcardR : (J.card : ℝ) = (d : ℝ) - 1 := by
      rw [hJcard, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hdpos.ne')]
      norm_num
    have hdR : (0 : ℝ) < d := by positivity
    have hd16 : (16 : ℝ) ≤ d := by nlinarith [hdlarge]
    have hrq : 15 * ε ≤ (J.card : ℝ) * (16 * ε / d) := by
      rw [hJcardR]
      calc
        15 * ε ≤ ((d : ℝ) - 1) * (16 * ε) / d := by
          apply (le_div_iff₀ hdR).2
          nlinarith [hd16, hε]
        _ = ((d : ℝ) - 1) * (16 * ε / d) := by ring
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hleft : 15 * (k : ℝ) * ε ≤
        (k : ℝ) * (J.card : ℝ) * (16 * ε / d) := by
      nlinarith [mul_le_mul_of_nonneg_left hrq hkR.le]
    have hcoef : 0 ≤ 0.015 * (k : ℝ) / 4 := by positivity
    have hmupper : (m : ℝ) <
        (0.015 * (k : ℝ) / 4) * ((d : ℝ) / (48 * ε)) := by
      exact hbound.trans_le
        (mul_le_mul_of_nonneg_left (min_le_right _ _) hcoef)
    have hmprod : (m : ℝ) * (48 * ε) <
        (0.015 * (k : ℝ) / 4) * (d : ℝ) := by
      have hp : (0 : ℝ) < 48 * ε := by positivity
      have hh := mul_lt_mul_of_pos_right hmupper hp
      calc
        (m : ℝ) * (48 * ε) <
            ((0.015 * (k : ℝ) / 4) * ((d : ℝ) / (48 * ε))) *
              (48 * ε) := hh
        _ = (0.015 * (k : ℝ) / 4) * (d : ℝ) := by field_simp
    have hcost_num :
        256 * ε ^ 2 * (m : ℝ) < 0.02 * (k : ℝ) * ε * (d : ℝ) := by
      have hp : (0 : ℝ) < (256 / 48 : ℝ) * ε := by positivity
      have hh := mul_lt_mul_of_pos_right hmprod hp
      norm_num at hh ⊢
      nlinarith [hh]
    have hJle : (J.card : ℝ) ≤ (d : ℝ) := by
      rw [hJcardR]
      linarith
    have hcost :
        (16 * ε / d) * (16 * ε / d) * (J.card : ℝ) * (m : ℝ) <
          0.02 * (k : ℝ) * ε := by
      have hmnonneg : (0 : ℝ) ≤ m := by positivity
      calc
        (16 * ε / d) * (16 * ε / d) * (J.card : ℝ) * (m : ℝ) ≤
            (16 * ε / d) * (16 * ε / d) * (d : ℝ) * (m : ℝ) := by
              gcongr
        _ = (256 * ε ^ 2 * (m : ℝ)) / d := by field_simp; ring
        _ < (0.02 * (k : ℝ) * ε * (d : ℝ)) / d :=
          (div_lt_div_iff_of_pos_right hdR).2 hcost_num
        _ = 0.02 * (k : ℝ) * ε := by field_simp
    have hdq : (d : ℝ) * (16 * ε / d) = 16 * ε := by field_simp
    have hdqk : (k : ℝ) * (d : ℝ) * (16 * ε / d) =
        (k : ℝ) * (16 * ε) := by
      calc
        (k : ℝ) * (d : ℝ) * (16 * ε / d) =
            (k : ℝ) * ((d : ℝ) * (16 * ε / d)) := by ring
        _ = (k : ℝ) * (16 * ε) := by rw [hdq]
    rw [hdqk] at hmasterR
    nlinarith [hmasterR, hleft, hcost, hkR, hε]
  · let m := A.sampleComplexity k ε δ
    let test := mdl_sampling_tree_map decode (A.run k ε δ)
    refine ⟨m, test, ?_, ?_⟩
    · intro θ
      change ENNReal.ofReal (1 - 0.01) ≤
        (mdl_sampling_tree_eval (D θ) test).toOuterMeasure (good θ)
      have hsources : source_indexed_fixed_rcn_family C (D θ) := by
        refine ⟨fun i => target (θ i), ?_, fun _ => μ, ?_⟩
        · intro i
          exact htarget_mem (θ i)
        · intro i
          rfl
      have hδ_one : δ < 1 := by nlinarith [hδ_max]
      have hvalid := hA k hk (D θ) hsources ε δ hε hε_one hδ hδ_one
      rw [show test = mdl_sampling_tree_map decode (A.run k ε δ) by rfl,
        mdl_sampling_tree_eval_map, PMF.toOuterMeasure_map_apply]
      calc
        ENNReal.ofReal (1 - 0.01) ≤ ENNReal.ofReal (1 - δ) := by
          exact ENNReal.ofReal_le_ofReal (by nlinarith [hδ_max])
        _ ≤ (mdl_sampling_tree_eval (D θ) (A.run k ε δ)).toOuterMeasure
            {output | personalized_mdl_objective C (D θ) ε output} := hvalid
        _ ≤ (mdl_sampling_tree_eval (D θ) (A.run k ε δ)).toOuterMeasure
            (decode ⁻¹' good θ) := by
          apply PMF.toOuterMeasure_mono
          intro o ho i
          apply (hloss_disagree θ o i).trans
          exact fixed_rcn_indexed_objective_disagreement (fun _ : Fin k => μ)
            (fun i => target (θ i)) ε o (fun i => htarget_mem (θ i)) hε.le ho.1 i
    · dsimp [m]
      have hlog : 0 ≤ Real.log 600 := (Real.log_pos (by norm_num)).le
      have hextra : 0 ≤ 192 * (k : ℝ) * Real.log 600 / (48 * ε) := by
        positivity
      linarith

@[blueprint "lem:mdl-msht-raw-lower-bound"
  (statement := /-- Let $X$ be a type, let $\mathcal F\subseteq\{0,1\}^X$ have finite VC dimension equal to $d\in\mathbb N$, and let $\mathcal A$ be a valid MDL algorithm for $\mathcal F$ under fixed RCN noise of rate $1/4$.  For every $k\in\mathbb N$ and $\epsilon,\delta\in\mathbb R$ such that $(d,k,\epsilon,\delta)$ is admissible,
  \[
  \frac{0.015k}{4}\min\left\{\frac1{(48\epsilon)^2},
      \frac d{48\epsilon}\right\}
  \leq T_{\mathcal A}(k,\epsilon,\delta)
      +\frac{192k\log 600}{48\epsilon}.
  \] -/)
  (proof := /-- Invoke \cref{lem:mdl-to-msht-upper-bound} and choose its hard testing problem $P$, its solving tree, and its integer sample budget $m$.  The lower-bound property of that same witness $P$ bounds the displayed MSHT signal by $m$.  The reduction's budget estimate bounds $m$ by $T_{\mathcal A}(k,\epsilon,\delta)+192k\log(600)/(48\epsilon)$.  Transitivity gives the asserted inequality. -/)
  (title := /-- Raw lower bound furnished by the MDL-to-MSHT route -/)
  (latexEnv := "lemma")]
lemma mdl_msht_raw_lower_bound {X : Type*} {C : mdl_concept_class X Bool} (d : ℕ)
    (hfinite : mdl_has_finite_vc_dim C) (hvc : mdl_vc_dim C = d) (A : mdl_algorithm X C)
    (hA : is_mdl_algorithm A) (k : ℕ) (ε δ : ℝ)
    (hadm : admissible_mdl_parameters d k ε δ) :
    (0.015 * (k : ℝ) / 4) *
        min (1 / (48 * ε) ^ 2) ((d : ℝ) / (48 * ε)) ≤
      (A.sampleComplexity k ε δ : ℝ) +
        192 * (k : ℝ) * Real.log 600 / (48 * ε) := by
  rcases mdl_to_msht_upper_bound d hfinite hvc A hA k ε δ hadm with
    ⟨P, hlo, m, test, hsolve, hm⟩
  exact (hlo test hsolve).trans hm

@[blueprint "lem:mdl-testing-component-lower-bound"
  (statement := /-- There exists an absolute constant $c_{\mathrm{test}}\in\mathbb R$ with $c_{\mathrm{test}}>0$ such that the following holds.  Let $X$ be a type, let $\mathcal F\subseteq\{0,1\}^X$ have finite VC dimension equal to $d\in\mathbb N$, and let $\mathcal A$ be a valid MDL algorithm for $\mathcal F$ under fixed RCN noise of rate $1/4$.  For every $k\in\mathbb N$ and $\epsilon,\delta\in\mathbb R$ satisfying $k>0$, $0<\epsilon<1$, $0<\delta\leq0.01/3$, $384\epsilon\leq d$, and $4\cdot10^7\leq\min\{d,1/\epsilon\}$,
  \[
    T_{\mathcal A}(k,\epsilon,\delta)\geq
    c_{\mathrm{test}}k\min\left\{\frac1{\epsilon^2},
      \frac d\epsilon\right\}
  \] -/)
  (proof := /-- Set $c_{\mathrm{test}}=1/2000000$.  Fix $X$, $\mathcal F$, $d$, $\mathcal A$, $k$, $\epsilon$, and $\delta$ as in the statement.  By \cref{def:admissible-mdl-parameters}, one has $k>0$, $\epsilon>0$, and $4\cdot10^7\leq\min\{d,1/\epsilon\}$.  The two identities
  \[
    \frac1{(48\epsilon)^2}=\frac1{2304}\frac1{\epsilon^2},
    \qquad
    \frac d{48\epsilon}=\frac1{48}\frac d\epsilon
  \]
  and the nonnegativity of $d/\epsilon$ imply
  \[
    \min\left\{\frac1{(48\epsilon)^2},\frac d{48\epsilon}\right\}
    \geq\frac1{2304}\min\left\{\frac1{\epsilon^2},\frac d\epsilon\right\}.
  \]
  Hence \cref{lem:mdl-msht-raw-lower-bound}, together with $0.015/(4\cdot2304)=1/614400$, gives
  \[
    \frac Q{614400}\leq T_{\mathcal A}(k,\epsilon,\delta)
      +\frac{192k\log 600}{48\epsilon},
    \qquad
    Q=k\min\left\{\frac1{\epsilon^2},\frac d\epsilon\right\}.
  \]
  Since $600<(7/6)^{42}$ and $\log x<x-1$ for positive $x\ne1$, monotonicity of the logarithm yields
  $\log 600<42\log(7/6)<42/6=7$.  Thus the overhead is strictly less than $28k/\epsilon$.  Moreover,
  \[
    \min\left\{\frac1{\epsilon^2},\frac d\epsilon\right\}
      =\frac1\epsilon\min\left\{\frac1\epsilon,d\right\},
  \]
  so admissibility gives
  $28k/\epsilon\leq(7/10^7)Q$.  Subtracting the overhead from the preceding raw bound shows
  \[
    \left(\frac1{614400}-\frac7{10^7}\right)Q
      \leq T_{\mathcal A}(k,\epsilon,\delta).
  \]
  Finally, $Q\geq0$ and
  $1/2000000\leq1/614400-7/10^7$, which proves the claim with the asserted constant, chosen before every quantified object and parameter. -/)
  (title := /-- The multi-distribution testing contribution -/)
  (latexEnv := "lemma")]
lemma mdl_testing_component_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ {X : Type*} {C : mdl_concept_class X Bool} (d : ℕ),
        mdl_has_finite_vc_dim C → mdl_vc_dim C = d →
          ∀ (A : mdl_algorithm X C), is_mdl_algorithm A →
            ∀ (k : ℕ) (ε δ : ℝ), admissible_mdl_parameters d k ε δ →
              c * ((k : ℝ) * min (1 / ε ^ 2) ((d : ℝ) / ε)) ≤
                (A.sampleComplexity k ε δ : ℝ) := by
  refine ⟨1 / 2000000, by norm_num, ?_⟩
  intro X C d hfinite hvc A hA k ε δ hadm
  have hraw := mdl_msht_raw_lower_bound d hfinite hvc A hA k ε δ hadm
  rcases hadm with ⟨hk, hε, hε_one, hδ, hδ_max, hdε, hlarge⟩
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hbase_nonneg :
      0 ≤ min (1 / ε ^ 2) ((d : ℝ) / ε) := by
    exact le_min (by positivity) (by positivity)
  have hmin_scaled :
      (1 / 2304 : ℝ) * min (1 / ε ^ 2) ((d : ℝ) / ε) ≤
        min (1 / (48 * ε) ^ 2) ((d : ℝ) / (48 * ε)) := by
    apply le_min
    · calc
        (1 / 2304 : ℝ) * min (1 / ε ^ 2) ((d : ℝ) / ε) ≤
            (1 / 2304 : ℝ) * (1 / ε ^ 2) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
        _ = 1 / (48 * ε) ^ 2 := by
          field_simp [hε_ne]
          <;> ring
    · calc
        (1 / 2304 : ℝ) * min (1 / ε ^ 2) ((d : ℝ) / ε) ≤
            (1 / 2304 : ℝ) * ((d : ℝ) / ε) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
        _ ≤ (1 / 48 : ℝ) * ((d : ℝ) / ε) := by
          apply mul_le_mul_of_nonneg_right
          · norm_num
          · positivity
        _ = (d : ℝ) / (48 * ε) := by
          field_simp [hε_ne]
          <;> ring
  have hsignal :
      (1 / 614400 : ℝ) *
          ((k : ℝ) * min (1 / ε ^ 2) ((d : ℝ) / ε)) ≤
        (0.015 * (k : ℝ) / 4) *
          min (1 / (48 * ε) ^ 2) ((d : ℝ) / (48 * ε)) := by
    calc
      (1 / 614400 : ℝ) *
          ((k : ℝ) * min (1 / ε ^ 2) ((d : ℝ) / ε)) =
          (0.015 * (k : ℝ) / 4) *
            ((1 / 2304 : ℝ) * min (1 / ε ^ 2) ((d : ℝ) / ε)) := by
        ring
      _ ≤ (0.015 * (k : ℝ) / 4) *
          min (1 / (48 * ε) ^ 2) ((d : ℝ) / (48 * ε)) := by
        apply mul_le_mul_of_nonneg_left hmin_scaled
        positivity
  have hsignal_bound :
      (1 / 614400 : ℝ) *
          ((k : ℝ) * min (1 / ε ^ 2) ((d : ℝ) / ε)) ≤
        (A.sampleComplexity k ε δ : ℝ) +
          192 * (k : ℝ) * Real.log 600 / (48 * ε) :=
    hsignal.trans hraw
  have hpow : (600 : ℝ) < (7 / 6 : ℝ) ^ 42 := by
    norm_num
  have hlog_fraction : Real.log (7 / 6 : ℝ) < 1 / 6 := by
    convert Real.log_lt_sub_one_of_pos (x := (7 / 6 : ℝ)) (by norm_num) (by norm_num)
      using 1 <;> norm_num
  have hlog : Real.log 600 < 7 := by
    calc
      Real.log 600 < Real.log ((7 / 6 : ℝ) ^ 42) :=
        Real.log_lt_log (by norm_num) hpow
      _ = 42 * Real.log (7 / 6 : ℝ) := Real.log_pow _ _
      _ < 42 * (1 / 6 : ℝ) := by nlinarith
      _ = 7 := by norm_num
  have hk_div_pos : 0 < (k : ℝ) / ε := div_pos hk_pos hε
  have hoverhead :
      192 * (k : ℝ) * Real.log 600 / (48 * ε) <
        28 * ((k : ℝ) / ε) := by
    calc
      192 * (k : ℝ) * Real.log 600 / (48 * ε) =
          (4 * Real.log 600) * ((k : ℝ) / ε) := by
        field_simp [hε_ne]
        <;> ring
      _ < 28 * ((k : ℝ) / ε) := by
        apply mul_lt_mul_of_pos_right
        · nlinarith
        · exact hk_div_pos
  have hfactor :
      min (1 / ε ^ 2) ((d : ℝ) / ε) =
        (1 / ε) * min (1 / ε) (d : ℝ) := by
    calc
      min (1 / ε ^ 2) ((d : ℝ) / ε) =
          min ((1 / ε) * (1 / ε)) ((1 / ε) * (d : ℝ)) := by
        congr 1 <;> field_simp [hε_ne] <;> ring
      _ = (1 / ε) * min (1 / ε) (d : ℝ) := by
        symm
        exact mul_min_of_nonneg _ _ (by positivity)
  have hlarge' : (4 * 10 ^ 7 : ℝ) ≤ min (1 / ε) (d : ℝ) := by
    simpa [min_comm] using hlarge
  have hbase_large :
      (1 / ε) * (4 * 10 ^ 7 : ℝ) ≤
        min (1 / ε ^ 2) ((d : ℝ) / ε) := by
    rw [hfactor]
    exact mul_le_mul_of_nonneg_left hlarge' (by positivity)
  have hrate_large :
      28 * ((k : ℝ) / ε) ≤
        (7 / 10 ^ 7 : ℝ) *
          ((k : ℝ) * min (1 / ε ^ 2) ((d : ℝ) / ε)) := by
    have hkb := mul_le_mul_of_nonneg_left hbase_large hk_nonneg
    calc
      28 * ((k : ℝ) / ε) =
          (7 / 10 ^ 7 : ℝ) * ((k : ℝ) * ((1 / ε) * (4 * 10 ^ 7))) := by
        ring
      _ ≤ (7 / 10 ^ 7 : ℝ) *
          ((k : ℝ) * min (1 / ε ^ 2) ((d : ℝ) / ε)) := by
        exact mul_le_mul_of_nonneg_left hkb (by norm_num)
  have hoverhead_rate :
      192 * (k : ℝ) * Real.log 600 / (48 * ε) ≤
        (7 / 10 ^ 7 : ℝ) *
          ((k : ℝ) * min (1 / ε ^ 2) ((d : ℝ) / ε)) :=
    (hoverhead.trans_le hrate_large).le
  have hnet :
      ((1 / 614400 : ℝ) - 7 / 10 ^ 7) *
          ((k : ℝ) * min (1 / ε ^ 2) ((d : ℝ) / ε)) ≤
        (A.sampleComplexity k ε δ : ℝ) := by
    linarith
  nlinarith [mul_nonneg hk_nonneg hbase_nonneg]

@[blueprint "thm:mdl-lower-bound"
  (statement := /-- There is an absolute numerical constant $c>0$ with the following property.  Let $X$ be a domain, let $\mathcal F\subseteq\{0,1\}^X$ have finite VC dimension equal to $d\in\mathbb N$, and let $\mathcal A$ be an MDL algorithm for $\mathcal F$ that is valid under random classification noise with $\eta_i=\eta_i^*=1/4$ for every $i\in[k]$.  Then, for every $k\in\mathbb N$ and $\epsilon,\delta\in\mathbb R$ satisfying $k>0$, $0<\epsilon<1$, $0<\delta\leq0.01/3$, $384\epsilon\leq d$, and $4\cdot10^7\leq\min\{d,1/\epsilon\}$, one has
  \[
    T_{\mathcal A}(k,\epsilon,\delta)\geq
      c\left(\frac d\epsilon
        +k\min\left\{\frac1{\epsilon^2},\frac d\epsilon\right\}\right).
  \]
  Equivalently, the displayed rate is an $\Omega$ lower bound with one constant uniform in all the quantified parameters and objects. -/)
  (proof := /-- By \cref{lem:mdl-pac-component-lower-bound,lem:mdl-testing-component-lower-bound}, choose absolute constants $c_{\mathrm{PAC}}>0$ and $c_{\mathrm{test}}>0$ for the two rate components.  Set
  \[
    c=\frac12\min\{c_{\mathrm{PAC}},c_{\mathrm{test}}\}>0.
  \]
  Fix $X$, $\mathcal F$, $d$, a valid algorithm $\mathcal A$, and an admissible tuple $(k,\epsilon,\delta)$.  Unpacking \cref{def:admissible-mdl-parameters} gives $k>0$ and $\epsilon>0$.  Consequently
  \[
    x=\frac d\epsilon\geq0,
    \qquad
    y=k\min\left\{\frac1{\epsilon^2},\frac d\epsilon\right\}\geq0.
  \]
  The cited component bounds give $c_{\mathrm{PAC}}x\leq T_{\mathcal A}(k,\epsilon,\delta)$ and $c_{\mathrm{test}}y\leq T_{\mathcal A}(k,\epsilon,\delta)$.  Since $c\leq c_{\mathrm{PAC}}/2$ and $c\leq c_{\mathrm{test}}/2$, multiplication by the nonnegative quantities $x$ and $y$ yields
  \[
    cx\leq\frac12c_{\mathrm{PAC}}x,
    \qquad
    cy\leq\frac12c_{\mathrm{test}}y.
  \]
  Adding these inequalities and applying the two component bounds shows $c(x+y)\leq T_{\mathcal A}(k,\epsilon,\delta)$.  By \cref{def:mdl-lower-bound-rate,def:has-mdl-rate-lower-bound}, this is precisely the required rate lower bound. -/)
  (title := /-- MDL lower bound -/)
  (latexEnv := "theorem")]
theorem mdl_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ {X : Type*} {C : mdl_concept_class X Bool} (d : ℕ),
        mdl_has_finite_vc_dim C → mdl_vc_dim C = d →
          ∀ (A : mdl_algorithm X C), is_mdl_algorithm A →
            has_mdl_rate_lower_bound c A d := by
  rcases mdl_pac_component_lower_bound with ⟨c₁, hc₁, hpac⟩
  rcases mdl_testing_component_lower_bound with ⟨c₂, hc₂, htest⟩
  let c := min c₁ c₂ / 2
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨c, hc, ?_⟩
  intro X C d hfinite hdim A hA k ε δ hadm
  have hpac' := hpac d hfinite hdim A hA k ε δ hadm
  have htest' := htest d hfinite hdim A hA k ε δ hadm
  rcases hadm with ⟨hk, hε, hε_one, hδ, hδ_max, hdε, hlarge⟩
  have hd_nonneg : 0 ≤ (d : ℝ) / ε := by positivity
  have hmin_nonneg : 0 ≤ min (1 / ε ^ 2) ((d : ℝ) / ε) := by
    exact le_min (by positivity) hd_nonneg
  have htest_nonneg :
      0 ≤ (k : ℝ) * min (1 / ε ^ 2) ((d : ℝ) / ε) := by
    positivity
  have hc_le_pac : c ≤ c₁ / 2 := by
    dsimp [c]
    linarith [min_le_left c₁ c₂]
  have hc_le_test : c ≤ c₂ / 2 := by
    dsimp [c]
    linarith [min_le_right c₁ c₂]
  have hpac_scaled := mul_le_mul_of_nonneg_right hc_le_pac hd_nonneg
  have htest_scaled := mul_le_mul_of_nonneg_right hc_le_test htest_nonneg
  dsimp [has_mdl_rate_lower_bound, mdl_lower_bound_rate]
  nlinarith

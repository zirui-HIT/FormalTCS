import Architect
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sign
import Mathlib.NumberTheory.ZetaValues

set_option linter.all false
set_option maxHeartbeats 500000

variable {X : Type*} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

@[blueprint "def:kernel-of-feature-map"
  (statement := /-- Let $\mathcal{X}$ be a set and let $\mathcal{F}$ be a real inner product
  space. Given a map $\Phi : \mathcal{X} \times \mathbb{R} \to \mathcal{F}$, the
  \emph{kernel associated with the feature map $\Phi$} is the function
  \[
    k : (\mathcal{X} \times \mathbb{R}) \times (\mathcal{X} \times \mathbb{R}) \to \mathbb{R},
    \qquad k(z, z') = \langle \Phi(z), \Phi(z') \rangle_{\mathcal{F}} .
  \]
  This is the representation of a kernel used throughout: a kernel is symmetric and positive
  definite precisely when it arises in this way from a feature map into a real inner product
  space, and the space $\mathcal{F}$ then plays the role of the reproducing kernel Hilbert
  space of $k$, with the reproducing identity
  $f(z) = \langle f, \Phi(z) \rangle_{\mathcal{F}}$ holding by definition of the evaluation
  of $f \in \mathcal{F}$ at $z$. -/)
  (title := /-- Kernel Associated with a Feature Map -/)
  (latexEnv := "definition")]
def kernel_of_feature_map (Φ : X × ℝ → F) (z z' : X × ℝ) : ℝ :=
  inner ℝ (Φ z) (Φ z')

@[blueprint "def:history-local"
  (statement := /-- A \emph{selection} is a map $\sigma : \mathbb{N} \to \{0,1\}$; the value
  $\sigma(s)$ is to be read as recording which of two possible predictions was realised at
  round $s$, so that a selection encodes one complete trajectory of a two-atom randomised
  forecaster. Let $t \in \mathbb{N}$, let $\alpha$ be a type, and let
  $G : (\mathbb{N} \to \{0,1\}) \to \alpha$. We say that $G$ is \emph{history-local at $t$}
  if
  \[
    G(\sigma) = G(\tau) \qquad \text{whenever } \sigma(s) = \tau(s) \text{ for every } s < t,
  \]
  that is, if $G$ depends on its argument only through the coordinates strictly below $t$.
  History-locality at $t$ is the causality requirement that a quantity available to the
  forecaster at the beginning of round $t$ may depend on the realised predictions
  $p_0, \dots, p_{t-1}$ of the preceding rounds, and on nothing later. -/)
  (title := /-- History-Local Dependence on a Selection -/)
  (latexEnv := "definition")]
def history_local {α : Type*} (t : ℕ) (G : (ℕ → Fin 2) → α) : Prop :=
  ∀ σ τ : ℕ → Fin 2, (∀ s, s < t → σ s = τ s) → G σ = G τ

@[blueprint "def:any-kernel-transcript"
  (statement := /-- A \emph{transcript} of the Any Kernel algorithm over a feature set
  $\mathcal{X}$ consists of the following data, in which $\sigma$ ranges over the selections
  of \cref{def:history-local} and $t$ over the round numbers $\mathbb{N}$:
  \begin{itemize}
    \item a feature $x_t^{\sigma} \in \mathcal{X}$, the feature presented at round $t$ after
      the history recorded by $\sigma$;
    \item a pair of candidate predictions
      $q_t^{\sigma}(0), q_t^{\sigma}(1) \in [0,1]$, indexed by $i \in \{0,1\}$, which are the
      two atoms of the prediction distribution $\Delta_t^{\sigma}$ issued at round $t$ after
      the history recorded by $\sigma$;
    \item a pair of weights $w_t^{\sigma}(0), w_t^{\sigma}(1) \in \mathbb{R}$, which are the
      masses that $\Delta_t^{\sigma}$ assigns to the two atoms, so that
      $w_t^{\sigma}(i) \geq 0$ for $i \in \{0,1\}$ and
      $w_t^{\sigma}(0) + w_t^{\sigma}(1) = 1$;
    \item an outcome $y_t^{\sigma} \in \{0, 1\}$, revealed at round $t$ after the history
      recorded by $\sigma$;
  \end{itemize}
  subject to the requirement that, for every round $t$, all four maps
  $\sigma \mapsto x_t^{\sigma}$, $\sigma \mapsto q_t^{\sigma}$,
  $\sigma \mapsto w_t^{\sigma}$ and $\sigma \mapsto y_t^{\sigma}$ are history-local at $t$ in
  the sense of \cref{def:history-local}.
  Thus $\Delta_t^{\sigma}$ is the distribution on $[0,1]$ that puts mass $w_t^{\sigma}(i)$ on
  $q_t^{\sigma}(i)$ for $i \in \{0,1\}$; the case in which $\Delta_t^{\sigma}$ is a point mass
  is the case $q_t^{\sigma}(0) = q_t^{\sigma}(1)$. History-locality is precisely the
  adaptivity of the Any Kernel algorithm: the distribution issued at round $t$ is computed
  from the realised predictions $p_0, \dots, p_{t-1}$ of the preceding rounds, and from
  nothing that happens at round $t$ or later. History-locality of $x_t^{\sigma}$ and
  $y_t^{\sigma}$ is, symmetrically, the adaptivity of the adversary: the feature and the
  outcome of round $t$ are chosen, arbitrarily and with no further constraint than
  $y_t^{\sigma} \in \{0,1\}$, as functions of the realised predictions
  $p_0, \dots, p_{t-1}$ of the preceding rounds. This is the class of adversaries the main
  theorem is stated against; quantifying instead over fixed sequences
  $(x_t)_t$ and $(y_t)_t$ would capture only an oblivious adversary, since the atoms of
  $\Delta_t^{\sigma}$ realised at round $t$ differ from trajectory to trajectory and an
  adaptive adversary answers differently on each. Dependence of $y_t^{\sigma}$ on the
  prediction $p_t$ of the current round is deliberately not permitted: within a round the
  outcome is one and the same at both atoms of $\Delta_t^{\sigma}$. -/)
  (title := /-- Transcript of the Any Kernel Algorithm -/)
  (latexEnv := "definition")]
structure any_kernel_transcript (Feature : Type*) where
  feature : ℕ → (ℕ → Fin 2) → Feature
  candidate : ℕ → (ℕ → Fin 2) → Fin 2 → ℝ
  weight : ℕ → (ℕ → Fin 2) → Fin 2 → ℝ
  outcome : ℕ → (ℕ → Fin 2) → ℝ
  feature_history_local : ∀ t : ℕ, history_local t (feature t)
  candidate_history_local : ∀ t : ℕ, history_local t (candidate t)
  weight_history_local : ∀ t : ℕ, history_local t (weight t)
  outcome_history_local : ∀ t : ℕ, history_local t (outcome t)
  weight_nonneg : ∀ t : ℕ, ∀ σ : ℕ → Fin 2, ∀ i : Fin 2, 0 ≤ weight t σ i
  weight_sum_one : ∀ t : ℕ, ∀ σ : ℕ → Fin 2, ∑ i : Fin 2, weight t σ i = 1
  candidate_mem_unitInterval :
    ∀ t : ℕ, ∀ σ : ℕ → Fin 2, ∀ i : Fin 2, candidate t σ i ∈ Set.Icc (0 : ℝ) 1
  outcome_mem_zero_one :
    ∀ t : ℕ, ∀ σ : ℕ → Fin 2, outcome t σ = 0 ∨ outcome t σ = 1

@[blueprint "def:selector-extension"
  (statement := /-- Fix a horizon $T \in \mathbb{N}$. A \emph{selector} for horizon $T$ is a
  map $\sigma : \{0, \dots, T-1\} \to \{0,1\}$, recording, for each round $t < T$, which of
  the two atoms of $\Delta_t$ was realised. Its \emph{extension} is the map
  $\bar\sigma : \mathbb{N} \to \{0,1\}$ defined by $\bar\sigma(t) = \sigma(t)$ for $t < T$
  and $\bar\sigma(t) = 0$ for $t \geq T$. The extension exists only so that a selector may be
  applied at every round index; the value assigned beyond the horizon is irrelevant to every
  statement below, since all sums range over $t < T$. -/)
  (title := /-- Extension of a Finite-Horizon Selector -/)
  (latexEnv := "definition")]
def selector_extension (T : ℕ) (σ : Fin T → Fin 2) : ℕ → Fin 2 :=
  fun t => if h : t < T then σ ⟨t, h⟩ else 0

@[blueprint "def:trajectory-weight"
  (statement := /-- Let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript} and let $T \in \mathbb{N}$. For a selector
  $\sigma : \{0, \dots, T-1\} \to \{0,1\}$, the \emph{trajectory weight} of $\sigma$ is
  \[
    W_T(\sigma) = \prod_{t = 0}^{T-1} w_t^{\bar\sigma}\bigl(\bar\sigma(t)\bigr),
  \]
  where $\bar\sigma$ is the extension of \cref{def:selector-extension}. Since
  $\sigma \mapsto w_t^{\sigma}$ is history-local at $t$ by
  \cref{def:any-kernel-transcript}, the factor indexed by $t$ depends only on the
  coordinates $\bar\sigma(0), \dots, \bar\sigma(t-1)$ preceding it, so $W_T(\sigma)$ is the
  product of successive conditional probabilities: it is the probability that the adaptive
  draws $p_t \sim \Delta_t^{\bar\sigma}$, $0 \leq t < T$, realise exactly the atoms selected
  by $\sigma$. -/)
  (title := /-- Weight of a Trajectory -/)
  (latexEnv := "definition")]
def trajectory_weight (tr : any_kernel_transcript X) (T : ℕ) (σ : Fin T → Fin 2) : ℝ :=
  ∏ t ∈ Finset.range T,
    tr.weight t (selector_extension T σ) (selector_extension T σ t)

@[blueprint "def:round-expectation"
  (statement := /-- Let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $t \in \mathbb{N}$, let
  $\sigma : \mathbb{N} \to \{0,1\}$ be a selection recording the history, and let
  $g : \{0,1\} \to \mathbb{R}$ assign a real number to each atom of $\Delta_t^{\sigma}$. The
  \emph{round-$t$ expectation} of $g$ after the history $\sigma$ is
  \[
    \mathbb{E}_{p_t \sim \Delta_t^{\sigma}} g = \sum_{i \in \{0,1\}} w_t^{\sigma}(i) \, g(i).
  \]
  This is the expectation appearing as $\mathbb{E}_{p_t \sim \Delta_t}$ in the statement of
  the main theorem, taken at the history $\sigma$; it depends on $\sigma$ only through the
  coordinates strictly below $t$, because $\sigma \mapsto w_t^{\sigma}$ is history-local at
  $t$ by \cref{def:any-kernel-transcript}. -/)
  (title := /-- Expectation over the Round-$t$ Prediction Distribution -/)
  (latexEnv := "definition")]
def round_expectation (tr : any_kernel_transcript X) (t : ℕ) (σ : ℕ → Fin 2)
    (g : Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin 2, tr.weight t σ i * g i

@[blueprint "def:horizon-expectation"
  (statement := /-- Let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $T \in \mathbb{N}$, and let $G$ assign a real number
  to each map $\mathbb{N} \to \{0,1\}$. The \emph{horizon-$T$ expectation} of $G$ is
  \[
    \mathbb{E}_T\,G = \sum_{\sigma : \{0,\dots,T-1\} \to \{0,1\}} W_T(\sigma)\, G(\bar\sigma),
  \]
  the sum ranging over all $2^T$ selectors, with $W_T$ as in
  \cref{def:trajectory-weight} and $\bar\sigma$ as in \cref{def:selector-extension}. This is
  the expectation over the whole trajectory $(p_0, \dots, p_{T-1})$ of the adaptive draws
  $p_t \sim \Delta_t^{\bar\sigma}$, written $\mathbb{E}$ without a subscript in the source
  proof. -/)
  (title := /-- Expectation over the Trajectory of Predictions -/)
  (latexEnv := "definition")]
def horizon_expectation (tr : any_kernel_transcript X) (T : ℕ)
    (G : (ℕ → Fin 2) → ℝ) : ℝ :=
  ∑ σ : Fin T → Fin 2, trajectory_weight tr T σ * G (selector_extension T σ)

@[blueprint "def:score-function"
  (statement := /-- Let $\Phi : \mathcal{X} \times \mathbb{R} \to \mathcal{F}$ be a feature
  map with associated kernel $k$ as in \cref{def:kernel-of-feature-map}, let
  $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $t \in \mathbb{N}$, and let
  $\sigma : \mathbb{N} \to \{0,1\}$ be a selection of atoms, so that the prediction realised
  at round $s$ is $p_s = q_s^{\sigma}(\sigma(s))$. The \emph{score function} of round $t$
  along
  $\sigma$ is the map $S_t : \mathbb{R} \to \mathbb{R}$ given by
  \[
    S_t(p) = \sum_{s = 0}^{t-1}
        k\bigl((x_t^{\sigma}, p), (x_s^{\sigma}, p_s)\bigr) (y_s^{\sigma} - p_s)
      + \tfrac{1}{2} k\bigl((x_t^{\sigma}, p), (x_t^{\sigma}, p)\bigr) (1 - 2p).
  \]
  This is the quantity the Any Kernel algorithm evaluates at round $t$ in order to choose
  $\Delta_t^{\sigma}$. Only the rounds $s < t$ contribute; each realised prediction $p_s$
  entering the sum depends on $\sigma$ only through the coordinates
  $\sigma(0), \dots, \sigma(s)$, because $\sigma \mapsto q_s^{\sigma}$ is history-local at
  $s$ by \cref{def:any-kernel-transcript}, and the features $x_s^{\sigma}, x_t^{\sigma}$ and
  the outcomes $y_s^{\sigma}$ likewise depend on $\sigma$ only through the coordinates
  strictly below $t$, being history-local at $s \leq t$ respectively at $t$ by
  \cref{def:any-kernel-transcript}; hence $\sigma \mapsto S_t$ is history-local at $t$
  in the sense of \cref{def:history-local}, as the adaptivity of the algorithm requires. -/)
  (title := /-- Score Function of a Round -/)
  (latexEnv := "definition")]
noncomputable def score_function (Φ : X × ℝ → F) (tr : any_kernel_transcript X) (t : ℕ)
    (σ : ℕ → Fin 2) (p : ℝ) : ℝ :=
  (∑ s ∈ Finset.range t,
      kernel_of_feature_map Φ (tr.feature t σ, p) (tr.feature s σ, tr.candidate s σ (σ s))
        * (tr.outcome s σ - tr.candidate s σ (σ s)))
    + (1 / 2) * kernel_of_feature_map Φ (tr.feature t σ, p) (tr.feature t σ, p) * (1 - 2 * p)

@[blueprint "def:feature-regret-vector"
  (statement := /-- Let $\Phi : \mathcal{X} \times \mathbb{R} \to \mathcal{F}$ be a feature
  map, let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $T \in \mathbb{N}$, and let
  $\sigma : \mathbb{N} \to \{0,1\}$, so that $p_t = q_t^{\sigma}(\sigma(t))$. The
  \emph{feature regret vector} of the trajectory $\sigma$ is the element of $\mathcal{F}$
  \[
    V_T(\sigma) = \sum_{t=0}^{T-1} (y_t^{\sigma} - p_t)\, \Phi(x_t^{\sigma}, p_t).
  \]
  Its norm is the quantity bounded in the course of the proof of the main theorem. -/)
  (title := /-- Feature Regret Vector of a Trajectory -/)
  (latexEnv := "definition")]
def feature_regret_vector (Φ : X × ℝ → F) (tr : any_kernel_transcript X) (T : ℕ)
    (σ : ℕ → Fin 2) : F :=
  ∑ t ∈ Finset.range T,
    (tr.outcome t σ - tr.candidate t σ (σ t)) • Φ (tr.feature t σ, tr.candidate t σ (σ t))

@[blueprint "def:is-any-kernel-round"
  (statement := /-- Let $\Phi : \mathcal{X} \times \mathbb{R} \to \mathcal{F}$ be a feature
  map, let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $B \in \mathbb{R}$, let $t \in \mathbb{N}$ and let
  $\sigma : \mathbb{N} \to \{0,1\}$ record the history. Write $S_t$ for the score function of
  \cref{def:score-function}. We say that round $t$ along $\sigma$ is an
  \emph{Any Kernel round with magnitude parameter $B$} if exactly one of the following two
  alternatives holds.
  \begin{enumerate}
    \item (\emph{Aligned case.}) The score has the same nonzero sign at both endpoints,
      $\operatorname{sign} S_t(0) = \operatorname{sign} S_t(1) \neq 0$, and
      $\Delta_t^{\sigma}$ is the point mass at
      $\bigl(1 + \operatorname{sign} S_t(0)\bigr)/2$, that is,
      $q_t^{\sigma}(0) = \bigl(1 + \operatorname{sign} S_t(0)\bigr)/2$ and
      $q_t^{\sigma}(1) = q_t^{\sigma}(0)$.
    \item (\emph{Hedged case.}) One has $B > 0$; the scores at the two atoms have strictly
      opposite signs, $S_t(q_t^{\sigma}(0))\, S_t(q_t^{\sigma}(1)) < 0$; the mass of the
      first atom is the forecast-hedging weight
      \[
        w_t^{\sigma}(0)
          = \frac{|S_t(q_t^{\sigma}(1))|}{|S_t(q_t^{\sigma}(0))| + |S_t(q_t^{\sigma}(1))|};
      \]
      the two atoms are separated by at most
      $|q_t^{\sigma}(0) - q_t^{\sigma}(1)| \leq \dfrac{1}{10 B (t+1)^3}$; and the score at
      the first atom satisfies $|S_t(q_t^{\sigma}(0))| \leq (t+1) B$.
  \end{enumerate}
  Both alternatives constrain the round-$t$ data at the single history $\sigma$, which is the
  granularity at which the algorithm operates: it inspects the score function determined by
  the realised predictions $p_0, \dots, p_{t-1}$ and only then issues $\Delta_t^{\sigma}$.
  The hedged case records exactly what the Any Kernel algorithm is asserted to supply and no
  more. The existence of the sign-crossing pair $q_t^{\sigma}(0), q_t^{\sigma}(1)$ at
  separation $1/(10 B (t+1)^3)$ is produced by the binary search of the algorithm, for which
  the source gives no termination or correctness argument; it is therefore imposed here as a
  hypothesis rather than derived. Likewise the magnitude bound
  $|S_t(q_t^{\sigma}(0))| \leq (t+1) B$ is the estimate that the source asserts in the form
  $|S_t(q_t)| \leq t \cdot \max_{t' \leq t} k((x_t,p_t),(x_t,p_t))$ without proof; it too is
  a hypothesis here. -/)
  (title := /-- Any Kernel Round with Magnitude Parameter $B$ -/)
  (latexEnv := "definition")]
def is_any_kernel_round (Φ : X × ℝ → F) (tr : any_kernel_transcript X) (bound : ℝ)
    (t : ℕ) (σ : ℕ → Fin 2) : Prop :=
  (Real.sign (score_function Φ tr t σ 0) = Real.sign (score_function Φ tr t σ 1) ∧
      Real.sign (score_function Φ tr t σ 0) ≠ 0 ∧
      tr.candidate t σ 0 = (1 + Real.sign (score_function Φ tr t σ 0)) / 2 ∧
      tr.candidate t σ 1 = tr.candidate t σ 0)
    ∨ (0 < bound ∧
      score_function Φ tr t σ (tr.candidate t σ 0) *
          score_function Φ tr t σ (tr.candidate t σ 1) < 0 ∧
      tr.weight t σ 0 =
        |score_function Φ tr t σ (tr.candidate t σ 1)| /
          (|score_function Φ tr t σ (tr.candidate t σ 0)| +
            |score_function Φ tr t σ (tr.candidate t σ 1)|) ∧
      |tr.candidate t σ 0 - tr.candidate t σ 1| ≤ 1 / (10 * bound * ((t : ℝ) + 1) ^ 3) ∧
      |score_function Φ tr t σ (tr.candidate t σ 0)| ≤ ((t : ℝ) + 1) * bound)

@[blueprint "lem:deviation-sq-identity"
  (statement := /-- For every $y \in \{0,1\}$ and every $p \in \mathbb{R}$,
  \[
    (y - p)^2 = p(1 - p) + (1 - 2p)(y - p).
  \] -/)
  (proof := /-- By hypothesis $y = 0$ or $y = 1$, so it suffices to substitute each of these
  two values of $y$ in turn and to verify, for every $p \in \mathbb{R}$, the resulting
  polynomial identity in $p$. If $y = 0$, the left-hand side is $p^2$ and the right-hand side
  is $p - p^2 + (1 - 2p)(-p) = p - p^2 - p + 2p^2 = p^2$. If $y = 1$, the left-hand side is
  $1 - 2p + p^2$ and the right-hand side is
  $p - p^2 + (1 - 2p)(1 - p) = p - p^2 + 1 - 3p + 2p^2 = 1 - 2p + p^2$. In both cases the two
  sides agree, which is the assertion. -/)
  (title := /-- Deviation Identity for Binary Outcomes -/)
  (latexEnv := "lemma")]
lemma deviation_sq_identity (y p : ℝ) (hy : y = 0 ∨ y = 1) :
    (y - p) ^ 2 = p * (1 - p) + (1 - 2 * p) * (y - p) := by
  rcases hy with rfl | rfl <;> ring

@[blueprint "lem:norm-sq-sum-smul-double-sum"
  (statement := /-- Let $\mathcal{F}$ be a real inner product space, let $T \in \mathbb{N}$,
  let $a : \mathbb{N} \to \mathbb{R}$ and let $v : \mathbb{N} \to \mathcal{F}$. Then
  \[
    \Bigl\| \sum_{t=0}^{T-1} a_t\, v_t \Bigr\|_{\mathcal{F}}^2
      = \sum_{t=0}^{T-1} \sum_{s=0}^{T-1} a_t\, a_s\,
          \langle v_t, v_s \rangle_{\mathcal{F}} .
  \] -/)
  (proof := /-- Write $V = \sum_{t=0}^{T-1} a_t v_t$. In a real inner product space
  $\|V\|_{\mathcal{F}}^2 = \langle V, V\rangle_{\mathcal{F}}$, so it suffices to expand
  $\langle V, V\rangle_{\mathcal{F}}$. The inner product is additive in its first argument, so
  \[
    \langle V, V \rangle_{\mathcal{F}}
      = \sum_{t=0}^{T-1} \langle a_t v_t, V \rangle_{\mathcal{F}} ,
  \]
  and it is additive in its second argument, so for each $t$
  \[
    \langle a_t v_t, V \rangle_{\mathcal{F}}
      = \sum_{s=0}^{T-1} \langle a_t v_t, a_s v_s \rangle_{\mathcal{F}} .
  \]
  Finally, the inner product is homogeneous with respect to real scalars in each argument, so
  $\langle a_t v_t, a_s v_s\rangle_{\mathcal{F}}
    = a_t\, a_s \langle v_t, v_s\rangle_{\mathcal{F}}$ for all $t$ and $s$. Combining the three
  displayed identities gives the assertion. -/)
  (title := /-- Squared Norm of a Finite Linear Combination -/)
  (latexEnv := "lemma")]
lemma norm_sq_sum_smul_double_sum (T : ℕ) (a : ℕ → ℝ) (v : ℕ → F) :
    ‖∑ t ∈ Finset.range T, a t • v t‖ ^ 2 =
      ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T,
        a t * a s * inner ℝ (v t) (v s) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

@[blueprint "lem:sum-range-double-symm-split"
  (statement := /-- Let $T \in \mathbb{N}$ and let $f : \mathbb{N} \times \mathbb{N} \to
  \mathbb{R}$ satisfy $f(t,s) = f(s,t)$ for all $t, s \in \mathbb{N}$. Then
  \[
    \sum_{t=0}^{T-1} \sum_{s=0}^{T-1} f(t,s)
      = \sum_{t=0}^{T-1} f(t,t)
        + 2 \sum_{t=0}^{T-1} \sum_{s=0}^{t-1} f(t,s) .
  \] -/)
  (proof := /-- We argue by induction on $T$.

  For $T = 0$ all three sums are empty, so both sides are $0$.

  Assume the identity for $T = n$ and consider $T = n+1$. Splitting off the last term of a sum
  over $\{0,\dots,n\}$ gives, for the left-hand side,
  \[
    \sum_{t=0}^{n} \sum_{s=0}^{n} f(t,s)
      = \sum_{t=0}^{n-1}\Bigl( \sum_{s=0}^{n-1} f(t,s) + f(t,n) \Bigr)
        + \sum_{s=0}^{n-1} f(n,s) + f(n,n),
  \]
  where the outer sum was split at $t = n$ and each inner sum at $s = n$. Distributing the
  outer sum over the two summands, the left-hand side equals
  \[
    \sum_{t=0}^{n-1} \sum_{s=0}^{n-1} f(t,s)
      + \sum_{t=0}^{n-1} f(t,n)
      + \sum_{s=0}^{n-1} f(n,s) + f(n,n).
  \]
  By the symmetry hypothesis, $f(t,n) = f(n,t)$ for every $t$, so the two middle sums are
  equal and their total is $2 \sum_{s=0}^{n-1} f(n,s)$. Applying the induction hypothesis to
  the first term, the left-hand side equals
  \[
    \sum_{t=0}^{n-1} f(t,t)
      + 2 \sum_{t=0}^{n-1} \sum_{s=0}^{t-1} f(t,s)
      + 2 \sum_{s=0}^{n-1} f(n,s) + f(n,n).
  \]
  The right-hand side for $T = n+1$ is, after splitting both of its sums at $t = n$,
  \[
    \Bigl( \sum_{t=0}^{n-1} f(t,t) + f(n,n) \Bigr)
      + 2 \Bigl( \sum_{t=0}^{n-1} \sum_{s=0}^{t-1} f(t,s) + \sum_{s=0}^{n-1} f(n,s) \Bigr),
  \]
  which is the same real number, the two expressions differing only by the order of addition
  and by distributing the factor $2$. This completes the induction. -/)
  (title := /-- Diagonal and Strictly Triangular Splitting of a Symmetric Double Sum -/)
  (latexEnv := "lemma")]
lemma sum_range_double_symm_split (T : ℕ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ t s : ℕ, f t s = f s t) :
    ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, f t s =
      (∑ t ∈ Finset.range T, f t t)
        + 2 * ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range t, f t s := by
  induction T with
  | zero => simp
  | succ n ih =>
    have h1 : ∀ t : ℕ,
        ∑ s ∈ Finset.range (n + 1), f t s = (∑ s ∈ Finset.range n, f t s) + f t n :=
      fun t => Finset.sum_range_succ _ _
    have h2 : ∑ t ∈ Finset.range n, f t n = ∑ s ∈ Finset.range n, f n s :=
      Finset.sum_congr rfl fun t _ => hf t n
    rw [Finset.sum_range_succ, Finset.sum_range_succ (f := fun t => f t t),
      Finset.sum_range_succ (f := fun t => ∑ s ∈ Finset.range t, f t s)]
    simp only [h1, Finset.sum_add_distrib]
    rw [ih, h2]
    ring

@[blueprint "lem:feature-regret-norm-sq-expand"
  (statement := /-- Let $\Phi : \mathcal{X} \times \mathbb{R} \to \mathcal{F}$ be a feature
  map with associated kernel $k$ as in \cref{def:kernel-of-feature-map}, let
  $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $T \in \mathbb{N}$, and let
  $\sigma : \mathbb{N} \to \{0,1\}$, so that $p_t = q_t^{\sigma}(\sigma(t))$. Then the
  feature regret
  vector of \cref{def:feature-regret-vector} satisfies
  \[
    \|V_T(\sigma)\|_{\mathcal{F}}^2
      = \sum_{t=0}^{T-1} (y_t^{\sigma} - p_t)^2\,
          k\bigl((x_t^{\sigma},p_t),(x_t^{\sigma},p_t)\bigr)
        + 2 \sum_{t=0}^{T-1} (y_t^{\sigma} - p_t)
            \sum_{s=0}^{t-1} k\bigl((x_t^{\sigma},p_t),(x_s^{\sigma},p_s)\bigr)
              (y_s^{\sigma} - p_s).
  \] -/)
  (proof := /-- Write $a_t = y_t^{\sigma} - p_t$ and $v_t = \Phi(x_t^{\sigma},p_t)$ for
  $t \in \mathbb{N}$, so that, by \cref{def:feature-regret-vector},
  $V_T(\sigma) = \sum_{t=0}^{T-1} a_t\, v_t$. Applying
  \cref{lem:norm-sq-sum-smul-double-sum} to the horizon $T$, the scalars $a$ and the
  vectors $v$, and then using the definition of $k$ in
  \cref{def:kernel-of-feature-map}, gives
  \[
    \|V_T(\sigma)\|_{\mathcal{F}}^2
      = \sum_{t=0}^{T-1}\sum_{s=0}^{T-1} a_t\, a_s\,
        \langle v_t, v_s \rangle_{\mathcal{F}} .
  \]
  Put $f(t,s) = a_t\, a_s \langle v_t, v_s \rangle_{\mathcal{F}}$. Since the inner product
  of a real inner product space is symmetric, $\langle v_t, v_s\rangle_{\mathcal{F}} =
  \langle v_s, v_t\rangle_{\mathcal{F}}$, and multiplication of reals is commutative, so
  $f(t,s) = f(s,t)$ for all $t, s \in \mathbb{N}$. Hence
  \cref{lem:sum-range-double-symm-split} applies to $f$ and yields
  \[
    \|V_T(\sigma)\|_{\mathcal{F}}^2
      = \sum_{t=0}^{T-1} f(t,t) + 2 \sum_{t=0}^{T-1} \sum_{s=0}^{t-1} f(t,s) .
  \]
  It remains to identify the two resulting sums with those of the assertion, which we do
  termwise. For the diagonal sum, $f(t,t) = a_t\, a_t \langle v_t, v_t
  \rangle_{\mathcal{F}} = (y_t^{\sigma} - p_t)^2\,
  k\bigl((x_t^{\sigma},p_t),(x_t^{\sigma},p_t)\bigr)$ for every
  $t \in \{0,\dots,T-1\}$, by the definition of $k$ in \cref{def:kernel-of-feature-map}
  and commutativity of multiplication. For the strictly lower triangular sum, fix
  $t \in \{0,\dots,T-1\}$; distributing the factor $(y_t^{\sigma} - p_t)$ over the inner
  sum turns
  $(y_t^{\sigma} - p_t) \sum_{s=0}^{t-1}
    k\bigl((x_t^{\sigma},p_t),(x_s^{\sigma},p_s)\bigr)(y_s^{\sigma} - p_s)$
  into $\sum_{s=0}^{t-1} (y_t^{\sigma} - p_t)
    k\bigl((x_t^{\sigma},p_t),(x_s^{\sigma},p_s)\bigr)(y_s^{\sigma} - p_s)$, and for each
  $s \in \{0,\dots,t-1\}$ this summand equals
  $f(t,s) = a_t\, a_s \langle v_t, v_s\rangle_{\mathcal{F}}$, again by the definition of
  $k$ and commutativity of multiplication. Therefore the two sums coincide with the
  asserted ones, which proves the identity. -/)
  (title := /-- Symmetric Expansion of the Squared Feature Regret -/)
  (latexEnv := "lemma")]
lemma feature_regret_norm_sq_expand (Φ : X × ℝ → F) (tr : any_kernel_transcript X)
    (T : ℕ) (σ : ℕ → Fin 2) :
    ‖feature_regret_vector Φ tr T σ‖ ^ 2 =
      (∑ t ∈ Finset.range T,
          (tr.outcome t σ - tr.candidate t σ (σ t)) ^ 2 *
            kernel_of_feature_map Φ (tr.feature t σ, tr.candidate t σ (σ t))
              (tr.feature t σ, tr.candidate t σ (σ t)))
        + 2 * ∑ t ∈ Finset.range T,
            (tr.outcome t σ - tr.candidate t σ (σ t)) *
              ∑ s ∈ Finset.range t,
                kernel_of_feature_map Φ (tr.feature t σ, tr.candidate t σ (σ t))
                    (tr.feature s σ, tr.candidate s σ (σ s)) *
                  (tr.outcome s σ - tr.candidate s σ (σ s)) := by
  set a : ℕ → ℝ := fun t => tr.outcome t σ - tr.candidate t σ (σ t) with ha
  set v : ℕ → F := fun t => Φ (tr.feature t σ, tr.candidate t σ (σ t)) with hv
  have hsymm : ∀ t s : ℕ, a t * a s * inner ℝ (v t) (v s)
      = a s * a t * inner ℝ (v s) (v t) := by
    intro t s
    rw [real_inner_comm]
    ring
  have hnorm : ‖feature_regret_vector Φ tr T σ‖ ^ 2 =
      ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range T, a t * a s * inner ℝ (v t) (v s) :=
    norm_sq_sum_smul_double_sum T a v
  rw [hnorm, sum_range_double_symm_split T _ hsymm]
  congr 1
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp only [kernel_of_feature_map, ha, hv]
    ring
  · congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [kernel_of_feature_map, ha, hv]
    ring

@[blueprint "lem:feature-regret-norm-sq-eq-variance-add-score"
  (statement := /-- Let $\Phi : \mathcal{X} \times \mathbb{R} \to \mathcal{F}$ be a feature
  map with associated kernel $k$, let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the
  sense of \cref{def:any-kernel-transcript}, let $T \in \mathbb{N}$, and let
  $\sigma : \mathbb{N} \to \{0,1\}$, so that $p_t = q_t^{\sigma}(\sigma(t))$. Then, with
  $S_t$ the
  score function of \cref{def:score-function} and $V_T$ the feature regret vector of
  \cref{def:feature-regret-vector},
  \[
    \|V_T(\sigma)\|_{\mathcal{F}}^2
      = \sum_{t=0}^{T-1} p_t(1 - p_t)\,
          k\bigl((x_t^{\sigma},p_t),(x_t^{\sigma},p_t)\bigr)
        + 2\sum_{t=0}^{T-1} S_t(p_t)(y_t^{\sigma} - p_t).
  \] -/)
  (proof := /-- By \cref{lem:feature-regret-norm-sq-expand},
  \[
    \|V_T(\sigma)\|_{\mathcal{F}}^2
      = \sum_{t=0}^{T-1} (y_t^{\sigma} - p_t)^2
          k\bigl((x_t^{\sigma},p_t),(x_t^{\sigma},p_t)\bigr)
        + 2 \sum_{t=0}^{T-1} (y_t^{\sigma} - p_t)
            \sum_{s=0}^{t-1} k\bigl((x_t^{\sigma},p_t),(x_s^{\sigma},p_s)\bigr)
              (y_s^{\sigma} - p_s).
  \]
  Each outcome $y_t^{\sigma}$ lies in $\{0,1\}$ by \cref{def:any-kernel-transcript}, so
  \cref{lem:deviation-sq-identity} applies with $y = y_t^{\sigma}$ and $p = p_t$ and gives
  $(y_t^{\sigma} - p_t)^2 = p_t(1 - p_t) + (1 - 2p_t)(y_t^{\sigma} - p_t)$. Substituting this
  in the first sum and multiplying through by
  $k((x_t^{\sigma},p_t),(x_t^{\sigma},p_t))$ turns the first sum into
  \[
    \sum_{t=0}^{T-1} p_t(1-p_t) k\bigl((x_t^{\sigma},p_t),(x_t^{\sigma},p_t)\bigr)
      + \sum_{t=0}^{T-1} (y_t^{\sigma} - p_t)\,
        k\bigl((x_t^{\sigma},p_t),(x_t^{\sigma},p_t)\bigr)(1 - 2p_t).
  \]
  Moving the second of these two sums inside the factor
  $2\sum_t (y_t^{\sigma} - p_t)(\cdot)$, that is, writing it as
  $2\sum_{t} (y_t^{\sigma} - p_t) \cdot
    \tfrac12 k((x_t^{\sigma},p_t),(x_t^{\sigma},p_t))(1 - 2p_t)$, the bracket
  multiplying $2(y_t^{\sigma} - p_t)$ becomes
  \[
    \sum_{s=0}^{t-1} k\bigl((x_t^{\sigma},p_t),(x_s^{\sigma},p_s)\bigr)(y_s^{\sigma} - p_s)
      + \tfrac12 k\bigl((x_t^{\sigma},p_t),(x_t^{\sigma},p_t)\bigr)(1 - 2p_t),
  \]
  which is precisely $S_t(p_t)$ by \cref{def:score-function}. This is the asserted
  identity. -/)
  (title := /-- Squared Feature Regret as Variance plus Score -/)
  (latexEnv := "lemma")]
lemma feature_regret_norm_sq_eq_variance_add_score (Φ : X × ℝ → F)
    (tr : any_kernel_transcript X) (T : ℕ) (σ : ℕ → Fin 2) :
    ‖feature_regret_vector Φ tr T σ‖ ^ 2 =
      (∑ t ∈ Finset.range T,
          tr.candidate t σ (σ t) * (1 - tr.candidate t σ (σ t)) *
            kernel_of_feature_map Φ (tr.feature t σ, tr.candidate t σ (σ t))
              (tr.feature t σ, tr.candidate t σ (σ t)))
        + 2 * ∑ t ∈ Finset.range T,
            score_function Φ tr t σ (tr.candidate t σ (σ t)) *
              (tr.outcome t σ - tr.candidate t σ (σ t)) := by
  rw [feature_regret_norm_sq_expand, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [deviation_sq_identity (tr.outcome t σ) (tr.candidate t σ (σ t))
    (tr.outcome_mem_zero_one t σ)]
  simp only [score_function]
  ring

@[blueprint "lem:real-sign-eq-one-pos"
  (statement := /-- Let $r \in \mathbb{R}$ satisfy $\operatorname{sign} r = 1$. Then
  $r > 0$. -/)
  (proof := /-- We argue by trichotomy on the position of $r$ relative to $0$.

  If $r < 0$, then $\operatorname{sign} r = -1$ by the definition of the sign function, so the
  hypothesis gives $-1 = 1$, which is false.

  If $r = 0$, then $\operatorname{sign} r = 0$ by the definition of the sign function, so the
  hypothesis gives $0 = 1$, which is false.

  The remaining alternative is $r > 0$, which is the assertion. -/)
  (title := /-- Positivity from Unit Sign -/)
  (latexEnv := "lemma")]
lemma real_sign_eq_one_pos (r : ℝ) (h : Real.sign r = 1) : 0 < r := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · rw [Real.sign_of_neg hr] at h
    norm_num at h
  · rw [hr, Real.sign_zero] at h
    norm_num at h
  · exact hr

@[blueprint "lem:real-sign-eq-neg-one-neg"
  (statement := /-- Let $r \in \mathbb{R}$ satisfy $\operatorname{sign} r = -1$. Then
  $r < 0$. -/)
  (proof := /-- We argue by trichotomy on the position of $r$ relative to $0$.

  If $r = 0$, then $\operatorname{sign} r = 0$ by the definition of the sign function, so the
  hypothesis gives $0 = -1$, which is false.

  If $r > 0$, then $\operatorname{sign} r = 1$ by the definition of the sign function, so the
  hypothesis gives $1 = -1$, which is false.

  The remaining alternative is $r < 0$, which is the assertion. -/)
  (title := /-- Negativity from Sign Equal to Minus One -/)
  (latexEnv := "lemma")]
lemma real_sign_eq_neg_one_neg (r : ℝ) (h : Real.sign r = -1) : r < 0 := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · exact hr
  · rw [hr, Real.sign_zero] at h
    norm_num at h
  · rw [Real.sign_of_pos hr] at h
    norm_num at h

@[blueprint "lem:aligned-sign-round-nonpos"
  (statement := /-- Let $S : \mathbb{R} \to \mathbb{R}$, let $y \in \{0,1\}$, and suppose
  that $\operatorname{sign} S(0) = \operatorname{sign} S(1)$ and
  $\operatorname{sign} S(0) \neq 0$. Put
  $p = \bigl(1 + \operatorname{sign} S(0)\bigr)/2$. Then
  \[
    S(p)\,(y - p) \leq 0.
  \] -/)
  (proof := /-- Since $\operatorname{sign} S(0) \neq 0$, the value $\operatorname{sign} S(0)$
  is either $1$ or $-1$; we treat the two cases separately.

  Suppose first that $\operatorname{sign} S(0) = 1$. Then $p = (1+1)/2 = 1$. By hypothesis
  $\operatorname{sign} S(1) = \operatorname{sign} S(0) = 1$, so $S(1) > 0$ by
  \cref{lem:real-sign-eq-one-pos}. Moreover
  $y \in \{0,1\}$ gives $y - p = y - 1 \leq 0$. Hence $S(p)(y-p) = S(1)(y-1) \leq 0$, being
  the product of a nonnegative and a nonpositive real number.

  Suppose now that $\operatorname{sign} S(0) = -1$. Then $p = (1-1)/2 = 0$, and
  $S(0) < 0$ by \cref{lem:real-sign-eq-neg-one-neg}. Moreover $y \in \{0,1\}$ gives
  $y - p = y \geq 0$. Hence $S(p)(y-p) = S(0)\,y \leq 0$, being the product of a nonpositive
  and a nonnegative real number.

  In both cases $S(p)(y-p) \leq 0$, which is the assertion. -/)
  (title := /-- Nonpositive Score Product in the Aligned-Sign Case -/)
  (latexEnv := "lemma")]
lemma aligned_sign_round_nonpos (S : ℝ → ℝ) (y : ℝ) (hy : y = 0 ∨ y = 1)
    (hsign : Real.sign (S 0) = Real.sign (S 1)) (hne : Real.sign (S 0) ≠ 0) :
    S ((1 + Real.sign (S 0)) / 2) * (y - (1 + Real.sign (S 0)) / 2) ≤ 0 := by
  have hy0 : 0 ≤ y := by
    rcases hy with h | h <;> rw [h] <;> norm_num
  have hy1 : y ≤ 1 := by
    rcases hy with h | h <;> rw [h] <;> norm_num
  rcases Real.sign_apply_eq (S 0) with h | h | h
  · rw [h, show (1 + (-1 : ℝ)) / 2 = 0 by norm_num]
    have hneg : S 0 < 0 := real_sign_eq_neg_one_neg (S 0) h
    exact mul_nonpos_of_nonpos_of_nonneg hneg.le (by linarith)
  · exact absurd h hne
  · rw [h, show (1 + (1 : ℝ)) / 2 = 1 by norm_num]
    have hpos : 0 < S 1 := real_sign_eq_one_pos (S 1) (hsign.symm.trans h)
    exact mul_nonpos_of_nonneg_of_nonpos hpos.le (by linarith)

@[blueprint "lem:hedged-weight-cancellation"
  (statement := /-- Let $a, b \in \mathbb{R}$ satisfy $ab < 0$, and set
  $\tau = \dfrac{|b|}{|a| + |b|}$. Then
  \[
    \tau a + (1 - \tau) b = 0.
  \] -/)
  (proof := /-- A product of two reals is strictly negative precisely when its factors are
  strictly of opposite signs, so the hypothesis $ab < 0$ leaves exactly the two cases
  $a > 0 \wedge b < 0$ and $a < 0 \wedge b > 0$. We treat them in turn.

  Assume first $a > 0$ and $b < 0$. Then $|a| = a$ and $|b| = -b$, so
  $|a| + |b| = a - b$, and $a - b > 0$ because $a > 0 > b$; in particular $a - b \neq 0$,
  so we may clear this denominator. Doing so, $\tau = -b/(a-b)$ and
  $1 - \tau = \bigl((a - b) + b\bigr)/(a - b) = a/(a-b)$, whence
  \[
    \tau a + (1-\tau) b = \frac{-ab}{a-b} + \frac{ab}{a-b} = 0,
  \]
  the last equality being an identity of polynomials in $a$ and $b$.

  Assume now $a < 0$ and $b > 0$. Then $|a| = -a$ and $|b| = b$, so
  $|a| + |b| = -a + b$, and $-a + b > 0$ because $b > 0 > a$; in particular
  $-a + b \neq 0$, so again we may clear this denominator. Doing so,
  $\tau = b/(b-a)$ and $1 - \tau = \bigl((b - a) - b\bigr)/(b-a) = -a/(b-a)$, whence
  \[
    \tau a + (1-\tau) b = \frac{ab}{b-a} + \frac{-ab}{b-a} = 0,
  \]
  again by expanding the polynomial identity. As the two cases are exhaustive, the
  asserted equality holds in general. -/)
  (title := /-- Cancellation Property of the Forecast-Hedging Weight -/)
  (latexEnv := "lemma")]
lemma hedged_weight_cancellation (a b : ℝ) (hab : a * b < 0) :
    (|b| / (|a| + |b|)) * a + (1 - |b| / (|a| + |b|)) * b = 0 := by
  rcases mul_neg_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [abs_of_pos ha, abs_of_neg hb]
    have h : a + -b ≠ 0 := by linarith
    field_simp
    ring
  · rw [abs_of_neg ha, abs_of_pos hb]
    have h : -a + b ≠ 0 := by linarith
    field_simp
    ring

@[blueprint "lem:hedged-round-expectation-eq"
  (statement := /-- Let $a, b, y, q_0, q_1, w_0, w_1 \in \mathbb{R}$ satisfy
  $w_0 a + w_1 b = 0$. Then
  \[
    w_0\, a (y - q_0) + w_1\, b (y - q_1) = w_0\, a\, (q_1 - q_0).
  \] -/)
  (proof := /-- Multiplying the hypothesis $w_0 a + w_1 b = 0$ by the scalar $y - q_1$ gives
  \[
    (w_0 a + w_1 b)\,(y - q_1) = 0 .
  \]
  Expanding all products in the commutative ring $\mathbb{R}$, the left-hand side of the
  asserted identity satisfies
  \[
    w_0\, a (y - q_0) + w_1\, b (y - q_1)
      = w_0\, a\, (q_1 - q_0) + (w_0 a + w_1 b)\,(y - q_1),
  \]
  since both sides expand to
  $w_0 a y - w_0 a q_0 + w_1 b y - w_1 b q_1$. Substituting the displayed vanishing of
  $(w_0 a + w_1 b)(y - q_1)$ into this identity leaves
  \[
    w_0\, a (y - q_0) + w_1\, b (y - q_1) = w_0\, a\, (q_1 - q_0),
  \]
  which is the assertion. -/)
  (title := /-- Hedged Round Expectation after Cancellation -/)
  (latexEnv := "lemma")]
lemma hedged_round_expectation_eq (a b y q₀ q₁ w₀ w₁ : ℝ) (hcancel : w₀ * a + w₁ * b = 0) :
    w₀ * (a * (y - q₀)) + w₁ * (b * (y - q₁)) = w₀ * a * (q₁ - q₀) := by
  linear_combination (y - q₁) * hcancel

@[blueprint "lem:hedged-product-magnitude-bound"
  (statement := /-- Let $a, d, \tau, B \in \mathbb{R}$ and $n \in \mathbb{N}$ satisfy
  $B > 0$, $0 \leq \tau \leq 1$, $|a| \leq (n+1) B$ and
  $|d| \leq \dfrac{1}{10 B (n+1)^3}$. Then
  \[
    \tau\, a\, d \leq \frac{1}{10 (n+1)^2} .
  \] -/)
  (proof := /-- Since $n \geq 0$ we have $n + 1 > 0$; together with $B > 0$ this makes the
  quantities $(n+1)$ and $B$ nonzero, so the denominators occurring below may be cleared.

  We first show $\tau a d \leq |a|\,|d|$. A real number is bounded by its absolute value, so
  $\tau a d \leq |\tau a d|$. Absolute value is multiplicative and $|\tau| = \tau$ because
  $\tau \geq 0$, so $|\tau a d| = \tau\,(|a|\,|d|)$. Moreover $|a|\,|d| \geq 0$, being a
  product of two nonnegative reals, and $1 - \tau \geq 0$ by hypothesis, whence
  $(1 - \tau)\,|a|\,|d| \geq 0$, that is, $\tau\,(|a|\,|d|) \leq |a|\,|d|$. Chaining the
  three relations gives $\tau a d \leq |a|\,|d|$.

  We next bound $|a|\,|d|$. The two hypotheses $|a| \leq (n+1)B$ and
  $|d| \leq 1/(10 B (n+1)^3)$ have nonnegative left-hand sides, and
  $(n+1)B \geq 0$ since $n + 1 > 0$ and $B > 0$; hence multiplication is monotone on the
  relevant nonnegative reals and
  \[
    |a|\,|d| \leq (n+1) B \cdot \frac{1}{10 B (n+1)^3} .
  \]

  Finally, since $B \neq 0$ and $n + 1 \neq 0$, clearing denominators and expanding the
  resulting polynomial identity gives
  \[
    (n+1) B \cdot \frac{1}{10 B (n+1)^3} = \frac{1}{10 (n+1)^2} .
  \]
  Combining the three displayed relations yields
  $\tau a d \leq 1/(10 (n+1)^2)$, which is the assertion. -/)
  (title := /-- Magnitude Bound for a Damped Product -/)
  (latexEnv := "lemma")]
lemma hedged_product_magnitude_bound (a d τ bound : ℝ) (n : ℕ) (hbound : 0 < bound)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hmag : |a| ≤ ((n : ℝ) + 1) * bound)
    (hsep : |d| ≤ 1 / (10 * bound * ((n : ℝ) + 1) ^ 3)) :
    τ * a * d ≤ 1 / (10 * ((n : ℝ) + 1) ^ 2) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hb : bound ≠ 0 := ne_of_gt hbound
  have hn' : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hn
  have hnn : (0 : ℝ) ≤ |a| * |d| := mul_nonneg (abs_nonneg a) (abs_nonneg d)
  have habs : τ * a * d ≤ |a| * |d| := by
    have h1 : τ * a * d ≤ |τ * a * d| := le_abs_self _
    have h2 : |τ * a * d| = τ * (|a| * |d|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hτ0, mul_assoc]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - τ) hnn]
  have hprod : |a| * |d| ≤ ((n : ℝ) + 1) * bound * (1 / (10 * bound * ((n : ℝ) + 1) ^ 3)) :=
    mul_le_mul hmag hsep (abs_nonneg d) (mul_nonneg hn.le hbound.le)
  have hval : ((n : ℝ) + 1) * bound * (1 / (10 * bound * ((n : ℝ) + 1) ^ 3))
      = 1 / (10 * ((n : ℝ) + 1) ^ 2) := by
    field_simp
  rw [hval] at hprod
  linarith

@[blueprint "lem:hedged-round-bound"
  (statement := /-- Let $\Phi : \mathcal{X} \times \mathbb{R} \to \mathcal{F}$ be a feature
  map, let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $B \in \mathbb{R}$ with $B > 0$, let
  $t \in \mathbb{N}$ and let $\sigma : \mathbb{N} \to \{0,1\}$ record the history. Write
  $S_t$ for the score
  function of \cref{def:score-function}. Assume the hedged-case hypotheses of
  \cref{def:is-any-kernel-round}, namely
  \[
    S_t(q_t^{\sigma}(0))\,S_t(q_t^{\sigma}(1)) < 0, \qquad
    w_t^{\sigma}(0)
      = \frac{|S_t(q_t^{\sigma}(1))|}{|S_t(q_t^{\sigma}(0))| + |S_t(q_t^{\sigma}(1))|},
  \]
  \[
    |q_t^{\sigma}(0) - q_t^{\sigma}(1)| \leq \frac{1}{10 B (t+1)^3}, \qquad
    |S_t(q_t^{\sigma}(0))| \leq (t+1) B .
  \]
  Then, with the round expectation of \cref{def:round-expectation},
  \[
    \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}\bigl[S_t(p_t)(y_t^{\sigma} - p_t)\bigr]
      \leq \frac{1}{10 (t+1)^2}.
  \] -/)
  (proof := /-- Write $a = S_t(q_t^{\sigma}(0))$, $b = S_t(q_t^{\sigma}(1))$,
  $\tau = w_t^{\sigma}(0)$ and
  $\tau' = w_t^{\sigma}(1)$, so that $\tau + \tau' = 1$ and $\tau, \tau' \geq 0$ by
  \cref{def:any-kernel-transcript}. By \cref{def:round-expectation},
  \[
    \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}\bigl[S_t(p_t)(y_t^{\sigma} - p_t)\bigr]
      = \tau\, a\,(y_t^{\sigma} - q_t^{\sigma}(0))
        + \tau'\, b\,(y_t^{\sigma} - q_t^{\sigma}(1)),
  \]
  the same outcome $y_t^{\sigma}$ occurring at both atoms because, by
  \cref{def:any-kernel-transcript}, the outcome of round $t$ is a function of the history
  $\sigma$ alone and not of the prediction realised at round $t$.
  Since $ab < 0$ and $\tau = |b|/(|a| + |b|)$, \cref{lem:hedged-weight-cancellation} applied
  to $a$ and $b$ gives $\tau a + (1 - \tau) b = 0$, that is, $\tau a + \tau' b = 0$.
  Consequently \cref{lem:hedged-round-expectation-eq}, applied with $w_0 = \tau$,
  $w_1 = \tau'$, $y = y_t^{\sigma}$, $q_0 = q_t^{\sigma}(0)$ and $q_1 = q_t^{\sigma}(1)$,
  yields
  \[
    \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}\bigl[S_t(p_t)(y_t^{\sigma} - p_t)\bigr]
      = \tau\, a\, (q_t^{\sigma}(1) - q_t^{\sigma}(0)).
  \]
  Now $0 \leq \tau \leq 1$: indeed $\tau \geq 0$, and $\tau \leq 1$ follows from
  $\tau + \tau' = 1$ together with $\tau' \geq 0$.
  Put $d = q_t^{\sigma}(1) - q_t^{\sigma}(0)$. Since $|d| = |q_t^{\sigma}(0) -
  q_t^{\sigma}(1)|$, the assumed separation bound reads
  $|d| \leq 1/(10 B (t+1)^3)$, and the assumed magnitude bound reads $|a| \leq (t+1) B$.
  Therefore \cref{lem:hedged-product-magnitude-bound}, applied with this $a$ and $d$, with
  the weight $\tau$, with the magnitude parameter $B > 0$ and with $n = t$, gives
  \[
    \tau\, a\, d \leq \frac{1}{10 (t+1)^2} .
  \]
  Combining this with the displayed evaluation of the round expectation yields
  \[
    \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}\bigl[S_t(p_t)(y_t^{\sigma} - p_t)\bigr]
      \leq \frac{1}{10 (t+1)^2},
  \]
  which is the assertion. -/)
  (title := /-- Round Bound in the Hedged Case -/)
  (latexEnv := "lemma")]
lemma hedged_round_bound (Φ : X × ℝ → F) (tr : any_kernel_transcript X) (bound : ℝ)
    (t : ℕ) (σ : ℕ → Fin 2) (hbound : 0 < bound)
    (hopp : score_function Φ tr t σ (tr.candidate t σ 0) *
        score_function Φ tr t σ (tr.candidate t σ 1) < 0)
    (hweight : tr.weight t σ 0 =
        |score_function Φ tr t σ (tr.candidate t σ 1)| /
          (|score_function Φ tr t σ (tr.candidate t σ 0)| +
            |score_function Φ tr t σ (tr.candidate t σ 1)|))
    (hsep : |tr.candidate t σ 0 - tr.candidate t σ 1| ≤
        1 / (10 * bound * ((t : ℝ) + 1) ^ 3))
    (hmag : |score_function Φ tr t σ (tr.candidate t σ 0)| ≤ ((t : ℝ) + 1) * bound) :
    round_expectation tr t σ
        (fun i => score_function Φ tr t σ (tr.candidate t σ i) *
          (tr.outcome t σ - tr.candidate t σ i)) ≤ 1 / (10 * ((t : ℝ) + 1) ^ 2) := by
  have hw0 : 0 ≤ tr.weight t σ 0 := tr.weight_nonneg t σ 0
  have hw1 : 0 ≤ tr.weight t σ 1 := tr.weight_nonneg t σ 1
  have hsum : tr.weight t σ 0 + tr.weight t σ 1 = 1 := by
    have h := tr.weight_sum_one t σ
    simpa [Fin.sum_univ_two] using h
  have hcancel : tr.weight t σ 0 * score_function Φ tr t σ (tr.candidate t σ 0)
      + tr.weight t σ 1 * score_function Φ tr t σ (tr.candidate t σ 1) = 0 := by
    have h := hedged_weight_cancellation (score_function Φ tr t σ (tr.candidate t σ 0))
      (score_function Φ tr t σ (tr.candidate t σ 1)) hopp
    rw [hweight]
    have hw1' : tr.weight t σ 1 = 1 - |score_function Φ tr t σ (tr.candidate t σ 1)| /
        (|score_function Φ tr t σ (tr.candidate t σ 0)| +
          |score_function Φ tr t σ (tr.candidate t σ 1)|) := by
      rw [hweight] at hsum
      linarith
    rw [hw1']
    exact h
  have heq : round_expectation tr t σ
      (fun i => score_function Φ tr t σ (tr.candidate t σ i) *
        (tr.outcome t σ - tr.candidate t σ i))
      = tr.weight t σ 0 * score_function Φ tr t σ (tr.candidate t σ 0) *
        (tr.candidate t σ 1 - tr.candidate t σ 0) := by
    simp only [round_expectation, Fin.sum_univ_two]
    exact hedged_round_expectation_eq _ _ _ _ _ _ _ hcancel
  rw [heq]
  have hsep' : |tr.candidate t σ 1 - tr.candidate t σ 0| ≤
      1 / (10 * bound * ((t : ℝ) + 1) ^ 3) := by
    rwa [abs_sub_comm]
  exact hedged_product_magnitude_bound _ _ _ bound t hbound hw0 (by linarith)
    hmag hsep'

@[blueprint "lem:round-score-expectation-bound"
  (statement := /-- Let $\Phi : \mathcal{X} \times \mathbb{R} \to \mathcal{F}$ be a feature
  map, let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $B \in \mathbb{R}$, let $t \in \mathbb{N}$ and let
  $\sigma : \mathbb{N} \to \{0,1\}$ record the history. Assume that round $t$ along $\sigma$
  is an Any Kernel
  round with magnitude parameter $B$ in the sense of \cref{def:is-any-kernel-round}. Then,
  with $S_t$ the score function of \cref{def:score-function},
  \[
    \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}\bigl[S_t(p_t)(y_t^{\sigma} - p_t)\bigr]
      \leq \frac{1}{10 (t+1)^2}.
  \] -/)
  (proof := /-- By \cref{def:is-any-kernel-round} one of two alternatives holds.

  In the aligned case one has
  $\operatorname{sign} S_t(0) = \operatorname{sign} S_t(1) \neq 0$ and
  $q_t^{\sigma}(0) = q_t^{\sigma}(1) = \bigl(1 + \operatorname{sign} S_t(0)\bigr)/2 =: p$.
  Since
  $q_t^{\sigma}(0) = q_t^{\sigma}(1)$, the round expectation of
  \cref{def:round-expectation} collapses:
  \[
    \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}\bigl[S_t(p_t)(y_t^{\sigma} - p_t)\bigr]
      = \bigl(w_t^{\sigma}(0) + w_t^{\sigma}(1)\bigr) S_t(p)(y_t^{\sigma} - p)
      = S_t(p)(y_t^{\sigma} - p),
  \]
  using $w_t^{\sigma}(0) + w_t^{\sigma}(1) = 1$ from \cref{def:any-kernel-transcript}. The
  outcome $y_t^{\sigma}$ lies
  in $\{0,1\}$, again by \cref{def:any-kernel-transcript}, so
  \cref{lem:aligned-sign-round-nonpos} applied to the function $S_t$ and to
  $y = y_t^{\sigma}$ gives
  $S_t(p)(y_t^{\sigma} - p) \leq 0$. Since $(t+1)^2 > 0$, we have $0 \leq 1/(10(t+1)^2)$, and
  the asserted bound follows.

  In the hedged case, all five hypotheses of \cref{lem:hedged-round-bound} are exactly the
  clauses of the second alternative of \cref{def:is-any-kernel-round}, so that lemma applies
  verbatim and yields the asserted bound. -/)
  (title := /-- Uniform Round Bound on the Expected Score Product -/)
  (latexEnv := "lemma")]
lemma round_score_expectation_bound (Φ : X × ℝ → F) (tr : any_kernel_transcript X)
    (bound : ℝ) (t : ℕ) (σ : ℕ → Fin 2)
    (hround : is_any_kernel_round Φ tr bound t σ) :
    round_expectation tr t σ
        (fun i => score_function Φ tr t σ (tr.candidate t σ i) *
          (tr.outcome t σ - tr.candidate t σ i)) ≤ 1 / (10 * ((t : ℝ) + 1) ^ 2) := by
  have hRHS : (0 : ℝ) ≤ 1 / (10 * ((t : ℝ) + 1) ^ 2) := by positivity
  rcases hround with ⟨hsign, hne, hc0, hc1⟩ | ⟨hb, hopp, hw, hsep, hmag⟩
  · have hle := aligned_sign_round_nonpos (score_function Φ tr t σ) (tr.outcome t σ)
      (tr.outcome_mem_zero_one t σ) hsign hne
    have hsum : tr.weight t σ 0 + tr.weight t σ 1 = 1 := by
      simpa [Fin.sum_univ_two] using tr.weight_sum_one t σ
    have hval : round_expectation tr t σ
        (fun i => score_function Φ tr t σ (tr.candidate t σ i) *
          (tr.outcome t σ - tr.candidate t σ i))
        = score_function Φ tr t σ (tr.candidate t σ 0) *
            (tr.outcome t σ - tr.candidate t σ 0) := by
      simp only [round_expectation, Fin.sum_univ_two, hc1]
      linear_combination (score_function Φ tr t σ (tr.candidate t σ 0) *
        (tr.outcome t σ - tr.candidate t σ 0)) * hsum
    rw [hval, hc0]
    exact hle.trans hRHS
  · exact hedged_round_bound Φ tr bound t σ hb hopp hw hsep hmag

@[blueprint "lem:basel-shifted-partial-sum-le"
  (statement := /-- For every $T \in \mathbb{N}$,
  \[
    \sum_{t=0}^{T-1} \frac{1}{(t+1)^2} \leq \frac{\pi^2}{6} .
  \] -/)
  (proof := /-- Reindex the sum by $m = t+1$. Since the summand $m \mapsto 1/m^2$ is
  evaluated with the convention that division by zero yields zero, the term with $m = 0$
  vanishes, and therefore
  \[
    \sum_{t=0}^{T-1} \frac{1}{(t+1)^2} = \sum_{m=0}^{T} \frac{1}{m^2} .
  \]
  Every summand $1/m^2$ is nonnegative. By Euler's solution of the Basel problem the series
  $\sum_{m \geq 0} 1/m^2$ converges with sum $\pi^2/6$, and a finite partial sum of a
  convergent series with nonnegative terms is at most the total sum. Applying this to the
  index set $\{0,\dots,T\}$ bounds the right-hand side by $\pi^2/6$, which is the assertion. -/)
  (title := /-- Basel Bound for Shifted Inverse-Square Partial Sums -/)
  (latexEnv := "lemma")]
lemma basel_shifted_partial_sum_le (T : ℕ) :
    ∑ t ∈ Finset.range T, 1 / (((t : ℝ) + 1) ^ 2) ≤ Real.pi ^ 2 / 6 := by
  rw [show ∑ t ∈ Finset.range T, 1 / (((t : ℝ) + 1) ^ 2)
      = ∑ m ∈ Finset.range (T + 1), 1 / ((m : ℝ) ^ 2) by
    rw [Finset.sum_range_succ' (fun m => 1 / ((m : ℝ) ^ 2)) T]
    push_cast
    simp]
  exact sum_le_hasSum (Finset.range (T + 1)) (fun i _ => by positivity) hasSum_zeta_two

@[blueprint "lem:pi-sq-le-thirty"
  (statement := /-- The real number $\pi$ satisfies $\pi^2 \leq 30$. -/)
  (proof := /-- The constant $\pi$ is positive and satisfies $\pi \leq 4$. Multiplying the
  inequality $\pi \leq 4$ by the nonnegative number $\pi$ gives $\pi^2 \leq 4\pi \leq 16$,
  and $16 \leq 30$, whence $\pi^2 \leq 30$. -/)
  (title := /-- Crude Upper Bound for the Square of Pi -/)
  (latexEnv := "lemma")]
lemma pi_sq_le_thirty : Real.pi ^ 2 ≤ 30 := by
  nlinarith [Real.pi_le_four, Real.pi_pos]

@[blueprint "lem:basel-partial-sum-bound"
  (statement := /-- For every $T \in \mathbb{N}$,
  \[
    2 \sum_{t=0}^{T-1} \frac{1}{10 (t+1)^2} \leq 1 .
  \] -/)
  (proof := /-- For each $t$ one has $1/(10(t+1)^2) = (1/10)\cdot 1/(t+1)^2$, so summing this
  identity termwise over $t \in \{0,\dots,T-1\}$ and pulling the constant factor out of the
  finite sum gives
  \[
    \sum_{t=0}^{T-1} \frac{1}{10 (t+1)^2}
      = \frac{1}{10}\sum_{t=0}^{T-1} \frac{1}{(t+1)^2} .
  \]
  By \cref{lem:basel-shifted-partial-sum-le} the remaining sum is at most $\pi^2/6$, hence
  \[
    2 \sum_{t=0}^{T-1} \frac{1}{10 (t+1)^2}
      = \frac{1}{5}\sum_{t=0}^{T-1} \frac{1}{(t+1)^2}
      \leq \frac{1}{5}\cdot\frac{\pi^2}{6} = \frac{\pi^2}{30},
  \]
  where the first inequality uses that $1/5 > 0$. Finally $\pi^2 \leq 30$ by
  \cref{lem:pi-sq-le-thirty}, so $\pi^2/30 \leq 1$, which gives the asserted bound. -/)
  (title := /-- Basel Bound for the Accumulated Round Errors -/)
  (latexEnv := "lemma")]
lemma basel_partial_sum_bound (T : ℕ) :
    2 * ∑ t ∈ Finset.range T, 1 / (10 * ((t : ℝ) + 1) ^ 2) ≤ 1 := by
  have hscale : ∑ t ∈ Finset.range T, 1 / (10 * ((t : ℝ) + 1) ^ 2)
      = (1 / 10) * ∑ t ∈ Finset.range T, 1 / (((t : ℝ) + 1) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [← one_div_mul_one_div]
  rw [hscale]
  linarith [basel_shifted_partial_sum_le T, pi_sq_le_thirty]

@[blueprint "lem:selector-extension-snoc"
  (statement := /-- Let $T \in \mathbb{N}$, let $\rho : \{0,\dots,T-1\} \to \{0,1\}$ be a
  selector for horizon $T$ and let $i \in \{0,1\}$. Write $(\rho, i)$ for the selector for
  horizon $T+1$ that agrees with $\rho$ at every index $s < T$ and takes the value $i$ at the
  index $T$. Then the extension of $(\rho, i)$ in the sense of
  \cref{def:selector-extension} satisfies
  \[
    \overline{(\rho, i)}(s) = \bar\rho(s) \quad \text{for every } s < T,
    \qquad \overline{(\rho, i)}(T) = i .
  \] -/)
  (proof := /-- Both assertions are read off from \cref{def:selector-extension}. Let $s < T$.
  Then also $s < T + 1$, so the extension of $(\rho, i)$ at $s$ is the value of $(\rho, i)$ at
  the index $s$ of $\{0, \dots, T\}$, which is $\rho(s)$ by the definition of $(\rho,i)$,
  while the extension of $\rho$ at $s$ is $\rho(s)$ as well; the two agree. For the second
  assertion, $T < T + 1$, so the extension of $(\rho, i)$ at $T$ is the value of $(\rho, i)$
  at the index $T$ of $\{0,\dots,T\}$, which is $i$ by the definition of $(\rho, i)$. -/)
  (title := /-- Extension of a Selector with an Appended Value -/)
  (latexEnv := "lemma")]
lemma selector_extension_snoc (T : ℕ) (ρ : Fin T → Fin 2) (i : Fin 2) :
    (∀ s : ℕ, s < T →
        selector_extension (T + 1) (Fin.snoc ρ i) s = selector_extension T ρ s) ∧
      selector_extension (T + 1) (Fin.snoc ρ i) T = i := by
  refine ⟨fun s hs => ?_, ?_⟩
  · simp only [selector_extension, dif_pos hs, dif_pos (Nat.lt_succ_of_lt hs)]
    exact Fin.snoc_castSucc (α := fun _ => Fin 2) i ρ ⟨s, hs⟩
  · simp only [selector_extension, dif_pos (Nat.lt_succ_self T)]
    exact Fin.snoc_last (α := fun _ => Fin 2) i ρ

@[blueprint "lem:trajectory-weight-snoc"
  (statement := /-- Let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $T \in \mathbb{N}$, let
  $\rho : \{0,\dots,T-1\} \to \{0,1\}$ be a selector for horizon $T$ and let $i \in \{0,1\}$.
  Write $(\rho, i)$ for the selector for horizon $T+1$ that agrees with $\rho$ below $T$ and
  takes the value $i$ at $T$. Then the trajectory weights of \cref{def:trajectory-weight}
  satisfy
  \[
    W_{T+1}\bigl((\rho, i)\bigr) = W_T(\rho)\, w_T^{\bar\rho}(i) .
  \] -/)
  (proof := /-- By \cref{def:trajectory-weight} the left-hand side is the product over
  $t < T+1$ of the factors
  $w_t^{\overline{(\rho,i)}}\bigl(\overline{(\rho,i)}(t)\bigr)$; splitting off the factor
  indexed by $t = T$ it equals
  \[
    \Bigl(\prod_{t=0}^{T-1}
        w_t^{\overline{(\rho,i)}}\bigl(\overline{(\rho,i)}(t)\bigr)\Bigr)
      \cdot w_T^{\overline{(\rho,i)}}\bigl(\overline{(\rho,i)}(T)\bigr) .
  \]
  By \cref{lem:selector-extension-snoc} the extensions $\overline{(\rho,i)}$ and $\bar\rho$
  agree at every index $s < T$.

  Fix $t < T$. Then every $s < t$ satisfies $s < T$, so the two extensions agree below $t$,
  and since $u \mapsto w_t^{u}$ is history-local at $t$ by
  \cref{def:any-kernel-transcript}, in the sense of \cref{def:history-local}, we get
  $w_t^{\overline{(\rho,i)}} = w_t^{\bar\rho}$; moreover
  $\overline{(\rho,i)}(t) = \bar\rho(t)$ by \cref{lem:selector-extension-snoc}. Hence the
  factor indexed by $t$ equals $w_t^{\bar\rho}\bigl(\bar\rho(t)\bigr)$, and the product of
  these factors over $t < T$ is $W_T(\rho)$ by \cref{def:trajectory-weight}.

  For the remaining factor, the two extensions agree at every $s < T$, so history-locality of
  $u \mapsto w_T^{u}$ at $T$ gives $w_T^{\overline{(\rho,i)}} = w_T^{\bar\rho}$, while
  $\overline{(\rho,i)}(T) = i$ by \cref{lem:selector-extension-snoc}; the factor is therefore
  $w_T^{\bar\rho}(i)$. Multiplying the two contributions gives the claimed identity. -/)
  (title := /-- Factorisation of a Trajectory Weight at the Last Round -/)
  (latexEnv := "lemma")]
lemma trajectory_weight_snoc (tr : any_kernel_transcript X) (T : ℕ) (ρ : Fin T → Fin 2)
    (i : Fin 2) :
    trajectory_weight tr (T + 1) (Fin.snoc ρ i)
      = trajectory_weight tr T ρ * tr.weight T (selector_extension T ρ) i := by
  obtain ⟨hlt, hlast⟩ := selector_extension_snoc T ρ i
  rw [trajectory_weight, trajectory_weight, Finset.prod_range_succ]
  congr 1
  · refine Finset.prod_congr rfl fun t ht => ?_
    have htT : t < T := Finset.mem_range.mp ht
    have hw : tr.weight t (selector_extension (T + 1) (Fin.snoc ρ i))
        = tr.weight t (selector_extension T ρ) :=
      tr.weight_history_local t _ _ fun s hs => hlt s (hs.trans htT)
    rw [hw, hlt t htT]
  · have hw : tr.weight T (selector_extension (T + 1) (Fin.snoc ρ i))
        = tr.weight T (selector_extension T ρ) :=
      tr.weight_history_local T _ _ fun s hs => hlt s hs
    rw [hw, hlast]

@[blueprint "lem:sum-over-selectors-snoc"
  (statement := /-- Let $T \in \mathbb{N}$ and let $f$ assign a real number to each selector
  for horizon $T+1$, in the sense of \cref{def:selector-extension}. Writing $(\rho, i)$ for
  the selector for horizon $T+1$ that agrees with the selector $\rho$ for horizon $T$ below
  $T$ and takes the value $i$ at $T$, one has
  \[
    \sum_{\sigma : \{0,\dots,T\} \to \{0,1\}} f(\sigma)
      = \sum_{\rho : \{0,\dots,T-1\} \to \{0,1\}} \sum_{i \in \{0,1\}} f\bigl((\rho, i)\bigr).
  \] -/)
  (proof := /-- The assignment $(i, \rho) \mapsto (\rho, i)$ is a bijection from
  $\{0,1\} \times \bigl(\{0,\dots,T-1\} \to \{0,1\}\bigr)$ onto the selectors
  $\{0,\dots,T\} \to \{0,1\}$: its inverse sends $\sigma$ to the pair consisting of
  $\sigma(T)$ and the restriction of $\sigma$ to $\{0,\dots,T-1\}$. Reindexing the finite sum
  on the left along this bijection therefore gives
  $\sum_{i}\sum_{\rho} f\bigl((\rho,i)\bigr)$, after writing the sum over the product of the
  two index sets as an iterated sum. Interchanging the two finite sums, which is legitimate
  because both index sets are finite, yields the asserted identity. -/)
  (title := /-- Splitting a Sum over Selectors at the Last Round -/)
  (latexEnv := "lemma")]
lemma sum_over_selectors_snoc (T : ℕ) (f : (Fin (T + 1) → Fin 2) → ℝ) :
    ∑ σ : Fin (T + 1) → Fin 2, f σ
      = ∑ ρ : Fin T → Fin 2, ∑ i : Fin 2, f (Fin.snoc ρ i) := by
  rw [← Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (T + 1) => Fin 2) f,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp [Fin.snocEquiv]

@[blueprint "lem:trajectory-weight-nonneg-and-sum"
  (statement := /-- Let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript} and let $T \in \mathbb{N}$. Then the trajectory weights of
  \cref{def:trajectory-weight} form a probability vector on the set of selectors: for every
  selector $\sigma : \{0,\dots,T-1\} \to \{0,1\}$ one has $W_T(\sigma) \geq 0$, and
  \[
    \sum_{\sigma : \{0,\dots,T-1\} \to \{0,1\}} W_T(\sigma) = 1 .
  \] -/)
  (proof := /-- Nonnegativity is immediate: $W_T(\sigma)$ is by
  \cref{def:trajectory-weight} a finite product of the numbers
  $w_t^{\bar\sigma}(\bar\sigma(t))$ for $t < T$, each of which is nonnegative by
  \cref{def:any-kernel-transcript}, and a product of nonnegative reals is nonnegative.

  For the total mass we argue by induction on $T$. For $T = 0$ there is exactly one selector,
  the empty one, and its weight is the empty product, equal to $1$; the sum is therefore $1$.
  Assume the identity for $T$, and write $(\rho, i)$ for the selector on $\{0,\dots,T\}$ that
  agrees with the selector $\rho$ on $\{0,\dots,T-1\}$ below $T$ and takes the value
  $i \in \{0,1\}$ at $T$. Splitting the sum over the selectors on $\{0,\dots,T\}$ according to
  this decomposition, which is legitimate by \cref{lem:sum-over-selectors-snoc}, and then
  factorising each summand by \cref{lem:trajectory-weight-snoc}, we obtain
  \[
    \sum_{\text{selectors on } \{0,\dots,T\}} W_{T+1}
      = \sum_{\rho}\sum_{i \in \{0,1\}} W_{T+1}\bigl((\rho, i)\bigr)
      = \sum_{\rho}\sum_{i \in \{0,1\}} W_T(\rho)\, w_T^{\bar\rho}(i)
      = \sum_{\rho} W_T(\rho) \Bigl(\sum_{i \in \{0,1\}} w_T^{\bar\rho}(i)\Bigr)
      = \sum_{\rho} W_T(\rho) = 1,
  \]
  where the third equality pulls the factor $W_T(\rho)$, which does not depend on $i$, out of
  the inner sum, the fourth uses the normalisation
  $w_T^{\bar\rho}(0) + w_T^{\bar\rho}(1) = 1$ of
  \cref{def:any-kernel-transcript}, valid at every history $\bar\rho$, and the last is the
  induction hypothesis. This completes the induction and the proof. -/)
  (title := /-- Trajectory Weights Form a Probability Vector -/)
  (latexEnv := "lemma")]
lemma trajectory_weight_nonneg_and_sum (tr : any_kernel_transcript X) (T : ℕ) :
    (∀ σ : Fin T → Fin 2, 0 ≤ trajectory_weight tr T σ) ∧
      ∑ σ : Fin T → Fin 2, trajectory_weight tr T σ = 1 := by
  refine ⟨fun σ => Finset.prod_nonneg fun t _ => tr.weight_nonneg t _ _, ?_⟩
  induction T with
  | zero => simp [trajectory_weight]
  | succ T ih =>
      rw [sum_over_selectors_snoc T (trajectory_weight tr (T + 1))]
      have hstep : ∀ ρ : Fin T → Fin 2,
          ∑ i : Fin 2, trajectory_weight tr (T + 1) (Fin.snoc ρ i)
            = trajectory_weight tr T ρ := by
        intro ρ
        rw [Finset.sum_congr rfl fun i _ => trajectory_weight_snoc tr T ρ i,
          ← Finset.mul_sum, tr.weight_sum_one, mul_one]
      rw [Finset.sum_congr rfl fun ρ _ => hstep ρ]
      exact ih

@[blueprint "lem:sum-over-selectors-succ"
  (statement := /-- Let $T \in \mathbb{N}$ and let $f$ assign a real number to every selector
  $\sigma : \{0, \dots, T\} \to \{0,1\}$ for horizon $T+1$. Writing $(\rho, i)$ for the
  selector that restricts to $\rho : \{0, \dots, T-1\} \to \{0,1\}$ and takes the value
  $i \in \{0,1\}$ at $T$, we have
  \[
    \sum_{\sigma : \{0,\dots,T\} \to \{0,1\}} f(\sigma)
      = \sum_{\rho : \{0,\dots,T-1\} \to \{0,1\}} \sum_{i \in \{0,1\}} f\bigl((\rho,i)\bigr).
  \] -/)
  (proof := /-- The map $(\rho, i) \mapsto (\rho, i)$, sending a pair consisting of a selector
  for horizon $T$ and an element of $\{0,1\}$ to the selector for horizon $T+1$ obtained by
  prolonging $\rho$ by the value $i$ at $T$, is a bijection from
  $\bigl(\{0,\dots,T-1\} \to \{0,1\}\bigr) \times \{0,1\}$ onto
  $\bigl(\{0,\dots,T\} \to \{0,1\}\bigr)$: its inverse sends $\sigma$ to the pair consisting
  of the restriction of $\sigma$ to $\{0,\dots,T-1\}$ and the value $\sigma(T)$. Reindexing
  the sum on the left along this bijection therefore gives
  \[
    \sum_{\sigma} f(\sigma) = \sum_{(\rho, i)} f\bigl((\rho,i)\bigr),
  \]
  the sum on the right ranging over the product set, and writing that sum over the product
  set as the iterated sum, first over $\rho$ and then over $i \in \{0,1\}$, yields the
  assertion. -/)
  (title := /-- Selectors for One More Round Split Off the Final Coordinate -/)
  (latexEnv := "lemma")]
lemma sum_over_selectors_succ (T : ℕ) (f : (Fin (T + 1) → Fin 2) → ℝ) :
    ∑ σ : Fin (T + 1) → Fin 2, f σ =
      ∑ ρ : Fin T → Fin 2, ∑ i : Fin 2, f (Fin.snoc ρ i) := by
  rw [← (Fin.snocEquiv (fun _ => Fin 2)).sum_comp f, Fintype.sum_prod_type_right]
  simp [Fin.snocEquiv]

@[blueprint "lem:horizon-expectation-drop-last"
  (statement := /-- Let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $T \in \mathbb{N}$, and let
  $G : (\mathbb{N} \to \{0,1\}) \to \mathbb{R}$ be history-local at $T$ in the sense of
  \cref{def:history-local}, that is, $G(\sigma)$ depends only on the coordinates
  $\sigma(0), \dots, \sigma(T-1)$. Then, with the expectation of
  \cref{def:horizon-expectation},
  \[
    \mathbb{E}_{T+1}\, G = \mathbb{E}_T\, G .
  \] -/)
  (proof := /-- Every selector $\sigma : \{0, \dots, T\} \to \{0,1\}$ is uniquely determined
  by its restriction $\rho : \{0,\dots,T-1\} \to \{0,1\}$ together with its value
  $i = \sigma(T) \in \{0,1\}$; write $\sigma = (\rho, i)$ for that selector.

  By \cref{def:horizon-expectation} the left-hand side is
  $\sum_{\sigma} W_{T+1}(\sigma)\, G\bigl(\bar\sigma\bigr)$, the sum ranging over all
  selectors $\sigma$ for horizon $T+1$. Applying \cref{lem:sum-over-selectors-succ} to the
  function $\sigma \mapsto W_{T+1}(\sigma)\, G(\bar\sigma)$ rewrites this as the iterated sum
  \[
    \mathbb{E}_{T+1}\, G
      = \sum_{\rho} \sum_{i \in \{0,1\}}
          W_{T+1}\bigl((\rho,i)\bigr)\, G\bigl(\overline{(\rho,i)}\bigr),
  \]
  in which $\rho$ ranges over the selectors for horizon $T$ and $i$ over $\{0,1\}$. It
  therefore suffices to prove, for each fixed $\rho$, that the inner sum over $i$ equals
  $W_T(\rho)\, G(\bar\rho)$.

  Fix $\rho$ and $i \in \{0,1\}$. The extensions $\overline{(\rho,i)}$ and $\bar\rho$ of
  \cref{def:selector-extension} agree at every coordinate $s < T$ by
  \cref{lem:selector-extension-snoc}; since $G$ is history-local at $T$ in the sense of
  \cref{def:history-local}, this gives $G\bigl(\overline{(\rho,i)}\bigr) = G(\bar\rho)$.
  Furthermore \cref{lem:trajectory-weight-snoc} gives the factorisation
  $W_{T+1}\bigl((\rho,i)\bigr) = W_T(\rho)\, w_T^{\bar\rho}(i)$ of the trajectory weight of
  \cref{def:trajectory-weight}. Multiplying these two identities and rearranging the
  resulting product of real numbers, each summand becomes
  \[
    W_{T+1}\bigl((\rho,i)\bigr)\, G\bigl(\overline{(\rho,i)}\bigr)
      = w_T^{\bar\rho}(i)\,\bigl(W_T(\rho)\, G(\bar\rho)\bigr).
  \]
  Summing over $i \in \{0,1\}$ and taking the factor $W_T(\rho)\, G(\bar\rho)$, which does
  not depend on $i$, out of the sum, the inner sum equals
  $\bigl(\sum_{i \in \{0,1\}} w_T^{\bar\rho}(i)\bigr)\, W_T(\rho)\, G(\bar\rho)$. The
  normalisation $\sum_{i \in \{0,1\}} w_T^{\bar\rho}(i) = 1$ of
  \cref{def:any-kernel-transcript}, valid at every history, reduces this to
  $W_T(\rho)\, G(\bar\rho)$. Summing over $\rho$ and using
  \cref{def:horizon-expectation} once more yields
  $\mathbb{E}_{T+1}\, G = \sum_{\rho} W_T(\rho)\, G(\bar\rho) = \mathbb{E}_T\, G$, which is
  the assertion. -/)
  (title := /-- Marginalisation of the Final Coordinate -/)
  (latexEnv := "lemma")]
lemma horizon_expectation_drop_last (tr : any_kernel_transcript X) (T : ℕ)
    (G : (ℕ → Fin 2) → ℝ) (hG : history_local T G) :
    horizon_expectation tr (T + 1) G = horizon_expectation tr T G := by
  unfold horizon_expectation
  rw [sum_over_selectors_succ T
    (fun σ => trajectory_weight tr (T + 1) σ * G (selector_extension (T + 1) σ))]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hGval : ∀ i : Fin 2,
      G (selector_extension (T + 1) (Fin.snoc ρ i)) = G (selector_extension T ρ) := by
    intro i
    exact hG _ _ fun s hs => (selector_extension_snoc T ρ i).1 s hs
  have hsum : ∀ i : Fin 2,
      trajectory_weight tr (T + 1) (Fin.snoc ρ i) *
          G (selector_extension (T + 1) (Fin.snoc ρ i)) =
        tr.weight T (selector_extension T ρ) i *
          (trajectory_weight tr T ρ * G (selector_extension T ρ)) := by
    intro i
    rw [trajectory_weight_snoc tr T ρ i, hGval i]
    ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hsum i, ← Finset.sum_mul,
    tr.weight_sum_one T (selector_extension T ρ), one_mul]

@[blueprint "lem:horizon-expectation-tower-last"
  (statement := /-- Let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $T \in \mathbb{N}$, and let $g$ assign to every
  selection $\sigma : \mathbb{N} \to \{0,1\}$ a function
  $g^{\sigma} : \{0,1\} \to \mathbb{R}$, in such a way that $\sigma \mapsto g^{\sigma}$ is
  history-local at $T$ in the sense of \cref{def:history-local}. Then, with the expectations
  of \cref{def:horizon-expectation} and \cref{def:round-expectation},
  \[
    \mathbb{E}_{T+1}\bigl[\, \sigma \mapsto g^{\sigma}(\sigma(T)) \bigr]
      = \mathbb{E}_{T+1}\bigl[\, \sigma \mapsto
          \mathbb{E}_{p_T \sim \Delta_T^{\sigma}}\, g^{\sigma} \bigr] .
  \] -/)
  (proof := /-- Every selector $\sigma : \{0,\dots,T\} \to \{0,1\}$ is uniquely determined by
  its restriction $\rho : \{0,\dots,T-1\} \to \{0,1\}$ together with its value
  $i = \sigma(T) \in \{0,1\}$; write $\sigma = (\rho, i)$ for that selector.

  By \cref{def:horizon-expectation} both sides of the assertion are sums over all selectors
  for horizon $T+1$: the left-hand side is
  $\sum_{\sigma} W_{T+1}(\sigma)\, g^{\bar\sigma}\bigl(\bar\sigma(T)\bigr)$ and the
  right-hand side is
  $\sum_{\sigma} W_{T+1}(\sigma)\, \mathbb{E}_{p_T \sim \Delta_T^{\bar\sigma}} g^{\bar\sigma}$,
  with $W_{T+1}$ the trajectory weight of \cref{def:trajectory-weight} and $\bar\sigma$ the
  extension of \cref{def:selector-extension}. Applying
  \cref{lem:sum-over-selectors-succ} to each of the two summands rewrites both sides as
  iterated sums, first over the selectors $\rho$ for horizon $T$ and then over
  $i \in \{0,1\}$. It therefore suffices to prove, for each fixed $\rho$, that the two inner
  sums over $i$ agree.

  Fix $\rho$. By \cref{lem:selector-extension-snoc} the extensions $\overline{(\rho,i)}$ and
  $\bar\rho$ agree at every coordinate $s < T$, for both values of $i$. Since
  $\sigma \mapsto g^{\sigma}$ is history-local at $T$ by hypothesis, this gives
  $g^{\overline{(\rho,i)}} = g^{\bar\rho}$; since $u \mapsto w_T^{u}$ is history-local at $T$
  by \cref{def:any-kernel-transcript}, it gives likewise
  $w_T^{\overline{(\rho,i)}} = w_T^{\bar\rho}$.

  For the left-hand inner sum, \cref{lem:trajectory-weight-snoc} gives the factorisation
  $W_{T+1}\bigl((\rho,i)\bigr) = W_T(\rho)\, w_T^{\bar\rho}(i)$, and
  \cref{lem:selector-extension-snoc} gives $\overline{(\rho,i)}(T) = i$, so each summand
  equals $W_T(\rho)\,\bigl(w_T^{\bar\rho}(i)\, g^{\bar\rho}(i)\bigr)$ after rearranging the
  product of real numbers. Taking the factor $W_T(\rho)$, which does not depend on $i$, out of
  the sum, the left-hand inner sum equals
  \[
    W_T(\rho) \sum_{i \in \{0,1\}} w_T^{\bar\rho}(i)\, g^{\bar\rho}(i)
      = W_T(\rho)\, \mathbb{E}_{p_T \sim \Delta_T^{\bar\rho}} g^{\bar\rho},
  \]
  the last step being \cref{def:round-expectation}.

  For the right-hand inner sum, expanding both round-$T$ expectations by
  \cref{def:round-expectation} and using the same factorisation
  $W_{T+1}\bigl((\rho,i)\bigr) = W_T(\rho)\, w_T^{\bar\rho}(i)$ of
  \cref{lem:trajectory-weight-snoc}, each summand equals
  $w_T^{\bar\rho}(i)\,\bigl(W_T(\rho)\, \mathbb{E}_{p_T \sim \Delta_T^{\bar\rho}}
  g^{\bar\rho}\bigr)$, again after rearranging the product of real numbers. Taking the factor
  $W_T(\rho)\, \mathbb{E}_{p_T \sim \Delta_T^{\bar\rho}} g^{\bar\rho}$, which does not depend
  on $i$, out of the sum, the right-hand inner sum equals
  $\bigl(\sum_{i \in \{0,1\}} w_T^{\bar\rho}(i)\bigr)\, W_T(\rho)\,
  \mathbb{E}_{p_T \sim \Delta_T^{\bar\rho}} g^{\bar\rho}$, and the normalisation
  $\sum_{i \in \{0,1\}} w_T^{\bar\rho}(i) = 1$ of \cref{def:any-kernel-transcript}, valid at
  every history, reduces it to
  $W_T(\rho)\, \mathbb{E}_{p_T \sim \Delta_T^{\bar\rho}} g^{\bar\rho}$.

  The two inner sums have thus been shown to have the common value
  $W_T(\rho)\, \mathbb{E}_{p_T \sim \Delta_T^{\bar\rho}} g^{\bar\rho}$, so they agree for
  every $\rho$, which is the assertion. -/)
  (title := /-- Tower Property at the Final Round -/)
  (latexEnv := "lemma")]
lemma horizon_expectation_tower_last (tr : any_kernel_transcript X) (T : ℕ)
    (g : (ℕ → Fin 2) → Fin 2 → ℝ) (hg : history_local T g) :
    horizon_expectation tr (T + 1) (fun σ => g σ (σ T)) =
      horizon_expectation tr (T + 1) (fun σ => round_expectation tr T σ (g σ)) := by
  unfold horizon_expectation
  rw [sum_over_selectors_succ T
      (fun σ => trajectory_weight tr (T + 1) σ *
        g (selector_extension (T + 1) σ) (selector_extension (T + 1) σ T)),
    sum_over_selectors_succ T
      (fun σ => trajectory_weight tr (T + 1) σ *
        round_expectation tr T (selector_extension (T + 1) σ)
          (g (selector_extension (T + 1) σ)))]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hgval : ∀ i : Fin 2,
      g (selector_extension (T + 1) (Fin.snoc ρ i)) = g (selector_extension T ρ) := fun i =>
    hg _ _ fun s hs => (selector_extension_snoc T ρ i).1 s hs
  have hwval : ∀ i : Fin 2,
      tr.weight T (selector_extension (T + 1) (Fin.snoc ρ i))
        = tr.weight T (selector_extension T ρ) := fun i =>
    tr.weight_history_local T _ _ fun s hs => (selector_extension_snoc T ρ i).1 s hs
  have hL : ∀ i : Fin 2,
      trajectory_weight tr (T + 1) (Fin.snoc ρ i) *
          g (selector_extension (T + 1) (Fin.snoc ρ i))
            (selector_extension (T + 1) (Fin.snoc ρ i) T)
        = trajectory_weight tr T ρ *
            (tr.weight T (selector_extension T ρ) i * g (selector_extension T ρ) i) := by
    intro i
    rw [trajectory_weight_snoc tr T ρ i, hgval i, (selector_extension_snoc T ρ i).2]
    ring
  have hR : ∀ i : Fin 2,
      trajectory_weight tr (T + 1) (Fin.snoc ρ i) *
          round_expectation tr T (selector_extension (T + 1) (Fin.snoc ρ i))
            (g (selector_extension (T + 1) (Fin.snoc ρ i)))
        = tr.weight T (selector_extension T ρ) i *
            (trajectory_weight tr T ρ *
              round_expectation tr T (selector_extension T ρ)
                (g (selector_extension T ρ))) := by
    intro i
    rw [trajectory_weight_snoc tr T ρ i, round_expectation, round_expectation, hgval i, hwval i]
    ring
  have hLsum : ∑ i : Fin 2,
      trajectory_weight tr (T + 1) (Fin.snoc ρ i) *
          g (selector_extension (T + 1) (Fin.snoc ρ i))
            (selector_extension (T + 1) (Fin.snoc ρ i) T)
        = trajectory_weight tr T ρ *
            round_expectation tr T (selector_extension T ρ) (g (selector_extension T ρ)) := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hL i, ← Finset.mul_sum]
    rfl
  have hRsum : ∑ i : Fin 2,
      trajectory_weight tr (T + 1) (Fin.snoc ρ i) *
          round_expectation tr T (selector_extension (T + 1) (Fin.snoc ρ i))
            (g (selector_extension (T + 1) (Fin.snoc ρ i)))
        = trajectory_weight tr T ρ *
            round_expectation tr T (selector_extension T ρ) (g (selector_extension T ρ)) := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hR i, ← Finset.sum_mul,
      tr.weight_sum_one T (selector_extension T ρ), one_mul]
  rw [hLsum, hRsum]

@[blueprint "lem:history-local-of-le"
  (statement := /-- Let $\alpha$ be a type, let $t, T \in \mathbb{N}$ satisfy $t \leq T$, and
  let $G$ assign an element of $\alpha$ to every selection $\sigma : \mathbb{N} \to \{0,1\}$.
  If $G$ is history-local at $t$ in the sense of \cref{def:history-local}, then $G$ is
  history-local at $T$. -/)
  (proof := /-- Let $\sigma, \tau : \mathbb{N} \to \{0,1\}$ be selections with
  $\sigma(s) = \tau(s)$ for every $s < T$; by \cref{def:history-local} it suffices to deduce
  $G(\sigma) = G(\tau)$. Every $s < t$ satisfies $s < t \leq T$ and hence $s < T$, so the
  assumed agreement below $T$ gives $\sigma(s) = \tau(s)$ for every $s < t$. History-locality
  of $G$ at $t$, again in the sense of \cref{def:history-local}, applied to this agreement,
  yields $G(\sigma) = G(\tau)$, as required. -/)
  (title := /-- History-Locality is Inherited by Later Rounds -/)
  (latexEnv := "lemma")]
lemma history_local_of_le {α : Type*} (t T : ℕ) (htT : t ≤ T) (G : (ℕ → Fin 2) → α)
    (hG : history_local t G) : history_local T G := by
  intro σ τ h
  exact hG σ τ fun s hs => h s (lt_of_lt_of_le hs htT)

@[blueprint "lem:history-local-eval-at-round"
  (statement := /-- Let $t \in \mathbb{N}$ and let $g$ assign to every selection
  $\sigma : \mathbb{N} \to \{0,1\}$ a function $g^{\sigma} : \{0,1\} \to \mathbb{R}$, in such
  a way that $\sigma \mapsto g^{\sigma}$ is history-local at $t$ in the sense of
  \cref{def:history-local}. Then the real-valued map
  $\sigma \mapsto g^{\sigma}\bigl(\sigma(t)\bigr)$ is history-local at $t + 1$. -/)
  (proof := /-- Let $\sigma, \tau : \mathbb{N} \to \{0,1\}$ be selections with
  $\sigma(s) = \tau(s)$ for every $s < t + 1$; by \cref{def:history-local} it suffices to
  deduce $g^{\sigma}\bigl(\sigma(t)\bigr) = g^{\tau}\bigl(\tau(t)\bigr)$. Every $s < t$
  satisfies $s < t + 1$, so the assumed agreement gives $\sigma(s) = \tau(s)$ for every
  $s < t$, and history-locality of $\sigma \mapsto g^{\sigma}$ at $t$ in the sense of
  \cref{def:history-local} therefore gives $g^{\sigma} = g^{\tau}$. Taking $s = t$, which
  satisfies $t < t + 1$, the same agreement gives $\sigma(t) = \tau(t)$. Substituting these
  two equalities into $g^{\sigma}\bigl(\sigma(t)\bigr)$ yields
  $g^{\tau}\bigl(\tau(t)\bigr)$, as required. -/)
  (title := /-- History-Locality of the Value Realised at Round $t$ -/)
  (latexEnv := "lemma")]
lemma history_local_eval_at_round (t : ℕ) (g : (ℕ → Fin 2) → Fin 2 → ℝ)
    (hg : history_local t g) : history_local (t + 1) (fun σ => g σ (σ t)) := by
  intro σ τ h
  show g σ (σ t) = g τ (τ t)
  rw [hg σ τ fun s hs => h s (Nat.lt_succ_of_lt hs), h t (Nat.lt_succ_self t)]

@[blueprint "lem:history-local-round-expectation"
  (statement := /-- Let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $t \in \mathbb{N}$, and let $g$ assign to every
  selection $\sigma : \mathbb{N} \to \{0,1\}$ a function $g^{\sigma} : \{0,1\} \to \mathbb{R}$,
  in such a way that $\sigma \mapsto g^{\sigma}$ is history-local at $t$ in the sense of
  \cref{def:history-local}. Then the map
  $\sigma \mapsto \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}\, g^{\sigma}$ of
  \cref{def:round-expectation} is history-local at $t$. -/)
  (proof := /-- Let $\sigma, \tau : \mathbb{N} \to \{0,1\}$ be selections with
  $\sigma(s) = \tau(s)$ for every $s < t$; by \cref{def:history-local} it suffices to deduce
  $\mathbb{E}_{p_t \sim \Delta_t^{\sigma}}\, g^{\sigma}
    = \mathbb{E}_{p_t \sim \Delta_t^{\tau}}\, g^{\tau}$. By \cref{def:round-expectation} the
  left-hand side is $\sum_{i \in \{0,1\}} w_t^{\sigma}(i)\, g^{\sigma}(i)$ and the right-hand
  side is $\sum_{i \in \{0,1\}} w_t^{\tau}(i)\, g^{\tau}(i)$. History-locality of
  $\sigma \mapsto g^{\sigma}$ at $t$, applied to the assumed agreement below $t$, gives
  $g^{\sigma} = g^{\tau}$, and history-locality of $\sigma \mapsto w_t^{\sigma}$ at $t$,
  which is part of \cref{def:any-kernel-transcript}, applied to the same agreement, gives
  $w_t^{\sigma} = w_t^{\tau}$. Substituting these two equalities of functions on $\{0,1\}$
  into the first sum turns it into the second, which is the required identity. -/)
  (title := /-- History-Locality of the Round-$t$ Expectation -/)
  (latexEnv := "lemma")]
lemma history_local_round_expectation (tr : any_kernel_transcript X) (t : ℕ)
    (g : (ℕ → Fin 2) → Fin 2 → ℝ) (hg : history_local t g) :
    history_local t (fun σ => round_expectation tr t σ (g σ)) := by
  intro σ τ h
  show round_expectation tr t σ (g σ) = round_expectation tr t τ (g τ)
  unfold round_expectation
  rw [hg σ τ h, tr.weight_history_local t σ τ h]

@[blueprint "lem:horizon-expectation-tower"
  (statement := /-- Let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $T \in \mathbb{N}$, let $t < T$, and let $g$ assign
  to every selection $\sigma : \mathbb{N} \to \{0,1\}$ a function
  $g^{\sigma} : \{0,1\} \to \mathbb{R}$, in such a way that $\sigma \mapsto g^{\sigma}$ is
  history-local at $t$ in the sense of \cref{def:history-local}. Then, with the expectations
  of \cref{def:horizon-expectation} and \cref{def:round-expectation},
  \[
    \mathbb{E}_T\bigl[\, \sigma \mapsto g^{\sigma}(\sigma(t)) \bigr]
      = \mathbb{E}_T\bigl[\, \sigma \mapsto
          \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}\, g^{\sigma} \bigr] .
  \]
  This is the tower property of the trajectory expectation at the single round $t$: averaging
  the realised value $g^{\sigma}(\sigma(t))$ over all trajectories is the same as first
  averaging over the round-$t$ draw, at each history, and then over the trajectory. -/)
  (proof := /-- Fix the round $t$ and the function $g$, history-local at $t$, and argue by
  induction on the horizon $T$, the assertion for a given $T$ being the implication: if
  $t < T$, then the displayed identity holds at the horizon $T$. Throughout write
  $G_1 : \sigma \mapsto g^{\sigma}(\sigma(t))$ and
  $G_2 : \sigma \mapsto \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}\, g^{\sigma}$ for the two
  integrands, so that the assertion at the horizon $T$ reads
  $\mathbb{E}_T\, G_1 = \mathbb{E}_T\, G_2$.

  For $T = 0$ the hypothesis $t < 0$ is impossible, so the implication holds vacuously.

  Let now $T = T' + 1$ and assume the implication at the horizon $T'$. Let $t < T' + 1$.
  Then either $t < T'$ or $t = T'$.

  Suppose first $t < T'$. The map $G_1$ is history-local at $t + 1$ by
  \cref{lem:history-local-eval-at-round}, applied to $g$, and $t + 1 \leq T'$ because
  $t < T'$, so \cref{lem:history-local-of-le} shows that $G_1$ is history-local at $T'$.
  Likewise $G_2$ is history-local at $t$ by \cref{lem:history-local-round-expectation},
  applied to the transcript and to $g$, and $t \leq T'$, so \cref{lem:history-local-of-le}
  shows that $G_2$ too is history-local at $T'$. Applying
  \cref{lem:horizon-expectation-drop-last} to $G_1$ and to $G_2$ at the horizon $T'$
  therefore gives $\mathbb{E}_{T'+1} G_1 = \mathbb{E}_{T'} G_1$ and
  $\mathbb{E}_{T'+1} G_2 = \mathbb{E}_{T'} G_2$; rewriting both sides of the goal by these two
  identities reduces the assertion at the horizon $T' + 1$ to
  $\mathbb{E}_{T'} G_1 = \mathbb{E}_{T'} G_2$, which is exactly the induction hypothesis
  applied to $t < T'$.

  Suppose finally $t = T'$. Substituting $T' = t$, the assertion to be proved is
  $\mathbb{E}_{t+1} G_1 = \mathbb{E}_{t+1} G_2$, which is
  \cref{lem:horizon-expectation-tower-last} applied to the transcript, to the round $t$ and
  to $g$, the latter being history-local at $t$ by hypothesis. This completes the
  induction. -/)
  (title := /-- Tower Property of the Trajectory Expectation at One Round -/)
  (latexEnv := "lemma")]
lemma horizon_expectation_tower (tr : any_kernel_transcript X) (T t : ℕ) (ht : t < T)
    (g : (ℕ → Fin 2) → Fin 2 → ℝ) (hg : history_local t g) :
    horizon_expectation tr T (fun σ => g σ (σ t)) =
      horizon_expectation tr T (fun σ => round_expectation tr t σ (g σ)) := by
  revert ht
  induction T with
  | zero =>
    intro ht
    exact absurd ht (Nat.not_lt_zero t)
  | succ T' ih =>
    intro ht
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | heq
    · rw [horizon_expectation_drop_last tr T' (fun σ => g σ (σ t))
        (history_local_of_le (t + 1) T' hlt _ (history_local_eval_at_round t g hg)),
        horizon_expectation_drop_last tr T' (fun σ => round_expectation tr t σ (g σ))
          (history_local_of_le t T' hlt.le _ (history_local_round_expectation tr t g hg))]
      exact ih hlt
    · subst heq
      exact horizon_expectation_tower_last tr t g hg

@[blueprint "lem:horizon-expectation-round-sum"
  (statement := /-- Let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $T \in \mathbb{N}$, and for each $t \in \mathbb{N}$
  let $g_t$ assign to every selection $\sigma : \mathbb{N} \to \{0,1\}$ a function
  $g_t^{\sigma} : \{0,1\} \to \mathbb{R}$, in such a way that $\sigma \mapsto g_t^{\sigma}$
  is history-local at $t$ in the sense of \cref{def:history-local}. Then, with the
  expectations of \cref{def:horizon-expectation} and \cref{def:round-expectation},
  \[
    \mathbb{E}_T\Bigl[\, \sigma \mapsto \sum_{t=0}^{T-1} g_t^{\sigma}(\sigma(t)) \Bigr]
      = \sum_{t=0}^{T-1} \mathbb{E}_T\Bigl[\, \sigma \mapsto
        \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}\, g_t^{\sigma} \Bigr] .
  \]
  For an adaptive transcript the inner expectation must remain under the trajectory
  expectation, because the distribution $\Delta_t^{\sigma}$ itself depends on the realised
  history; when every $\Delta_t^{\sigma}$ is independent of $\sigma$ the right-hand side
  collapses to $\sum_{t<T} \mathbb{E}_{p_t \sim \Delta_t} g_t$. -/)
  (proof := /-- By \cref{def:horizon-expectation} the horizon-$T$ expectation is a finite
  weighted sum, hence additive in its integrand, so
  \[
    \mathbb{E}_T\Bigl[\, \sigma \mapsto \sum_{t=0}^{T-1} g_t^{\sigma}(\sigma(t)) \Bigr]
      = \sum_{t=0}^{T-1}
        \mathbb{E}_T\bigl[\, \sigma \mapsto g_t^{\sigma}(\sigma(t)) \bigr],
  \]
  the interchange being that of two finite sums. Fix $t < T$. The map
  $\sigma \mapsto g_t^{\sigma}$ is history-local at $t$ by hypothesis, so
  \cref{lem:horizon-expectation-tower} applies at the round $t$ and gives
  \[
    \mathbb{E}_T\bigl[\, \sigma \mapsto g_t^{\sigma}(\sigma(t)) \bigr]
      = \mathbb{E}_T\bigl[\, \sigma \mapsto
          \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}\, g_t^{\sigma} \bigr].
  \]
  Substituting this identity for each $t < T$ into the previous display yields the
  assertion. -/)
  (title := /-- Marginalisation of a Sum of Single-Round Functions -/)
  (latexEnv := "lemma")]
lemma horizon_expectation_round_sum (tr : any_kernel_transcript X) (T : ℕ)
    (g : ℕ → (ℕ → Fin 2) → Fin 2 → ℝ) (hg : ∀ t : ℕ, history_local t (g t)) :
    horizon_expectation tr T (fun σ => ∑ t ∈ Finset.range T, g t σ (σ t)) =
      ∑ t ∈ Finset.range T,
        horizon_expectation tr T (fun σ => round_expectation tr t σ (g t σ)) := by
  have h1 : horizon_expectation tr T (fun σ => ∑ t ∈ Finset.range T, g t σ (σ t))
      = ∑ t ∈ Finset.range T, horizon_expectation tr T (fun σ => g t σ (σ t)) := by
    simp only [horizon_expectation, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [h1]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_range] at ht
  exact horizon_expectation_tower tr T t ht (g t) (hg t)

@[blueprint "lem:weighted-mean-le-sqrt-weighted-mean-sq"
  (statement := /-- Let $\iota$ be a finite index set, let $w : \iota \to \mathbb{R}$ satisfy
  $w_i \geq 0$ for every $i \in \iota$ and $\sum_{i \in \iota} w_i = 1$, and let
  $g : \iota \to \mathbb{R}$ satisfy $g_i \geq 0$ for every $i \in \iota$. Then
  \[
    \sum_{i \in \iota} w_i g_i \leq \sqrt{\sum_{i \in \iota} w_i g_i^2} .
  \] -/)
  (proof := /-- Write $A = \sum_{i} w_i g_i$ and $Q = \sum_{i} w_i g_i^2$, both sums being
  finite. Each summand $w_i g_i$ is a product of two nonnegative reals, hence nonnegative, so
  $A \geq 0$; likewise $w_i g_i^2 \geq 0$ for every $i$, since $g_i^2 \geq 0$, so $Q \geq 0$.
  Because $A \geq 0$ and $Q \geq 0$, the assertion $A \leq \sqrt{Q}$ is equivalent to
  $A^2 \leq Q$.

  To prove $A^2 \leq Q$ we use the Cauchy--Schwarz inequality for finite sums in the form
  \[
    \Bigl(\sum_{i} r_i\Bigr)^2 \leq \Bigl(\sum_{i} f_i\Bigr)\Bigl(\sum_{i} h_i\Bigr),
  \]
  valid for real families with $f_i \geq 0$, $h_i \geq 0$ and $r_i^2 \leq f_i h_i$ for every
  $i$. Take $r_i = w_i g_i$, $f_i = w_i$ and $h_i = w_i g_i^2$. Then $f_i \geq 0$ by
  hypothesis on $w$, and $h_i \geq 0$ as a product of the nonnegative numbers $w_i$ and
  $g_i^2$, while
  \[
    r_i^2 = (w_i g_i)^2 = w_i^2 g_i^2 = w_i \cdot \bigl(w_i g_i^2\bigr) = f_i h_i ,
  \]
  so the required inequality $r_i^2 \leq f_i h_i$ holds with equality. The conclusion of
  Cauchy--Schwarz therefore reads $A^2 \leq \bigl(\sum_{i} w_i\bigr) Q$, and the normalisation
  $\sum_{i} w_i = 1$ turns the right-hand side into $Q$. Hence $A^2 \leq Q$, and the
  equivalence recorded above yields $A \leq \sqrt{Q}$, as asserted. -/)
  (title := /-- Weighted Mean is Bounded by the Root of the Weighted Mean of Squares -/)
  (latexEnv := "lemma")]
lemma weighted_mean_le_sqrt_weighted_mean_sq {ι : Type*} [Fintype ι] (w g : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hg : ∀ i, 0 ≤ g i) :
    ∑ i, w i * g i ≤ Real.sqrt (∑ i, w i * g i ^ 2) := by
  have hA : 0 ≤ ∑ i, w i * g i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hg i)
  have hQ : 0 ≤ ∑ i, w i * g i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  rw [Real.le_sqrt hA hQ]
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset ι)
    (r := fun i => w i * g i) (f := w) (g := fun i => w i * g i ^ 2)
    (fun i _ => hw i) (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
    (fun i _ => le_of_eq (by ring))
  rw [hsum, one_mul] at hcs
  exact hcs

@[blueprint "lem:horizon-expectation-sqrt-jensen"
  (statement := /-- Let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $T \in \mathbb{N}$, and let
  $G : (\mathbb{N} \to \{0,1\}) \to \mathbb{R}$ satisfy $G \geq 0$ pointwise. Then, with the
  expectation of \cref{def:horizon-expectation},
  \[
    \mathbb{E}_T\, G \leq \sqrt{\mathbb{E}_T\bigl[G^2\bigr]} .
  \] -/)
  (proof := /-- Write $W_T(\sigma)$ for the trajectory weights of
  \cref{def:trajectory-weight}. By \cref{lem:trajectory-weight-nonneg-and-sum} these are
  nonnegative, $W_T(\sigma) \geq 0$ for every selector
  $\sigma : \{0,\dots,T-1\} \to \{0,1\}$, and they sum to $1$, that is
  $\sum_{\sigma} W_T(\sigma) = 1$. By \cref{def:horizon-expectation} the two sides of the
  assertion are the finite sums
  \[
    \mathbb{E}_T\, G = \sum_{\sigma} W_T(\sigma)\, G(\bar\sigma),
    \qquad
    \mathbb{E}_T\bigl[G^2\bigr] = \sum_{\sigma} W_T(\sigma)\, G(\bar\sigma)^2,
  \]
  the index set being the finite set of selectors and $\bar\sigma$ the extension of
  \cref{def:selector-extension}. Setting $w_{\sigma} = W_T(\sigma)$ and
  $g_{\sigma} = G(\bar\sigma)$, the family $w$ is nonnegative with total mass $1$ by the two
  facts just recorded, and $g$ is nonnegative because $G \geq 0$ pointwise, in particular at
  every extended selector $\bar\sigma$. Thus
  \cref{lem:weighted-mean-le-sqrt-weighted-mean-sq} applies to $w$ and $g$ and gives
  \[
    \sum_{\sigma} W_T(\sigma)\, G(\bar\sigma)
      \leq \sqrt{\sum_{\sigma} W_T(\sigma)\, G(\bar\sigma)^2},
  \]
  which is exactly $\mathbb{E}_T\,G \leq \sqrt{\mathbb{E}_T[G^2]}$, as asserted. -/)
  (title := /-- Jensen Inequality for the Trajectory Expectation -/)
  (latexEnv := "lemma")]
lemma horizon_expectation_sqrt_jensen (tr : any_kernel_transcript X) (T : ℕ)
    (G : (ℕ → Fin 2) → ℝ) (hG : ∀ σ, 0 ≤ G σ) :
    horizon_expectation tr T G ≤
      Real.sqrt (horizon_expectation tr T (fun σ => G σ ^ 2)) := by
  obtain ⟨hnonneg, hsum⟩ := trajectory_weight_nonneg_and_sum tr T
  simpa [horizon_expectation] using
    weighted_mean_le_sqrt_weighted_mean_sq (trajectory_weight tr T)
      (fun σ => G (selector_extension T σ)) hnonneg hsum
      (fun σ => hG (selector_extension T σ))

@[blueprint "lem:horizon-expectation-add-const-mul"
  (statement := /-- Let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $T \in \mathbb{N}$, let $f, g$ assign a real number
  to each selection $\sigma : \mathbb{N} \to \{0,1\}$ and let $c \in \mathbb{R}$. Then, with
  the expectation of \cref{def:horizon-expectation},
  \[
    \mathbb{E}_T\bigl[\, \sigma \mapsto f(\sigma) + c\, g(\sigma) \bigr]
      = \mathbb{E}_T[f] + c\, \mathbb{E}_T[g] .
  \] -/)
  (proof := /-- By \cref{def:horizon-expectation} each horizon-$T$ expectation is the finite
  sum $\sum_{\sigma} W_T(\sigma)\,(\cdot)$ over the $2^T$ selectors, with $W_T$ the trajectory
  weight. Evaluating the integrand $\sigma \mapsto f(\sigma) + c\, g(\sigma)$ gives
  $\mathbb{E}_T[f + c\, g] = \sum_{\sigma} W_T(\sigma)\bigl(f(\bar\sigma) + c\, g(\bar\sigma)\bigr)$.
  Since multiplication distributes over addition in $\mathbb{R}$, each summand equals
  $W_T(\sigma)\, f(\bar\sigma) + c\,\bigl(W_T(\sigma)\, g(\bar\sigma)\bigr)$; splitting the
  finite sum into two and extracting the constant factor $c$ from the second one yields
  $\sum_{\sigma} W_T(\sigma)\, f(\bar\sigma) + c \sum_{\sigma} W_T(\sigma)\, g(\bar\sigma)
    = \mathbb{E}_T[f] + c\, \mathbb{E}_T[g]$. -/)
  (title := /-- Linearity of the Trajectory Expectation -/)
  (latexEnv := "lemma")]
lemma horizon_expectation_add_const_mul (tr : any_kernel_transcript X) (T : ℕ)
    (f g : (ℕ → Fin 2) → ℝ) (c : ℝ) :
    horizon_expectation tr T (fun σ => f σ + c * g σ) =
      horizon_expectation tr T f + c * horizon_expectation tr T g := by
  simp only [horizon_expectation]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  ring

@[blueprint "lem:horizon-expectation-le-const"
  (statement := /-- Let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $T \in \mathbb{N}$, let $c \in \mathbb{R}$ and let
  $f$ assign a real number to each selection $\sigma : \mathbb{N} \to \{0,1\}$. If
  $f(\sigma) \leq c$ for every $\sigma$, then, with the expectation of
  \cref{def:horizon-expectation}, $\mathbb{E}_T[f] \leq c$. -/)
  (proof := /-- By \cref{lem:trajectory-weight-nonneg-and-sum} the trajectory weights satisfy
  $W_T(\sigma) \geq 0$ for every selector $\sigma$ and $\sum_{\sigma} W_T(\sigma) = 1$. By
  \cref{def:horizon-expectation}, $\mathbb{E}_T[f] = \sum_{\sigma} W_T(\sigma)\, f(\bar\sigma)$.
  Applying the hypothesis $f(\bar\sigma) \leq c$ together with $W_T(\sigma) \geq 0$ to each
  summand gives $\mathbb{E}_T[f] \leq \sum_{\sigma} W_T(\sigma)\, c
    = \bigl(\sum_{\sigma} W_T(\sigma)\bigr) c = c$, the last equality being the normalisation
  $\sum_{\sigma} W_T(\sigma) = 1$. -/)
  (title := /-- Constant Upper Bound for the Trajectory Expectation -/)
  (latexEnv := "lemma")]
lemma horizon_expectation_le_const (tr : any_kernel_transcript X) (T : ℕ)
    (f : (ℕ → Fin 2) → ℝ) (c : ℝ) (hf : ∀ σ : ℕ → Fin 2, f σ ≤ c) :
    horizon_expectation tr T f ≤ c := by
  obtain ⟨hnonneg, hsum⟩ := trajectory_weight_nonneg_and_sum tr T
  have hconst : horizon_expectation tr T (fun _ : ℕ → Fin 2 => c) = c := by
    simp only [horizon_expectation]
    rw [← Finset.sum_mul, hsum, one_mul]
  calc horizon_expectation tr T f
      ≤ horizon_expectation tr T (fun _ : ℕ → Fin 2 => c) := by
        simp only [horizon_expectation]
        exact Finset.sum_le_sum fun ρ _ =>
          mul_le_mul_of_nonneg_left (hf _) (hnonneg ρ)
    _ = c := hconst

@[blueprint "lem:score-function-history-local"
  (statement := /-- Let $\Phi : \mathcal{X} \times \mathbb{R} \to \mathcal{F}$ be a feature
  map, let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $t \in \mathbb{N}$ and let
  $\sigma, \tau : \mathbb{N} \to \{0,1\}$ satisfy $\sigma(s) = \tau(s)$ for every $s < t$.
  Then, with $S_t$ the score function of \cref{def:score-function}, $S_t^{\sigma}(p)
    = S_t^{\tau}(p)$ for every $p \in \mathbb{R}$; equivalently $\sigma \mapsto S_t^{\sigma}$
  is history-local at $t$ in the sense of \cref{def:history-local}. -/)
  (proof := /-- By \cref{def:score-function},
  $S_t^{\sigma}(p) = \sum_{s<t} k\bigl((x_t^{\sigma},p),(x_s^{\sigma},p_s^{\sigma})\bigr)
    (y_s^{\sigma} - p_s^{\sigma}) + \tfrac12 k\bigl((x_t^{\sigma},p),(x_t^{\sigma},p)\bigr)
    (1-2p)$, where $p_s^{\sigma} = q_s^{\sigma}(\sigma(s))$, and likewise for $\tau$. The
  feature satisfies $x_t^{\sigma} = x_t^{\tau}$, because $\sigma \mapsto x_t^{\sigma}$ is
  history-local at $t$ by \cref{def:any-kernel-transcript} and $\sigma, \tau$ agree below
  $t$; this makes the final term and the first kernel argument of every summand coincide.
  Fix $s < t$. Every $r < s$ satisfies $r < t$, so $\sigma$ and $\tau$ agree below $s$; hence
  $x_s^{\sigma} = x_s^{\tau}$, $q_s^{\sigma} = q_s^{\tau}$ and $y_s^{\sigma} = y_s^{\tau}$,
  all three maps being history-local at $s$ by \cref{def:any-kernel-transcript}. Finally
  $\sigma(s) = \tau(s)$ since $s < t$, so
  $p_s^{\sigma} = q_s^{\sigma}(\sigma(s)) = q_s^{\tau}(\tau(s)) = p_s^{\tau}$. Substituting
  these equalities term by term identifies the two sums, whence $S_t^{\sigma}(p)
    = S_t^{\tau}(p)$. -/)
  (title := /-- History-Locality of the Score Function -/)
  (latexEnv := "lemma")]
lemma score_function_history_local (Φ : X × ℝ → F) (tr : any_kernel_transcript X)
    (t : ℕ) (σ τ : ℕ → Fin 2) (h : ∀ s, s < t → σ s = τ s) (p : ℝ) :
    score_function Φ tr t σ p = score_function Φ tr t τ p := by
  unfold score_function
  rw [tr.feature_history_local t σ τ h]
  congr 1
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  have hle : ∀ r, r < s → σ r = τ r := fun r hr => h r (hr.trans hs)
  rw [tr.feature_history_local s σ τ hle, tr.candidate_history_local s σ τ hle,
    tr.outcome_history_local s σ τ hle, h s hs]

@[blueprint "lem:history-local-variance-summand"
  (statement := /-- Let $\Phi : \mathcal{X} \times \mathbb{R} \to \mathcal{F}$ be a feature
  map with associated kernel $k$ as in \cref{def:kernel-of-feature-map}, let
  $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript} and let $t \in \mathbb{N}$. The family assigning to each
  selection $\sigma : \mathbb{N} \to \{0,1\}$ the function
  $i \mapsto q_t^{\sigma}(i)\bigl(1 - q_t^{\sigma}(i)\bigr)\,
    k\bigl((x_t^{\sigma}, q_t^{\sigma}(i)),(x_t^{\sigma}, q_t^{\sigma}(i))\bigr)$ on $\{0,1\}$
  is history-local at $t$ in the sense of \cref{def:history-local}. -/)
  (proof := /-- Let $\sigma, \tau : \mathbb{N} \to \{0,1\}$ agree at every coordinate $s < t$.
  Both $\sigma \mapsto q_t^{\sigma}$ and $\sigma \mapsto x_t^{\sigma}$ are history-local at $t$
  by \cref{def:any-kernel-transcript}, so $q_t^{\sigma} = q_t^{\tau}$ and
  $x_t^{\sigma} = x_t^{\tau}$. The displayed function depends on $\sigma$ only through
  $q_t^{\sigma}$ and $x_t^{\sigma}$, so substituting these two equalities makes the value at
  each $i \in \{0,1\}$ coincide; hence the two functions on $\{0,1\}$ are equal. -/)
  (title := /-- History-Locality of the Round Variance Summand -/)
  (latexEnv := "lemma")]
lemma history_local_variance_summand (Φ : X × ℝ → F) (tr : any_kernel_transcript X)
    (t : ℕ) :
    history_local t (fun σ => fun i : Fin 2 =>
      tr.candidate t σ i * (1 - tr.candidate t σ i) *
        kernel_of_feature_map Φ (tr.feature t σ, tr.candidate t σ i)
          (tr.feature t σ, tr.candidate t σ i)) := by
  intro σ τ h
  funext i
  dsimp only
  rw [tr.candidate_history_local t σ τ h, tr.feature_history_local t σ τ h]

@[blueprint "lem:history-local-score-summand"
  (statement := /-- Let $\Phi : \mathcal{X} \times \mathbb{R} \to \mathcal{F}$ be a feature
  map, let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript} and let $t \in \mathbb{N}$. The family assigning to each
  selection $\sigma : \mathbb{N} \to \{0,1\}$ the function
  $i \mapsto S_t^{\sigma}\bigl(q_t^{\sigma}(i)\bigr)\bigl(y_t^{\sigma} - q_t^{\sigma}(i)\bigr)$
  on $\{0,1\}$, with $S_t$ the score function of \cref{def:score-function}, is history-local
  at $t$ in the sense of \cref{def:history-local}. -/)
  (proof := /-- Let $\sigma, \tau : \mathbb{N} \to \{0,1\}$ agree at every coordinate $s < t$.
  The maps $\sigma \mapsto q_t^{\sigma}$ and $\sigma \mapsto y_t^{\sigma}$ are history-local
  at $t$ by \cref{def:any-kernel-transcript}, so $q_t^{\sigma} = q_t^{\tau}$ and
  $y_t^{\sigma} = y_t^{\tau}$; and $S_t^{\sigma}(p) = S_t^{\tau}(p)$ for every $p$ by
  \cref{lem:score-function-history-local}. Fix $i \in \{0,1\}$. Then
  $q_t^{\sigma}(i) = q_t^{\tau}(i)$ and $y_t^{\sigma} = y_t^{\tau}$, and
  $S_t^{\sigma}\bigl(q_t^{\tau}(i)\bigr) = S_t^{\tau}\bigl(q_t^{\tau}(i)\bigr)$; substituting
  these equalities gives
  $S_t^{\sigma}(q_t^{\sigma}(i))(y_t^{\sigma} - q_t^{\sigma}(i))
    = S_t^{\tau}(q_t^{\tau}(i))(y_t^{\tau} - q_t^{\tau}(i))$, so the two functions on
  $\{0,1\}$ agree. -/)
  (title := /-- History-Locality of the Round Score Summand -/)
  (latexEnv := "lemma")]
lemma history_local_score_summand (Φ : X × ℝ → F) (tr : any_kernel_transcript X)
    (t : ℕ) :
    history_local t (fun σ => fun i : Fin 2 =>
      score_function Φ tr t σ (tr.candidate t σ i) *
        (tr.outcome t σ - tr.candidate t σ i)) := by
  intro σ τ h
  funext i
  dsimp only
  rw [tr.candidate_history_local t σ τ h, tr.outcome_history_local t σ τ h,
    score_function_history_local Φ tr t σ τ h (tr.candidate t τ i)]

@[blueprint "lem:expected-norm-sq-bound"
  (statement := /-- Let $\Phi : \mathcal{X} \times \mathbb{R} \to \mathcal{F}$ be a feature
  map with associated kernel $k$, let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the
  sense of \cref{def:any-kernel-transcript}, let $B \in \mathbb{R}$ and let
  $T \in \mathbb{N}$. Assume that for every round $t < T$ and every
  selection $\sigma : \mathbb{N} \to \{0,1\}$, round $t$ at the history $\sigma$ is an Any
  Kernel round with
  magnitude parameter $B$ in the sense of \cref{def:is-any-kernel-round}. Then, with the
  feature regret vector of \cref{def:feature-regret-vector},
  \[
    \mathbb{E}_T\Bigl[\,\|V_T\|_{\mathcal{F}}^2\Bigr]
      \leq \sum_{t=0}^{T-1} \mathbb{E}_T\Bigl[\, \sigma \mapsto
            \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}
            \bigl[p_t(1-p_t)
              k\bigl((x_t^{\sigma},p_t),(x_t^{\sigma},p_t)\bigr)\bigr]\Bigr] + 1 .
  \] -/)
  (proof := /-- Fix a selector and apply
  \cref{lem:feature-regret-norm-sq-eq-variance-add-score}: for every
  $\sigma : \mathbb{N} \to \{0,1\}$,
  \[
    \|V_T(\sigma)\|_{\mathcal{F}}^2
      = \sum_{t=0}^{T-1} p_t(1-p_t) k\bigl((x_t^{\sigma},p_t),(x_t^{\sigma},p_t)\bigr)
        + 2\sum_{t=0}^{T-1} S_t(p_t)(y_t^{\sigma} - p_t),
  \]
  where $p_t = q_t^{\sigma}(\sigma(t))$. Taking the horizon-$T$ expectation of both sides and
  applying the linearity of \cref{lem:horizon-expectation-add-const-mul} with the constant
  factor $2$, we obtain
  \[
    \mathbb{E}_T\bigl[\|V_T\|^2_{\mathcal{F}}\bigr]
      = \mathbb{E}_T\Bigl[\sum_{t<T} p_t(1-p_t)
          k\bigl((x_t^{\sigma},p_t),(x_t^{\sigma},p_t)\bigr)\Bigr]
        + 2\, \mathbb{E}_T\Bigl[\sum_{t<T} S_t(p_t)(y_t^{\sigma}-p_t)\Bigr].
  \]
  For the first summand, the family
  $g_t^{\sigma}(i) = q_t^{\sigma}(i)\bigl(1 - q_t^{\sigma}(i)\bigr)
    k\bigl((x_t^{\sigma}, q_t^{\sigma}(i)),(x_t^{\sigma},q_t^{\sigma}(i))\bigr)$
  is history-local at $t$ for each $t$ by \cref{lem:history-local-variance-summand}. Hence
  \cref{lem:horizon-expectation-round-sum} applies and converts
  the first summand into
  $\sum_{t<T} \mathbb{E}_T\bigl[\sigma \mapsto
    \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}[p_t(1-p_t)
      k((x_t^{\sigma},p_t),(x_t^{\sigma},p_t))]\bigr]$, which is
  the first term of the asserted bound.

  For the second summand, the family
  $h_t^{\sigma}(i) = S_t(q_t^{\sigma}(i))\bigl(y_t^{\sigma} - q_t^{\sigma}(i)\bigr)$ is likewise
  history-local at $t$ by \cref{lem:history-local-score-summand}. So
  \cref{lem:horizon-expectation-round-sum} gives
  \[
    \mathbb{E}_T\Bigl[\sum_{t<T} S_t(p_t)(y_t^{\sigma}-p_t)\Bigr]
      = \sum_{t=0}^{T-1} \mathbb{E}_T\Bigl[\, \sigma \mapsto
        \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}\bigl[S_t(p_t)(y_t^{\sigma}-p_t)\bigr]\Bigr].
  \]
  Fix $t < T$. By hypothesis round $t$ is an Any Kernel round with magnitude parameter $B$ at
  every history $\sigma$, so \cref{lem:round-score-expectation-bound} bounds the integrand
  $\mathbb{E}_{p_t \sim \Delta_t^{\sigma}}[S_t(p_t)(y_t^{\sigma}-p_t)]$ by $1/(10(t+1)^2)$ for every
  $\sigma$. By \cref{lem:horizon-expectation-le-const} the horizon expectation of a function
  bounded above by a constant is bounded above by that same constant; therefore each term of
  the last display is at most $1/(10(t+1)^2)$ and
  \[
    2\, \mathbb{E}_T\Bigl[\sum_{t<T} S_t(p_t)(y_t^{\sigma}-p_t)\Bigr]
      \leq 2 \sum_{t=0}^{T-1} \frac{1}{10 (t+1)^2},
  \]
  and \cref{lem:basel-partial-sum-bound} bounds the right-hand side by $1$. Adding the two
  estimates gives the assertion. -/)
  (title := /-- Bound on the Expected Squared Feature Regret -/)
  (latexEnv := "lemma")]
lemma expected_norm_sq_bound (Φ : X × ℝ → F) (tr : any_kernel_transcript X)
    (bound : ℝ) (T : ℕ)
    (hrounds : ∀ t ∈ Finset.range T, ∀ σ : ℕ → Fin 2,
      is_any_kernel_round Φ tr bound t σ) :
    horizon_expectation tr T (fun σ => ‖feature_regret_vector Φ tr T σ‖ ^ 2) ≤
      (∑ t ∈ Finset.range T,
          horizon_expectation tr T (fun σ =>
            round_expectation tr t σ (fun i =>
              tr.candidate t σ i * (1 - tr.candidate t σ i) *
                kernel_of_feature_map Φ (tr.feature t σ, tr.candidate t σ i)
                  (tr.feature t σ, tr.candidate t σ i)))) + 1 := by
  have hV : horizon_expectation tr T (fun σ => ∑ t ∈ Finset.range T,
        tr.candidate t σ (σ t) * (1 - tr.candidate t σ (σ t)) *
          kernel_of_feature_map Φ (tr.feature t σ, tr.candidate t σ (σ t))
            (tr.feature t σ, tr.candidate t σ (σ t)))
      = ∑ t ∈ Finset.range T, horizon_expectation tr T (fun σ =>
          round_expectation tr t σ (fun i =>
            tr.candidate t σ i * (1 - tr.candidate t σ i) *
              kernel_of_feature_map Φ (tr.feature t σ, tr.candidate t σ i)
                (tr.feature t σ, tr.candidate t σ i))) :=
    horizon_expectation_round_sum tr T
      (fun t σ i => tr.candidate t σ i * (1 - tr.candidate t σ i) *
        kernel_of_feature_map Φ (tr.feature t σ, tr.candidate t σ i)
          (tr.feature t σ, tr.candidate t σ i))
      (fun t => history_local_variance_summand Φ tr t)
  have hS : horizon_expectation tr T (fun σ => ∑ t ∈ Finset.range T,
        score_function Φ tr t σ (tr.candidate t σ (σ t)) *
          (tr.outcome t σ - tr.candidate t σ (σ t)))
      = ∑ t ∈ Finset.range T, horizon_expectation tr T (fun σ =>
          round_expectation tr t σ (fun i =>
            score_function Φ tr t σ (tr.candidate t σ i) *
              (tr.outcome t σ - tr.candidate t σ i))) :=
    horizon_expectation_round_sum tr T
      (fun t σ i => score_function Φ tr t σ (tr.candidate t σ i) *
        (tr.outcome t σ - tr.candidate t σ i))
      (fun t => history_local_score_summand Φ tr t)
  have hsplit : horizon_expectation tr T (fun σ => ‖feature_regret_vector Φ tr T σ‖ ^ 2)
      = horizon_expectation tr T (fun σ =>
          (∑ t ∈ Finset.range T,
            tr.candidate t σ (σ t) * (1 - tr.candidate t σ (σ t)) *
              kernel_of_feature_map Φ (tr.feature t σ, tr.candidate t σ (σ t))
                (tr.feature t σ, tr.candidate t σ (σ t)))
          + 2 * ∑ t ∈ Finset.range T,
              score_function Φ tr t σ (tr.candidate t σ (σ t)) *
                (tr.outcome t σ - tr.candidate t σ (σ t))) := by
    congr 1
    funext σ
    exact feature_regret_norm_sq_eq_variance_add_score Φ tr T σ
  rw [hsplit, horizon_expectation_add_const_mul, hV, hS]
  have hbound2 : 2 * ∑ t ∈ Finset.range T, horizon_expectation tr T (fun σ =>
        round_expectation tr t σ (fun i =>
          score_function Φ tr t σ (tr.candidate t σ i) *
            (tr.outcome t σ - tr.candidate t σ i))) ≤ 1 := by
    have hstep : (∑ t ∈ Finset.range T, horizon_expectation tr T (fun σ =>
          round_expectation tr t σ (fun i =>
            score_function Φ tr t σ (tr.candidate t σ i) *
              (tr.outcome t σ - tr.candidate t σ i))))
        ≤ ∑ t ∈ Finset.range T, 1 / (10 * ((t : ℝ) + 1) ^ 2) := by
      refine Finset.sum_le_sum fun t ht => ?_
      refine horizon_expectation_le_const tr T _ _ fun σ => ?_
      exact round_score_expectation_bound Φ tr bound t σ (hrounds t ht σ)
    have hbasel := basel_partial_sum_bound T
    linarith [hstep, hbasel]
  linarith [hbound2]

@[blueprint "lem:expected-feature-regret-bound"
  (statement := /-- Let $\Phi : \mathcal{X} \times \mathbb{R} \to \mathcal{F}$ be a feature
  map with associated kernel $k$, let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the
  sense of \cref{def:any-kernel-transcript}, let $B \in \mathbb{R}$ and let
  $T \in \mathbb{N}$. Assume that for every round $t < T$ and every
  selection $\sigma : \mathbb{N} \to \{0,1\}$, round $t$ at the history $\sigma$ is an Any
  Kernel round with magnitude parameter $B$ in the sense of
  \cref{def:is-any-kernel-round}. Then
  \[
    \mathbb{E}_T\bigl[\|V_T\|_{\mathcal{F}}\bigr]
      \leq \sqrt{1 + \sum_{t=0}^{T-1} \mathbb{E}_T\Bigl[\, \sigma \mapsto
        \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}
        \bigl[p_t(1-p_t) k\bigl((x_t^{\sigma},p_t),(x_t^{\sigma},p_t)\bigr)\bigr]\Bigr]} .
  \] -/)
  (proof := /-- The function $\sigma \mapsto \|V_T(\sigma)\|_{\mathcal{F}}$ is nonnegative,
  so \cref{lem:horizon-expectation-sqrt-jensen} applies and gives
  \[
    \mathbb{E}_T\bigl[\|V_T\|_{\mathcal{F}}\bigr]
      \leq \sqrt{\mathbb{E}_T\bigl[\|V_T\|_{\mathcal{F}}^2\bigr]}.
  \]
  By \cref{lem:expected-norm-sq-bound},
  \[
    \mathbb{E}_T\bigl[\|V_T\|^2_{\mathcal{F}}\bigr]
      \leq \sum_{t=0}^{T-1} \mathbb{E}_T\Bigl[\, \sigma \mapsto
            \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}
            \bigl[p_t(1-p_t)
              k\bigl((x_t^{\sigma},p_t),(x_t^{\sigma},p_t)\bigr)\bigr]\Bigr] + 1 .
  \]
  The square root is monotone on the reals, so combining the two displays and commuting the
  two summands under the root yields the asserted bound. -/)
  (title := /-- Bound on the Expected Feature Regret -/)
  (latexEnv := "lemma")]
lemma expected_feature_regret_bound (Φ : X × ℝ → F) (tr : any_kernel_transcript X)
    (bound : ℝ) (T : ℕ)
    (hrounds : ∀ t ∈ Finset.range T, ∀ σ : ℕ → Fin 2,
      is_any_kernel_round Φ tr bound t σ) :
    horizon_expectation tr T (fun σ => ‖feature_regret_vector Φ tr T σ‖) ≤
      Real.sqrt (1 + ∑ t ∈ Finset.range T,
        horizon_expectation tr T (fun σ =>
          round_expectation tr t σ (fun i =>
            tr.candidate t σ i * (1 - tr.candidate t σ i) *
              kernel_of_feature_map Φ (tr.feature t σ, tr.candidate t σ i)
                (tr.feature t σ, tr.candidate t σ i)))) := by
  refine le_trans (horizon_expectation_sqrt_jensen tr T _ (fun σ => norm_nonneg _)) ?_
  apply Real.sqrt_le_sqrt
  have h := expected_norm_sq_bound Φ tr bound T hrounds
  linarith

@[blueprint "lem:indistinguishability-error-eq-inner"
  (statement := /-- Let $\Phi : \mathcal{X} \times \mathbb{R} \to \mathcal{F}$ be a feature
  map, let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $T \in \mathbb{N}$ and let $f \in \mathcal{F}$. Then,
  with $V_T$ the feature regret vector of \cref{def:feature-regret-vector},
  \[
    \sum_{t=0}^{T-1} \mathbb{E}_T\Bigl[\, \sigma \mapsto
      \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}
      \bigl[(y_t^{\sigma} - p_t)\,
        \langle f, \Phi(x_t^{\sigma},p_t)\rangle_{\mathcal{F}}\bigr]\Bigr]
      = \mathbb{E}_T\bigl[\,\langle f, V_T \rangle_{\mathcal{F}}\bigr] .
  \] -/)
  (proof := /-- Fix $\sigma : \mathbb{N} \to \{0,1\}$ and write
  $p_t = q_t^{\sigma}(\sigma(t))$. By
  \cref{def:feature-regret-vector} and linearity of the inner product in its second argument,
  \[
    \langle f, V_T(\sigma) \rangle_{\mathcal{F}}
      = \Bigl\langle f, \sum_{t=0}^{T-1} (y_t^{\sigma} - p_t)
          \Phi(x_t^{\sigma},p_t)\Bigr\rangle_{\mathcal{F}}
      = \sum_{t=0}^{T-1} (y_t^{\sigma} - p_t)\,
          \langle f, \Phi(x_t^{\sigma},p_t)\rangle_{\mathcal{F}} .
  \]
  For each $t$ define
  $g_t^{\sigma}(i)
    = \bigl(y_t^{\sigma} - q_t^{\sigma}(i)\bigr)
      \langle f, \Phi(x_t^{\sigma},q_t^{\sigma}(i))\rangle_{\mathcal{F}}$, so that the $t$-th summand
  above is $g_t^{\sigma}(\sigma(t))$. The map $\sigma \mapsto g_t^{\sigma}$ is history-local
  at $t$ in the sense of \cref{def:history-local}, because each of
  $\sigma \mapsto q_t^{\sigma}$, $\sigma \mapsto x_t^{\sigma}$ and
  $\sigma \mapsto y_t^{\sigma}$ is history-local at $t$ by
  \cref{def:any-kernel-transcript} and $g_t^{\sigma}$ depends on $\sigma$ only through these
  three quantities. Hence
  \cref{lem:horizon-expectation-round-sum}, applied to this family, gives
  \[
    \mathbb{E}_T\bigl[\langle f, V_T\rangle_{\mathcal{F}}\bigr]
      = \sum_{t=0}^{T-1} \mathbb{E}_T\Bigl[\, \sigma \mapsto
        \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}\bigl[(y_t^{\sigma} - p_t)
        \langle f, \Phi(x_t^{\sigma},p_t)\rangle_{\mathcal{F}}\bigr]\Bigr],
  \]
  which is the asserted identity. -/)
  (title := /-- Indistinguishability Error as an Inner Product -/)
  (latexEnv := "lemma")]
lemma indistinguishability_error_eq_inner (Φ : X × ℝ → F) (tr : any_kernel_transcript X)
    (T : ℕ) (f : F) :
    (∑ t ∈ Finset.range T,
        horizon_expectation tr T (fun σ =>
          round_expectation tr t σ (fun i =>
            (tr.outcome t σ - tr.candidate t σ i) *
              inner ℝ f (Φ (tr.feature t σ, tr.candidate t σ i)))))
      = horizon_expectation tr T
          (fun σ => inner ℝ f (feature_regret_vector Φ tr T σ)) := by
  have hg : ∀ t : ℕ,
      history_local t (fun σ i =>
        (tr.outcome t σ - tr.candidate t σ i) *
          inner ℝ f (Φ (tr.feature t σ, tr.candidate t σ i))) := by
    intro t σ τ h
    have ho := tr.outcome_history_local t σ τ h
    have hc := tr.candidate_history_local t σ τ h
    have hf := tr.feature_history_local t σ τ h
    funext i
    simp only [ho, hc, hf]
  rw [← horizon_expectation_round_sum tr T
        (fun t σ i =>
          (tr.outcome t σ - tr.candidate t σ i) *
            inner ℝ f (Φ (tr.feature t σ, tr.candidate t σ i))) hg]
  congr 1
  funext σ
  rw [feature_regret_vector, inner_sum]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [real_inner_smul_right]

@[blueprint "lem:indistinguishability-le-norm-mul-expected-regret"
  (statement := /-- Let $\Phi : \mathcal{X} \times \mathbb{R} \to \mathcal{F}$ be a feature
  map, let $\{(x_t, \Delta_t, y_t)\}_{t}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $T \in \mathbb{N}$ and let $f \in \mathcal{F}$. Then,
  with $V_T$ the feature regret vector of \cref{def:feature-regret-vector},
  \[
    \bigl| \mathbb{E}_T\bigl[\langle f, V_T\rangle_{\mathcal{F}}\bigr] \bigr|
      \leq \|f\|_{\mathcal{F}} \cdot \mathbb{E}_T\bigl[\|V_T\|_{\mathcal{F}}\bigr] .
  \] -/)
  (proof := /-- By \cref{def:horizon-expectation} the left-hand side is the absolute value of
  the finite sum $\sum_{\sigma} W_T(\sigma) \langle f, V_T(\bar\sigma)\rangle_{\mathcal{F}}$.
  By \cref{lem:trajectory-weight-nonneg-and-sum} the weights $W_T(\sigma)$ are nonnegative,
  so the triangle inequality for finite sums gives
  \[
    \Bigl|\sum_{\sigma} W_T(\sigma) \langle f, V_T(\bar\sigma)\rangle_{\mathcal{F}}\Bigr|
      \leq \sum_{\sigma} W_T(\sigma)
        \bigl|\langle f, V_T(\bar\sigma)\rangle_{\mathcal{F}}\bigr| .
  \]
  For each $\sigma$ the Cauchy--Schwarz inequality in the real inner product space
  $\mathcal{F}$ gives
  $|\langle f, V_T(\bar\sigma)\rangle_{\mathcal{F}}|
    \leq \|f\|_{\mathcal{F}} \|V_T(\bar\sigma)\|_{\mathcal{F}}$. Multiplying by the
  nonnegative weight $W_T(\sigma)$ and summing over $\sigma$ therefore gives
  \[
    \sum_{\sigma} W_T(\sigma)\bigl|\langle f, V_T(\bar\sigma)\rangle_{\mathcal{F}}\bigr|
      \leq \|f\|_{\mathcal{F}} \sum_{\sigma} W_T(\sigma) \|V_T(\bar\sigma)\|_{\mathcal{F}}
      = \|f\|_{\mathcal{F}} \cdot \mathbb{E}_T\bigl[\|V_T\|_{\mathcal{F}}\bigr],
  \]
  the last equality being \cref{def:horizon-expectation} again. Chaining the two displays
  yields the assertion. -/)
  (title := /-- Cauchy--Schwarz Bound on the Indistinguishability Error -/)
  (latexEnv := "lemma")]
lemma indistinguishability_le_norm_mul_expected_regret (Φ : X × ℝ → F)
    (tr : any_kernel_transcript X) (T : ℕ) (f : F) :
    |horizon_expectation tr T (fun σ => inner ℝ f (feature_regret_vector Φ tr T σ))| ≤
      ‖f‖ * horizon_expectation tr T (fun σ => ‖feature_regret_vector Φ tr T σ‖) := by
  have hnonneg := (trajectory_weight_nonneg_and_sum tr T).1
  unfold horizon_expectation
  calc
    |∑ σ : Fin T → Fin 2, trajectory_weight tr T σ *
          inner ℝ f (feature_regret_vector Φ tr T (selector_extension T σ))|
        ≤ ∑ σ : Fin T → Fin 2, |trajectory_weight tr T σ *
          inner ℝ f (feature_regret_vector Φ tr T (selector_extension T σ))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ : Fin T → Fin 2, trajectory_weight tr T σ *
          (‖f‖ * ‖feature_regret_vector Φ tr T (selector_extension T σ)‖) := by
          refine Finset.sum_le_sum fun σ _ => ?_
          rw [abs_mul, abs_of_nonneg (hnonneg σ)]
          exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (hnonneg σ)
    _ = ‖f‖ * ∑ σ : Fin T → Fin 2, trajectory_weight tr T σ *
          ‖feature_regret_vector Φ tr T (selector_extension T σ)‖ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun σ _ => by ring

@[blueprint "thm:indistinguishability-main"
  (statement := /-- Let $\mathcal{X}$ be a set, let $\mathcal{F}$ be a real inner product
  space, let $\Phi : \mathcal{X} \times [0,1] \to \mathcal{F}$ be a feature map, and let $k$
  be the associated kernel of \cref{def:kernel-of-feature-map}, so that $\mathcal{F}$ is the
  reproducing kernel Hilbert space of $k$ and every $f \in \mathcal{F}$ satisfies the
  reproducing identity $f(x,p) = \langle f, \Phi(x,p)\rangle_{\mathcal{F}}$. Let
  $\{(x_t, \Delta_t, y_t)\}_{t=0}^{T-1}$ be a transcript in the sense of
  \cref{def:any-kernel-transcript}, let $B \in \mathbb{R}$, and assume that every round
  $t < T$ is, at every history $\sigma$ of the previously realised predictions, an Any Kernel
  round with magnitude parameter $B$ in the sense of \cref{def:is-any-kernel-round}; this is
  exactly the per-round guarantee the algorithm supplies, since by
  \cref{def:any-kernel-transcript} the distribution $\Delta_t^{\sigma}$ is computed from the
  realised predictions $p_0, \dots, p_{t-1}$. Then for every $f \in \mathcal{F}$,
  \[
    \Bigl| \sum_{t=0}^{T-1} \mathbb{E}_T\Bigl[\, \sigma \mapsto
      \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}
        f(x_t^{\sigma},p_t)(y_t^{\sigma} - p_t) \Bigr] \Bigr|
      \leq \|f\|_{\mathcal{F}}
        \sqrt{1 + \sum_{t=0}^{T-1} \mathbb{E}_T\Bigl[\, \sigma \mapsto
          \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}
          p_t (1-p_t) k\bigl((x_t^{\sigma},p_t),(x_t^{\sigma},p_t)\bigr)\Bigr]} .
  \]
  That is, the Any Kernel algorithm is online outcome indistinguishable with respect to
  $\mathcal{F}$ with the stated regret bound. Each occurrence of
  $\mathbb{E}_{p_t \sim \Delta_t}$ in the source statement is read, as it must be for an
  adaptive forecaster, as the expectation over the round-$t$ draw at the realised history,
  averaged over the trajectory; when every $\Delta_t^{\sigma}$ happens to be independent of
  $\sigma$, each such double expectation collapses to the single round expectation
  $\mathbb{E}_{p_t \sim \Delta_t}$. The guarantee holds against an adaptive adversary: by
  \cref{def:any-kernel-transcript} the feature $x_t^{\sigma}$ and the outcome
  $y_t^{\sigma} \in \{0,1\}$ of round $t$ are arbitrary functions of the realised predictions
  $p_0, \dots, p_{t-1}$ of the preceding rounds, so the quantification over transcripts is a
  quantification over all adversaries that may react to the whole realised history, and not
  merely over fixed sequences $(x_t)_t$, $(y_t)_t$, which would describe only an oblivious
  adversary. -/)
  (proof := /-- Fix $f \in \mathcal{F}$. By the reproducing identity, the indistinguishability
  error is
  \[
    \sum_{t=0}^{T-1} \mathbb{E}_T\Bigl[\, \sigma \mapsto
      \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}
        \bigl[(y_t^{\sigma} - p_t) f(x_t^{\sigma},p_t)\bigr]\Bigr]
      = \sum_{t=0}^{T-1} \mathbb{E}_T\Bigl[\, \sigma \mapsto
        \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}
        \bigl[(y_t^{\sigma} - p_t)
          \langle f, \Phi(x_t^{\sigma},p_t)\rangle_{\mathcal{F}}\bigr]\Bigr],
  \]
  and \cref{lem:indistinguishability-error-eq-inner} identifies the right-hand side with
  $\mathbb{E}_T[\langle f, V_T\rangle_{\mathcal{F}}]$, where $V_T$ is the feature regret
  vector of \cref{def:feature-regret-vector}. Taking absolute values and applying
  \cref{lem:indistinguishability-le-norm-mul-expected-regret} gives
  \[
    \Bigl| \sum_{t=0}^{T-1} \mathbb{E}_T\Bigl[\, \sigma \mapsto
      \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}
        f(x_t^{\sigma},p_t)(y_t^{\sigma}-p_t) \Bigr] \Bigr|
      \leq \|f\|_{\mathcal{F}} \cdot \mathbb{E}_T\bigl[\|V_T\|_{\mathcal{F}}\bigr].
  \]
  By hypothesis every round $t < T$ is an Any Kernel round with magnitude parameter $B$ at
  every history, so \cref{lem:expected-feature-regret-bound} applies and bounds
  $\mathbb{E}_T[\|V_T\|_{\mathcal{F}}]$ by
  \[
    \sqrt{1 + \sum_{t=0}^{T-1} \mathbb{E}_T\Bigl[\, \sigma \mapsto
      \mathbb{E}_{p_t \sim \Delta_t^{\sigma}}
      \bigl[p_t(1-p_t) k\bigl((x_t^{\sigma},p_t),(x_t^{\sigma},p_t)\bigr)\bigr]\Bigr]}.
  \]
  Since $\|f\|_{\mathcal{F}} \geq 0$, multiplying this bound by $\|f\|_{\mathcal{F}}$
  preserves the inequality, and chaining the two displays yields the assertion. -/)
  (title := /-- Online Outcome Indistinguishability of the Any Kernel Algorithm -/)
  (latexEnv := "theorem")]
theorem indistinguishability_main (Φ : X × ℝ → F) (tr : any_kernel_transcript X)
    (bound : ℝ) (T : ℕ) (f : F)
    (hrounds : ∀ t ∈ Finset.range T, ∀ σ : ℕ → Fin 2,
      is_any_kernel_round Φ tr bound t σ) :
    |∑ t ∈ Finset.range T,
        horizon_expectation tr T (fun σ =>
          round_expectation tr t σ (fun i =>
            (tr.outcome t σ - tr.candidate t σ i) *
              inner ℝ f (Φ (tr.feature t σ, tr.candidate t σ i))))| ≤
      ‖f‖ * Real.sqrt (1 + ∑ t ∈ Finset.range T,
        horizon_expectation tr T (fun σ =>
          round_expectation tr t σ (fun i =>
            tr.candidate t σ i * (1 - tr.candidate t σ i) *
              kernel_of_feature_map Φ (tr.feature t σ, tr.candidate t σ i)
                (tr.feature t σ, tr.candidate t σ i)))) := by
  rw [indistinguishability_error_eq_inner]
  refine le_trans (indistinguishability_le_norm_mul_expected_regret Φ tr T f) ?_
  exact mul_le_mul_of_nonneg_left (expected_feature_regret_bound Φ tr bound T hrounds) (norm_nonneg f)

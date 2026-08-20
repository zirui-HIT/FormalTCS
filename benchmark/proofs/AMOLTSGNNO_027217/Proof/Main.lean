import Architect
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

set_option linter.all false
set_option maxHeartbeats 500000

open scoped Matrix

attribute [local instance] Matrix.instPartialOrder Matrix.instStarOrderedRing
  Matrix.instNonnegSpectrumClass Matrix.normedAddCommGroup Matrix.normedSpace

@[blueprint "def:matrix-inner-product"
  (statement := /-- For matrices $A, B \in \mathbb{R}^{m \times n}$, the trace (Frobenius) inner
    product is defined by $\langle A, B\rangle := \operatorname{Tr}(A^{\top} B)
    = \sum_{i=1}^{m}\sum_{j=1}^{n} A_{ij} B_{ij}$. -/)
  (title := /-- Trace inner product on matrices -/)
  (latexEnv := "definition")]
noncomputable def matrix_inner_product {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  (Aᵀ * B).trace

@[blueprint "def:bregman-divergence"
  (statement := /-- Let $f : \mathbb{R}^{m \times n} \to \mathbb{R}$ be differentiable with matrix
    gradient map $\nabla f : \mathbb{R}^{m \times n} \to \mathbb{R}^{m \times n}$. For
    $U, V \in \mathbb{R}^{m \times n}$, the Bregman divergence of $f$ from the anchor point $V$ to
    the point $U$ is $B_f(U, V) := f(U) - f(V) - \langle \nabla f(V), U - V\rangle$, where
    $\langle \cdot, \cdot\rangle$ is the trace inner product of \cref{def:matrix-inner-product}. -/)
  (title := /-- Bregman divergence -/)
  (latexEnv := "definition")]
noncomputable def bregman_divergence {m n : ℕ}
    (f : Matrix (Fin m) (Fin n) ℝ → ℝ)
    (grad : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin n) ℝ)
    (U V : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  f U - f V - matrix_inner_product (grad V) (U - V)

@[blueprint "def:cumulative-gradient"
  (statement := /-- Given a sequence $G : \mathbb{N} \to \mathbb{R}^{m \times n}$ of gradient
    matrices, the cumulative gradient at round $t$ is $S_t := \sum_{s=1}^{t} G_s$. -/)
  (title := /-- Cumulative gradient -/)
  (latexEnv := "definition")]
noncomputable def cumulative_gradient {m n : ℕ}
    (G : ℕ → Matrix (Fin m) (Fin n) ℝ) (t : ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  ∑ s ∈ Finset.Icc 1 t, G s

@[blueprint "def:gradient-covariance"
  (statement := /-- Given a sequence $G : \mathbb{N} \to \mathbb{R}^{m \times n}$, the
    gradient-covariance matrix at round $t$ is the symmetric positive semidefinite matrix
    $M_t := \sum_{s=1}^{t} G_s G_s^{\top} \in \mathbb{R}^{m \times m}$. -/)
  (title := /-- Gradient-covariance matrix -/)
  (latexEnv := "definition")]
noncomputable def gradient_covariance {m n : ℕ}
    (G : ℕ → Matrix (Fin m) (Fin n) ℝ) (t : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ s ∈ Finset.Icc 1 t, G s * (G s)ᵀ

@[blueprint "def:preconditioner"
  (statement := /-- Fix a uniform bound $G \ge 0$ and a gradient sequence
    $(G_s)_{s} \subset \mathbb{R}^{m \times n}$. The adaptive preconditioner at round $t$ is the
    positive semidefinite matrix square root $L_t := (G^2 I + M_t)^{1/2} \in \mathbb{R}^{m \times m}$,
    where $M_t$ is the gradient covariance of \cref{def:gradient-covariance} and
    $I \in \mathbb{R}^{m \times m}$ is the identity matrix. -/)
  (title := /-- Adaptive preconditioner -/)
  (latexEnv := "definition")]
noncomputable def preconditioner {m n : ℕ} (Gconst : ℝ)
    (G : ℕ → Matrix (Fin m) (Fin n) ℝ) (t : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  CFC.sqrt (Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) + gradient_covariance G t)

@[blueprint "def:learning-rate"
  (statement := /-- Given admissibility constants $\alpha, \beta > 0$, the learning-rate scaling is
    $\eta := \sqrt{\alpha / \beta}$. -/)
  (title := /-- Learning-rate scaling -/)
  (latexEnv := "definition")]
noncomputable def learning_rate (alpha beta : ℝ) : ℝ :=
  Real.sqrt (alpha / beta)

@[blueprint "def:admissible-smoothing"
  (statement := /-- An $(\alpha, \beta)$-admissible smoothing of the nuclear norm on
    $\mathbb{R}^{m \times n}$ consists of an operator norm $\|\cdot\|_{\mathrm{op}}$ and a nuclear
    norm $\|\cdot\|_{*}$ on $\mathbb{R}^{m \times n}$; a potential family
    $\widetilde{\Psi}(\cdot\,; L) : \mathbb{R}^{m \times n} \to \mathbb{R}$ parametrized by a
    symmetric positive semidefinite matrix $L \in \mathbb{R}^{m \times m}$, together with a specified
    matrix field $\mathsf{g}(X;L)$; and constants $\alpha, \beta > 0$. For every $L \succ 0$ and every
    $X$, the matrix $\mathsf{g}(X;L)$ is required to be the Fréchet gradient of
    $Z \mapsto \widetilde{\Psi}(Z;L)$ at $X$. For singular positive semidefinite $L$, including
    $L=0$, $\mathsf{g}(X;L)$ remains part of the data but no differentiability is asserted. These data
    are subject to the following conditions. (a) Feasibility: for every $L \succeq 0$ and every $X$,
    $\|\mathsf{g}(X; L)\|_{\mathrm{op}} \le 1$. (b) Dominance: for every $L \succeq 0$
    and every $X$, $\widetilde{\Psi}(X; L) \ge \|X\|_{*}$, and moreover $\widetilde{\Psi}(X; 0) =
    \|X\|_{*}$. (c) Upper stability: whenever $L_1,L_2 \succeq 0$ and $L_1 \preceq L_2$ (that is,
    $L_2 - L_1 \succeq 0$), one has $\widetilde{\Psi}(X; L_2) - \widetilde{\Psi}(X; L_1) \le \alpha\,(\operatorname{Tr} L_2 -
    \operatorname{Tr} L_1)$ for every $X$. (d) $\beta$-smoothness: for every $L \succ 0$ and all
    $X, Y$, the Bregman divergence (\cref{def:bregman-divergence}) of $\widetilde{\Psi}(\cdot; L)$
    satisfies $B_{\widetilde{\Psi}(\cdot; L)}(Y, X) \le \frac{\beta}{2}\,\operatorname{Tr}\!\bigl(
    (X - Y)^{\top} L^{-1} (X - Y)\bigr)$. (e) Duality: the nuclear norm is the support function of
    the operator-norm ball, so that for every $A \in \mathbb{R}^{m \times n}$ and every radius
    $D \ge 0$, $\inf_{\|Y\|_{\mathrm{op}} \le D} \langle A, Y\rangle = -D\,\|A\|_{*}$; equivalently
    $\|A\|_{*} = \max_{\|X\|_{\mathrm{op}} \le 1} \langle X, A\rangle$, exhibiting
    $\|\cdot\|_{*}$ as the dual norm of $\|\cdot\|_{\mathrm{op}}$. Here $\langle \cdot, \cdot\rangle$
    is the trace inner product of \cref{def:matrix-inner-product}. (f) Nuclear normalization: the
    nuclear norm is the genuine nuclear (Schatten-$1$) norm, so that for every
    $A \in \mathbb{R}^{m \times n}$ one has $\|A\|_{*} = \operatorname{Tr}\!\bigl((A^{\top} A)^{1/2}
    \bigr)$, the sum of the singular values of $A$, where $(A^{\top} A)^{1/2}$ is the positive
    semidefinite matrix square root. (g) Operator normalization: the operator norm dominates the
    genuine spectral norm in the Loewner order, so that for every $A \in \mathbb{R}^{m \times n}$
    and every $c \in \mathbb{R}$ with $\|A\|_{\mathrm{op}} \le c$ one has $A A^{\top} \preceq c^2 I$,
    that is $c^2 I - A A^{\top} \succeq 0$, where $I \in \mathbb{R}^{m \times m}$ is the identity
    matrix. Conditions (f) and (g) pin the abstract pair $(\|\cdot\|_{\mathrm{op}}, \|\cdot\|_{*})$
    to the genuine operator and nuclear norms on $\mathbb{R}^{m \times n}$, placing them on the
    common scale of the trace inner product and of the identity matrix $I$ entering the
    preconditioner $L_t = (G^2 I + M_t)^{1/2}$ (\cref{def:preconditioner}); without them the pair
    would retain the spurious rescaling freedom $(\|\cdot\|_{\mathrm{op}}, \|\cdot\|_{*}) \mapsto
    (\|\cdot\|_{\mathrm{op}} / K, K\,\|\cdot\|_{*})$ (for $K > 0$), under which the two right-hand
    terms of the regret bound scale oppositely to the left-hand side and the conclusion becomes
    false. -/)
  (title := /-- $(\alpha, \beta)$-admissible smoothing of the nuclear norm -/)
  (latexEnv := "definition")]
structure admissible_smoothing (m n : ℕ) where
  opNorm : Matrix (Fin m) (Fin n) ℝ → ℝ
  nucNorm : Matrix (Fin m) (Fin n) ℝ → ℝ
  pot : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin m) ℝ → ℝ
  gradPot : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin m) (Fin m) ℝ → Matrix (Fin m) (Fin n) ℝ
  alpha : ℝ
  beta : ℝ
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta
  gradPot_is_gradient : ∀ (X : Matrix (Fin m) (Fin n) ℝ) (L : Matrix (Fin m) (Fin m) ℝ),
    L.PosDef →
      DifferentiableAt ℝ (fun Z => pot Z L) X ∧
        ∀ H, fderiv ℝ (fun Z => pot Z L) X H = matrix_inner_product (gradPot X L) H
  feasibility : ∀ (X : Matrix (Fin m) (Fin n) ℝ) (L : Matrix (Fin m) (Fin m) ℝ),
    L.PosSemidef → opNorm (gradPot X L) ≤ 1
  dominance_ge : ∀ (X : Matrix (Fin m) (Fin n) ℝ) (L : Matrix (Fin m) (Fin m) ℝ),
    L.PosSemidef → nucNorm X ≤ pot X L
  dominance_zero : ∀ (X : Matrix (Fin m) (Fin n) ℝ), pot X 0 = nucNorm X
  upper_stability : ∀ (X : Matrix (Fin m) (Fin n) ℝ) (L₁ L₂ : Matrix (Fin m) (Fin m) ℝ),
    L₁.PosSemidef → (L₂ - L₁).PosSemidef →
      pot X L₂ - pot X L₁ ≤ alpha * (L₂.trace - L₁.trace)
  smoothness : ∀ (X Y : Matrix (Fin m) (Fin n) ℝ) (L : Matrix (Fin m) (Fin m) ℝ),
    L.PosDef →
      bregman_divergence (fun Z => pot Z L) (fun Z => gradPot Z L) Y X
        ≤ (beta / 2) * ((X - Y)ᵀ * L⁻¹ * (X - Y)).trace
  nucNorm_dual : ∀ (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ), 0 ≤ D →
    sInf ((fun Y => matrix_inner_product A Y) ''
        {Y : Matrix (Fin m) (Fin n) ℝ | opNorm Y ≤ D})
      = -D * nucNorm A
  nucNorm_normalization : ∀ (A : Matrix (Fin m) (Fin n) ℝ),
    nucNorm A = (CFC.sqrt (Aᵀ * A)).trace
  opNorm_normalization : ∀ (A : Matrix (Fin m) (Fin n) ℝ) (c : ℝ),
    opNorm A ≤ c → (c ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) - A * Aᵀ).PosSemidef

@[blueprint "def:gbpa-run"
  (statement := /-- Fix an $(\alpha, \beta)$-admissible smoothing $\mathcal{S}$
    (\cref{def:admissible-smoothing}). A GBPA run over a nonempty horizon $T \ge 1$ for
    $\mathcal{S}$ consists of a
    gradient sequence $G : \mathbb{N} \to \mathbb{R}^{m \times n}$, an iterate sequence
    $X : \mathbb{N} \to \mathbb{R}^{m \times n}$, a decision-set radius $D > 0$, and a uniform bound
    $G_{\max} \ge 0$, such that: $\|G_t\|_{\mathrm{op}} \le G_{\max}$ for all $1 \le t \le T$;
    $X_1 = 0$; and for every $1 \le t < T$,
    $X_{t+1} = -D\,\mathsf{g}\bigl(S_t;\, L_t / \eta\bigr)$, where $\mathsf{g}$ is the specified
    matrix field from \cref{def:admissible-smoothing}, $S_t$ is the
    cumulative gradient (\cref{def:cumulative-gradient}), $L_t = (G_{\max}^2 I + M_t)^{1/2}$ is the
    preconditioner (\cref{def:preconditioner}), and $\eta = \sqrt{\alpha / \beta}$
    (\cref{def:learning-rate}). If $G_{\max}>0$, then $L_t/\eta\succ0$, and hence $\mathsf{g}$ at
    every parameter used by the update is the genuine Fréchet gradient. If $G_{\max}=0$, the gradient
    bound and operator normalization force every loss matrix to vanish; this degenerate case requires
    no differentiability assertion at the zero parameter. -/)
  (title := /-- GBPA run with adaptive smoothing -/)
  (latexEnv := "definition")]
structure gbpa_run {m n : ℕ} (S : admissible_smoothing m n) where
  G : ℕ → Matrix (Fin m) (Fin n) ℝ
  X : ℕ → Matrix (Fin m) (Fin n) ℝ
  D : ℝ
  D_pos : 0 < D
  Gconst : ℝ
  Gconst_nonneg : 0 ≤ Gconst
  T : ℕ
  T_pos : 1 ≤ T
  grad_bound : ∀ t, 1 ≤ t → t ≤ T → S.opNorm (G t) ≤ Gconst
  init : X 1 = 0
  update : ∀ t, 1 ≤ t → t < T →
    X (t + 1) =
      (-D) • S.gradPot (cumulative_gradient G t)
        ((learning_rate S.alpha S.beta)⁻¹ • preconditioner Gconst G t)

@[blueprint "def:regret"
  (statement := /-- For a gradient sequence $G$, an iterate sequence $X$, a radius $D > 0$ and a
    horizon $T$, over the decision set $\mathcal{X} = \{Y \in \mathbb{R}^{m \times n} :
    \|Y\|_{\mathrm{op}} \le D\}$ the regret is $\mathrm{Reg}_T := \sum_{t=1}^{T} \langle G_t, X_t\rangle
    - \inf_{Y \in \mathcal{X}} \sum_{t=1}^{T} \langle G_t, Y\rangle$, where $\langle \cdot, \cdot\rangle$
    is the trace inner product of \cref{def:matrix-inner-product}. -/)
  (title := /-- Regret of an online matrix learner -/)
  (latexEnv := "definition")]
noncomputable def regret {m n : ℕ} (opNorm : Matrix (Fin m) (Fin n) ℝ → ℝ)
    (G X : ℕ → Matrix (Fin m) (Fin n) ℝ) (D : ℝ) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.Icc 1 T, matrix_inner_product (G t) (X t))
    - sInf ((fun Y => ∑ t ∈ Finset.Icc 1 T, matrix_inner_product (G t) Y) ''
        {Y : Matrix (Fin m) (Fin n) ℝ | opNorm Y ≤ D})

@[blueprint "lem:gbpa-decomposition"
  (statement := /-- Let $\mathcal{S}$ be an $(\alpha, \beta)$-admissible smoothing
    (\cref{def:admissible-smoothing}) and let $(G, X, D, G_{\max}, T)$ be a GBPA run for
    $\mathcal{S}$ (\cref{def:gbpa-run}). Write $S_t = \sum_{s=1}^{t} G_s$ for the cumulative
    gradient (\cref{def:cumulative-gradient}), $\widetilde{\Phi}_t(\cdot) :=
    \widetilde{\Psi}(\cdot\,; L_t / \eta)$ with $L_t = (G_{\max}^2 I + M_t)^{1/2}$
    (\cref{def:preconditioner}) and $\eta = \sqrt{\alpha / \beta}$ (\cref{def:learning-rate}), and
    $\Phi(\cdot) := \|\cdot\|_{*}$. Then the regret (\cref{def:regret}) admits the decomposition
    $\mathrm{Reg}_T = D\bigl(\Phi(S_T) - \widetilde{\Phi}_T(S_T)\bigr)
    + D\sum_{t=1}^{T-1} B_{\widetilde{\Phi}_t}(S_{t+1}, S_t)
    + D\sum_{t=1}^{T-1}\bigl(\widetilde{\Phi}_{t+1}(S_{t+1}) - \widetilde{\Phi}_t(S_{t+1})\bigr)
    + D\,\widetilde{\Phi}_1(G_1)$, where $B_{\widetilde{\Phi}_t}$ is the Bregman divergence
    (\cref{def:bregman-divergence}). -/)
  (proof := /-- The losses $\ell_t(X) = \langle G_t, X\rangle$ are linear, so
    $\sum_{t=1}^{T} \langle G_t, X\rangle = \langle S_T, X\rangle$ for every fixed $X$, and the
    regret of \cref{def:regret} is $\sum_{t=1}^{T} \langle G_t, X_t\rangle - \inf_{Y \in \mathcal{X}}
    \langle S_T, Y\rangle$. By the duality condition (e) of \cref{def:admissible-smoothing}, the
    nuclear norm is the support function of the operator-norm ball, so
    $\inf_{Y \in \mathcal{X}} \langle S_T, Y\rangle = \inf_{\|Y\|_{\mathrm{op}} \le D}
    \langle S_T, Y\rangle = -D\,\|S_T\|_{*} = -D\,\Phi(S_T)$; hence the regret equals
    $\sum_{t=1}^{T} \langle G_t, X_t\rangle + D\,\Phi(S_T)$. By the GBPA update of
    \cref{def:gbpa-run}, $X_1 = 0$ and
    $X_{t+1} = -D\,\nabla \widetilde{\Phi}_t(S_t)$; substituting these iterates and expanding the
    Bregman divergence $B_{\widetilde{\Phi}_t}(S_{t+1}, S_t) = \widetilde{\Phi}_t(S_{t+1}) -
    \widetilde{\Phi}_t(S_t) - \langle \nabla \widetilde{\Phi}_t(S_t), S_{t+1} - S_t\rangle$ of
    \cref{def:bregman-divergence}, together with $S_{t+1} - S_t = G_{t+1}$, one telescopes the
    surrogate potentials $\widetilde{\Phi}_t$ across the rounds $t = 1, \dots, T$. This is the matrix
    analogue of the Gradient-Based Prediction Algorithm regret decomposition (Abernethy, Lee and
    Tewari, 2016, Lemma 1.2) and yields the four stated terms: the terminal gap
    $D(\Phi(S_T) - \widetilde{\Phi}_T(S_T))$, the summed Bregman divergences, the summed
    potential-parameter increments $\widetilde{\Phi}_{t+1}(S_{t+1}) - \widetilde{\Phi}_t(S_{t+1})$,
    and the initial term $D\,\widetilde{\Phi}_1(G_1)$. -/)
  (title := /-- GBPA regret decomposition -/)
  (latexEnv := "lemma")]
lemma gbpa_decomposition {m n : ℕ} (S : admissible_smoothing m n) (run : gbpa_run S) :
    regret S.opNorm run.G run.X run.D run.T =
      run.D * (S.nucNorm (cumulative_gradient run.G run.T)
          - S.pot (cumulative_gradient run.G run.T)
              ((learning_rate S.alpha S.beta)⁻¹ • preconditioner run.Gconst run.G run.T))
      + run.D * (∑ t ∈ Finset.Icc 1 (run.T - 1),
          bregman_divergence
            (fun Z => S.pot Z ((learning_rate S.alpha S.beta)⁻¹ • preconditioner run.Gconst run.G t))
            (fun Z => S.gradPot Z ((learning_rate S.alpha S.beta)⁻¹ • preconditioner run.Gconst run.G t))
            (cumulative_gradient run.G (t + 1)) (cumulative_gradient run.G t))
      + run.D * (∑ t ∈ Finset.Icc 1 (run.T - 1),
          (S.pot (cumulative_gradient run.G (t + 1))
              ((learning_rate S.alpha S.beta)⁻¹ • preconditioner run.Gconst run.G (t + 1))
            - S.pot (cumulative_gradient run.G (t + 1))
              ((learning_rate S.alpha S.beta)⁻¹ • preconditioner run.Gconst run.G t)))
      + run.D * S.pot (run.G 1)
          ((learning_rate S.alpha S.beta)⁻¹ • preconditioner run.Gconst run.G 1) := by
  have hTpos : (1 : ℕ) ≤ run.T := run.T_pos
  have hsymm : ∀ A B : Matrix (Fin m) (Fin n) ℝ,
      matrix_inner_product A B = matrix_inner_product B A := by
    intro A B
    simp only [matrix_inner_product]
    rw [← Matrix.trace_transpose (Bᵀ * A), Matrix.transpose_mul, Matrix.transpose_transpose]
  have hsmul : ∀ (A B : Matrix (Fin m) (Fin n) ℝ) (c : ℝ),
      matrix_inner_product A (c • B) = c * matrix_inner_product A B := by
    intro A B c
    simp only [matrix_inner_product, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  have tele : ∀ (f : ℕ → ℝ) (N : ℕ),
      (∑ s ∈ Finset.Icc 1 N, f s)
        = - f (N + 1) + (∑ s ∈ Finset.Icc 1 N, f (s + 1)) + f 1 := by
    intro f N
    induction N with
    | zero =>
      rw [show (0 : ℕ) + 1 = 1 from rfl,
          Finset.Icc_eq_empty (by omega : ¬ (1 : ℕ) ≤ 0),
          Finset.sum_empty, Finset.sum_empty]
      ring
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ k + 1 by omega),
          Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ k + 1 by omega), ih]
      ring
  have hcum1 : cumulative_gradient run.G 1 = run.G 1 := by
    simp only [cumulative_gradient, Finset.Icc_self, Finset.sum_singleton]
  have hReindex : ∀ N, N + 1 ≤ run.T →
      (∑ t ∈ Finset.Icc 1 (N + 1), matrix_inner_product (run.G t) (run.X t))
        = ∑ s ∈ Finset.Icc 1 N, matrix_inner_product (run.G (s + 1)) (run.X (s + 1)) := by
    intro N
    induction N with
    | zero =>
      intro _
      rw [zero_add, Finset.Icc_self, Finset.sum_singleton, run.init,
          Finset.Icc_eq_empty (by omega : ¬ (1 : ℕ) ≤ 0), Finset.sum_empty]
      simp [matrix_inner_product]
    | succ k ih =>
      intro hk
      rw [Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ k + 1 + 1 by omega)]
      rw [ih (by omega)]
      rw [Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ k + 1 by omega)]
  have hterm : ∀ s ∈ Finset.Icc 1 (run.T - 1),
      matrix_inner_product (run.G (s + 1)) (run.X (s + 1))
        = run.D * bregman_divergence
            (fun Z => S.pot Z ((learning_rate S.alpha S.beta)⁻¹ • preconditioner run.Gconst run.G s))
            (fun Z => S.gradPot Z ((learning_rate S.alpha S.beta)⁻¹ • preconditioner run.Gconst run.G s))
            (cumulative_gradient run.G (s + 1)) (cumulative_gradient run.G s)
          + run.D * (S.pot (cumulative_gradient run.G s)
                ((learning_rate S.alpha S.beta)⁻¹ • preconditioner run.Gconst run.G s)
              - S.pot (cumulative_gradient run.G (s + 1))
                ((learning_rate S.alpha S.beta)⁻¹ • preconditioner run.Gconst run.G s)) := by
    intro s hs
    simp only [Finset.mem_Icc] at hs
    have hsT : s < run.T := by omega
    rw [run.update s hs.1 hsT, hsmul, hsymm (run.G (s + 1))]
    have hG : run.G (s + 1)
        = cumulative_gradient run.G (s + 1) - cumulative_gradient run.G s := by
      simp only [cumulative_gradient]
      rw [Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ s + 1 by omega)]
      abel
    rw [hG]
    simp only [bregman_divergence]
    ring
  have hInf : sInf ((fun Y => ∑ t ∈ Finset.Icc 1 run.T, matrix_inner_product (run.G t) Y) ''
        {Y : Matrix (Fin m) (Fin n) ℝ | S.opNorm Y ≤ run.D})
      = -run.D * S.nucNorm (cumulative_gradient run.G run.T) := by
    have hset : (fun Y => ∑ t ∈ Finset.Icc 1 run.T, matrix_inner_product (run.G t) Y) ''
          {Y : Matrix (Fin m) (Fin n) ℝ | S.opNorm Y ≤ run.D}
        = (fun Y => matrix_inner_product (cumulative_gradient run.G run.T) Y) ''
          {Y : Matrix (Fin m) (Fin n) ℝ | S.opNorm Y ≤ run.D} := by
      apply Set.image_congr
      intro Y _
      simp only [matrix_inner_product, cumulative_gradient]
      rw [Matrix.transpose_sum, Matrix.sum_mul, Matrix.trace_sum]
    rw [hset]
    exact S.nucNorm_dual (cumulative_gradient run.G run.T) run.D (le_of_lt run.D_pos)
  have hpre : (∑ t ∈ Finset.Icc 1 run.T, matrix_inner_product (run.G t) (run.X t))
      = ∑ s ∈ Finset.Icc 1 (run.T - 1),
          matrix_inner_product (run.G (s + 1)) (run.X (s + 1)) := by
    have h := hReindex (run.T - 1) (by omega)
    rwa [Nat.sub_add_cancel hTpos] at h
  simp only [regret]
  rw [hInf]
  rw [hpre]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have htel := tele (fun u => S.pot (cumulative_gradient run.G u)
      ((learning_rate S.alpha S.beta)⁻¹ • preconditioner run.Gconst run.G u)) (run.T - 1)
  simp only [Nat.sub_add_cancel hTpos] at htel
  rw [hcum1] at htel
  linear_combination run.D * htel

@[blueprint "lem:matrix-sqrt-order"
  (statement := /-- Let $A,B\in\mathbb{R}^{m\times m}$. If $A$ and $B-A$ are symmetric positive
    semidefinite matrices, then their positive semidefinite square roots satisfy
    $A^{1/2}\preceq B^{1/2}$. -/)
  (proof := /-- Set $S_A=A^{1/2}$, $S_B=B^{1/2}$, and $D=S_B-S_A$. Since $A$ and $B-A$ are
    positive semidefinite, so is $B$; hence $S_A$ and $S_B$ are positive semidefinite and $D$ is
    symmetric. The square-root identities $S_A^2=A$ and $S_B^2=B$ give
    \[
      B-A=S_BD+DS_A.
    \]
    It suffices to prove that every eigenvalue of $D$ is nonnegative. Suppose instead that
    $Dv=\lambda v$ for a unit eigenvector $v$ and an eigenvalue $\lambda<0$. Symmetry of $D$
    implies
    \[
      v^{\top}(B-A)v
      =\lambda\bigl(v^{\top}S_Bv+v^{\top}S_Av\bigr).
    \]
    Both quadratic forms in parentheses are nonnegative. Moreover,
    $\lambda=v^{\top}Dv=v^{\top}S_Bv-v^{\top}S_Av<0$, so their sum is strictly positive.
    The displayed identity therefore makes $v^{\top}(B-A)v$ negative, contradicting the positive
    semidefiniteness of $B-A$. Thus every eigenvalue of the symmetric matrix $D$ is nonnegative,
    and consequently $D$ is positive semidefinite. -/)
  (title := /-- Loewner monotonicity of the matrix square root -/)
  (latexEnv := "lemma")]
lemma matrix_sqrt_order {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.PosSemidef) (hBA : (B - A).PosSemidef) :
    (CFC.sqrt B - CFC.sqrt A).PosSemidef := by
  classical
  let SA := CFC.sqrt A
  let SB := CFC.sqrt B
  let D := SB - SA
  have hSA : SA.PosSemidef := by
    exact Matrix.LE.le.posSemidef (CFC.sqrt_nonneg A)
  have hB : B.PosSemidef := by
    apply Matrix.LE.le.posSemidef
    exact hA.nonneg.trans hBA
  have hSB : SB.PosSemidef := by
    exact Matrix.LE.le.posSemidef (CFC.sqrt_nonneg B)
  have hD : D.IsHermitian := hSB.isHermitian.sub hSA.isHermitian
  have hDtranspose : D.transpose = D := by
    exact Matrix.isHermitian_iff_isSymm.mp hD
  have hsqA : SA * SA = A := by
    simpa [SA, pow_two] using CFC.sq_sqrt A hA.nonneg
  have hsqB : SB * SB = B := by
    simpa [SB, pow_two] using CFC.sq_sqrt B hB.nonneg
  have hfactor : B - A = SB * D + D * SA := by
    rw [← hsqB, ← hsqA]
    simp only [D]
    noncomm_ring
  change D.PosSemidef
  rw [hD.posSemidef_iff_eigenvalues_nonneg]
  intro i
  by_contra hi
  have hlam : hD.eigenvalues i < 0 := lt_of_not_ge hi
  let v : Fin m → ℝ := ⇑(hD.eigenvectorBasis i)
  have heig : D *ᵥ v = (hD.eigenvalues i) • v := by
    simpa [v] using hD.mulVec_eigenvectorBasis i
  have hvnorm : star v ⬝ᵥ v = 1 := by
    have hvnorm' := hD.eigenvectorBasis.inner_eq_one i
    change v ⬝ᵥ star v = 1 at hvnorm'
    rw [dotProduct_comm] at hvnorm'
    exact hvnorm'
  have hmove (w : Fin m → ℝ) :
      star v ⬝ᵥ (D *ᵥ w) = hD.eigenvalues i * (star v ⬝ᵥ w) := by
    calc
      star v ⬝ᵥ (D *ᵥ w) = star w ⬝ᵥ (D *ᵥ v) := by
        simpa [hDtranspose] using Matrix.dotProduct_transpose_mulVec D v w
      _ = hD.eigenvalues i * (star v ⬝ᵥ w) := by
        rw [heig]
        simp [dotProduct_comm]
  have hqD : star v ⬝ᵥ (D *ᵥ v) = hD.eigenvalues i := by
    rw [hmove, hvnorm, mul_one]
  have hqSA : 0 ≤ star v ⬝ᵥ (SA *ᵥ v) := hSA.dotProduct_mulVec_nonneg v
  have hqSB : 0 ≤ star v ⬝ᵥ (SB *ᵥ v) := hSB.dotProduct_mulVec_nonneg v
  have hqDsplit :
      star v ⬝ᵥ (D *ᵥ v) =
        (star v ⬝ᵥ (SB *ᵥ v)) - (star v ⬝ᵥ (SA *ᵥ v)) := by
    simp [D, Matrix.sub_mulVec, dotProduct_sub]
  have hsumpos :
      0 < (star v ⬝ᵥ (SB *ᵥ v)) + (star v ⬝ᵥ (SA *ᵥ v)) := by
    rw [hqDsplit] at hqD
    linarith
  have hqfactor :
      star v ⬝ᵥ ((SB * D + D * SA) *ᵥ v) =
        hD.eigenvalues i *
          ((star v ⬝ᵥ (SB *ᵥ v)) + (star v ⬝ᵥ (SA *ᵥ v))) := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, heig,
      Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, hmove]
    ring
  have hHnonneg := hBA.dotProduct_mulVec_nonneg v
  rw [hfactor, hqfactor] at hHnonneg
  exact (not_lt_of_ge hHnonneg) (mul_neg_of_neg_of_pos hlam hsumpos)

@[blueprint "lem:matrix-inverse-antitone"
  (statement := /-- Let $A,B\in\mathbb{R}^{m\times m}$ be symmetric positive definite matrices.
    If $A\preceq B$, then $B^{-1}\preceq A^{-1}$. -/)
  (proof := /-- Set $D=A^{-1}-B^{-1}$. Since $B-A$ is positive semidefinite and
    $B^{-1}$ is symmetric, the congruence $B^{-1}(B-A)B^{-1}$ is positive semidefinite.
    Likewise, positive definiteness of $A$ implies that $A$ is positive semidefinite, so
    $DAD$ is positive semidefinite because $D$ is symmetric. Positive definiteness of $A$ and
    $B$ also makes both matrices invertible. Expanding the products and using
    $A^{-1}A=AA^{-1}=B^{-1}B=BB^{-1}=I$ gives
    \[
      B^{-1}(B-A)B^{-1}+DAD=D.
    \]
    Thus $D$ is a sum of two positive semidefinite matrices and is positive semidefinite. -/)
  (title := /-- Antitonicity of inversion on positive definite matrices -/)
  (latexEnv := "lemma")]
lemma matrix_inverse_antitone {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hBA : (B - A).PosSemidef) :
    (A⁻¹ - B⁻¹).PosSemidef := by
  have hAi : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det (A := A)).mp hA.isUnit
  have hBi : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det (A := B)).mp hB.isUnit
  have h₁ := hBA.conjTranspose_mul_mul_same (B⁻¹)
  rw [hB.inv.isHermitian.eq] at h₁
  have h₂ := hA.posSemidef.conjTranspose_mul_mul_same (A⁻¹ - B⁻¹)
  rw [(hA.inv.isHermitian.sub hB.inv.isHermitian).eq] at h₂
  have hsum := h₁.add h₂
  convert hsum using 1 <;>
    simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv A hAi,
      Matrix.mul_nonsing_inv B hBi,
      Matrix.nonsing_inv_mul_cancel_left (A := A) B⁻¹ hAi]

@[blueprint "lem:trace-sqrt-master-preconditioner-facts"
  (statement := /-- Let $c>0$, let $G_s\in\mathbb{R}^{m\times n}$ for every $s\in\mathbb{N}$,
    and let $t\in\mathbb{N}$. The preconditioner
    $L_t=(c^2I+\sum_{s=1}^tG_sG_s^{\top})^{1/2}$ is positive definite and satisfies
    $L_t^2=c^2I+\sum_{s=1}^tG_sG_s^{\top}$. -/)
  (proof := /-- By \cref{def:gradient-covariance}, every summand of $M_t$ has the form
    $G_sG_s^{\top}$ and is positive semidefinite, so $M_t$ is positive semidefinite. Since
    $c^2>0$, the matrix $c^2I+M_t$ is positive definite. Its square root in
    \cref{def:preconditioner} is positive semidefinite and invertible, hence positive definite,
    and the continuous-functional-calculus square-root identity gives
    $L_t^2=c^2I+M_t$. -/)
  (title := /-- Positivity and square identity for the preconditioner -/)
  (latexEnv := "lemma")]
lemma trace_sqrt_master_preconditioner_facts {m n : ℕ} (Gconst : ℝ)
    (G : ℕ → Matrix (Fin m) (Fin n) ℝ) (t : ℕ) (hGconst : 0 < Gconst) :
    (preconditioner Gconst G t).PosDef ∧
      preconditioner Gconst G t * preconditioner Gconst G t =
        Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) + gradient_covariance G t := by
  have hterm (s : ℕ) : (G s * (G s)ᵀ).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose (G s)
  have hcov : (gradient_covariance G t).PosSemidef := by
    rw [gradient_covariance]
    exact Matrix.posSemidef_sum _ (fun s _ => hterm s)
  have hconst : (Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ)).PosDef := by
    exact Matrix.PosDef.one.smul (sq_pos_of_pos hGconst)
  have hrad :
      (Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) + gradient_covariance G t).PosDef :=
    hconst.add_posSemidef hcov
  have hsqrt :
      (CFC.sqrt (Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) +
        gradient_covariance G t)).PosSemidef :=
    Matrix.LE.le.posSemidef (CFC.sqrt_nonneg _)
  have hsqrtUnit :
      IsUnit (CFC.sqrt (Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) +
        gradient_covariance G t)) :=
    hrad.isStrictlyPositive.isUnit_cfcSqrt _
  constructor
  · rw [preconditioner]
    exact hsqrt.posDef_iff_isUnit.mpr hsqrtUnit
  · simpa only [preconditioner, pow_two] using CFC.sq_sqrt
      (Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) + gradient_covariance G t)
      hrad.posSemidef.nonneg

@[blueprint "lem:trace-sqrt-master-step"
  (statement := /-- Let $c>0$, let $G_s\in\mathbb{R}^{m\times n}$ for every $s\in\mathbb{N}$,
    and fix $t\in\mathbb{N}$. If $G_{t+1}G_{t+1}^{\top}\preceq c^2I$, then the preconditioners
    $L_t,L_{t+1}$ satisfy
    \[
      \operatorname{Tr}(G_{t+1}^{\top}L_t^{-1}G_{t+1})
      \le 2(\operatorname{Tr}L_{t+1}-\operatorname{Tr}L_t)
        +c^2(\operatorname{Tr}L_t^{-1}-\operatorname{Tr}L_{t+1}^{-1}).
    \] -/)
  (proof := /-- Put $A=G_{t+1}G_{t+1}^{\top}$. By
    \cref{lem:trace-sqrt-master-preconditioner-facts}, $L_t$ and $L_{t+1}$ are positive definite,
    their squares are their defining radicands, and the covariance increment is $A$. Since
    $A\succeq0$, \cref{lem:matrix-sqrt-order} gives $L_{t+1}-L_t\succeq0$, and
    \cref{lem:matrix-inverse-antitone} gives $L_t^{-1}-L_{t+1}^{-1}\succeq0$. Hence the traces
    \[
      \operatorname{Tr}((c^2I-A)(L_t^{-1}-L_{t+1}^{-1}))
      \quad\text{and}\quad
      \operatorname{Tr}((L_{t+1}-L_t)L_{t+1}^{-1}(L_{t+1}-L_t))
    \]
    are nonnegative. Expanding their sum, using
    $A=L_{t+1}^2-L_t^2$, cyclicity of trace, and the inverse identities yields exactly the
    asserted inequality. -/)
  (title := /-- One-step preconditioner trace estimate -/)
  (latexEnv := "lemma")]
lemma trace_sqrt_master_step {m n : ℕ} (Gconst : ℝ)
    (G : ℕ → Matrix (Fin m) (Fin n) ℝ) (t : ℕ) (hGconst : 0 < Gconst)
    (hbound :
      (Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) -
        G (t + 1) * (G (t + 1))ᵀ).PosSemidef) :
    ((G (t + 1))ᵀ * (preconditioner Gconst G t)⁻¹ * G (t + 1)).trace
      ≤ 2 * ((preconditioner Gconst G (t + 1)).trace -
          (preconditioner Gconst G t).trace)
        + Gconst ^ 2 * (((preconditioner Gconst G t)⁻¹).trace -
          ((preconditioner Gconst G (t + 1))⁻¹).trace) := by
  let L := preconditioner Gconst G t
  let K := preconditioner Gconst G (t + 1)
  let A := G (t + 1) * (G (t + 1))ᵀ
  have hLf := trace_sqrt_master_preconditioner_facts Gconst G t hGconst
  have hKf := trace_sqrt_master_preconditioner_facts Gconst G (t + 1) hGconst
  have hL : L.PosDef := by simpa [L] using hLf.1
  have hK : K.PosDef := by simpa [K] using hKf.1
  have hLsq : L * L =
      Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) + gradient_covariance G t := by
    simpa [L] using hLf.2
  have hKsq : K * K =
      Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) +
        gradient_covariance G (t + 1) := by
    simpa [K] using hKf.2
  have hcov : gradient_covariance G (t + 1) = gradient_covariance G t + A := by
    simp only [gradient_covariance, A]
    rw [Finset.sum_Icc_succ_top (Nat.succ_pos t)]
  have hsqdiff : K * K - L * L = A := by
    rw [hKsq, hLsq, hcov]
    abel
  have hA : A.PosSemidef := by
    simpa [A] using Matrix.posSemidef_self_mul_conjTranspose (G (t + 1))
  have hLT : Lᵀ = L := Matrix.isHermitian_iff_isSymm.mp hL.isHermitian
  have hradL :
      (Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) +
        gradient_covariance G t).PosSemidef := by
    rw [← hLsq]
    simpa [hLT] using Matrix.posSemidef_self_mul_conjTranspose L
  have hradDiff :
      ((Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) +
          gradient_covariance G (t + 1)) -
        (Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) +
          gradient_covariance G t)).PosSemidef := by
    convert hA using 1
    rw [hcov]
    abel
  have hD : (K - L).PosSemidef := by
    simpa [K, L, preconditioner] using matrix_sqrt_order
      (Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) + gradient_covariance G t)
      (Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) + gradient_covariance G (t + 1))
      hradL hradDiff
  have hInvD : (L⁻¹ - K⁻¹).PosSemidef :=
    matrix_inverse_antitone L K hL hK hD
  have hpair :
      0 ≤ ((Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) - A) *
        (L⁻¹ - K⁻¹)).trace := by
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hInvD.nonneg
    rw [hB, Matrix.star_eq_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    exact ((by simpa [A] using hbound :
      (Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) - A).PosSemidef).mul_mul_conjTranspose_same B).trace_nonneg
  have hDT : (K - L)ᵀ = K - L := Matrix.isHermitian_iff_isSymm.mp hD.isHermitian
  have hquad : 0 ≤ ((K - L) * K⁻¹ * (K - L)).trace := by
    simpa [hDT] using
      (hK.inv.posSemidef.conjTranspose_mul_mul_same (K - L)).trace_nonneg
  letI : Invertible L := hL.isUnit.invertible
  letI : Invertible K := hK.isUnit.invertible
  have hweighted :
      ((G (t + 1))ᵀ * L⁻¹ * G (t + 1)).trace = (A * L⁻¹).trace := by
    calc
      ((G (t + 1))ᵀ * L⁻¹ * G (t + 1)).trace =
          (L⁻¹ * G (t + 1) * (G (t + 1))ᵀ).trace :=
        by simpa [Matrix.mul_assoc] using
          (Matrix.trace_mul_cycle' L⁻¹ (G (t + 1)) (G (t + 1))ᵀ).symm
      _ = (L⁻¹ * A).trace := by simp [A, Matrix.mul_assoc]
      _ = (A * L⁻¹).trace := Matrix.trace_mul_comm L⁻¹ A
  have hpair' :
      0 ≤ Gconst ^ 2 * ((L⁻¹).trace - (K⁻¹).trace) -
        ((A * L⁻¹).trace - (A * K⁻¹).trace) := by
    convert hpair using 1
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul,
      Matrix.one_mul, Matrix.trace_smul]
    ring
  have htraceIdentity :
      (A * K⁻¹).trace + ((K - L) * K⁻¹ * (K - L)).trace =
        2 * (K.trace - L.trace) := by
    rw [← hsqdiff]
    have hcycle : (L * (K⁻¹ * L)).trace = (L * (L * K⁻¹)).trace :=
      Matrix.trace_mul_cycle' L K⁻¹ L
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_assoc,
      Matrix.mul_inv_of_invertible, Matrix.inv_mul_of_invertible, Matrix.mul_one,
      Matrix.one_mul]
    rw [hcycle]
    ring
  change ((G (t + 1))ᵀ * L⁻¹ * G (t + 1)).trace ≤
    2 * (K.trace - L.trace) +
      Gconst ^ 2 * ((L⁻¹).trace - (K⁻¹).trace)
  rw [hweighted]
  linarith

@[blueprint "lem:trace-sqrt-master-initial-identity"
  (statement := /-- Let $c>0$ and let $G_s\in\mathbb{R}^{m\times n}$ for every
    $s\in\mathbb{N}$. For $L_1=(c^2I+G_1G_1^{\top})^{1/2}$,
    \[
      \operatorname{Tr}L_1
      =c^2\operatorname{Tr}L_1^{-1}
        +\operatorname{Tr}(G_1^{\top}L_1^{-1}G_1).
    \] -/)
  (proof := /-- By \cref{lem:trace-sqrt-master-preconditioner-facts}, $L_1$ is positive definite
    and $L_1^2=c^2I+M_1$. The definition of the covariance gives
    $M_1=G_1G_1^{\top}$. Left multiplication by $L_1^{-1}$ therefore gives
    $L_1=c^2L_1^{-1}+L_1^{-1}G_1G_1^{\top}$. Taking traces and applying cyclicity to the last
    term proves the identity. -/)
  (title := /-- Initial preconditioner trace identity -/)
  (latexEnv := "lemma")]
lemma trace_sqrt_master_initial_identity {m n : ℕ} (Gconst : ℝ)
    (G : ℕ → Matrix (Fin m) (Fin n) ℝ) (hGconst : 0 < Gconst) :
    (preconditioner Gconst G 1).trace =
      Gconst ^ 2 * (((preconditioner Gconst G 1)⁻¹).trace) +
        ((G 1)ᵀ * (preconditioner Gconst G 1)⁻¹ * G 1).trace := by
  let L := preconditioner Gconst G 1
  let A := G 1 * (G 1)ᵀ
  have hLf := trace_sqrt_master_preconditioner_facts Gconst G 1 hGconst
  have hL : L.PosDef := by simpa [L] using hLf.1
  have hcov : gradient_covariance G 1 = A := by
    simp [gradient_covariance, A]
  have hLsq : L * L = Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) + A := by
    simpa [L, hcov] using hLf.2
  letI : Invertible L := hL.isUnit.invertible
  have hmatrix : L = Gconst ^ 2 • L⁻¹ + L⁻¹ * A := by
    calc
      L = L⁻¹ * (L * L) := by
        rw [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.one_mul]
      _ = L⁻¹ * (Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) + A) := by rw [hLsq]
      _ = Gconst ^ 2 • L⁻¹ + L⁻¹ * A := by
        simp [Matrix.mul_add, Matrix.mul_smul]
  have hweighted :
      ((G 1)ᵀ * L⁻¹ * G 1).trace = (L⁻¹ * A).trace := by
    calc
      ((G 1)ᵀ * L⁻¹ * G 1).trace = (L⁻¹ * G 1 * (G 1)ᵀ).trace :=
        by simpa [Matrix.mul_assoc] using
          (Matrix.trace_mul_cycle' L⁻¹ (G 1) (G 1)ᵀ).symm
      _ = (L⁻¹ * A).trace := by simp [A, Matrix.mul_assoc]
  change L.trace = Gconst ^ 2 * (L⁻¹).trace + ((G 1)ᵀ * L⁻¹ * G 1).trace
  calc
    L.trace = (Gconst ^ 2 • L⁻¹ + L⁻¹ * A).trace := congrArg Matrix.trace hmatrix
    _ = Gconst ^ 2 * (L⁻¹).trace + (L⁻¹ * A).trace := by
      simp [Matrix.trace_add, Matrix.trace_smul]
    _ = Gconst ^ 2 * (L⁻¹).trace + ((G 1)ᵀ * L⁻¹ * G 1).trace := by rw [hweighted]

@[blueprint "lem:trace-sqrt-master-strong"
  (statement := /-- Let $G_1,\ldots,G_T\in\mathbb{R}^{m\times n}$, where $T\ge1$, and suppose
    $G_tG_t^{\top}\preceq c^2I$ for every $1\le t\le T$, with $c>0$. For the preconditioners
    $L_t=(c^2I+\sum_{s=1}^tG_sG_s^{\top})^{1/2}$,
    \[
      \sum_{t=1}^{T-1}\operatorname{Tr}(G_{t+1}^{\top}L_t^{-1}G_{t+1})
      +\operatorname{Tr}L_1
      +\operatorname{Tr}(G_1^{\top}L_1^{-1}G_1)
      +c^2\operatorname{Tr}L_T^{-1}
      \le 2\operatorname{Tr}L_T.
    \] -/)
  (proof := /-- The proof is by induction on the nonempty horizon. At $T=1$, the sum is empty
    and \cref{lem:trace-sqrt-master-initial-identity} makes the left-hand side equal to
    $2\operatorname{Tr}L_1$. For the induction step, split the last summand, whose index is
    $t=T-1$. The estimate \cref{lem:trace-sqrt-master-step} bounds it by the increment
    $2(\operatorname{Tr}L_T-\operatorname{Tr}L_{T-1})$ plus
    $c^2(\operatorname{Tr}L_{T-1}^{-1}-\operatorname{Tr}L_T^{-1})$. Adding this to the induction
    hypothesis cancels both previous terminal terms and proves the displayed strengthened
    inequality. -/)
  (title := /-- Strengthened trace-square-root master inequality -/)
  (latexEnv := "lemma")]
lemma trace_sqrt_master_strong {m n : ℕ} (Gconst : ℝ)
    (G : ℕ → Matrix (Fin m) (Fin n) ℝ) (T : ℕ)
    (hGconst : 0 < Gconst) (hT : 1 ≤ T)
    (hbound : ∀ t, 1 ≤ t → t ≤ T →
      (Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) - G t * (G t)ᵀ).PosSemidef) :
    (∑ t ∈ Finset.Icc 1 (T - 1),
        ((G (t + 1))ᵀ * (preconditioner Gconst G t)⁻¹ * G (t + 1)).trace)
      + (preconditioner Gconst G 1).trace
      + ((G 1)ᵀ * (preconditioner Gconst G 1)⁻¹ * G 1).trace
      + Gconst ^ 2 * (((preconditioner Gconst G T)⁻¹).trace)
      ≤ 2 * (preconditioner Gconst G T).trace := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one.mpr hT
  clear hT
  revert hbound
  induction k with
  | zero =>
      intro hbound
      have hinit := trace_sqrt_master_initial_identity Gconst G hGconst
      simp
      linarith
  | succ k ih =>
      intro hbound
      have hprevBound : ∀ t, 1 ≤ t → t ≤ k + 1 →
          (Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) -
            G t * (G t)ᵀ).PosSemidef := by
        intro t ht htk
        exact hbound t ht (by omega)
      have hih := ih hprevBound
      have hnewBound :
          (Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) -
            G ((k + 1) + 1) * (G ((k + 1) + 1))ᵀ).PosSemidef :=
        hbound ((k + 1) + 1) (by omega) (by omega)
      have hstep := trace_sqrt_master_step Gconst G (k + 1) hGconst hnewBound
      have hsum :
          (∑ t ∈ Finset.Icc 1 (((k + 1) + 1) - 1),
              ((G (t + 1))ᵀ * (preconditioner Gconst G t)⁻¹ * G (t + 1)).trace) =
            (∑ t ∈ Finset.Icc 1 ((k + 1) - 1),
              ((G (t + 1))ᵀ * (preconditioner Gconst G t)⁻¹ * G (t + 1)).trace) +
              ((G ((k + 1) + 1))ᵀ * (preconditioner Gconst G (k + 1))⁻¹ *
                G ((k + 1) + 1)).trace := by
        simpa only [Nat.add_sub_cancel] using Finset.sum_Icc_succ_top (Nat.succ_pos k)
          (fun t => ((G (t + 1))ᵀ * (preconditioner Gconst G t)⁻¹ * G (t + 1)).trace)
      rw [hsum]
      linarith

@[blueprint "lem:trace-sqrt-master"
  (statement := /-- Let $G_1,\ldots,G_T\in\mathbb{R}^{m\times n}$, where $T\ge1$, and suppose
    $G_tG_t^{\top}\preceq c^2I$ for every $1\le t\le T$, with $c>0$. Define
    $L_t=(c^2I+\sum_{s=1}^tG_sG_s^{\top})^{1/2}$ as in
    \cref{def:preconditioner}. Then
    \[
      \sum_{t=1}^{T-1}\operatorname{Tr}(G_{t+1}^{\top}L_t^{-1}G_{t+1})
      +\operatorname{Tr}L_1
      +\operatorname{Tr}(G_1^{\top}L_1^{-1}G_1)
      \le 2\operatorname{Tr}L_T .
    \] -/)
  (proof := /-- By \cref{lem:trace-sqrt-master-strong}, the left-hand side in the statement plus
    $c^2\operatorname{Tr}L_T^{-1}$ is at most $2\operatorname{Tr}L_T$. The positivity assertion in
    \cref{lem:trace-sqrt-master-preconditioner-facts} shows that $L_T$ is positive definite.
    Hence $L_T^{-1}$ is positive semidefinite and has nonnegative trace. Since $c^2\ge0$, the
    additional term is nonnegative, and discarding it proves the stated inequality. -/)
  (title := /-- Trace-square-root master inequality -/)
  (latexEnv := "lemma")]
lemma trace_sqrt_master {m n : ℕ} (Gconst : ℝ)
    (G : ℕ → Matrix (Fin m) (Fin n) ℝ) (T : ℕ)
    (hGconst : 0 < Gconst) (hT : 1 ≤ T)
    (hbound : ∀ t, 1 ≤ t → t ≤ T →
      (Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) - G t * (G t)ᵀ).PosSemidef) :
    (∑ t ∈ Finset.Icc 1 (T - 1),
        ((G (t + 1))ᵀ * (preconditioner Gconst G t)⁻¹ * G (t + 1)).trace)
      + (preconditioner Gconst G 1).trace
      + ((G 1)ᵀ * (preconditioner Gconst G 1)⁻¹ * G 1).trace
      ≤ 2 * (preconditioner Gconst G T).trace := by
  have hstrong := trace_sqrt_master_strong Gconst G T hGconst hT hbound
  have hLT := (trace_sqrt_master_preconditioner_facts Gconst G T hGconst).1
  have hinvTrace : 0 ≤ (((preconditioner Gconst G T)⁻¹).trace) :=
    hLT.inv.posSemidef.trace_nonneg
  have hcorrection :
      0 ≤ Gconst ^ 2 * (((preconditioner Gconst G T)⁻¹).trace) :=
    mul_nonneg (sq_nonneg Gconst) hinvTrace
  linarith

@[blueprint "lem:initial-nuclear-weighted-square"
  (statement := /-- Let $\mathcal{S}$ be an admissible smoothing
    (\cref{def:admissible-smoothing}), let $A\in\mathbb{R}^{m\times n}$, and let
    $L\in\mathbb{R}^{m\times m}$ be positive definite. Then
    \[
      2\|A\|_*\le
      \operatorname{Tr}L+\operatorname{Tr}(A^{\top}L^{-1}A).
    \] -/)
  (proof := /-- If $m=0$, the nuclear-normalization clause of
    \cref{def:admissible-smoothing} and the definitions of matrix multiplication and trace reduce
    both sides to zero. Assume henceforth that $m>0$. Positive definiteness of $L$ implies
    $\operatorname{Tr}L>0$, while positive definiteness of $L^{-1}$ implies
    $\operatorname{Tr}(A^{\top}L^{-1}A)\ge0$.

    Let $V$ be the set of values $\langle A,Y\rangle$ with
    $\|Y\|_{\mathrm{op}}\le1$, where the pairing is that of
    \cref{def:matrix-inner-product}. The duality clause of
    \cref{def:admissible-smoothing} gives
    $\inf V=-\|A\|_*$. If $V$ is empty, then its infimum is zero, so $\|A\|_*=0$ and the result
    follows from the preceding nonnegativity.

    Suppose that $V$ is nonempty and fix $Y$ with $\|Y\|_{\mathrm{op}}\le1$. Operator
    normalization in \cref{def:admissible-smoothing} gives $I-YY^{\top}\succeq0$.
    Factoring this positive-semidefinite matrix as $B^{\top}B$, applying congruence by $B$ to
    $L\succeq0$, and using cyclicity of trace yields
    \[
      0\le\operatorname{Tr}\bigl(L(I-YY^{\top})\bigr)
      =\operatorname{Tr}L-\operatorname{Tr}(Y^{\top}LY).
    \]
    Congruence of $L\succeq0$ by $L^{-1}A+Y$ likewise gives
    \[
      0\le
      \operatorname{Tr}(A^{\top}L^{-1}A)
      +2\langle A,Y\rangle
      +\operatorname{Tr}(Y^{\top}LY).
    \]
    Consequently every element of $V$ is at least
    $-\bigl(\operatorname{Tr}L+\operatorname{Tr}(A^{\top}L^{-1}A)\bigr)/2$.
    Taking the infimum and substituting $\inf V=-\|A\|_*$ proves the asserted inequality. -/)
  (title := /-- Weighted Frobenius bound for the initial nuclear norm -/)
  (latexEnv := "lemma")]
lemma initial_nuclear_weighted_square {m n : ℕ} (S : admissible_smoothing m n)
    (A : Matrix (Fin m) (Fin n) ℝ) (L : Matrix (Fin m) (Fin m) ℝ)
    (hL : L.PosDef) :
    2 * S.nucNorm A ≤ L.trace + (Aᵀ * L⁻¹ * A).trace := by
  by_cases hm : m = 0
  · subst m
    simp [S.nucNorm_normalization]
  letI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
  letI : Invertible L := hL.isUnit.invertible
  have hterm : 0 ≤ (Aᵀ * L⁻¹ * A).trace := by
    exact (hL.inv.posSemidef.conjTranspose_mul_mul_same A).trace_nonneg
  have hrhs : 0 ≤ L.trace + (Aᵀ * L⁻¹ * A).trace :=
    add_nonneg (le_of_lt hL.trace_pos) hterm
  let values : Set ℝ :=
    (fun Y => matrix_inner_product A Y) ''
      {Y : Matrix (Fin m) (Fin n) ℝ | S.opNorm Y ≤ 1}
  have hdual : sInf values = -S.nucNorm A := by
    simpa [values] using S.nucNorm_dual A 1 (by norm_num)
  by_cases hvalues : values.Nonempty
  · have hinf :
        -(L.trace + (Aᵀ * L⁻¹ * A).trace) / 2 ≤ sInf values := by
      apply le_csInf hvalues
      intro z hz
      rcases hz with ⟨Y, hY, rfl⟩
      have hYY : ((1 : Matrix (Fin m) (Fin m) ℝ) - Y * Yᵀ).PosSemidef := by
        simpa using S.opNorm_normalization Y 1 hY
      have htrace_nonneg :
          0 ≤ (L * ((1 : Matrix (Fin m) (Fin m) ℝ) - Y * Yᵀ)).trace := by
        obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hYY.nonneg
        rw [hB, Matrix.star_eq_conjTranspose, ← Matrix.mul_assoc,
          Matrix.trace_mul_cycle]
        exact (hL.posSemidef.mul_mul_conjTranspose_same B).trace_nonneg
      have htrace : (Yᵀ * L * Y).trace ≤ L.trace := by
        have hrewrite :
            (L * ((1 : Matrix (Fin m) (Fin m) ℝ) - Y * Yᵀ)).trace =
              L.trace - (Yᵀ * L * Y).trace := by
          simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub]
          rw [Matrix.trace_mul_cycle' L Y Yᵀ]
          rw [Matrix.mul_assoc]
        rw [hrewrite] at htrace_nonneg
        linarith
      have hquad_nonneg :
          0 ≤ ((L⁻¹ * A + Y)ᵀ * L * (L⁻¹ * A + Y)).trace := by
        exact
          (hL.posSemidef.conjTranspose_mul_mul_same (L⁻¹ * A + Y)).trace_nonneg
      have hLT : Lᵀ = L := by
        simpa using hL.1.eq
      have hinv_mul (B : Matrix (Fin m) (Fin n) ℝ) : L⁻¹ * (L * B) = B := by
        rw [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.one_mul]
      have hmul_inv (B : Matrix (Fin m) (Fin n) ℝ) : L * (L⁻¹ * B) = B := by
        rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]
      have hinner_symm : (Yᵀ * A).trace = (Aᵀ * Y).trace := by
        calc
          (Yᵀ * A).trace = ((Yᵀ * A)ᵀ).trace :=
            (Matrix.trace_transpose (Yᵀ * A)).symm
          _ = (Aᵀ * Y).trace := by simp
      have hquad :
          0 ≤ (Aᵀ * L⁻¹ * A).trace +
              2 * matrix_inner_product A Y + (Yᵀ * L * Y).trace := by
        convert hquad_nonneg using 1
        simp only [Matrix.transpose_add, Matrix.transpose_mul,
          Matrix.transpose_nonsing_inv, hLT, Matrix.mul_add,
          Matrix.add_mul, Matrix.trace_add, Matrix.mul_assoc, hinv_mul,
          hmul_inv, matrix_inner_product]
        rw [hinner_symm]
        ring
      linarith
    rw [hdual] at hinf
    linarith
  · have hempty : values = ∅ := by
      exact Set.not_nonempty_iff_eq_empty.mp hvalues
    rw [hempty, Real.sInf_empty] at hdual
    linarith

@[blueprint "lem:adagrad-trace-sum"
  (statement := /-- Let $\mathcal{S}$ be an admissible smoothing
    (\cref{def:admissible-smoothing}) and let $(G,X,D,G_{\max},T)$ be a GBPA run
    (\cref{def:gbpa-run}) with $G_{\max}>0$. For the preconditioners
    $L_t=(G_{\max}^2I+M_t)^{1/2}$ of \cref{def:preconditioner},
    \[
      \sum_{t=1}^{T-1}\operatorname{Tr}(G_{t+1}^{\top}L_t^{-1}G_{t+1})
      \le 2\bigl(\operatorname{Tr}L_T-\|G_1\|_*\bigr).
    \] -/)
  (proof := /-- For each $1\le t\le T$, the gradient bound from
    \cref{def:gbpa-run} and the operator normalization in
    \cref{def:admissible-smoothing} give
    $G_tG_t^{\top}\preceq G_{\max}^2I$. Thus
    \cref{lem:trace-sqrt-master} applies and bounds the displayed sum plus
    $\operatorname{Tr}L_1+\operatorname{Tr}(G_1^{\top}L_1^{-1}G_1)$ by
    $2\operatorname{Tr}L_T$. Since $G_{\max}>0$,
    \cref{lem:trace-sqrt-master-preconditioner-facts} shows that $L_1$ is positive definite, and
    \cref{lem:initial-nuclear-weighted-square} bounds that pair of initial trace terms below by
    $2\|G_1\|_*$. Subtracting this lower bound proves the assertion. -/)
  (title := /-- Full-matrix AdaGrad trace estimate -/)
  (latexEnv := "lemma")]
lemma adagrad_trace_sum {m n : ℕ} (S : admissible_smoothing m n) (run : gbpa_run S)
    (hGconst : 0 < run.Gconst) :
    (∑ t ∈ Finset.Icc 1 (run.T - 1),
        ((run.G (t + 1))ᵀ * (preconditioner run.Gconst run.G t)⁻¹
          * run.G (t + 1)).trace)
      ≤ 2 * ((preconditioner run.Gconst run.G run.T).trace - S.nucNorm (run.G 1)) := by
  have hmaster :=
    trace_sqrt_master run.Gconst run.G run.T hGconst run.T_pos
      (fun t ht htle =>
        S.opNorm_normalization (run.G t) run.Gconst (run.grad_bound t ht htle))
  have hpositive :=
    (trace_sqrt_master_preconditioner_facts run.Gconst run.G 1 hGconst).1
  have hinitial :=
    initial_nuclear_weighted_square S (run.G 1)
      (preconditioner run.Gconst run.G 1) hpositive
  linarith

@[blueprint "thm:main"
  (statement := /-- Fix $m,n\in\mathbb{N}$. Let $\mathcal{S}$ be an
    $(\alpha, \beta)$-admissible smoothing of the nuclear norm on
    $\mathbb{R}^{m\times n}$ (\cref{def:admissible-smoothing}), where $\alpha,\beta>0$, and let
    $(G, X, D, G_{\max}, T)$ be a GBPA run for $\mathcal{S}$ (\cref{def:gbpa-run}). Thus
    $D>0$, $G_{\max}\ge 0$, $T\ge 1$, $\|G_t\|_{\mathrm{op}} \le G_{\max}$ for every
    $1 \le t \le T$, and $X_1 = 0$. Moreover, for every $1\le t<T$,
    $X_{t+1} = -D\,\mathsf{g}(S_t; L_t / \eta)$, where $\mathsf{g}$ is the field from
    \cref{def:admissible-smoothing},
    $L_t = (G_{\max}^2 I + M_t)^{1/2}$ (\cref{def:preconditioner}) and $\eta = \sqrt{\alpha / \beta}$
    (\cref{def:learning-rate}). Then the regret (\cref{def:regret}) satisfies
    $\mathrm{Reg}_T \le 2\sqrt{\alpha\beta}\, D \, \operatorname{Tr}\!\bigl((G_{\max}^2 I + M_T)^{1/2}\bigr)
    + (1 - \sqrt{\alpha\beta})\, D \, \|G_1\|_{*}$. -/)
  (proof := /-- First suppose that $G_{\max}=0$. The gradient bound in
    \cref{def:gbpa-run}, together with the operator normalization in
    \cref{def:admissible-smoothing}, implies $G_tG_t^{\top}=0$ and hence $G_t=0$ for every
    $1\le t\le T$. Thus every incurred loss and every comparator loss is zero, so the regret is zero;
    the two terms on the asserted right-hand side are also zero. We may therefore assume
    $G_{\max}>0$. Since $M_t$ is positive semidefinite, $G_{\max}^2I+M_t$ is positive definite, and
    so is its positive semidefinite square root $L_t$. Moreover, $\alpha,\beta>0$ gives $\eta>0$.
    Consequently $L_t/\eta\succ0$ for every $1\le t\le T$, and the field $\mathsf{g}$ used by the
    updates is the Fréchet gradient certified in \cref{def:admissible-smoothing}; the positive
    definiteness and square identity used here are precisely
    \cref{lem:trace-sqrt-master-preconditioner-facts}.

    By \cref{lem:gbpa-decomposition} the regret equals
    $D(\Phi(S_T)-\widetilde{\Phi}_T(S_T))
    +D\sum_{t=1}^{T-1}B_{\widetilde{\Phi}_t}(S_{t+1},S_t)
    +D\sum_{t=1}^{T-1}(\widetilde{\Phi}_{t+1}(S_{t+1})
      -\widetilde{\Phi}_t(S_{t+1}))
    +D\,\widetilde{\Phi}_1(G_1)$, where
    $\widetilde{\Phi}_t(\cdot)=\widetilde{\Psi}(\cdot;L_t/\eta)$ and
    $\Phi(\cdot)=\|\cdot\|_*$. We bound these four terms separately. Dominance gives
    $\widetilde{\Phi}_T(S_T)\ge\|S_T\|_*=\Phi(S_T)$, so the terminal gap is nonpositive.

    Since $M_t\preceq M_{t+1}$, \cref{lem:matrix-sqrt-order} gives
    $L_t\preceq L_{t+1}$ and therefore $L_t/\eta\preceq L_{t+1}/\eta$. Upper stability bounds the
    potential-parameter increment at round $t$ by
    $\frac{\alpha}{\eta}(\operatorname{Tr}L_{t+1}-\operatorname{Tr}L_t)$. The sum telescopes to
    $\frac{\alpha}{\eta}(\operatorname{Tr}L_T-\operatorname{Tr}L_1)$. Upper stability between
    $0$ and $L_1/\eta$, followed by dominance at zero, also gives
    $\widetilde{\Phi}_1(G_1)\le\|G_1\|_*+
    \frac{\alpha}{\eta}\operatorname{Tr}L_1$. Thus the potential-increment and initial terms
    together are at most
    $\frac{\alpha}{\eta}\operatorname{Tr}L_T+\|G_1\|_*$.

    Smoothness at the positive definite parameter $L_t/\eta$, with
    $S_{t+1}-S_t=G_{t+1}$, gives
    \[
      B_{\widetilde{\Phi}_t}(S_{t+1},S_t)
      \le\frac{\beta\eta}{2}
        \operatorname{Tr}(G_{t+1}^{\top}L_t^{-1}G_{t+1}).
    \]
    Applying \cref{lem:adagrad-trace-sum} and summing shows that all Bregman terms together are at
    most $\beta\eta(\operatorname{Tr}L_T-\|G_1\|_*)$. Since $D>0$, multiplication by $D$ preserves
    every preceding inequality. Adding the four bounds gives
    \[
      \mathrm{Reg}_T\le D\left[
        \left(\frac{\alpha}{\eta}+\beta\eta\right)\operatorname{Tr}L_T
        +(1-\beta\eta)\|G_1\|_*\right].
    \]
    Finally, $\alpha,\beta>0$ and $\eta=\sqrt{\alpha/\beta}$ imply
    $\alpha/\eta=\beta\eta=\sqrt{\alpha\beta}$. Substitution is exactly
    $\mathrm{Reg}_T \le 2\sqrt{\alpha\beta}\,D\,\operatorname{Tr}L_T
    +(1-\sqrt{\alpha\beta})D\|G_1\|_*$, as required. -/)
  (title := /-- Regret of GBPA with admissible smoothing -/)
  (latexEnv := "theorem")]
theorem main {m n : ℕ} (S : admissible_smoothing m n) (run : gbpa_run S) :
    regret S.opNorm run.G run.X run.D run.T ≤
      2 * Real.sqrt (S.alpha * S.beta) * run.D
          * (preconditioner run.Gconst run.G run.T).trace
      + (1 - Real.sqrt (S.alpha * S.beta)) * run.D * S.nucNorm (run.G 1) := by
  rcases eq_or_lt_of_le run.Gconst_nonneg with hGzero | hGpos
  · have hgrad : ∀ t, 1 ≤ t → t ≤ run.T → run.G t = 0 := by
      intro t ht htT
      have hneg := S.opNorm_normalization (run.G t) 0
        (by simpa [hGzero] using run.grad_bound t ht htT)
      have hpos : (run.G t * (run.G t)ᵀ).PosSemidef :=
        by simpa using Matrix.posSemidef_self_mul_conjTranspose (run.G t)
      have hmul : run.G t * (run.G t)ᵀ = 0 :=
        le_antisymm (neg_nonneg.mp (by simpa using hneg.nonneg)) hpos.nonneg
      exact Matrix.self_mul_conjTranspose_eq_zero.mp (by simpa using hmul)
    have hG1 : run.G 1 = 0 := hgrad 1 (by omega) run.T_pos
    have hnuc0 : S.nucNorm (0 : Matrix (Fin m) (Fin n) ℝ) = 0 := by
      rw [S.nucNorm_normalization]
      simp
    have hloss :
        (∑ t ∈ Finset.Icc 1 run.T,
          matrix_inner_product (run.G t) (run.X t)) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      rw [hgrad t (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2]
      simp [matrix_inner_product]
    have hsum_zero (Y : Matrix (Fin m) (Fin n) ℝ) :
        (∑ t ∈ Finset.Icc 1 run.T, matrix_inner_product (run.G t) Y) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      rw [hgrad t (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2]
      simp [matrix_inner_product]
    have hcomp :
        (fun Y : Matrix (Fin m) (Fin n) ℝ =>
          ∑ t ∈ Finset.Icc 1 run.T, matrix_inner_product (run.G t) Y) =
        (fun Y => matrix_inner_product (0 : Matrix (Fin m) (Fin n) ℝ) Y) := by
      funext Y
      rw [hsum_zero Y]
      simp [matrix_inner_product]
    have hsinf :=
      S.nucNorm_dual (0 : Matrix (Fin m) (Fin n) ℝ) run.D (le_of_lt run.D_pos)
    have hreg : regret S.opNorm run.G run.X run.D run.T = 0 := by
      rw [regret, hloss, hcomp, hsinf, hnuc0]
      ring
    have hcov : gradient_covariance run.G run.T = 0 := by
      rw [gradient_covariance]
      apply Finset.sum_eq_zero
      intro t ht
      rw [hgrad t (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2]
      simp
    have hpre : preconditioner run.Gconst run.G run.T = 0 := by
      rw [← hGzero]
      simp [preconditioner, hcov]
    rw [hreg, hpre, hG1, hnuc0]
    norm_num
  · let η := learning_rate S.alpha S.beta
    have hη : 0 < η := by
      exact Real.sqrt_pos.2 (div_pos S.alpha_pos S.beta_pos)
    have hηne : η ≠ 0 := ne_of_gt hη
    have hηsq : η ^ 2 = S.alpha / S.beta := by
      exact Real.sq_sqrt (le_of_lt (div_pos S.alpha_pos S.beta_pos))
    have hab : S.alpha = S.beta * η ^ 2 := by
      calc
        S.alpha = S.beta * (S.alpha / S.beta) := by
          field_simp [ne_of_gt S.beta_pos]
        _ = S.beta * η ^ 2 := by rw [hηsq]
    have hcoeff : S.alpha / η = S.beta * η := by
      rw [hab]
      field_simp [hηne]
    have hβηsq : (S.beta * η) ^ 2 = S.alpha * S.beta := by
      calc
        (S.beta * η) ^ 2 = S.beta * (S.beta * η ^ 2) := by ring
        _ = S.beta * S.alpha := by rw [← hab]
        _ = S.alpha * S.beta := by ring
    have hβη : S.beta * η = Real.sqrt (S.alpha * S.beta) := by
      calc
        S.beta * η = |S.beta * η| := (abs_of_pos (mul_pos S.beta_pos hη)).symm
        _ = Real.sqrt ((S.beta * η) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ = Real.sqrt (S.alpha * S.beta) := by rw [hβηsq]
    have hLpos (t : ℕ) : (preconditioner run.Gconst run.G t).PosDef :=
      (trace_sqrt_master_preconditioner_facts run.Gconst run.G t hGpos).1
    have hscaledPos (t : ℕ) :
        (η⁻¹ • preconditioner run.Gconst run.G t).PosDef :=
      (hLpos t).smul (inv_pos.mpr hη)
    have hterminal :
        S.nucNorm (cumulative_gradient run.G run.T) -
            S.pot (cumulative_gradient run.G run.T)
              (η⁻¹ • preconditioner run.Gconst run.G run.T) ≤ 0 := by
      have hdom := S.dominance_ge (cumulative_gradient run.G run.T)
        (η⁻¹ • preconditioner run.Gconst run.G run.T)
        (hscaledPos run.T).posSemidef
      linarith
    have hcovPos (t : ℕ) : (gradient_covariance run.G t).PosSemidef := by
      rw [gradient_covariance]
      exact Matrix.posSemidef_sum _ (fun s _ => by
        simpa using Matrix.posSemidef_self_mul_conjTranspose (run.G s))
    have hradPos (t : ℕ) :
        (run.Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) +
          gradient_covariance run.G t).PosSemidef :=
      (Matrix.PosSemidef.one.smul (sq_nonneg run.Gconst)).add (hcovPos t)
    have hcov_succ (t : ℕ) (ht : 1 ≤ t) :
        gradient_covariance run.G (t + 1) =
          gradient_covariance run.G t + run.G (t + 1) * (run.G (t + 1))ᵀ := by
      simp [gradient_covariance, Finset.sum_Icc_succ_top, ht]
    have hradDiff (t : ℕ) (ht : 1 ≤ t) :
        ((run.Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) +
              gradient_covariance run.G (t + 1)) -
            (run.Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) +
              gradient_covariance run.G t)).PosSemidef := by
      rw [hcov_succ t ht]
      have hself :
          (run.G (t + 1) * (run.G (t + 1))ᵀ).PosSemidef := by
        simpa using Matrix.posSemidef_self_mul_conjTranspose (run.G (t + 1))
      convert hself using 1 <;> module
    have hLdiff (t : ℕ) (ht : 1 ≤ t) :
        (preconditioner run.Gconst run.G (t + 1) -
          preconditioner run.Gconst run.G t).PosSemidef := by
      simpa [preconditioner] using
        matrix_sqrt_order
          (run.Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) +
            gradient_covariance run.G t)
          (run.Gconst ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) +
            gradient_covariance run.G (t + 1))
          (hradPos t) (hradDiff t ht)
    have hscaledDiff (t : ℕ) (ht : 1 ≤ t) :
        (η⁻¹ • preconditioner run.Gconst run.G (t + 1) -
          η⁻¹ • preconditioner run.Gconst run.G t).PosSemidef := by
      have h := (hLdiff t ht).smul (le_of_lt (inv_pos.mpr hη))
      convert h using 1 <;> module
    have hpotstep (t : ℕ) (ht : 1 ≤ t) :
        S.pot (cumulative_gradient run.G (t + 1))
              (η⁻¹ • preconditioner run.Gconst run.G (t + 1)) -
            S.pot (cumulative_gradient run.G (t + 1))
              (η⁻¹ • preconditioner run.Gconst run.G t)
          ≤ S.alpha * η⁻¹ *
              ((preconditioner run.Gconst run.G (t + 1)).trace -
                (preconditioner run.Gconst run.G t).trace) := by
      have h := S.upper_stability (cumulative_gradient run.G (t + 1))
        (η⁻¹ • preconditioner run.Gconst run.G t)
        (η⁻¹ • preconditioner run.Gconst run.G (t + 1))
        (hscaledPos t).posSemidef (hscaledDiff t ht)
      rw [Matrix.trace_smul, Matrix.trace_smul] at h
      convert h using 1 <;> ring
    have tele (f : ℕ → ℝ) (N : ℕ) :
        (∑ t ∈ Finset.Icc 1 N, (f (t + 1) - f t)) = f (N + 1) - f 1 := by
      induction N with
      | zero =>
          simp [Finset.Icc_eq_empty (by omega : ¬ (1 : ℕ) ≤ 0)]
      | succ k ih =>
          rw [Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ k + 1 by omega), ih]
          ring
    have hpotSum :
        (∑ t ∈ Finset.Icc 1 (run.T - 1),
          (S.pot (cumulative_gradient run.G (t + 1))
                (η⁻¹ • preconditioner run.Gconst run.G (t + 1)) -
            S.pot (cumulative_gradient run.G (t + 1))
                (η⁻¹ • preconditioner run.Gconst run.G t)))
          ≤ S.alpha * η⁻¹ *
              ((preconditioner run.Gconst run.G run.T).trace -
                (preconditioner run.Gconst run.G 1).trace) := by
      calc
        (∑ t ∈ Finset.Icc 1 (run.T - 1),
            (S.pot (cumulative_gradient run.G (t + 1))
                  (η⁻¹ • preconditioner run.Gconst run.G (t + 1)) -
              S.pot (cumulative_gradient run.G (t + 1))
                  (η⁻¹ • preconditioner run.Gconst run.G t)))
            ≤ ∑ t ∈ Finset.Icc 1 (run.T - 1),
                S.alpha * η⁻¹ *
                  ((preconditioner run.Gconst run.G (t + 1)).trace -
                    (preconditioner run.Gconst run.G t).trace) := by
              exact Finset.sum_le_sum (fun t ht =>
                hpotstep t (Finset.mem_Icc.mp ht).1)
        _ = S.alpha * η⁻¹ *
              (∑ t ∈ Finset.Icc 1 (run.T - 1),
                ((preconditioner run.Gconst run.G (t + 1)).trace -
                  (preconditioner run.Gconst run.G t).trace)) := by
              rw [Finset.mul_sum]
        _ = S.alpha * η⁻¹ *
              ((preconditioner run.Gconst run.G run.T).trace -
                (preconditioner run.Gconst run.G 1).trace) := by
              rw [tele
                (fun t => (preconditioner run.Gconst run.G t).trace)
                (run.T - 1), Nat.sub_add_cancel run.T_pos]
    have hinitial :
        S.pot (run.G 1) (η⁻¹ • preconditioner run.Gconst run.G 1)
          ≤ S.nucNorm (run.G 1) +
              S.alpha * η⁻¹ * (preconditioner run.Gconst run.G 1).trace := by
      have h := S.upper_stability (run.G 1)
        (0 : Matrix (Fin m) (Fin m) ℝ)
        (η⁻¹ • preconditioner run.Gconst run.G 1)
        Matrix.PosSemidef.zero (by simpa using (hscaledPos 1).posSemidef)
      rw [S.dominance_zero, Matrix.trace_smul] at h
      rw [Matrix.trace_zero, sub_zero, smul_eq_mul] at h
      nlinarith
    have hinvScaled (t : ℕ) :
        (η⁻¹ • preconditioner run.Gconst run.G t)⁻¹ =
          η • (preconditioner run.Gconst run.G t)⁻¹ := by
      letI : Invertible (η⁻¹) := invertibleOfNonzero (inv_ne_zero hηne)
      have hdet : IsUnit (preconditioner run.Gconst run.G t).det :=
        (Matrix.isUnit_iff_isUnit_det
          (A := preconditioner run.Gconst run.G t)).mp (hLpos t).isUnit
      rw [Matrix.inv_smul
        (A := preconditioner run.Gconst run.G t) (η⁻¹) hdet]
      simp [inv_inv]
    have hcumDiff (t : ℕ) (ht : 1 ≤ t) :
        cumulative_gradient run.G t - cumulative_gradient run.G (t + 1) =
          -run.G (t + 1) := by
      simp only [cumulative_gradient]
      rw [Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ t + 1 by omega)]
      abel
    have hbregStep (t : ℕ) (ht : 1 ≤ t) :
        bregman_divergence
            (fun Z => S.pot Z (η⁻¹ • preconditioner run.Gconst run.G t))
            (fun Z => S.gradPot Z (η⁻¹ • preconditioner run.Gconst run.G t))
            (cumulative_gradient run.G (t + 1)) (cumulative_gradient run.G t)
          ≤ (S.beta * η / 2) *
              ((run.G (t + 1))ᵀ * (preconditioner run.Gconst run.G t)⁻¹ *
                run.G (t + 1)).trace := by
      have h := S.smoothness (cumulative_gradient run.G t)
        (cumulative_gradient run.G (t + 1))
        (η⁻¹ • preconditioner run.Gconst run.G t) (hscaledPos t)
      rw [hcumDiff t ht, hinvScaled t] at h
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul] at h
      have hneg :
          (-(run.G (t + 1))ᵀ * (preconditioner run.Gconst run.G t)⁻¹ *
              -run.G (t + 1)) =
            (run.G (t + 1))ᵀ * (preconditioner run.Gconst run.G t)⁻¹ *
              run.G (t + 1) := by
        rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_mul]
        exact neg_neg
          ((run.G (t + 1))ᵀ * (preconditioner run.Gconst run.G t)⁻¹ *
            run.G (t + 1))
      rw [Matrix.transpose_neg, hneg, smul_eq_mul] at h
      nlinarith
    have hadagrad := adagrad_trace_sum S run hGpos
    have hcoefNonneg : 0 ≤ S.beta * η / 2 :=
      le_of_lt (div_pos (mul_pos S.beta_pos hη) (by norm_num))
    have hbregSum :
        (∑ t ∈ Finset.Icc 1 (run.T - 1),
          bregman_divergence
            (fun Z => S.pot Z (η⁻¹ • preconditioner run.Gconst run.G t))
            (fun Z => S.gradPot Z (η⁻¹ • preconditioner run.Gconst run.G t))
            (cumulative_gradient run.G (t + 1)) (cumulative_gradient run.G t))
          ≤ S.beta * η *
              ((preconditioner run.Gconst run.G run.T).trace -
                S.nucNorm (run.G 1)) := by
      calc
        (∑ t ∈ Finset.Icc 1 (run.T - 1),
          bregman_divergence
            (fun Z => S.pot Z (η⁻¹ • preconditioner run.Gconst run.G t))
            (fun Z => S.gradPot Z (η⁻¹ • preconditioner run.Gconst run.G t))
            (cumulative_gradient run.G (t + 1)) (cumulative_gradient run.G t))
            ≤ ∑ t ∈ Finset.Icc 1 (run.T - 1),
                (S.beta * η / 2) *
                  ((run.G (t + 1))ᵀ * (preconditioner run.Gconst run.G t)⁻¹ *
                    run.G (t + 1)).trace := by
              exact Finset.sum_le_sum (fun t ht =>
                hbregStep t (Finset.mem_Icc.mp ht).1)
        _ = (S.beta * η / 2) *
              (∑ t ∈ Finset.Icc 1 (run.T - 1),
                ((run.G (t + 1))ᵀ * (preconditioner run.Gconst run.G t)⁻¹ *
                  run.G (t + 1)).trace) := by
              rw [Finset.mul_sum]
        _ ≤ (S.beta * η / 2) *
              (2 * ((preconditioner run.Gconst run.G run.T).trace -
                S.nucNorm (run.G 1))) :=
              mul_le_mul_of_nonneg_left hadagrad hcoefNonneg
        _ = S.beta * η *
              ((preconditioner run.Gconst run.G run.T).trace -
                S.nucNorm (run.G 1)) := by ring
    have hαη : S.alpha * η⁻¹ = S.beta * η := by
      simpa only [div_eq_mul_inv] using hcoeff
    have hDnonneg : 0 ≤ run.D := le_of_lt run.D_pos
    have hterminalD := mul_le_mul_of_nonneg_left hterminal hDnonneg
    have hbregSumD := mul_le_mul_of_nonneg_left hbregSum hDnonneg
    have hpotSumD := mul_le_mul_of_nonneg_left hpotSum hDnonneg
    have hinitialD := mul_le_mul_of_nonneg_left hinitial hDnonneg
    dsimp only [η] at hterminalD hbregSumD hpotSumD hinitialD hαη hβη
    rw [hαη] at hpotSumD hinitialD
    rw [gbpa_decomposition S run]
    rw [← hβη]
    nlinarith

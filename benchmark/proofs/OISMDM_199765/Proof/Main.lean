import Architect
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:node-seq"
  (statement := /-- Let $k \in \mathbb{N}$ and let $s : \mathbb{N} \to \mathbb{N}$ encode an unmasking
  schedule, where $s(t)$ is the $t$-th step size for $t \in [k] = \{1,\ldots,k\}$. The
  \emph{node sequence} induced by $s$ is the function $a \mapsto N_a$ defined by
  \[ N_a \;\triangleq\; 1 + \sum_{t=1}^{a-1} s(t). \]
  In particular $N_1 = 1$, and for a schedule whose steps are positive the nodes are
  strictly increasing. -/)
  (title := /-- Node sequence induced by a schedule -/)
  (latexEnv := "definition")]
def node_seq (s : ℕ → ℕ) (a : ℕ) : ℕ :=
  1 + ∑ t ∈ Finset.Ico 1 a, s t

@[blueprint "def:step-approx"
  (statement := /-- Fix a sequence $Z : \mathbb{N} \to \mathbb{R}$, a schedule $s : \mathbb{N} \to \mathbb{N}$,
  and a number of steps $k$, and let $N_a$ be the node sequence of $s$ (see \cref{def:node-seq}).
  The \emph{$k$-step left Riemann approximation} $Z^{\vec N} : \mathbb{N} \to \mathbb{R}$ of $Z$ assigns to
  index $j$ the value $Z_{N_{a^\ast(j)}}$, where $a^\ast(j) = \bigl|\{\, a \in [k] : N_a \le j \,\}\bigr|$
  is the number of nodes not exceeding $j$. Equivalently, $Z^{\vec N}_j = Z_{N_a}$ whenever
  $N_a \le j < N_{a+1}$, and $Z^{\vec N}_j = Z_{N_k}$ whenever $j \ge N_k$. -/)
  (title := /-- Left Riemann step approximation -/)
  (latexEnv := "definition")]
def step_approx (Z : ℕ → ℝ) (s : ℕ → ℕ) (k : ℕ) (j : ℕ) : ℝ :=
  Z (node_seq s (((Finset.Icc 1 k).filter (fun a => node_seq s a ≤ j)).card))

@[blueprint "def:l1-error"
  (statement := /-- Given two sequences $Z, Z' : \mathbb{N} \to \mathbb{R}$ and a length $n \in \mathbb{N}$,
  the \emph{$L^1$ integration error} on $[n] = \{1,\ldots,n\}$ is
  \[ \norm{Z - Z'}_{L^1} \;\triangleq\; \sum_{j=1}^{n} \bigl| Z_j - Z'_j \bigr|. \] -/)
  (title := /-- $L^1$ integration error -/)
  (latexEnv := "definition")]
def l1_error (Z Z' : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, |Z j - Z' j|

@[blueprint "def:valid-schedule"
  (statement := /-- A function $s : \mathbb{N} \to \mathbb{N}$ is a \emph{valid $k$-step schedule for length $n$}
  if every step $s(t)$ with $t \in [k]$ is at least $1$ and the step sizes sum to $n$:
  \[ \bigl( \forall\, t \in [k],\ s(t) \ge 1 \bigr) \quad\text{and}\quad \sum_{t=1}^{k} s(t) = n. \]
  These conditions make the induced nodes (see \cref{def:node-seq}) strictly increasing and contained
  in $[n]$, with $N_1 = 1$ and $N_k = n + 1 - s(k) \le n$. -/)
  (title := /-- Valid unmasking schedule -/)
  (latexEnv := "definition")]
def valid_schedule (s : ℕ → ℕ) (k n : ℕ) : Prop :=
  (∀ t ∈ Finset.Icc 1 k, 1 ≤ s t) ∧ ∑ t ∈ Finset.Icc 1 k, s t = n

@[blueprint "def:mdm-problem"
  (statement := /-- An \emph{MDM problem} packages the semantic data of the masked diffusion model
  inference task that lie outside the elementary geometry of the schedules. It consists of:
  a finite token alphabet $\Sigma$; a sequence length $n \in \mathbb{N}$; a data distribution
  $\mu$ over $\Sigma^n$; an \emph{information curve} $Z : \mathbb{N} \to \mathbb{R}$, whose value
  $Z_j = Z_j(\mu) = \E_{|S| = j-1,\ i \notin S}[\, I(X_i; X_S) \,]$ is the average mutual information;
  and an \emph{expected KL error} functional $\mathrm{eKL} : (\mathbb{N} \to \mathbb{N}) \to \mathbb{R}$,
  where $\mathrm{eKL}(s) = \E_{S_1,\ldots,S_k}\bigl[ \KL{\mu}{\nu^{S_1,\ldots,S_k}} \bigr]$ is the expected
  Kullback--Leibler divergence between $\mu$ and the output distribution $\nu^{S_1,\ldots,S_k}$ of the
  parallel-unmasking sampler under the subset sizes prescribed by $s$. The information curve is assumed
  to satisfy the two properties established by Han's inequality: the base condition $Z_1 = 0$ and
  monotonicity, $Z_i \le Z_j$ for all $1 \le i \le j \le n$. Finally, the expected KL error functional is
  tied to the information curve by the sampler analysis of the underlying paper: for every $k$ with
  $1 \le k \le n$ and every valid $k$-step schedule $s$ for length $n$ (\cref{def:valid-schedule}),
  \[ \mathrm{eKL}(s) \;=\; \norm{Z - Z^{\vec N}}_{L^1}, \]
  the $L^1$ integration error (\cref{def:l1-error}) between $Z$ and its $k$-step left Riemann
  approximation $Z^{\vec N}$ (\cref{def:step-approx}) induced by the node sequence of $s$
  (\cref{def:node-seq}). This defining relation is exactly the sampler-side identity proved for the
  parallel-unmasking algorithm, and it is what makes the expected KL error a function of the schedule
  through the information curve alone. -/)
  (title := /-- Masked diffusion inference problem -/)
  (latexEnv := "definition")]
structure mdm_problem where
  alphabet : Type
  alphabet_fintype : Fintype alphabet
  n : ℕ
  μ : PMF (Fin n → alphabet)
  Z : ℕ → ℝ
  expectedKL : (ℕ → ℕ) → ℝ
  Z_base : Z 1 = 0
  Z_mono : ∀ i ∈ Finset.Icc 1 n, ∀ j ∈ Finset.Icc 1 n, i ≤ j → Z i ≤ Z j
  expectedKL_eq : ∀ (k : ℕ), 1 ≤ k → k ≤ n → ∀ s, valid_schedule s k n →
    expectedKL s = l1_error Z (step_approx Z s k) n

@[blueprint "thm:kl-error-eq-riemann"
  (statement := /-- Let $P$ be an MDM problem (\cref{def:mdm-problem}) with sequence length $n$,
  information curve $Z$, and expected KL error functional $\mathrm{eKL}$. Let $k \in \mathbb{N}$ with
  $1 \le k \le n$, and let $s$ be a valid $k$-step schedule for length $n$ (\cref{def:valid-schedule}).
  Then the expected KL error of the parallel-unmasking sampler under schedule $s$ equals the $L^1$
  integration error (\cref{def:l1-error}) between the information curve $Z$ and its $k$-step left
  Riemann approximation $Z^{\vec N}$ (\cref{def:step-approx}) induced by the node sequence of $s$
  (\cref{def:node-seq}):
  \[ \mathrm{eKL}(s) \;=\; \norm{Z - Z^{\vec N}}_{L^1} \;=\; \sum_{j=1}^{n} \bigl| Z_j - Z^{\vec N}_j \bigr|. \] -/)
  (proof := /-- This identity is exactly the defining relation of the expected KL error functional
  recorded in \cref{def:mdm-problem}: an MDM problem carries, as part of its data, the sampler-side
  hypothesis that for every $k$ with $1 \le k \le n$ and every valid $k$-step schedule $s$ for length
  $n$, the expected KL error $\mathrm{eKL}(s)$ equals the $L^1$ integration error
  $\norm{Z - Z^{\vec N}}_{L^1}$. Applying this hypothesis to the given $k$ and $s$ yields the claim. -/)
  (title := /-- Expected KL error equals the $L^1$ step-approximation error -/)
  (latexEnv := "theorem")]
theorem kl_error_eq_riemann (P : mdm_problem) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ P.n)
    (s : ℕ → ℕ) (hs : valid_schedule s k P.n) :
    P.expectedKL s = l1_error P.Z (step_approx P.Z s k) P.n := by
  exact P.expectedKL_eq k hk hkn s hs

@[blueprint "thm:optimal-schedule"
  (statement := /-- Let $P$ be an MDM problem (\cref{def:mdm-problem}) with sequence length $n$, and let
  $k \in \mathbb{N}$ with $1 \le k \le n$. Suppose $s^\ast$ is a valid $k$-step schedule for length $n$
  (\cref{def:valid-schedule}) whose induced left Riemann approximation minimizes the $L^1$ integration
  error over all valid $k$-step schedules; that is, for every valid $k$-step schedule $s$,
  \[ \norm{Z - Z^{\vec N^{\ast}}}_{L^1} \;\le\; \norm{Z - Z^{\vec N}}_{L^1}, \]
  where $\vec N^{\ast}$ and $\vec N$ are the node sequences (\cref{def:node-seq}) of $s^\ast$ and $s$.
  Then $s^\ast$ minimizes the expected KL error over all valid $k$-step schedules: for every valid
  $k$-step schedule $s$, $\mathrm{eKL}(s^\ast) \le \mathrm{eKL}(s)$. -/)
  (proof := /-- Fix any valid $k$-step schedule $s$. By \cref{thm:kl-error-eq-riemann} applied to $s^\ast$
  and to $s$, the expected KL errors satisfy $\mathrm{eKL}(s^\ast) = \norm{Z - Z^{\vec N^{\ast}}}_{L^1}$ and
  $\mathrm{eKL}(s) = \norm{Z - Z^{\vec N}}_{L^1}$. The minimality hypothesis on $s^\ast$ gives
  $\norm{Z - Z^{\vec N^{\ast}}}_{L^1} \le \norm{Z - Z^{\vec N}}_{L^1}$, whence
  $\mathrm{eKL}(s^\ast) \le \mathrm{eKL}(s)$. -/)
  (title := /-- The $L^1$-optimal schedule minimizes the expected KL error -/)
  (latexEnv := "theorem")]
theorem optimal_schedule (P : mdm_problem) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ P.n)
    (sStar : ℕ → ℕ) (hsStar : valid_schedule sStar k P.n)
    (hmin : ∀ s, valid_schedule s k P.n →
      l1_error P.Z (step_approx P.Z sStar k) P.n ≤ l1_error P.Z (step_approx P.Z s k) P.n) :
    ∀ s, valid_schedule s k P.n → P.expectedKL sStar ≤ P.expectedKL s := by
  intro s hs
  rw [kl_error_eq_riemann P k hk hkn sStar hsStar,
    kl_error_eq_riemann P k hk hkn s hs]
  exact hmin s hs

import Architect
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Logic.Equiv.Defs

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory Finset BigOperators

@[blueprint "def:seed-measure"
  (statement := /-- The seed measure is the Lebesgue measure on $\mathbb{R}$ restricted to the
  unit interval $[0,1]$. It is the law of the uniform random threshold
  $r \sim \mathrm{Unif}([0,1])$ used by every random threshold algorithm. -/)
  (title := /-- The uniform seed measure on $[0,1]$ -/)
  (latexEnv := "definition")]
noncomputable def seed_measure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

@[blueprint "def:tester"
  (statement := /-- Fix a domain size $n$ and a sample size $m$. A \emph{tester} is a function
  $A : ([n]^{m}) \times \mathbb{R} \to \{\mathrm{accept}, \mathrm{reject}\}$, where the first
  argument is the sample sequence $X = (X_1,\dots,X_m)$ with each $X_i \in [n]$, and the second
  argument is the internal randomness $r$. We encode the domain $[n]$ by the finite type
  $\mathrm{Fin}\ n$, the sample sequence by a function $X : \mathrm{Fin}\ m \to \mathrm{Fin}\ n$,
  and the binary decision by a Boolean, with $\mathtt{true}$ standing for $\mathrm{accept}$ and
  $\mathtt{false}$ for $\mathrm{reject}$. -/)
  (title := /-- Tester -/)
  (latexEnv := "definition")]
def tester (n m : ℕ) : Type :=
  (Fin m → Fin n) → ℝ → Bool

@[blueprint "def:measurable-tester"
  (statement := /-- A tester $A$ on $n$ and $m$ is \emph{measurable} if for every sample sequence
  $X \in [n]^{m}$ the seed acceptance set $\{r \in \mathbb{R} : A(X;r) = \mathrm{accept}\}$ is a
  Lebesgue measurable subset of $\mathbb{R}$. This is the minimal regularity hypothesis under
  which the acceptance probability of $A$ over the seed is well behaved; it is automatic for every
  algorithm that reads finitely many bits of $r$, and it holds for the random threshold algorithms
  of \cref{def:threshold-tester} because their acceptance sets are intervals. -/)
  (title := /-- Measurable tester -/)
  (latexEnv := "definition")]
def measurable_tester {n m : ℕ} (A : tester n m) : Prop :=
  ∀ X : Fin m → Fin n, MeasurableSet {r : ℝ | A X r = true}

@[blueprint "def:seed-accept-prob"
  (statement := /-- For a tester $A$ and a fixed sample sequence $X \in [n]^{m}$, the
  \emph{seed acceptance probability} is
  \[
    \mathrm{Pr}_{r \sim \mathrm{Unif}([0,1])}\left[A(X;r) = \mathrm{accept}\right],
  \]
  realised as the real-valued seed measure (\cref{def:seed-measure}) of the acceptance set
  $\{r : A(X;r) = \mathrm{accept}\}$. This is the deterministic function of $X$ that the
  canonicalisation of Lemma~\ref{lem:canonical} of the source uses as its threshold. -/)
  (title := /-- Seed acceptance probability -/)
  (latexEnv := "definition")]
noncomputable def seed_accept_prob {n m : ℕ} (A : tester n m) (X : Fin m → Fin n) : ℝ :=
  seed_measure.real {r : ℝ | A X r = true}

@[blueprint "def:threshold-tester"
  (statement := /-- Let $f : [n]^{m} \to \mathbb{R}$ be a deterministic function of the sample
  sequence. The associated \emph{random threshold algorithm} is the tester that, on sample
  sequence $X$ and seed $r$, outputs $\mathrm{accept}$ if $r \le f(X)$ and $\mathrm{reject}$
  otherwise. This is the canonical format of Definition~\ref{def:canonical} of the source: a
  deterministic function of the input compared against a uniform random threshold. -/)
  (title := /-- Random threshold algorithm -/)
  (latexEnv := "definition")]
noncomputable def threshold_tester {n m : ℕ} (f : (Fin m → Fin n) → ℝ) : tester n m :=
  fun X r => decide (r ≤ f X)

@[blueprint "def:is-random-threshold"
  (statement := /-- A tester $A$ \emph{operates in canonical random threshold format} if there
  exists a deterministic function $f : [n]^{m} \to \mathbb{R}$, taking values in $[0,1]$, such
  that $A$ is the random threshold algorithm of \cref{def:threshold-tester} associated with $f$;
  that is, for every sample sequence $X$ and every seed $r$, $A(X;r) = \mathrm{accept}$ if and
  only if $r \le f(X)$. -/)
  (title := /-- Canonical random threshold format -/)
  (latexEnv := "definition")]
def is_random_threshold {n m : ℕ} (A : tester n m) : Prop :=
  ∃ f : (Fin m → Fin n) → ℝ, (∀ X, f X ∈ Set.Icc (0 : ℝ) 1) ∧ A = threshold_tester f

@[blueprint "def:sample-weight"
  (statement := /-- Let $p$ be a distribution on the domain $[n]$, given as a probability mass
  function. For a sample sequence $X \in [n]^{m}$, the \emph{sample weight} of $X$ under $p$ is
  \[
    p^{\otimes m}(X) \;=\; \prod_{i=1}^{m} p(X_i) \;\in\; [0,1],
  \]
  the probability that $m$ independent draws from $p$ produce exactly the sequence $X$. All
  probabilities over the samples are finite sums against this weight. -/)
  (title := /-- Product weight of a sample sequence -/)
  (latexEnv := "definition")]
noncomputable def sample_weight {n : ℕ} (p : PMF (Fin n)) {m : ℕ} (X : Fin m → Fin n) : ℝ :=
  ∏ i : Fin m, (p (X i)).toReal

@[blueprint "def:accept-prob"
  (statement := /-- Let $p$ be a distribution on $[n]$ and let $A$ be a tester on $n$ and $m$.
  The \emph{acceptance probability of $A$ under $p$} is
  \[
    \mathrm{Pr}_{X \sim p^{\otimes m},\, r \sim \mathrm{Unif}([0,1])}
      \left[A(X;r) = \mathrm{accept}\right]
    \;=\; \sum_{X \in [n]^{m}} p^{\otimes m}(X)\,
      \mathrm{Pr}_{r}\left[A(X;r) = \mathrm{accept}\right],
  \]
  where the identity is the decomposition of the joint probability over the independent sample
  and seed randomness, using \cref{def:sample-weight} and \cref{def:seed-accept-prob}. -/)
  (title := /-- Acceptance probability under a distribution -/)
  (latexEnv := "definition")]
noncomputable def accept_prob {n m : ℕ} (p : PMF (Fin n)) (A : tester n m) : ℝ :=
  ∑ X : Fin m → Fin n, sample_weight p X * seed_accept_prob A X

@[blueprint "def:replicable"
  (statement := /-- Let $\rho \in \mathbb{R}$. A tester $A$ on $n$ and $m$ is
  \emph{$\rho$-replicable} if for every distribution $p$ on the domain $[n]$,
  \[
    \mathrm{Pr}_{X, X' \sim p^{\otimes m},\, r \sim \mathrm{Unif}([0,1])}
      \left[A(X;r) = A(X';r)\right] \;\ge\; 1 - \rho,
  \]
  where $X$ and $X'$ are independent sample sequences of $m$ i.i.d.\ draws from $p$ and $r$ is a
  single shared seed. Expanding the joint law over the two independent sample sequences by
  \cref{def:sample-weight}, this reads
  \[
    \sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')\,
      \mathrm{Pr}_{r}\left[A(X;r) = A(X';r)\right] \;\ge\; 1 - \rho.
  \]
  This is Definition~\ref{def:replicability} of the source, specialised to samples drawn from a
  distribution on $[n]$. -/)
  (title := /-- $\rho$-replicability -/)
  (latexEnv := "definition")]
noncomputable def replicable {n m : ℕ} (ρ : ℝ) (A : tester n m) : Prop :=
  ∀ p : PMF (Fin n),
    1 - ρ ≤ ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
      sample_weight p X * sample_weight p X' *
        seed_measure.real {r : ℝ | A X r = A X' r}

@[blueprint "def:perm-pmf"
  (statement := /-- Let $\pi$ be a permutation of the domain $[n]$ and let $p$ be a distribution
  on $[n]$. The \emph{relabelled distribution} $p^{\pi}$ is the push-forward of $p$ along $\pi$,
  so that $p^{\pi} = p \circ \pi^{-1}$; explicitly, $p^{\pi}(\pi(j)) = p(j)$ for every
  $j \in [n]$. This is the distribution from which the relabelled sample sequence $\pi(X)$ is
  drawn when $X \sim p^{\otimes m}$. -/)
  (title := /-- Relabelling a distribution by a permutation -/)
  (latexEnv := "definition")]
noncomputable def perm_pmf {n : ℕ} (π : Equiv.Perm (Fin n)) (p : PMF (Fin n)) : PMF (Fin n) :=
  p.map π

@[blueprint "def:tv-dist"
  (statement := /-- The \emph{total variation distance} between two distributions $p$ and $q$ on
  the finite domain $[n]$ is
  \[
    d_{\mathrm{TV}}(p, q) \;=\; \frac{1}{2} \sum_{j \in [n]} \left|p(j) - q(j)\right|,
  \]
  the standard statistical distance on distributions over a finite domain. -/)
  (title := /-- Total variation distance -/)
  (latexEnv := "definition")]
noncomputable def tv_dist {n : ℕ} (p q : PMF (Fin n)) : ℝ :=
  (1 / 2) * ∑ j : Fin n, |(p j).toReal - (q j).toReal|

@[blueprint "def:symmetric-property"
  (statement := /-- Let $\mathcal{P}$ be a property of distributions on the domain $[n]$, that is,
  a collection of distributions on $[n]$. The property $\mathcal{P}$ is \emph{symmetric} if for
  every $p \in \mathcal{P}$ and every permutation $\pi$ of $[n]$, the relabelled distribution
  $p^{\pi}$ of \cref{def:perm-pmf} also lies in $\mathcal{P}$. This is
  Definition~\ref{def:symmetric_property} of the source. -/)
  (title := /-- Symmetric property -/)
  (latexEnv := "definition")]
def symmetric_property {n : ℕ} (P : Set (PMF (Fin n))) : Prop :=
  ∀ p ∈ P, ∀ π : Equiv.Perm (Fin n), perm_pmf π p ∈ P

@[blueprint "def:far-from"
  (statement := /-- Let $\mathcal{P}$ be a property of distributions on $[n]$ and let
  $\varepsilon > 0$. A distribution $p$ on $[n]$ is \emph{$\varepsilon$-far from $\mathcal{P}$}
  if every $q \in \mathcal{P}$ satisfies $d_{\mathrm{TV}}(p, q) \ge \varepsilon$, with
  $d_{\mathrm{TV}}$ as in \cref{def:tv-dist}. -/)
  (title := /-- $\varepsilon$-farness from a property -/)
  (latexEnv := "definition")]
noncomputable def far_from {n : ℕ} (ε : ℝ) (P : Set (PMF (Fin n))) (p : PMF (Fin n)) : Prop :=
  ∀ q ∈ P, ε ≤ tv_dist p q

@[blueprint "def:accurate-tester"
  (statement := /-- Let $\mathcal{P}$ be a property of distributions on $[n]$, let
  $\varepsilon, \delta \in (0,1)$, and let $A$ be a tester on $n$ and $m$. The tester $A$ is
  \emph{$(\varepsilon,\delta)$-accurate for $\mathcal{P}$} if both of the following hold.
  \begin{itemize}
    \item If $p \in \mathcal{P}$, then
      $\mathrm{Pr}_{X \sim p^{\otimes m}, r}[A(X;r) = \mathrm{accept}] \ge 1 - \delta$.
    \item If $p$ is $\varepsilon$-far from $\mathcal{P}$ in the sense of \cref{def:far-from},
      then $\mathrm{Pr}_{X \sim p^{\otimes m}, r}[A(X;r) = \mathrm{accept}] \le \delta$.
  \end{itemize}
  The second condition is the source's requirement that $A$ output $\mathrm{reject}$ with
  probability at least $1 - \delta$, written in terms of the acceptance probability of
  \cref{def:accept-prob}; the two forms agree because $A$ takes exactly the two values
  $\mathrm{accept}$ and $\mathrm{reject}$. -/)
  (title := /-- $(\varepsilon,\delta)$-accuracy for a property -/)
  (latexEnv := "definition")]
noncomputable def accurate_tester {n m : ℕ} (ε δ : ℝ) (P : Set (PMF (Fin n)))
    (A : tester n m) : Prop :=
  (∀ p ∈ P, 1 - δ ≤ accept_prob p A) ∧
    (∀ p : PMF (Fin n), far_from ε P p → accept_prob p A ≤ δ)

@[blueprint "def:order-invariant"
  (statement := /-- A tester $A$ on $n$ and $m$ is \emph{sample order invariant} if for every
  seed $r$, every permutation $\sigma$ of the sample positions $[m]$, and every sample sequence
  $X \in [n]^{m}$, we have $A(X;r) = A(X_{\sigma};r)$, where
  $X_{\sigma} = (X_{\sigma(1)},\dots,X_{\sigma(m)})$. This is the pointwise form of
  Definition~\ref{def:sample_invariant} of the source; it is strictly stronger than invariance of
  the output distribution, and it is what the construction of Lemma~\ref{lem:order_invariant} of the
  source achieves. -/)
  (title := /-- Sample order invariance -/)
  (latexEnv := "definition")]
def order_invariant {n m : ℕ} (A : tester n m) : Prop :=
  ∀ (r : ℝ) (σ : Equiv.Perm (Fin m)) (X : Fin m → Fin n), A X r = A (X ∘ σ) r

@[blueprint "def:label-invariant"
  (statement := /-- A tester $A$ on $n$ and $m$ is \emph{sample label invariant} if for every
  seed $r$, every permutation $\pi$ of the domain $[n]$, and every sample sequence
  $X \in [n]^{m}$, we have $A(X;r) = A(\pi(X);r)$, where
  $\pi(X) = (\pi(X_1),\dots,\pi(X_m))$. This is the label invariance of
  Lemma~\ref{lem:label_invariant} of the source. The source states the permutation there as
  $\pi : [m] \to [m]$; that is an index-set misprint, since the displayed relabelling
  $\pi(X) = (\pi(X_1),\dots,\pi(X_m))$ applies $\pi$ to sample \emph{values}, which range over
  the domain $[n]$. We therefore type $\pi$ as a permutation of $[n]$, the only typing under
  which the source's own proof is meaningful. -/)
  (title := /-- Sample label invariance -/)
  (latexEnv := "definition")]
def label_invariant {n m : ℕ} (A : tester n m) : Prop :=
  ∀ (r : ℝ) (π : Equiv.Perm (Fin n)) (X : Fin m → Fin n), A X r = A (π ∘ X) r

@[blueprint "def:perm-robust-replicable"
  (statement := /-- Let $\rho \in \mathbb{R}$. A tester $A$ on $n$ and $m$ satisfies
  \emph{$\rho$-permutation robust replicability} if for every distribution $p$ on $[n]$ and every
  permutation $\pi$ of $[n]$,
  \[
    \mathrm{Pr}_{r \sim \mathrm{Unif}([0,1]),\, X \sim p^{\otimes m},\,
      X' \sim (p^{\pi})^{\otimes m}}\left[A(X;r) \neq A(X';r)\right] \;\le\; \rho,
  \]
  where $p^{\pi}$ is the relabelled distribution of \cref{def:perm-pmf}. This is
  Definition~\ref{def:perm-rubust-replicability} of the source. The source quantifies instead
  over ``any prior distribution $\mathcal{D}$ over a given distribution and all of its
  permutation'', drawing the pair $(p, p^{\pi})$ from $\mathcal{D}$, but never specifies the
  joint law of that pair; we quantify over the pairs $(p, \pi)$ themselves, which is the
  statement the source's own proof establishes and from which any version averaged over a prior
  $\mathcal{D}$ follows by taking expectations, the bound being affine in $\mathcal{D}$. -/)
  (title := /-- Permutation robust replicability -/)
  (latexEnv := "definition")]
noncomputable def perm_robust_replicable {n m : ℕ} (ρ : ℝ) (A : tester n m) : Prop :=
  ∀ (p : PMF (Fin n)) (π : Equiv.Perm (Fin n)),
    ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
      sample_weight p X * sample_weight (perm_pmf π p) X' *
        seed_measure.real {r : ℝ | A X r ≠ A X' r} ≤ ρ

@[blueprint "def:order-avg"
  (statement := /-- Let $f : [n]^{m} \to \mathbb{R}$ be a deterministic function of the sample
  sequence. Its \emph{order average} is
  \[
    (\mathrm{ordAvg}\, f)(X) \;=\; \frac{1}{m!} \sum_{\sigma} f(X_{\sigma}),
  \]
  the average of $f$ over all $m!$ permutations $\sigma$ of the sample positions $[m]$. This is
  the function $q$ of Lemma~\ref{lem:order_invariant} of the source. -/)
  (title := /-- Order average of a score function -/)
  (latexEnv := "definition")]
noncomputable def order_avg {n m : ℕ} (f : (Fin m → Fin n) → ℝ) : (Fin m → Fin n) → ℝ :=
  fun X => 𝔼 σ : Equiv.Perm (Fin m), f (X ∘ σ)

@[blueprint "def:label-avg"
  (statement := /-- Let $f : [n]^{m} \to \mathbb{R}$ be a deterministic function of the sample
  sequence. Its \emph{label average} is
  \[
    (\mathrm{labAvg}\, f)(X) \;=\; \frac{1}{n!} \sum_{\pi} f(\pi(X)),
  \]
  the average of $f$ over all $n!$ permutations $\pi$ of the domain $[n]$, where
  $\pi(X) = (\pi(X_1),\dots,\pi(X_m))$. This is the function $h$ of
  Lemma~\ref{lem:label_invariant} of the source. -/)
  (title := /-- Label average of a score function -/)
  (latexEnv := "definition")]
noncomputable def label_avg {n m : ℕ} (f : (Fin m → Fin n) → ℝ) : (Fin m → Fin n) → ℝ :=
  fun X => 𝔼 π : Equiv.Perm (Fin n), f (π ∘ X)

@[blueprint "def:canonical-score"
  (statement := /-- Let $A$ be a tester on $n$ and $m$. Its \emph{canonical score} is the
  deterministic function of the sample sequence obtained by first taking the seed acceptance
  probability of $A$ (\cref{def:seed-accept-prob}), then averaging over all permutations of the
  sample positions (\cref{def:order-avg}), and finally averaging over all permutations of the
  domain labels (\cref{def:label-avg}):
  \[
    \mathrm{score}_{A}(X) \;=\; \frac{1}{n!}\sum_{\pi} \frac{1}{m!}\sum_{\sigma}
      \mathrm{Pr}_{r}\left[A\bigl(\pi(X)_{\sigma};r\bigr) = \mathrm{accept}\right].
  \]
  This single function composes the three successive constructions $A_0 \mapsto A_1 \mapsto A_2
  \mapsto A_3$ of Lemmas~\ref{lem:canonical}, \ref{lem:order_invariant}, and
  \ref{lem:label_invariant} of the source. -/)
  (title := /-- Canonical score of a tester -/)
  (latexEnv := "definition")]
noncomputable def canonical_score {n m : ℕ} (A : tester n m) : (Fin m → Fin n) → ℝ :=
  label_avg (order_avg (seed_accept_prob A))

@[blueprint "def:canonical-tester"
  (statement := /-- Let $A$ be a tester on $n$ and $m$. Its \emph{canonicalisation} $A'$ is the
  random threshold algorithm (\cref{def:threshold-tester}) associated with the canonical score
  of \cref{def:canonical-score}: on sample sequence $X$ and seed $r$, it outputs
  $\mathrm{accept}$ if $r \le \mathrm{score}_{A}(X)$ and $\mathrm{reject}$ otherwise. This is the
  algorithm $A_3$ of Lemma~\ref{lem:label_invariant} of the source, and it is the witness for the main
  theorem \cref{thm:main-canonical}. -/)
  (title := /-- Canonicalisation of a tester -/)
  (latexEnv := "definition")]
noncomputable def canonical_tester {n m : ℕ} (A : tester n m) : tester n m :=
  threshold_tester (canonical_score A)

@[blueprint "def:score-replicable"
  (statement := /-- Let $\rho \in \mathbb{R}$ and let $f : [n]^{m} \to \mathbb{R}$ be a
  deterministic function of the sample sequence. We say $f$ is \emph{$\rho$-score replicable} if
  for every distribution $p$ on $[n]$,
  \[
    \mathbb{E}_{X, X' \sim p^{\otimes m}}\left|f(X) - f(X')\right|
    \;=\; \sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')\,
      \left|f(X) - f(X')\right| \;\le\; \rho,
  \]
  where $X$ and $X'$ are independent sample sequences of $m$ i.i.d.\ draws from $p$. This is the
  quantity that governs the replicability of the random threshold algorithm associated with $f$:
  by \cref{lem:threshold-disagree-eq-abs-diff}, the seed disagreement probability of that
  algorithm on the pair $(X, X')$ is exactly $|f(X) - f(X')|$. Isolating this notion lets the
  replicability of \cref{lem:canonical-tester-replicable} be assembled from one entry step, two
  averaging steps, and one exit step. -/)
  (title := /-- Score replicability -/)
  (latexEnv := "definition")]
noncomputable def score_replicable {n m : ℕ} (ρ : ℝ) (f : (Fin m → Fin n) → ℝ) : Prop :=
  ∀ p : PMF (Fin n),
    ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
      sample_weight p X * sample_weight p X' * |f X - f X'| ≤ ρ

@[blueprint "lem:seed-measure-univ"
  (statement := /-- The seed measure of \cref{def:seed-measure} is a probability measure: the
  Lebesgue measure of the unit interval $[0,1]$ equals $1$, so
  $\mathrm{Unif}([0,1])(\mathbb{R}) = 1$. -/)
  (proof := /-- By \cref{def:seed-measure}, the seed measure is $\mathrm{vol}$ restricted to
  $[0,1]$, so its total mass is $\mathrm{vol}([0,1])$. The Lebesgue measure of a closed interval
  $[a,b]$ with $a \le b$ is $b - a$; with $a = 0$ and $b = 1$ this gives
  $\mathrm{vol}([0,1]) = 1$, as required. -/)
  (title := /-- The seed measure is a probability measure -/)
  (latexEnv := "lemma")]
lemma seed_measure_univ : seed_measure Set.univ = 1 := by
  simp [seed_measure, Measure.restrict_apply_univ, Real.volume_Icc]

@[blueprint "lem:seed-accept-prob-mem-Icc"
  (statement := /-- Let $n, m$ be natural numbers, let $A$ be a tester on $n$ and $m$ in the
  sense of \cref{def:tester}, and let $X \in [n]^{m}$ be a sample sequence. No measurability
  hypothesis on $A$ is assumed. Then the seed acceptance probability of
  \cref{def:seed-accept-prob} lies in the unit interval:
  \[
    \mathrm{Pr}_{r \sim \mathrm{Unif}([0,1])}\left[A(X;r) = \mathrm{accept}\right]
      \;\in\; [0,1] ,
  \]
  that is, $0 \le \mathrm{Pr}_{r}[A(X;r) = \mathrm{accept}] \le 1$. -/)
  (proof := /-- By \cref{def:seed-accept-prob} the quantity in question is the real-valued
  seed measure $\mathrm{Unif}([0,1])^{\mathbb{R}}(S)$ of the acceptance set
  $S = \{r \in \mathbb{R} : A(X;r) = \mathrm{accept}\}$, where $\mu^{\mathbb{R}}(E)$ denotes the
  real number obtained from the extended nonnegative value $\mu(E)$. Membership in $[0,1]$ is
  equivalent to the two inequalities $0 \le \mathrm{Unif}([0,1])^{\mathbb{R}}(S)$ and
  $\mathrm{Unif}([0,1])^{\mathbb{R}}(S) \le 1$, which we prove in turn.

  For the lower bound, the real-valued measure of any set is nonnegative, since it is the
  real number attached to an extended nonnegative quantity; this gives
  $0 \le \mathrm{Unif}([0,1])^{\mathbb{R}}(S)$ with no hypothesis on $S$.

  For the upper bound, first note that the total mass is finite: by
  \cref{lem:seed-measure-univ} we have $\mathrm{Unif}([0,1])(\mathbb{R}) = 1 \ne \infty$.
  Consequently the real-valued total mass satisfies
  $\mathrm{Unif}([0,1])^{\mathbb{R}}(\mathbb{R}) = 1$, again by
  \cref{lem:seed-measure-univ} together with the fact that the real number attached to the
  extended value $1$ is $1$. Since $S \subseteq \mathbb{R}$ and the total mass is finite,
  monotonicity of the real-valued measure yields
  $\mathrm{Unif}([0,1])^{\mathbb{R}}(S) \le \mathrm{Unif}([0,1])^{\mathbb{R}}(\mathbb{R})$.
  Rewriting the right-hand side by the computed total mass $1$ gives
  $\mathrm{Unif}([0,1])^{\mathbb{R}}(S) \le 1$, which completes the proof. -/)
  (title := /-- The seed acceptance probability lies in $[0,1]$ -/)
  (latexEnv := "lemma")]
lemma seed_accept_prob_mem_Icc {n m : ℕ} (A : tester n m) (X : Fin m → Fin n) :
    seed_accept_prob A X ∈ Set.Icc (0 : ℝ) 1 := by
  refine Set.mem_Icc.mpr ⟨measureReal_nonneg, ?_⟩
  have hfin : seed_measure Set.univ ≠ ⊤ := by
    rw [seed_measure_univ]
    exact ENNReal.one_ne_top
  have huniv : seed_measure.real Set.univ = 1 := by
    rw [Measure.real, seed_measure_univ, ENNReal.toReal_one]
  have hmono : seed_measure.real {r : ℝ | A X r = true} ≤ seed_measure.real Set.univ :=
    measureReal_mono (Set.subset_univ _) hfin
  rw [huniv] at hmono
  exact hmono

@[blueprint "lem:seed-agree-set-eq"
  (statement := /-- Let $A$ be a tester on $n$ and $m$ in the sense of \cref{def:tester}, and let
  $X, X' \in [n]^{m}$ be sample sequences. Write
  $S = \{r \in \mathbb{R} : A(X;r) = \mathrm{accept}\}$ and
  $S' = \{r \in \mathbb{R} : A(X';r) = \mathrm{accept}\}$ for the two seed acceptance sets. Then
  the seed agreement event decomposes as
  \[
    \{r \in \mathbb{R} : A(X;r) = A(X';r)\}
      \;=\; (S \cap S') \cup (S^{c} \cap S'^{c}).
  \] -/)
  (proof := /-- Fix a seed $r \in \mathbb{R}$; we show that $r$ belongs to the left-hand side if
  and only if it belongs to the right-hand side. By \cref{def:tester} each of $A(X;r)$ and
  $A(X';r)$ is one of the two Boolean values $\mathrm{accept}$ and $\mathrm{reject}$, so there
  are exactly four cases. If $A(X;r) = A(X';r) = \mathrm{accept}$, then $r \in S \cap S'$ and $r$
  lies in the agreement event. If $A(X;r) = A(X';r) = \mathrm{reject}$, then
  $r \in S^{c} \cap S'^{c}$ and again $r$ lies in the agreement event. In the two remaining
  cases the values differ, so $r$ lies in neither the agreement event nor either of the two
  intersections, because each intersection forces the two values to coincide. Hence the two sets
  have the same elements and are equal. -/)
  (title := /-- Decomposition of the seed agreement event -/)
  (latexEnv := "lemma")]
lemma seed_agree_set_eq {n m : ℕ} (A : tester n m) (X X' : Fin m → Fin n) :
    {r : ℝ | A X r = A X' r} =
      ({r : ℝ | A X r = true} ∩ {r : ℝ | A X' r = true}) ∪
        ({r : ℝ | A X r = true}ᶜ ∩ {r : ℝ | A X' r = true}ᶜ) := by
  ext r
  cases hx : A X r <;> cases hy : A X' r <;> simp [hx, hy]

@[blueprint "lem:seed-agree-measurable"
  (statement := /-- Let $A$ be a measurable tester on $n$ and $m$ in the sense of
  \cref{def:measurable-tester}, and let $X, X' \in [n]^{m}$ be sample sequences. Then the seed
  agreement event $\{r \in \mathbb{R} : A(X;r) = A(X';r)\}$ is a Lebesgue measurable subset of
  $\mathbb{R}$. -/)
  (proof := /-- By \cref{lem:seed-agree-set-eq} the agreement event equals
  $(S \cap S') \cup (S^{c} \cap S'^{c})$, where
  $S = \{r \in \mathbb{R} : A(X;r) = \mathrm{accept}\}$ and
  $S' = \{r \in \mathbb{R} : A(X';r) = \mathrm{accept}\}$. Since $A$ is measurable, both $S$ and
  $S'$ are measurable by \cref{def:measurable-tester}. The measurable sets of $\mathbb{R}$ are
  closed under complement, pairwise intersection, and pairwise union, so $S \cap S'$ is
  measurable, $S^{c} \cap S'^{c}$ is measurable, and their union is measurable. -/)
  (title := /-- The seed agreement event is measurable -/)
  (latexEnv := "lemma")]
lemma seed_agree_measurable {n m : ℕ} (A : tester n m) (hA : measurable_tester A)
    (X X' : Fin m → Fin n) :
    MeasurableSet {r : ℝ | A X r = A X' r} := by
  rw [seed_agree_set_eq A X X']
  exact ((hA X).inter (hA X')).union ((hA X).compl.inter (hA X').compl)

@[blueprint "lem:seed-measure-prob"
  (statement := /-- The seed measure of \cref{def:seed-measure} is a probability measure, that
  is, it satisfies the predicate asserting that its total mass equals $1$. -/)
  (proof := /-- Being a probability measure means precisely that the measure of the whole space
  $\mathbb{R}$ equals $1$, and this is the content of \cref{lem:seed-measure-univ}. -/)
  (title := /-- The seed measure is a probability measure -/)
  (latexEnv := "lemma")]
lemma seed_measure_prob : IsProbabilityMeasure seed_measure := by
  exact ⟨seed_measure_univ⟩

@[blueprint "lem:seed-disagree-eq"
  (statement := /-- Let $A$ be a measurable tester on $n$ and $m$ in the sense of
  \cref{def:measurable-tester}, and let $X, X' \in [n]^{m}$ be sample sequences. Then the seed
  agreement and disagreement probabilities are complementary:
  \[
    \mathrm{Pr}_{r \sim \mathrm{Unif}([0,1])}\left[A(X;r) = A(X';r)\right]
    \;=\; 1 - \mathrm{Pr}_{r \sim \mathrm{Unif}([0,1])}\left[A(X;r) \neq A(X';r)\right].
  \]
  This is the bridge between the agreement form of replicability
  (\cref{def:replicable}) and the disagreement form of permutation robust replicability
  (\cref{def:perm-robust-replicable}). -/)
  (proof := /-- The disagreement event $\{r : A(X;r) \neq A(X';r)\}$ is, by definition of
  inequality of Boolean values, exactly the complement of the agreement event
  $\{r : A(X;r) = A(X';r)\}$ in $\mathbb{R}$. The agreement event is measurable by
  \cref{lem:seed-agree-measurable}, using that $A$ is a measurable tester. By
  \cref{lem:seed-measure-prob} the seed measure is a probability measure; in particular it is a
  finite measure, so the real-valued measure of the complement of a measurable set $S$ equals
  $\mathrm{Unif}([0,1])(\mathbb{R}) - \mathrm{Unif}([0,1])(S)$, and
  $\mathrm{Unif}([0,1])(\mathbb{R}) = 1$. Applying this with $S$ the agreement event, the
  right-hand side of the claim becomes
  $1 - \left(1 - \mathrm{Pr}_{r}[A(X;r) = A(X';r)]\right)$, which equals
  $\mathrm{Pr}_{r}[A(X;r) = A(X';r)]$, as required. -/)
  (title := /-- Seed agreement and disagreement are complementary -/)
  (latexEnv := "lemma")]
lemma seed_disagree_eq {n m : ℕ} (A : tester n m) (hA : measurable_tester A)
    (X X' : Fin m → Fin n) :
    seed_measure.real {r : ℝ | A X r = A X' r} =
      1 - seed_measure.real {r : ℝ | A X r ≠ A X' r} := by
  haveI := seed_measure_prob
  have hcompl : {r : ℝ | A X r ≠ A X' r} = {r : ℝ | A X r = A X' r}ᶜ := rfl
  rw [hcompl, measureReal_compl (seed_agree_measurable A hA X X'), measureReal_univ_eq_one]
  ring

@[blueprint "lem:threshold-tester-measurable"
  (statement := /-- Let $f : [n]^{m} \to \mathbb{R}$ be any deterministic function of the sample
  sequence. Then the random threshold algorithm of \cref{def:threshold-tester} associated with
  $f$ is a measurable tester in the sense of \cref{def:measurable-tester}. -/)
  (proof := /-- By \cref{def:measurable-tester} it suffices to fix a sample sequence
  $X \in [n]^{m}$ and show that the seed acceptance set
  $\{r \in \mathbb{R} : A(X;r) = \mathrm{accept}\}$ is measurable, where $A$ is the random
  threshold algorithm associated with $f$. By \cref{def:threshold-tester}, the algorithm accepts
  on seed $r$ precisely when $r \le f(X)$; hence, extensionally in $r$, this acceptance set
  equals the ray $(-\infty, f(X)]$. Every such ray is a measurable subset of $\mathbb{R}$, so
  rewriting along this set identity gives the claim. -/)
  (title := /-- Random threshold algorithms are measurable -/)
  (latexEnv := "lemma")]
lemma threshold_tester_measurable {n m : ℕ} (f : (Fin m → Fin n) → ℝ) :
    measurable_tester (threshold_tester f) := by
  intro X
  have hset : {r : ℝ | threshold_tester f X r = true} = Set.Iic (f X) := by
    ext r
    simp [threshold_tester]
  rw [hset]
  exact measurableSet_Iic

@[blueprint "lem:seed-accept-prob-threshold"
  (statement := /-- Let $f : [n]^{m} \to \mathbb{R}$ satisfy $f(X) \in [0,1]$ for every sample
  sequence $X \in [n]^{m}$. Then for every sample sequence $X \in [n]^{m}$, the random threshold
  algorithm associated with $f$ in the sense of \cref{def:threshold-tester} accepts $X$ with the
  seed acceptance probability of \cref{def:seed-accept-prob} equal to exactly $f(X)$:
  \[
    \mathrm{Pr}_{r \sim \mathrm{Unif}([0,1])}\left[r \le f(X)\right] \;=\; f(X).
  \]
  This is the computation underlying Equation~\eqref{eq:A_0_accept} of the source: a uniform
  threshold turns the value of a $[0,1]$-valued deterministic function into an acceptance
  probability. -/)
  (proof := /-- Fix the sample sequence $X$ and write $t = f(X)$; by hypothesis $0 \le t$ and
  $t \le 1$. By \cref{def:threshold-tester} the algorithm outputs $\mathrm{accept}$ on seed $r$
  exactly when $r \le t$, so its acceptance set is the ray
  $\{r \in \mathbb{R} : r \le t\} = (-\infty, t]$; by \cref{def:seed-accept-prob} the quantity to
  compute is the seed measure of this ray. The ray is measurable, being closed, so by
  \cref{def:seed-measure} the seed measure restricted to the unit interval evaluates it as the
  Lebesgue measure of the intersection $(-\infty, t] \cap [0,1]$.

  We claim this intersection equals $[0, t]$. If $r \le t$ and $0 \le r \le 1$, then
  $0 \le r$ and $r \le t$, so $r \in [0,t]$. Conversely, if $0 \le r \le t$, then $r \le t$,
  and moreover $0 \le r$ and $r \le t \le 1$, so $r \in [0,1]$; here the hypothesis $t \le 1$ is
  exactly what guarantees that no part of the ray below $t$ is cut off by the restriction.

  Therefore the seed measure of the acceptance set is $\mathrm{vol}([0,t])$. Since $0 \le t$, the
  Lebesgue measure of the closed interval $[0,t]$ is $t - 0 = t$. Hence the seed acceptance
  probability equals $t = f(X)$, which is the assertion. -/)
  (title := /-- Acceptance probability of a random threshold algorithm -/)
  (latexEnv := "lemma")]
lemma seed_accept_prob_threshold {n m : ℕ} (f : (Fin m → Fin n) → ℝ)
    (hf : ∀ X, f X ∈ Set.Icc (0 : ℝ) 1) (X : Fin m → Fin n) :
    seed_accept_prob (threshold_tester f) X = f X := by
  obtain ⟨h0, h1⟩ := hf X
  have hset : {r : ℝ | threshold_tester f X r = true} = Set.Iic (f X) := by
    ext r
    simp [threshold_tester]
  have hinter : Set.Iic (f X) ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 (f X) := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun hr => ⟨hr.2.1, hr.1⟩, fun hr => ⟨hr.2, hr.1, hr.2.trans h1⟩⟩
  rw [seed_accept_prob, hset, seed_measure,
    MeasureTheory.measureReal_restrict_apply measurableSet_Iic, hinter,
    Real.volume_real_Icc_of_le h0, sub_zero]

@[blueprint "lem:threshold-disagree-set"
  (statement := /-- Let $f : [n]^{m} \to \mathbb{R}$ be a deterministic function of the sample
  sequence, let $A$ be the random threshold algorithm of \cref{def:threshold-tester} associated
  with $f$, and let $X, X' \in [n]^{m}$. Then the set of seeds on which $A$ disagrees on $X$ and
  $X'$ is the half-open interval between the two scores:
  \[
    \left\{r \in \mathbb{R} : A(X;r) \neq A(X';r)\right\}
      \;=\; \bigl(\min\{f(X), f(X')\},\; \max\{f(X), f(X')\}\bigr] .
  \]
  No hypothesis on the range of $f$ is required. -/)
  (proof := /-- Fix a seed $r \in \mathbb{R}$. By \cref{def:threshold-tester} we have
  $A(X;r) = \mathrm{accept}$ if and only if $r \le f(X)$, and $A(X';r) = \mathrm{accept}$ if and
  only if $r \le f(X')$. Since $A$ takes exactly the two values $\mathrm{accept}$ and
  $\mathrm{reject}$, the outputs $A(X;r)$ and $A(X';r)$ differ if and only if the two conditions
  $r \le f(X)$ and $r \le f(X')$ are not equivalent. We distinguish the two cases supplied by the
  totality of the order on $\mathbb{R}$.

  Suppose first $f(X) \le f(X')$, so that $\min\{f(X), f(X')\} = f(X)$ and
  $\max\{f(X), f(X')\} = f(X')$. If $r \le f(X)$ then also $r \le f(X')$, so the two conditions
  are equivalent; if $r > f(X')$ then also $r > f(X)$, and again they are equivalent. In the
  remaining case $f(X) < r \le f(X')$ the condition $r \le f(X')$ holds while $r \le f(X)$ fails,
  so the two conditions are not equivalent. Hence the disagreement set is
  $\left(f(X), f(X')\right] = \bigl(\min\{f(X), f(X')\}, \max\{f(X), f(X')\}\bigr]$.

  Suppose now $f(X') \le f(X)$, so that $\min\{f(X), f(X')\} = f(X')$ and
  $\max\{f(X), f(X')\} = f(X)$. Exchanging the roles of $X$ and $X'$ in the previous paragraph
  shows that the two conditions fail to be equivalent exactly when $f(X') < r \le f(X)$, so the
  disagreement set is $\left(f(X'), f(X)\right]$, which is again
  $\bigl(\min\{f(X), f(X')\}, \max\{f(X), f(X')\}\bigr]$.

  In both cases the two sets contain exactly the same seeds, hence they are equal. -/)
  (title := /-- The seed disagreement set of a random threshold algorithm is an interval -/)
  (latexEnv := "lemma")]
lemma threshold_disagree_set {n m : ℕ} (f : (Fin m → Fin n) → ℝ) (X X' : Fin m → Fin n) :
    {r : ℝ | threshold_tester f X r ≠ threshold_tester f X' r} =
      Set.Ioc (min (f X) (f X')) (max (f X) (f X')) := by
  ext r
  simp only [threshold_tester, Set.mem_setOf_eq, ne_eq, decide_eq_decide, Set.mem_Ioc]
  rcases le_total (f X) (f X') with h | h <;>
    [rw [min_eq_left h, max_eq_right h]; rw [min_eq_right h, max_eq_left h]] <;>
    by_cases h1 : r ≤ f X <;> by_cases h2 : r ≤ f X' <;> simp [h1, h2] <;> linarith

@[blueprint "lem:seed-measure-real-Ioc-min-max"
  (statement := /-- Let $a, b \in [0,1]$. Then the seed measure of \cref{def:seed-measure}
  assigns to the half-open interval between $a$ and $b$ exactly its length:
  \[
    \mathrm{Unif}([0,1])\bigl(\left(\min\{a,b\},\; \max\{a,b\}\right]\bigr) \;=\; |a - b| .
  \]
  Here the left-hand side is the real-valued seed measure of the interval. -/)
  (proof := /-- Write $I = \left(\min\{a,b\}, \max\{a,b\}\right]$. We first show
  $I \subseteq [0,1]$. Let $r \in I$. Since $0 \le a$ and $0 \le b$ we have
  $0 \le \min\{a,b\} < r$, and since $a \le 1$ and $b \le 1$ we have
  $r \le \max\{a,b\} \le 1$; hence $r \in [0,1]$. Consequently $I \cap [0,1] = I$.

  The set $I$ is a half-open interval and therefore Lebesgue measurable, so by
  \cref{def:seed-measure} the defining formula for a restricted measure gives
  $\mathrm{Unif}([0,1])(I) = \mathrm{vol}(I \cap [0,1]) = \mathrm{vol}(I)$. The Lebesgue measure
  of the half-open interval $\left(\min\{a,b\}, \max\{a,b\}\right]$ is the difference of its
  endpoints, namely $\max\{a,b\} - \min\{a,b\}$; this quantity is a nonnegative real because
  $\min\{a,b\} \le \max\{a,b\}$, so no information is lost in passing from the extended
  nonnegative value to its real value. Finally, for any two reals one has
  $\max\{a,b\} - \min\{a,b\} = |b - a| = |a - b|$, which is the asserted identity. -/)
  (title := /-- Seed measure of the interval between two points of $[0,1]$ -/)
  (latexEnv := "lemma")]
lemma seed_measure_real_Ioc_min_max (a b : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    seed_measure.real (Set.Ioc (min a b) (max a b)) = |a - b| := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have hsub : Set.Ioc (min a b) (max a b) ∩ Set.Icc (0 : ℝ) 1 =
      Set.Ioc (min a b) (max a b) :=
    Set.inter_eq_self_of_subset_left
      (fun r hr => ⟨le_trans (le_min ha0 hb0) hr.1.le, le_trans hr.2 (max_le ha1 hb1)⟩)
  rw [seed_measure, MeasureTheory.measureReal_def,
    MeasureTheory.Measure.restrict_apply measurableSet_Ioc, hsub, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr min_le_max), max_sub_min_eq_abs, abs_sub_comm]

@[blueprint "lem:threshold-disagree-eq-abs-diff"
  (statement := /-- Let $f : [n]^{m} \to \mathbb{R}$ satisfy $f(X) \in [0,1]$ for every sample
  sequence $X$, and let $X, X' \in [n]^{m}$. Then the random threshold algorithm associated with
  $f$ disagrees on $X$ and $X'$ with seed probability exactly the gap between the two scores:
  \[
    \mathrm{Pr}_{r \sim \mathrm{Unif}([0,1])}\left[A(X;r) \neq A(X';r)\right]
      \;=\; \left|f(X) - f(X')\right|,
  \]
  where $A$ is the random threshold algorithm of \cref{def:threshold-tester}. -/)
  (proof := /-- Write $t = f(X)$ and $t' = f(X')$; by the hypothesis on $f$ both lie in $[0,1]$.
  By \cref{lem:threshold-disagree-set}, the set of seeds on which the random threshold algorithm
  associated with $f$ disagrees on $X$ and $X'$ is exactly the half-open interval
  $\left(\min\{t, t'\}, \max\{t, t'\}\right]$; rewriting the disagreement set by this identity
  reduces the claim to computing the seed measure of that interval. By
  \cref{lem:seed-measure-real-Ioc-min-max}, applied to $a = t$ and $b = t'$, which lie in $[0,1]$,
  that seed measure equals $|t - t'| = |f(X) - f(X')|$. This is the claim. -/)
  (title := /-- Seed disagreement of a random threshold algorithm -/)
  (latexEnv := "lemma")]
lemma threshold_disagree_eq_abs_diff {n m : ℕ} (f : (Fin m → Fin n) → ℝ)
    (hf : ∀ X, f X ∈ Set.Icc (0 : ℝ) 1) (X X' : Fin m → Fin n) :
    seed_measure.real {r : ℝ | threshold_tester f X r ≠ threshold_tester f X' r} =
      |f X - f X'| := by
  rw [threshold_disagree_set f X X', seed_measure_real_Ioc_min_max (f X) (f X') (hf X) (hf X')]

@[blueprint "lem:seed-measure-ne-top"
  (statement := /-- The seed measure of \cref{def:seed-measure} assigns finite mass to every
  subset of the reals: for every set $s \subseteq \mathbb{R}$,
  \[
    \mathrm{Unif}([0,1])(s) \;\neq\; \infty .
  \]
  This is the finiteness hypothesis required to pass from the extended nonnegative measure to its
  real-valued version and to use monotonicity of the latter. -/)
  (proof := /-- Fix a set $s \subseteq \mathbb{R}$. Since $s \subseteq \mathbb{R}$, monotonicity
  of the seed measure gives
  $\mathrm{Unif}([0,1])(s) \le \mathrm{Unif}([0,1])(\mathbb{R})$, and by
  \cref{lem:seed-measure-univ} the right-hand side equals $1$; hence
  $\mathrm{Unif}([0,1])(s) \le 1$. In the extended nonnegative reals $1 \neq \infty$, and any
  element bounded above by an element different from $\infty$ is itself different from $\infty$.
  Therefore $\mathrm{Unif}([0,1])(s) \neq \infty$. -/)
  (title := /-- The seed measure is finite on every set -/)
  (latexEnv := "lemma")]
lemma seed_measure_ne_top (s : Set ℝ) : seed_measure s ≠ ⊤ := by
  have h : seed_measure s ≤ 1 := by
    calc seed_measure s ≤ seed_measure Set.univ := measure_mono (Set.subset_univ s)
      _ = 1 := seed_measure_univ
  exact ne_top_of_le_ne_top ENNReal.one_ne_top h

@[blueprint "lem:seed-accept-prob-le-add-disagree"
  (statement := /-- Let $A$ be a tester on $n$ and $m$ and let $X, X' \in [n]^{m}$ be sample
  sequences. Then the seed acceptance probability of \cref{def:seed-accept-prob} on $X$ is
  bounded by the one on $X'$ plus the seed disagreement probability of the pair:
  \[
    \mathrm{Pr}_{r \sim \mathrm{Unif}([0,1])}\left[A(X;r) = \mathrm{accept}\right]
      \;\le\; \mathrm{Pr}_{r \sim \mathrm{Unif}([0,1])}\left[A(X';r) = \mathrm{accept}\right]
        + \mathrm{Pr}_{r \sim \mathrm{Unif}([0,1])}\left[A(X;r) \neq A(X';r)\right].
  \]
  This is the one-sided form of the coupling bound; the two-sided form follows by exchanging the
  roles of $X$ and $X'$. -/)
  (proof := /-- Write $S = \{r : A(X;r) = \mathrm{accept}\}$,
  $S' = \{r : A(X';r) = \mathrm{accept}\}$ and $D = \{r : A(X;r) \neq A(X';r)\}$, so that by
  \cref{def:seed-accept-prob} the claim reads
  $\mathrm{Unif}([0,1])(S) \le \mathrm{Unif}([0,1])(S') + \mathrm{Unif}([0,1])(D)$ for the
  real-valued seed measure.

  First, $S \subseteq S' \cup D$. Indeed, let $r \in S$, so $A(X;r) = \mathrm{accept}$. If
  $A(X';r) = \mathrm{accept}$ then $r \in S'$. Otherwise $A(X';r) \neq \mathrm{accept}$, so
  $A(X';r)$ differs from $A(X;r) = \mathrm{accept}$, that is $r \in D$. In both cases
  $r \in S' \cup D$.

  By \cref{lem:seed-measure-ne-top} the seed measure of the set $S' \cup D$ is finite, so
  monotonicity of the real-valued seed measure applies to the inclusion above and gives
  $\mathrm{Unif}([0,1])(S) \le \mathrm{Unif}([0,1])(S' \cup D)$. Subadditivity of the
  real-valued measure on a union of two sets gives
  $\mathrm{Unif}([0,1])(S' \cup D) \le \mathrm{Unif}([0,1])(S') + \mathrm{Unif}([0,1])(D)$.
  Chaining the two inequalities yields the claim. -/)
  (title := /-- One-sided coupling bound for the acceptance probability -/)
  (latexEnv := "lemma")]
lemma seed_accept_prob_le_add_disagree {n m : ℕ} (A : tester n m) (X X' : Fin m → Fin n) :
    seed_accept_prob A X ≤
      seed_accept_prob A X' + seed_measure.real {r : ℝ | A X r ≠ A X' r} := by
  have hsub : {r : ℝ | A X r = true} ⊆
      {r : ℝ | A X' r = true} ∪ {r : ℝ | A X r ≠ A X' r} := by
    intro r hr
    simp only [Set.mem_setOf_eq] at hr
    by_cases h : A X' r = true
    · exact Or.inl h
    · refine Or.inr ?_
      simp only [Set.mem_setOf_eq]
      rw [hr]
      exact fun hc => h hc.symm
  simp only [seed_accept_prob]
  calc seed_measure.real {r : ℝ | A X r = true}
      ≤ seed_measure.real ({r : ℝ | A X' r = true} ∪ {r : ℝ | A X r ≠ A X' r}) :=
        measureReal_mono hsub (seed_measure_ne_top _)
    _ ≤ seed_measure.real {r : ℝ | A X' r = true} +
        seed_measure.real {r : ℝ | A X r ≠ A X' r} := measureReal_union_le _ _

@[blueprint "lem:coupling-disagree-lower-bound"
  (statement := /-- Let $A$ be a measurable tester on $n$ and $m$ in the sense of
  \cref{def:measurable-tester}, and let $X, X' \in [n]^{m}$ be sample sequences. Then
  \[
    \mathrm{Pr}_{r \sim \mathrm{Unif}([0,1])}\left[A(X;r) \neq A(X';r)\right]
      \;\ge\; \left|\mathrm{Pr}_{r}\left[A(X;r) = \mathrm{accept}\right]
        - \mathrm{Pr}_{r}\left[A(X';r) = \mathrm{accept}\right]\right| .
  \]
  That is, the probability that the two runs of $A$ on the shared seed $r$ disagree is at least
  the gap between their acceptance probabilities. -/)
  (proof := /-- Write $a = \mathrm{Pr}_{r}[A(X;r) = \mathrm{accept}]$ and
  $a' = \mathrm{Pr}_{r}[A(X';r) = \mathrm{accept}]$ for the two seed acceptance probabilities of
  \cref{def:seed-accept-prob}, and let $D = \{r : A(X;r) \neq A(X';r)\}$ and
  $D' = \{r : A(X';r) \neq A(X;r)\}$ be the two disagreement events.

  The two disagreement events coincide as sets: for each seed $r$, the Booleans $A(X;r)$ and
  $A(X';r)$ satisfy $A(X';r) \neq A(X;r)$ if and only if $A(X;r) \neq A(X';r)$, by symmetry of
  disequality. Hence $\mathrm{Unif}([0,1])(D') = \mathrm{Unif}([0,1])(D)$.

  Applying \cref{lem:seed-accept-prob-le-add-disagree} to the ordered pair $(X, X')$ gives
  $a \le a' + \mathrm{Unif}([0,1])(D)$, and applying it to the ordered pair $(X', X)$ gives
  $a' \le a + \mathrm{Unif}([0,1])(D')$, which by the set identity above is
  $a' \le a + \mathrm{Unif}([0,1])(D)$.

  A real number $|a - a'|$ is bounded by a real number $c$ precisely when both
  $a - a' \le c$ and $a' - a \le c$ hold. With $c = \mathrm{Unif}([0,1])(D)$, the first of these
  is the first displayed inequality rearranged, and the second is the second displayed inequality
  rearranged. Therefore $|a - a'| \le \mathrm{Unif}([0,1])(D)$, which is the claim. -/)
  (title := /-- Disagreement dominates the acceptance gap -/)
  (latexEnv := "lemma")]
lemma coupling_disagree_lower_bound {n m : ℕ} (A : tester n m) (hA : measurable_tester A)
    (X X' : Fin m → Fin n) :
    |seed_accept_prob A X - seed_accept_prob A X'| ≤
      seed_measure.real {r : ℝ | A X r ≠ A X' r} := by
  have hsymm : {r : ℝ | A X' r ≠ A X r} = {r : ℝ | A X r ≠ A X' r} := by
    ext r
    exact ne_comm
  have h₁ := seed_accept_prob_le_add_disagree A X X'
  have h₂ := seed_accept_prob_le_add_disagree A X' X
  rw [hsymm] at h₂
  rw [abs_sub_le_iff]
  constructor
  · linarith
  · linarith

@[blueprint "lem:sample-weight-sum-one"
  (statement := /-- Let $p$ be a distribution on the domain $[n]$ and let $m$ be a sample size.
  Then the product weights of \cref{def:sample-weight} form a probability distribution on the
  sample sequences:
  \[
    \sum_{X \in [n]^{m}} p^{\otimes m}(X) \;=\; \sum_{X \in [n]^{m}} \prod_{i=1}^{m} p(X_i)
      \;=\; 1 ,
  \]
  where the sum ranges over all $n^{m}$ sample sequences $X : [m] \to [n]$. -/)
  (proof := /-- We first record that the real-valued masses of $p$ sum to one, that is,
  $\sum_{j \in [n]} p(j) = 1$. Indeed, $p$ is a probability mass function with values in
  $[0, \infty]$ whose total mass is $\sum_{j \in [n]} p(j) = 1$, because on the finite domain
  $[n]$ the defining unconditional sum of a probability mass function is the finite sum over
  $[n]$. Each value $p(j)$ is finite, since it is bounded above by the total mass $1$, so passing
  to real values commutes with this finite sum and the real masses sum to the real number $1$.

  Now expand the left-hand side. By \cref{def:sample-weight} the summand is
  $p^{\otimes m}(X) = \prod_{i=1}^{m} p(X_i)$, and the index set of all sample sequences
  $X : [m] \to [n]$ is the set of all choice functions selecting, for each coordinate
  $i \in [m]$, a value in $[n]$. Summing a product over this index set factorises as the product
  over the coordinates of the sums over the values, that is,
  \[
    \sum_{X : [m] \to [n]} \prod_{i=1}^{m} p(X_i)
      \;=\; \prod_{i=1}^{m} \left(\sum_{j \in [n]} p(j)\right),
  \]
  which is the distributivity of a finite product over finite sums: expanding the right-hand side
  produces exactly one term for each way of choosing one summand $p(X_i)$ in each of the $m$
  factors, and such a choice is precisely a sample sequence $X$. Substituting the total mass
  $\sum_{j \in [n]} p(j) = 1$ from the first paragraph, the product over the $m$ coordinates is
  $1^{m} = 1$, as claimed. -/)
  (title := /-- The product weights sum to one -/)
  (latexEnv := "lemma")]
lemma sample_weight_sum_one {n : ℕ} (p : PMF (Fin n)) (m : ℕ) :
    ∑ X : Fin m → Fin n, sample_weight p X = 1 := by
  have hmass : ∑ j : Fin n, (p j).toReal = 1 := by
    have hone : ∑ j : Fin n, p j = 1 := by simpa using p.tsum_coe
    rw [← ENNReal.toReal_sum (fun j _ => PMF.apply_ne_top p j), hone, ENNReal.toReal_one]
  calc ∑ X : Fin m → Fin n, sample_weight p X
      = ∑ X ∈ Fintype.piFinset (fun _ : Fin m => (Finset.univ : Finset (Fin n))),
          ∏ i : Fin m, (p (X i)).toReal := by
        simp [sample_weight, Fintype.piFinset_univ]
    _ = ∏ _i : Fin m, ∑ j : Fin n, (p j).toReal :=
        (Finset.prod_univ_sum (fun _ => Finset.univ) (fun _ j => (p j).toReal)).symm
    _ = 1 := by simp [hmass]

@[blueprint "lem:sample-weight-nonneg"
  (statement := /-- Let $p$ be a distribution on the domain $[n]$ and let $X \in [n]^{m}$ be a
  sample sequence. Then $p^{\otimes m}(X) \ge 0$, where $p^{\otimes m}$ is the product weight of
  \cref{def:sample-weight}. -/)
  (proof := /-- By \cref{def:sample-weight}, the weight is the product
  $\prod_{i=1}^{m} p(X_i)$ of the values of the probability mass function $p$ at the sample
  points, each of which is a nonnegative real number. A finite product of nonnegative reals is
  nonnegative. -/)
  (title := /-- The product weights are nonnegative -/)
  (latexEnv := "lemma")]
lemma sample_weight_nonneg {n m : ℕ} (p : PMF (Fin n)) (X : Fin m → Fin n) :
    0 ≤ sample_weight p X := by
  exact Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg

@[blueprint "lem:sample-weight-order-invariant"
  (statement := /-- Let $p$ be a distribution on $[n]$, let $\sigma$ be a permutation of the
  sample positions $[m]$, and let $X \in [n]^{m}$ be a sample sequence. Then reordering the
  samples does not change their product weight:
  \[
    p^{\otimes m}(X_{\sigma}) \;=\; p^{\otimes m}(X),
    \qquad X_{\sigma} = (X_{\sigma(1)},\dots,X_{\sigma(m)}).
  \]
  Equivalently, $X_{\sigma}$ has the same law as $X$ when $X \sim p^{\otimes m}$; this is the
  identity in distribution $X_{\sigma} \overset{d}{=} X$ used in Lemma~\ref{lem:order_invariant} of
  the source. -/)
  (proof := /-- By \cref{def:sample-weight}, the weight of $X_{\sigma}$ is
  $\prod_{i=1}^{m} p(X_{\sigma(i)})$. Since $\sigma$ is a bijection of the index set $[m]$,
  reindexing a finite product along it permutes its factors and hence leaves the product
  unchanged, giving $\prod_{i=1}^{m} p(X_{\sigma(i)}) = \prod_{i=1}^{m} p(X_i)$, which is the
  weight of $X$. -/)
  (title := /-- Product weights are invariant under reordering samples -/)
  (latexEnv := "lemma")]
lemma sample_weight_order_invariant {n m : ℕ} (p : PMF (Fin n)) (σ : Equiv.Perm (Fin m))
    (X : Fin m → Fin n) :
    sample_weight p (X ∘ σ) = sample_weight p X := by
  simpa [sample_weight] using Equiv.prod_comp σ (fun i => (p (X i)).toReal)

@[blueprint "lem:sample-weight-perm-pmf"
  (statement := /-- Let $p$ be a distribution on $[n]$, let $\pi$ be a permutation of $[n]$, and
  let $X \in [n]^{m}$ be a sample sequence. Then
  \[
    (p^{\pi})^{\otimes m}(\pi(X)) \;=\; p^{\otimes m}(X),
    \qquad \pi(X) = (\pi(X_1),\dots,\pi(X_m)),
  \]
  where $p^{\pi}$ is the relabelled distribution of \cref{def:perm-pmf}. Equivalently,
  $\pi(X) \sim (p^{\pi})^{\otimes m}$ whenever $X \sim p^{\otimes m}$; this is the change of
  variables used in Lemma~\ref{lem:label_invariant} of the source. -/)
  (proof := /-- By \cref{def:sample-weight}, the left-hand side is
  $\prod_{i=1}^{m} p^{\pi}(\pi(X_i))$. By \cref{def:perm-pmf}, the relabelled distribution is
  the push-forward of $p$ along the bijection $\pi$, so $p^{\pi}(\pi(j)) = p(j)$ for every
  $j \in [n]$: the push-forward assigns to $\pi(j)$ the total mass of its unique preimage $j$.
  Applying this with $j = X_i$ for each coordinate $i$ turns the product into
  $\prod_{i=1}^{m} p(X_i)$, which is $p^{\otimes m}(X)$. -/)
  (title := /-- Relabelling samples matches relabelling the distribution -/)
  (latexEnv := "lemma")]
lemma sample_weight_perm_pmf {n m : ℕ} (p : PMF (Fin n)) (π : Equiv.Perm (Fin n))
    (X : Fin m → Fin n) :
    sample_weight (perm_pmf π p) (π ∘ X) = sample_weight p X := by
  simp [sample_weight, perm_pmf, PMF.map_apply]

@[blueprint "lem:score-replicable-of-replicable"
  (statement := /-- Let $\rho \in \mathbb{R}$ and let $A$ be a measurable tester on $n$ and $m$
  in the sense of \cref{def:measurable-tester} which is $\rho$-replicable in the sense of
  \cref{def:replicable}. Then its seed acceptance probability
  $f(X) = \mathrm{Pr}_{r}[A(X;r) = \mathrm{accept}]$ is $\rho$-score replicable in the sense of
  \cref{def:score-replicable}, that is, for every distribution $p$ on $[n]$,
  \[
    \mathbb{E}_{X, X' \sim p^{\otimes m}}\left|f(X) - f(X')\right| \;\le\; \rho .
  \]
  This is the entry step of the replicability argument of Lemma~\ref{lem:canonical} of the source:
  replicability of the original algorithm is converted into a bound on the expected gap of its
  acceptance probability. -/)
  (proof := /-- Fix a distribution $p$ on $[n]$. By \cref{lem:coupling-disagree-lower-bound},
  applied to each pair of sample sequences $(X, X')$ and using the measurability of $A$, we have
  $\left|f(X) - f(X')\right| \le \mathrm{Pr}_{r}\left[A(X;r) \neq A(X';r)\right]$ for every pair
  $(X, X')$. By \cref{lem:seed-disagree-eq}, again using the measurability of $A$, the seed
  agreement probability satisfies
  $\mathrm{Pr}_{r}[A(X;r) = A(X';r)] = 1 - \mathrm{Pr}_{r}[A(X;r) \neq A(X';r)]$, so eliminating
  the disagreement probability between these two relations gives the pointwise bound
  \[
    \left|f(X) - f(X')\right| \;\le\; 1 - \mathrm{Pr}_{r}\left[A(X;r) = A(X';r)\right] .
  \]
  The weights $p^{\otimes m}(X)\, p^{\otimes m}(X')$ of \cref{def:sample-weight} are nonnegative
  by \cref{lem:sample-weight-nonneg}, so multiplying the pointwise bound by them preserves the
  inequality, and summing the resulting inequalities over all pairs $(X, X')$ gives
  \[
    \mathbb{E}_{X,X'}\left|f(X) - f(X')\right|
      \;\le\; \sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')
        \left(1 - \mathrm{Pr}_{r}\left[A(X;r) = A(X';r)\right]\right).
  \]
  The weights sum to $1$ over all pairs, since
  $\sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')
    = \left(\sum_{X} p^{\otimes m}(X)\right)^{2} = 1$ by \cref{lem:sample-weight-sum-one}, so
  splitting the last sum along the subtraction shows that its right-hand side equals
  \[
    1 - \sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')\,
      \mathrm{Pr}_{r}\left[A(X;r) = A(X';r)\right],
  \]
  which is at most $1 - (1 - \rho) = \rho$ because the double sum is at least $1 - \rho$ by the
  $\rho$-replicability of $A$ from \cref{def:replicable}. Chaining the two displays with this
  bound gives $\mathbb{E}_{X,X'}\left|f(X) - f(X')\right| \le \rho$, which is the claim by
  \cref{def:score-replicable}. -/)
  (title := /-- Replicability implies score replicability -/)
  (latexEnv := "lemma")]
lemma score_replicable_of_replicable {n m : ℕ} (ρ : ℝ) (A : tester n m)
    (hA : measurable_tester A) (hrep : replicable ρ A) :
    score_replicable ρ (seed_accept_prob A) := by
  intro p
  have hstep : ∀ X X' : Fin m → Fin n,
      sample_weight p X * sample_weight p X' *
          |seed_accept_prob A X - seed_accept_prob A X'| ≤
        sample_weight p X * sample_weight p X' -
          sample_weight p X * sample_weight p X' *
            seed_measure.real {r : ℝ | A X r = A X' r} := by
    intro X X'
    have hw : 0 ≤ sample_weight p X * sample_weight p X' :=
      mul_nonneg (sample_weight_nonneg p X) (sample_weight_nonneg p X')
    have hle := coupling_disagree_lower_bound A hA X X'
    have heq := seed_disagree_eq A hA X X'
    have hb : |seed_accept_prob A X - seed_accept_prob A X'| ≤
        1 - seed_measure.real {r : ℝ | A X r = A X' r} := by linarith
    calc sample_weight p X * sample_weight p X' *
          |seed_accept_prob A X - seed_accept_prob A X'|
        ≤ sample_weight p X * sample_weight p X' *
            (1 - seed_measure.real {r : ℝ | A X r = A X' r}) :=
          mul_le_mul_of_nonneg_left hb hw
      _ = sample_weight p X * sample_weight p X' -
            sample_weight p X * sample_weight p X' *
              seed_measure.real {r : ℝ | A X r = A X' r} := by ring
  have hweights : ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
      sample_weight p X * sample_weight p X' = 1 := by
    rw [← Finset.sum_mul_sum, sample_weight_sum_one p m, mul_one]
  have hmain : ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
      sample_weight p X * sample_weight p X' *
        |seed_accept_prob A X - seed_accept_prob A X'| ≤
      ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
        (sample_weight p X * sample_weight p X' -
          sample_weight p X * sample_weight p X' *
            seed_measure.real {r : ℝ | A X r = A X' r}) :=
    Finset.sum_le_sum fun X _ => Finset.sum_le_sum fun X' _ => hstep X X'
  have hsplit : ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
      (sample_weight p X * sample_weight p X' -
        sample_weight p X * sample_weight p X' *
          seed_measure.real {r : ℝ | A X r = A X' r}) =
      1 - ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
        sample_weight p X * sample_weight p X' *
          seed_measure.real {r : ℝ | A X r = A X' r} := by
    simp only [Finset.sum_sub_distrib, hweights]
  have hrp := hrep p
  rw [hsplit] at hmain
  simpa [score_replicable, seed_accept_prob] using hmain.trans (by linarith)

@[blueprint "lem:order-avg-abs-sub-le"
  (statement := /-- Let $f : [n]^{m} \to \mathbb{R}$ and let $X, X' \in [n]^{m}$ be two sample
  sequences. Then the order averages of \cref{def:order-avg} satisfy
  \[
    \left|(\mathrm{ordAvg}\, f)(X) - (\mathrm{ordAvg}\, f)(X')\right|
      \;\le\; \frac{1}{m!}\sum_{\sigma}\left|f(X_{\sigma}) - f(X'_{\sigma})\right|,
  \]
  the average on the right running over all $m!$ permutations $\sigma$ of the sample
  positions $[m]$, with $X_{\sigma} = (X_{\sigma(1)},\dots,X_{\sigma(m)})$. -/)
  (proof := /-- By \cref{def:order-avg} both order averages are averages over the same index
  set of permutations $\sigma$ of $[m]$, so their difference is the average of the differences,
  \[
    (\mathrm{ordAvg}\, f)(X) - (\mathrm{ordAvg}\, f)(X')
      = \frac{1}{m!}\sum_{\sigma}\left(f(X_{\sigma}) - f(X'_{\sigma})\right),
  \]
  because an average is a scalar multiple of a finite sum and a finite sum distributes over
  subtraction. Taking absolute values and applying the triangle inequality for averages, which
  states that the absolute value of an average is at most the average of the absolute values,
  yields the claimed bound. -/)
  (title := /-- The order average is a contraction for the pairwise distance -/)
  (latexEnv := "lemma")]
lemma order_avg_abs_sub_le {n m : ℕ} (f : (Fin m → Fin n) → ℝ) (X X' : Fin m → Fin n) :
    |order_avg f X - order_avg f X'|
      ≤ 𝔼 σ : Equiv.Perm (Fin m), |f (X ∘ σ) - f (X' ∘ σ)| := by
  have hsub : order_avg f X - order_avg f X'
      = 𝔼 σ : Equiv.Perm (Fin m), (f (X ∘ σ) - f (X' ∘ σ)) := by
    simp only [order_avg, Finset.expect_sub_distrib]
  rw [hsub]
  exact Finset.abs_expect_le _ _

@[blueprint "lem:score-sum-order-reindex"
  (statement := /-- Let $p$ be a distribution on $[n]$, let $f : [n]^{m} \to \mathbb{R}$, and let
  $\sigma$ be a permutation of the sample positions $[m]$. Then reordering the arguments of $f$
  inside the score replicability sum of \cref{def:score-replicable} does not change its value:
  \[
    \sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')\,
      \left|f(X_{\sigma}) - f(X'_{\sigma})\right|
    \;=\; \sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')\,
      \left|f(X) - f(X')\right|,
  \]
  where both double sums range over all sample sequences $X, X' \in [n]^{m}$, the weights are
  the product weights of \cref{def:sample-weight}, and
  $X_{\sigma} = (X_{\sigma(1)},\dots,X_{\sigma(m)})$. -/)
  (proof := /-- By \cref{lem:sample-weight-order-invariant} the product weights are unchanged by
  reordering, that is $p^{\otimes m}(X_{\sigma}) = p^{\otimes m}(X)$ and likewise for $X'$, so
  each summand on the left may be rewritten as
  $p^{\otimes m}(X_{\sigma})\, p^{\otimes m}(X'_{\sigma})\,|f(X_{\sigma}) - f(X'_{\sigma})|$,
  which is the value at $(X_{\sigma}, X'_{\sigma})$ of the function
  $(Y, Y') \mapsto p^{\otimes m}(Y)\, p^{\otimes m}(Y')\, |f(Y) - f(Y')|$ summed on the right.
  The map $X \mapsto X_{\sigma}$ is a bijection of the finite set $[n]^{m}$ of sample sequences,
  with inverse $X \mapsto X_{\sigma^{-1}}$, since composing with $\sigma$ and then with
  $\sigma^{-1}$ restores every coordinate. Reindexing the outer sum over $X$ and the inner sum
  over $X'$ along this bijection therefore leaves the total unchanged and produces exactly the
  right-hand side. -/)
  (title := /-- Reordering samples does not change the score replicability sum -/)
  (latexEnv := "lemma")]
lemma score_sum_order_reindex {n m : ℕ} (p : PMF (Fin n)) (f : (Fin m → Fin n) → ℝ)
    (σ : Equiv.Perm (Fin m)) :
    ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
        sample_weight p X * sample_weight p X' * |f (X ∘ σ) - f (X' ∘ σ)|
      = ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
        sample_weight p X * sample_weight p X' * |f X - f X'| := by
  have hbij : Function.Bijective (fun X : Fin m → Fin n => X ∘ σ) := by
    refine ⟨fun X Y hXY => ?_, fun Y => ⟨Y ∘ σ.symm, ?_⟩⟩
    · funext i
      have := congrFun hXY (σ.symm i)
      simpa using this
    · funext i
      simp
  refine Fintype.sum_bijective _ hbij _ _ fun X => ?_
  refine Fintype.sum_bijective _ hbij _ _ fun X' => ?_
  rw [sample_weight_order_invariant p σ X, sample_weight_order_invariant p σ X']

@[blueprint "lem:score-replicable-order-avg"
  (statement := /-- Let $\rho \in \mathbb{R}$ and let $f : [n]^{m} \to \mathbb{R}$ be
  $\rho$-score replicable in the sense of \cref{def:score-replicable}. Then its order average
  $\mathrm{ordAvg}\, f$ of \cref{def:order-avg} is also $\rho$-score replicable:
  \[
    \mathbb{E}_{X, X' \sim p^{\otimes m}}
      \left|(\mathrm{ordAvg}\, f)(X) - (\mathrm{ordAvg}\, f)(X')\right| \;\le\; \rho
    \qquad\text{for every distribution } p \text{ on } [n].
  \]
  This is the replicability half of Lemma~\ref{lem:order_invariant} of the source, in the score
  formulation. -/)
  (proof := /-- Fix a distribution $p$ on $[n]$. By \cref{def:order-avg},
  by \cref{def:score-replicable} the claim to prove is
  \[
    \sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')\,
      \left|(\mathrm{ordAvg}\, f)(X) - (\mathrm{ordAvg}\, f)(X')\right| \;\le\; \rho,
  \]
  the double sum running over all sample sequences $X, X' \in [n]^{m}$.

  Fix a pair $(X, X')$. By \cref{lem:order-avg-abs-sub-le},
  \[
    \left|(\mathrm{ordAvg}\, f)(X) - (\mathrm{ordAvg}\, f)(X')\right|
      \;\le\; \frac{1}{m!}\sum_{\sigma}\left|f(X_{\sigma}) - f(X'_{\sigma})\right|,
  \]
  the average running over all $m!$ permutations $\sigma$ of the sample positions $[m]$. The
  product weights of \cref{def:sample-weight} are nonnegative by
  \cref{lem:sample-weight-nonneg}, hence so is their product
  $p^{\otimes m}(X)\, p^{\otimes m}(X')$, and multiplying the displayed inequality by this
  nonnegative factor preserves it. Since multiplication by a fixed scalar commutes with a finite
  average, this gives, for every pair $(X, X')$,
  \[
    p^{\otimes m}(X)\, p^{\otimes m}(X')\,
      \left|(\mathrm{ordAvg}\, f)(X) - (\mathrm{ordAvg}\, f)(X')\right|
    \;\le\; \frac{1}{m!}\sum_{\sigma} p^{\otimes m}(X)\, p^{\otimes m}(X')\,
      \left|f(X_{\sigma}) - f(X'_{\sigma})\right| .
  \]
  Summing these termwise inequalities over $X$ and then over $X'$, and exchanging the finite
  double sum over $(X, X')$ with the finite average over $\sigma$, bounds the quantity to be
  estimated by
  \[
    \frac{1}{m!}\sum_{\sigma}
      \sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')\,
        \left|f(X_{\sigma}) - f(X'_{\sigma})\right| .
  \]
  It therefore suffices to bound each term of this average by $\rho$, since an average over the
  nonempty index set of permutations of $[m]$ of quantities all at most $\rho$ is itself at most
  $\rho$. Fix $\sigma$. By \cref{lem:score-sum-order-reindex} the corresponding double sum equals
  \[
    \sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')\,\left|f(X) - f(X')\right|,
  \]
  which is at most $\rho$ by the assumed $\rho$-score replicability of $f$ applied to the
  distribution $p$. This completes the proof. -/)
  (title := /-- Order averaging preserves score replicability -/)
  (latexEnv := "lemma")]
lemma score_replicable_order_avg {n m : ℕ} (ρ : ℝ) (f : (Fin m → Fin n) → ℝ)
    (hf : score_replicable ρ f) :
    score_replicable ρ (order_avg f) := by
  intro p
  have key : ∀ X X' : Fin m → Fin n,
      sample_weight p X * sample_weight p X' * |order_avg f X - order_avg f X'|
        ≤ 𝔼 σ : Equiv.Perm (Fin m),
            sample_weight p X * sample_weight p X' * |f (X ∘ σ) - f (X' ∘ σ)| := by
    intro X X'
    rw [← Finset.mul_expect]
    exact mul_le_mul_of_nonneg_left (order_avg_abs_sub_le f X X')
      (mul_nonneg (sample_weight_nonneg p X) (sample_weight_nonneg p X'))
  calc ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
        sample_weight p X * sample_weight p X' * |order_avg f X - order_avg f X'|
      ≤ ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
          𝔼 σ : Equiv.Perm (Fin m),
            sample_weight p X * sample_weight p X' * |f (X ∘ σ) - f (X' ∘ σ)| :=
        Finset.sum_le_sum fun X _ => Finset.sum_le_sum fun X' _ => key X X'
    _ = 𝔼 σ : Equiv.Perm (Fin m), ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
          sample_weight p X * sample_weight p X' * |f (X ∘ σ) - f (X' ∘ σ)| := by
        simp only [Finset.expect_sum_comm]
    _ ≤ ρ := by
        refine Finset.expect_le Finset.univ_nonempty fun σ _ => ?_
        rw [score_sum_order_reindex p f σ]
        exact hf p

@[blueprint "lem:label-avg-abs-sub-le-expect"
  (statement := /-- Let $f : [n]^{m} \to \mathbb{R}$ be a deterministic function of the sample
  sequence and let $X, X' \in [n]^{m}$ be sample sequences. Then the label averages of
  \cref{def:label-avg} satisfy
  \[
    \left|(\mathrm{labAvg}\, f)(X) - (\mathrm{labAvg}\, f)(X')\right|
      \;\le\; \frac{1}{n!}\sum_{\pi}\left|f(\pi(X)) - f(\pi(X'))\right|,
  \]
  where $\pi$ runs over all $n!$ permutations of the domain $[n]$ and
  $\pi(X) = (\pi(X_1),\dots,\pi(X_m))$. -/)
  (proof := /-- By \cref{def:label-avg} the two label averages are averages of $f$ over the same
  finite index set, namely the set of permutations $\pi$ of $[n]$, so their difference is the
  average of the pointwise differences:
  \[
    (\mathrm{labAvg}\, f)(X) - (\mathrm{labAvg}\, f)(X')
      = \frac{1}{n!}\sum_{\pi}\left(f(\pi(X)) - f(\pi(X'))\right).
  \]
  Taking absolute values and applying the triangle inequality for averages, which bounds the
  absolute value of an average of reals by the average of their absolute values, yields
  \[
    \left|(\mathrm{labAvg}\, f)(X) - (\mathrm{labAvg}\, f)(X')\right|
      \;\le\; \frac{1}{n!}\sum_{\pi}\left|f(\pi(X)) - f(\pi(X'))\right|,
  \]
  which is the assertion. -/)
  (title := /-- The label average is Lipschitz for the averaged absolute differences -/)
  (latexEnv := "lemma")]
lemma label_avg_abs_sub_le_expect {n m : ℕ} (f : (Fin m → Fin n) → ℝ)
    (X X' : Fin m → Fin n) :
    |label_avg f X - label_avg f X'|
      ≤ 𝔼 π : Equiv.Perm (Fin n), |f (π ∘ X) - f (π ∘ X')| := by
  simp only [label_avg]
  rw [← Finset.expect_sub_distrib]
  exact Finset.abs_expect_le _ _

@[blueprint "lem:score-sum-perm-reindex"
  (statement := /-- Let $p$ be a distribution on $[n]$, let $\pi$ be a permutation of $[n]$, and
  let $f : [n]^{m} \to \mathbb{R}$ be a deterministic function of the sample sequence. Then,
  with $p^{\otimes m}$ the product weight of \cref{def:sample-weight} and $p^{\pi}$ the
  relabelled distribution of \cref{def:perm-pmf},
  \[
    \sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')\,
        \left|f(\pi(X)) - f(\pi(X'))\right|
      \;=\; \sum_{Y}\sum_{Y'} (p^{\pi})^{\otimes m}(Y)\, (p^{\pi})^{\otimes m}(Y')\,
        \left|f(Y) - f(Y')\right|,
  \]
  all four sums running over the finite set $[n]^{m}$ of sample sequences and
  $\pi(X) = (\pi(X_1),\dots,\pi(X_m))$. -/)
  (proof := /-- The map $X \mapsto \pi(X)$ is a bijection of the finite set $[n]^{m}$ of sample
  sequences onto itself, being the postcomposition with the bijection $\pi$ of $[n]$; its
  inverse is $Y \mapsto \pi^{-1}(Y)$. A finite sum is unchanged when its index set is reindexed
  along a bijection, so it suffices to check that the summand on the left indexed by the pair
  $(X, X')$ equals the summand on the right indexed by the image pair $(\pi(X), \pi(X'))$;
  we reindex the outer sum and then, for each fixed $X$, the inner sum along this bijection.
  For the summands, \cref{lem:sample-weight-perm-pmf} gives
  $(p^{\pi})^{\otimes m}(\pi(X)) = p^{\otimes m}(X)$ and, applied to $X'$,
  $(p^{\pi})^{\otimes m}(\pi(X')) = p^{\otimes m}(X')$, while the remaining factor
  $\left|f(\pi(X)) - f(\pi(X'))\right|$ is literally the factor
  $\left|f(Y) - f(Y')\right|$ evaluated at $Y = \pi(X)$ and $Y' = \pi(X')$. Hence the two
  double sums have equal terms after reindexing, and therefore are equal. -/)
  (title := /-- Relabelling the samples transports the score sum to the relabelled distribution -/)
  (latexEnv := "lemma")]
lemma score_sum_perm_reindex {n m : ℕ} (p : PMF (Fin n)) (π : Equiv.Perm (Fin n))
    (f : (Fin m → Fin n) → ℝ) :
    ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
        sample_weight p X * sample_weight p X' * |f (π ∘ X) - f (π ∘ X')|
      = ∑ Y : Fin m → Fin n, ∑ Y' : Fin m → Fin n,
        sample_weight (perm_pmf π p) Y * sample_weight (perm_pmf π p) Y' * |f Y - f Y'| := by
  refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin m)) π) _ _ fun X => ?_
  refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin m)) π) _ _ fun X' => ?_
  have hX : (Equiv.arrowCongr (Equiv.refl (Fin m)) π) X = π ∘ X := rfl
  have hX' : (Equiv.arrowCongr (Equiv.refl (Fin m)) π) X' = π ∘ X' := rfl
  rw [hX, hX', sample_weight_perm_pmf, sample_weight_perm_pmf]

@[blueprint "lem:score-replicable-label-avg"
  (statement := /-- Let $\rho \in \mathbb{R}$ and let $f : [n]^{m} \to \mathbb{R}$ be
  $\rho$-score replicable in the sense of \cref{def:score-replicable}. Then its label average
  $\mathrm{labAvg}\, f$ of \cref{def:label-avg} is also $\rho$-score replicable:
  \[
    \mathbb{E}_{X, X' \sim p^{\otimes m}}
      \left|(\mathrm{labAvg}\, f)(X) - (\mathrm{labAvg}\, f)(X')\right| \;\le\; \rho
    \qquad\text{for every distribution } p \text{ on } [n].
  \]
  This is the replicability half of Lemma~\ref{lem:label_invariant} of the source, in the score
  formulation. The source discharges it with the remark that one follows the structure of the
  proof of Lemma~\ref{lem:order_invariant}; the argument below is that structure, with the domain
  relabelling $\pi$ in place of the position reordering $\sigma$. -/)
  (proof := /-- Fix a distribution $p$ on $[n]$; by \cref{def:score-replicable} we must bound the
  double sum
  $\sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')\,
    \left|(\mathrm{labAvg}\, f)(X) - (\mathrm{labAvg}\, f)(X')\right|$ by $\rho$. We do so in
  three steps.

  First, fix a pair $(X, X')$ of sample sequences. By
  \cref{lem:label-avg-abs-sub-le-expect},
  \[
    \left|(\mathrm{labAvg}\, f)(X) - (\mathrm{labAvg}\, f)(X')\right|
      \;\le\; \frac{1}{n!}\sum_{\pi}\left|f(\pi(X)) - f(\pi(X'))\right| ,
  \]
  the average running over all $n!$ permutations $\pi$ of $[n]$. The coefficient
  $p^{\otimes m}(X)\, p^{\otimes m}(X')$ is a product of two nonnegative reals by
  \cref{lem:sample-weight-nonneg}, hence nonnegative, so multiplying the displayed inequality by
  it preserves the inequality; pulling the constant coefficient inside the average over $\pi$ and
  summing the resulting inequalities over all pairs $(X, X')$ gives
  \[
    \sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')\,
        \left|(\mathrm{labAvg}\, f)(X) - (\mathrm{labAvg}\, f)(X')\right|
      \;\le\; \sum_{X}\sum_{X'} \frac{1}{n!}\sum_{\pi}
        p^{\otimes m}(X)\, p^{\otimes m}(X')\, \left|f(\pi(X)) - f(\pi(X'))\right| .
  \]

  Second, all three index sets are finite, so the average over $\pi$ commutes with the two sums
  over $X$ and $X'$, and the right-hand side equals
  \[
    \frac{1}{n!}\sum_{\pi} \sum_{X}\sum_{X'}
      p^{\otimes m}(X)\, p^{\otimes m}(X')\, \left|f(\pi(X)) - f(\pi(X'))\right| .
  \]

  Third, the set of permutations of $[n]$ is nonempty, since it contains the identity, so this
  average is at most $\rho$ as soon as each of its terms is. Fix therefore a permutation $\pi$ of
  $[n]$. By \cref{lem:score-sum-perm-reindex}, the corresponding double sum equals
  \[
    \sum_{Y}\sum_{Y'} (p^{\pi})^{\otimes m}(Y)\, (p^{\pi})^{\otimes m}(Y')\,
      \left|f(Y) - f(Y')\right| ,
  \]
  where $p^{\pi}$ is the relabelled distribution of \cref{def:perm-pmf}. By
  \cref{def:score-replicable}, the assumed $\rho$-score replicability of $f$ applied to the
  distribution $p^{\pi}$ bounds this quantity by $\rho$. Hence every term of the average is at
  most $\rho$, so the average is at most $\rho$, and the claimed bound follows. -/)
  (title := /-- Label averaging preserves score replicability -/)
  (latexEnv := "lemma")]
lemma score_replicable_label_avg {n m : ℕ} (ρ : ℝ) (f : (Fin m → Fin n) → ℝ)
    (hf : score_replicable ρ f) :
    score_replicable ρ (label_avg f) := by
  intro p
  calc ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
        sample_weight p X * sample_weight p X' * |label_avg f X - label_avg f X'|
      ≤ ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
          𝔼 π : Equiv.Perm (Fin n),
            sample_weight p X * sample_weight p X' * |f (π ∘ X) - f (π ∘ X')| := by
        refine Finset.sum_le_sum fun X _ => Finset.sum_le_sum fun X' _ => ?_
        rw [← Finset.mul_expect]
        exact mul_le_mul_of_nonneg_left (label_avg_abs_sub_le_expect f X X')
          (mul_nonneg (sample_weight_nonneg p X) (sample_weight_nonneg p X'))
    _ = 𝔼 π : Equiv.Perm (Fin n), ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
          sample_weight p X * sample_weight p X' * |f (π ∘ X) - f (π ∘ X')| := by
        rw [Finset.expect_sum_comm]
        exact Finset.sum_congr rfl fun X _ => (Finset.expect_sum_comm _ _ _).symm
    _ ≤ ρ := by
        refine Finset.expect_le Finset.univ_nonempty fun π _ => ?_
        rw [score_sum_perm_reindex]
        exact hf (perm_pmf π p)

@[blueprint "lem:replicable-of-score-replicable"
  (statement := /-- Let $\rho \in \mathbb{R}$ and let $f : [n]^{m} \to \mathbb{R}$ satisfy
  $f(X) \in [0,1]$ for every sample sequence $X$, and suppose $f$ is $\rho$-score replicable in
  the sense of \cref{def:score-replicable}. Then the random threshold algorithm associated with
  $f$ by \cref{def:threshold-tester} is $\rho$-replicable in the sense of
  \cref{def:replicable}. -/)
  (proof := /-- Write $A$ for the random threshold algorithm associated with $f$ and fix a
  distribution $p$ on $[n]$. By \cref{lem:threshold-tester-measurable}, $A$ is a measurable
  tester, so \cref{lem:seed-disagree-eq} applies to every pair of sample sequences $(X, X')$ and
  gives
  $\mathrm{Pr}_{r}[A(X;r) = A(X';r)] = 1 - \mathrm{Pr}_{r}[A(X;r) \neq A(X';r)]$. By
  \cref{lem:threshold-disagree-eq-abs-diff}, the disagreement probability equals
  $\left|f(X) - f(X')\right|$. Hence
  \[
    \sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')\,
      \mathrm{Pr}_{r}\left[A(X;r) = A(X';r)\right]
    = \sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')
      \left(1 - \left|f(X) - f(X')\right|\right).
  \]
  The weights sum to $1$ over all pairs by \cref{lem:sample-weight-sum-one}, so the right-hand
  side equals $1 - \mathbb{E}_{X,X'}\left|f(X) - f(X')\right|$, which is at least $1 - \rho$ by
  the $\rho$-score replicability of $f$. This is exactly the inequality required by
  \cref{def:replicable}. -/)
  (title := /-- Score replicability implies replicability of the threshold algorithm -/)
  (latexEnv := "lemma")]
lemma replicable_of_score_replicable {n m : ℕ} (ρ : ℝ) (f : (Fin m → Fin n) → ℝ)
    (hf : ∀ X, f X ∈ Set.Icc (0 : ℝ) 1) (hrep : score_replicable ρ f) :
    replicable ρ (threshold_tester f) := by
  intro p
  have hmeas : measurable_tester (threshold_tester f) := threshold_tester_measurable f
  have key : ∀ X X' : Fin m → Fin n,
      sample_weight p X * sample_weight p X' *
          seed_measure.real {r : ℝ | threshold_tester f X r = threshold_tester f X' r} =
        sample_weight p X * sample_weight p X' -
          sample_weight p X * sample_weight p X' * |f X - f X'| := by
    intro X X'
    rw [seed_disagree_eq (threshold_tester f) hmeas X X',
      threshold_disagree_eq_abs_diff f hf X X']
    ring
  have hweights : ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
      sample_weight p X * sample_weight p X' = 1 := by
    rw [← Finset.sum_mul_sum, sample_weight_sum_one p m, mul_one]
  have hsplit : ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
      sample_weight p X * sample_weight p X' *
        seed_measure.real {r : ℝ | threshold_tester f X r = threshold_tester f X' r} =
      1 - ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
        sample_weight p X * sample_weight p X' * |f X - f X'| := by
    simp only [key, Finset.sum_sub_distrib, hweights]
  rw [hsplit]
  have := hrep p
  linarith

@[blueprint "lem:expect-mem-Icc-of-forall-mem-Icc"
  (statement := /-- Let $I$ be a nonempty finite index set and let $g : I \to \mathbb{R}$ be a
  function satisfying $g(i) \in [0,1]$ for every $i \in I$. Then the average of $g$ over $I$ lies
  in the unit interval:
  \[
    \frac{1}{|I|} \sum_{i \in I} g(i) \;\in\; [0,1] .
  \] -/)
  (proof := /-- Membership in $[0,1]$ is equivalent to the two inequalities
  $0 \le \frac{1}{|I|}\sum_{i \in I} g(i)$ and $\frac{1}{|I|}\sum_{i \in I} g(i) \le 1$, which we
  prove in turn.

  For the lower bound, every summand satisfies $0 \le g(i)$ by hypothesis, so the sum
  $\sum_{i \in I} g(i)$ is nonnegative, and multiplying a nonnegative real by the nonnegative
  scalar $1/|I|$ preserves nonnegativity; hence $0 \le \frac{1}{|I|}\sum_{i \in I} g(i)$.

  For the upper bound, $I$ is nonempty, so $|I| > 0$ and the average is well behaved: since
  $g(i) \le 1$ for every $i \in I$, we have $\sum_{i \in I} g(i) \le |I| \cdot 1$, and dividing by
  the positive quantity $|I|$ gives $\frac{1}{|I|}\sum_{i \in I} g(i) \le 1$, as required. -/)
  (title := /-- An average of numbers in the unit interval lies in the unit interval -/)
  (latexEnv := "lemma")]
lemma expect_mem_Icc_of_forall_mem_Icc {ι : Type*} [Fintype ι] [Nonempty ι] (g : ι → ℝ)
    (hg : ∀ i, g i ∈ Set.Icc (0 : ℝ) 1) :
    (𝔼 i, g i) ∈ Set.Icc (0 : ℝ) 1 := by
  refine Set.mem_Icc.mpr ⟨Finset.expect_nonneg fun i _ => (Set.mem_Icc.mp (hg i)).1, ?_⟩
  exact Finset.expect_le Finset.univ_nonempty fun i _ => (Set.mem_Icc.mp (hg i)).2

@[blueprint "lem:canonical-score-mem-Icc"
  (statement := /-- Let $A$ be a tester on $n$ and $m$. Then its canonical score of
  \cref{def:canonical-score} takes values in the unit interval:
  $\mathrm{score}_{A}(X) \in [0,1]$ for every sample sequence $X \in [n]^{m}$. -/)
  (proof := /-- By \cref{def:canonical-score}, \cref{def:label-avg} and \cref{def:order-avg}, the
  canonical score of $A$ at $X$ is the double average
  \[
    \mathrm{score}_{A}(X) \;=\; \frac{1}{n!}\sum_{\pi} \frac{1}{m!}\sum_{\sigma}
      \mathrm{Pr}_{r}\left[A\bigl((\pi \circ X) \circ \sigma; r\bigr) = \mathrm{accept}\right],
  \]
  where $\pi$ runs over the permutations of the domain $[n]$ and $\sigma$ over the permutations of
  the sample positions $[m]$; both index sets are nonempty finite sets, since the permutations of
  a finite type form a group and hence contain the identity.

  By \cref{lem:seed-accept-prob-mem-Icc}, for every sample sequence $Y \in [n]^{m}$ the seed
  acceptance probability satisfies $\mathrm{Pr}_{r}[A(Y;r) = \mathrm{accept}] \in [0,1]$. Fix
  $\pi$; applying \cref{lem:expect-mem-Icc-of-forall-mem-Icc} to the index set of permutations
  $\sigma$ of $[m]$ and to the function
  $\sigma \mapsto \mathrm{Pr}_{r}[A((\pi \circ X) \circ \sigma; r) = \mathrm{accept}]$ shows that
  the inner average lies in $[0,1]$. Applying
  \cref{lem:expect-mem-Icc-of-forall-mem-Icc} once more, now to the index set of permutations
  $\pi$ of $[n]$ and to the function sending $\pi$ to that inner average, shows that the outer
  average lies in $[0,1]$. This is exactly the assertion $\mathrm{score}_{A}(X) \in [0,1]$. -/)
  (title := /-- The canonical score is a valid threshold -/)
  (latexEnv := "lemma")]
lemma canonical_score_mem_Icc {n m : ℕ} (A : tester n m) (X : Fin m → Fin n) :
    canonical_score A X ∈ Set.Icc (0 : ℝ) 1 := by
  exact expect_mem_Icc_of_forall_mem_Icc _ fun _ =>
    expect_mem_Icc_of_forall_mem_Icc _ fun _ => seed_accept_prob_mem_Icc A _

@[blueprint "lem:order-avg-comp-perm"
  (statement := /-- Let $f : [n]^{m} \to \mathbb{R}$ be a deterministic function of the sample
  sequence, let $\sigma$ be a permutation of the sample positions $[m]$, and let
  $X \in [n]^{m}$. Then the order average of \cref{def:order-avg} is unchanged by reordering the
  samples: $(\mathrm{ordAvg}\, f)(X_{\sigma}) = (\mathrm{ordAvg}\, f)(X)$. -/)
  (proof := /-- Unfolding \cref{def:order-avg} at the sample sequence $X_{\sigma}$ gives
  \[
    (\mathrm{ordAvg}\, f)(X_{\sigma})
      = \frac{1}{m!}\sum_{\tau} f\bigl((X_{\sigma})_{\tau}\bigr)
      = \frac{1}{m!}\sum_{\tau} f\bigl(X_{\sigma\tau}\bigr),
  \]
  the two averages running over all permutations $\tau$ of $[m]$; the second equality holds
  pointwise, since composing the reindexing by $\sigma$ with the reindexing by $\tau$ is the
  reindexing by the composite permutation $\sigma\tau$. Left translation
  $\tau \mapsto \sigma\tau$ is a bijection of the group of permutations of $[m]$ onto itself,
  with inverse $\tau \mapsto \sigma^{-1}\tau$. An average over a finite index set is invariant
  under reindexing along a bijection of that index set, so reindexing the last average along
  this bijection yields
  $\frac{1}{m!}\sum_{\tau} f\bigl(X_{\tau}\bigr) = (\mathrm{ordAvg}\, f)(X)$, which is the
  claim. -/)
  (title := /-- The order average is invariant under reordering samples -/)
  (latexEnv := "lemma")]
lemma order_avg_comp_perm {n m : ℕ} (f : (Fin m → Fin n) → ℝ) (σ : Equiv.Perm (Fin m))
    (X : Fin m → Fin n) :
    order_avg f (X ∘ σ) = order_avg f X := by
  simp only [order_avg]
  exact Fintype.expect_equiv (Equiv.mulLeft σ) _ _ fun τ => rfl

@[blueprint "lem:canonical-score-order-invariant"
  (statement := /-- Let $A$ be a tester on $n$ and $m$, let $\sigma$ be a permutation of the
  sample positions $[m]$, and let $X \in [n]^{m}$. Then the canonical score of
  \cref{def:canonical-score} is unchanged by reordering the samples:
  $\mathrm{score}_{A}(X_{\sigma}) = \mathrm{score}_{A}(X)$. -/)
  (proof := /-- Write $g = \mathrm{Pr}_{r}[A(\cdot\,;r) = \mathrm{accept}]$ for the seed
  acceptance probability of \cref{def:seed-accept-prob}. By \cref{def:canonical-score} and
  \cref{def:label-avg},
  \[
    \mathrm{score}_{A}(X_{\sigma})
      = \frac{1}{n!}\sum_{\pi} (\mathrm{ordAvg}\, g)\bigl(\pi(X_{\sigma})\bigr),
    \qquad
    \mathrm{score}_{A}(X)
      = \frac{1}{n!}\sum_{\pi} (\mathrm{ordAvg}\, g)\bigl(\pi(X)\bigr),
  \]
  both averages running over the same index set of permutations $\pi$ of the domain $[n]$. It
  therefore suffices to prove that the two summands agree for each fixed $\pi$. Fix $\pi$.
  Relabelling values and reordering positions act on disjoint arguments, so they commute:
  $\pi(X_{\sigma}) = (\pi(X))_{\sigma}$, since both sides send the position $i \in [m]$ to
  $\pi\bigl(X_{\sigma(i)}\bigr)$. Applying \cref{lem:order-avg-comp-perm} to the function $g$,
  the permutation $\sigma$ and the sample sequence $\pi(X)$ gives
  $(\mathrm{ordAvg}\, g)\bigl((\pi(X))_{\sigma}\bigr)
    = (\mathrm{ordAvg}\, g)\bigl(\pi(X)\bigr)$.
  Hence the two summands indexed by $\pi$ coincide, and so do the two averages, which is the
  claim. -/)
  (title := /-- The canonical score is invariant under reordering samples -/)
  (latexEnv := "lemma")]
lemma canonical_score_order_invariant {n m : ℕ} (A : tester n m) (σ : Equiv.Perm (Fin m))
    (X : Fin m → Fin n) :
    canonical_score A (X ∘ σ) = canonical_score A X := by
  simp only [canonical_score, label_avg]
  exact Finset.expect_congr rfl fun π _ => order_avg_comp_perm _ σ (π ∘ X)

@[blueprint "lem:canonical-score-label-invariant"
  (statement := /-- Let $A$ be a tester on $n$ and $m$, let $\pi$ be a permutation of the domain
  $[n]$, and let $X \in [n]^{m}$. Then the canonical score of \cref{def:canonical-score} is
  unchanged by relabelling the samples:
  $\mathrm{score}_{A}(\pi(X)) = \mathrm{score}_{A}(X)$. -/)
  (proof := /-- By \cref{def:canonical-score}, the canonical score is the label average of the
  function $g = \mathrm{ordAvg}\bigl(\mathrm{Pr}_{r}[A(\cdot\,;r) = \mathrm{accept}]\bigr)$.
  From \cref{def:label-avg},
  \[
    (\mathrm{labAvg}\, g)(\pi(X))
      = \frac{1}{n!}\sum_{\varpi} g\bigl(\varpi(\pi(X))\bigr)
      = \frac{1}{n!}\sum_{\varpi} g\bigl((\varpi\pi)(X)\bigr),
  \]
  where $\varpi\pi$ denotes the composite permutation of $[n]$. As $\varpi$ ranges over all
  permutations of $[n]$, so does $\varpi\pi$, because right translation by $\pi$ is a bijection
  of the permutation group. Reindexing the average along this bijection gives
  $\frac{1}{n!}\sum_{\varpi} g(\varpi(X)) = (\mathrm{labAvg}\, g)(X)$, which is
  $\mathrm{score}_{A}(X)$. -/)
  (title := /-- The canonical score is invariant under relabelling samples -/)
  (latexEnv := "lemma")]
lemma canonical_score_label_invariant {n m : ℕ} (A : tester n m) (π : Equiv.Perm (Fin n))
    (X : Fin m → Fin n) :
    canonical_score A (π ∘ X) = canonical_score A X := by
  simp only [canonical_score, label_avg]
  exact Fintype.expect_equiv (Equiv.mulRight π) _ _ fun _ => rfl

@[blueprint "lem:canonical-tester-is-random-threshold"
  (statement := /-- Let $A$ be a tester on $n$ and $m$. Then its canonicalisation
  $A' = \mathrm{canon}(A)$ of \cref{def:canonical-tester} operates in the canonical random
  threshold format of \cref{def:is-random-threshold}: it compares a deterministic
  $[0,1]$-valued function of the sample sequence against a uniform random threshold. -/)
  (proof := /-- By \cref{def:canonical-tester}, $A'$ is by construction the random threshold
  algorithm of \cref{def:threshold-tester} associated with the deterministic function
  $\mathrm{score}_{A}$ of \cref{def:canonical-score}. By
  \cref{lem:canonical-score-mem-Icc}, that function takes values in $[0,1]$. Hence
  $\mathrm{score}_{A}$ witnesses the existential in \cref{def:is-random-threshold}. -/)
  (title := /-- The canonicalisation is a random threshold algorithm -/)
  (latexEnv := "lemma")]
lemma canonical_tester_is_random_threshold {n m : ℕ} (A : tester n m) :
    is_random_threshold (canonical_tester A) := by
  exact ⟨canonical_score A, canonical_score_mem_Icc A, rfl⟩

@[blueprint "lem:canonical-tester-order-invariant"
  (statement := /-- Let $A$ be a tester on $n$ and $m$. Then its canonicalisation
  $A' = \mathrm{canon}(A)$ of \cref{def:canonical-tester} is sample order invariant in the sense
  of \cref{def:order-invariant}: for every seed $r$, every permutation $\sigma$ of the sample
  positions $[m]$, and every sample sequence $X$, one has $A'(X;r) = A'(X_{\sigma};r)$. -/)
  (proof := /-- Fix $r$, $\sigma$ and $X$. By \cref{def:canonical-tester} and
  \cref{def:threshold-tester}, $A'(X;r) = \mathrm{accept}$ if and only if
  $r \le \mathrm{score}_{A}(X)$, and similarly $A'(X_{\sigma};r) = \mathrm{accept}$ if and only
  if $r \le \mathrm{score}_{A}(X_{\sigma})$. By
  \cref{lem:canonical-score-order-invariant} the two thresholds coincide, so the two
  comparisons have the same truth value and the two outputs agree. -/)
  (title := /-- The canonicalisation is sample order invariant -/)
  (latexEnv := "lemma")]
lemma canonical_tester_order_invariant {n m : ℕ} (A : tester n m) :
    order_invariant (canonical_tester A) := by
  intro r σ X
  simp only [canonical_tester, threshold_tester]
  rw [canonical_score_order_invariant]

@[blueprint "lem:canonical-tester-label-invariant"
  (statement := /-- Let $A$ be a tester on $n$ and $m$. Then its canonicalisation
  $A' = \mathrm{canon}(A)$ of \cref{def:canonical-tester} is sample label invariant in the sense
  of \cref{def:label-invariant}: for every seed $r$, every permutation $\pi$ of the domain
  $[n]$, and every sample sequence $X$, one has $A'(X;r) = A'(\pi(X);r)$. -/)
  (proof := /-- Fix $r$, $\pi$ and $X$. By \cref{def:canonical-tester} and
  \cref{def:threshold-tester}, $A'(X;r) = \mathrm{accept}$ if and only if
  $r \le \mathrm{score}_{A}(X)$, and $A'(\pi(X);r) = \mathrm{accept}$ if and only if
  $r \le \mathrm{score}_{A}(\pi(X))$. By \cref{lem:canonical-score-label-invariant} the two
  thresholds coincide, so the two comparisons have the same truth value and the two outputs
  agree. -/)
  (title := /-- The canonicalisation is sample label invariant -/)
  (latexEnv := "lemma")]
lemma canonical_tester_label_invariant {n m : ℕ} (A : tester n m) :
    label_invariant (canonical_tester A) := by
  intro r π X
  unfold canonical_tester threshold_tester
  rw [canonical_score_label_invariant]

@[blueprint "lem:canonical-tester-replicable"
  (statement := /-- Let $\rho \in \mathbb{R}$ and let $A$ be a measurable tester on $n$ and $m$
  in the sense of \cref{def:measurable-tester} which is $\rho$-replicable in the sense of
  \cref{def:replicable}. Then its canonicalisation $A' = \mathrm{canon}(A)$ of
  \cref{def:canonical-tester} is again $\rho$-replicable. -/)
  (proof := /-- By \cref{lem:score-replicable-of-replicable}, the measurability and
  $\rho$-replicability of $A$ imply that its seed acceptance probability
  $f(X) = \mathrm{Pr}_{r}[A(X;r) = \mathrm{accept}]$ is $\rho$-score replicable in the sense of
  \cref{def:score-replicable}. Applying \cref{lem:score-replicable-order-avg} to $f$ shows that
  $\mathrm{ordAvg}\, f$ is $\rho$-score replicable, and applying
  \cref{lem:score-replicable-label-avg} to $\mathrm{ordAvg}\, f$ shows that
  $\mathrm{labAvg}(\mathrm{ordAvg}\, f) = \mathrm{score}_{A}$ is $\rho$-score replicable, by
  \cref{def:canonical-score}. By \cref{lem:canonical-score-mem-Icc} the canonical score takes
  values in $[0,1]$, so \cref{lem:replicable-of-score-replicable} applies to it and yields that
  the random threshold algorithm associated with $\mathrm{score}_{A}$, which is $A'$ by
  \cref{def:canonical-tester}, is $\rho$-replicable. -/)
  (title := /-- The canonicalisation is $\rho$-replicable -/)
  (latexEnv := "lemma")]
lemma canonical_tester_replicable {n m : ℕ} (ρ : ℝ) (A : tester n m)
    (hA : measurable_tester A) (hrep : replicable ρ A) :
    replicable ρ (canonical_tester A) := by
  have h1 : score_replicable ρ (seed_accept_prob A) :=
    score_replicable_of_replicable ρ A hA hrep
  have h2 : score_replicable ρ (order_avg (seed_accept_prob A)) :=
    score_replicable_order_avg ρ _ h1
  have h3 : score_replicable ρ (canonical_score A) :=
    score_replicable_label_avg ρ _ h2
  exact replicable_of_score_replicable ρ (canonical_score A)
    (fun X => canonical_score_mem_Icc A X) h3

@[blueprint "lem:perm-disagree-sum-reindex"
  (statement := /-- Let $B$ be a tester on $n$ and $m$ which is sample label invariant in the
  sense of \cref{def:label-invariant}, let $p$ be a distribution on the domain $[n]$, and let
  $\pi$ be a permutation of $[n]$. Then the cross-permutation disagreement sum of $B$, in which
  the second sample sequence is weighted by the relabelled distribution $p^{\pi}$ of
  \cref{def:perm-pmf}, coincides with the plain disagreement sum in which both sample sequences
  are weighted by $p$:
  \[
    \sum_{X}\sum_{X'} p^{\otimes m}(X)\, (p^{\pi})^{\otimes m}(X')\,
      \mathrm{Pr}_{r}\left[B(X;r) \neq B(X';r)\right]
    = \sum_{X}\sum_{Y} p^{\otimes m}(X)\, p^{\otimes m}(Y)\,
      \mathrm{Pr}_{r}\left[B(X;r) \neq B(Y;r)\right],
  \]
  both sums running over all sample sequences in $[n]^{m}$, with the weights of
  \cref{def:sample-weight} and the seed probabilities of \cref{def:seed-measure}. -/)
  (proof := /-- Fix a sample sequence $X \in [n]^{m}$; it suffices to prove the identity of the
  two inner sums for this fixed $X$, since summing the resulting identities over all $X$ gives
  the claim. Because $\pi$ is a permutation of $[n]$, the map $Y \mapsto \pi(Y)$, where
  $\pi(Y) = (\pi(Y_1),\dots,\pi(Y_m))$, is a bijection of the finite set $[n]^{m}$ onto itself.
  Reindexing the sum over $X'$ along this bijection, it therefore suffices to show that for every
  $Y \in [n]^{m}$ the summand indexed by $Y$ on the right-hand side equals the summand indexed by
  $\pi(Y)$ on the left-hand side, that is,
  \[
    p^{\otimes m}(X)\, p^{\otimes m}(Y)\,
      \mathrm{Pr}_{r}\left[B(X;r) \neq B(Y;r)\right]
    = p^{\otimes m}(X)\, (p^{\pi})^{\otimes m}(\pi(Y))\,
      \mathrm{Pr}_{r}\left[B(X;r) \neq B(\pi(Y);r)\right].
  \]
  The weights agree: by \cref{lem:sample-weight-perm-pmf} we have
  $(p^{\pi})^{\otimes m}(\pi(Y)) = p^{\otimes m}(Y)$. The seed probabilities agree as well,
  because the two disagreement events coincide as subsets of $\mathbb{R}$: for every seed $r$,
  label invariance of $B$ in the sense of \cref{def:label-invariant}, applied to the seed $r$,
  the permutation $\pi$ and the sample sequence $Y$, gives $B(Y;r) = B(\pi(Y);r)$, so
  $B(X;r) \neq B(Y;r)$ holds if and only if $B(X;r) \neq B(\pi(Y);r)$ holds. Multiplying the two
  identities by the common factor $p^{\otimes m}(X)$ gives the displayed equality of
  summands. -/)
  (title := /-- Reindexing the cross-permutation disagreement sum -/)
  (latexEnv := "lemma")]
lemma perm_disagree_sum_reindex {n m : ℕ} (B : tester n m) (hB : label_invariant B)
    (p : PMF (Fin n)) (π : Equiv.Perm (Fin n)) :
    ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
        sample_weight p X * sample_weight (perm_pmf π p) X' *
          seed_measure.real {r : ℝ | B X r ≠ B X' r}
      = ∑ X : Fin m → Fin n, ∑ Y : Fin m → Fin n,
        sample_weight p X * sample_weight p Y *
          seed_measure.real {r : ℝ | B X r ≠ B Y r} := by
  refine Finset.sum_congr rfl fun X _ => ?_
  refine (Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin m)) π) _ _ fun Y => ?_).symm
  have hY : (Equiv.arrowCongr (Equiv.refl (Fin m)) π) Y = π ∘ Y := rfl
  have hset : {r : ℝ | B X r ≠ B Y r} = {r : ℝ | B X r ≠ B (π ∘ Y) r} := by
    ext r
    simp only [Set.mem_setOf_eq, hB r π Y]
  rw [hY, sample_weight_perm_pmf, hset]

@[blueprint "lem:disagree-sum-le-of-replicable"
  (statement := /-- Let $\rho \in \mathbb{R}$, let $B$ be a measurable tester on $n$ and $m$ in
  the sense of \cref{def:measurable-tester} which is $\rho$-replicable in the sense of
  \cref{def:replicable}, and let $p$ be a distribution on the domain $[n]$. Then the expected
  seed disagreement probability of $B$ on two independent sample sequences drawn from
  $p^{\otimes m}$ is at most $\rho$:
  \[
    \sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')\,
      \mathrm{Pr}_{r}\left[B(X;r) \neq B(X';r)\right] \;\le\; \rho ,
  \]
  the sums running over all sample sequences in $[n]^{m}$, with the weights of
  \cref{def:sample-weight}. -/)
  (proof := /-- Since $B$ is measurable, \cref{lem:seed-disagree-eq} gives, for every pair
  $(X, X')$ of sample sequences,
  $\mathrm{Pr}_{r}[B(X;r) = B(X';r)] = 1 - \mathrm{Pr}_{r}[B(X;r) \neq B(X';r)]$, hence
  $\mathrm{Pr}_{r}[B(X;r) \neq B(X';r)] = 1 - \mathrm{Pr}_{r}[B(X;r) = B(X';r)]$. Substituting
  this into each summand and expanding the product, the double sum to be bounded equals
  \[
    \sum_{X}\sum_{X'} \left(p^{\otimes m}(X)\, p^{\otimes m}(X')
      - p^{\otimes m}(X)\, p^{\otimes m}(X')\,
        \mathrm{Pr}_{r}\left[B(X;r) = B(X';r)\right]\right),
  \]
  and since all index sets are finite this splits as the difference
  \[
    \sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')
    \;-\; \sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')\,
      \mathrm{Pr}_{r}\left[B(X;r) = B(X';r)\right].
  \]
  For the first term, pulling the factor $p^{\otimes m}(X)$ out of the inner sum and applying
  \cref{lem:sample-weight-sum-one} twice, once to the inner sum over $X'$ and once to the
  resulting sum over $X$, gives $\sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X') = 1$. For
  the second term, the assumed $\rho$-replicability of $B$ applied to the distribution $p$ gives,
  by \cref{def:replicable},
  \[
    \sum_{X}\sum_{X'} p^{\otimes m}(X)\, p^{\otimes m}(X')\,
      \mathrm{Pr}_{r}\left[B(X;r) = B(X';r)\right] \;\ge\; 1 - \rho .
  \]
  Therefore the double sum is at most $1 - (1 - \rho) = \rho$, as claimed. -/)
  (title := /-- Replicability bounds the expected seed disagreement -/)
  (latexEnv := "lemma")]
lemma disagree_sum_le_of_replicable {n m : ℕ} (ρ : ℝ) (B : tester n m)
    (hB : measurable_tester B) (hrep : replicable ρ B) (p : PMF (Fin n)) :
    ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
        sample_weight p X * sample_weight p X' *
          seed_measure.real {r : ℝ | B X r ≠ B X' r} ≤ ρ := by
  have hone : ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
      sample_weight p X * sample_weight p X' = 1 := by
    have hsum := sample_weight_sum_one p m
    calc ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
          sample_weight p X * sample_weight p X'
        = ∑ X : Fin m → Fin n, sample_weight p X *
            ∑ X' : Fin m → Fin n, sample_weight p X' := by
          simp [Finset.mul_sum]
      _ = 1 := by simp [hsum]
  have hsplit : ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
        sample_weight p X * sample_weight p X' *
          seed_measure.real {r : ℝ | B X r ≠ B X' r}
      = (∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
          sample_weight p X * sample_weight p X')
        - ∑ X : Fin m → Fin n, ∑ X' : Fin m → Fin n,
          sample_weight p X * sample_weight p X' *
            seed_measure.real {r : ℝ | B X r = B X' r} := by
    simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun X _ => Finset.sum_congr rfl fun X' _ => ?_
    have hd := seed_disagree_eq B hB X X'
    have hd' : seed_measure.real {r : ℝ | B X r ≠ B X' r}
        = 1 - seed_measure.real {r : ℝ | B X r = B X' r} := by linarith
    rw [hd']
    ring
  rw [hsplit, hone]
  have hagree := hrep p
  linarith

@[blueprint "lem:canonical-tester-perm-robust"
  (statement := /-- Let $\rho \in \mathbb{R}$ and let $A$ be a measurable tester on $n$ and $m$
  in the sense of \cref{def:measurable-tester} which is $\rho$-replicable in the sense of
  \cref{def:replicable}. Then its canonicalisation $A' = \mathrm{canon}(A)$ of
  \cref{def:canonical-tester} satisfies $\rho$-permutation robust replicability in the sense of
  \cref{def:perm-robust-replicable}: for every distribution $p$ on $[n]$ and every permutation
  $\pi$ of $[n]$,
  \[
    \mathrm{Pr}_{r,\, X \sim p^{\otimes m},\, X' \sim (p^{\pi})^{\otimes m}}
      \left[A'(X;r) \neq A'(X';r)\right] \;\le\; \rho .
  \]
  This is Lemma~\ref{lem:perm_robust} of the source. -/)
  (proof := /-- By \cref{def:perm-robust-replicable} it suffices to fix a distribution $p$ on
  $[n]$ and a permutation $\pi$ of $[n]$ and to bound the double sum
  \[
    \sum_{X}\sum_{X'} p^{\otimes m}(X)\, (p^{\pi})^{\otimes m}(X')\,
      \mathrm{Pr}_{r}\left[A'(X;r) \neq A'(X';r)\right]
  \]
  by $\rho$, where $A' = \mathrm{canon}(A)$.

  We first record that $A'$ is a measurable tester in the sense of
  \cref{def:measurable-tester}. By \cref{lem:canonical-tester-is-random-threshold} there is a
  function $f : [n]^{m} \to \mathbb{R}$ such that $A'$ is the random threshold algorithm
  associated with $f$ in the sense of \cref{def:threshold-tester}, and by
  \cref{lem:threshold-tester-measurable} every such algorithm is measurable; rewriting $A'$ as
  that algorithm gives the measurability of $A'$.

  Next we remove the relabelling from the second sample sequence. By
  \cref{lem:canonical-tester-label-invariant}, $A'$ is sample label invariant in the sense of
  \cref{def:label-invariant}, so \cref{lem:perm-disagree-sum-reindex}, applied to the tester
  $A'$, the distribution $p$ and the permutation $\pi$, shows that the displayed double sum
  equals
  \[
    \sum_{X}\sum_{Y} p^{\otimes m}(X)\, p^{\otimes m}(Y)\,
      \mathrm{Pr}_{r}\left[A'(X;r) \neq A'(Y;r)\right],
  \]
  in which both sample sequences are weighted by $p^{\otimes m}$.

  Finally, by \cref{lem:canonical-tester-replicable}, the measurability and
  $\rho$-replicability of $A$ imply that $A'$ is $\rho$-replicable in the sense of
  \cref{def:replicable}. Since $A'$ is also measurable, as shown above,
  \cref{lem:disagree-sum-le-of-replicable}, applied to $A'$ and the distribution $p$, bounds this
  last double sum by $\rho$. This is the required bound. -/)
  (title := /-- The canonicalisation is permutation robust replicable -/)
  (latexEnv := "lemma")]
lemma canonical_tester_perm_robust {n m : ℕ} (ρ : ℝ) (A : tester n m)
    (hA : measurable_tester A) (hrep : replicable ρ A) :
    perm_robust_replicable ρ (canonical_tester A) := by
  intro p π
  have hmeas : measurable_tester (canonical_tester A) := by
    obtain ⟨f, -, hf⟩ := canonical_tester_is_random_threshold A
    rw [hf]
    exact threshold_tester_measurable f
  rw [perm_disagree_sum_reindex (canonical_tester A)
    (canonical_tester_label_invariant A) p π]
  exact disagree_sum_le_of_replicable ρ (canonical_tester A) hmeas
    (canonical_tester_replicable ρ A hA hrep) p

@[blueprint "lem:perm-pmf-apply-symm"
  (statement := /-- Let $r$ be a distribution on the domain $[n]$, let $\pi$ be a permutation of
  $[n]$, and let $j \in [n]$. Then the relabelled distribution $r^{\pi}$ of \cref{def:perm-pmf}
  satisfies
  \[
    r^{\pi}(j) \;=\; r\left(\pi^{-1}(j)\right).
  \]
  Equivalently, $r^{\pi}(\pi(k)) = r(k)$ for every $k \in [n]$. -/)
  (proof := /-- By \cref{def:perm-pmf}, the relabelled distribution $r^{\pi}$ is the push-forward
  of $r$ along $\pi$, whose mass at $j$ is by definition the sum
  $\sum_{a \in [n]} \left[\, j = \pi(a) \,\right] r(a)$ of the masses of all preimages of $j$.
  Since $\pi$ is a bijection, the condition $j = \pi(a)$ holds precisely for the single index
  $a = \pi^{-1}(j)$, so every other summand vanishes and the sum collapses to
  $r\left(\pi^{-1}(j)\right)$. -/)
  (title := /-- Value of a relabelled distribution -/)
  (latexEnv := "lemma")]
lemma perm_pmf_apply_symm {n : ℕ} (π : Equiv.Perm (Fin n)) (r : PMF (Fin n)) (j : Fin n) :
    perm_pmf π r j = r (π.symm j) := by
  simp [perm_pmf, PMF.map_apply, ← Equiv.symm_apply_eq, tsum_ite_eq]

@[blueprint "lem:tv-dist-perm-invariant"
  (statement := /-- Let $p$ and $q$ be distributions on the domain $[n]$ and let $\pi$ be a
  permutation of $[n]$. Then the total variation distance of \cref{def:tv-dist} is invariant
  under simultaneous relabelling:
  \[
    d_{\mathrm{TV}}\left(p^{\pi},\, q^{\pi}\right) \;=\; d_{\mathrm{TV}}(p, q),
  \]
  with $p^{\pi}$ and $q^{\pi}$ as in \cref{def:perm-pmf}. -/)
  (proof := /-- By \cref{def:tv-dist}, the left-hand side is
  $\frac{1}{2}\sum_{j \in [n]}\left|p^{\pi}(j) - q^{\pi}(j)\right|$ and the right-hand side is
  $\frac{1}{2}\sum_{k \in [n]}\left|p(k) - q(k)\right|$, so it suffices to prove that the two
  sums agree. Reindex the sum on the left along the bijection $\pi^{-1}$ of $[n]$: this is a
  permutation of the index set, so it leaves the value of the finite sum unchanged, and it
  matches the summand at index $j \in [n]$ on the left with the summand at index
  $\pi^{-1}(j)$ on the right. It therefore remains to check, for each $j \in [n]$, that
  \[
    \left|p^{\pi}(j) - q^{\pi}(j)\right|
      \;=\; \left|p\left(\pi^{-1}(j)\right) - q\left(\pi^{-1}(j)\right)\right| .
  \]
  By \cref{lem:perm-pmf-apply-symm}, applied to $p$ and to $q$ at the point $j$, we have
  $p^{\pi}(j) = p\left(\pi^{-1}(j)\right)$ and $q^{\pi}(j) = q\left(\pi^{-1}(j)\right)$, so the
  two sides are literally the same expression. Hence the sums are equal and
  $d_{\mathrm{TV}}(p^{\pi}, q^{\pi}) = d_{\mathrm{TV}}(p, q)$. -/)
  (title := /-- Total variation distance is invariant under relabelling -/)
  (latexEnv := "lemma")]
lemma tv_dist_perm_invariant {n : ℕ} (p q : PMF (Fin n)) (π : Equiv.Perm (Fin n)) :
    tv_dist (perm_pmf π p) (perm_pmf π q) = tv_dist p q := by
  unfold tv_dist
  congr 1
  refine Fintype.sum_equiv π.symm _ _ fun k => ?_
  rw [perm_pmf_apply_symm π p k, perm_pmf_apply_symm π q k]

@[blueprint "lem:perm-pmf-mem-of-symmetric"
  (statement := /-- Let $\mathcal{P}$ be a symmetric property of distributions on $[n]$ in the
  sense of \cref{def:symmetric-property}, let $p \in \mathcal{P}$, and let $\pi$ be a
  permutation of $[n]$. Then the relabelled distribution $p^{\pi}$ of \cref{def:perm-pmf} also
  lies in $\mathcal{P}$. -/)
  (proof := /-- This is precisely the defining condition of a symmetric property in
  \cref{def:symmetric-property}, instantiated at the member $p$ of $\mathcal{P}$ and at the
  permutation $\pi$ of $[n]$. -/)
  (title := /-- Symmetric properties are closed under relabelling -/)
  (latexEnv := "lemma")]
lemma perm_pmf_mem_of_symmetric {n : ℕ} (P : Set (PMF (Fin n))) (hP : symmetric_property P)
    (p : PMF (Fin n)) (hp : p ∈ P) (π : Equiv.Perm (Fin n)) :
    perm_pmf π p ∈ P := by
  exact hP p hp π

@[blueprint "lem:perm-pmf-symm-cancel"
  (statement := /-- Let $q$ be a distribution on $[n]$ and let $\pi$ be a permutation of $[n]$.
  Then relabelling $q$ first by $\pi^{-1}$ and then by $\pi$ recovers $q$, that is,
  $\left(q^{\pi^{-1}}\right)^{\pi} = q$, with relabelling as in \cref{def:perm-pmf}. -/)
  (proof := /-- By \cref{def:perm-pmf} the relabelling $q^{\sigma}$ is the push-forward of $q$
  along the permutation $\sigma$, so $\left(q^{\pi^{-1}}\right)^{\pi}$ is the push-forward of $q$
  along $\pi^{-1}$ followed by the push-forward along $\pi$. Functoriality of the push-forward
  identifies this iterated push-forward with the push-forward of $q$ along the composite map
  $\pi \circ \pi^{-1}$. Since $\pi \circ \pi^{-1}$ is the identity map of $[n]$ and the
  push-forward along the identity map leaves every distribution unchanged, we conclude
  $\left(q^{\pi^{-1}}\right)^{\pi} = q$. -/)
  (title := /-- Relabelling by a permutation and by its inverse cancel -/)
  (latexEnv := "lemma")]
lemma perm_pmf_symm_cancel {n : ℕ} (q : PMF (Fin n)) (π : Equiv.Perm (Fin n)) :
    perm_pmf π (perm_pmf π⁻¹ q) = q := by
  simp [perm_pmf, PMF.map_comp, PMF.map_id]

@[blueprint "lem:perm-pmf-far"
  (statement := /-- Let $\mathcal{P}$ be a symmetric property of distributions on $[n]$ in the
  sense of \cref{def:symmetric-property}, let $\varepsilon \in \mathbb{R}$, let $p$ be a
  distribution on $[n]$ that is $\varepsilon$-far from $\mathcal{P}$ in the sense of
  \cref{def:far-from}, and let $\pi$ be a permutation of $[n]$. Then the relabelled distribution
  $p^{\pi}$ of \cref{def:perm-pmf} is also $\varepsilon$-far from $\mathcal{P}$. -/)
  (proof := /-- Let $q \in \mathcal{P}$; we must show $d_{\mathrm{TV}}(p^{\pi}, q) \ge
  \varepsilon$. Since $\pi^{-1}$ is a permutation of $[n]$ and $\mathcal{P}$ is symmetric, the
  relabelled distribution $q^{\pi^{-1}}$ lies in $\mathcal{P}$ by
  \cref{lem:perm-pmf-mem-of-symmetric}. As $p$ is $\varepsilon$-far from $\mathcal{P}$, applying
  \cref{def:far-from} to this member gives
  $d_{\mathrm{TV}}\left(p,\, q^{\pi^{-1}}\right) \ge \varepsilon$. By
  \cref{lem:tv-dist-perm-invariant}, relabelling both arguments by $\pi$ preserves the total
  variation distance, so
  \[
    d_{\mathrm{TV}}\left(p^{\pi},\, \left(q^{\pi^{-1}}\right)^{\pi}\right)
      \;=\; d_{\mathrm{TV}}\left(p,\, q^{\pi^{-1}}\right) \;\ge\; \varepsilon .
  \]
  Finally $\left(q^{\pi^{-1}}\right)^{\pi} = q$ by \cref{lem:perm-pmf-symm-cancel}. Hence
  $d_{\mathrm{TV}}(p^{\pi}, q) \ge \varepsilon$, as required. -/)
  (title := /-- Farness is preserved by relabelling -/)
  (latexEnv := "lemma")]
lemma perm_pmf_far {n : ℕ} (ε : ℝ) (P : Set (PMF (Fin n))) (hP : symmetric_property P)
    (p : PMF (Fin n)) (hp : far_from ε P p) (π : Equiv.Perm (Fin n)) :
    far_from ε P (perm_pmf π p) := by
  intro q hq
  have hq' : perm_pmf π⁻¹ q ∈ P := perm_pmf_mem_of_symmetric P hP q hq π⁻¹
  calc ε ≤ tv_dist p (perm_pmf π⁻¹ q) := hp _ hq'
    _ = tv_dist (perm_pmf π p) (perm_pmf π (perm_pmf π⁻¹ q)) :=
        (tv_dist_perm_invariant p (perm_pmf π⁻¹ q) π).symm
    _ = tv_dist (perm_pmf π p) q := by rw [perm_pmf_symm_cancel]

@[blueprint "lem:sum-sample-weight-order-avg"
  (statement := /-- Let $p$ be a distribution on $[n]$ and let $g : [n]^{m} \to \mathbb{R}$ be a
  function of the sample sequence. Then replacing $g$ by its order average of
  \cref{def:order-avg} does not change its expectation against the product weight of
  \cref{def:sample-weight}:
  \[
    \sum_{X \in [n]^{m}} p^{\otimes m}(X)\, (\mathrm{ordAvg}\, g)(X)
      \;=\; \sum_{X \in [n]^{m}} p^{\otimes m}(X)\, g(X).
  \] -/)
  (proof := /-- Fix a permutation $\sigma$ of the sample positions $[m]$ and write
  $X_{\sigma} = (X_{\sigma(1)},\dots,X_{\sigma(m)})$. The map $X \mapsto X_{\sigma}$ is a
  bijection of $[n]^{m}$ onto itself: it is injective because $X_{\sigma} = Y_{\sigma}$ evaluated
  at $\sigma^{-1}(i)$ gives $X_i = Y_i$ for every index $i$, and it is surjective because
  $Y_{\sigma^{-1}}$ is mapped to $Y$. Reindexing the finite sum
  $\sum_{X} p^{\otimes m}(X)\, g(X)$ along this bijection and using
  \cref{lem:sample-weight-order-invariant}, which gives
  $p^{\otimes m}(X_{\sigma}) = p^{\otimes m}(X)$ for every $X$, yields
  \[
    \sum_{X} p^{\otimes m}(X)\, g(X_{\sigma}) \;=\; \sum_{X} p^{\otimes m}(X)\, g(X)
    \tag{$\ast$}
  \]
  for every $\sigma$.

  Now unfold \cref{def:order-avg}. For each fixed $X$ the scalar $p^{\otimes m}(X)$ may be moved
  inside the finite average over $\sigma$, so
  $p^{\otimes m}(X)\, (\mathrm{ordAvg}\, g)(X)
    = \frac{1}{m!}\sum_{\sigma} p^{\otimes m}(X)\, g(X_{\sigma})$. Summing over the finitely many
  sample sequences $X$ and exchanging the sum over $X$ with the average over $\sigma$ gives
  \[
    \sum_{X} p^{\otimes m}(X)\, (\mathrm{ordAvg}\, g)(X)
      \;=\; \frac{1}{m!}\sum_{\sigma} \sum_{X} p^{\otimes m}(X)\, g(X_{\sigma}).
  \]
  By $(\ast)$ every term of this average over $\sigma$ equals
  $\sum_{X} p^{\otimes m}(X)\, g(X)$, and the average of a constant over the nonempty finite set
  of permutations of $[m]$ is that constant. This is the claim. -/)
  (title := /-- Order averaging is invisible to the product weight -/)
  (latexEnv := "lemma")]
lemma sum_sample_weight_order_avg {n m : ℕ} (p : PMF (Fin n)) (g : (Fin m → Fin n) → ℝ) :
    ∑ X : Fin m → Fin n, sample_weight p X * order_avg g X =
      ∑ X : Fin m → Fin n, sample_weight p X * g X := by
  have key : ∀ σ : Equiv.Perm (Fin m),
      ∑ X : Fin m → Fin n, sample_weight p X * g (X ∘ σ) =
        ∑ X : Fin m → Fin n, sample_weight p X * g X := by
    intro σ
    have hbij : Function.Bijective (fun X : Fin m → Fin n => X ∘ σ) := by
      constructor
      · intro X Y hXY
        funext i
        have h := congrFun hXY (σ.symm i)
        simpa using h
      · intro Y
        refine ⟨Y ∘ σ.symm, ?_⟩
        funext i
        simp
    refine Fintype.sum_bijective _ hbij _ _ ?_
    intro X
    rw [sample_weight_order_invariant]
  have hstep : ∀ X : Fin m → Fin n,
      sample_weight p X * order_avg g X =
        𝔼 σ : Equiv.Perm (Fin m), sample_weight p X * g (X ∘ σ) := by
    intro X
    simp only [order_avg]
    exact Finset.mul_expect _ _ _
  calc ∑ X : Fin m → Fin n, sample_weight p X * order_avg g X
      = ∑ X : Fin m → Fin n, 𝔼 σ : Equiv.Perm (Fin m), sample_weight p X * g (X ∘ σ) :=
        Finset.sum_congr rfl fun X _ => hstep X
    _ = 𝔼 σ : Equiv.Perm (Fin m), ∑ X : Fin m → Fin n, sample_weight p X * g (X ∘ σ) :=
        (Finset.expect_sum_comm _ _ _).symm
    _ = 𝔼 _σ : Equiv.Perm (Fin m), ∑ X : Fin m → Fin n, sample_weight p X * g X :=
        Finset.expect_congr rfl fun σ _ => key σ
    _ = ∑ X : Fin m → Fin n, sample_weight p X * g X :=
        Finset.expect_const Finset.univ_nonempty _

@[blueprint "lem:sum-sample-weight-comp-perm"
  (statement := /-- Let $p$ be a distribution on $[n]$, let $\pi$ be a permutation of $[n]$, and
  let $g : [n]^{m} \to \mathbb{R}$ be a function of the sample sequence. Then relabelling the
  argument of $g$ by $\pi$ is the same as relabelling the distribution:
  \[
    \sum_{X \in [n]^{m}} p^{\otimes m}(X)\, g(\pi(X))
      \;=\; \sum_{X \in [n]^{m}} (p^{\pi})^{\otimes m}(X)\, g(X),
  \]
  where $\pi(X) = (\pi(X_1),\dots,\pi(X_m))$, the weights are those of \cref{def:sample-weight},
  and $p^{\pi}$ is the relabelled distribution of \cref{def:perm-pmf}. -/)
  (proof := /-- The map $X \mapsto \pi(X)$ is a bijection of $[n]^{m}$ onto itself: it is
  injective because $\pi(X) = \pi(Y)$ gives $\pi(X_i) = \pi(Y_i)$ and hence $X_i = Y_i$ for every
  index $i$, by injectivity of the permutation $\pi$, and it is surjective because
  $\pi^{-1}(Y)$ is mapped to $Y$. Reindexing the finite sum
  $\sum_{X} (p^{\pi})^{\otimes m}(X)\, g(X)$ along this bijection turns it into
  $\sum_{X} (p^{\pi})^{\otimes m}(\pi(X))\, g(\pi(X))$, and by
  \cref{lem:sample-weight-perm-pmf} we have $(p^{\pi})^{\otimes m}(\pi(X)) = p^{\otimes m}(X)$
  for every sample sequence $X$. Substituting this identity termwise gives
  $\sum_{X} p^{\otimes m}(X)\, g(\pi(X))$, which is the claim. -/)
  (title := /-- Relabelling the samples is relabelling the distribution -/)
  (latexEnv := "lemma")]
lemma sum_sample_weight_comp_perm {n m : ℕ} (p : PMF (Fin n)) (π : Equiv.Perm (Fin n))
    (g : (Fin m → Fin n) → ℝ) :
    ∑ X : Fin m → Fin n, sample_weight p X * g (π ∘ X) =
      ∑ X : Fin m → Fin n, sample_weight (perm_pmf π p) X * g X := by
  have hbij : Function.Bijective (fun X : Fin m → Fin n => (π : Fin n → Fin n) ∘ X) := by
    constructor
    · intro X Y hXY
      funext i
      exact π.injective (congrFun hXY i)
    · intro Y
      refine ⟨(π.symm : Fin n → Fin n) ∘ Y, ?_⟩
      funext i
      simp
  refine Fintype.sum_bijective _ hbij _ _ ?_
  intro X
  rw [sample_weight_perm_pmf]

@[blueprint "lem:accept-prob-canonical-eq-avg"
  (statement := /-- Let $A$ be a measurable tester on $n$ and $m$ in the sense of
  \cref{def:measurable-tester} and let $p$ be a distribution on $[n]$. Then the acceptance
  probability of the canonicalisation $A' = \mathrm{canon}(A)$ of \cref{def:canonical-tester}
  under $p$ is the average, over all permutations $\pi$ of the domain $[n]$, of the acceptance
  probabilities of the original tester $A$ under the relabelled distributions $p^{\pi}$:
  \[
    \mathrm{Pr}_{X \sim p^{\otimes m},\, r}\left[A'(X;r) = \mathrm{accept}\right]
      \;=\; \frac{1}{n!}\sum_{\pi}
        \mathrm{Pr}_{X \sim (p^{\pi})^{\otimes m},\, r}\left[A(X;r) = \mathrm{accept}\right].
  \]
  This identity is the whole content of the accuracy analysis: it is the chain of displays in
  Lemmas~\ref{lem:canonical}, \ref{lem:order_invariant}, and \ref{lem:label_invariant} of the source,
  culminating in the statement that the acceptance probability of $A_3$ under $p$ is the average
  acceptance probability of $A_0$ over all relabellings of $p$. -/)
  (proof := /-- Write $f(X) = \mathrm{Pr}_{r}[A(X;r) = \mathrm{accept}]$ for the seed acceptance
  probability of \cref{def:seed-accept-prob}. By
  \cref{lem:canonical-score-mem-Icc} the canonical score takes values in $[0,1]$, so
  \cref{lem:seed-accept-prob-threshold} applies to it and gives, for every sample sequence $X$,
  \[
    \mathrm{Pr}_{r}\left[A'(X;r) = \mathrm{accept}\right] \;=\; \mathrm{score}_{A}(X),
  \]
  using \cref{def:canonical-tester}. Substituting into \cref{def:accept-prob} and unfolding
  \cref{def:canonical-score} and \cref{def:label-avg},
  \[
    \mathrm{Pr}_{X \sim p^{\otimes m},\, r}\left[A'(X;r) = \mathrm{accept}\right]
      = \sum_{X} p^{\otimes m}(X)\, \mathrm{score}_{A}(X)
      = \sum_{X} p^{\otimes m}(X)\, \frac{1}{n!}\sum_{\pi}
        (\mathrm{ordAvg}\, f)(\pi(X)),
  \]
  with $\mathrm{ordAvg}$ the order average of \cref{def:order-avg}.

  For each fixed sample sequence $X$ the scalar $p^{\otimes m}(X)$ may be moved inside the finite
  average over the permutations $\pi$ of $[n]$, and the finite sum over the sample sequences $X$
  may then be exchanged with that finite average, giving
  \[
    \mathrm{Pr}_{X \sim p^{\otimes m},\, r}\left[A'(X;r) = \mathrm{accept}\right]
      = \frac{1}{n!}\sum_{\pi} \sum_{X} p^{\otimes m}(X)\,
        (\mathrm{ordAvg}\, f)(\pi(X)).
  \]
  Fix a permutation $\pi$ of $[n]$ and consider the inner sum. Applying
  \cref{lem:sum-sample-weight-comp-perm} to the function $\mathrm{ordAvg}\, f$ replaces the
  relabelling of the samples by a relabelling of the distribution,
  \[
    \sum_{X} p^{\otimes m}(X)\, (\mathrm{ordAvg}\, f)(\pi(X))
      \;=\; \sum_{X} (p^{\pi})^{\otimes m}(X)\, (\mathrm{ordAvg}\, f)(X),
  \]
  and then \cref{lem:sum-sample-weight-order-avg}, applied to the distribution $p^{\pi}$ and the
  function $f$, removes the order average,
  \[
    \sum_{X} (p^{\pi})^{\otimes m}(X)\, (\mathrm{ordAvg}\, f)(X)
      \;=\; \sum_{X} (p^{\pi})^{\otimes m}(X)\, f(X)
      \;=\; \mathrm{Pr}_{X \sim (p^{\pi})^{\otimes m},\, r}
        \left[A(X;r) = \mathrm{accept}\right],
  \]
  the last equality being \cref{def:accept-prob} unfolded. Since this holds for every $\pi$,
  averaging over the permutations $\pi$ of $[n]$ gives the claim. -/)
  (title := /-- Acceptance probability of the canonicalisation -/)
  (latexEnv := "lemma")]
lemma accept_prob_canonical_eq_avg {n m : ℕ} (A : tester n m) (hA : measurable_tester A)
    (p : PMF (Fin n)) :
    accept_prob p (canonical_tester A) =
      𝔼 π : Equiv.Perm (Fin n), accept_prob (perm_pmf π p) A := by
  have hscore : ∀ X : Fin m → Fin n,
      seed_accept_prob (canonical_tester A) X = canonical_score A X := fun X =>
    seed_accept_prob_threshold (canonical_score A) (canonical_score_mem_Icc A) X
  have hinner : ∀ π : Equiv.Perm (Fin n),
      ∑ X : Fin m → Fin n,
          sample_weight p X *
            order_avg (seed_accept_prob A) ((π : Fin n → Fin n) ∘ X) =
        accept_prob (perm_pmf π p) A := by
    intro π
    rw [sum_sample_weight_comp_perm p π (order_avg (seed_accept_prob A)),
      sum_sample_weight_order_avg]
    rfl
  calc accept_prob p (canonical_tester A)
      = ∑ X : Fin m → Fin n, sample_weight p X * canonical_score A X := by
        simp only [accept_prob, hscore]
    _ = ∑ X : Fin m → Fin n, 𝔼 π : Equiv.Perm (Fin n),
          sample_weight p X *
            order_avg (seed_accept_prob A) ((π : Fin n → Fin n) ∘ X) := by
        refine Finset.sum_congr rfl fun X _ => ?_
        simp only [canonical_score, label_avg]
        exact Finset.mul_expect _ _ _
    _ = 𝔼 π : Equiv.Perm (Fin n), ∑ X : Fin m → Fin n,
          sample_weight p X *
            order_avg (seed_accept_prob A) ((π : Fin n → Fin n) ∘ X) :=
        (Finset.expect_sum_comm _ _ _).symm
    _ = 𝔼 π : Equiv.Perm (Fin n), accept_prob (perm_pmf π p) A :=
        Finset.expect_congr rfl fun π _ => hinner π

@[blueprint "lem:canonical-tester-accurate"
  (statement := /-- Let $\varepsilon, \delta \in \mathbb{R}$, let $\mathcal{P}$ be a symmetric
  property of distributions on $[n]$ in the sense of \cref{def:symmetric-property}, and let $A$
  be a measurable tester on $n$ and $m$ in the sense of \cref{def:measurable-tester} which is
  $(\varepsilon,\delta)$-accurate for $\mathcal{P}$ in the sense of
  \cref{def:accurate-tester}. Then its canonicalisation $A' = \mathrm{canon}(A)$ of
  \cref{def:canonical-tester} is again $(\varepsilon,\delta)$-accurate for $\mathcal{P}$, using
  the same number $m$ of samples. -/)
  (proof := /-- By \cref{lem:accept-prob-canonical-eq-avg}, for every distribution $p$ on $[n]$
  the acceptance probability of $A'$ under $p$ equals the average over all permutations $\pi$ of
  $[n]$ of the acceptance probability of $A$ under $p^{\pi}$. We verify the two clauses of
  \cref{def:accurate-tester} separately.

  Suppose first $p \in \mathcal{P}$. For every permutation $\pi$ of $[n]$, the relabelled
  distribution $p^{\pi}$ lies in $\mathcal{P}$ by
  \cref{lem:perm-pmf-mem-of-symmetric}, since $\mathcal{P}$ is symmetric. Hence the first clause
  of the accuracy of $A$ gives
  $\mathrm{Pr}_{X \sim (p^{\pi})^{\otimes m}, r}[A(X;r) = \mathrm{accept}] \ge 1 - \delta$ for
  every $\pi$. An average over the nonempty finite index set of permutations of $[n]$ of
  quantities each at least $1 - \delta$ is itself at least $1 - \delta$, so the averaged
  expression, which equals $\mathrm{Pr}_{X \sim p^{\otimes m}, r}[A'(X;r) = \mathrm{accept}]$, is
  at least $1 - \delta$.

  Suppose next that $p$ is $\varepsilon$-far from $\mathcal{P}$ in the sense of
  \cref{def:far-from}. For every permutation $\pi$ of $[n]$, the relabelled distribution
  $p^{\pi}$ is again $\varepsilon$-far from $\mathcal{P}$ by \cref{lem:perm-pmf-far}. Hence the
  second clause of the accuracy of $A$ gives
  $\mathrm{Pr}_{X \sim (p^{\pi})^{\otimes m}, r}[A(X;r) = \mathrm{accept}] \le \delta$ for every
  $\pi$. An average over a nonempty finite index set of quantities each at most $\delta$ is at
  most $\delta$, so $\mathrm{Pr}_{X \sim p^{\otimes m}, r}[A'(X;r) = \mathrm{accept}] \le \delta$.

  Both clauses of \cref{def:accurate-tester} hold for $A'$, which is the claim. -/)
  (title := /-- The canonicalisation retains the accuracy of the original tester -/)
  (latexEnv := "lemma")]
lemma canonical_tester_accurate {n m : ℕ} (ε δ : ℝ) (P : Set (PMF (Fin n)))
    (hP : symmetric_property P) (A : tester n m) (hA : measurable_tester A)
    (hacc : accurate_tester ε δ P A) :
    accurate_tester ε δ P (canonical_tester A) := by
  refine ⟨fun p hp => ?_, fun p hpfar => ?_⟩
  · rw [accept_prob_canonical_eq_avg A hA p]
    exact Finset.le_expect Finset.univ_nonempty fun π _ =>
      hacc.1 _ (perm_pmf_mem_of_symmetric P hP p hp π)
  · rw [accept_prob_canonical_eq_avg A hA p]
    exact Finset.expect_le Finset.univ_nonempty fun π _ =>
      hacc.2 _ (perm_pmf_far ε P hP p hpfar π)

@[blueprint "thm:main-canonical"
  (statement := /-- \emph{(Canonical properties of replicable testers.)} Let $n$ and $m$ be
  natural numbers, let $\rho, \varepsilon, \delta \in \mathbb{R}$, let $\mathcal{P}$ be a
  symmetric property of distributions on the domain $[n]$ in the sense of
  \cref{def:symmetric-property}, and let $A$ be a tester on $n$ and $m$
  (\cref{def:tester}) that is measurable (\cref{def:measurable-tester}) and satisfies:
  \begin{itemize}
    \item $A$ is $\rho$-replicable in the sense of \cref{def:replicable};
    \item $A$ is $(\varepsilon,\delta)$-accurate for $\mathcal{P}$ in the sense of
      \cref{def:accurate-tester}; that is, if $p \in \mathcal{P}$ then
      $\mathrm{Pr}_{X \sim p^{\otimes m}, r}[A(X;r) = \mathrm{accept}] \ge 1 - \delta$, and if
      $p$ is $\varepsilon$-far from $\mathcal{P}$ then
      $\mathrm{Pr}_{X \sim p^{\otimes m}, r}[A(X;r) = \mathrm{accept}] \le \delta$.
  \end{itemize}
  Then there exists a tester $A'$ on the same domain size $n$ and the same sample size $m$ which
  achieves the same accuracy, namely $A'$ is $(\varepsilon,\delta)$-accurate for $\mathcal{P}$,
  and which has the following canonical properties:
  \begin{itemize}
    \item $A'$ operates in the canonical format of comparing a deterministic $[0,1]$-valued
      function of the samples to a uniform random threshold (\cref{def:is-random-threshold});
    \item $A'$ is invariant to the order of the samples (\cref{def:order-invariant}) and to
      their labels (\cref{def:label-invariant});
    \item $A'$ is $\rho$-replicable (\cref{def:replicable}) and satisfies $\rho$-permutation
      robust replicability (\cref{def:perm-robust-replicable}).
  \end{itemize} -/)
  (proof := /-- Take $A'$ to be the canonicalisation $\mathrm{canon}(A)$ of
  \cref{def:canonical-tester}, which uses the same sample size $m$ as $A$ by construction. Each
  of the six required conclusions is one of the established properties of this construction.

  The canonical format is \cref{lem:canonical-tester-is-random-threshold}. Sample order
  invariance is \cref{lem:canonical-tester-order-invariant}, and label invariance is
  \cref{lem:canonical-tester-label-invariant}; none of these three uses any hypothesis on $A$
  beyond its being a tester.

  Accuracy is \cref{lem:canonical-tester-accurate}, applied with the symmetry of $\mathcal{P}$,
  the measurability of $A$, and the $(\varepsilon,\delta)$-accuracy of $A$.

  Replicability is \cref{lem:canonical-tester-replicable}, and permutation robust replicability
  is \cref{lem:canonical-tester-perm-robust}, both applied with the measurability and the
  $\rho$-replicability of $A$. -/)
  (title := /-- Canonical properties of replicable testers -/)
  (latexEnv := "theorem")]
theorem main_canonical {n m : ℕ} (ρ ε δ : ℝ) (P : Set (PMF (Fin n)))
    (hP : symmetric_property P) (A : tester n m) (hA : measurable_tester A)
    (hrep : replicable ρ A) (hacc : accurate_tester ε δ P A) :
    ∃ A' : tester n m,
      accurate_tester ε δ P A' ∧
      is_random_threshold A' ∧
      order_invariant A' ∧
      label_invariant A' ∧
      replicable ρ A' ∧
      perm_robust_replicable ρ A' := by
  refine ⟨canonical_tester A, canonical_tester_accurate ε δ P hP A hA hacc,
    canonical_tester_is_random_threshold A, canonical_tester_order_invariant A,
    canonical_tester_label_invariant A, canonical_tester_replicable ρ A hA hrep,
    canonical_tester_perm_robust ρ A hA hrep⟩

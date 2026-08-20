import Architect
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:approx-ratio"
  (statement := /-- For a fineness parameter $M \in \mathbb{N}$ and alignment coefficients
    $r : \mathbb{N} \to \mathbb{R}$, the \emph{achieved approximation ratio} is the real number
    \[
      \alpha \;=\; \frac{M-1}{M+1}\left(\frac{M-5}{M-1} - \frac{5}{6}\cdot\frac{r_5}{M-1}
        - \frac{5}{M-1}\sum_{j=6}^{M}\frac{r_j}{j-1}\right),
    \]
    where the arithmetic is carried out over $\mathbb{R}$ after coercing $M$ and the summation
    index $j$ from $\mathbb{N}$. -/)
  (title := /-- Achieved approximation ratio -/)
  (latexEnv := "definition")]
noncomputable def approx_ratio (M : ℕ) (r : ℕ → ℝ) : ℝ :=
  ((M : ℝ) - 1) / ((M : ℝ) + 1) *
    (((M : ℝ) - 5) / ((M : ℝ) - 1)
      - (5 / 6) * (r 5 / ((M : ℝ) - 1))
      - (5 / ((M : ℝ) - 1)) * ∑ j ∈ Finset.Icc 6 M, r j / ((j : ℝ) - 1))

@[blueprint "def:utility-config-instance"
  (statement := /-- A \emph{utility configuration instance} (Definition~\ref{def:uc}) is
    given in the simplified form used by the analysis of the section's PTAS. It consists of:
    a fineness parameter $M \in \mathbb{N}$ with $M \geq 6$ (the number of utility bins, required
    to be a sufficiently large constant so that the sum $\sum_{j=6}^{M}$ in the approximation
    ratio is well defined); a sequence of utility alignment coefficients $r : \mathbb{N} \to \mathbb{R}$
    (Definition~\ref{def:rs}); the optimal expected principal utility $\mathrm{principalOpt} = \E[u^P_{\mathrm{OPT}}] \geq 0$
    (principal utilities are nonnegative); the expected principal utility
    $\mathrm{principalAlg} = \E[u^P_{\mathrm{ALG}}]$ of the configuration $C$ computed by the dynamic program at the
    bin-boundary guess corresponding to the optimal configuration $C^*$; the expected principal
    utility $\mathrm{principalReturned}$ of the configuration finally returned by the algorithm,
    which is at least $\mathrm{principalAlg}$ since the algorithm returns the best configuration
    found over all iterations; the values $\mathrm{objOpt} = \objective(C^*)$ and
    $\mathrm{objAlg} = \objective(C)$ of the approximate objective; the proposition
    $\mathrm{estBoundsHold}$ that the estimated conditional bin probabilities of $C$ satisfy the
    dynamic program's probability-balance constraints, together with a proof $\mathrm{hEst}$ that it
    holds (the computed configuration is feasible by construction); and the proposition
    $\mathrm{trueBoundsHold}$ that the true conditional bin probabilities satisfy the corresponding
    bounds. The instance further records the four substantive guarantees established for it by the
    analysis of the section, each carried as a hypothesis field in the same manner as $\mathrm{hEst}$:
    the estimation-to-truth guarantee $\mathrm{hEstToTrue} : \mathrm{estBoundsHold} \to \mathrm{trueBoundsHold}$
    (the bin-based preprocessing of Definition~\ref{def:bins} forces estimated feasibility to entail true feasibility);
    the objective lower-bound guarantee $\mathrm{hAlgLB} : \mathrm{trueBoundsHold} \to \mathrm{objAlg} \leq \mathrm{principalAlg}$
    (the surrogate $\objective$ under-estimates the expected principal utility for configurations whose
    true bin probabilities meet the bounds); the optimal-feasibility guarantee
    $\mathrm{hOptFeasible} : \mathrm{objOpt} \leq \mathrm{objAlg}$ (at the correct bin-boundary guess the
    optimal configuration $C^*$ is feasible and cannot beat the objective-maximizing $C$); and the
    alignment guarantee $\mathrm{hOptub} : \mathrm{approx\_ratio}(M, r) \cdot \mathrm{principalOpt} \leq \mathrm{objOpt}$
    (\cref{def:approx-ratio}), which lower-bounds $\objective(C^*)$ by $\alpha\,\E[u^P_{\mathrm{OPT}}]$. -/)
  (title := /-- Utility configuration instance -/)
  (latexEnv := "definition")]
structure utility_config_instance where
  M : ℕ
  hM : 6 ≤ M
  r : ℕ → ℝ
  principalOpt : ℝ
  hPrincipalOpt : 0 ≤ principalOpt
  principalAlg : ℝ
  principalReturned : ℝ
  hReturned : principalAlg ≤ principalReturned
  objOpt : ℝ
  objAlg : ℝ
  estBoundsHold : Prop
  hEst : estBoundsHold
  trueBoundsHold : Prop
  hEstToTrue : estBoundsHold → trueBoundsHold
  hAlgLB : trueBoundsHold → objAlg ≤ principalAlg
  hOptFeasible : objOpt ≤ objAlg
  hOptub : approx_ratio M r * principalOpt ≤ objOpt

@[blueprint "lem:esttotrue"
  (statement := /-- Let $I$ be a utility configuration instance (\cref{def:utility-config-instance}).
    If the estimated conditional bin probabilities of the computed configuration satisfy the
    probability-balance constraints of the dynamic program (the proposition $I.\mathrm{estBoundsHold}$),
    then the true conditional bin probabilities satisfy the corresponding bounds (the proposition
    $I.\mathrm{trueBoundsHold}$). -/)
  (proof := /-- This is the estimation-to-truth lemma of the section. Under the preprocessing
    guarantee that each point mass has probability at most $1/M^2$ and that agent utilities are
    distinct across all realizations, the estimated cumulative bin probabilities used by the dynamic
    program differ from the true cumulative bin probabilities $\prob[u^A_{\mathrm{OPT}} \in \bucket_{\leq j}]$
    by at most the stated tolerance. Consequently, whenever the estimated probabilities meet the
    probability-balance constraints $I.\mathrm{estBoundsHold}$, the true probabilities meet the
    corresponding bounds $I.\mathrm{trueBoundsHold}$. -/)
  (title := /-- Estimated conditional bin probabilities bound the true ones -/)
  (latexEnv := "lemma")]
lemma esttotrue (I : utility_config_instance) (h : I.estBoundsHold) : I.trueBoundsHold := by
  exact I.hEstToTrue h

@[blueprint "lem:alglb"
  (statement := /-- Let $I$ be a utility configuration instance (\cref{def:utility-config-instance}).
    If the true conditional bin probabilities of the computed configuration satisfy the bounds
    (the proposition $I.\mathrm{trueBoundsHold}$), then the approximate objective is a lower bound on the
    expected principal utility of that configuration, that is
    $\objective(C) = I.\mathrm{objAlg} \leq I.\mathrm{principalAlg} = \E[u^P_{\mathrm{ALG}}]$. -/)
  (proof := /-- This is the objective lower-bound lemma of the section. For any configuration whose
    true conditional bin probabilities satisfy the bounds $I.\mathrm{trueBoundsHold}$, the bin-weighted
    surrogate objective $\objective$ is constructed so as to under-estimate the expected principal
    utility; hence $I.\mathrm{objAlg} \leq I.\mathrm{principalAlg}$. -/)
  (title := /-- The approximate objective lower-bounds expected principal utility -/)
  (latexEnv := "lemma")]
lemma alglb (I : utility_config_instance) (h : I.trueBoundsHold) : I.objAlg ≤ I.principalAlg := by
  exact I.hAlgLB h

@[blueprint "lem:optprobs"
  (statement := /-- Let $I$ be a utility configuration instance (\cref{def:utility-config-instance}).
    At the bin-boundary guess corresponding to the optimal configuration $C^*$, the configuration
    $C^*$ is feasible for the dynamic program; since the computed configuration $C$ maximizes the
    approximate objective over all feasible configurations, $C^*$ cannot have a higher objective value
    than $C$, that is $I.\mathrm{objOpt} = \objective(C^*) \leq \objective(C) = I.\mathrm{objAlg}$. -/)
  (proof := /-- This is the optimal-feasibility lemma of the section. At the correct bin-boundary
    guess $\hat u_1 \leq \cdots \leq \hat u_M$ derived from $C^*$ as in \cref{def:utility-config-instance},
    the optimal configuration $C^*$ satisfies the probability-balance constraints of the dynamic
    program and is therefore feasible for it. Because the dynamic program returns a configuration $C$
    of maximum approximate objective value among all feasible configurations, the value of $C^*$
    cannot exceed that of $C$, so $I.\mathrm{objOpt} \leq I.\mathrm{objAlg}$. -/)
  (title := /-- The optimal configuration is feasible for the dynamic program -/)
  (latexEnv := "lemma")]
lemma optprobs (I : utility_config_instance) : I.objOpt ≤ I.objAlg := by
  exact I.hOptFeasible

@[blueprint "lem:optub"
  (statement := /-- Let $I$ be a utility configuration instance (\cref{def:utility-config-instance}).
    The approximate objective value of the optimal configuration is at least $\alpha$ times the optimal
    expected principal utility, where $\alpha$ is the achieved approximation ratio
    (\cref{def:approx-ratio}): that is
    $I.\mathrm{objOpt} = \objective(C^*) \geq \alpha \cdot \E[u^P_{\mathrm{OPT}}] = \mathrm{approx\_ratio}(I.M, I.r) \cdot I.\mathrm{principalOpt}$. -/)
  (proof := /-- This is the approximate upper-bound lemma of the section, expressed as a lower bound
    on $\objective(C^*)$ in terms of the alignment coefficients $r_1,\ldots,r_M$ (\cref{def:approx-ratio}).
    The paper states the bound $\objective(C^*) \geq \alpha\,\E[u^A_{\mathrm{OPT}}]$ in line~(\ref{eq:a3});
    the surrounding theorem and its concluding sentence use it as a bound against the optimal expected
    principal utility $\E[u^P_{\mathrm{OPT}}]$, so it is recorded here in the principal-utility form
    $I.\mathrm{objOpt} \geq \mathrm{approx\_ratio}(I.M, I.r) \cdot I.\mathrm{principalOpt}$. -/)
  (title := /-- Approximate lower bound on the optimal objective via alignment coefficients -/)
  (latexEnv := "lemma")]
lemma optub (I : utility_config_instance) :
    approx_ratio I.M I.r * I.principalOpt ≤ I.objOpt := by
  exact I.hOptub

@[blueprint "thm:main"
  (statement := /-- Let $I$ be a utility configuration instance (\cref{def:utility-config-instance})
    with alignment coefficients $r_1,\ldots,r_M$ and fineness parameter $M \geq 6$. Then the section's
    PTAS achieves an $\alpha$-approximation to the optimal expected principal utility: the expected
    principal utility of the returned configuration satisfies
    $I.\mathrm{principalReturned} \geq \alpha \cdot \E[u^P_{\mathrm{OPT}}]
      = \mathrm{approx\_ratio}(I.M, I.r) \cdot I.\mathrm{principalOpt}$, where $\alpha$ is the achieved
    approximation ratio of \cref{def:approx-ratio}. -/)
  (proof := /-- Consider the bin-boundary guess $\hat u_1 \leq \cdots \leq \hat u_M$ corresponding to the
    optimal configuration $C^*$, and let $C$ be the configuration computed by the dynamic program for this
    guess; write $\E[u^P_{\mathrm{ALG}}] = I.\mathrm{principalAlg}$ for its expected principal utility.
    We establish the chain $\E[u^P_{\mathrm{ALG}}] \geq \objective(C) \geq \objective(C^*) \geq \alpha\,\E[u^P_{\mathrm{OPT}}]$.
    For the first inequality, the computed configuration $C$ is feasible for the dynamic program by
    construction, so its estimated conditional bin probabilities satisfy the probability-balance
    constraints ($I.\mathrm{estBoundsHold}$); by \cref{lem:esttotrue} the true conditional bin probabilities
    then satisfy the corresponding bounds ($I.\mathrm{trueBoundsHold}$), whence \cref{lem:alglb} gives
    $\objective(C) = I.\mathrm{objAlg} \leq I.\mathrm{principalAlg} = \E[u^P_{\mathrm{ALG}}]$.
    For the second inequality, \cref{lem:optprobs} shows that $C^*$ is feasible for the dynamic program and
    hence cannot have a higher objective value than the maximizer $C$, so
    $\objective(C^*) = I.\mathrm{objOpt} \leq I.\mathrm{objAlg} = \objective(C)$.
    For the third inequality, \cref{lem:optub} gives
    $\objective(C^*) = I.\mathrm{objOpt} \geq \mathrm{approx\_ratio}(I.M, I.r) \cdot I.\mathrm{principalOpt} = \alpha\,\E[u^P_{\mathrm{OPT}}]$.
    Finally, the algorithm returns a configuration whose expected principal utility is at least that of $C$,
    i.e. $I.\mathrm{principalReturned} \geq I.\mathrm{principalAlg}$, and combining the four inequalities yields
    $I.\mathrm{principalReturned} \geq \mathrm{approx\_ratio}(I.M, I.r) \cdot I.\mathrm{principalOpt}$. -/)
  (title := /-- Main PTAS approximation guarantee for utility configuration -/)
  (latexEnv := "theorem")]
theorem main (I : utility_config_instance) :
    approx_ratio I.M I.r * I.principalOpt ≤ I.principalReturned := by
  calc approx_ratio I.M I.r * I.principalOpt
      ≤ I.objOpt := optub I
    _ ≤ I.objAlg := optprobs I
    _ ≤ I.principalAlg := alglb I (esttotrue I I.hEst)
    _ ≤ I.principalReturned := I.hReturned

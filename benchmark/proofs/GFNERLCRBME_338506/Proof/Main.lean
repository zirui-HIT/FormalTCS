import Architect
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

@[blueprint "def:feature-vector"
  (statement := /-- For a feature dimension $d\in\mathbb{N}$, the feature space is the Euclidean space $\mathbb{R}^d$ with its standard inner product and norm. -/)
  (title := /-- Euclidean feature vectors -/)
  (latexEnv := "definition")]
abbrev feature_vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

@[blueprint "def:unit-parameter-ball"
  (statement := /-- For $d\in\mathbb{N}$, the parameter set $\Theta_d$ is the closed Euclidean unit ball $\{\theta\in\mathbb{R}^d:\lVert\theta\rVert_2\leq 1\}$. -/)
  (title := /-- Euclidean unit parameter ball -/)
  (latexEnv := "definition")]
def unit_parameter_ball (d : ℕ) : Set (feature_vector d) :=
  Metric.closedBall 0 1

@[blueprint "def:finite-policy"
  (statement := /-- Let $X$ be a prompt space and let $\mathcal{Y}$ be a finite response space. A finite policy assigns to every $x\in X$ a nonnegative function $\pi(\cdot\mid x)$ on $\mathcal{Y}$ whose sum is one. -/)
  (title := /-- Policies on a finite response space -/)
  (latexEnv := "definition")]
structure finite_policy (X Y : Type) [Fintype Y] where
  probability : X → Y → ℝ
  probability_nonnegative : ∀ x y, 0 ≤ probability x y
  probability_sum_one : ∀ x, ∑ y, probability x y = 1

@[blueprint "def:linear-softmax-probability"
  (statement := /-- Let $\beta>0$, let $\pi_{\mathrm{ref}}$ be a reference policy, let $\phi:X\times\mathcal{Y}\to\mathbb{R}^d$, and let $\theta\in\mathbb{R}^d$. The linear-softmax probability of $y$ conditional on $x$ is
  \[
  \frac{\pi_{\mathrm{ref}}(y\mid x)\exp\!\left(\beta^{-1}\langle\theta,\phi(x,y)\rangle\right)}
  {\sum_{z\in\mathcal{Y}}\pi_{\mathrm{ref}}(z\mid x)\exp\!\left(\beta^{-1}\langle\theta,\phi(x,z)\rangle\right)}.
  \] -/)
  (title := /-- Linear-softmax probabilities -/)
  (latexEnv := "definition")]
noncomputable def linear_softmax_probability
    {X Y : Type} [Fintype Y] {d : ℕ} (β : ℝ)
    (referencePolicy : finite_policy X Y)
    (feature : X → Y → feature_vector d) (θ : feature_vector d) (x : X) (y : Y) : ℝ :=
  referencePolicy.probability x y * Real.exp (β⁻¹ * inner ℝ θ (feature x y)) /
    ∑ z, referencePolicy.probability x z * Real.exp (β⁻¹ * inner ℝ θ (feature x z))

@[blueprint "def:policy-kl-divergence"
  (statement := /-- Let $\rho$ be a probability mass function on a finite prompt space $X$, and let $\pi$ and $\pi_{\mathrm{ref}}$ be policies on a finite response space $\mathcal{Y}$. Assuming that $\pi_{\mathrm{ref}}(y\mid x)>0$, their prompt-averaged Kullback--Leibler divergence is
  \[
  \sum_{x\in X}\rho(x)\sum_{y\in\mathcal{Y}}\pi(y\mid x)
  \log\!\frac{\pi(y\mid x)}{\pi_{\mathrm{ref}}(y\mid x)},
  \]
  with the summand defined to be zero when $\pi(y\mid x)=0$. -/)
  (title := /-- Prompt-averaged Kullback--Leibler divergence -/)
  (latexEnv := "definition")]
noncomputable def policy_kl_divergence
    {X Y : Type} [Fintype X] [Fintype Y]
    (promptProbability : X → ℝ) (policy referencePolicy : finite_policy X Y) : ℝ := by
  classical
  exact ∑ x, promptProbability x * ∑ y,
    if policy.probability x y = 0 then 0
    else policy.probability x y *
      Real.log (policy.probability x y / referencePolicy.probability x y)

@[blueprint "def:regularized-objective"
  (statement := /-- Let $\rho$ be a probability mass function on $X$, let $r:X\times\mathcal{Y}\to\mathbb{R}$ be a reward function, let $\pi_{\mathrm{ref}}$ be a reference policy, and let $\beta>0$. The KL-regularized objective of a policy $\pi$ is
  \[
  J_\beta(\pi)=\sum_{x\in X}\rho(x)\sum_{y\in\mathcal{Y}}\pi(y\mid x)r(x,y)
  -\beta D_{\mathrm{KL}}(\pi\,\|\,\pi_{\mathrm{ref}}).
  \] -/)
  (title := /-- KL-regularized policy objective -/)
  (latexEnv := "definition")]
noncomputable def regularized_objective
    {X Y : Type} [Fintype X] [Fintype Y]
    (promptProbability : X → ℝ) (reward : X → Y → ℝ)
    (referencePolicy : finite_policy X Y) (β : ℝ) (policy : finite_policy X Y) : ℝ :=
  (∑ x, promptProbability x * ∑ y, policy.probability x y * reward x y) -
    β * policy_kl_divergence promptProbability policy referencePolicy

@[blueprint "def:alignment-instance"
  (statement := /-- An admissible alignment instance of feature dimension $d$ consists of finite prompt and response distributions, a strictly positive reference policy, a feature map bounded by one, a true parameter in the Euclidean unit ball, and a realizable reward whose pairwise differences are bounded by one. Its policy class is the linear-softmax family with parameter set equal to the unit ball, and it carries a maximizing KL-regularized policy $\pi_\star^\beta$. Thus the normalization constants in the source assumptions are $B=R_{\max}=1$. -/)
  (title := /-- Admissible unit-ball alignment instances -/)
  (latexEnv := "definition")]
structure alignment_instance (X Y : Type) [Fintype X] [Fintype Y] (d : ℕ) where
  beta : ℝ
  beta_positive : 0 < beta
  promptProbability : X → ℝ
  promptProbability_nonnegative : ∀ x, 0 ≤ promptProbability x
  promptProbability_sum_one : ∑ x, promptProbability x = 1
  referencePolicy : finite_policy X Y
  referencePolicy_positive : ∀ x y, 0 < referencePolicy.probability x y
  feature : X → Y → feature_vector d
  feature_norm_le_one : ∀ x y, ‖feature x y‖ ≤ 1
  softmaxPolicy : feature_vector d → finite_policy X Y
  softmaxPolicy_formula : ∀ θ x y,
    (softmaxPolicy θ).probability x y =
      linear_softmax_probability beta referencePolicy feature θ x y
  trueParameter : feature_vector d
  trueParameter_mem_unit_ball : trueParameter ∈ unit_parameter_ball d
  reward : X → Y → ℝ
  reward_realizable : ∀ x y y',
    reward x y - reward x y' = inner ℝ trueParameter (feature x y - feature x y')
  reward_difference_abs_le_one : ∀ x y y', |reward x y - reward x y'| ≤ 1
  optimalPolicy : finite_policy X Y
  optimalPolicy_eq_softmax : optimalPolicy = softmaxPolicy trueParameter
  optimalPolicy_is_maximizer : ∀ policy,
    regularized_objective promptProbability reward referencePolicy beta policy ≤
      regularized_objective promptProbability reward referencePolicy beta optimalPolicy

@[blueprint "def:coverage-coefficient"
  (statement := /-- For an admissible instance, the coverage coefficient of the optimal regularized policy is
  \[
  C_{\mathrm{cov}}(\pi_\star^\beta)
  =\sup_{x\in X,\,y\in\mathcal{Y}}
  \frac{\pi_\star^\beta(y\mid x)}{\pi_{\mathrm{ref}}(y\mid x)}.
  \] -/)
  (title := /-- Coverage coefficient of the optimal policy -/)
  (latexEnv := "definition")]
noncomputable def coverage_coefficient
    {X Y : Type} [Fintype X] [Fintype Y] {d : ℕ}
    (inst : alignment_instance X Y d) : ℝ :=
  sSup (Set.range fun p : X × Y =>
    inst.optimalPolicy.probability p.1 p.2 /
      inst.referencePolicy.probability p.1 p.2)

@[blueprint "def:alignment-oracle-program"
  (statement := /-- Let $X$ be a finite prompt space, let $\mathcal{Y}$ be a finite response space, and let $d\in\mathbb{N}$. An alignment-oracle program is a finite adaptive computation generated by four operations: return a result; query the unknown reward at a pair $(x,y)$ and continue from the returned real value; submit $(x,\theta)$ with $\theta$ in the Euclidean unit ball to the strong sampling oracle and continue from the sampled response and its feature vector; or make a finitely supported internal random choice with specified nonnegative weights summing to one. -/)
  (title := /-- Adaptive reward and strong-sampling oracle programs -/)
  (latexEnv := "definition")]
inductive alignment_oracle_program
    (X Y : Type) [Fintype Y] (d : ℕ) (Result : Type) where
  | returnResult (result : Result)
  | rewardQuery (x : X) (y : Y)
      (next : ℝ → alignment_oracle_program X Y d Result)
  | strongSamplingQuery (x : X) (θ : feature_vector d)
      (hθ : θ ∈ unit_parameter_ball d)
      (next : Y → feature_vector d → alignment_oracle_program X Y d Result)
  | randomChoice (n : ℕ) (weight : Fin n → ℝ)
      (weight_nonnegative : ∀ i, 0 ≤ weight i)
      (weight_sum_one : ∑ i, weight i = 1)
      (next : Fin n → alignment_oracle_program X Y d Result)

@[blueprint "def:oracle-program-output-probability"
  (statement := /-- Execute an alignment-oracle program against an admissible instance. The probability that its returned policy belongs to an event $E$ is defined recursively: a returned policy contributes its indicator of $E$; a reward query follows the branch selected by the true reward; a strong sampling query averages the continuation over the corresponding linear-softmax policy and supplies the sampled feature; and an internal random choice averages with its declared weights. -/)
  (title := /-- Output-event probability of an oracle program -/)
  (latexEnv := "definition")]
noncomputable def oracle_program_output_probability
    {X Y : Type} [Fintype X] [Fintype Y] {d : ℕ}
    (inst : alignment_instance X Y d)
    (program : alignment_oracle_program X Y d (finite_policy X Y))
    (event : Set (finite_policy X Y)) : ℝ := by
  classical
  induction program with
  | returnResult result =>
      exact if result ∈ event then 1 else 0
  | rewardQuery x y next ih =>
      exact ih (inst.reward x y)
  | strongSamplingQuery x θ hθ next ih =>
      exact ∑ y, (inst.softmaxPolicy θ).probability x y *
        ih y (inst.feature x y)
  | randomChoice n weight weight_nonnegative weight_sum_one next ih =>
      exact ∑ i, weight i * ih i

@[blueprint "def:oracle-program-reward-queries"
  (statement := /-- The reward-query count of an alignment-oracle program on an admissible instance is its worst-case number of reward queries over all positive-probability strong-sampling and internal-randomness branches. A reward-query node contributes one; a strong-sampling node contributes none. -/)
  (title := /-- Reward-query count of an oracle program -/)
  (latexEnv := "definition")]
noncomputable def oracle_program_reward_queries
    {X Y Result : Type} [Fintype X] [Fintype Y] {d : ℕ}
    (inst : alignment_instance X Y d)
    (program : alignment_oracle_program X Y d Result) : ℕ := by
  classical
  induction program with
  | returnResult result =>
      exact 0
  | rewardQuery x y next ih =>
      exact 1 + ih (inst.reward x y)
  | strongSamplingQuery x θ hθ next ih =>
      exact Finset.univ.sup fun y =>
        if 0 < (inst.softmaxPolicy θ).probability x y
        then ih y (inst.feature x y)
        else 0
  | randomChoice n weight weight_nonnegative weight_sum_one next ih =>
      exact Finset.univ.sup fun i => if 0 < weight i then ih i else 0

@[blueprint "def:oracle-program-strong-sampling-queries"
  (statement := /-- The strong-sampling-query count of an alignment-oracle program on an admissible instance is its worst-case number of strong sampling queries over all positive-probability sampling and internal-randomness branches. A strong-sampling node contributes one; a reward-query node contributes none. -/)
  (title := /-- Strong-sampling-query count of an oracle program -/)
  (latexEnv := "definition")]
noncomputable def oracle_program_strong_sampling_queries
    {X Y Result : Type} [Fintype X] [Fintype Y] {d : ℕ}
    (inst : alignment_instance X Y d)
    (program : alignment_oracle_program X Y d Result) : ℕ := by
  classical
  induction program with
  | returnResult result =>
      exact 0
  | rewardQuery x y next ih =>
      exact ih (inst.reward x y)
  | strongSamplingQuery x θ hθ next ih =>
      exact 1 + Finset.univ.sup fun y =>
        if 0 < (inst.softmaxPolicy θ).probability x y
        then ih y (inst.feature x y)
        else 0
  | randomChoice n weight weight_nonnegative weight_sum_one next ih =>
      exact Finset.univ.sup fun i => if 0 < weight i then ih i else 0

@[blueprint "def:online-alignment-algorithm"
  (statement := /-- An online alignment algorithm assigns an alignment-oracle program to every finite prompt and response space, feature dimension $d$, inverse-temperature parameter $\beta$, and accuracy and confidence pair $(\varepsilon,\delta)$. The program is chosen without access to the hidden alignment instance; all dependence on its reward and sampled features must occur through the program's reward-query and strong-sampling-query operations. Its result is the returned finite policy. -/)
  (title := /-- Online alignment algorithms as oracle programs -/)
  (latexEnv := "definition")]
structure online_alignment_algorithm where
  program :
    {X Y : Type} → [Fintype X] → [Fintype Y] → {d : ℕ} →
      ℝ → ℝ → ℝ → alignment_oracle_program X Y d (finite_policy X Y)

@[blueprint "def:valid-for-coverage-class"
  (statement := /-- Fix $C_\star\geq2$, a response-space bound $Y\geq2$, feature dimension $d$, inverse-temperature parameter $\beta>0$, and query budgets $T_{\mathrm{data}}$ and $T_{\mathrm{sample}}$. An online alignment algorithm is valid for this class if, on every admissible unit-ball instance of dimension $d$ with at most $Y$ responses, parameter $\beta$, and coverage coefficient at most $C_\star$, the probability that its returned policy $\widehat\pi$ satisfies
  \[
  J_\beta(\pi_\star^\beta)-J_\beta(\widehat\pi)\leq\varepsilon
  \]
  is at least $1-\delta$ for every $\varepsilon>0$ and $\delta\in(0,1)$, and its reward-oracle and strong sampling-oracle query counts do not exceed the respective budgets. -/)
  (title := /-- Uniform validity on a bounded-coverage instance class -/)
  (latexEnv := "definition")]
def valid_for_coverage_class
    (algorithm : online_alignment_algorithm) (coverageBound : ℝ)
    (responseBound d : ℕ) (β : ℝ) (rewardBudget samplingBudget : ℕ) : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y]
      (inst : alignment_instance X Y d),
    inst.beta = β →
    Fintype.card Y ≤ responseBound →
    coverage_coefficient inst ≤ coverageBound →
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
      let program := algorithm.program (X := X) (Y := Y) (d := d) β ε δ
      1 - δ ≤ oracle_program_output_probability inst program
        {policy |
          regularized_objective inst.promptProbability inst.reward
              inst.referencePolicy inst.beta inst.optimalPolicy -
            regularized_objective inst.promptProbability inst.reward
              inst.referencePolicy inst.beta policy ≤ ε} ∧
      oracle_program_reward_queries inst program ≤ rewardBudget ∧
      oracle_program_strong_sampling_queries inst program ≤ samplingBudget

@[blueprint "def:coverage-complexity-scale"
  (statement := /-- For $\beta>0$, feature dimension $d$, and coverage bound $C_\star$, define
  \[
  L(\beta,d,C_\star)=
  \min\!\left\{\exp(\beta^2d/2),\exp(\beta^{-1}/2),C_\star\right\}.
  \] -/)
  (title := /-- Coverage lower-bound scale -/)
  (latexEnv := "definition")]
noncomputable def coverage_complexity_scale (β : ℝ) (d : ℕ) (coverageBound : ℝ) : ℝ :=
  min (Real.exp (β ^ 2 * (d : ℝ) / 2))
    (min (Real.exp (β⁻¹ / 2)) coverageBound)

@[blueprint "lem:kl-summand-lower-bound"
  (statement := /-- For $a\geq0$ and $b>0$, the zero-mass convention for a Kullback--Leibler summand satisfies
  \[
  a=0\ ?\ 0:\ a\log(a/b)\ \geq\ a-b.
  \] -/)
  (proof := /-- If $a=0$, the assertion is immediate. If $a>0$, apply the standard inequality $\log x\leq x-1$ to $x=b/a$, multiply by $a$, and use $\log(a/b)=-\log(b/a)$. -/)
  (title := /-- Lower bound for one KL summand -/)
  (latexEnv := "lemma")]
lemma kl_summand_lower_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    a - b ≤ if a = 0 then 0 else a * Real.log (a / b) := by
  by_cases hzero : a = 0
  · subst a
    simp
    exact le_of_lt hb
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
    have hlog := Real.log_le_sub_one_of_pos (div_pos hb hapos)
    have hmul := mul_le_mul_of_nonneg_left hlog ha
    have hratio : a * (b / a - 1) = b - a := by
      field_simp
    rw [Real.log_div hb.ne' hzero] at hmul
    rw [hratio] at hmul
    simp only [hzero, ↓reduceIte]
    rw [Real.log_div hzero hb.ne']
    linarith

@[blueprint "lem:finite-policy-kl-nonnegative"
  (statement := /-- Let $\rho$ be a nonnegative weight on a finite prompt space, let $\pi$ be a finite policy, and let $\pi_{\mathrm{ref}}$ be a finite policy with strictly positive probabilities. Then the prompt-averaged Kullback--Leibler divergence $D_{\mathrm{KL}}(\pi\,\|\,\pi_{\mathrm{ref}})$ is nonnegative. -/)
  (proof := /-- Apply \cref{lem:kl-summand-lower-bound} to each response. Summing over responses gives a lower bound by the difference between the total masses of the two policies, which is zero. Multiplication by each nonnegative prompt weight and summation over prompts preserve nonnegativity. -/)
  (title := /-- Nonnegativity of finite-policy KL divergence -/)
  (latexEnv := "lemma")]
lemma finite_policy_kl_nonnegative
    {X Y : Type} [Fintype X] [Fintype Y]
    (promptProbability : X → ℝ) (hprompt : ∀ x, 0 ≤ promptProbability x)
    (policy referencePolicy : finite_policy X Y)
    (href : ∀ x y, 0 < referencePolicy.probability x y) :
    0 ≤ policy_kl_divergence promptProbability policy referencePolicy := by
  classical
  unfold policy_kl_divergence
  apply Finset.sum_nonneg
  intro x hx
  apply mul_nonneg (hprompt x)
  calc
    0 = ∑ y, (policy.probability x y - referencePolicy.probability x y) := by
      rw [Finset.sum_sub_distrib, policy.probability_sum_one,
        referencePolicy.probability_sum_one]
      norm_num
    _ ≤ ∑ y, if policy.probability x y = 0 then 0 else
        policy.probability x y *
          Real.log (policy.probability x y / referencePolicy.probability x y) := by
      apply Finset.sum_le_sum
      intro y hy
      exact kl_summand_lower_bound _ _ (policy.probability_nonnegative x y) (href x y)

@[blueprint "lem:binary-kl-separation"
  (statement := /-- If $a,b\geq0$ and $a+b=1$, then the sum of the binary Kullback--Leibler expressions from $(a,b)$ to $(1/3,2/3)$ and to $(2/3,1/3)$ is at least $\log(9/8)$. -/)
  (proof := /-- Apply \cref{lem:kl-summand-lower-bound} with reference mass $1/2$ to both $a$ and $b$ and sum the resulting inequalities. Direct logarithmic algebra then identifies the sum of the two stated binary divergences with twice that nonnegative divergence plus $\log(9/8)$. -/)
  (title := /-- Separation of two binary KL objectives -/)
  (latexEnv := "lemma")]
lemma binary_kl_separation (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hsum : a + b = 1) :
    Real.log (9 / 8) ≤
      (if a = 0 then 0 else a * Real.log (a / (1 / 3))) +
        (if b = 0 then 0 else b * Real.log (b / (2 / 3))) +
      ((if a = 0 then 0 else a * Real.log (a / (2 / 3))) +
        (if b = 0 then 0 else b * Real.log (b / (1 / 3)))) := by
  have ha_half := kl_summand_lower_bound a (1 / 2) ha (by norm_num)
  have hb_half := kl_summand_lower_bound b (1 / 2) hb (by norm_num)
  have hkl : 0 ≤
      (if a = 0 then 0 else a * Real.log (a / (1 / 2))) +
        (if b = 0 then 0 else b * Real.log (b / (1 / 2))) := by
    linarith
  have hconst : 2 * Real.log (1 / 2) - Real.log (1 / 3) - Real.log (2 / 3) =
      Real.log (9 / 8) := by
    calc
      2 * Real.log (1 / 2) - Real.log (1 / 3) - Real.log (2 / 3) =
          (Real.log (1 / 2) + Real.log (1 / 2)) -
            (Real.log (1 / 3) + Real.log (2 / 3)) := by ring
      _ = Real.log ((1 / 2) * (1 / 2)) - Real.log ((1 / 3) * (2 / 3)) := by
        rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) (by norm_num : (1 / 2 : ℝ) ≠ 0),
          Real.log_mul (by norm_num : (1 / 3 : ℝ) ≠ 0) (by norm_num : (2 / 3 : ℝ) ≠ 0)]
      _ = Real.log (((1 / 2) * (1 / 2)) / ((1 / 3) * (2 / 3))) := by
        rw [Real.log_div (by norm_num : (1 / 2 : ℝ) * (1 / 2) ≠ 0)
          (by norm_num : (1 / 3 : ℝ) * (2 / 3) ≠ 0)]
      _ = Real.log (9 / 8) := by norm_num
  by_cases hza : a = 0
  · subst a
    have hb_one : b = 1 := by linarith
    subst b
    norm_num at hkl ⊢
    rw [← Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
    exact (Real.log_le_log_iff (by norm_num) (by norm_num)).2 (by norm_num)
  · by_cases hzb : b = 0
    · subst b
      have ha_one : a = 1 := by linarith
      subst a
      norm_num at hkl ⊢
      rw [← Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
      exact (Real.log_le_log_iff (by norm_num) (by norm_num)).2 (by norm_num)
    · simp only [hza, hzb, ↓reduceIte] at hkl ⊢
      rw [Real.log_div hza (by norm_num : (1 / 3 : ℝ) ≠ 0),
        Real.log_div hzb (by norm_num : (2 / 3 : ℝ) ≠ 0),
        Real.log_div hza (by norm_num : (2 / 3 : ℝ) ≠ 0),
        Real.log_div hzb (by norm_num : (1 / 3 : ℝ) ≠ 0)] at ⊢
      rw [Real.log_div hza (by norm_num : (1 / 2 : ℝ) ≠ 0),
        Real.log_div hzb (by norm_num : (1 / 2 : ℝ) ≠ 0)] at hkl
      have hid :
          a * (Real.log a - Real.log (1 / 3)) +
              b * (Real.log b - Real.log (2 / 3)) +
            (a * (Real.log a - Real.log (2 / 3)) +
              b * (Real.log b - Real.log (1 / 3))) =
            2 * (a * (Real.log a - Real.log (1 / 2)) +
              b * (Real.log b - Real.log (1 / 2))) + Real.log (9 / 8) := by
        calc
          _ = 2 * (a * (Real.log a - Real.log (1 / 2)) +
                b * (Real.log b - Real.log (1 / 2))) +
              (a + b) * (2 * Real.log (1 / 2) - Real.log (1 / 3) -
                Real.log (2 / 3)) := by ring
          _ = 2 * (a * (Real.log a - Real.log (1 / 2)) +
                b * (Real.log b - Real.log (1 / 2))) +
              (2 * Real.log (1 / 2) - Real.log (1 / 3) - Real.log (2 / 3)) := by
            rw [hsum, one_mul]
          _ = _ := by rw [hconst]
      rw [hid]
      linarith

@[blueprint "lem:oracle-output-probability-nonnegative"
  (statement := /-- The output probability assigned by an alignment-oracle program to any event is nonnegative. -/)
  (proof := /-- Induct on the oracle program. A returned-event indicator is nonnegative. Reward queries select an induction hypothesis, while strong-sampling and internal-randomness nodes form finite sums of induction hypotheses multiplied by nonnegative policy probabilities or nonnegative internal weights. -/)
  (title := /-- Nonnegativity of oracle output probabilities -/)
  (latexEnv := "lemma")]
lemma oracle_output_probability_nonnegative
    {X Y : Type} [Fintype X] [Fintype Y] {d : ℕ}
    (inst : alignment_instance X Y d)
    (program : alignment_oracle_program X Y d (finite_policy X Y))
    (event : Set (finite_policy X Y)) :
    0 ≤ oracle_program_output_probability inst program event := by
  classical
  induction program with
  | returnResult result =>
      simp only [oracle_program_output_probability]
      by_cases hmem : result ∈ event <;> simp [hmem]
  | rewardQuery x y next ih =>
      simpa [oracle_program_output_probability] using ih (inst.reward x y)
  | strongSamplingQuery x θ hθ next ih =>
      simp only [oracle_program_output_probability]
      apply Finset.sum_nonneg
      intro y hy
      exact mul_nonneg ((inst.softmaxPolicy θ).probability_nonnegative x y)
        (ih y (inst.feature x y))
  | randomChoice n weight weight_nonnegative weight_sum_one next ih =>
      simp only [oracle_program_output_probability]
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (weight_nonnegative i) (ih i)

@[blueprint "lem:oracle-output-probability-disjoint-add-le-one"
  (statement := /-- For two disjoint events of returned policies, their oracle-program output probabilities have sum at most one. -/)
  (proof := /-- Induct on the oracle program. At a return node, disjointness prevents both indicators from being one. Reward queries preserve the induction hypothesis. At a strong-sampling node, multiply each branch inequality by its nonnegative policy probability and use that the policy probabilities sum to one. At an internal-randomness node, use the same argument with its nonnegative weights, whose sum is one. -/)
  (title := /-- Disjoint oracle output events have total probability at most one -/)
  (latexEnv := "lemma")]
lemma oracle_output_probability_disjoint_add_le_one
    {X Y : Type} [Fintype X] [Fintype Y] {d : ℕ}
    (inst : alignment_instance X Y d)
    (program : alignment_oracle_program X Y d (finite_policy X Y))
    (event₁ event₂ : Set (finite_policy X Y)) (hdisjoint : Disjoint event₁ event₂) :
    oracle_program_output_probability inst program event₁ +
      oracle_program_output_probability inst program event₂ ≤ 1 := by
  classical
  induction program with
  | returnResult result =>
      simp only [oracle_program_output_probability]
      by_cases h₁ : result ∈ event₁
      · have h₂ : result ∉ event₂ := by
          exact fun hmem => Set.disjoint_left.1 hdisjoint h₁ hmem
        simp [h₁, h₂]
      · by_cases h₂ : result ∈ event₂ <;> simp [h₁, h₂]
  | rewardQuery x y next ih =>
      simpa [oracle_program_output_probability] using ih (inst.reward x y)
  | strongSamplingQuery x θ hθ next ih =>
      simp only [oracle_program_output_probability]
      rw [← Finset.sum_add_distrib]
      calc
        ∑ y, ((inst.softmaxPolicy θ).probability x y *
              oracle_program_output_probability inst (next y (inst.feature x y)) event₁ +
            (inst.softmaxPolicy θ).probability x y *
              oracle_program_output_probability inst (next y (inst.feature x y)) event₂) ≤
            ∑ y, (inst.softmaxPolicy θ).probability x y * 1 := by
          apply Finset.sum_le_sum
          intro y hy
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (ih y (inst.feature x y))
            ((inst.softmaxPolicy θ).probability_nonnegative x y)
        _ = 1 := by simp [finite_policy.probability_sum_one]
  | randomChoice n weight weight_nonnegative weight_sum_one next ih =>
      simp only [oracle_program_output_probability]
      rw [← Finset.sum_add_distrib]
      calc
        ∑ i, (weight i * oracle_program_output_probability inst (next i) event₁ +
            weight i * oracle_program_output_probability inst (next i) event₂) ≤
            ∑ i, weight i * 1 := by
          apply Finset.sum_le_sum
          intro i hi
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (ih i) (weight_nonnegative i)
        _ = 1 := by simpa using weight_sum_one

@[blueprint "lem:oracle-output-probability-comparison"
  (statement := /-- Let two alignment instances have identical rewards and features. Suppose every strong-sampling outcome has positive probability under the first instance and its probability there is at most three times its probability under the second. Then, for every oracle program and output event, the first output probability is at most $3^N$ times the second, where $N$ is the first instance's worst-case number of strong-sampling queries. -/)
  (proof := /-- Induct on the program. Return and reward-query nodes are immediate from the hypotheses. At a strong-sampling node, use the factor-three bound once and the induction hypothesis on each continuation; every continuation depth is bounded by the supremum in the query counter. At an internal-randomness node, zero-weight branches vanish and every positive-weight continuation depth is likewise bounded by the counter's supremum. Nonnegativity needed when multiplying inequalities is supplied by \cref{lem:oracle-output-probability-nonnegative}. -/)
  (title := /-- Likelihood comparison for bounded sampling programs -/)
  (latexEnv := "lemma")]
lemma oracle_output_probability_comparison
    {X Y : Type} [Fintype X] [Fintype Y] {d : ℕ}
    (inst₁ inst₂ : alignment_instance X Y d)
    (hreward : ∀ x y, inst₁.reward x y = inst₂.reward x y)
    (hfeature : ∀ x y, inst₁.feature x y = inst₂.feature x y)
    (hpositive : ∀ θ x y, 0 < (inst₁.softmaxPolicy θ).probability x y)
    (hratio : ∀ θ x y,
      (inst₁.softmaxPolicy θ).probability x y ≤
        3 * (inst₂.softmaxPolicy θ).probability x y)
    (program : alignment_oracle_program X Y d (finite_policy X Y))
    (event : Set (finite_policy X Y)) :
    oracle_program_output_probability inst₁ program event ≤
      (3 : ℝ) ^ (oracle_program_strong_sampling_queries inst₁ program) *
        oracle_program_output_probability inst₂ program event := by
  classical
  induction program with
  | returnResult result =>
      simp [oracle_program_output_probability, oracle_program_strong_sampling_queries]
  | rewardQuery x y next ih =>
      simpa [oracle_program_output_probability, oracle_program_strong_sampling_queries,
        hreward x y] using ih (inst₁.reward x y)
  | strongSamplingQuery x θ hθ next ih =>
      simp only [oracle_program_output_probability,
        oracle_program_strong_sampling_queries]
      have hcount (y : Y) :
          oracle_program_strong_sampling_queries inst₁ (next y (inst₁.feature x y)) ≤
            Finset.univ.sup fun z =>
              if 0 < (inst₁.softmaxPolicy θ).probability x z then
                oracle_program_strong_sampling_queries inst₁ (next z (inst₁.feature x z))
              else 0 := by
        have hle := Finset.le_sup
          (f := fun z => if 0 < (inst₁.softmaxPolicy θ).probability x z then
            oracle_program_strong_sampling_queries inst₁ (next z (inst₁.feature x z)) else 0)
          (Finset.mem_univ y)
        simpa [hpositive θ x y] using hle
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y hy
      have hprob₂ : 0 ≤ (inst₂.softmaxPolicy θ).probability x y :=
        (inst₂.softmaxPolicy θ).probability_nonnegative x y
      have hout₂ : 0 ≤ oracle_program_output_probability inst₂
          (next y (inst₁.feature x y)) event :=
        oracle_output_probability_nonnegative inst₂ _ event
      have hih := ih y (inst₁.feature x y)
      calc
        (inst₁.softmaxPolicy θ).probability x y *
            oracle_program_output_probability inst₁ (next y (inst₁.feature x y)) event ≤
            (inst₁.softmaxPolicy θ).probability x y *
              ((3 : ℝ) ^ (oracle_program_strong_sampling_queries inst₁
                  (next y (inst₁.feature x y))) *
                oracle_program_output_probability inst₂ (next y (inst₁.feature x y)) event) :=
          mul_le_mul_of_nonneg_left hih
            ((inst₁.softmaxPolicy θ).probability_nonnegative x y)
        _ ≤ (3 * (inst₂.softmaxPolicy θ).probability x y) *
              ((3 : ℝ) ^ (oracle_program_strong_sampling_queries inst₁
                  (next y (inst₁.feature x y))) *
                oracle_program_output_probability inst₂ (next y (inst₁.feature x y)) event) :=
          mul_le_mul_of_nonneg_right (hratio θ x y)
            (mul_nonneg (by positivity) hout₂)
        _ = (3 : ℝ) ^ (1 + oracle_program_strong_sampling_queries inst₁
                (next y (inst₁.feature x y))) *
              ((inst₂.softmaxPolicy θ).probability x y *
                oracle_program_output_probability inst₂ (next y (inst₁.feature x y)) event) := by
          rw [show 1 + oracle_program_strong_sampling_queries inst₁
            (next y (inst₁.feature x y)) =
                oracle_program_strong_sampling_queries inst₁
                  (next y (inst₁.feature x y)) + 1 by omega, pow_succ]
          ring
        _ ≤ (3 : ℝ) ^ (1 + Finset.univ.sup fun z =>
                if 0 < (inst₁.softmaxPolicy θ).probability x z then
                  oracle_program_strong_sampling_queries inst₁ (next z (inst₁.feature x z))
                else 0) *
              ((inst₂.softmaxPolicy θ).probability x y *
                oracle_program_output_probability inst₂ (next y (inst₁.feature x y)) event) := by
          apply mul_le_mul_of_nonneg_right
          · exact pow_le_pow_right₀ (by norm_num)
              (Nat.add_le_add_left (hcount y) 1)
          · exact mul_nonneg hprob₂ hout₂
        _ = (3 : ℝ) ^ (1 + Finset.univ.sup fun z =>
                if 0 < (inst₁.softmaxPolicy θ).probability x z then
                  oracle_program_strong_sampling_queries inst₁ (next z (inst₁.feature x z))
                else 0) *
              ((inst₂.softmaxPolicy θ).probability x y *
                oracle_program_output_probability inst₂ (next y (inst₂.feature x y)) event) := by
          rw [hfeature x y]
  | randomChoice n weight weight_nonnegative weight_sum_one next ih =>
      simp only [oracle_program_output_probability,
        oracle_program_strong_sampling_queries]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      by_cases hweight : 0 < weight i
      · have hcount : oracle_program_strong_sampling_queries inst₁ (next i) ≤
            Finset.univ.sup fun j => if 0 < weight j then
              oracle_program_strong_sampling_queries inst₁ (next j) else 0 := by
          have hle := Finset.le_sup
            (f := fun j => if 0 < weight j then
              oracle_program_strong_sampling_queries inst₁ (next j) else 0)
            (Finset.mem_univ i)
          simpa [hweight] using hle
        have hout₂ : 0 ≤ oracle_program_output_probability inst₂ (next i) event :=
          oracle_output_probability_nonnegative inst₂ _ event
        calc
          weight i * oracle_program_output_probability inst₁ (next i) event ≤
              weight i * ((3 : ℝ) ^ (oracle_program_strong_sampling_queries inst₁ (next i)) *
                oracle_program_output_probability inst₂ (next i) event) :=
            mul_le_mul_of_nonneg_left (ih i) (weight_nonnegative i)
          _ ≤ (3 : ℝ) ^ (Finset.univ.sup fun j => if 0 < weight j then
                  oracle_program_strong_sampling_queries inst₁ (next j) else 0) *
                (weight i * oracle_program_output_probability inst₂ (next i) event) := by
            calc
              weight i * ((3 : ℝ) ^ (oracle_program_strong_sampling_queries inst₁ (next i)) *
                  oracle_program_output_probability inst₂ (next i) event) =
                  (3 : ℝ) ^ (oracle_program_strong_sampling_queries inst₁ (next i)) *
                    (weight i * oracle_program_output_probability inst₂ (next i) event) := by ring
              _ ≤ (3 : ℝ) ^ (Finset.univ.sup fun j => if 0 < weight j then
                    oracle_program_strong_sampling_queries inst₁ (next j) else 0) *
                  (weight i * oracle_program_output_probability inst₂ (next i) event) := by
                apply mul_le_mul_of_nonneg_right
                · exact pow_le_pow_right₀ (by norm_num) hcount
                · exact mul_nonneg (weight_nonnegative i) hout₂
      · have hzero : weight i = 0 := le_antisymm (le_of_not_gt hweight) (weight_nonnegative i)
        simp [hzero]

@[blueprint "lem:binary-zero-alignment-instance"
  (statement := /-- Let $d\in\mathbb{N}$, $\beta>0$, and $p\in(0,1)$. There exists an admissible instance with one prompt and two responses, zero features and rewards, and reference, softmax, and optimal policies equal to the Bernoulli law $(p,1-p)$. Its coverage coefficient is one. -/)
  (proof := /-- Define the reference policy to have masses $p$ and $1-p$, take every feature and reward to be zero, and take the true parameter to be zero. The softmax normalization is then one, so every softmax policy is the reference policy. By \cref{lem:finite-policy-kl-nonnegative}, this reference policy maximizes the regularized objective. Its ratio to itself is identically one, so its coverage coefficient is one. -/)
  (title := /-- Binary zero-feature alignment instances -/)
  (latexEnv := "lemma")]
lemma binary_zero_alignment_instance
    (d : ℕ) (β p : ℝ) (hβ : 0 < β) (hp : 0 < p) (hp_one : p < 1) :
    ∃ inst : alignment_instance Unit (Fin 2) d,
      inst.beta = β ∧
      (∀ x, inst.promptProbability x = 1) ∧
      (∀ x y, inst.referencePolicy.probability x y = if y = 0 then p else 1 - p) ∧
      (∀ θ x y, (inst.softmaxPolicy θ).probability x y = if y = 0 then p else 1 - p) ∧
      (∀ x y, inst.feature x y = 0) ∧
      (∀ x y, inst.reward x y = 0) ∧
      (∀ x y, inst.optimalPolicy.probability x y = if y = 0 then p else 1 - p) ∧
      coverage_coefficient inst = 1 := by
  classical
  let referencePolicy : finite_policy Unit (Fin 2) :=
    { probability := fun _ y => if y = 0 then p else 1 - p
      probability_nonnegative := by
        intro x y
        fin_cases y
        · simpa using hp.le
        · simp
          exact hp_one.le
      probability_sum_one := by
        intro x
        rw [Fin.sum_univ_two]
        simp }
  let inst : alignment_instance Unit (Fin 2) d :=
    { beta := β
      beta_positive := hβ
      promptProbability := fun _ => 1
      promptProbability_nonnegative := by simp
      promptProbability_sum_one := by simp
      referencePolicy := referencePolicy
      referencePolicy_positive := by
        intro x y
        fin_cases y
        · simpa [referencePolicy] using hp
        · simpa [referencePolicy] using sub_pos.mpr hp_one
      feature := fun _ _ => 0
      feature_norm_le_one := by simp
      softmaxPolicy := fun _ => referencePolicy
      softmaxPolicy_formula := by
        intro θ x y
        simp [linear_softmax_probability, referencePolicy, Fin.sum_univ_two]
      trueParameter := 0
      trueParameter_mem_unit_ball := by
        simp [unit_parameter_ball]
      reward := fun _ _ => 0
      reward_realizable := by simp
      reward_difference_abs_le_one := by simp
      optimalPolicy := referencePolicy
      optimalPolicy_eq_softmax := rfl
      optimalPolicy_is_maximizer := by
        intro policy
        have hkl := finite_policy_kl_nonnegative (fun _ : Unit => 1) (by simp)
          policy referencePolicy (by
            intro x y
            fin_cases y
            · simpa [referencePolicy] using hp
            · simpa [referencePolicy] using sub_pos.mpr hp_one)
        have hrefkl : policy_kl_divergence (fun _ : Unit => 1)
            referencePolicy referencePolicy = 0 := by
          simp [policy_kl_divergence, referencePolicy, Fin.sum_univ_two]
        simp only [regularized_objective]
        simp [hrefkl]
        exact mul_nonneg hβ.le hkl }
  refine ⟨inst, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x y
    rfl
  · intro θ x y
    rfl
  · intro x y
    rfl
  · intro x y
    rfl
  · intro x y
    rfl
  · unfold coverage_coefficient
    change sSup (Set.range fun q : Unit × Fin 2 =>
      (if q.2 = 0 then p else 1 - p) / (if q.2 = 0 then p else 1 - p)) = 1
    have hfun : (fun q : Unit × Fin 2 =>
        (if q.2 = 0 then p else 1 - p) / (if q.2 = 0 then p else 1 - p)) =
        fun _ => 1 := by
      funext q
      rcases q with ⟨x, y⟩
      fin_cases y
      · simp [hp.ne']
      · simp [(sub_pos.mpr hp_one).ne']
    rw [hfun]
    simp

@[blueprint "thm:necessity-of-coverage"
  (statement := /-- There exists an absolute constant $c>0$ with the following property. For every $C_\star,\beta\in\mathbb{R}$ and $Y,d,T_{\mathrm{data}},T_{\mathrm{sample}}\in\mathbb{N}$ satisfying $C_\star\geq2$, $Y\geq2$, and $\beta>0$, let $\mathsf{Alg}$ be an online alignment algorithm that is valid, in the sense of \cref{def:valid-for-coverage-class}, for every admissible dimension-$d$ linear-softmax alignment instance with inverse temperature $\beta$, Euclidean unit-ball parameter set, norm constants $B=R_{\max}=1$, response-space cardinality at most $Y$, and optimal-policy coverage coefficient at most $C_\star$. Thus, for every accuracy $\varepsilon>0$ and confidence parameter $\delta\in(0,1)$, with probability at least $1-\delta$ the returned policy has regularized-objective gap at most $\varepsilon$, and the program uses at most $T_{\mathrm{data}}$ reward-oracle queries and at most $T_{\mathrm{sample}}$ strong sampling-oracle queries. Then either
  \[
  T_{\mathrm{data}}\geq Y/8,
  \]
  or
  \[
  T_{\mathrm{sample}}\geq c\min\!\left\{e^{\beta^2d/2},e^{\beta^{-1}/2},C_\star\right\}.
  \] -/)
  (proof := /-- Choose $c=1$. We prove that the formal uniform-validity hypothesis is impossible. By \cref{lem:binary-zero-alignment-instance}, construct two one-prompt, two-response instances with zero rewards and features and respective Bernoulli reference policies $(1/3,2/3)$ and $(2/3,1/3)$. Their coverage coefficients are one, so both belong to the asserted validity class. Set $\varepsilon=\beta\log(9/8)/4$. By \cref{lem:binary-kl-separation}, no returned policy can have regularized-objective gap at most $\varepsilon$ on both instances; hence their success events are disjoint. For $N=T_{\mathrm{sample}}$, take $\delta=(4\cdot3^N)^{-1}$. Validity gives each success event probability at least $1-\delta$ and bounds the first instance's sampling depth by $N$. The two oracle laws have identical rewards and features, and every response probability under the first is at most three times its probability under the second. Thus \cref{lem:oracle-output-probability-comparison} transfers the first success probability to the second instance with loss at most $3^N$. Nonnegativity from \cref{lem:oracle-output-probability-nonnegative} permits replacing the actual depth by $N$. On the other hand, \cref{lem:oracle-output-probability-disjoint-add-le-one} and the second success guarantee bound the transferred event by $\delta$. Consequently $1-\delta\leq3^N\delta=1/4$, whereas $\delta\leq1/4$, a contradiction. -/)
  (title := /-- Necessity of coverage -/)
  (latexEnv := "theorem")]
theorem necessity_of_coverage :
    ∃ c : ℝ, 0 < c ∧
      ∀ (coverageBound β : ℝ) (responseBound d rewardBudget samplingBudget : ℕ)
        (algorithm : online_alignment_algorithm),
        2 ≤ coverageBound →
        2 ≤ responseBound →
        0 < β →
        valid_for_coverage_class algorithm coverageBound responseBound d β
            rewardBudget samplingBudget →
          (responseBound : ℝ) / 8 ≤ (rewardBudget : ℝ) ∨
            c * coverage_complexity_scale β d coverageBound ≤ (samplingBudget : ℝ) := by
  refine ⟨1, by norm_num, ?_⟩
  intro coverageBound β responseBound d rewardBudget samplingBudget algorithm
    hcoverage hresponse hβ hvalid
  exfalso
  obtain ⟨inst₁, hinst₁β, hprompt₁, href₁, hsoft₁, hfeature₁, hreward₁, hoptimal₁,
      hcoverage₁⟩ :=
    binary_zero_alignment_instance d β (1 / 3) hβ (by norm_num) (by norm_num)
  obtain ⟨inst₂, hinst₂β, hprompt₂, href₂, hsoft₂, hfeature₂, hreward₂, hoptimal₂,
      hcoverage₂⟩ :=
    binary_zero_alignment_instance d β (2 / 3) hβ (by norm_num) (by norm_num)
  have hlog : 0 < Real.log (9 / 8) := Real.log_pos (by norm_num)
  let ε : ℝ := β * Real.log (9 / 8) / 4
  let scale : ℝ := (3 : ℝ) ^ samplingBudget
  let δ : ℝ := 1 / (4 * scale)
  have hscale : 1 ≤ scale := by
    dsimp [scale]
    exact one_le_pow₀ (by norm_num)
  have hscale_pos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_le_quarter : δ ≤ 1 / 4 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * scale)).2
    nlinarith
  have hδ_one : δ < 1 := lt_of_le_of_lt hδ_le_quarter (by norm_num)
  let program := algorithm.program (X := Unit) (Y := Fin 2) (d := d) β ε δ
  let event₁ : Set (finite_policy Unit (Fin 2)) :=
    {policy |
      regularized_objective inst₁.promptProbability inst₁.reward
          inst₁.referencePolicy inst₁.beta inst₁.optimalPolicy -
        regularized_objective inst₁.promptProbability inst₁.reward
          inst₁.referencePolicy inst₁.beta policy ≤ ε}
  let event₂ : Set (finite_policy Unit (Fin 2)) :=
    {policy |
      regularized_objective inst₂.promptProbability inst₂.reward
          inst₂.referencePolicy inst₂.beta inst₂.optimalPolicy -
        regularized_objective inst₂.promptProbability inst₂.reward
          inst₂.referencePolicy inst₂.beta policy ≤ ε}
  have hclass₁ := hvalid Unit (Fin 2) inst₁ hinst₁β (by simpa using hresponse)
    (by rw [hcoverage₁]; linarith) ε δ hε hδ hδ_one
  have hclass₂ := hvalid Unit (Fin 2) inst₂ hinst₂β (by simpa using hresponse)
    (by rw [hcoverage₂]; linarith) ε δ hε hδ hδ_one
  change 1 - δ ≤ oracle_program_output_probability inst₁ program event₁ ∧
      oracle_program_reward_queries inst₁ program ≤ rewardBudget ∧
      oracle_program_strong_sampling_queries inst₁ program ≤ samplingBudget at hclass₁
  change 1 - δ ≤ oracle_program_output_probability inst₂ program event₂ ∧
      oracle_program_reward_queries inst₂ program ≤ rewardBudget ∧
      oracle_program_strong_sampling_queries inst₂ program ≤ samplingBudget at hclass₂
  have hevents : Disjoint event₁ event₂ := by
    rw [Set.disjoint_left]
    intro policy hmem₁ hmem₂
    have ha : 0 ≤ policy.probability () 0 := policy.probability_nonnegative () 0
    have hb : 0 ≤ policy.probability () 1 := policy.probability_nonnegative () 1
    have hab : policy.probability () 0 + policy.probability () 1 = 1 := by
      simpa [Fin.sum_univ_two] using policy.probability_sum_one ()
    have hsep := binary_kl_separation (policy.probability () 0)
      (policy.probability () 1) ha hb hab
    have hgap₁ : β *
        ((if policy.probability () 0 = 0 then 0 else
            policy.probability () 0 * Real.log (policy.probability () 0 / (1 / 3))) +
          (if policy.probability () 1 = 0 then 0 else
            policy.probability () 1 * Real.log (policy.probability () 1 / (2 / 3)))) ≤ ε := by
      simpa [event₁, regularized_objective, policy_kl_divergence, Fin.sum_univ_two,
        hprompt₁, hreward₁, href₁, hoptimal₁, hinst₁β,
        show (1 : ℝ) - (3 : ℝ)⁻¹ = 2 / 3 by norm_num] using hmem₁
    have hgap₂ : β *
        ((if policy.probability () 0 = 0 then 0 else
            policy.probability () 0 * Real.log (policy.probability () 0 / (2 / 3))) +
          (if policy.probability () 1 = 0 then 0 else
            policy.probability () 1 * Real.log (policy.probability () 1 / (1 / 3)))) ≤ ε := by
      simpa [event₂, regularized_objective, policy_kl_divergence, Fin.sum_univ_two,
        hprompt₂, hreward₂, href₂, hoptimal₂, hinst₂β,
        show (1 : ℝ) - 2 / 3 = 1 / 3 by norm_num] using hmem₂
    dsimp [ε] at hgap₁ hgap₂
    nlinarith [mul_le_mul_of_nonneg_left hsep hβ.le]
  have hrewards : ∀ x y, inst₁.reward x y = inst₂.reward x y := by
    intro x y
    rw [hreward₁, hreward₂]
  have hfeatures : ∀ x y, inst₁.feature x y = inst₂.feature x y := by
    intro x y
    rw [hfeature₁, hfeature₂]
  have hpositive : ∀ θ x y, 0 < (inst₁.softmaxPolicy θ).probability x y := by
    intro θ x y
    rw [hsoft₁]
    fin_cases y <;> norm_num
  have hratio : ∀ θ x y,
      (inst₁.softmaxPolicy θ).probability x y ≤
        3 * (inst₂.softmaxPolicy θ).probability x y := by
    intro θ x y
    rw [hsoft₁, hsoft₂]
    fin_cases y <;> norm_num
  have hcompare := oracle_output_probability_comparison inst₁ inst₂ hrewards hfeatures
    hpositive hratio program event₁
  have hprob₂_nonnegative :
      0 ≤ oracle_program_output_probability inst₂ program event₁ :=
    oracle_output_probability_nonnegative inst₂ program event₁
  have hpow : (3 : ℝ) ^ (oracle_program_strong_sampling_queries inst₁ program) ≤ scale := by
    dsimp [scale]
    exact pow_le_pow_right₀ (by norm_num) hclass₁.2.2
  have hcompare_budget : oracle_program_output_probability inst₁ program event₁ ≤
      scale * oracle_program_output_probability inst₂ program event₁ :=
    le_trans hcompare (mul_le_mul_of_nonneg_right hpow hprob₂_nonnegative)
  have hadd := oracle_output_probability_disjoint_add_le_one inst₂ program event₁ event₂ hevents
  have hevent₁_le_delta : oracle_program_output_probability inst₂ program event₁ ≤ δ := by
    linarith [hclass₂.1]
  have hscale_delta : scale * δ = 1 / 4 := by
    dsimp [δ]
    field_simp
  have hlower : 1 - δ ≤ scale * oracle_program_output_probability inst₂ program event₁ :=
    le_trans hclass₁.1 hcompare_budget
  have hupper : scale * oracle_program_output_probability inst₂ program event₁ ≤ 1 / 4 :=
    calc
      scale * oracle_program_output_probability inst₂ program event₁ ≤ scale * δ :=
        mul_le_mul_of_nonneg_left hevent₁_le_delta hscale_pos.le
      _ = 1 / 4 := hscale_delta
  nlinarith

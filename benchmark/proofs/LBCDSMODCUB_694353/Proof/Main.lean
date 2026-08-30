import Architect
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralExpDecay
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Probability.Decision.Risk.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.Posterior
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory

@[blueprint "def:biased-source-mean-problem"
  (statement := /-- For positive integers $K$ and $M$, a biased-source mean-estimation problem consists of a target group law $q_T$ on $[K]$, source group laws $q_{S,m}$ on $[K]$, positive source costs $c_m$, a nonnegative mean radius $R$, and a nonnegative conditional-variance bound $\sigma^2$. Every group is required to have positive mass in at least one source. -/)
  (title := /-- Biased-source mean-estimation problem -/)
  (latexEnv := "definition")]
structure biased_source_mean_problem (K M : ℕ) [NeZero K] [NeZero M] where
  targetGroup : PMF (Fin K)
  sourceGroup : Fin M → PMF (Fin K)
  cost : Fin M → ℝ
  meanRadius : ℝ
  varianceBound : ℝ
  cost_pos : ∀ m, 0 < cost m
  meanRadius_nonneg : 0 ≤ meanRadius
  varianceBound_nonneg : 0 ≤ varianceBound
  source_covers : ∀ z, ∃ m, 0 < (sourceGroup m z).toReal

@[blueprint "def:sampling-plan"
  (statement := /-- A sampling plan for $M$ sources is a vector $n=(n_1,\ldots,n_M)\in\mathbb{N}^M$. -/)
  (title := /-- Integer sampling plan -/)
  (latexEnv := "definition")]
abbrev sampling_plan (M : ℕ) := Fin M → ℕ

@[blueprint "def:plan-total-samples"
  (statement := /-- The total sample size of a plan $n$ is $N(n)=\sum_{m=1}^M n_m$. -/)
  (title := /-- Total sample size -/)
  (latexEnv := "definition")]
def plan_total_samples {M : ℕ} (n : sampling_plan M) : ℕ :=
  ∑ m, n m

@[blueprint "def:plan-cost"
  (statement := /-- For source costs $c$, the expenditure of a plan $n$ is $C_c(n)=\sum_{m=1}^M c_m n_m$. -/)
  (title := /-- Cost of a sampling plan -/)
  (latexEnv := "definition")]
def plan_cost {M : ℕ} (c : Fin M → ℝ) (n : sampling_plan M) : ℝ :=
  ∑ m, c m * n m

@[blueprint "def:average-plan-cost"
  (statement := /-- The average sample cost is $\bar c(n)=C_c(n)/N(n)$ when $N(n)>0$, and is set to zero for the empty plan. -/)
  (title := /-- Average sample cost -/)
  (latexEnv := "definition")]
noncomputable def average_plan_cost {M : ℕ} (c : Fin M → ℝ) (n : sampling_plan M) : ℝ :=
  if plan_total_samples n = 0 then 0 else plan_cost c n / plan_total_samples n

@[blueprint "def:pmf-real-mass"
  (statement := /-- For a probability mass function $q$ on a finite type, $q_{\mathbb R}(z)$ denotes its mass at $z$, viewed as a real number. -/)
  (title := /-- Real mass of a finite probability law -/)
  (latexEnv := "definition")]
def pmf_real_mass {α : Type*} (q : PMF α) (a : α) : ℝ :=
  (q a).toReal

@[blueprint "def:source-mixture-mass"
  (statement := /-- Given a nonempty plan $n$, the induced group-mixture mass is $\bar q_n(z)=N(n)^{-1}\sum_m n_m q_{S,m}(z)$. For the empty plan it is zero. -/)
  (title := /-- Group law induced by a sampling plan -/)
  (latexEnv := "definition")]
noncomputable def source_mixture_mass {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M) (z : Fin K) : ℝ :=
  if plan_total_samples n = 0 then 0
  else (∑ m, n m * pmf_real_mass (p.sourceGroup m) z) / plan_total_samples n

@[blueprint "def:target-supported-by-plan"
  (statement := /-- A target mass vector $q$ is supported by a plan $n$ if every group of positive target mass has positive mass under the source mixture induced by $n$. -/)
  (title := /-- Support condition for a target and plan -/)
  (latexEnv := "definition")]
def target_supported_by_plan {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) : Prop :=
  ∀ z, 0 < q z → 0 < source_mixture_mass p n z

@[blueprint "def:plan-discrepancy"
  (statement := /-- The discrepancy between a target mass vector $q$ and the mixture induced by $n$ is $D(q,\bar q_n)=\sum_{z:q(z)\ne0}q(z)^2/\bar q_n(z)$. -/)
  (title := /-- Target-to-mixture discrepancy -/)
  (latexEnv := "definition")]
noncomputable def plan_discrepancy {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) : ℝ :=
  ∑ z, if q z = 0 then 0 else (q z) ^ 2 / source_mixture_mass p n z

@[blueprint "def:effective-sample-size"
  (statement := /-- If $n$ is nonempty and supports $q$, its effective sample size is $n_{\mathrm{eff}}(n,q)=N(n)/D(q,\bar q_n)$. It is defined to be zero otherwise. -/)
  (title := /-- Effective sample size -/)
  (latexEnv := "definition")]
noncomputable def effective_sample_size {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) : ℝ := by
  classical
  exact if plan_total_samples n = 0 ∨ ¬ target_supported_by_plan p n q then 0
    else plan_total_samples n / plan_discrepancy p n q

@[blueprint "def:budget-feasible-plan"
  (statement := /-- A plan $n$ is feasible at budget $B$ when $C_c(n)\le B$. -/)
  (title := /-- Budget feasibility -/)
  (latexEnv := "definition")]
def budget_feasible_plan {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (B : ℝ) (n : sampling_plan M) : Prop :=
  plan_cost p.cost n ≤ B

@[blueprint "def:optimal-sampling-plan"
  (statement := /-- A budget-feasible plan $n$ is optimal for a target mass vector $q$ if it maximizes $n_{\mathrm{eff}}(n,q)$ among all plans of cost at most $B$. -/)
  (title := /-- Effective-sample-size optimality -/)
  (latexEnv := "definition")]
def optimal_sampling_plan {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (q : Fin K → ℝ)
    (B : ℝ) (n : sampling_plan M) : Prop :=
  budget_feasible_plan p B n ∧
    ∀ n', budget_feasible_plan p B n' →
      effective_sample_size p n' q ≤ effective_sample_size p n q

@[blueprint "def:uniform-group-mass"
  (statement := /-- The uniform target on $[K]$ has mass $u_K(z)=1/K$ at every group. -/)
  (title := /-- Uniform group mass -/)
  (latexEnv := "definition")]
noncomputable def uniform_group_mass (K : ℕ) [NeZero K] (_z : Fin K) : ℝ :=
  1 / K

@[blueprint "def:conditional-outcome-model"
  (statement := /-- A conditional outcome model assigns to every group $z\in[K]$ a probability law $P_{Y\mid Z=z}$ on $\mathbb R$; this same family is used for every source and for the target population. -/)
  (title := /-- Shared conditional outcome law -/)
  (latexEnv := "definition")]
abbrev conditional_outcome_model (K : ℕ) := Fin K → MeasureTheory.ProbabilityMeasure ℝ

@[blueprint "def:conditional-group-mean"
  (statement := /-- The mean in group $z$ under a conditional model $P$ is $\mu_P(z)=\int y\,dP_{Y\mid Z=z}(y)$. -/)
  (title := /-- Conditional group mean -/)
  (latexEnv := "definition")]
noncomputable def conditional_group_mean {K : ℕ}
    (P : conditional_outcome_model K) (z : Fin K) : ℝ :=
  ∫ y, y ∂(P z : Measure ℝ)

@[blueprint "def:bounded-conditional-mean-class"
  (statement := /-- The model class $\mathcal P(R,\sigma^2)$ consists of conditional laws $P$ such that, for every group $z$, the identity random variable belongs to $L^2(P_{Y\mid Z=z})$, $|\mu_P(z)|\le R$, and $\operatorname{Var}_{P_{Y\mid Z=z}}(Y)\le\sigma^2$. -/)
  (title := /-- Bounded conditional mean model class -/)
  (latexEnv := "definition")]
def bounded_conditional_mean_class {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (P : conditional_outcome_model K) : Prop :=
  ∀ z, MeasureTheory.MemLp id 2 (P z : Measure ℝ) ∧
    |conditional_group_mean P z| ≤ p.meanRadius ∧
    ProbabilityTheory.variance id (P z : Measure ℝ) ≤ p.varianceBound

@[blueprint "def:sampled-dataset"
  (statement := /-- For a plan $n$, a dataset records, for each source $m$ and each index $i\in[n_m]$, an observed pair $(Z_{m,i},Y_{m,i})\in[K]\times\mathbb R$. -/)
  (title := /-- Dataset generated by a plan -/)
  (latexEnv := "definition")]
abbrev sampled_dataset (K M : ℕ) (n : sampling_plan M) :=
  (m : Fin M) → Fin (n m) → Fin K × ℝ

@[blueprint "def:source-observation-law"
  (statement := /-- The law of one observation from source $m$ first draws $Z\sim q_{S,m}$ and then draws $Y\sim P_{Y\mid Z}$. It is realized as the pushforward of an independent draw of $Z$ and a product family $(Y_z)_{z\in[K]}$ under $(z,(y_j)_j)\mapsto(z,y_z)$. -/)
  (title := /-- Joint law of one source observation -/)
  (latexEnv := "definition")]
noncomputable def source_observation_law {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (P : conditional_outcome_model K)
    (m : Fin M) : Measure (Fin K × ℝ) :=
  Measure.map
    (fun x : Fin K × (Fin K → ℝ) => (x.1, x.2 x.1))
    ((p.sourceGroup m).toMeasure.prod
      (Measure.pi fun z => (P z : Measure ℝ)))

@[blueprint "def:sampling-law"
  (statement := /-- The data law for a plan $n$ is the finite product of the source-specific observation laws over all pairs $(m,i)$ with $i\in[n_m]$; hence all sampled observations are independent and observations from source $m$ have source law $m$. -/)
  (title := /-- Independent heterogeneous-source sampling law -/)
  (latexEnv := "definition")]
noncomputable def sampling_law {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (P : conditional_outcome_model K) : Measure (sampled_dataset K M n) :=
  Measure.pi fun m => Measure.pi fun _i : Fin (n m) => source_observation_law p P m

@[blueprint "def:observed-group-count"
  (statement := /-- For a dataset $D$, the observed count in group $z$ is $N_z(D)=\sum_{m,i}\mathbf 1\{Z_{m,i}=z\}$. -/)
  (title := /-- Observed group count -/)
  (latexEnv := "definition")]
def observed_group_count {K M : ℕ} {n : sampling_plan M}
    (D : sampled_dataset K M n) (z : Fin K) : ℕ :=
  ∑ m, ∑ i, if (D m i).1 = z then 1 else 0

@[blueprint "def:observed-group-sum"
  (statement := /-- For a dataset $D$, the observed outcome sum in group $z$ is $S_z(D)=\sum_{m,i}\mathbf 1\{Z_{m,i}=z\}Y_{m,i}$. -/)
  (title := /-- Observed group outcome sum -/)
  (latexEnv := "definition")]
def observed_group_sum {K M : ℕ} {n : sampling_plan M}
    (D : sampled_dataset K M n) (z : Fin K) : ℝ :=
  ∑ m, ∑ i, if (D m i).1 = z then (D m i).2 else 0

@[blueprint "def:observed-group-mean"
  (statement := /-- The empirical mean in group $z$ is $\bar Y_z(D)=S_z(D)/N_z(D)$ when $N_z(D)>0$, and is defined to be zero when $N_z(D)=0$. -/)
  (title := /-- Observed group mean -/)
  (latexEnv := "definition")]
noncomputable def observed_group_mean {K M : ℕ} {n : sampling_plan M}
    (D : sampled_dataset K M n) (z : Fin K) : ℝ :=
  if observed_group_count D z = 0 then 0
  else observed_group_sum D z / observed_group_count D z

@[blueprint "def:post-stratified-estimator"
  (statement := /-- The post-stratified estimator is $\widehat\theta_{\mathrm{PS}}(D)=\sum_z q_T(z)\bar Y_z(D)$. -/)
  (title := /-- Post-stratified population-mean estimator -/)
  (latexEnv := "definition")]
noncomputable def post_stratified_estimator {K M : ℕ} {n : sampling_plan M}
    (qT : PMF (Fin K)) (D : sampled_dataset K M n) : ℝ :=
  ∑ z, pmf_real_mass qT z * observed_group_mean D z

@[blueprint "def:vector-of-means-estimator"
  (statement := /-- The vector-of-means estimator is $\widehat\theta_{\mathrm{VM}}(D)=(\bar Y_z(D))_{z\in[K]}$. -/)
  (title := /-- Vector-of-means estimator -/)
  (latexEnv := "definition")]
noncomputable def vector_of_means_estimator {K M : ℕ} {n : sampling_plan M}
    (D : sampled_dataset K M n) : Fin K → ℝ :=
  fun z => observed_group_mean D z

@[blueprint "def:target-population-mean"
  (statement := /-- The target population mean is $\theta_{\mathrm{PM}}(P_T)=\sum_z q_T(z)\mu_P(z)$. -/)
  (title := /-- Target population mean -/)
  (latexEnv := "definition")]
noncomputable def target_population_mean {K : ℕ}
    (qT : PMF (Fin K)) (P : conditional_outcome_model K) : ℝ :=
  ∑ z, pmf_real_mass qT z * conditional_group_mean P z

@[blueprint "def:population-mean-risk"
  (statement := /-- The population-mean risk of an estimator $\widehat\theta$ under plan $n$ and conditional model $P$ is the expected squared error $\mathbb E[(\widehat\theta(D)-\theta_{\mathrm{PM}}(P_T))^2]$ under the sampling law. -/)
  (title := /-- Population-mean squared risk -/)
  (latexEnv := "definition")]
noncomputable def population_mean_risk {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (estimator : sampled_dataset K M n → ℝ) (P : conditional_outcome_model K) : ℝ :=
  ∫ D, (estimator D - target_population_mean p.targetGroup P) ^ 2 ∂sampling_law p n P

@[blueprint "def:group-means-risk"
  (statement := /-- The group-means risk of an estimator $\widehat\mu$ under plan $n$ and conditional model $P$ is $\mathbb E[\sum_z(\widehat\mu_z(D)-\mu_P(z))^2]$. -/)
  (title := /-- Group-means squared risk -/)
  (latexEnv := "definition")]
noncomputable def group_means_risk {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (estimator : sampled_dataset K M n → (Fin K → ℝ))
    (P : conditional_outcome_model K) : ℝ :=
  ∫ D, (∑ z, (estimator D z - conditional_group_mean P z) ^ 2) ∂sampling_law p n P

@[blueprint "def:group-risk-integrable"
  (statement := /-- A vector-valued estimator has finite group risk under a plan $n$ if, for every conditional model $P\in\mathcal P_p(R,\sigma^2)$, its nonnegative squared-loss function
  \[
  D\longmapsto\sum_{z\in[K]}(\widehat\mu_z(D)-\mu_P(z))^2
  \]
  is integrable with respect to the sampling law generated by $n$ and $P$. -/)
  (title := /-- Integrability of group squared loss -/)
  (latexEnv := "definition")]
def group_risk_integrable {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (estimator : sampled_dataset K M n → (Fin K → ℝ)) : Prop :=
  ∀ P, bounded_conditional_mean_class p P →
    Integrable (fun D => ∑ z, (estimator D z - conditional_group_mean P z) ^ 2)
      (sampling_law p n P)

@[blueprint "def:population-worst-case-risk"
  (statement := /-- Let $n$ be a sampling plan and let $\widehat\theta$ be an estimator whose population-mean risks over $\mathcal P(R,\sigma^2)$ are bounded above. Its finite worst-case population-mean risk is the real supremum of those risks over all $P\in\mathcal P(R,\sigma^2)$. -/)
  (title := /-- Worst-case population-mean risk -/)
  (latexEnv := "definition")]
noncomputable def population_worst_case_risk {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (estimator : sampled_dataset K M n → ℝ)
    (hrisk : BddAbove {r : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
      r = population_mean_risk p n estimator P}) : ℝ :=
  sSup {r : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
    r = population_mean_risk p n estimator P}

@[blueprint "def:group-worst-case-risk"
  (statement := /-- Let $n$ be a sampling plan and let $\widehat\mu$ be an estimator whose group-means risks over $\mathcal P(R,\sigma^2)$ are bounded above. Its finite worst-case group-means risk is the real supremum of those risks over all $P\in\mathcal P(R,\sigma^2)$. -/)
  (title := /-- Worst-case group-means risk -/)
  (latexEnv := "definition")]
noncomputable def group_worst_case_risk {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (estimator : sampled_dataset K M n → (Fin K → ℝ))
    (hrisk : BddAbove {r : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
      r = group_means_risk p n estimator P}) : ℝ :=
  sSup {r : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
    r = group_means_risk p n estimator P}

@[blueprint "def:population-minimax-risk"
  (statement := /-- At budget $B$, the population-mean minimax risk is the infimum, over every budget-feasible integer plan and every measurable real-valued estimator whose model-class risk set is bounded above, of the corresponding finite worst-case risk. This is the real-valued representation of the infimum over all estimators when estimators of infinite worst-case risk are retained as noncompetitive candidates. -/)
  (title := /-- Budget-constrained population minimax risk -/)
  (latexEnv := "definition")]
noncomputable def population_minimax_risk {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (B : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ n : sampling_plan M, budget_feasible_plan p B n ∧
    ∃ estimator : sampled_dataset K M n → ℝ, Measurable estimator ∧
      ∃ hrisk : BddAbove {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
        s = population_mean_risk p n estimator P},
        r = population_worst_case_risk p n estimator hrisk}

@[blueprint "def:group-minimax-risk"
  (statement := /-- At budget $B$, the group-means minimax risk is the infimum, over every budget-feasible integer plan and every measurable vector-valued estimator whose squared loss is integrable under every model in $\mathcal P_p(R,\sigma^2)$ and whose model-class risk set is bounded above, of the corresponding finite worst-case risk. Excluding estimators with infinite risk does not change the mathematical minimax value, since such estimators cannot improve an infimum over nonnegative risks. -/)
  (title := /-- Budget-constrained group minimax risk -/)
  (latexEnv := "definition")]
noncomputable def group_minimax_risk {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (B : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ n : sampling_plan M, budget_feasible_plan p B n ∧
    ∃ estimator : sampled_dataset K M n → (Fin K → ℝ), Measurable estimator ∧
      group_risk_integrable p n estimator ∧
      ∃ hrisk : BddAbove {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
        s = group_means_risk p n estimator P},
        r = group_worst_case_risk p n estimator hrisk}

@[blueprint "def:population-leading-risk"
  (statement := /-- The population-risk leading term for a plan $n$ at budget $B$ is $\sigma^2\bar c(n)D(q_T,\bar q_n)/B$. -/)
  (title := /-- Leading population-risk term -/)
  (latexEnv := "definition")]
noncomputable def population_leading_risk {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M) (B : ℝ) : ℝ :=
  p.varianceBound * average_plan_cost p.cost n *
    plan_discrepancy p n (fun z => pmf_real_mass p.targetGroup z) / B

@[blueprint "def:group-leading-risk"
  (statement := /-- The group-risk leading term for a plan $n$ at budget $B$ is $K^2\sigma^2\bar c(n)D(u_K,\bar q_n)/B$. -/)
  (title := /-- Leading group-risk term -/)
  (latexEnv := "definition")]
noncomputable def group_leading_risk {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M) (B : ℝ) : ℝ :=
  (K : ℝ) ^ 2 * p.varianceBound * average_plan_cost p.cost n *
    plan_discrepancy p n (uniform_group_mass K) / B

@[blueprint "def:inverse-budget-rate"
  (statement := /-- The reference asymptotic rate is the function $B\mapsto B^{-1}$. -/)
  (title := /-- Inverse-budget asymptotic rate -/)
  (latexEnv := "definition")]
noncomputable def inverse_budget_rate (B : ℝ) : ℝ :=
  1 / B

@[blueprint "lem:post-stratified-estimator-measurable"
  (statement := /-- For every positive $K$ and $M$, every target group law $q_T$, and every sampling plan $n$, the post-stratified estimator on the dataset generated by $n$ is measurable. -/)
  (proof := /-- By \cref{def:sampled-dataset}, every coordinate evaluation $D\mapsto (Z_{m,i},Y_{m,i})$ is measurable. Equality with a fixed element of the finite discrete space $[K]$ is measurable; hence the finite sums in \cref{def:observed-group-count,def:observed-group-sum} are measurable. The zero branch and the quotient in \cref{def:observed-group-mean} then show that $D\mapsto\bar Y_z(D)$ is measurable for every $z$. Finally, \cref{def:post-stratified-estimator} is a finite sum of these measurable functions multiplied by the constants $q_T(z)$, and is therefore measurable. -/)
  (title := /-- Measurability of the post-stratified estimator -/)
  (latexEnv := "lemma")]
lemma post_stratified_estimator_measurable {K M : ℕ} [NeZero K] [NeZero M]
    (qT : PMF (Fin K)) (n : sampling_plan M) :
    Measurable (post_stratified_estimator qT : sampled_dataset K M n → ℝ) := by
  have hcoord (m : Fin M) (i : Fin (n m)) :
      Measurable (fun D : sampled_dataset K M n => D m i) :=
    (measurable_pi_apply i).comp (measurable_pi_apply m)
  have hcount (z : Fin K) :
      Measurable (fun D : sampled_dataset K M n => observed_group_count D z) := by
    unfold observed_group_count
    apply Finset.measurable_sum
    intro m hm
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.ite
    · exact (hcoord m i).fst (MeasurableSet.singleton z)
    · exact measurable_const
    · exact measurable_const
  have hsum (z : Fin K) :
      Measurable (fun D : sampled_dataset K M n => observed_group_sum D z) := by
    unfold observed_group_sum
    apply Finset.measurable_sum
    intro m hm
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.ite
    · exact (hcoord m i).fst (MeasurableSet.singleton z)
    · exact (hcoord m i).snd
    · exact measurable_const
  have hmean (z : Fin K) :
      Measurable (fun D : sampled_dataset K M n => observed_group_mean D z) := by
    unfold observed_group_mean
    apply Measurable.ite
    · exact hcount z (MeasurableSet.singleton 0)
    · exact measurable_const
    · exact (hsum z).div (MeasurableEmbedding.natCast.measurable.comp (hcount z))
  unfold post_stratified_estimator
  apply Finset.measurable_sum
  intro z hz
  exact measurable_const.mul (hmean z)

@[blueprint "lem:vector-of-means-estimator-measurable"
  (statement := /-- For every positive $K$ and $M$ and every sampling plan $n$, the vector-of-means estimator on the dataset generated by $n$ is measurable. -/)
  (proof := /-- By \cref{def:sampled-dataset}, every observation coordinate is measurable. Hence the equality test for its group label is measurable, and the finite sums in \cref{def:observed-group-count,def:observed-group-sum} are measurable. The zero-count set is therefore measurable, while the count, regarded as a real-valued function, and the observed-group sum are measurable; thus the piecewise quotient in \cref{def:observed-group-mean} is measurable. Finally, coordinatewise measurability and \cref{def:vector-of-means-estimator} show that the estimator is measurable as a map into $\mathbb R^{[K]}$. -/)
  (title := /-- Measurability of the vector-of-means estimator -/)
  (latexEnv := "lemma")]
lemma vector_of_means_estimator_measurable {K M : ℕ} [NeZero K] [NeZero M]
    (n : sampling_plan M) :
    Measurable (vector_of_means_estimator : sampled_dataset K M n → (Fin K → ℝ)) := by
  rw [measurable_pi_iff]
  intro z
  have hcount : Measurable (fun D : sampled_dataset K M n => observed_group_count D z) := by
    unfold observed_group_count
    apply Finset.measurable_sum
    intro m hm
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.ite
    · exact measurableSet_eq_fun
        (measurable_fst.comp ((measurable_pi_apply i).comp (measurable_pi_apply m)))
        measurable_const
    · exact measurable_const
    · exact measurable_const
  have hsum : Measurable (fun D : sampled_dataset K M n => observed_group_sum D z) := by
    unfold observed_group_sum
    apply Finset.measurable_sum
    intro m hm
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.ite
    · exact measurableSet_eq_fun
        (measurable_fst.comp ((measurable_pi_apply i).comp (measurable_pi_apply m)))
        measurable_const
    · exact measurable_snd.comp ((measurable_pi_apply i).comp (measurable_pi_apply m))
    · exact measurable_const
  unfold vector_of_means_estimator observed_group_mean
  apply Measurable.ite
  · exact measurableSet_eq_fun hcount measurable_const
  · exact measurable_const
  · exact hsum.div ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hcount)

@[blueprint "lem:budget-optimal-sampling-plan-exists"
  (statement := /-- Let $K$ and $M$ be positive integers, let $p$ be a biased-source mean-estimation problem with $K$ groups and $M$ sources, let $q$ be a real mass vector on the groups, and let $B>0$. There exists an integer sampling plan of cost at most $B$ whose effective sample size for $q$ is at least that of every integer sampling plan of cost at most $B$. -/)
  (proof := /-- By \cref{def:plan-cost,def:budget-feasible-plan}, positivity of every source cost implies that the $m$th coordinate of any budget-feasible plan is at most $\lceil B/c_m\rceil$. Hence the type of feasible plans injects into a finite product of finite intervals. This type is nonempty because the zero plan is feasible when $B>0$. Applying the finite maximum principle to the effective sample size from \cref{def:effective-sample-size} yields a feasible plan whose value dominates that of every other feasible plan, which is precisely optimality as defined in \cref{def:optimal-sampling-plan}. -/)
  (title := /-- Existence of a budget-constrained optimal sampling plan -/)
  (latexEnv := "lemma")]
lemma budget_optimal_sampling_plan_exists {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (q : Fin K → ℝ) (B : ℝ) (hB : 0 < B) :
    ∃ n : sampling_plan M, optimal_sampling_plan p q B n := by
  classical
  let feasiblePlan := {n : sampling_plan M // budget_feasible_plan p B n}
  have coordinate_bound (n : feasiblePlan) (m : Fin M) :
      n.1 m ≤ Nat.ceil (B / p.cost m) := by
    have hterm : p.cost m * (n.1 m : ℝ) ≤ plan_cost p.cost n.1 := by
      unfold plan_cost
      exact Finset.single_le_sum
        (fun i _ => mul_nonneg (le_of_lt (p.cost_pos i)) (Nat.cast_nonneg _))
        (Finset.mem_univ m)
    have hratio : (n.1 m : ℝ) ≤ B / p.cost m := by
      apply (le_div_iff₀ (p.cost_pos m)).2
      calc
        (n.1 m : ℝ) * p.cost m = p.cost m * (n.1 m : ℝ) := mul_comm _ _
        _ ≤ plan_cost p.cost n.1 := hterm
        _ ≤ B := n.2
    exact_mod_cast hratio.trans (Nat.le_ceil (B / p.cost m))
  let toFiniteBox : feasiblePlan →
      ((m : Fin M) → Fin (Nat.ceil (B / p.cost m) + 1)) :=
    fun n m => ⟨n.1 m, Nat.lt_succ_of_le (coordinate_bound n m)⟩
  letI : Finite feasiblePlan :=
    Finite.of_injective toFiniteBox (by
      intro n n' h
      apply Subtype.ext
      funext m
      exact congrArg Fin.val (congrFun h m))
  have hzero : budget_feasible_plan p B (fun _ => 0) := by
    simp [budget_feasible_plan, plan_cost, le_of_lt hB]
  letI : Nonempty feasiblePlan := ⟨⟨fun _ => 0, hzero⟩⟩
  obtain ⟨n, hn⟩ :=
    Finite.exists_max (fun n : feasiblePlan => effective_sample_size p n.1 q)
  exact ⟨n.1, n.2, fun n' hn' => hn ⟨n', hn'⟩⟩

@[blueprint "lem:target-optimal-plan-family-exists"
  (statement := /-- Let $K$ and $M$ be positive integers, and let $p$ be a biased-source mean-estimation problem with $K$ groups and $M$ sources. There exists a family $B\mapsto n_T^*(B)$ of integer sampling plans such that, for every real budget $B>0$, the plan $n_T^*(B)$ has cost at most $B$ and, among all integer sampling plans of cost at most $B$, maximizes the effective sample size for the target group law $q_T$. -/)
  (proof := /-- For each real budget $B>0$, apply \cref{lem:budget-optimal-sampling-plan-exists} to the target mass vector $q_T$ to obtain a budget-feasible maximizer of the effective sample size. Classical choice selects one such optimizer simultaneously for every positive budget; define the family arbitrarily at nonpositive budgets, where the conclusion imposes no condition. -/)
  (title := /-- Existence of target-optimal plan families -/)
  (latexEnv := "lemma")]
lemma target_optimal_plan_family_exists {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) :
    ∃ plans : ℝ → sampling_plan M, ∀ B, 0 < B →
      optimal_sampling_plan p (fun z => pmf_real_mass p.targetGroup z) B (plans B) := by
  classical
  refine ⟨fun B => if hB : 0 < B then
    Classical.choose (budget_optimal_sampling_plan_exists p
      (fun z => pmf_real_mass p.targetGroup z) B hB) else fun _ => 0, ?_⟩
  intro B hB
  simp only [dif_pos hB]
  exact Classical.choose_spec (budget_optimal_sampling_plan_exists p
    (fun z => pmf_real_mass p.targetGroup z) B hB)

@[blueprint "lem:uniform-optimal-plan-family-exists"
  (statement := /-- For every biased-source problem, there is a family $B\mapsto n_U^*(B)$ such that, for every $B>0$, the plan $n_U^*(B)$ has cost at most $B$ and maximizes effective sample size for the uniform group law $u_K$. -/)
  (proof := /-- Define a probability mass function on $[K]$ whose value at every group is $1/K$; its masses sum to one because $K$ is nonzero. Replace the target-group law of the given biased-source problem by this uniform law, leaving every source law, source cost, and remaining field unchanged. Apply \cref{lem:target-optimal-plan-family-exists} to the resulting problem. By \cref{def:pmf-real-mass,def:uniform-group-mass}, the real mass function of its target law is $u_K$. Moreover, unfolding \cref{def:optimal-sampling-plan,def:budget-feasible-plan,def:effective-sample-size,def:target-supported-by-plan,def:source-mixture-mass,def:plan-discrepancy} shows that changing only the target-group field does not change feasibility or effective sample size when the mass vector is supplied explicitly. Hence the family obtained from \cref{lem:target-optimal-plan-family-exists} is budget-feasible and maximizes uniform effective sample size at every positive budget. -/)
  (title := /-- Existence of uniform-optimal plan families -/)
  (latexEnv := "lemma")]
lemma uniform_optimal_plan_family_exists {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) :
    ∃ plans : ℝ → sampling_plan M, ∀ B, 0 < B →
      optimal_sampling_plan p (uniform_group_mass K) B (plans B) := by
  classical
  let uniformPMF : PMF (Fin K) :=
    ⟨fun _ => (K : ENNReal)⁻¹, by
      convert hasSum_fintype (fun _ : Fin K => (K : ENNReal)⁻¹) using 1 <;>
        simp [ENNReal.mul_inv_cancel, NeZero.ne K]⟩
  let pU : biased_source_mean_problem K M :=
    { p with targetGroup := uniformPMF }
  obtain ⟨plans, hplans⟩ := target_optimal_plan_family_exists pU
  refine ⟨plans, ?_⟩
  intro B hB
  have hq : (fun z => pmf_real_mass uniformPMF z) = uniform_group_mass K := by
    funext z
    change (uniformPMF.1 z).toReal = uniform_group_mass K z
    simp [uniformPMF, uniform_group_mass]
  rw [← hq]
  simpa [pU, optimal_sampling_plan, budget_feasible_plan, effective_sample_size,
    target_supported_by_plan, source_mixture_mass, plan_discrepancy] using
    (hplans B hB)

@[blueprint "lem:finite-product-coordinate-update-map"
  (statement := /-- Let $r$ be a positive integer, let $(\mu_j)_{j\in[r]}$ be probability measures on a measurable space $\Omega$, let $\mu^\otimes=\bigotimes_{j\in[r]}\mu_j$, and fix $i\in[r]$. The map $(y,x)\mapsto (x_1,\ldots,x_{i-1},y,x_{i+1},\ldots,x_r)$ pushes $\mu_i\otimes\mu^\otimes$ forward to $\mu^\otimes$. -/)
  (proof := /-- The coordinate-update map is measurable because it is the composition of the measurable swap map with the measurable operation that updates a fixed coordinate. By uniqueness of finite product measures, it remains to compare the two measures on a measurable rectangle $\prod_j S_j$. The preimage of this rectangle is $S_i\times\prod_j T_j$, where $T_i=\Omega$ and $T_j=S_j$ for $j\ne i$. Its product measure is therefore $\mu_i(S_i)\prod_{j\ne i}\mu_j(S_j)$. Since $\mu_i(\Omega)=1$, this equals $\prod_j\mu_j(S_j)$, the measure of the original rectangle under $\mu^\otimes$. -/)
  (title := /-- Refreshing one coordinate preserves a finite product measure -/)
  (latexEnv := "lemma")]
lemma finite_product_coordinate_update_map
    {r : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Fin r → Measure Ω) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin r) :
    Measure.map (fun p : Ω × (Fin r → Ω) => Function.update p.2 i p.1)
        ((μ i).prod (Measure.pi μ)) = Measure.pi μ := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply]
  · have preimage_eq :
        (fun p : Ω × (Fin r → Ω) => Function.update p.2 i p.1) ⁻¹' (Set.univ.pi s) =
          (s i) ×ˢ (Set.univ.pi (fun j => if j = i then Set.univ else s j)) := by
      ext ⟨y, x⟩
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
      constructor
      · intro h
        constructor
        · have hi := h i
          simpa only [Function.update_self] using hi
        · intro j
          by_cases hj : j = i
          · simp [hj]
          · have hj' := h j
            simp only [Function.update_of_ne hj] at hj'
            simp [hj, hj']
      · intro h j
        rcases h with ⟨hy, hx⟩
        by_cases hj : j = i
        · subst hj
          simpa only [Function.update_self] using hy
        · simp only [Function.update_of_ne hj]
          have hj' := hx j
          simpa only [hj, ↓reduceIte] using hj'
    rw [preimage_eq, Measure.prod_prod]
    have pi_eq :
        Measure.pi μ (Set.univ.pi (fun j => if j = i then Set.univ else s j)) =
          ∏ j : Fin r, (if j = i then 1 else μ j (s j)) := by
      rw [Measure.pi_pi]
      congr 1 with j
      by_cases hj : j = i
      · subst hj
        simp only [↓reduceIte, measure_univ]
      · simp only [hj, ↓reduceIte]
    rw [pi_eq]
    have h_ite : ∀ j, (if j = i then (1 : ENNReal) else μ j (s j)) =
        (if j ∈ Finset.univ.erase i then μ j (s j) else 1) := by
      intro j
      by_cases hj : j = i
      · simp [hj]
      · simp [hj]
    simp_rw [h_ite]
    rw [Fintype.prod_extend_by_one, mul_comm,
      Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  · have hfun :
        (fun p : Ω × (Fin r → Ω) => Function.update p.2 i p.1) =
          (fun q : (Fin r → Ω) × Ω => Function.update q.1 i q.2) ∘ Prod.swap := rfl
    rw [hfun]
    exact (measurable_update' (a := i)).comp measurable_swap
  · exact MeasurableSet.univ_pi (fun j => hs j)

@[blueprint "lem:finite-product-coordinate-reintegration"
  (statement := /-- Let $r$ be a positive integer, let $(\mu_j)_{j\in[r]}$ be probability measures on a measurable space $\Omega$, and let $\mu^\otimes=\bigotimes_{j\in[r]}\mu_j$. For every coordinate $i\in[r]$ and every integrable function $f\colon\Omega^r\to\mathbb R$,
  \[
  \int_\Omega\!\int_{\Omega^r}
    f(x_1,\ldots,x_{i-1},y,x_{i+1},\ldots,x_r)
    \,d\mu^\otimes(x)\,d\mu_i(y)
  =\int_{\Omega^r}f(x)\,d\mu^\otimes(x).
  \] -/)
  (proof := /-- Let $T_i(y,x)$ be the vector obtained from $x$ by replacing its $i$th coordinate by $y$. By \cref{lem:finite-product-coordinate-update-map}, the measurable map $T_i$ pushes $\mu_i\otimes\mu^\otimes$ forward to $\mu^\otimes$. Consequently, integrability of $f$ with respect to $\mu^\otimes$ implies integrability of $f\circ T_i$ with respect to $\mu_i\otimes\mu^\otimes$. Fubini's theorem identifies the iterated integral in the statement with the integral of $f\circ T_i$ against this product measure. The change-of-variables formula for the pushforward identity then identifies that integral with the integral of $f$ against $\mu^\otimes$. -/)
  (title := /-- Reintegration of one finite-product coordinate -/)
  (latexEnv := "lemma")]
lemma finite_product_coordinate_reintegration
    {r : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Fin r → Measure Ω) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin r) (f : (Fin r → Ω) → ℝ)
    (hf : Integrable f (Measure.pi μ)) :
    (∫ y, ∫ x, f (Function.update x i y) ∂(Measure.pi μ) ∂(μ i)) =
      ∫ x, f x ∂(Measure.pi μ) := by
  have hmeas : Measurable
      (fun p : Ω × (Fin r → Ω) => Function.update p.2 i p.1) := by
    have hfun :
        (fun p : Ω × (Fin r → Ω) => Function.update p.2 i p.1) =
          (fun q : (Fin r → Ω) × Ω => Function.update q.1 i q.2) ∘ Prod.swap := rfl
    rw [hfun]
    exact (measurable_update' (a := i)).comp measurable_swap
  have hpres : MeasurePreserving
      (fun p : Ω × (Fin r → Ω) => Function.update p.2 i p.1)
      ((μ i).prod (Measure.pi μ)) (Measure.pi μ) :=
    ⟨hmeas, finite_product_coordinate_update_map μ i⟩
  have hcomp : Integrable
      (fun p : Ω × (Fin r → Ω) => f (Function.update p.2 i p.1))
      ((μ i).prod (Measure.pi μ)) :=
    (hpres.integrable_comp hf.aestronglyMeasurable).mpr hf
  calc
    (∫ y, ∫ x, f (Function.update x i y) ∂(Measure.pi μ) ∂(μ i)) =
        ∫ p : Ω × (Fin r → Ω), f (Function.update p.2 i p.1)
          ∂((μ i).prod (Measure.pi μ)) :=
      (integral_prod _ hcomp).symm
    _ = ∫ x, f x ∂Measure.map
        (fun p : Ω × (Fin r → Ω) => Function.update p.2 i p.1)
        ((μ i).prod (Measure.pi μ)) := by
      symm
      apply integral_map hmeas.aemeasurable
      rw [finite_product_coordinate_update_map μ i]
      exact hf.aestronglyMeasurable
    _ = ∫ x, f x ∂(Measure.pi μ) := by
      rw [finite_product_coordinate_update_map μ i]

@[blueprint "lem:vector-of-means-group-risk-integrable"
  (statement := /-- Let $K$ and $M$ be positive integers, let $p$ be a biased-source mean-estimation problem, and let $n$ be any sampling plan. The squared group loss of the vector-of-means estimator is integrable under the sampling law of every model $P\in\mathcal P_p(R,\sigma^2)$. -/)
  (proof := /-- Fix $P\in\mathcal P_p(R,\sigma^2)$. By \cref{def:bounded-conditional-mean-class}, the identity belongs to $L^2(P_z)$ for every $z\in[K]$. In the product measure used in \cref{def:source-observation-law}, each coordinate projection therefore belongs to $L^2$. The measurable selector $(z,(y_j)_j)\mapsto y_z$ is the finite sum, over $j\in[K]$, of the $j$th coordinate restricted to the measurable event $\{z=j\}$. It consequently belongs to $L^2$, and the pushforward characterization of $L^2$ shows that the outcome coordinate belongs to $L^2$ under every source-observation law. Applying the measure-preserving coordinate projections in the two finite products of \cref{def:sampling-law} then shows that every sampled outcome $D_{m,i}.2$ belongs to $L^2$ under the sampling law.\n\n  Fix $z\in[K]$. By \cref{def:observed-group-sum}, the sum $S_z(D)$ is a finite sum of sampled outcomes restricted to the measurable events $\{D_{m,i}.1=z\}$, so $S_z\in L^2$. The measurability of $D\mapsto\bar Y_z(D)$ follows from \cref{lem:vector-of-means-estimator-measurable} and \cref{def:vector-of-means-estimator}. If $N_z(D)=0$, then $\bar Y_z(D)=0$; otherwise $N_z(D)\ge 1$, and \cref{def:observed-group-mean} gives $|\bar Y_z(D)|=|S_z(D)|/N_z(D)\le |S_z(D)|$. Hence $\bar Y_z\in L^2$ by domination. The sampling law is a probability measure, so subtracting the constant $\mu_P(z)$ preserves $L^2$; its square is therefore integrable. Summing these integrable squared errors over the finite set $[K]$ proves \cref{def:group-risk-integrable}. -/)
  (title := /-- Finite group risk of the vector-of-means estimator -/)
  (latexEnv := "lemma")]
lemma vector_of_means_group_risk_integrable
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M) :
    group_risk_integrable p n vector_of_means_estimator := by
  rw [group_risk_integrable]
  intro P hP
  classical
  let select : Fin K × (Fin K → ℝ) → Fin K × ℝ :=
    fun x => (x.1, x.2 x.1)
  have hselect : Measurable select := by
    apply measurable_fst.prodMk
    have heval : Measurable (fun x : Fin K × (Fin K → ℝ) =>
        ∑ z, if x.1 = z then x.2 z else 0) := by
      apply Finset.measurable_sum Finset.univ
      intro z _
      exact Measurable.ite ((measurableSet_singleton z).preimage measurable_fst)
        ((measurable_pi_apply z).comp measurable_snd) measurable_const
    simpa using heval
  have houtcome_source : ∀ m, MeasureTheory.MemLp
      (fun x : Fin K × ℝ => x.2) 2 (source_observation_law p P m) := by
    intro m
    have hcoord : ∀ z, MeasureTheory.MemLp (fun y : Fin K → ℝ => y z) 2
        (Measure.pi fun z => (P z : Measure ℝ)) := by
      intro z
      simpa [Function.comp_def] using
        (hP z).1.comp_measurePreserving
          (MeasureTheory.measurePreserving_eval (fun z => (P z : Measure ℝ)) z)
    have hselected : MeasureTheory.MemLp
        (fun x : Fin K × (Fin K → ℝ) => x.2 x.1) 2
        ((p.sourceGroup m).toMeasure.prod (Measure.pi fun z => (P z : Measure ℝ))) := by
      have hterm : ∀ z, MeasureTheory.MemLp
          (Set.indicator {x : Fin K × (Fin K → ℝ) | x.1 = z} (fun x => x.2 z)) 2
          ((p.sourceGroup m).toMeasure.prod (Measure.pi fun z => (P z : Measure ℝ))) := by
        intro z
        exact ((hcoord z).comp_snd (p.sourceGroup m).toMeasure).indicator
          (measurableSet_eq_fun measurable_fst measurable_const)
      convert MeasureTheory.memLp_finsetSum Finset.univ (fun z _ => hterm z) using 1
      ext x
      simp [Set.indicator_apply]
    rw [source_observation_law,
      MeasureTheory.memLp_map_measure_iff measurable_snd.aestronglyMeasurable
        hselect.aemeasurable]
    simpa [select, Function.comp_def] using hselected
  letI : ∀ m, IsProbabilityMeasure (source_observation_law p P m) := fun m => by
    rw [source_observation_law]
    exact Measure.isProbabilityMeasure_map hselect.aemeasurable
  have hcoordinate : ∀ m i, MeasureTheory.MemLp
      (fun D : sampled_dataset K M n => (D m i).2) 2 (sampling_law p n P) := by
    intro m i
    have hinner : MeasureTheory.MemLp
        (fun x : Fin (n m) → Fin K × ℝ => (x i).2) 2
        (Measure.pi fun _i : Fin (n m) => source_observation_law p P m) := by
      simpa [Function.comp_def] using
        (houtcome_source m).comp_measurePreserving
          (MeasureTheory.measurePreserving_eval
            (fun _i : Fin (n m) => source_observation_law p P m) i)
    simpa [sampling_law, Function.comp_def] using
      hinner.comp_measurePreserving
        (MeasureTheory.measurePreserving_eval
          (fun m => Measure.pi fun _i : Fin (n m) => source_observation_law p P m) m)
  have hsum : ∀ z, MeasureTheory.MemLp
      (fun D : sampled_dataset K M n => observed_group_sum D z) 2
      (sampling_law p n P) := by
    intro z
    change MeasureTheory.MemLp
      (fun D : sampled_dataset K M n =>
        ∑ m, ∑ i, if (D m i).1 = z then (D m i).2 else 0) 2
      (sampling_law p n P)
    apply MeasureTheory.memLp_finsetSum Finset.univ
    intro m _
    apply MeasureTheory.memLp_finsetSum Finset.univ
    intro i _
    have hevent : MeasurableSet
        {D : sampled_dataset K M n | (D m i).1 = z} :=
      measurableSet_eq_fun
        (measurable_fst.comp ((measurable_pi_apply i).comp (measurable_pi_apply m)))
        measurable_const
    convert (hcoordinate m i).indicator hevent using 1
    ext D
    simp [Set.indicator_apply]
  have hmean_meas : ∀ z, Measurable
      (fun D : sampled_dataset K M n => observed_group_mean D z) := by
    intro z
    change Measurable (fun D : sampled_dataset K M n => vector_of_means_estimator D z)
    exact (measurable_pi_apply z).comp (vector_of_means_estimator_measurable n)
  have hmean : ∀ z, MeasureTheory.MemLp
      (fun D : sampled_dataset K M n => observed_group_mean D z) 2
      (sampling_law p n P) := by
    intro z
    apply (hsum z).mono (hmean_meas z).aestronglyMeasurable
    filter_upwards [] with D
    rw [observed_group_mean]
    split_ifs with hz
    · simp
    · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div]
      apply div_le_self (abs_nonneg _)
      have hcount : (1 : ℝ) ≤ observed_group_count D z := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      simpa [abs_of_nonneg] using hcount
  letI : IsProbabilityMeasure (sampling_law p n P) := by
    unfold sampling_law
    infer_instance
  apply MeasureTheory.integrable_finsetSum Finset.univ
  intro z _
  have herr : MeasureTheory.MemLp
      (fun D : sampled_dataset K M n =>
        observed_group_mean D z - conditional_group_mean P z) 2
      (sampling_law p n P) :=
    (hmean z).sub (MeasureTheory.memLp_const (conditional_group_mean P z))
  simpa [vector_of_means_estimator] using herr.integrable_sq

@[blueprint "lem:post-stratified-finite-measure-sum-product-left-local"
  (statement := /-- Product with a fixed finite measure distributes over a finite sum in the left factor. -/)
  (proof := /-- Induct over the finite index set and use additivity of product measure in its left argument. -/)
  (title := /-- Finite left distributivity of product measure -/)
  (latexEnv := "lemma")]
lemma post_stratified_finite_measure_sum_product_left_local
    {ι α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (s : Finset ι) (μ : ι → Measure α) (ν : Measure β)
    [∀ i, IsFiniteMeasure (μ i)] [SFinite ν] :
    (∑ i ∈ s, μ i).prod ν = ∑ i ∈ s, (μ i).prod ν := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert, ha, not_false_eq_true]
      rw [add_comm, Measure.add_prod (μ a), ih, add_comm]

@[blueprint "lem:post-stratified-finite-measure-sum-map-local"
  (statement := /-- A measurable pushforward distributes over a finite sum of measures. -/)
  (proof := /-- Induct over the finite index set, using preservation of zero and addition by measurable pushforward. -/)
  (title := /-- Finite distributivity of measurable pushforward -/)
  (latexEnv := "lemma")]
lemma post_stratified_finite_measure_sum_map_local
    {ι α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (s : Finset ι) (μ : ι → Measure α) (f : α → β) (hf : Measurable f) :
    (∑ i ∈ s, μ i).map f = ∑ i ∈ s, (μ i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [ha, Measure.map_add, hf, ih]

@[blueprint "lem:post-stratified-finite-pmf-dirac-expansion-local"
  (statement := /-- On a finite measurable space with measurable singletons, the measure of a probability mass function is the weighted sum of its Dirac masses. -/)
  (proof := /-- Evaluate both measures on an arbitrary measurable set and use the finite-space formula for a probability mass function. -/)
  (title := /-- Dirac expansion of a finite probability law -/)
  (latexEnv := "lemma")]
lemma post_stratified_finite_pmf_dirac_expansion_local
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (q : PMF α) :
    q.toMeasure = ∑ x, (q x).toNNReal • Measure.dirac x := by
  ext A hA
  simp [PMF.toMeasure_apply_fintype, hA]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : x ∈ A <;>
    simp [h, ENNReal.coe_toNNReal (q.apply_ne_top x)]

@[blueprint "lem:post-stratified-source-observation-law-mixture-local"
  (statement := /-- The law of one source observation is the finite mixture
  \[
  \sum_z q_{S,m}(z)\,(y\mapsto(z,y))_\#P_z.
  \] -/)
  (proof := /-- Expand the source probability mass function by
  \cref{lem:post-stratified-finite-pmf-dirac-expansion-local}, distribute
  product and pushforward using
  \cref{lem:post-stratified-finite-measure-sum-product-left-local,lem:post-stratified-finite-measure-sum-map-local},
  and identify the selected coordinate marginal of the finite product law. -/)
  (title := /-- Mixture form of a source observation law -/)
  (latexEnv := "lemma")]
lemma post_stratified_source_observation_law_mixture_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (P : conditional_outcome_model K)
    (m : Fin M) :
    source_observation_law p P m =
      ∑ z, (p.sourceGroup m z).toNNReal •
        (P z : Measure ℝ).map (Prod.mk z) := by
  classical
  let ν : Measure (Fin K → ℝ) := Measure.pi fun z => (P z : Measure ℝ)
  let f : Fin K × (Fin K → ℝ) → Fin K × ℝ := fun x => (x.1, x.2 x.1)
  have heval : Measurable (fun x : Fin K × (Fin K → ℝ) => x.2 x.1) := by
    have heq : (fun x : Fin K × (Fin K → ℝ) => x.2 x.1) =
        fun x => ∑ z, if x.1 = z then x.2 z else 0 := by
      funext x
      simp
    rw [heq]
    apply Finset.measurable_sum
    intro z hz
    apply Measurable.ite
    · exact measurable_fst (MeasurableSet.singleton z)
    · exact (measurable_pi_apply z).comp measurable_snd
    · exact measurable_const
  have hf : Measurable f := measurable_fst.prodMk heval
  rw [source_observation_law,
    post_stratified_finite_pmf_dirac_expansion_local (p.sourceGroup m)]
  change ((∑ z, (p.sourceGroup m z).toNNReal • Measure.dirac z).prod ν).map f = _
  have hprod :
      (∑ z, (p.sourceGroup m z).toNNReal • Measure.dirac z).prod ν =
        ∑ z, ((p.sourceGroup m z).toNNReal • Measure.dirac z).prod ν := by
    simpa using post_stratified_finite_measure_sum_product_left_local
      (Finset.univ : Finset (Fin K))
      (fun z => (p.sourceGroup m z).toNNReal • Measure.dirac z) ν
  rw [hprod]
  have hmap :
      (∑ z, ((p.sourceGroup m z).toNNReal • Measure.dirac z).prod ν).map f =
        ∑ z, (((p.sourceGroup m z).toNNReal • Measure.dirac z).prod ν).map f := by
    simpa using post_stratified_finite_measure_sum_map_local
      (Finset.univ : Finset (Fin K))
      (fun z => ((p.sourceGroup m z).toNNReal • Measure.dirac z).prod ν) f hf
  rw [hmap]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Measure.prod_smul_left, Measure.map_smul]
  congr 1
  rw [Measure.dirac_prod]
  have hcoord : ν.map (Function.eval z) = (P z : Measure ℝ) := by
    simpa [ν] using Measure.pi_map_eval (fun z => (P z : Measure ℝ)) z
  calc
    (ν.map (Prod.mk z)).map f = ν.map (f ∘ Prod.mk z) :=
      Measure.map_map hf measurable_prodMk_left
    _ = ν.map (Prod.mk z ∘ Function.eval z) := by
      apply Measure.map_congr
      filter_upwards with x
      rfl
    _ = (ν.map (Function.eval z)).map (Prod.mk z) :=
      (Measure.map_map measurable_prodMk_left (measurable_pi_apply z)).symm
    _ = (P z : Measure ℝ).map (Prod.mk z) := by rw [hcoord]

@[blueprint "lem:post-stratified-finite-pi-mixture-local"
  (statement := /-- A finite product of finite mixtures is the finite mixture, indexed by all coordinatewise choices, of the corresponding product measures. -/)
  (proof := /-- By uniqueness of finite product measures, evaluate both sides on a measurable rectangle. The result is the distributive identity expressing a product of finite sums as the sum, over all choice functions, of the associated products. -/)
  (title := /-- Expansion of a finite product of mixtures -/)
  (latexEnv := "lemma")]
lemma post_stratified_finite_pi_mixture_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (w : ∀ i, κ i → NNReal) (μ : ∀ i, κ i → Measure (Ω i))
    [∀ i j, IsFiniteMeasure (μ i j)] :
    Measure.pi (fun i => ∑ j, w i j • μ i j) =
      ∑ x : ∀ i, κ i, (∏ i, w i (x i)) •
        Measure.pi (fun i => μ i (x i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  simp [Measure.pi_pi, hs, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x hx
  change (↑(∏ i, w i (x i)) : ENNReal) *
      (∏ i, (μ i (x i)) (s i)) =
    ∏ i, (w i (x i) : ENNReal) * (μ i (x i)) (s i)
  have hw : (↑(∏ i, w i (x i)) : ENNReal) =
      ∏ i, (w i (x i) : ENNReal) := by
    push_cast
    rfl
  rw [hw, Finset.prod_mul_distrib]

@[blueprint "def:post-stratified-label-weight-local"
  (statement := /-- The probability weight of a complete sampled-label array is the product of its source-specific group masses. -/)
  (title := /-- Weight of a sampled-label array -/)
  (latexEnv := "definition")]
noncomputable def post_stratified_label_weight_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (L : (m : Fin M) → Fin (n m) → Fin K) : NNReal :=
  ∏ m, ∏ i, (p.sourceGroup m (L m i)).toNNReal

@[blueprint "def:post-stratified-fixed-label-measure-local"
  (statement := /-- For a fixed sampled-label array, the conditional dataset law is the finite product of the corresponding outcome laws, with each fixed label attached to its outcome. -/)
  (title := /-- Conditional dataset law at fixed labels -/)
  (latexEnv := "definition")]
noncomputable def post_stratified_fixed_label_measure_local
    {K M : ℕ} {n : sampling_plan M}
    (P : conditional_outcome_model K)
    (L : (m : Fin M) → Fin (n m) → Fin K) :
    Measure (sampled_dataset K M n) :=
  Measure.pi fun m => Measure.pi fun i =>
    (P (L m i) : Measure ℝ).map (Prod.mk (L m i))

@[blueprint "lem:post-stratified-sampling-law-mixture-local"
  (statement := /-- The full sampling law is the finite mixture, over all sampled-label arrays, of the corresponding fixed-label product outcome laws. -/)
  (proof := /-- Rewrite every one-observation source law by
  \cref{lem:post-stratified-source-observation-law-mixture-local}. Apply
  \cref{lem:post-stratified-finite-pi-mixture-local} first within each
  source and then across sources; the resulting nested product of group
  masses is exactly the label weight in the statement. -/)
  (title := /-- Fixed-label mixture expansion of the sampling law -/)
  (latexEnv := "lemma")]
lemma post_stratified_sampling_law_mixture_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (P : conditional_outcome_model K) :
    sampling_law p n P =
      ∑ L : (m : Fin M) → Fin (n m) → Fin K,
        post_stratified_label_weight_local p n L •
          post_stratified_fixed_label_measure_local P L := by
  classical
  unfold sampling_law
  have hinner (m : Fin M) :
      Measure.pi (fun _i : Fin (n m) => source_observation_law p P m) =
        ∑ Lm : Fin (n m) → Fin K,
          (∏ i, (p.sourceGroup m (Lm i)).toNNReal) •
            Measure.pi (fun i =>
              (P (Lm i) : Measure ℝ).map (Prod.mk (Lm i))) := by
    simp_rw [post_stratified_source_observation_law_mixture_local p P m]
    exact post_stratified_finite_pi_mixture_local
      (fun _i z => (p.sourceGroup m z).toNNReal)
      (fun _i z => (P z : Measure ℝ).map (Prod.mk z))
  simp_rw [hinner]
  rw [post_stratified_finite_pi_mixture_local]
  rfl

@[blueprint "def:post-stratified-label-count-local"
  (statement := /-- For a complete label array, its deterministic count in group $z$ is the number of coordinates carrying label $z$. -/)
  (title := /-- Group count of a fixed label array -/)
  (latexEnv := "definition")]
def post_stratified_label_count_local
    {K M : ℕ} {n : sampling_plan M}
    (L : (m : Fin M) → Fin (n m) → Fin K) (z : Fin K) : ℕ :=
  ∑ m, ∑ i, if L m i = z then 1 else 0

@[blueprint "lem:post-stratified-label-count-present-positive-local"
  (statement := /-- The count of the label occurring at any coordinate of a fixed label array is positive. -/)
  (proof := /-- The indicated coordinate contributes one to its inner sum, and all other summands are nonnegative. -/)
  (title := /-- Positivity of every observed fixed-label count -/)
  (latexEnv := "lemma")]
lemma post_stratified_label_count_present_positive_local
    {K M : ℕ} {n : sampling_plan M}
    (L : (m : Fin M) → Fin (n m) → Fin K) (m : Fin M) (i : Fin (n m)) :
    0 < post_stratified_label_count_local L (L m i) := by
  unfold post_stratified_label_count_local
  apply Finset.sum_pos'
  · intro m' hm'
    exact Finset.sum_nonneg fun i' hi' => Nat.zero_le _
  · refine ⟨m, Finset.mem_univ m, ?_⟩
    apply Finset.sum_pos'
    · intro i' hi'
      exact Nat.zero_le _
    · exact ⟨i, Finset.mem_univ i, by simp⟩

@[blueprint "lem:post-stratified-estimator-fixed-labels-local"
  (statement := /-- If a dataset has fixed labels $L$, then the post-stratified estimator is the coordinate sum
  \[
  \sum_{m,i}\frac{q_T(L_{m,i})}{N_{L_{m,i}}(L)}Y_{m,i}.
  \] -/)
  (proof := /-- Substitute the fixed labels into the definitions of the observed counts and sums. For a group of count zero every indicator is zero. For a group of positive count, distribute its weight over its outcome sum, interchange the three finite sums, and use
  \cref{lem:post-stratified-label-count-present-positive-local} to collapse the group sum at each observed coordinate. -/)
  (title := /-- Coordinate form of the estimator at fixed labels -/)
  (latexEnv := "lemma")]
lemma post_stratified_estimator_fixed_labels_local
    {K M : ℕ} [NeZero K] [NeZero M] {n : sampling_plan M}
    (q : PMF (Fin K)) (L : (m : Fin M) → Fin (n m) → Fin K)
    (D : sampled_dataset K M n) (hD : ∀ m i, (D m i).1 = L m i) :
    post_stratified_estimator q D =
      ∑ m, ∑ i,
        (pmf_real_mass q (L m i) /
          post_stratified_label_count_local L (L m i)) * (D m i).2 := by
  unfold post_stratified_estimator observed_group_mean observed_group_count
    observed_group_sum post_stratified_label_count_local
  simp_rw [hD]
  have hgroup (z : Fin K) :
      pmf_real_mass q z *
          (if ((∑ m, ∑ i, if L m i = z then 1 else 0) : ℕ) = 0 then 0
          else (∑ m, ∑ i, if L m i = z then (D m i).2 else 0) /
            ((∑ m, ∑ i, if L m i = z then 1 else 0) : ℕ)) =
        ∑ m, ∑ i, if L m i = z then
          (pmf_real_mass q z /
            ((∑ m, ∑ i, if L m i = z then 1 else 0) : ℕ)) * (D m i).2 else 0 := by
    by_cases hz : ((∑ m, ∑ i, if L m i = z then 1 else 0) : ℕ) = 0
    · rw [if_pos hz]
      simp only [mul_zero]
      symm
      apply Finset.sum_eq_zero
      intro m hm
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hL : L m i = z
      · have hp := post_stratified_label_count_present_positive_local L m i
        unfold post_stratified_label_count_local at hp
        rw [hL, hz] at hp
        omega
      · simp [hL]
    · rw [if_neg hz]
      rw [← mul_div_assoc, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hL : L m i = z
      · simp only [hL, if_true]
        ring
      · simp [hL]
  simp_rw [hgroup]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (L m i)]
  · have hp := post_stratified_label_count_present_positive_local L m i
    simp only [if_pos rfl]
    rfl
  · intro z hz hne
    simp [hne.symm]
  · intro h
    exact (h (Finset.mem_univ (L m i))).elim

@[blueprint "lem:post-stratified-fixed-label-measure-support-local"
  (statement := /-- Under the fixed-label conditional measure, every dataset coordinate has its prescribed label almost surely. -/)
  (proof := /-- A pushed-forward coordinate law is supported on pairs whose first component is the fixed label. Apply the almost-everywhere product-coordinate theorem within each source and then across sources. -/)
  (title := /-- Almost-sure support of the fixed-label law -/)
  (latexEnv := "lemma")]
lemma post_stratified_fixed_label_measure_support_local
    {K M : ℕ} {n : sampling_plan M}
    (P : conditional_outcome_model K)
    (L : (m : Fin M) → Fin (n m) → Fin K) :
    ∀ᵐ D ∂post_stratified_fixed_label_measure_local P L,
      ∀ m i, (D m i).1 = L m i := by
  have hcoord (m : Fin M) (i : Fin (n m)) :
      (fun x : Fin K × ℝ => x.1) =ᵐ[
          (P (L m i) : Measure ℝ).map (Prod.mk (L m i))]
        fun _ => L m i := by
    apply (MeasureTheory.ae_map_iff measurable_prodMk_left.aemeasurable
      (measurableSet_eq_fun measurable_fst measurable_const)).2
    exact Filter.Eventually.of_forall fun y => rfl
  have hinner (m : Fin M) :
      (fun d : Fin (n m) → Fin K × ℝ => fun i => (d i).1) =ᵐ[
          Measure.pi fun i =>
            (P (L m i) : Measure ℝ).map (Prod.mk (L m i))]
        fun _ => L m :=
    Measure.ae_eq_pi fun i => hcoord m i
  have houter :
      (fun D : sampled_dataset K M n => fun m i => (D m i).1) =ᵐ[
          post_stratified_fixed_label_measure_local P L] fun _ => L := by
    unfold post_stratified_fixed_label_measure_local
    exact Measure.ae_eq_pi hinner
  filter_upwards [houter] with D hD
  intro m i
  exact congrFun (congrFun hD m) i

@[blueprint "def:post-stratified-fixed-label-estimator-local"
  (statement := /-- At fixed labels $L$, write the post-stratified estimator as the weighted coordinate sum with coefficient $q_T(L_{m,i})/N_{L_{m,i}}(L)$. -/)
  (title := /-- Fixed-label coordinate estimator -/)
  (latexEnv := "definition")]
noncomputable def post_stratified_fixed_label_estimator_local
    {K M : ℕ} {n : sampling_plan M}
    (q : PMF (Fin K)) (L : (m : Fin M) → Fin (n m) → Fin K)
    (D : sampled_dataset K M n) : ℝ :=
  ∑ m, ∑ i,
    (pmf_real_mass q (L m i) /
      post_stratified_label_count_local L (L m i)) * (D m i).2

@[blueprint "def:post-stratified-fixed-label-harmonic-local"
  (statement := /-- For fixed labels $L$, the conditional variance coefficient is
  $\sum_{z:N_z(L)>0}q_T(z)^2/N_z(L)$. -/)
  (title := /-- Fixed-label reciprocal-count harmonic term -/)
  (latexEnv := "definition")]
noncomputable def post_stratified_fixed_label_harmonic_local
    {K M : ℕ} {n : sampling_plan M}
    (q : PMF (Fin K)) (L : (m : Fin M) → Fin (n m) → Fin K) : ℝ :=
  ∑ z, if post_stratified_label_count_local L z = 0 then 0
    else (pmf_real_mass q z) ^ 2 / post_stratified_label_count_local L z

@[blueprint "def:post-stratified-fixed-label-missing-mass-local"
  (statement := /-- For fixed labels $L$, the missing target mass is the sum of $q_T(z)$ over groups with $N_z(L)=0$. -/)
  (title := /-- Missing target mass at fixed labels -/)
  (latexEnv := "definition")]
noncomputable def post_stratified_fixed_label_missing_mass_local
    {K M : ℕ} {n : sampling_plan M}
    (q : PMF (Fin K)) (L : (m : Fin M) → Fin (n m) → Fin K) : ℝ :=
  ∑ z, if post_stratified_label_count_local L z = 0
    then pmf_real_mass q z else 0

@[blueprint "lem:post-stratified-integral-eval-pi-local"
  (statement := /-- The expectation of a function of one coordinate under a finite product probability measure is its expectation under that coordinate law. -/)
  (proof := /-- Apply the change-of-variables formula for the measurable coordinate evaluation map and its product-measure marginal identity. -/)
  (title := /-- Coordinate integration under a finite product law -/)
  (latexEnv := "lemma")]
lemma post_stratified_integral_eval_pi_local
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) (f : Ω i → ℝ) (hf : AEStronglyMeasurable f (μ i)) :
    (∫ x, f (x i) ∂Measure.pi μ) = ∫ y, f y ∂μ i := by
  have hf' : AEStronglyMeasurable f
      (Measure.map (Function.eval i) (Measure.pi μ)) := by
    simpa [Measure.pi_map_eval] using hf
  calc
    (∫ x, f (x i) ∂Measure.pi μ) =
        ∫ y, f y ∂Measure.map (Function.eval i) (Measure.pi μ) := by
      symm
      exact MeasureTheory.integral_map (measurable_pi_apply i).aemeasurable hf'
    _ = ∫ y, f y ∂μ i := by
      simp [Measure.pi_map_eval]

@[blueprint "lem:post-stratified-fixed-label-coefficient-square-sum-local"
  (statement := /-- The sum of the squared fixed-label coordinate coefficients equals the reciprocal-count harmonic term:
  \[
  \sum_{m,i}\left(\frac{q_T(L_{m,i})}{N_{L_{m,i}}(L)}\right)^2
  =\sum_{z:N_z(L)>0}\frac{q_T(z)^2}{N_z(L)}.
  \] -/)
  (proof := /-- Regroup the coordinate sum by labels. A group of count zero contributes nothing, using
  \cref{lem:post-stratified-label-count-present-positive-local} to rule out a coordinate with that label. A group of positive count contributes its common squared coefficient exactly $N_z(L)$ times, which simplifies to $q_T(z)^2/N_z(L)$. -/)
  (title := /-- Squared coefficient sum at fixed labels -/)
  (latexEnv := "lemma")]
lemma post_stratified_fixed_label_coefficient_square_sum_local
    {K M : ℕ} [NeZero K] [NeZero M] {n : sampling_plan M}
    (q : PMF (Fin K)) (L : (m : Fin M) → Fin (n m) → Fin K) :
    (∑ m, ∑ i,
      (pmf_real_mass q (L m i) /
        post_stratified_label_count_local L (L m i)) ^ 2) =
      post_stratified_fixed_label_harmonic_local q L := by
  classical
  have hgroup (z : Fin K) :
      (∑ m, ∑ i, if L m i = z then
        (pmf_real_mass q z /
          post_stratified_label_count_local L z) ^ 2 else 0) =
        if post_stratified_label_count_local L z = 0 then 0
        else (pmf_real_mass q z) ^ 2 /
          post_stratified_label_count_local L z := by
    by_cases hz : post_stratified_label_count_local L z = 0
    · rw [if_pos hz]
      apply Finset.sum_eq_zero
      intro m hm
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hL : L m i = z
      · have hp := post_stratified_label_count_present_positive_local L m i
        rw [hL, hz] at hp
        omega
      · simp [hL]
    · rw [if_neg hz]
      have hcount :
          (∑ m, ∑ i, if L m i = z then
            (pmf_real_mass q z /
              post_stratified_label_count_local L z) ^ 2 else 0) =
            (pmf_real_mass q z /
                post_stratified_label_count_local L z) ^ 2 *
              (post_stratified_label_count_local L z : ℝ) := by
        unfold post_stratified_label_count_local
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hL : L m i = z <;> simp [hL]
      rw [hcount]
      have hzr : (post_stratified_label_count_local L z : ℝ) ≠ 0 := by
        exact_mod_cast hz
      field_simp
  rw [post_stratified_fixed_label_harmonic_local]
  rw [← Finset.sum_congr rfl fun z _ => hgroup z]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (L m i)]
  · simp
  · intro z hz hne
    simp [hne.symm]
  · intro h
    exact (h (Finset.mem_univ (L m i))).elim

@[blueprint "lem:post-stratified-fixed-label-coefficient-sum-local"
  (statement := /-- For every group-indexed vector $v$, summing the fixed-label coordinate coefficients against $v_{L_{m,i}}$ gives
  \[
  \sum_{z:N_z(L)>0}q_T(z)v_z.
  \] -/)
  (proof := /-- Regroup coordinates by their labels. A missing group contributes zero by
  \cref{lem:post-stratified-label-count-present-positive-local}, while a present group contributes the common value $q_T(z)v_z/N_z(L)$ exactly $N_z(L)$ times. -/)
  (title := /-- Fixed-label coefficient regrouping identity -/)
  (latexEnv := "lemma")]
lemma post_stratified_fixed_label_coefficient_sum_local
    {K M : ℕ} [NeZero K] [NeZero M] {n : sampling_plan M}
    (q : PMF (Fin K)) (L : (m : Fin M) → Fin (n m) → Fin K)
    (v : Fin K → ℝ) :
    (∑ m, ∑ i,
      (pmf_real_mass q (L m i) /
        post_stratified_label_count_local L (L m i)) * v (L m i)) =
      ∑ z, if post_stratified_label_count_local L z = 0 then 0
        else pmf_real_mass q z * v z := by
  classical
  have hgroup (z : Fin K) :
      (∑ m, ∑ i, if L m i = z then
        (pmf_real_mass q z / post_stratified_label_count_local L z) * v z
        else 0) =
        if post_stratified_label_count_local L z = 0 then 0
        else pmf_real_mass q z * v z := by
    by_cases hz : post_stratified_label_count_local L z = 0
    · rw [if_pos hz]
      apply Finset.sum_eq_zero
      intro m hm
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hL : L m i = z
      · have hp := post_stratified_label_count_present_positive_local L m i
        rw [hL, hz] at hp
        omega
      · simp [hL]
    · rw [if_neg hz]
      have hcount :
          (∑ m, ∑ i, if L m i = z then
            (pmf_real_mass q z / post_stratified_label_count_local L z) * v z
            else 0) =
            ((pmf_real_mass q z / post_stratified_label_count_local L z) * v z) *
              (post_stratified_label_count_local L z : ℝ) := by
        unfold post_stratified_label_count_local
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hL : L m i = z <;> simp [hL]
      rw [hcount]
      have hzr : (post_stratified_label_count_local L z : ℝ) ≠ 0 := by
        exact_mod_cast hz
      field_simp
  rw [← Finset.sum_congr rfl fun z _ => hgroup z]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (L m i)]
  · simp
  · intro z hz hne
    simp [hne.symm]
  · intro h
    exact (h (Finset.mem_univ (L m i))).elim

@[blueprint "lem:post-stratified-fixed-label-estimator-memlp-local"
  (statement := /-- Under every bounded conditional outcome model, the fixed-label coordinate estimator belongs to $L^2$ of its fixed-label product law. -/)
  (proof := /-- Each coordinate outcome belongs to $L^2$ after attaching its fixed label, because the identity belongs to $L^2(P_z)$. Constant multiplication, coordinate pullback under the product law, and finite summation preserve $L^2$, first within sources and then across sources. -/)
  (title := /-- Square integrability of the fixed-label estimator -/)
  (latexEnv := "lemma")]
lemma post_stratified_fixed_label_estimator_memlp_local
    {K M : ℕ} [NeZero K] [NeZero M] {n : sampling_plan M}
    (p : biased_source_mean_problem K M) (P : conditional_outcome_model K)
    (hP : bounded_conditional_mean_class p P)
    (L : (m : Fin M) → Fin (n m) → Fin K) :
    MemLp (post_stratified_fixed_label_estimator_local p.targetGroup L) 2
      (post_stratified_fixed_label_measure_local P L) := by
  classical
  let μ (m : Fin M) (i : Fin (n m)) : Measure (Fin K × ℝ) :=
    (P (L m i) : Measure ℝ).map (Prod.mk (L m i))
  let a (m : Fin M) (i : Fin (n m)) : ℝ :=
    pmf_real_mass p.targetGroup (L m i) /
      post_stratified_label_count_local L (L m i)
  let X (m : Fin M) (i : Fin (n m)) (x : Fin K × ℝ) : ℝ :=
    a m i * x.2
  let block (m : Fin M) (d : Fin (n m) → Fin K × ℝ) : ℝ :=
    ∑ i, X m i (d i)
  letI hprob : ∀ m i, IsProbabilityMeasure (μ m i) := fun m i =>
    ⟨by
      unfold μ
      rw [Measure.map_apply_of_aemeasurable measurable_prodMk_left.aemeasurable
        MeasurableSet.univ]
      simp⟩
  have hcoord (m : Fin M) (i : Fin (n m)) :
      MemLp (X m i) 2 (μ m i) := by
    change MemLp ((fun _ : Fin K × ℝ => a m i) * Prod.snd) 2
      ((P (L m i) : Measure ℝ).map (Prod.mk (L m i)))
    rw [MeasureTheory.memLp_map_measure_iff
      (measurable_const.mul measurable_snd).aestronglyMeasurable
      measurable_prodMk_left.aemeasurable]
    simpa [a, Function.comp_def] using
      (hP (L m i)).1.const_mul (a m i)
  have hinner (m : Fin M) :
      MemLp (block m) 2 (Measure.pi fun i => μ m i) := by
    have hsum := MeasureTheory.memLp_finsetSum (Finset.univ : Finset (Fin (n m)))
      (fun i _ => (hcoord m i).comp_measurePreserving
        (measurePreserving_eval (fun i => μ m i) i))
    simpa [block, Finset.sum_apply] using hsum
  letI hprobInner : ∀ m, IsProbabilityMeasure
      (Measure.pi fun i => μ m i) := fun m => inferInstance
  have hsum := MeasureTheory.memLp_finsetSum (Finset.univ : Finset (Fin M))
    (fun m _ => (hinner m).comp_measurePreserving
      (measurePreserving_eval (fun m => Measure.pi fun i => μ m i) m))
  change MemLp
    (fun D => ∑ m, ∑ i,
      (pmf_real_mass p.targetGroup (L m i) /
        post_stratified_label_count_local L (L m i)) * (D m i).2) 2
    (Measure.pi fun m => Measure.pi fun i =>
      (P (L m i) : Measure ℝ).map (Prod.mk (L m i)))
  simpa [block, X, a, μ, Finset.sum_apply] using hsum

@[blueprint "lem:post-stratified-fixed-label-estimator-mean-local"
  (statement := /-- Conditional on fixed labels $L$, the mean of the coordinate estimator is
  $\sum_{z:N_z(L)>0}q_T(z)\mu_P(z)$. -/)
  (proof := /-- Integrate the finite coordinate sum first across sources and then within each source. Coordinate evaluation preserves the corresponding product marginal, and pushing forward by $y\mapsto(L_{m,i},y)$ leaves the outcome mean equal to $mu_P(L_{m,i})$. Regroup the resulting coordinate means using
  \cref{lem:post-stratified-integral-eval-pi-local,lem:post-stratified-fixed-label-coefficient-sum-local}. -/)
  (title := /-- Conditional mean at fixed labels -/)
  (latexEnv := "lemma")]
lemma post_stratified_fixed_label_estimator_mean_local
    {K M : ℕ} [NeZero K] [NeZero M] {n : sampling_plan M}
    (p : biased_source_mean_problem K M) (P : conditional_outcome_model K)
    (hP : bounded_conditional_mean_class p P)
    (L : (m : Fin M) → Fin (n m) → Fin K) :
    (∫ D, post_stratified_fixed_label_estimator_local p.targetGroup L D
        ∂post_stratified_fixed_label_measure_local P L) =
      ∑ z, if post_stratified_label_count_local L z = 0 then 0
        else pmf_real_mass p.targetGroup z * conditional_group_mean P z := by
  classical
  let μ (m : Fin M) (i : Fin (n m)) : Measure (Fin K × ℝ) :=
    (P (L m i) : Measure ℝ).map (Prod.mk (L m i))
  let a (m : Fin M) (i : Fin (n m)) : ℝ :=
    pmf_real_mass p.targetGroup (L m i) /
      post_stratified_label_count_local L (L m i)
  let X (m : Fin M) (i : Fin (n m)) (x : Fin K × ℝ) : ℝ :=
    a m i * x.2
  let block (m : Fin M) (d : Fin (n m) → Fin K × ℝ) : ℝ :=
    ∑ i, X m i (d i)
  letI hprob : ∀ m i, IsProbabilityMeasure (μ m i) := fun m i =>
    ⟨by
      unfold μ
      rw [Measure.map_apply_of_aemeasurable measurable_prodMk_left.aemeasurable
        MeasurableSet.univ]
      simp⟩
  have hcoord (m : Fin M) (i : Fin (n m)) :
      MemLp (X m i) 2 (μ m i) := by
    change MemLp ((fun _ : Fin K × ℝ => a m i) * Prod.snd) 2
      ((P (L m i) : Measure ℝ).map (Prod.mk (L m i)))
    rw [MeasureTheory.memLp_map_measure_iff
      (measurable_const.mul measurable_snd).aestronglyMeasurable
      measurable_prodMk_left.aemeasurable]
    simpa [a, Function.comp_def] using
      (hP (L m i)).1.const_mul (a m i)
  have hinner (m : Fin M) :
      MemLp (block m) 2 (Measure.pi fun i => μ m i) := by
    have hsum := MeasureTheory.memLp_finsetSum (Finset.univ : Finset (Fin (n m)))
      (fun i _ => (hcoord m i).comp_measurePreserving
        (measurePreserving_eval (fun i => μ m i) i))
    simpa [block, Finset.sum_apply] using hsum
  have hintcoord (m : Fin M) (i : Fin (n m)) :
      (∫ x, X m i x ∂μ m i) =
        a m i * conditional_group_mean P (L m i) := by
    unfold μ X
    rw [MeasureTheory.integral_map measurable_prodMk_left.aemeasurable
      ((hcoord m i).integrable (by norm_num)).aestronglyMeasurable]
    have hid : Integrable (fun y : ℝ => y) (P (L m i) : Measure ℝ) := by
      simpa [Function.id_def] using (hP (L m i)).1.integrable (by norm_num)
    rw [integral_const_mul_of_integrable hid]
    rfl
  have hintblock (m : Fin M) :
      (∫ d, block m d ∂Measure.pi fun i => μ m i) =
        ∑ i, a m i * conditional_group_mean P (L m i) := by
    have hfun : block m = ∑ i, fun d => X m i (d i) := by
      funext d
      simp [block, Finset.sum_apply]
    rw [hfun]
    simp only [Finset.sum_apply]
    calc
      (∫ d, ∑ i, X m i (d i) ∂Measure.pi fun i => μ m i) =
          ∑ i, ∫ d, X m i (d i) ∂Measure.pi fun i => μ m i := by
        simpa [Finset.sum_apply] using
          MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin (n m)))
            (fun i _ => ((hcoord m i).comp_measurePreserving
              (measurePreserving_eval (fun i => μ m i) i)).integrable
                (by norm_num))
      _ = ∑ i, a m i * conditional_group_mean P (L m i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [post_stratified_integral_eval_pi_local
          (fun i => μ m i) i (X m i) (hcoord m i).aestronglyMeasurable,
          hintcoord]
  letI hprobInner : ∀ m, IsProbabilityMeasure
      (Measure.pi fun i => μ m i) := fun m => inferInstance
  have hfun :
      post_stratified_fixed_label_estimator_local p.targetGroup L =
        ∑ m, fun D => block m (D m) := by
    funext D
    simp [post_stratified_fixed_label_estimator_local, block, X, a,
      Finset.sum_apply]
  rw [post_stratified_fixed_label_measure_local, hfun]
  simp only [Finset.sum_apply]
  calc
    (∫ D, ∑ m, block m (D m)
        ∂Measure.pi fun m => Measure.pi fun i => μ m i) =
        ∑ m, ∫ D, block m (D m)
          ∂Measure.pi fun m => Measure.pi fun i => μ m i := by
      simpa [Finset.sum_apply] using
        MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin M))
          (fun m _ => ((hinner m).comp_measurePreserving
            (measurePreserving_eval (fun m => Measure.pi fun i => μ m i) m)).integrable
              (by norm_num))
    _ = ∑ m, ∫ d, block m d ∂Measure.pi fun i => μ m i := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [post_stratified_integral_eval_pi_local
        (fun m => Measure.pi fun i => μ m i) m (block m)
        (hinner m).aestronglyMeasurable]
    _ = ∑ m, ∑ i, a m i * conditional_group_mean P (L m i) := by
      simp_rw [hintblock]
    _ = _ := by
      simpa [a] using
        post_stratified_fixed_label_coefficient_sum_local p.targetGroup L
          (conditional_group_mean P)

@[blueprint "lem:post-stratified-bias-variance-identity-local"
  (statement := /-- For a square-integrable real random variable $X$ on a probability space and every constant $c$,
  \[
  \int (X-c)^2=\operatorname{Var}(X)+(\mathbb E X-c)^2.
  \] -/)
  (proof := /-- Expand the square, use linearity of the integral for the $L^2$ variable and its square, and substitute the second-moment formula for variance. -/)
  (title := /-- Bias--variance identity -/)
  (latexEnv := "lemma")]
lemma post_stratified_bias_variance_identity_local
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (c : ℝ) :
    (∫ x, (X x - c) ^ 2 ∂μ) =
      ProbabilityTheory.variance X μ + ((∫ x, X x ∂μ) - c) ^ 2 := by
  have hXint : Integrable X μ := hX.integrable (by norm_num)
  have hXsq : Integrable (fun x => (X x) ^ 2) μ := hX.integrable_sq
  rw [ProbabilityTheory.variance_eq_sub hX]
  calc
    (∫ x, (X x - c) ^ 2 ∂μ) =
        ∫ x, (X x) ^ 2 - (2 * c) * X x + c ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring
    _ = (∫ x, (X x) ^ 2 ∂μ) -
          (2 * c) * (∫ x, X x ∂μ) + c ^ 2 := by
      calc
        (∫ x, (X x) ^ 2 - (2 * c) * X x + c ^ 2 ∂μ) =
            (∫ x, (X x) ^ 2 - (2 * c) * X x ∂μ) +
              ∫ _x : Ω, c ^ 2 ∂μ := by
          simpa only [Pi.add_apply, Pi.sub_apply] using
            integral_add (hXsq.sub (hXint.const_mul (2 * c)))
              (integrable_const (c := c ^ 2))
        _ = ((∫ x, (X x) ^ 2 ∂μ) -
              ∫ x, (2 * c) * X x ∂μ) + c ^ 2 := by
          rw [integral_sub hXsq (hXint.const_mul (2 * c)), integral_const]
          simp
        _ = _ := by
          rw [integral_const_mul_of_integrable hXint]
    _ = (∫ x, (X x) ^ 2 ∂μ) - (∫ x, X x ∂μ) ^ 2 +
          ((∫ x, X x ∂μ) - c) ^ 2 := by ring

@[blueprint "lem:post-stratified-pmf-real-mass-sum-local"
  (statement := /-- The real masses of a probability mass function on a finite type sum to one. -/)
  (proof := /-- Apply the real coercion to the defining extended-nonnegative normalization; every finite PMF mass is finite, so coercion commutes with the finite sum. -/)
  (title := /-- Normalization of finite real PMF masses -/)
  (latexEnv := "lemma")]
lemma post_stratified_pmf_real_mass_sum_local
    {α : Type*} [Fintype α] (q : PMF α) :
    ∑ z, pmf_real_mass q z = 1 := by
  have hENN : (∑ z, q z) = (1 : ENNReal) :=
    (hasSum_fintype (fun z => q z)).unique (PMF.hasSum_coe_one q)
  unfold pmf_real_mass
  rw [← ENNReal.toReal_sum]
  · rw [hENN]
    simp
  · intro a ha
    exact q.apply_ne_top a

@[blueprint "lem:post-stratified-fixed-label-bias-bound-local"
  (statement := /-- Under the mean-radius bound, the squared fixed-label bias is at most $R^2$ times the missing target mass. -/)
  (proof := /-- The conditional mean omits exactly the terms belonging to groups of count zero. Bound the absolute omitted sum by $R$ times its target mass. That mass lies in $[0,1]$ by
  \cref{lem:post-stratified-pmf-real-mass-sum-local}, so its square is at most itself. -/)
  (title := /-- Missing-group bias bound at fixed labels -/)
  (latexEnv := "lemma")]
lemma post_stratified_fixed_label_bias_bound_local
    {K M : ℕ} [NeZero K] [NeZero M] {n : sampling_plan M}
    (p : biased_source_mean_problem K M) (P : conditional_outcome_model K)
    (hP : bounded_conditional_mean_class p P)
    (L : (m : Fin M) → Fin (n m) → Fin K) :
    ((∑ z, if post_stratified_label_count_local L z = 0 then 0
        else pmf_real_mass p.targetGroup z * conditional_group_mean P z) -
      target_population_mean p.targetGroup P) ^ 2 ≤
        p.meanRadius ^ 2 *
          post_stratified_fixed_label_missing_mass_local p.targetGroup L := by
  classical
  let W := post_stratified_fixed_label_missing_mass_local p.targetGroup L
  let t := ∑ z, if post_stratified_label_count_local L z = 0
    then pmf_real_mass p.targetGroup z * conditional_group_mean P z else 0
  have hWnonneg : 0 ≤ W := by
    unfold W post_stratified_fixed_label_missing_mass_local
    exact Finset.sum_nonneg fun z _ => by
      split_ifs
      · exact ENNReal.toReal_nonneg
      · exact le_rfl
  have hWle : W ≤ 1 := by
    calc
      W ≤ ∑ z, pmf_real_mass p.targetGroup z := by
        unfold W post_stratified_fixed_label_missing_mass_local
        apply Finset.sum_le_sum
        intro z hz
        split_ifs
        · exact le_rfl
        · exact ENNReal.toReal_nonneg
      _ = 1 := post_stratified_pmf_real_mass_sum_local p.targetGroup
  have ht : |t| ≤ p.meanRadius * W := by
    calc
      |t| ≤ ∑ z, |if post_stratified_label_count_local L z = 0
          then pmf_real_mass p.targetGroup z * conditional_group_mean P z
          else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z, if post_stratified_label_count_local L z = 0
          then pmf_real_mass p.targetGroup z * p.meanRadius else 0 := by
        apply Finset.sum_le_sum
        intro z hz
        by_cases hc : post_stratified_label_count_local L z = 0
        · simp only [hc, if_true]
          rw [abs_mul, abs_of_nonneg
            (show 0 ≤ pmf_real_mass p.targetGroup z from ENNReal.toReal_nonneg)]
          exact mul_le_mul_of_nonneg_left (hP z).2.1 ENNReal.toReal_nonneg
        · simp [hc]
      _ = p.meanRadius * W := by
        unfold W post_stratified_fixed_label_missing_mass_local
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hc : post_stratified_label_count_local L z = 0 <;>
          simp [hc, mul_comm]
  have hb :
      (∑ z, if post_stratified_label_count_local L z = 0 then 0
          else pmf_real_mass p.targetGroup z * conditional_group_mean P z) -
        target_population_mean p.targetGroup P = -t := by
    unfold target_population_mean t
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hc : post_stratified_label_count_local L z = 0 <;>
      simp [hc]
  rw [hb]
  have hRWnonneg : 0 ≤ p.meanRadius * W :=
    mul_nonneg p.meanRadius_nonneg hWnonneg
  have hsquare : |t| ^ 2 ≤ (p.meanRadius * W) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg t) hRWnonneg).2 ht
  have hWW : W ^ 2 ≤ W := by nlinarith
  calc
    (-t) ^ 2 = |t| ^ 2 := by rw [sq_abs]; ring
    _ ≤ (p.meanRadius * W) ^ 2 := hsquare
    _ = p.meanRadius ^ 2 * W ^ 2 := by ring
    _ ≤ p.meanRadius ^ 2 * W :=
      mul_le_mul_of_nonneg_left hWW (sq_nonneg p.meanRadius)

@[blueprint "lem:post-stratified-fixed-label-estimator-variance-local"
  (statement := /-- Conditional on a fixed label array $L$, the variance of the post-stratified coordinate estimator is at most
  $\sigma^2\sum_{z:N_z(L)>0}q_T(z)^2/N_z(L)$. -/)
  (proof := /-- Apply the product-space variance-of-a-sum identity within each source and then across sources. Each coordinate variance is its squared fixed-label coefficient times the conditional group variance, which is at most $sigma^2$. Sum these bounds and use
  \cref{lem:post-stratified-fixed-label-coefficient-square-sum-local}. -/)
  (title := /-- Conditional variance bound at fixed labels -/)
  (latexEnv := "lemma")]
lemma post_stratified_fixed_label_estimator_variance_local
    {K M : ℕ} [NeZero K] [NeZero M] {n : sampling_plan M}
    (p : biased_source_mean_problem K M) (P : conditional_outcome_model K)
    (hP : bounded_conditional_mean_class p P)
    (L : (m : Fin M) → Fin (n m) → Fin K) :
    ProbabilityTheory.variance
        (post_stratified_fixed_label_estimator_local p.targetGroup L)
        (post_stratified_fixed_label_measure_local P L) ≤
      p.varianceBound *
        post_stratified_fixed_label_harmonic_local p.targetGroup L := by
  classical
  let μ (m : Fin M) (i : Fin (n m)) : Measure (Fin K × ℝ) :=
    (P (L m i) : Measure ℝ).map (Prod.mk (L m i))
  let a (m : Fin M) (i : Fin (n m)) : ℝ :=
    pmf_real_mass p.targetGroup (L m i) /
      post_stratified_label_count_local L (L m i)
  let X (m : Fin M) (i : Fin (n m)) (x : Fin K × ℝ) : ℝ :=
    a m i * x.2
  let block (m : Fin M) (d : Fin (n m) → Fin K × ℝ) : ℝ :=
    ∑ i, X m i (d i)
  letI hprob : ∀ m i, IsProbabilityMeasure (μ m i) := fun m i =>
    ⟨by
      unfold μ
      rw [Measure.map_apply_of_aemeasurable measurable_prodMk_left.aemeasurable
        MeasurableSet.univ]
      simp⟩
  have hcoord (m : Fin M) (i : Fin (n m)) :
      MemLp (X m i) 2 (μ m i) := by
    change MemLp ((fun _ : Fin K × ℝ => a m i) * Prod.snd) 2
      ((P (L m i) : Measure ℝ).map (Prod.mk (L m i)))
    rw [MeasureTheory.memLp_map_measure_iff
      (measurable_const.mul measurable_snd).aestronglyMeasurable
      measurable_prodMk_left.aemeasurable]
    simpa [a, Function.comp_def] using
      (hP (L m i)).1.const_mul (a m i)
  have hvarcoord (m : Fin M) (i : Fin (n m)) :
      ProbabilityTheory.variance (X m i) (μ m i) =
        (a m i) ^ 2 * ProbabilityTheory.variance id (P (L m i)) := by
    have hmap :
        ProbabilityTheory.variance (fun x : Fin K × ℝ => x.2) (μ m i) =
          ProbabilityTheory.variance id (P (L m i)) := by
      unfold μ
      rw [ProbabilityTheory.variance_map measurable_snd.aemeasurable
        measurable_prodMk_left.aemeasurable]
      rfl
    unfold X
    rw [ProbabilityTheory.variance_const_mul, hmap]
  have hinner (m : Fin M) :
      ProbabilityTheory.variance (block m) (Measure.pi fun i => μ m i) =
        ∑ i, (a m i) ^ 2 *
          ProbabilityTheory.variance id (P (L m i)) := by
    have hfun : block m = ∑ i, fun d => X m i (d i) := by
      funext d
      simp [block, Finset.sum_apply]
    rw [hfun, ProbabilityTheory.variance_sum_pi
      (μ := fun i => μ m i) (X := fun i => X m i) (fun i => hcoord m i)]
    simp_rw [hvarcoord]
  letI hprobInner : ∀ m, IsProbabilityMeasure
      (Measure.pi fun i => μ m i) := fun m => inferInstance
  have hmemBlock (m : Fin M) :
      MemLp (block m) 2 (Measure.pi fun i => μ m i) := by
    have hsum := MeasureTheory.memLp_finsetSum (Finset.univ : Finset (Fin (n m)))
      (fun i _ => (hcoord m i).comp_measurePreserving
        (measurePreserving_eval (fun i => μ m i) i))
    simpa [block, Finset.sum_apply] using hsum
  have hfun :
      post_stratified_fixed_label_estimator_local p.targetGroup L =
        ∑ m, fun D => block m (D m) := by
    funext D
    simp [post_stratified_fixed_label_estimator_local, block, X, a,
      Finset.sum_apply]
  rw [post_stratified_fixed_label_measure_local, hfun,
    ProbabilityTheory.variance_sum_pi
      (μ := fun m => Measure.pi fun i => μ m i) (X := block) hmemBlock]
  simp_rw [hinner]
  calc
    (∑ m, ∑ i, (a m i) ^ 2 *
        ProbabilityTheory.variance id (P (L m i))) ≤
        ∑ m, ∑ i, (a m i) ^ 2 * p.varianceBound := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hP (L m i)).2.2 (sq_nonneg _)
    _ = p.varianceBound * ∑ m, ∑ i, (a m i) ^ 2 := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = p.varianceBound *
        post_stratified_fixed_label_harmonic_local p.targetGroup L := by
      rw [← post_stratified_fixed_label_coefficient_square_sum_local]

@[blueprint "lem:post-stratified-fixed-label-risk-upper-local"
  (statement := /-- Conditional on a fixed label array $L$, the post-stratified squared risk is at most
  \[
  \sigma^2\sum_{z:N_z(L)>0}\frac{q_T(z)^2}{N_z(L)}
  +R^2\sum_{z:N_z(L)=0}q_T(z).
  \] -/)
  (proof := /-- The fixed-label support identity
  \cref{lem:post-stratified-fixed-label-measure-support-local} and
  \cref{lem:post-stratified-estimator-fixed-labels-local} replace the estimator almost everywhere by its coordinate form. Apply
  \cref{lem:post-stratified-bias-variance-identity-local}, then use
  \cref{lem:post-stratified-fixed-label-estimator-variance-local,lem:post-stratified-fixed-label-estimator-mean-local,lem:post-stratified-fixed-label-bias-bound-local};
  square integrability is
  \cref{lem:post-stratified-fixed-label-estimator-memlp-local}. -/)
  (title := /-- Conditional post-stratified risk bound -/)
  (latexEnv := "lemma")]
lemma post_stratified_fixed_label_risk_upper_local
    {K M : ℕ} [NeZero K] [NeZero M] {n : sampling_plan M}
    (p : biased_source_mean_problem K M) (P : conditional_outcome_model K)
    (hP : bounded_conditional_mean_class p P)
    (L : (m : Fin M) → Fin (n m) → Fin K) :
    (∫ D, (post_stratified_estimator p.targetGroup D -
        target_population_mean p.targetGroup P) ^ 2
      ∂post_stratified_fixed_label_measure_local P L) ≤
      p.varianceBound *
          post_stratified_fixed_label_harmonic_local p.targetGroup L +
        p.meanRadius ^ 2 *
          post_stratified_fixed_label_missing_mass_local p.targetGroup L := by
  classical
  letI hprobCoord : ∀ m i, IsProbabilityMeasure
      ((P (L m i) : Measure ℝ).map (Prod.mk (L m i))) := fun m i =>
    ⟨by
      rw [Measure.map_apply_of_aemeasurable measurable_prodMk_left.aemeasurable
        MeasurableSet.univ]
      simp⟩
  letI hprobInner : ∀ m, IsProbabilityMeasure
      (Measure.pi fun i => (P (L m i) : Measure ℝ).map (Prod.mk (L m i))) :=
    fun m => inferInstance
  letI hprobFixed : IsProbabilityMeasure
      (post_stratified_fixed_label_measure_local P L) := by
    unfold post_stratified_fixed_label_measure_local
    infer_instance
  have hest :
      post_stratified_estimator p.targetGroup =ᵐ[
          post_stratified_fixed_label_measure_local P L]
        post_stratified_fixed_label_estimator_local p.targetGroup L := by
    filter_upwards [post_stratified_fixed_label_measure_support_local P L]
      with D hD
    exact post_stratified_estimator_fixed_labels_local p.targetGroup L D hD
  have hintegral :
      (∫ D, (post_stratified_estimator p.targetGroup D -
          target_population_mean p.targetGroup P) ^ 2
        ∂post_stratified_fixed_label_measure_local P L) =
      ∫ D, (post_stratified_fixed_label_estimator_local p.targetGroup L D -
          target_population_mean p.targetGroup P) ^ 2
        ∂post_stratified_fixed_label_measure_local P L := by
    apply integral_congr_ae
    filter_upwards [hest] with D hD
    rw [hD]
  rw [hintegral,
    post_stratified_bias_variance_identity_local
      (post_stratified_fixed_label_measure_local P L)
      (post_stratified_fixed_label_estimator_local p.targetGroup L)
      (post_stratified_fixed_label_estimator_memlp_local p P hP L)
      (target_population_mean p.targetGroup P)]
  apply add_le_add
  · exact post_stratified_fixed_label_estimator_variance_local p P hP L
  · rw [post_stratified_fixed_label_estimator_mean_local p P hP L]
    exact post_stratified_fixed_label_bias_bound_local p P hP L

@[blueprint "def:post-stratified-label-harmonic-expectation-local"
  (statement := /-- The reciprocal-count contribution for a plan is the label-law expectation of its fixed-label harmonic term. -/)
  (title := /-- Expected reciprocal-count harmonic term -/)
  (latexEnv := "definition")]
noncomputable def post_stratified_label_harmonic_expectation_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M) : ℝ :=
  ∑ L : (m : Fin M) → Fin (n m) → Fin K,
    (post_stratified_label_weight_local p n L : ℝ) *
      post_stratified_fixed_label_harmonic_local p.targetGroup L

@[blueprint "def:post-stratified-label-missing-expectation-local"
  (statement := /-- The missing-group contribution for a plan is the label-law expectation of its fixed-label missing target mass. -/)
  (title := /-- Expected missing target mass -/)
  (latexEnv := "definition")]
noncomputable def post_stratified_label_missing_expectation_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M) : ℝ :=
  ∑ L : (m : Fin M) → Fin (n m) → Fin K,
    (post_stratified_label_weight_local p n L : ℝ) *
      post_stratified_fixed_label_missing_mass_local p.targetGroup L

@[blueprint "lem:post-stratified-finite-plan-risk-upper-local"
  (statement := /-- For every plan $n$ and bounded conditional model $P$, the post-stratified risk is at most $sigma^2$ times the expected reciprocal-count harmonic term plus $R^2$ times the expected missing target mass. -/)
  (proof := /-- Expand the sampling law by
  \cref{lem:post-stratified-sampling-law-mixture-local}. The squared loss is integrable under each fixed-label law by
  \cref{lem:post-stratified-fixed-label-estimator-memlp-local,lem:post-stratified-fixed-label-measure-support-local}, the support identity, and
  \cref{lem:post-stratified-estimator-fixed-labels-local}. Linearity over the finite mixture and
  \cref{lem:post-stratified-fixed-label-risk-upper-local} then give the asserted weighted sum. -/)
  (title := /-- Finite-plan post-stratified risk bound -/)
  (latexEnv := "lemma")]
lemma post_stratified_finite_plan_risk_upper_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (P : conditional_outcome_model K) (hP : bounded_conditional_mean_class p P) :
    population_mean_risk p n (post_stratified_estimator p.targetGroup) P ≤
      p.varianceBound * post_stratified_label_harmonic_expectation_local p n +
        p.meanRadius ^ 2 * post_stratified_label_missing_expectation_local p n := by
  classical
  let Label := (m : Fin M) → Fin (n m) → Fin K
  let loss : sampled_dataset K M n → ℝ := fun D =>
    (post_stratified_estimator p.targetGroup D -
      target_population_mean p.targetGroup P) ^ 2
  letI hprobCoord : ∀ (L : Label) m i, IsProbabilityMeasure
      ((P (L m i) : Measure ℝ).map (Prod.mk (L m i))) := fun L m i =>
    ⟨by
      rw [Measure.map_apply_of_aemeasurable measurable_prodMk_left.aemeasurable
        MeasurableSet.univ]
      simp⟩
  letI hprobInner : ∀ (L : Label) m, IsProbabilityMeasure
      (Measure.pi fun i => (P (L m i) : Measure ℝ).map (Prod.mk (L m i))) :=
    fun L m => inferInstance
  letI hprobFixed : ∀ L : Label, IsProbabilityMeasure
      (post_stratified_fixed_label_measure_local P L) := fun L => by
    unfold post_stratified_fixed_label_measure_local
    infer_instance
  have hloss (L : Label) :
      Integrable loss (post_stratified_fixed_label_measure_local P L) := by
    have hest :
        post_stratified_estimator p.targetGroup =ᵐ[
            post_stratified_fixed_label_measure_local P L]
          post_stratified_fixed_label_estimator_local p.targetGroup L := by
      filter_upwards [post_stratified_fixed_label_measure_support_local P L]
        with D hD
      exact post_stratified_estimator_fixed_labels_local p.targetGroup L D hD
    have herr : MemLp
        (fun D => post_stratified_fixed_label_estimator_local p.targetGroup L D -
          target_population_mean p.targetGroup P) 2
        (post_stratified_fixed_label_measure_local P L) :=
      (post_stratified_fixed_label_estimator_memlp_local p P hP L).sub
        (MeasureTheory.memLp_const (target_population_mean p.targetGroup P))
    apply herr.integrable_sq.congr
    filter_upwards [hest] with D hD
    simp only [loss]
    rw [hD]
  rw [population_mean_risk, post_stratified_sampling_law_mixture_local p n P]
  change (∫ D, loss D ∂(∑ L : Label,
    post_stratified_label_weight_local p n L •
      post_stratified_fixed_label_measure_local P L)) ≤ _
  rw [MeasureTheory.integral_finsetSum_measure
    (fun L _ => (hloss L).smul_measure_nnreal)]
  simp_rw [MeasureTheory.integral_smul_nnreal_measure]
  simp only [NNReal.smul_def]
  calc
    (∑ L : Label, (post_stratified_label_weight_local p n L : ℝ) *
        ∫ D, loss D ∂post_stratified_fixed_label_measure_local P L) ≤
      ∑ L : Label, (post_stratified_label_weight_local p n L : ℝ) *
        (p.varianceBound *
            post_stratified_fixed_label_harmonic_local p.targetGroup L +
          p.meanRadius ^ 2 *
            post_stratified_fixed_label_missing_mass_local p.targetGroup L) := by
      apply Finset.sum_le_sum
      intro L hL
      exact mul_le_mul_of_nonneg_left
        (post_stratified_fixed_label_risk_upper_local p P hP L)
        (post_stratified_label_weight_local p n L).2
    _ = p.varianceBound * post_stratified_label_harmonic_expectation_local p n +
        p.meanRadius ^ 2 * post_stratified_label_missing_expectation_local p n := by
      unfold post_stratified_label_harmonic_expectation_local
        post_stratified_label_missing_expectation_local
      simp only [Finset.mul_sum]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro L hL
        ring
      · apply Finset.sum_congr rfl
        intro L hL
        ring

@[blueprint "def:post-stratified-expected-group-count-local"
  (statement := /-- The expected count in group $z$ under plan $n$ is
  $\lambda_z(n)=\sum_m n_mq_{S,m}(z)$. -/)
  (title := /-- Expected group count of a plan -/)
  (latexEnv := "definition")]
noncomputable def post_stratified_expected_group_count_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (z : Fin K) : ℝ :=
  ∑ m, n m * pmf_real_mass (p.sourceGroup m) z

@[blueprint "lem:post-stratified-label-count-pgf-local"
  (statement := /-- For every group $z$ and real $t$, the probability-generating polynomial of its sampled count under the finite label law is
  \[
  \sum_L w_n(L)t^{N_z(L)}
  =\prod_m\bigl(1-q_{S,m}(z)+q_{S,m}(z)t\bigr)^{n_m}.
  \] -/)
  (proof := /-- Expand the label weight and the power of the double count sum into coordinatewise products. Apply finite distributivity over all label functions first across sources and then within each source. The inner sum over a group label is $1-q_{S,m}(z)+q_{S,m}(z)t$ by
  \cref{lem:post-stratified-pmf-real-mass-sum-local}. -/)
  (title := /-- Probability-generating polynomial of a sampled group count -/)
  (latexEnv := "lemma")]
lemma post_stratified_label_count_pgf_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (z : Fin K) (t : ℝ) :
    (∑ L : (m : Fin M) → Fin (n m) → Fin K,
      (post_stratified_label_weight_local p n L : ℝ) *
        t ^ post_stratified_label_count_local L z) =
      ∏ m, (1 - pmf_real_mass (p.sourceGroup m) z +
        pmf_real_mass (p.sourceGroup m) z * t) ^ n m := by
  classical
  have hsource (m : Fin M) :
      (∑ k : Fin K, pmf_real_mass (p.sourceGroup m) k *
        t ^ (if k = z then 1 else 0)) =
        1 - pmf_real_mass (p.sourceGroup m) z +
          pmf_real_mass (p.sourceGroup m) z * t := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ z)]
    have hoff :
        (∑ k ∈ Finset.univ.erase z,
          pmf_real_mass (p.sourceGroup m) k *
            t ^ (if k = z then 1 else 0)) =
          ∑ k ∈ Finset.univ.erase z, pmf_real_mass (p.sourceGroup m) k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkz : k ≠ z := Finset.ne_of_mem_erase hk
      simp [hkz]
    rw [hoff]
    simp only [if_pos, pow_one]
    have hsum := post_stratified_pmf_real_mass_sum_local (p.sourceGroup m)
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ z)] at hsum
    linarith
  calc
    (∑ L : (m : Fin M) → Fin (n m) → Fin K,
      (post_stratified_label_weight_local p n L : ℝ) *
        t ^ post_stratified_label_count_local L z) =
      ∑ L : (m : Fin M) → Fin (n m) → Fin K,
        ∏ m, ∏ i, pmf_real_mass (p.sourceGroup m) (L m i) *
          t ^ (if L m i = z then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro L hL
      unfold post_stratified_label_weight_local
        post_stratified_label_count_local pmf_real_mass
      push_cast
      rw [← Finset.prod_pow_eq_pow_sum Finset.univ
        (fun m => ∑ i, if L m i = z then 1 else 0) t]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro m hm
      rw [← Finset.prod_pow_eq_pow_sum Finset.univ
        (fun i => if L m i = z then 1 else 0) t]
      rw [Finset.prod_mul_distrib]
    _ = ∏ m, ∑ Lm : Fin (n m) → Fin K,
        ∏ i, pmf_real_mass (p.sourceGroup m) (Lm i) *
          t ^ (if Lm i = z then 1 else 0) := by
      rw [Fintype.prod_sum]
    _ = ∏ m, ∏ i : Fin (n m), ∑ k : Fin K,
        pmf_real_mass (p.sourceGroup m) k *
          t ^ (if k = z then 1 else 0) := by
      apply Finset.prod_congr rfl
      intro m hm
      rw [Fintype.prod_sum]
    _ = ∏ m, ∏ _i : Fin (n m),
        (1 - pmf_real_mass (p.sourceGroup m) z +
          pmf_real_mass (p.sourceGroup m) z * t) := by
      simp_rw [hsource]
    _ = ∏ m, (1 - pmf_real_mass (p.sourceGroup m) z +
        pmf_real_mass (p.sourceGroup m) z * t) ^ n m := by
      apply Finset.prod_congr rfl
      intro m hm
      simp

@[blueprint "lem:post-stratified-label-count-pgf-upper-local"
  (statement := /-- For $0\le t\le1$, the probability-generating polynomial of a sampled group count is at most $\exp(-\lambda_z(n)(1-t))$. -/)
  (proof := /-- Rewrite the polynomial by \cref{lem:post-stratified-label-count-pgf-local}. Each source factor is nonnegative and is bounded by the exponential of its negative missing-mass contribution, using $1-x\le e^{-x}$. Multiplying these bounds and collecting the exponents gives the claim. -/)
  (title := /-- Exponential upper bound for the group-count generating polynomial -/)
  (latexEnv := "lemma")]
lemma post_stratified_label_count_pgf_upper_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (z : Fin K) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑ L : (m : Fin M) → Fin (n m) → Fin K,
      (post_stratified_label_weight_local p n L : ℝ) *
        t ^ post_stratified_label_count_local L z) ≤
      Real.exp (-post_stratified_expected_group_count_local p n z * (1 - t)) := by
  classical
  rw [post_stratified_label_count_pgf_local]
  have hq0 (m : Fin M) : 0 ≤ pmf_real_mass (p.sourceGroup m) z :=
    ENNReal.toReal_nonneg
  have hq1 (m : Fin M) : pmf_real_mass (p.sourceGroup m) z ≤ 1 := by
    unfold pmf_real_mass
    have hone : (1 : ENNReal) ≠ ⊤ := by simp
    simpa using ENNReal.toReal_mono hone (PMF.coe_le_one (p.sourceGroup m) z)
  have hbase (m : Fin M) :
      0 ≤ 1 - pmf_real_mass (p.sourceGroup m) z +
        pmf_real_mass (p.sourceGroup m) z * t := by
    nlinarith [mul_nonneg (hq0 m) ht0,
      mul_nonneg (sub_nonneg.2 (hq1 m)) (show 0 ≤ 1 from zero_le_one)]
  calc
    (∏ m, (1 - pmf_real_mass (p.sourceGroup m) z +
        pmf_real_mass (p.sourceGroup m) z * t) ^ n m) ≤
      ∏ m, (Real.exp (-pmf_real_mass (p.sourceGroup m) z * (1 - t))) ^ n m := by
        apply Finset.prod_le_prod
        · intro m hm
          exact pow_nonneg (hbase m) _
        · intro m hm
          apply pow_le_pow_left₀ (hbase m)
          calc
            1 - pmf_real_mass (p.sourceGroup m) z +
                pmf_real_mass (p.sourceGroup m) z * t =
              1 - pmf_real_mass (p.sourceGroup m) z * (1 - t) := by ring
            _ ≤ Real.exp (-(pmf_real_mass (p.sourceGroup m) z * (1 - t))) :=
              Real.one_sub_le_exp_neg _
            _ = Real.exp (-pmf_real_mass (p.sourceGroup m) z * (1 - t)) := by
              congr 1
              ring
    _ = Real.exp (-post_stratified_expected_group_count_local p n z * (1 - t)) := by
      simp_rw [← Real.exp_nat_mul]
      rw [← Real.exp_sum]
      congr 1
      unfold post_stratified_expected_group_count_local
      push_cast
      calc
        (∑ m, (n m : ℝ) *
            (-pmf_real_mass (p.sourceGroup m) z * (1 - t))) =
          ∑ m, (-(n m * pmf_real_mass (p.sourceGroup m) z)) * (1 - t) := by
            apply Finset.sum_congr rfl
            intro m hm
            ring
        _ = (-(∑ m, n m * pmf_real_mass (p.sourceGroup m) z)) * (1 - t) := by
          rw [← Finset.sum_mul]
          congr 1
          rw [← Finset.sum_neg_distrib]

@[blueprint "lem:post-stratified-exponential-integral-bounds-local"
  (statement := /-- For every $\lambda>0$, the exponential comparison kernel on $[0,1]$ satisfies
  \[
  \int_0^1 e^{-\lambda(1-t)}\,dt\le\lambda^{-1},\qquad
  \int_0^1(1-t)e^{-\lambda(1-t)}\,dt\le\lambda^{-2}.
  \] -/)
  (proof := /-- The functions $\lambda^{-1}e^{-\lambda(1-t)}$ and $e^{-\lambda(1-t)}((1-t)/\lambda+1/\lambda^2)$ are antiderivatives of the two integrands. The fundamental theorem of calculus gives each integral as its value at one minus its value at zero; discarding the nonnegative exponential endpoint term gives the displayed upper bounds. -/)
  (title := /-- Exponential kernel integral bounds -/)
  (latexEnv := "lemma")]
lemma post_stratified_exponential_integral_bounds_local (lam : ℝ) (hlam : 0 < lam) :
    (∫ t in (0 : ℝ)..1, Real.exp (-lam * (1 - t))) ≤ 1 / lam ∧
      (∫ t in (0 : ℝ)..1, (1 - t) * Real.exp (-lam * (1 - t))) ≤
        1 / lam ^ 2 := by
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  let F : ℝ → ℝ := fun t => Real.exp (-lam * (1 - t)) / lam
  have hFderiv (t : ℝ) : HasDerivAt F (Real.exp (-lam * (1 - t))) t := by
    have hg : HasDerivAt (fun x : ℝ => -lam * (1 - x)) lam t := by
      have hfun : (fun x : ℝ => -lam * (1 - x)) = fun x => x * lam + (-lam) := by
        funext x
        ring
      rw [hfun]
      simpa using ((hasDerivAt_id t).mul_const lam).add_const (-lam)
    have he : HasDerivAt (fun x : ℝ => Real.exp (-lam * (1 - x)))
        (Real.exp (-lam * (1 - t)) * lam) t := by
      convert (Real.hasDerivAt_exp _).comp t hg using 1 <;> first | rfl
    dsimp only [F]
    have hd := he.div_const lam
    convert hd using 1
    all_goals first | rfl | field_simp
  have hFint : (∫ t in (0 : ℝ)..1, Real.exp (-lam * (1 - t))) =
      F 1 - F 0 := by
    apply intervalIntegral.integral_deriv_eq_sub' F
    · funext t
      exact (hFderiv t).deriv
    · intro t ht
      exact (hFderiv t).differentiableAt
    · fun_prop
  let G : ℝ → ℝ := fun t => Real.exp (-lam * (1 - t)) *
    ((1 - t) / lam + 1 / lam ^ 2)
  have hGderiv (t : ℝ) :
      HasDerivAt G ((1 - t) * Real.exp (-lam * (1 - t))) t := by
    have hg : HasDerivAt (fun x : ℝ => -lam * (1 - x)) lam t := by
      have hfun : (fun x : ℝ => -lam * (1 - x)) = fun x => x * lam + (-lam) := by
        funext x
        ring
      rw [hfun]
      simpa using ((hasDerivAt_id t).mul_const lam).add_const (-lam)
    have he : HasDerivAt (fun x : ℝ => Real.exp (-lam * (1 - x)))
        (Real.exp (-lam * (1 - t)) * lam) t := by
      convert (Real.hasDerivAt_exp _).comp t hg using 1 <;> first | rfl
    have hh : HasDerivAt (fun x : ℝ => (1 - x) / lam + 1 / lam ^ 2)
        (-1 / lam) t := by
      have hbase := ((hasDerivAt_const t 1).sub (hasDerivAt_id t)).div_const lam
      have hadd := hbase.add_const (1 / lam ^ 2)
      simpa using hadd
    dsimp only [G]
    convert he.mul hh using 1
    all_goals first | rfl | (field_simp; ring)
  have hGint : (∫ t in (0 : ℝ)..1,
      (1 - t) * Real.exp (-lam * (1 - t))) = G 1 - G 0 := by
    apply intervalIntegral.integral_deriv_eq_sub' G
    · funext t
      exact (hGderiv t).deriv
    · intro t ht
      exact (hGderiv t).differentiableAt
    · fun_prop
  constructor
  · rw [hFint]
    dsimp only [F]
    have hexp : 0 ≤ Real.exp (-lam) / lam :=
      div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt hlam)
    simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, one_div, one_mul,
      sub_zero, mul_one]
    linarith
  · rw [hGint]
    dsimp only [G]
    have hexp : 0 ≤ Real.exp (-lam) * (1 / lam + 1 / lam ^ 2) := by
      positivity
    simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, zero_div, zero_add,
      one_mul, sub_zero, mul_one]
    linarith

@[blueprint "lem:post-stratified-reciprocal-count-elementary-local"
  (statement := /-- For every natural number $k$,
  \[
  \mathbf 1_{\{k>0\}}k^{-1}\le (k+1)^{-1}+3((k+1)(k+2))^{-1},
  \qquad
  \mathbf 1_{\{k=0\}}\le2((k+1)(k+2))^{-1}.
  \] -/)
  (proof := /-- If $k=0$, both assertions are immediate. If $k\ge1$, clear the positive denominators; the first inequality reduces to a nonnegative polynomial in $k$, and the second has zero left-hand side. -/)
  (title := /-- Elementary reciprocal-count inequalities -/)
  (latexEnv := "lemma")]
lemma post_stratified_reciprocal_count_elementary_local (k : ℕ) :
    (if k = 0 then (0 : ℝ) else 1 / k) ≤
        1 / (k + 1) + 3 / ((k + 1) * (k + 2)) ∧
      (if k = 0 then (1 : ℝ) else 0) ≤
        2 / ((k + 1) * (k + 2)) := by
  by_cases hk : k = 0
  · subst k
    norm_num
  · have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hkone : (1 : ℝ) ≤ k := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.2 hk)
    simp only [hk, ↓reduceIte]
    constructor
    · field_simp
      nlinarith
    · positivity

@[blueprint "lem:post-stratified-label-count-integral-identities-local"
  (statement := /-- Under the finite label law, the expectations of $(N_z+1)^{-1}$ and $((N_z+1)(N_z+2))^{-1}$ are respectively the integrals on $[0,1]$ of the count generating polynomial and of $(1-t)$ times that polynomial. -/)
  (proof := /-- Interchange each finite sum with the interval integral. The identities then follow termwise from $\int_0^1t^k\,dt=(k+1)^{-1}$ and from subtracting the corresponding formulas for powers $k$ and $k+1$. -/)
  (title := /-- Integral identities for regularized reciprocal counts -/)
  (latexEnv := "lemma")]
lemma post_stratified_label_count_integral_identities_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M) (z : Fin K) :
    (∑ L : (m : Fin M) → Fin (n m) → Fin K,
      (post_stratified_label_weight_local p n L : ℝ) /
        (post_stratified_label_count_local L z + 1)) =
      ∫ t in (0 : ℝ)..1, ∑ L : (m : Fin M) → Fin (n m) → Fin K,
        (post_stratified_label_weight_local p n L : ℝ) *
          t ^ post_stratified_label_count_local L z ∧
    (∑ L : (m : Fin M) → Fin (n m) → Fin K,
      (post_stratified_label_weight_local p n L : ℝ) /
        ((post_stratified_label_count_local L z + 1) *
          (post_stratified_label_count_local L z + 2))) =
      ∫ t in (0 : ℝ)..1, (1 - t) *
        ∑ L : (m : Fin M) → Fin (n m) → Fin K,
          (post_stratified_label_weight_local p n L : ℝ) *
            t ^ post_stratified_label_count_local L z := by
  classical
  constructor
  · rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro L hL
      rw [intervalIntegral.integral_const_mul, integral_pow]
      push_cast
      rw [div_eq_mul_inv]
      simp
    · intro i hi
      exact (intervalIntegral.intervalIntegrable_pow
        (n := post_stratified_label_count_local i z)).const_mul _
  · rw [show (fun t : ℝ => (1 - t) *
        ∑ L : (m : Fin M) → Fin (n m) → Fin K,
          (post_stratified_label_weight_local p n L : ℝ) *
            t ^ post_stratified_label_count_local L z) =
        fun t => ∑ L : (m : Fin M) → Fin (n m) → Fin K,
          (post_stratified_label_weight_local p n L : ℝ) *
            ((1 - t) * t ^ post_stratified_label_count_local L z) by
      funext t
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro L hL
      ring]
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro L hL
      rw [intervalIntegral.integral_const_mul]
      simp_rw [sub_mul, one_mul, ← pow_succ']
      rw [intervalIntegral.integral_sub, integral_pow, integral_pow]
      push_cast
      field_simp
      ring
      all_goals
        exact intervalIntegral.intervalIntegrable_pow (n := _)
    · intro i hi
      exact (by fun_prop : Continuous (fun t : ℝ =>
        (post_stratified_label_weight_local p n i : ℝ) *
          ((1 - t) * t ^ post_stratified_label_count_local i z))).intervalIntegrable 0 1

@[blueprint "lem:post-stratified-label-reciprocal-bounds-local"
  (statement := /-- If the expected count $\lambda_z(n)$ is positive, then under the finite label law
  \[
  \mathbb E[\mathbf 1_{\{N_z>0\}}/N_z]\le\lambda_z^{-1}+3\lambda_z^{-2},
  \qquad
  \Pr\{N_z=0\}\le2\lambda_z^{-2}.
  \] -/)
  (proof := /-- Apply the pointwise inequalities of \cref{lem:post-stratified-reciprocal-count-elementary-local} and sum with the nonnegative label weights. By \cref{lem:post-stratified-label-count-integral-identities-local}, the two regularized reciprocal moments are integrals of the probability-generating polynomial. Bound that polynomial by \cref{lem:post-stratified-label-count-pgf-upper-local} and use \cref{lem:post-stratified-exponential-integral-bounds-local}. -/)
  (title := /-- Reciprocal and missing-count bounds under the label law -/)
  (latexEnv := "lemma")]
lemma post_stratified_label_reciprocal_bounds_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M) (z : Fin K)
    (hlam : 0 < post_stratified_expected_group_count_local p n z) :
    (∑ L : (m : Fin M) → Fin (n m) → Fin K,
      (post_stratified_label_weight_local p n L : ℝ) *
        (if post_stratified_label_count_local L z = 0 then 0
          else (1 : ℝ) / (post_stratified_label_count_local L z : ℝ))) ≤
        1 / post_stratified_expected_group_count_local p n z +
          3 / post_stratified_expected_group_count_local p n z ^ 2 ∧
    (∑ L : (m : Fin M) → Fin (n m) → Fin K,
      (post_stratified_label_weight_local p n L : ℝ) *
        (if post_stratified_label_count_local L z = 0 then (1 : ℝ) else 0)) ≤
          2 / post_stratified_expected_group_count_local p n z ^ 2 := by
  classical
  let G : ℝ → ℝ := fun t =>
    ∑ L : (m : Fin M) → Fin (n m) → Fin K,
      (post_stratified_label_weight_local p n L : ℝ) *
        t ^ post_stratified_label_count_local L z
  have hGcont : Continuous G := by
    dsimp only [G]
    fun_prop
  have hexpcont : Continuous (fun t : ℝ =>
      Real.exp (-post_stratified_expected_group_count_local p n z * (1 - t))) := by
    fun_prop
  have hmono1 : (∫ t in (0 : ℝ)..1, G t) ≤
      ∫ t in (0 : ℝ)..1,
        Real.exp (-post_stratified_expected_group_count_local p n z * (1 - t)) := by
    apply intervalIntegral.integral_mono_on zero_le_one
      (hGcont.intervalIntegrable 0 1) (hexpcont.intervalIntegrable 0 1)
    intro t ht
    exact post_stratified_label_count_pgf_upper_local p n z t ht.1 ht.2
  have hweightedcont : Continuous (fun t : ℝ => (1 - t) * G t) := by
    fun_prop
  have hexpweightedcont : Continuous (fun t : ℝ =>
      (1 - t) * Real.exp
        (-post_stratified_expected_group_count_local p n z * (1 - t))) := by
    fun_prop
  have hmono2 : (∫ t in (0 : ℝ)..1, (1 - t) * G t) ≤
      ∫ t in (0 : ℝ)..1, (1 - t) *
        Real.exp (-post_stratified_expected_group_count_local p n z * (1 - t)) := by
    apply intervalIntegral.integral_mono_on zero_le_one
      (hweightedcont.intervalIntegrable 0 1)
      (hexpweightedcont.intervalIntegrable 0 1)
    intro t ht
    exact mul_le_mul_of_nonneg_left
      (post_stratified_label_count_pgf_upper_local p n z t ht.1 ht.2)
      (sub_nonneg.2 ht.2)
  have hexpbounds := post_stratified_exponential_integral_bounds_local
    (post_stratified_expected_group_count_local p n z) hlam
  have hreg1 :
      (∑ L : (m : Fin M) → Fin (n m) → Fin K,
        (post_stratified_label_weight_local p n L : ℝ) /
          (post_stratified_label_count_local L z + 1)) ≤
        1 / post_stratified_expected_group_count_local p n z := by
    rw [(post_stratified_label_count_integral_identities_local p n z).1]
    exact le_trans hmono1 hexpbounds.1
  have hreg2 :
      (∑ L : (m : Fin M) → Fin (n m) → Fin K,
        (post_stratified_label_weight_local p n L : ℝ) /
          ((post_stratified_label_count_local L z + 1) *
            (post_stratified_label_count_local L z + 2))) ≤
        1 / post_stratified_expected_group_count_local p n z ^ 2 := by
    rw [(post_stratified_label_count_integral_identities_local p n z).2]
    exact le_trans hmono2 hexpbounds.2
  constructor
  · calc
      (∑ L : (m : Fin M) → Fin (n m) → Fin K,
          (post_stratified_label_weight_local p n L : ℝ) *
          (if post_stratified_label_count_local L z = 0 then 0
            else (1 : ℝ) / (post_stratified_label_count_local L z : ℝ))) ≤
        ∑ L : (m : Fin M) → Fin (n m) → Fin K,
          (post_stratified_label_weight_local p n L : ℝ) *
            (1 / (post_stratified_label_count_local L z + 1) +
              3 / ((post_stratified_label_count_local L z + 1) *
                (post_stratified_label_count_local L z + 2))) := by
          apply Finset.sum_le_sum
          intro L hL
          exact mul_le_mul_of_nonneg_left
            (post_stratified_reciprocal_count_elementary_local
              (post_stratified_label_count_local L z)).1
            (post_stratified_label_weight_local p n L).2
      _ = (∑ L : (m : Fin M) → Fin (n m) → Fin K,
          (post_stratified_label_weight_local p n L : ℝ) /
            (post_stratified_label_count_local L z + 1)) +
          3 * ∑ L : (m : Fin M) → Fin (n m) → Fin K,
            (post_stratified_label_weight_local p n L : ℝ) /
              ((post_stratified_label_count_local L z + 1) *
                (post_stratified_label_count_local L z + 2)) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          congr 1
          · apply Finset.sum_congr rfl
            intro L hL
            ring
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro L hL
            ring
      _ ≤ 1 / post_stratified_expected_group_count_local p n z +
          3 * (1 / post_stratified_expected_group_count_local p n z ^ 2) :=
        add_le_add hreg1 (mul_le_mul_of_nonneg_left hreg2 (by norm_num))
      _ = 1 / post_stratified_expected_group_count_local p n z +
          3 / post_stratified_expected_group_count_local p n z ^ 2 := by ring
  · calc
      (∑ L : (m : Fin M) → Fin (n m) → Fin K,
        (post_stratified_label_weight_local p n L : ℝ) *
          (if post_stratified_label_count_local L z = 0 then (1 : ℝ) else 0)) ≤
        ∑ L : (m : Fin M) → Fin (n m) → Fin K,
          (post_stratified_label_weight_local p n L : ℝ) *
            (2 / ((post_stratified_label_count_local L z + 1) *
              (post_stratified_label_count_local L z + 2))) := by
          apply Finset.sum_le_sum
          intro L hL
          exact mul_le_mul_of_nonneg_left
            (post_stratified_reciprocal_count_elementary_local
              (post_stratified_label_count_local L z)).2
            (post_stratified_label_weight_local p n L).2
      _ = 2 * ∑ L : (m : Fin M) → Fin (n m) → Fin K,
          (post_stratified_label_weight_local p n L : ℝ) /
            ((post_stratified_label_count_local L z + 1) *
              (post_stratified_label_count_local L z + 2)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro L hL
          ring
      _ ≤ 2 * (1 / post_stratified_expected_group_count_local p n z ^ 2) :=
        mul_le_mul_of_nonneg_left hreg2 (by norm_num)
      _ = 2 / post_stratified_expected_group_count_local p n z ^ 2 := by ring

@[blueprint "def:post-stratified-plan-harmonic-local"
  (statement := /-- For a plan $n$ and target mass vector $q$, let $H(n,q)=\sum_{z:q_z\ne0}q_z^2/\lambda_z(n)$. -/)
  (title := /-- Harmonic quantity for the post-stratified upper bound -/)
  (latexEnv := "definition")]
noncomputable def post_stratified_plan_harmonic_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) : ℝ :=
  ∑ z, if q z = 0 then 0
    else (q z) ^ 2 / post_stratified_expected_group_count_local p n z

@[blueprint "def:post-stratified-plan-second-order-local"
  (statement := /-- The finite-plan second-order term is
  \[
  S(n)=\sum_{z:q_T(z)\ne0}
  \frac{3\sigma^2q_T(z)^2+2R^2q_T(z)}{\lambda_z(n)^2}.
  \] -/)
  (title := /-- Second-order post-stratified plan term -/)
  (latexEnv := "definition")]
noncomputable def post_stratified_plan_second_order_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M) : ℝ :=
  ∑ z, if pmf_real_mass p.targetGroup z = 0 then 0 else
    (3 * p.varianceBound * (pmf_real_mass p.targetGroup z) ^ 2 +
      2 * p.meanRadius ^ 2 * pmf_real_mass p.targetGroup z) /
        post_stratified_expected_group_count_local p n z ^ 2

@[blueprint "lem:post-stratified-expected-group-count-positive-local"
  (statement := /-- If a nonempty plan supports a positive target coordinate, then its expected count in that coordinate is positive. -/)
  (proof := /-- Expand the source-mixture mass in the support hypothesis as the expected group count divided by the positive total sample size. -/)
  (title := /-- Positive expected count on supported target coordinates -/)
  (latexEnv := "lemma")]
lemma post_stratified_expected_group_count_positive_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) (hn : plan_total_samples n ≠ 0)
    (hsupp : target_supported_by_plan p n q)
    (z : Fin K) (hq : 0 < q z) :
    0 < post_stratified_expected_group_count_local p n z := by
  have hs := hsupp z hq
  unfold source_mixture_mass at hs
  rw [if_neg hn] at hs
  unfold post_stratified_expected_group_count_local
  push_cast at hs
  have hN : 0 < (plan_total_samples n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  rcases div_pos_iff.mp hs with h | h
  · exact h.1
  · linarith [h.2, hN]

@[blueprint "lem:post-stratified-finite-plan-moment-upper-local"
  (statement := /-- For a nonempty target-supporting plan, the expected reciprocal-count and missing-group terms are bounded by their harmonic leading terms plus the explicit inverse-square corrections encoded in \cref{def:post-stratified-plan-second-order-local}. Consequently the risk is at most $\sigma^2H(n,q_T)+S(n)$. -/)
  (proof := /-- Interchange the finite sums over label configurations and groups. Coordinates of zero target mass vanish. At every positive target coordinate, support gives a positive expected count by \cref{lem:post-stratified-expected-group-count-positive-local}, so \cref{lem:post-stratified-label-reciprocal-bounds-local} applies. Multiply its two inequalities by the appropriate nonnegative target coefficients, sum over groups, and combine with the finite-plan risk inequality \cref{lem:post-stratified-finite-plan-risk-upper-local}. -/)
  (title := /-- Harmonic plus second-order finite-plan risk bound -/)
  (latexEnv := "lemma")]
lemma post_stratified_finite_plan_moment_upper_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (P : conditional_outcome_model K) (hP : bounded_conditional_mean_class p P)
    (hn : plan_total_samples n ≠ 0)
    (hsupp : target_supported_by_plan p n
      (fun z => pmf_real_mass p.targetGroup z)) :
    population_mean_risk p n (post_stratified_estimator p.targetGroup) P ≤
      p.varianceBound * post_stratified_plan_harmonic_local p n
        (fun z => pmf_real_mass p.targetGroup z) +
        post_stratified_plan_second_order_local p n := by
  classical
  let q : Fin K → ℝ := fun z => pmf_real_mass p.targetGroup z
  have hharm : post_stratified_label_harmonic_expectation_local p n ≤
      post_stratified_plan_harmonic_local p n q +
        3 * ∑ z, if q z = 0 then 0 else
          (q z) ^ 2 / post_stratified_expected_group_count_local p n z ^ 2 := by
    unfold post_stratified_label_harmonic_expectation_local
      post_stratified_fixed_label_harmonic_local
      post_stratified_plan_harmonic_local
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z hz
    by_cases hqz : q z = 0
    · simp [q, hqz]
    · have hqpos : 0 < q z := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hqz)
      have hlam := post_stratified_expected_group_count_positive_local
        p n q hn hsupp z hqpos
      have hb := (post_stratified_label_reciprocal_bounds_local p n z hlam).1
      calc
        (∑ L, (post_stratified_label_weight_local p n L : ℝ) *
          (if post_stratified_label_count_local L z = 0 then 0
            else q z ^ 2 / (post_stratified_label_count_local L z : ℝ))) =
          q z ^ 2 * ∑ L, (post_stratified_label_weight_local p n L : ℝ) *
            (if post_stratified_label_count_local L z = 0 then 0
              else (1 : ℝ) / (post_stratified_label_count_local L z : ℝ)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro L hL
                split_ifs <;> ring
        _ ≤ q z ^ 2 *
            (1 / post_stratified_expected_group_count_local p n z +
              3 / post_stratified_expected_group_count_local p n z ^ 2) :=
          mul_le_mul_of_nonneg_left hb (sq_nonneg _)
        _ = (if q z = 0 then 0 else
              q z ^ 2 / post_stratified_expected_group_count_local p n z) +
            3 * (if q z = 0 then 0 else
              q z ^ 2 / post_stratified_expected_group_count_local p n z ^ 2) := by
          rw [if_neg hqz, if_neg hqz]
          ring
  have hmiss : post_stratified_label_missing_expectation_local p n ≤
      2 * ∑ z, if q z = 0 then 0 else
        q z / post_stratified_expected_group_count_local p n z ^ 2 := by
    unfold post_stratified_label_missing_expectation_local
      post_stratified_fixed_label_missing_mass_local
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro z hz
    by_cases hqz : q z = 0
    · simp [q, hqz]
    · have hqpos : 0 < q z := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hqz)
      have hlam := post_stratified_expected_group_count_positive_local
        p n q hn hsupp z hqpos
      have hb := (post_stratified_label_reciprocal_bounds_local p n z hlam).2
      calc
        (∑ L, (post_stratified_label_weight_local p n L : ℝ) *
          (if post_stratified_label_count_local L z = 0 then q z else 0)) =
          q z * ∑ L, (post_stratified_label_weight_local p n L : ℝ) *
            (if post_stratified_label_count_local L z = 0 then (1 : ℝ) else 0) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro L hL
                split_ifs <;> ring
        _ ≤ q z * (2 / post_stratified_expected_group_count_local p n z ^ 2) :=
          mul_le_mul_of_nonneg_left hb (le_of_lt hqpos)
        _ = 2 * (if q z = 0 then 0 else
            q z / post_stratified_expected_group_count_local p n z ^ 2) := by
          rw [if_neg hqz]
          ring
  calc
    population_mean_risk p n (post_stratified_estimator p.targetGroup) P ≤
      p.varianceBound * post_stratified_label_harmonic_expectation_local p n +
        p.meanRadius ^ 2 * post_stratified_label_missing_expectation_local p n :=
      post_stratified_finite_plan_risk_upper_local p n P hP
    _ ≤ p.varianceBound *
          (post_stratified_plan_harmonic_local p n q +
            3 * ∑ z, if q z = 0 then 0 else
              (q z) ^ 2 / post_stratified_expected_group_count_local p n z ^ 2) +
        p.meanRadius ^ 2 *
          (2 * ∑ z, if q z = 0 then 0 else
            q z / post_stratified_expected_group_count_local p n z ^ 2) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hharm p.varianceBound_nonneg)
        (mul_le_mul_of_nonneg_left hmiss (sq_nonneg _))
    _ = p.varianceBound * post_stratified_plan_harmonic_local p n q +
        post_stratified_plan_second_order_local p n := by
      unfold post_stratified_plan_second_order_local
      rw [mul_add]
      rw [add_assoc]
      apply congrArg (fun x => p.varianceBound *
        post_stratified_plan_harmonic_local p n q + x)
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hqz : q z = 0
      · simp [q, hqz]
      · rw [if_neg hqz, if_neg hqz, if_neg hqz]
        ring

@[blueprint "def:post-stratified-uniform-source-plan-local"
  (statement := /-- The multiplicity-$t$ comparison plan takes $t$ observations from every source. -/)
  (title := /-- Uniform source comparison plan -/)
  (latexEnv := "definition")]
def post_stratified_uniform_source_plan_local {M : ℕ} (t : ℕ) : sampling_plan M :=
  fun _ => t

@[blueprint "def:post-stratified-total-source-cost-local"
  (statement := /-- Let $c_\Sigma=\sum_m c_m$ be the cost of one observation from every source. -/)
  (title := /-- Total source cost for the post-stratified comparison -/)
  (latexEnv := "definition")]
noncomputable def post_stratified_total_source_cost_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) : ℝ :=
  ∑ m, p.cost m

@[blueprint "lem:post-stratified-total-source-cost-positive-local"
  (statement := /-- The total cost $c_\Sigma$ is strictly positive. -/)
  (proof := /-- Every source cost is strictly positive and the finite source type is nonempty. -/)
  (title := /-- Positivity of total source cost -/)
  (latexEnv := "lemma")]
lemma post_stratified_total_source_cost_positive_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) :
    0 < post_stratified_total_source_cost_local p := by
  unfold post_stratified_total_source_cost_local
  exact Finset.sum_pos (fun m _ => p.cost_pos m) Finset.univ_nonempty

@[blueprint "lem:post-stratified-uniform-source-plan-cost-local"
  (statement := /-- The multiplicity-$t$ uniform comparison plan costs $tc_\Sigma$. -/)
  (proof := /-- Expand the finite cost sum and factor out the common multiplicity. -/)
  (title := /-- Cost of the uniform source comparison plan -/)
  (latexEnv := "lemma")]
lemma post_stratified_uniform_source_plan_cost_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (t : ℕ) :
    plan_cost p.cost (post_stratified_uniform_source_plan_local t) =
      t * post_stratified_total_source_cost_local p := by
  unfold plan_cost post_stratified_uniform_source_plan_local
    post_stratified_total_source_cost_local
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

@[blueprint "lem:post-stratified-uniform-source-plan-support-local"
  (statement := /-- Every positive-multiplicity uniform source plan supports every target mass vector. -/)
  (proof := /-- Source coverage supplies a positive summand in the expected count of each group. The uniform plan has positive total sample size, so its induced mixture mass is positive. -/)
  (title := /-- Support of the uniform source comparison plan -/)
  (latexEnv := "lemma")]
lemma post_stratified_uniform_source_plan_support_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (q : Fin K → ℝ)
    (t : ℕ) (ht : 0 < t) :
    target_supported_by_plan p (post_stratified_uniform_source_plan_local t) q := by
  intro z hq
  unfold source_mixture_mass
  have htotal : plan_total_samples
      (post_stratified_uniform_source_plan_local (M := M) t) ≠ 0 := by
    unfold plan_total_samples post_stratified_uniform_source_plan_local
    simp [NeZero.ne M, Nat.ne_of_gt ht]
  rw [if_neg htotal]
  have hN : 0 < (plan_total_samples
      (post_stratified_uniform_source_plan_local (M := M) t) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero htotal
  apply div_pos
  · rcases p.source_covers z with ⟨m, hm⟩
    unfold post_stratified_uniform_source_plan_local
    exact Finset.sum_pos'
      (fun j _ => mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)
      ⟨m, Finset.mem_univ m, mul_pos (by exact_mod_cast ht) hm⟩
  · exact hN

@[blueprint "lem:post-stratified-plan-discrepancy-harmonic-local"
  (statement := /-- For every nonempty plan, discrepancy equals total sample size times the harmonic quantity. -/)
  (proof := /-- Substitute the source-mixture definition and \cref{def:post-stratified-expected-group-count-local} in every nonzero target coordinate, then cancel the nonzero total sample size. -/)
  (title := /-- Discrepancy in harmonic form -/)
  (latexEnv := "lemma")]
lemma post_stratified_plan_discrepancy_harmonic_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) (hn : plan_total_samples n ≠ 0) :
    plan_discrepancy p n q =
      plan_total_samples n * post_stratified_plan_harmonic_local p n q := by
  unfold plan_discrepancy post_stratified_plan_harmonic_local
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hq : q z = 0
  · simp [hq]
  · simp only [hq, if_false]
    unfold source_mixture_mass post_stratified_expected_group_count_local
    rw [if_neg hn]
    push_cast
    field_simp

@[blueprint "lem:post-stratified-effective-sample-size-harmonic-local"
  (statement := /-- On a nonempty supported plan, effective sample size is the reciprocal of the harmonic quantity. -/)
  (proof := /-- Unfold effective sample size and use \cref{lem:post-stratified-plan-discrepancy-harmonic-local}; the positive total sample size cancels. -/)
  (title := /-- Effective sample size as reciprocal harmonic quantity -/)
  (latexEnv := "lemma")]
lemma post_stratified_effective_sample_size_harmonic_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) (hn : plan_total_samples n ≠ 0)
    (hsupp : target_supported_by_plan p n q) :
    effective_sample_size p n q =
      (post_stratified_plan_harmonic_local p n q)⁻¹ := by
  rw [effective_sample_size]
  simp only [hn, hsupp, not_true_eq_false, or_false, if_false]
  rw [post_stratified_plan_discrepancy_harmonic_local p n q hn]
  push_cast
  field_simp

@[blueprint "lem:post-stratified-plan-harmonic-positive-local"
  (statement := /-- A nonempty plan supporting a probability target has strictly positive harmonic quantity. -/)
  (proof := /-- The normalization identity \cref{lem:post-stratified-pmf-real-mass-sum-local} supplies a positive target coordinate. Its expected count is positive by \cref{lem:post-stratified-expected-group-count-positive-local}, so its harmonic summand is positive, while all other summands are nonnegative. -/)
  (title := /-- Positivity of the post-stratified harmonic quantity -/)
  (latexEnv := "lemma")]
lemma post_stratified_plan_harmonic_positive_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : PMF (Fin K)) (hn : plan_total_samples n ≠ 0)
    (hsupp : target_supported_by_plan p n (fun z => pmf_real_mass q z)) :
    0 < post_stratified_plan_harmonic_local p n
      (fun z => pmf_real_mass q z) := by
  have hsum := post_stratified_pmf_real_mass_sum_local q
  have hex : ∃ z, 0 < pmf_real_mass q z := by
    by_contra h
    push Not at h
    have hz : ∀ z, pmf_real_mass q z = 0 := fun z =>
      le_antisymm (h z) ENNReal.toReal_nonneg
    rw [Finset.sum_eq_zero fun z _ => hz z] at hsum
    norm_num at hsum
  rcases hex with ⟨z, hz⟩
  have hlam := post_stratified_expected_group_count_positive_local p n
    (fun j => pmf_real_mass q j) hn hsupp z hz
  unfold post_stratified_plan_harmonic_local
  have hnonneg : ∀ j, 0 ≤ if pmf_real_mass q j = 0 then 0
      else (pmf_real_mass q j) ^ 2 /
        post_stratified_expected_group_count_local p n j := by
    intro j
    split_ifs with hj
    · exact le_rfl
    · exact div_nonneg (sq_nonneg _) (by
        unfold post_stratified_expected_group_count_local
        exact Finset.sum_nonneg fun m _ =>
          mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)
  have hterm : 0 < (if pmf_real_mass q z = 0 then 0
      else (pmf_real_mass q z) ^ 2 /
        post_stratified_expected_group_count_local p n z) := by
    rw [if_neg (ne_of_gt hz)]
    exact div_pos (sq_pos_of_pos hz) hlam
  exact lt_of_lt_of_le hterm
    (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ z))

@[blueprint "lem:post-stratified-uniform-source-plan-harmonic-scale-local"
  (statement := /-- For $t>0$, the harmonic quantity of the multiplicity-$t$ uniform source plan is $t^{-1}$ times its one-round value. -/)
  (proof := /-- Every expected group count is multiplied by $t$; substitute this identity coordinatewise and factor out $t^{-1}$. -/)
  (title := /-- Harmonic scaling of the uniform comparison plan -/)
  (latexEnv := "lemma")]
lemma post_stratified_uniform_source_plan_harmonic_scale_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (q : Fin K → ℝ)
    (t : ℕ) (ht : 0 < t) :
    post_stratified_plan_harmonic_local p
        (post_stratified_uniform_source_plan_local t) q =
      post_stratified_plan_harmonic_local p
        (post_stratified_uniform_source_plan_local 1) q / t := by
  unfold post_stratified_plan_harmonic_local
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hq : q z = 0
  · simp [hq]
  · simp only [hq, if_false]
    unfold post_stratified_expected_group_count_local
      post_stratified_uniform_source_plan_local
    push_cast
    rw [← Finset.mul_sum]
    field_simp [Nat.ne_of_gt ht]

@[blueprint "lem:post-stratified-optimal-plan-eventual-support-local"
  (statement := /-- Once the budget covers one observation from every source, every target-effective-sample-size-optimal plan is nonempty and supports the target. -/)
  (proof := /-- The one-round uniform comparison plan is feasible by \cref{lem:post-stratified-uniform-source-plan-cost-local}, supports the target by \cref{lem:post-stratified-uniform-source-plan-support-local}, and has positive harmonic quantity by \cref{lem:post-stratified-plan-harmonic-positive-local}. Thus its effective sample size is positive by \cref{lem:post-stratified-effective-sample-size-harmonic-local}. Optimality forces the selected plan to have positive effective sample size, excluding emptiness and lack of support. -/)
  (title := /-- Eventual support of optimal post-stratified plans -/)
  (latexEnv := "lemma")]
lemma post_stratified_optimal_plan_eventual_support_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (B : ℝ) (nopt : sampling_plan M)
    (hB : post_stratified_total_source_cost_local p ≤ B)
    (hopt : optimal_sampling_plan p
      (fun z => pmf_real_mass p.targetGroup z) B nopt) :
    plan_total_samples nopt ≠ 0 ∧
      target_supported_by_plan p nopt
        (fun z => pmf_real_mass p.targetGroup z) := by
  let ncover : sampling_plan M := post_stratified_uniform_source_plan_local 1
  have hcost : budget_feasible_plan p B ncover := by
    unfold budget_feasible_plan
    rw [show plan_cost p.cost ncover = post_stratified_total_source_cost_local p by
      simpa [ncover] using post_stratified_uniform_source_plan_cost_local p 1]
    exact hB
  have hcover : target_supported_by_plan p ncover
      (fun z => pmf_real_mass p.targetGroup z) :=
    post_stratified_uniform_source_plan_support_local p _ 1 Nat.zero_lt_one
  have hncover : plan_total_samples ncover ≠ 0 := by
    unfold ncover plan_total_samples post_stratified_uniform_source_plan_local
    simp [NeZero.ne M]
  have hHcover : 0 < post_stratified_plan_harmonic_local p ncover
      (fun z => pmf_real_mass p.targetGroup z) :=
    post_stratified_plan_harmonic_positive_local p ncover p.targetGroup
      hncover hcover
  have heffcover : 0 < effective_sample_size p ncover
      (fun z => pmf_real_mass p.targetGroup z) := by
    rw [post_stratified_effective_sample_size_harmonic_local
      p ncover _ hncover hcover]
    exact inv_pos.2 hHcover
  have heffopt : 0 < effective_sample_size p nopt
      (fun z => pmf_real_mass p.targetGroup z) :=
    lt_of_lt_of_le heffcover (hopt.2 ncover hcost)
  constructor
  · intro hn
    rw [effective_sample_size] at heffopt
    simp [hn] at heffopt
  · by_contra hs
    rw [effective_sample_size] at heffopt
    simp [hs] at heffopt

@[blueprint "lem:post-stratified-optimal-harmonic-eventual-bound-local"
  (statement := /-- Along any target-effective-sample-size-optimal plan family, the selected plan is eventually nonempty and supported, and its harmonic quantity is at most a positive constant divided by the budget. -/)
  (proof := /-- Let $c_\Sigma$ be the one-round cost and let $H_1$ be the one-round harmonic quantity; these constants are positive by \cref{lem:post-stratified-total-source-cost-positive-local,lem:post-stratified-plan-harmonic-positive-local}. For $B\ge2c_\Sigma$, take $t=\lfloor B/c_\Sigma\rfloor$. Then $t\ge B/(2c_\Sigma)>0$, the multiplicity-$t$ uniform plan is feasible and supported by \cref{lem:post-stratified-uniform-source-plan-cost-local,lem:post-stratified-uniform-source-plan-support-local}, and its harmonic quantity is $H_1/t$ by \cref{lem:post-stratified-uniform-source-plan-harmonic-scale-local}. The selected plan is supported by \cref{lem:post-stratified-optimal-plan-eventual-support-local}; rewriting both effective sample sizes using \cref{lem:post-stratified-effective-sample-size-harmonic-local} transfers optimality into the asserted harmonic upper bound. -/)
  (title := /-- Eventual inverse-budget harmonic bound -/)
  (latexEnv := "lemma")]
lemma post_stratified_optimal_harmonic_eventual_bound_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (plans : ℝ → sampling_plan M)
    (hplans : ∀ B, 0 < B → optimal_sampling_plan p
      (fun z => pmf_real_mass p.targetGroup z) B (plans B)) :
    let C := post_stratified_total_source_cost_local p
    let H₁ := post_stratified_plan_harmonic_local p
      (post_stratified_uniform_source_plan_local 1)
      (fun z => pmf_real_mass p.targetGroup z)
    ∀ᶠ B in Filter.atTop,
      plan_total_samples (plans B) ≠ 0 ∧
      target_supported_by_plan p (plans B)
        (fun z => pmf_real_mass p.targetGroup z) ∧
      post_stratified_plan_harmonic_local p (plans B)
        (fun z => pmf_real_mass p.targetGroup z) ≤ 2 * C * H₁ / B := by
  let C := post_stratified_total_source_cost_local p
  let H₁ := post_stratified_plan_harmonic_local p
    (post_stratified_uniform_source_plan_local 1)
    (fun z => pmf_real_mass p.targetGroup z)
  have hC : 0 < C := post_stratified_total_source_cost_positive_local p
  have hH₁ : 0 < H₁ :=
    post_stratified_plan_harmonic_positive_local p
      (post_stratified_uniform_source_plan_local 1) p.targetGroup
      (by
        unfold plan_total_samples post_stratified_uniform_source_plan_local
        simp [NeZero.ne M])
      (post_stratified_uniform_source_plan_support_local p _ 1 Nat.zero_lt_one)
  filter_upwards [Filter.eventually_ge_atTop (2 * C)] with B hB
  have hBpos : 0 < B := lt_of_lt_of_le (by positivity : 0 < 2 * C) hB
  have hBcover : C ≤ B := by nlinarith
  obtain ⟨hnopt, hsopt⟩ := post_stratified_optimal_plan_eventual_support_local
    p B (plans B) hBcover (hplans B hBpos)
  refine ⟨hnopt, hsopt, ?_⟩
  have hxratio : 2 ≤ B / C := by
    apply (le_div_iff₀ hC).2
    nlinarith
  let t : ℕ := ⌊B / C⌋₊
  have ht : 0 < t := Nat.floor_pos.2 (le_trans (by norm_num) hxratio)
  have htupper : (t : ℝ) ≤ B / C :=
    Nat.floor_le (div_nonneg (le_of_lt hBpos) (le_of_lt hC))
  have htlower : B / (2 * C) ≤ (t : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (B / C)
    change B / C < (t : ℝ) + 1 at hfloor
    rw [show B / (2 * C) = (B / C) / 2 by field_simp [ne_of_gt hC]]
    nlinarith
  let nt : sampling_plan M := post_stratified_uniform_source_plan_local t
  have hntfeas : budget_feasible_plan p B nt := by
    unfold budget_feasible_plan
    rw [show plan_cost p.cost nt = t * C by
      simpa [nt, C] using post_stratified_uniform_source_plan_cost_local p t]
    have hm := mul_le_mul_of_nonneg_right htupper (le_of_lt hC)
    field_simp [ne_of_gt hC] at hm
    simpa [mul_comm] using hm
  have hntsupp : target_supported_by_plan p nt
      (fun z => pmf_real_mass p.targetGroup z) :=
    post_stratified_uniform_source_plan_support_local p _ t ht
  have hntnonempty : plan_total_samples nt ≠ 0 := by
    unfold nt plan_total_samples post_stratified_uniform_source_plan_local
    simp [NeZero.ne M, Nat.ne_of_gt ht]
  have hHnt : 0 < post_stratified_plan_harmonic_local p nt
      (fun z => pmf_real_mass p.targetGroup z) :=
    post_stratified_plan_harmonic_positive_local p nt p.targetGroup
      hntnonempty hntsupp
  have hHopt : 0 < post_stratified_plan_harmonic_local p (plans B)
      (fun z => pmf_real_mass p.targetGroup z) :=
    post_stratified_plan_harmonic_positive_local p (plans B) p.targetGroup
      hnopt hsopt
  have heff := (hplans B hBpos).2 nt hntfeas
  rw [post_stratified_effective_sample_size_harmonic_local p nt _
      hntnonempty hntsupp,
    post_stratified_effective_sample_size_harmonic_local p (plans B) _
      hnopt hsopt] at heff
  have hHcompare : post_stratified_plan_harmonic_local p (plans B)
      (fun z => pmf_real_mass p.targetGroup z) ≤
      post_stratified_plan_harmonic_local p nt
        (fun z => pmf_real_mass p.targetGroup z) := by
    apply (inv_le_inv₀ hHnt hHopt).mp
    exact heff
  rw [post_stratified_uniform_source_plan_harmonic_scale_local
    p _ t ht] at hHcompare
  apply le_trans hHcompare
  change H₁ / (t : ℝ) ≤ 2 * C * H₁ / B
  apply (div_le_div_iff₀ (by exact_mod_cast ht) hBpos).2
  have hm := mul_le_mul_of_nonneg_right htlower (le_of_lt hH₁)
  field_simp [ne_of_gt hC] at hm
  nlinarith

@[blueprint "def:post-stratified-increment-plan-local"
  (statement := /-- Increment a sampling plan by one observation at a specified source. -/)
  (title := /-- One-observation plan increment -/)
  (latexEnv := "definition")]
def post_stratified_increment_plan_local {M : ℕ}
    (n : sampling_plan M) (m₀ : Fin M) : sampling_plan M :=
  fun m => if m = m₀ then n m + 1 else n m

@[blueprint "lem:post-stratified-increment-plan-identities-local"
  (statement := /-- Incrementing source $m_0$ adds $c_{m_0}$ to plan cost and adds $q_{S,m_0}(z)$ to every expected group count. -/)
  (proof := /-- Expand both finite sums. All coordinates other than $m_0$ are unchanged, while the selected coordinate gains exactly one copy of its cost or source mass. -/)
  (title := /-- Cost and count identities for a plan increment -/)
  (latexEnv := "lemma")]
lemma post_stratified_increment_plan_identities_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M) (m₀ : Fin M) :
    plan_cost p.cost (post_stratified_increment_plan_local n m₀) =
        plan_cost p.cost n + p.cost m₀ ∧
      ∀ z, post_stratified_expected_group_count_local p
          (post_stratified_increment_plan_local n m₀) z =
        post_stratified_expected_group_count_local p n z +
          pmf_real_mass (p.sourceGroup m₀) z := by
  classical
  constructor
  · unfold plan_cost post_stratified_increment_plan_local
    rw [show (∑ m, p.cost m * ↑(if m = m₀ then n m + 1 else n m)) =
        ∑ m, (p.cost m * n m + if m = m₀ then p.cost m else 0) by
      apply Finset.sum_congr rfl
      intro m hm
      by_cases h : m = m₀ <;> simp [h] <;> ring]
    rw [Finset.sum_add_distrib]
    simp
  · intro z
    unfold post_stratified_expected_group_count_local
      post_stratified_increment_plan_local
    rw [show (∑ m, ↑(if m = m₀ then n m + 1 else n m) *
          pmf_real_mass (p.sourceGroup m) z) =
        ∑ m, (n m * pmf_real_mass (p.sourceGroup m) z +
          if m = m₀ then pmf_real_mass (p.sourceGroup m) z else 0) by
      apply Finset.sum_congr rfl
      intro m hm
      by_cases h : m = m₀ <;> simp [h] <;> ring]
    rw [Finset.sum_add_distrib]
    simp

@[blueprint "lem:post-stratified-increment-plan-support-local"
  (statement := /-- Incrementing one source preserves target support and produces a nonempty plan. -/)
  (proof := /-- The incremented coordinate is positive, so the new plan is nonempty. For every positive target coordinate, the old expected count is positive by \cref{lem:post-stratified-expected-group-count-positive-local}; the count identity in \cref{lem:post-stratified-increment-plan-identities-local} and nonnegativity of source masses preserve positivity, hence support. -/)
  (title := /-- Support is preserved by a plan increment -/)
  (latexEnv := "lemma")]
lemma post_stratified_increment_plan_support_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M) (m₀ : Fin M)
    (q : Fin K → ℝ) (hn : plan_total_samples n ≠ 0)
    (hsupp : target_supported_by_plan p n q) :
    plan_total_samples (post_stratified_increment_plan_local n m₀) ≠ 0 ∧
      target_supported_by_plan p
        (post_stratified_increment_plan_local n m₀) q := by
  have hnplus : plan_total_samples
      (post_stratified_increment_plan_local n m₀) ≠ 0 := by
    unfold plan_total_samples post_stratified_increment_plan_local
    intro hzero
    have hm : (if m₀ = m₀ then n m₀ + 1 else n m₀) ≤
        ∑ m, if m = m₀ then n m + 1 else n m :=
      Finset.single_le_sum
        (f := fun m => if m = m₀ then n m + 1 else n m)
        (fun m _ => Nat.zero_le _) (Finset.mem_univ m₀)
    rw [hzero] at hm
    simp at hm
  refine ⟨hnplus, ?_⟩
  intro z hq
  unfold source_mixture_mass
  rw [if_neg hnplus]
  have hlam := post_stratified_expected_group_count_positive_local
    p n q hn hsupp z hq
  have hid := (post_stratified_increment_plan_identities_local p n m₀).2 z
  have hmass : 0 ≤ pmf_real_mass (p.sourceGroup m₀) z := ENNReal.toReal_nonneg
  have hnum : 0 < post_stratified_expected_group_count_local p
      (post_stratified_increment_plan_local n m₀) z := by linarith
  have hden : 0 < (plan_total_samples
      (post_stratified_increment_plan_local n m₀) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hnplus
  unfold post_stratified_expected_group_count_local at hnum
  push_cast at hnum
  exact div_pos hnum hden

@[blueprint "lem:post-stratified-increment-plan-harmonic-strict-local"
  (statement := /-- If source $m_0$ has positive mass at a positive target coordinate, incrementing $m_0$ strictly decreases the harmonic quantity of a supported nonempty plan. -/)
  (proof := /-- The count identity from \cref{lem:post-stratified-increment-plan-identities-local} increases every denominator by a nonnegative source mass and increases the specified positive-target denominator strictly. Positivity of all relevant old counts follows from \cref{lem:post-stratified-expected-group-count-positive-local}; summing the coordinatewise weak inequalities and the one strict inequality proves the claim. -/)
  (title := /-- Strict harmonic improvement from a useful increment -/)
  (latexEnv := "lemma")]
lemma post_stratified_increment_plan_harmonic_strict_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (qpmf : PMF (Fin K)) (hn : plan_total_samples n ≠ 0)
    (hsupp : target_supported_by_plan p n (fun z => pmf_real_mass qpmf z))
    (z₀ : Fin K) (hz₀ : 0 < pmf_real_mass qpmf z₀)
    (m₀ : Fin M) (hm₀ : 0 < pmf_real_mass (p.sourceGroup m₀) z₀) :
    post_stratified_plan_harmonic_local p
        (post_stratified_increment_plan_local n m₀)
        (fun z => pmf_real_mass qpmf z) <
      post_stratified_plan_harmonic_local p n
        (fun z => pmf_real_mass qpmf z) := by
  unfold post_stratified_plan_harmonic_local
  apply Finset.sum_lt_sum
  · intro z hz
    by_cases hqz : pmf_real_mass qpmf z = 0
    · simp [hqz]
    · rw [if_neg hqz, if_neg hqz,
        (post_stratified_increment_plan_identities_local p n m₀).2 z]
      have hlam : 0 < post_stratified_expected_group_count_local p n z :=
        post_stratified_expected_group_count_positive_local p n _ hn hsupp z
          (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hqz))
      exact div_le_div_of_nonneg_left (sq_nonneg _)
        hlam (le_add_of_nonneg_right ENNReal.toReal_nonneg)
  · refine ⟨z₀, Finset.mem_univ z₀, ?_⟩
    rw [if_neg (ne_of_gt hz₀), if_neg (ne_of_gt hz₀),
      (post_stratified_increment_plan_identities_local p n m₀).2 z₀]
    have hlam : 0 < post_stratified_expected_group_count_local p n z₀ :=
      post_stratified_expected_group_count_positive_local p n _ hn hsupp z₀ hz₀
    exact div_lt_div_of_pos_left (sq_pos_of_pos hz₀) hlam
      (lt_add_of_pos_right _ hm₀)

@[blueprint "lem:post-stratified-optimal-plan-cost-gap-local"
  (statement := /-- Above the one-round covering cost, the unused budget of an optimal plan is smaller than the cost of a fixed source that is useful at a positive target coordinate. -/)
  (proof := /-- The selected plan is nonempty and supported by \cref{lem:post-stratified-optimal-plan-eventual-support-local}, and its harmonic quantity and that of the incremented plan are positive by \cref{lem:post-stratified-plan-harmonic-positive-local}. If its unused budget were at least the useful source cost, the one-observation increment would be feasible by \cref{lem:post-stratified-increment-plan-identities-local}, would remain nonempty and supported by \cref{lem:post-stratified-increment-plan-support-local}, and would strictly reduce the harmonic quantity by \cref{lem:post-stratified-increment-plan-harmonic-strict-local}. Rewriting effective sample sizes with \cref{lem:post-stratified-effective-sample-size-harmonic-local} would then contradict optimality. -/)
  (title := /-- Bounded budget underspend of an optimal plan -/)
  (latexEnv := "lemma")]
lemma post_stratified_optimal_plan_cost_gap_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (B : ℝ) (n : sampling_plan M)
    (hB : post_stratified_total_source_cost_local p ≤ B)
    (hopt : optimal_sampling_plan p
      (fun z => pmf_real_mass p.targetGroup z) B n)
    (z₀ : Fin K) (hz₀ : 0 < pmf_real_mass p.targetGroup z₀)
    (m₀ : Fin M) (hm₀ : 0 < pmf_real_mass (p.sourceGroup m₀) z₀) :
    B - plan_cost p.cost n < p.cost m₀ := by
  obtain ⟨hn, hsupp⟩ := post_stratified_optimal_plan_eventual_support_local
    p B n hB hopt
  by_contra hgap
  have hgap' : p.cost m₀ ≤ B - plan_cost p.cost n := le_of_not_gt hgap
  let nplus := post_stratified_increment_plan_local n m₀
  have hnplus := post_stratified_increment_plan_support_local p n m₀ _ hn hsupp
  have hnplusfeas : budget_feasible_plan p B nplus := by
    unfold budget_feasible_plan
    rw [show plan_cost p.cost nplus = plan_cost p.cost n + p.cost m₀ by
      simpa [nplus] using (post_stratified_increment_plan_identities_local p n m₀).1]
    linarith
  have hHlt := post_stratified_increment_plan_harmonic_strict_local
    p n p.targetGroup hn hsupp z₀ hz₀ m₀ hm₀
  have hHn : 0 < post_stratified_plan_harmonic_local p n
      (fun z => pmf_real_mass p.targetGroup z) :=
    post_stratified_plan_harmonic_positive_local p n p.targetGroup hn hsupp
  have hHplus : 0 < post_stratified_plan_harmonic_local p nplus
      (fun z => pmf_real_mass p.targetGroup z) :=
    post_stratified_plan_harmonic_positive_local p nplus p.targetGroup
      hnplus.1 hnplus.2
  have heff := hopt.2 nplus hnplusfeas
  rw [post_stratified_effective_sample_size_harmonic_local p nplus _
      hnplus.1 hnplus.2,
    post_stratified_effective_sample_size_harmonic_local p n _ hn hsupp] at heff
  exact (not_lt_of_ge heff) ((inv_lt_inv₀ hHn hHplus).2 hHlt)

@[blueprint "lem:post-stratified-leading-risk-harmonic-local"
  (statement := /-- For a positive budget and a nonempty plan, the population leading risk equals $\sigma^2(C_c(n)/B)H(n,q_T)$. -/)
  (proof := /-- Substitute \cref{lem:post-stratified-plan-discrepancy-harmonic-local} and the definition of average cost, then cancel the nonzero total sample size. -/)
  (title := /-- Population leading risk in harmonic form -/)
  (latexEnv := "lemma")]
lemma post_stratified_leading_risk_harmonic_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M) (B : ℝ)
    (hn : plan_total_samples n ≠ 0) :
    population_leading_risk p n B =
      p.varianceBound * (plan_cost p.cost n / B) *
        post_stratified_plan_harmonic_local p n
          (fun z => pmf_real_mass p.targetGroup z) := by
  unfold population_leading_risk average_plan_cost
  rw [if_neg hn,
    post_stratified_plan_discrepancy_harmonic_local p n _ hn]
  push_cast
  field_simp [show (plan_total_samples n : ℝ) ≠ 0 by exact_mod_cast hn]

@[blueprint "lem:post-stratified-inverse-square-little-o-local"
  (statement := /-- For every real constant $A$, the function $B\mapsto A/B^2$ is little-$o$ of $B\mapsto B^{-1}$ at infinity. -/)
  (proof := /-- Given $c>0$, take $B>|A|/c$ and $B>0$. Then $|A|/B^2\le c/B$ after multiplying by the positive budget. This is the defining norm inequality for little-$o$. -/)
  (title := /-- Inverse-square terms are negligible at inverse-budget scale -/)
  (latexEnv := "lemma")]
lemma post_stratified_inverse_square_little_o_local (A : ℝ) :
    (fun B : ℝ => A / B ^ 2) =o[Filter.atTop] inverse_budget_rate := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [Filter.eventually_gt_atTop (|A| / c),
    Filter.eventually_gt_atTop (0 : ℝ)] with B hB hBpos
  simp only [Real.norm_eq_abs, inverse_budget_rate]
  rw [abs_div, abs_pow, abs_of_pos hBpos,
    abs_of_pos (one_div_pos.2 hBpos)]
  have hAc : |A| < c * B := by
    have := (div_lt_iff₀ hc).mp hB
    nlinarith
  have hB0 : B ≠ 0 := ne_of_gt hBpos
  field_simp [hB0]
  nlinarith

@[blueprint "lem:post-stratified-selected-plan-eventual-risk-local"
  (statement := /-- Along any target-effective-sample-size-optimal family and for every bounded conditional model, there is a constant $A$ such that eventually
  \[
  \operatorname{Risk}_{\mathrm{PM}}(n(B),P)
  \le L(n(B),B)+A/B^2.
  \] -/)
  (proof := /-- The target normalization in \cref{lem:post-stratified-pmf-real-mass-sum-local} supplies a positive coordinate, and the source-covering assumption supplies a useful source. The one-round comparison constants are positive by \cref{lem:post-stratified-total-source-cost-positive-local,lem:post-stratified-uniform-source-plan-support-local,lem:post-stratified-plan-harmonic-positive-local}. The harmonic control in \cref{lem:post-stratified-optimal-harmonic-eventual-bound-local} makes $H(n(B),q_T)=O(B^{-1})$. Each positive-target summand, whose count is positive by \cref{lem:post-stratified-expected-group-count-positive-local}, then gives $\lambda_z(n(B))=\Omega(B)$, so the explicit second-order term in \cref{lem:post-stratified-finite-plan-moment-upper-local} is $O(B^{-2})$. The budget gap is bounded by the useful source cost by \cref{lem:post-stratified-optimal-plan-cost-gap-local}. Combining this with \cref{lem:post-stratified-leading-risk-harmonic-local} shows that replacing $\sigma^2H$ by the budget-normalized leading risk costs only $O(B^{-2})$. -/)
  (title := /-- Second-order risk bound along selected optimal plans -/)
  (latexEnv := "lemma")]
lemma post_stratified_selected_plan_eventual_risk_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (plans : ℝ → sampling_plan M)
    (hplans : ∀ B, 0 < B → optimal_sampling_plan p
      (fun z => pmf_real_mass p.targetGroup z) B (plans B))
    (P : conditional_outcome_model K) (hP : bounded_conditional_mean_class p P) :
    ∃ A : ℝ, ∀ᶠ B in Filter.atTop,
      population_mean_risk p (plans B)
          (post_stratified_estimator p.targetGroup) P ≤
        population_leading_risk p (plans B) B + A / B ^ 2 := by
  let q : Fin K → ℝ := fun z => pmf_real_mass p.targetGroup z
  let C := post_stratified_total_source_cost_local p
  let H₁ := post_stratified_plan_harmonic_local p
    (post_stratified_uniform_source_plan_local 1) q
  let KH := 2 * C * H₁
  have hC : 0 < C := post_stratified_total_source_cost_positive_local p
  have hH₁ : 0 < H₁ :=
    post_stratified_plan_harmonic_positive_local p
      (post_stratified_uniform_source_plan_local 1) p.targetGroup
      (by
        unfold plan_total_samples post_stratified_uniform_source_plan_local
        simp [NeZero.ne M])
      (post_stratified_uniform_source_plan_support_local p _ 1 Nat.zero_lt_one)
  have hKH : 0 < KH := by
    dsimp only [KH]
    positivity
  have hqsum := post_stratified_pmf_real_mass_sum_local p.targetGroup
  have hqexists : ∃ z, 0 < q z := by
    by_contra h
    push Not at h
    have hz : ∀ z, q z = 0 := fun z =>
      le_antisymm (h z) ENNReal.toReal_nonneg
    have : (∑ z, q z) = 0 := Finset.sum_eq_zero fun z _ => hz z
    dsimp only [q] at this
    linarith
  rcases hqexists with ⟨z₀, hz₀⟩
  rcases p.source_covers z₀ with ⟨m₀, hm₀⟩
  let A₂ : ℝ := ∑ z, if q z = 0 then 0 else
    (3 * p.varianceBound * (q z) ^ 2 + 2 * p.meanRadius ^ 2 * q z) *
      KH ^ 2 / (q z) ^ 4
  let A : ℝ := p.varianceBound * KH * p.cost m₀ + A₂
  refine ⟨A, ?_⟩
  have hcontrol := post_stratified_optimal_harmonic_eventual_bound_local
    p plans hplans
  dsimp only [C, H₁, KH] at hcontrol
  filter_upwards [hcontrol,
    Filter.eventually_ge_atTop C,
    Filter.eventually_gt_atTop (0 : ℝ)] with B hB hBcover hBpos
  have hHbound : post_stratified_plan_harmonic_local p (plans B) q ≤ KH / B := by
    simpa [KH, C, H₁] using hB.2.2
  have hopt := hplans B hBpos
  have hcostle : plan_cost p.cost (plans B) ≤ B := hopt.1
  have hgapnonneg : 0 ≤ B - plan_cost p.cost (plans B) := sub_nonneg.2 hcostle
  have hgap : B - plan_cost p.cost (plans B) < p.cost m₀ :=
    post_stratified_optimal_plan_cost_gap_local p B (plans B)
      (by simpa [C] using hBcover)
      hopt z₀ hz₀ m₀ hm₀
  have hfinite := post_stratified_finite_plan_moment_upper_local
    p (plans B) P hP hB.1 hB.2.1
  have hsecond : post_stratified_plan_second_order_local p (plans B) ≤ A₂ / B ^ 2 := by
    unfold post_stratified_plan_second_order_local
    dsimp only [A₂]
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro z hz
    by_cases hqz : q z = 0
    · simp [q, hqz]
    · have hqpos : 0 < q z :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hqz)
      have hlam : 0 < post_stratified_expected_group_count_local p (plans B) z :=
        post_stratified_expected_group_count_positive_local p (plans B) q
          hB.1 hB.2.1 z hqpos
      have htermle : q z ^ 2 /
          post_stratified_expected_group_count_local p (plans B) z ≤
          post_stratified_plan_harmonic_local p (plans B) q := by
        unfold post_stratified_plan_harmonic_local
        have hnonneg : ∀ j, 0 ≤ if q j = 0 then 0 else
            q j ^ 2 / post_stratified_expected_group_count_local p (plans B) j := by
          intro j
          by_cases hqj : q j = 0
          · rw [if_pos hqj]
          · rw [if_neg hqj]
            exact div_nonneg (sq_nonneg _) (by
              unfold post_stratified_expected_group_count_local
              exact Finset.sum_nonneg fun m _ =>
                mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)
        have hs := Finset.single_le_sum
          (fun j _ => hnonneg j) (Finset.mem_univ z)
        simpa [hqz] using hs
      have hcross : B * q z ^ 2 ≤ KH *
          post_stratified_expected_group_count_local p (plans B) z := by
        have := le_trans htermle hHbound
        field_simp [ne_of_gt hlam, ne_of_gt hBpos] at this
        nlinarith
      have hinv : 1 / post_stratified_expected_group_count_local p (plans B) z ≤
          KH / (q z ^ 2 * B) := by
        apply (div_le_div_iff₀ hlam (mul_pos (sq_pos_of_pos hqpos) hBpos)).2
        nlinarith
      have hinvnonneg : 0 ≤ 1 /
          post_stratified_expected_group_count_local p (plans B) z := by positivity
      have hinvright : 0 ≤ KH / (q z ^ 2 * B) := by positivity
      have hinvsq := mul_self_le_mul_self hinvnonneg hinv
      have hinvsq' : 1 /
          post_stratified_expected_group_count_local p (plans B) z ^ 2 ≤
          KH ^ 2 / (q z ^ 4 * B ^ 2) := by
        calc
          1 / post_stratified_expected_group_count_local p (plans B) z ^ 2 =
              (1 / post_stratified_expected_group_count_local p (plans B) z) ^ 2 := by ring
          _ ≤ (KH / (q z ^ 2 * B)) ^ 2 := by
            simpa [pow_two] using hinvsq
          _ = KH ^ 2 / (q z ^ 4 * B ^ 2) := by ring
      have hcoef : 0 ≤ 3 * p.varianceBound * q z ^ 2 +
          2 * p.meanRadius ^ 2 * q z := by
        exact add_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) p.varianceBound_nonneg) (sq_nonneg _))
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (le_of_lt hqpos))
      rw [if_neg hqz, if_neg hqz]
      calc
        (3 * p.varianceBound * pmf_real_mass p.targetGroup z ^ 2 +
            2 * p.meanRadius ^ 2 * pmf_real_mass p.targetGroup z) /
            post_stratified_expected_group_count_local p (plans B) z ^ 2 =
          (3 * p.varianceBound * q z ^ 2 + 2 * p.meanRadius ^ 2 * q z) *
            (1 / post_stratified_expected_group_count_local p (plans B) z ^ 2) := by
              dsimp only [q]
              ring
        _ ≤ (3 * p.varianceBound * q z ^ 2 + 2 * p.meanRadius ^ 2 * q z) *
            (KH ^ 2 / (q z ^ 4 * B ^ 2)) :=
          mul_le_mul_of_nonneg_left hinvsq' hcoef
        _ = (3 * p.varianceBound * q z ^ 2 + 2 * p.meanRadius ^ 2 * q z) *
            KH ^ 2 / q z ^ 4 / B ^ 2 := by ring
  have hHcost : p.varianceBound *
      post_stratified_plan_harmonic_local p (plans B) q ≤
      population_leading_risk p (plans B) B +
        (p.varianceBound * KH * p.cost m₀) / B ^ 2 := by
    rw [post_stratified_leading_risk_harmonic_local p (plans B) B hB.1]
    let H := post_stratified_plan_harmonic_local p (plans B) q
    let d := B - plan_cost p.cost (plans B)
    have hHnonneg : 0 ≤ H := by
      exact le_of_lt (post_stratified_plan_harmonic_positive_local p
        (plans B) p.targetGroup hB.1 hB.2.1)
    have hgaple : d ≤ p.cost m₀ := le_of_lt hgap
    have hprod : H * d ≤ (KH / B) * p.cost m₀ :=
      mul_le_mul hHbound hgaple hgapnonneg (div_nonneg (le_of_lt hKH) (le_of_lt hBpos))
    have hdiv : H * d / B ≤ (KH / B) * p.cost m₀ / B :=
      div_le_div_of_nonneg_right hprod (le_of_lt hBpos)
    have hscaled := mul_le_mul_of_nonneg_left hdiv p.varianceBound_nonneg
    have hid : H = plan_cost p.cost (plans B) / B * H + H * d / B := by
      dsimp only [d]
      field_simp [ne_of_gt hBpos]
      ring
    calc
      p.varianceBound * H = p.varianceBound *
          (plan_cost p.cost (plans B) / B * H + H * d / B) :=
        congrArg (fun x => p.varianceBound * x) hid
      _ = p.varianceBound * (plan_cost p.cost (plans B) / B) * H +
            p.varianceBound * (H * d / B) := by ring
      _ ≤ p.varianceBound * (plan_cost p.cost (plans B) / B) * H +
          p.varianceBound * ((KH / B) * p.cost m₀ / B) :=
        by
          simpa [add_comm, add_left_comm] using
            add_le_add_left hscaled
              (p.varianceBound * (plan_cost p.cost (plans B) / B) * H)
      _ = p.varianceBound * (plan_cost p.cost (plans B) / B) * H +
          p.varianceBound * KH * p.cost m₀ / B ^ 2 := by ring
  calc
    population_mean_risk p (plans B)
        (post_stratified_estimator p.targetGroup) P ≤
      p.varianceBound * post_stratified_plan_harmonic_local p (plans B) q +
        post_stratified_plan_second_order_local p (plans B) := hfinite
    _ ≤ (population_leading_risk p (plans B) B +
          (p.varianceBound * KH * p.cost m₀) / B ^ 2) + A₂ / B ^ 2 :=
      add_le_add hHcost hsecond
    _ = population_leading_risk p (plans B) B + A / B ^ 2 := by
      dsimp only [A]
      ring

@[blueprint "lem:post-stratified-arbitrary-plan-risk-upper"
  (statement := /-- Let $K$ and $M$ be positive integers, let $p$ be a biased-source mean-estimation problem with target group law $q_T$, and let $B\mapsto n_T(B)$ be a family of integer sampling plans indexed by $B\in\mathbb R$. Suppose that, for every $B>0$, the plan $n_T(B)$ maximizes the effective sample size for $q_T$ among all plans of cost at most $B$. For every conditional outcome model $P\in\mathcal P_p(R,\sigma^2)$, there exists a function $e_{P,n_T}\colon\mathbb R\times\mathbb N^M\to\mathbb R$ such that, for every $B>0$ and every integer sampling plan $n$,
  \[
  \operatorname{Risk}_{\mathrm{PM}}((n,\widehat\theta_{\mathrm{PS}}),P)
  \le \frac{\sigma^2\bar c(n)D(q_T,\bar q_n)}{B}+e_{P,n_T}(B,n).
  \]
  Moreover, $e_{P,n_T}(B,n_T(B))=o(B^{-1})$ as $B\to\infty$. -/)
  (proof := /-- By \cref{lem:post-stratified-selected-plan-eventual-risk-local}, for the fixed bounded conditional model there is a constant $A$ such that the risk of the selected plan is eventually at most its leading risk plus $A/B^2$. Define the plan-indexed remainder to be the maximum of the exact risk excess and $A/B^2$ on the selected plan, and to be the exact risk excess on every other plan. The arbitrary-plan inequality is then immediate. Along the selected family the eventual bound makes the maximum equal to $A/B^2$, which is little-$o(B^{-1})$ by \cref{lem:post-stratified-inverse-square-little-o-local}. -/)
  (title := /-- Post-stratified risk bound relative to a selected optimal family -/)
  (latexEnv := "lemma")]
lemma post_stratified_arbitrary_plan_risk_upper {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (plans : ℝ → sampling_plan M)
    (hplans : ∀ B, 0 < B →
      optimal_sampling_plan p (fun z => pmf_real_mass p.targetGroup z) B (plans B)) :
    ∀ P, bounded_conditional_mean_class p P →
      ∃ planRemainder : ℝ → sampling_plan M → ℝ,
        Asymptotics.IsLittleO Filter.atTop
            (fun B => planRemainder B (plans B)) inverse_budget_rate ∧
        ∀ B, 0 < B → ∀ n : sampling_plan M,
          population_mean_risk p n
              (post_stratified_estimator p.targetGroup) P ≤
            population_leading_risk p n B + planRemainder B n := by
  intro P hP
  obtain ⟨A, hA⟩ := post_stratified_selected_plan_eventual_risk_local
    p plans hplans P hP
  let planRemainder : ℝ → sampling_plan M → ℝ := fun B n =>
    if n = plans B then
      max (population_mean_risk p n (post_stratified_estimator p.targetGroup) P -
        population_leading_risk p n B) (A / B ^ 2)
    else
      population_mean_risk p n (post_stratified_estimator p.targetGroup) P -
        population_leading_risk p n B
  refine ⟨planRemainder, ?_, ?_⟩
  · have heq : (fun B => A / B ^ 2) =ᶠ[Filter.atTop]
        fun B => planRemainder B (plans B) := by
      filter_upwards [hA] with B hbound
      dsimp only [planRemainder]
      rw [if_pos rfl, max_eq_right]
      linarith
    exact (post_stratified_inverse_square_little_o_local A).congr'
      heq (Filter.EventuallyEq.rfl)
  · intro B hB n
    by_cases hn : n = plans B
    · dsimp only [planRemainder]
      rw [if_pos hn]
      have hmax := le_max_left
        (population_mean_risk p n (post_stratified_estimator p.targetGroup) P -
          population_leading_risk p n B) (A / B ^ 2)
      linarith
    · dsimp only [planRemainder]
      rw [if_neg hn]
      linarith

@[blueprint "lem:post-stratified-optimal-risk-upper"
  (statement := /-- Let $K$ and $M$ be positive integers, let $p$ be a biased-source mean-estimation problem with target group law $q_T$, and let $n_T\colon\mathbb R\to\mathbb N^M$ be a family such that, for every $B>0$, the plan $n_T(B)$ maximizes the effective sample size for $q_T$ among all plans of cost at most $B$. Then, for every conditional outcome model $P\in\mathcal P_p(R,\sigma^2)$, there exists a function $r_P\colon\mathbb R\to\mathbb R$ such that $r_P=o(B^{-1})$ as $B\to\infty$ and, for every $B>0$,
  \[
  \operatorname{Risk}_{\mathrm{PM}}((n_T(B),\widehat\theta_{\mathrm{PS}}),P)
  \le \frac{\sigma^2\bar c(n_T(B))D(q_T,\bar q_{n_T(B)})}{B}+r_P(B).
  \] -/)
  (proof := /-- Apply \cref{lem:post-stratified-arbitrary-plan-risk-upper} to the prescribed family $n_T$, its optimality hypothesis, and the conditional model $P$. Let $e_{P,n_T}(B,n)$ be the resulting plan-indexed error and set $r_P(B)=e_{P,n_T}(B,n_T(B))$. The first conclusion of that lemma gives $r_P=o(B^{-1})$, and its arbitrary-plan inequality with $n=n_T(B)$ gives the asserted risk bound for every $B>0$. -/)
  (title := /-- Post-stratified risk at a target-optimal plan -/)
  (latexEnv := "lemma")]
lemma post_stratified_optimal_risk_upper {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (plans : ℝ → sampling_plan M)
    (hplans : ∀ B, 0 < B →
      optimal_sampling_plan p (fun z => pmf_real_mass p.targetGroup z) B (plans B)) :
    ∀ P, bounded_conditional_mean_class p P →
      ∃ remainder : ℝ → ℝ,
        Asymptotics.IsLittleO Filter.atTop remainder inverse_budget_rate ∧
        ∀ B, 0 < B →
          population_mean_risk p (plans B)
              (post_stratified_estimator p.targetGroup) P ≤
            population_leading_risk p (plans B) B + remainder B := by
  intro P hP
  obtain ⟨planRemainder, hsmall, hbound⟩ :=
    post_stratified_arbitrary_plan_risk_upper p plans hplans P hP
  exact ⟨fun B => planRemainder B (plans B), hsmall,
    fun B hB => hbound B hB (plans B)⟩

@[blueprint "lem:vector-of-means-optimal-risk-upper"
  (statement := /-- Let $K$ and $M$ be positive integers, let $p$ be a biased-source mean-estimation problem with $K$ groups and $M$ sources, and let $n_U\colon\mathbb R\to\mathbb N^M$ be a family such that, for every $B>0$, the plan $n_U(B)$ maximizes the effective sample size for the uniform mass $u_K$ among all plans of cost at most $B$. Then, for every conditional outcome model $P\in\mathcal P_p(R,\sigma^2)$, there exists a function $r_P\colon\mathbb R\to\mathbb R$ satisfying $r_P=o(B^{-1})$ as $B\to\infty$ and, for every $B>0$,
  \[
  \operatorname{Risk}_{\mathrm{GM}}((n_U(B),\widehat\theta_{\mathrm{VM}}),P)
  \le \frac{K^2\sigma^2\bar c(n_U(B))D(u_K,\bar q_{n_U(B)})}{B}+r_P(B).
  \] -/)
  (proof := /-- Let $u$ be the uniform probability mass function on $[K]$, and replace the target law of $p$ by $u$ while leaving its sources, costs, and model bounds unchanged. The assumed plans remain optimal for this modified problem. For every sign vector $s\in\{-1,1\}^K$, push the conditional law in group $z$ forward by $y\mapsto s_z y$. This pushforward preserves membership in $\mathcal P_p(R,\sigma^2)$: multiplication by a sign preserves the $L^2$ condition, the absolute conditional mean, and the conditional variance. Applying \cref{lem:post-stratified-optimal-risk-upper} to every signed model gives remainders $r_s=o(B^{-1})$ and scalar uniform-mean risk bounds. Their finite normalized sum is again $o(B^{-1})$.

  Multiplication of every sampled outcome in group $z$ by $s_z$ pushes the complete product sampling law to the signed sampling law. Under this coupling, the post-stratified estimation error for the uniform target is $K^{-1}\sum_z s_z(\overline Y_z-\mu_z)$. Measurability needed for the pushforward integrals follows from \cref{lem:post-stratified-estimator-measurable,lem:vector-of-means-estimator-measurable}. Reindexing all sign vectors by flipping one coordinate proves the orthogonality relation
  \[
  \sum_s s_zs_w=\begin{cases}2^K,&z=w,\\0,&z\ne w.\end{cases}
  \]
  Consequently, averaging the squared signed scalar errors and multiplying by $K^2$ gives exactly $\sum_z(\overline Y_z-\mu_z)^2$, while the corresponding scalar leading terms give exactly the asserted group leading term. If this nonnegative vector loss is integrable, finite-sum linearity of the integral and the signed scalar bounds yield the result. If it is not integrable, its Bochner integral is zero by definition, whereas the averaged right-hand side is nonnegative by the same scalar bounds. Thus the normalized sum of the $r_s$ is the required remainder in both cases. -/)
  (title := /-- Vector-of-means risk at a uniform-optimal plan -/)
  (latexEnv := "lemma")]
lemma vector_of_means_optimal_risk_upper {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (plans : ℝ → sampling_plan M)
    (hplans : ∀ B, 0 < B →
      optimal_sampling_plan p (uniform_group_mass K) B (plans B)) :
    ∀ P, bounded_conditional_mean_class p P →
      ∃ remainder : ℝ → ℝ,
        Asymptotics.IsLittleO Filter.atTop remainder inverse_budget_rate ∧
        ∀ B, 0 < B →
          group_means_risk p (plans B) vector_of_means_estimator P ≤
            group_leading_risk p (plans B) B + remainder B := by
  intro P hP
  let u : PMF (Fin K) :=
    ⟨fun _ => (K : ENNReal)⁻¹, by
      convert hasSum_fintype (fun _ : Fin K => (K : ENNReal)⁻¹) using 1 <;> simp
      exact (ENNReal.mul_inv_cancel (NeZero.natCast_ne K ENNReal)
        (ENNReal.natCast_ne_top K)).symm⟩
  let pu : biased_source_mean_problem K M := { p with targetGroup := u }
  have hu : (fun z => pmf_real_mass u z) = uniform_group_mass K := by
    funext z
    change ((K : ENNReal)⁻¹).toReal = (1 : ℝ) / K
    rw [ENNReal.toReal_inv]
    simp
  have hp : ∀ B, 0 < B →
      optimal_sampling_plan pu (fun z => pmf_real_mass pu.targetGroup z) B (plans B) := by
    intro B hB
    simpa [pu, hu, optimal_sampling_plan, budget_feasible_plan,
      effective_sample_size, target_supported_by_plan, source_mixture_mass,
      plan_discrepancy] using hplans B hB
  let sign (s : Fin K → Bool) (z : Fin K) : ℝ := if s z then -1 else 1
  let signedModel (s : Fin K → Bool) : conditional_outcome_model K := fun z =>
    (P z).map ((measurable_const.mul measurable_id :
      Measurable (fun y : ℝ => sign s z * y)).aemeasurable)
  let signedVector (s : Fin K → Bool) (y : Fin K → ℝ) : Fin K → ℝ :=
    fun z => sign s z * y z
  let signedPair (s : Fin K → Bool) (x : Fin K × ℝ) : Fin K × ℝ :=
    (x.1, sign s x.1 * x.2)
  let signedData (s : Fin K → Bool) {n : sampling_plan M}
      (D : sampled_dataset K M n) : sampled_dataset K M n :=
    fun m i => signedPair s (D m i)
  have hsignedVector_meas : ∀ s, Measurable (signedVector s) := by
    intro s
    fun_prop
  have hsignedPair_meas : ∀ s, Measurable (signedPair s) := by
    intro s
    fun_prop
  have hsignedData_meas : ∀ s (n : sampling_plan M),
      Measurable (signedData s : sampled_dataset K M n → sampled_dataset K M n) := by
    intro s n
    fun_prop
  have hsource : ∀ s m, source_observation_law pu (signedModel s) m =
      Measure.map (signedPair s) (source_observation_law p P m) := by
    intro s m
    let select : Fin K × (Fin K → ℝ) → Fin K × ℝ := fun x => (x.1, x.2 x.1)
    have heval : Measurable (fun x : Fin K × (Fin K → ℝ) => x.2 x.1) := by
      have hsum : Measurable (fun x : Fin K × (Fin K → ℝ) =>
          ∑ z, if x.1 = z then x.2 z else 0) := by
        apply Finset.measurable_sum Finset.univ
        intro z hz
        exact Measurable.ite ((measurableSet_singleton z).preimage measurable_fst)
          (by fun_prop) measurable_const
      convert hsum using 1
      funext x
      simp
    have hselect : Measurable select := measurable_fst.prodMk heval
    have hpi : Measure.pi (fun z => Measure.map (fun y : ℝ => sign s z * y)
        (P z : Measure ℝ)) =
        Measure.map (signedVector s) (Measure.pi fun z => (P z : Measure ℝ)) := by
      symm
      exact Measure.pi_map_pi (fun z =>
        (measurable_const.mul measurable_id).aemeasurable)
    rw [source_observation_law, source_observation_law]
    change Measure.map select
        ((p.sourceGroup m).toMeasure.prod
          (Measure.pi fun z => Measure.map (fun y : ℝ => sign s z * y) (P z : Measure ℝ))) = _
    rw [hpi]
    calc
      Measure.map select ((p.sourceGroup m).toMeasure.prod
          (Measure.map (signedVector s) (Measure.pi fun z => (P z : Measure ℝ)))) =
          Measure.map select
            ((Measure.map id (p.sourceGroup m).toMeasure).prod
              (Measure.map (signedVector s) (Measure.pi fun z => (P z : Measure ℝ)))) := by simp
      _ = Measure.map select
          (Measure.map (Prod.map id (signedVector s))
            ((p.sourceGroup m).toMeasure.prod (Measure.pi fun z => (P z : Measure ℝ)))) := by
          rw [Measure.map_prod_map _ _ measurable_id (hsignedVector_meas s)]
      _ = Measure.map (select ∘ Prod.map id (signedVector s))
          ((p.sourceGroup m).toMeasure.prod (Measure.pi fun z => (P z : Measure ℝ))) := by
          rw [Measure.map_map hselect (measurable_id.prodMap (hsignedVector_meas s))]
      _ = Measure.map (signedPair s ∘ select)
          ((p.sourceGroup m).toMeasure.prod (Measure.pi fun z => (P z : Measure ℝ))) := by
          congr 1
      _ = Measure.map (signedPair s)
          (Measure.map select
            ((p.sourceGroup m).toMeasure.prod (Measure.pi fun z => (P z : Measure ℝ)))) := by
          rw [Measure.map_map (hsignedPair_meas s) hselect]
  have hsampling : ∀ s (n : sampling_plan M),
      sampling_law pu n (signedModel s) =
        Measure.map (signedData s) (sampling_law p n P) := by
    intro s n
    letI hfinSource : ∀ m, IsFiniteMeasure (source_observation_law p P m) := fun m => by
      rw [source_observation_law]
      infer_instance
    have hinner : ∀ m, Measure.pi (fun _i : Fin (n m) =>
        source_observation_law pu (signedModel s) m) =
        Measure.map (fun d i => signedPair s (d i))
          (Measure.pi fun _i : Fin (n m) => source_observation_law p P m) := by
      intro m
      simp_rw [hsource s m]
      symm
      exact Measure.pi_map_pi (fun _i => (hsignedPair_meas s).aemeasurable)
    rw [sampling_law, sampling_law]
    simp_rw [hinner]
    symm
    letI hfinPi : ∀ m, IsFiniteMeasure
        (Measure.pi fun _i : Fin (n m) => source_observation_law p P m) :=
      fun m => inferInstance
    letI hfinMap : ∀ m, IsFiniteMeasure
        (Measure.map (fun d i => signedPair s (d i))
          (Measure.pi fun _i : Fin (n m) => source_observation_law p P m)) :=
      fun m => inferInstance
    letI hSigma : ∀ m, SigmaFinite
        (Measure.map (fun d i => signedPair s (d i))
          (Measure.pi fun _i : Fin (n m) => source_observation_law p P m)) :=
      fun m => by
        letI := hfinMap m
        infer_instance
    have houter : ∀ m, Measurable
        (fun d : (i : Fin (n m)) → Fin K × ℝ => fun i => signedPair s (d i)) := by
      intro m
      fun_prop
    convert Measure.pi_map_pi (hμ := hSigma) (fun m => (houter m).aemeasurable) using 1
  have hsclass : ∀ s, bounded_conditional_mean_class pu (signedModel s) := by
    intro s z
    have hmap : AEMeasurable (fun y : ℝ => sign s z * y) (P z : Measure ℝ) :=
      (measurable_const.mul measurable_id).aemeasurable
    have hInt : Integrable (fun y : ℝ => y) (P z : Measure ℝ) := by
      simpa [Function.id_def] using (hP z).1.integrable (by norm_num)
    have hmean : conditional_group_mean (signedModel s) z =
        sign s z * conditional_group_mean P z := by
      change (∫ y, id y ∂Measure.map (fun y : ℝ => sign s z * y) (P z : Measure ℝ)) = _
      rw [MeasureTheory.integral_map hmap measurable_id.aestronglyMeasurable]
      simp only [Function.id_def]
      rw [integral_const_mul_of_integrable hInt]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · change MemLp id 2 (Measure.map (fun y : ℝ => sign s z * y) (P z : Measure ℝ))
      rw [MeasureTheory.memLp_map_measure_iff measurable_id.aestronglyMeasurable hmap]
      simpa [Function.comp_def] using (hP z).1.const_mul (sign s z)
    · rw [hmean]
      cases hsz : s z <;> simpa [pu, sign, hsz] using (hP z).2.1
    · change ProbabilityTheory.variance id
        (Measure.map (fun y : ℝ => sign s z * y) (P z : Measure ℝ)) ≤ p.varianceBound
      rw [ProbabilityTheory.variance_id_map hmap,
        ProbabilityTheory.variance_const_mul]
      cases hsz : s z <;> simpa [sign, hsz, Function.id_def] using (hP z).2.2
  have hsignedMean : ∀ s z, conditional_group_mean (signedModel s) z =
      sign s z * conditional_group_mean P z := by
    intro s z
    have hmap : AEMeasurable (fun y : ℝ => sign s z * y) (P z : Measure ℝ) :=
      (measurable_const.mul measurable_id).aemeasurable
    have hInt : Integrable (fun y : ℝ => y) (P z : Measure ℝ) := by
      simpa [Function.id_def] using (hP z).1.integrable (by norm_num)
    change (∫ y, id y ∂Measure.map (fun y : ℝ => sign s z * y) (P z : Measure ℝ)) = _
    rw [MeasureTheory.integral_map hmap measurable_id.aestronglyMeasurable]
    simp only [Function.id_def]
    rw [integral_const_mul_of_integrable hInt]
    rfl
  have hobsCount : ∀ s (n : sampling_plan M) (D : sampled_dataset K M n) z,
      observed_group_count (signedData s D) z = observed_group_count D z := by
    intro s n D z
    simp [observed_group_count, signedData, signedPair]
  have hobsSum : ∀ s (n : sampling_plan M) (D : sampled_dataset K M n) z,
      observed_group_sum (signedData s D) z = sign s z * observed_group_sum D z := by
    intro s n D z
    simp only [observed_group_sum, signedData, signedPair]
    simp_rw [show ∀ m i, (if (D m i).1 = z then sign s (D m i).1 * (D m i).2 else 0) =
        sign s z * (if (D m i).1 = z then (D m i).2 else 0) by
      intro m i
      split_ifs with h
      · rw [h]
      · simp]
    simp [Finset.mul_sum]
  have hobsMean : ∀ s (n : sampling_plan M) (D : sampled_dataset K M n) z,
      observed_group_mean (signedData s D) z = sign s z * observed_group_mean D z := by
    intro s n D z
    rw [observed_group_mean, observed_group_mean, hobsCount, hobsSum]
    split_ifs <;> ring
  have hscalarLoss : ∀ s (n : sampling_plan M) (D : sampled_dataset K M n),
      (post_stratified_estimator u (signedData s D) -
          target_population_mean u (signedModel s)) ^ 2 =
        (∑ z, (1 / (K : ℝ)) *
          sign s z * (observed_group_mean D z - conditional_group_mean P z)) ^ 2 := by
    intro s n D
    rw [post_stratified_estimator, target_population_mean]
    simp_rw [hu, hobsMean, hsignedMean]
    simp only [uniform_group_mass]
    congr 1
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  let flipAt (z : Fin K) : (Fin K → Bool) ≃ (Fin K → Bool) := {
    toFun := fun s j => if j = z then !(s j) else s j
    invFun := fun s j => if j = z then !(s j) else s j
    left_inv := by
      intro s
      funext j
      by_cases h : j = z <;> simp [h]
    right_inv := by
      intro s
      funext j
      by_cases h : j = z <;> simp [h] }
  have horth : ∀ z w, (∑ s : Fin K → Bool, sign s z * sign s w) =
      if z = w then Fintype.card (Fin K → Bool) else 0 := by
    intro z w
    by_cases hzw : z = w
    · subst w
      simp only [if_pos rfl]
      simp_rw [show ∀ s : Fin K → Bool, sign s z * sign s z = 1 by
        intro s
        cases h : s z <;> simp [sign, h]]
      simp
    · simp only [if_neg hzw]
      let f : (Fin K → Bool) → ℝ := fun s => sign s z * sign s w
      have hreindex : ∑ s, f (flipAt z s) = ∑ s, f s :=
        Equiv.sum_comp (flipAt z) f
      have hneg : ∀ s, f (flipAt z s) = -f s := by
        intro s
        have hwz : w ≠ z := Ne.symm hzw
        cases hsz : s z <;> cases hsw : s w <;>
          simp [f, flipAt, sign, hzw, hwz, hsz, hsw]
      have hsumneg : ∑ s, f (flipAt z s) = ∑ s, -f s :=
        Finset.sum_congr rfl (fun s _ => hneg s)
      have heq : ∑ s, f s = -∑ s, f s := by
        rw [Finset.sum_neg_distrib] at hsumneg
        exact hreindex.symm.trans hsumneg
      have hz : ∑ s, f s = 0 := by linarith
      simpa [f] using hz
  have hscalar : ∀ s : Fin K → Bool, ∃ r : ℝ → ℝ,
      Asymptotics.IsLittleO Filter.atTop r inverse_budget_rate ∧
      ∀ B, 0 < B →
        population_mean_risk pu (plans B) (post_stratified_estimator u)
            (signedModel s) ≤ population_leading_risk pu (plans B) B + r B := by
    intro s
    simpa [pu] using
      (post_stratified_optimal_risk_upper pu plans hp (signedModel s) (hsclass s))
  choose r hr_small hr_bound using hscalar
  let scale : ℝ := (K : ℝ) ^ 2 / Fintype.card (Fin K → Bool)
  have hrad : ∀ e : Fin K → ℝ,
      scale * ∑ s : Fin K → Bool, (∑ z, (1 / (K : ℝ)) * sign s z * e z) ^ 2 =
        ∑ z, (e z) ^ 2 := by
    intro e
    let a : (Fin K → Bool) → Fin K → ℝ := fun s z =>
      (1 / (K : ℝ)) * sign s z * e z
    have hexpand : ∀ s, (∑ z, a s z) ^ 2 = ∑ z, ∑ w, a s z * a s w := by
      intro s
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.mul_sum]
    have hreorder : scale * ∑ s, ∑ z, ∑ w, a s z * a s w =
        ∑ z, ∑ w, scale * ∑ s, a s z * a s w := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.sum_comm]
    change scale * ∑ s, (∑ z, a s z) ^ 2 = ∑ z, (e z) ^ 2
    simp_rw [hexpand]
    rw [hreorder]
    apply Finset.sum_congr rfl
    intro z hz
    calc
      (∑ w, scale * ∑ s, a s z * a s w) =
          ∑ w, if z = w then (e z) ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro w hw
        have hfactor : (∑ s, a s z * a s w) =
            ((1 / (K : ℝ)) ^ 2 * e z * e w) * ∑ s, sign s z * sign s w := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          simp [a]
          ring
        rw [hfactor, horth]
        by_cases hzw : z = w
        · subst w
          simp only [if_pos rfl, Nat.cast_ofNat]
          have hk : (K : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne K
          have hc : (Fintype.card (Fin K → Bool) : ℝ) ≠ 0 := by
            exact_mod_cast Fintype.card_ne_zero
          dsimp [scale]
          field_simp
        · simp [hzw]
      _ = (e z) ^ 2 := by simp
  let remainder : ℝ → ℝ := fun B => scale * ∑ s : Fin K → Bool, r s B
  refine ⟨remainder, ?_, ?_⟩
  · have hsum : (fun B => ∑ s : Fin K → Bool, r s B) =o[Filter.atTop]
        inverse_budget_rate := by
      simpa using (Asymptotics.IsLittleO.sum (s := Finset.univ)
        (fun s _ => hr_small s))
    exact hsum.const_mul_left scale
  · intro B hB
    let n := plans B
    let μ := sampling_law p n P
    let err : sampled_dataset K M n → Fin K → ℝ := fun D z =>
      observed_group_mean D z - conditional_group_mean P z
    let loss : (Fin K → Bool) → sampled_dataset K M n → ℝ := fun s D =>
      (∑ z, (1 / (K : ℝ)) * sign s z * err D z) ^ 2
    let vloss : sampled_dataset K M n → ℝ := fun D => ∑ z, (err D z) ^ 2
    have herr_meas : ∀ z, Measurable (fun D : sampled_dataset K M n => err D z) := by
      intro z
      exact ((measurable_pi_apply z).comp
        (vector_of_means_estimator_measurable n)).sub measurable_const
    have hloss_meas : ∀ s, Measurable (loss s) := by
      intro s
      apply Measurable.pow_const
      apply Finset.measurable_sum Finset.univ
      intro z hz
      exact (measurable_const.mul measurable_const).mul (herr_meas z)
    have hvloss_meas : Measurable vloss := by
      apply Finset.measurable_sum Finset.univ
      intro z hz
      exact (herr_meas z).pow_const 2
    have hpoint : ∀ D, scale * ∑ s, loss s D = vloss D := by
      intro D
      exact hrad (err D)
    have hscale : 0 < scale := by
      have hk : 0 < (K : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
      have hc : 0 < (Fintype.card (Fin K → Bool) : ℝ) := by positivity
      dsimp [scale]
      positivity
    have hriskrepr : ∀ s, population_mean_risk pu n (post_stratified_estimator u)
        (signedModel s) = ∫ D, loss s D ∂μ := by
      intro s
      rw [population_mean_risk, hsampling]
      change (∫ D, (post_stratified_estimator u D -
        target_population_mean u (signedModel s)) ^ 2
          ∂Measure.map (signedData s) (sampling_law p n P)) = _
      have hm : AEStronglyMeasurable (fun D : sampled_dataset K M n =>
          (post_stratified_estimator u D - target_population_mean u (signedModel s)) ^ 2)
          (Measure.map (signedData s) (sampling_law p n P)) :=
        (((post_stratified_estimator_measurable u n).sub measurable_const).pow_const 2).aestronglyMeasurable
      rw [MeasureTheory.integral_map (hsignedData_meas s n).aemeasurable hm]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with D
      exact hscalarLoss s n D
    have hlead : group_leading_risk p n B + remainder B =
        scale * ∑ s : Fin K → Bool,
          (population_leading_risk pu n B + r s B) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [mul_add]
      change group_leading_risk p n B + scale * ∑ s, r s B =
        scale * ((Fintype.card (Fin K → Bool) : ℝ) *
          population_leading_risk pu n B) + scale * ∑ s, r s B
      congr 1
      simp [group_leading_risk, population_leading_risk, pu, hu, scale,
        plan_discrepancy, source_mixture_mass]
      field_simp
    rw [hlead]
    have hsum_bound : (∑ s, population_mean_risk pu n
          (post_stratified_estimator u) (signedModel s)) ≤
        ∑ s, (population_leading_risk pu n B + r s B) := by
      apply Finset.sum_le_sum
      intro s hs
      exact hr_bound s B hB
    have hrhs_nonneg : 0 ≤ scale * ∑ s,
        (population_leading_risk pu n B + r s B) := by
      apply mul_nonneg (le_of_lt hscale)
      apply Finset.sum_nonneg
      intro s hs
      refine le_trans ?_ (hr_bound s B hB)
      rw [hriskrepr]
      exact MeasureTheory.integral_nonneg (fun D => sq_nonneg _)
    by_cases hvi : Integrable vloss μ
    · have hloss_int : ∀ s, Integrable (loss s) μ := by
        intro s
        apply Integrable.mono_nonneg ((hvi.const_mul (scale⁻¹)))
          (hloss_meas s).aestronglyMeasurable
        · filter_upwards with D
          exact sq_nonneg _
        · filter_upwards with D
          have hle : loss s D ≤ ∑ t, loss t D :=
            Finset.single_le_sum (fun t _ => (show 0 ≤ loss t D from sq_nonneg _))
              (Finset.mem_univ s)
          rw [inv_mul_eq_div]
          apply (le_div_iff₀ hscale).2
          calc
            loss s D * scale = scale * loss s D := by ring
            _ ≤ scale * ∑ t, loss t D :=
              mul_le_mul_of_nonneg_left hle (le_of_lt hscale)
            _ = vloss D := hpoint D
      rw [group_means_risk]
      change (∫ D, vloss D ∂μ) ≤ _
      simp_rw [← hpoint]
      rw [integral_const_mul_of_integrable
        (MeasureTheory.integrable_finsetSum Finset.univ (fun s _ => hloss_int s))]
      rw [MeasureTheory.integral_finsetSum Finset.univ (fun s _ => hloss_int s)]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hscale)
      simpa only [hriskrepr] using hsum_bound
    · rw [group_means_risk]
      change (∫ D, vloss D ∂μ) ≤ _
      rw [MeasureTheory.integral_undef hvi]
      exact hrhs_nonneg

@[blueprint "def:two-point-location-model-local"
  (statement := /-- Given a biased-source problem, a direction $v\in\mathbb R^K$, and a scalar parameter $\theta$, assign to group $z$ a two-point law on $\{\pm\sqrt{\sigma^2}\}$ whose positive-point mass is the projection of $(1+\theta v_z/\sqrt{\sigma^2})/2$ onto $[0,1]$. -/)
  (title := /-- Clamped two-point location submodel -/)
  (latexEnv := "definition")]
noncomputable def two_point_location_model_local {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ) :
    conditional_outcome_model K := fun z =>
  let s : ℝ := Real.sqrt p.varianceBound
  let r : ℝ := max 0 (min 1 ((1 + θ * v z / s) / 2))
  have hr0 : 0 ≤ r := le_max_left _ _
  have hr1 : r ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  let q : NNReal := ⟨r, hr0⟩
  have hqle : q ≤ 1 := hr1
  let qc : NNReal := 1 - q
  have hq : q + qc = 1 := add_tsub_cancel_of_le hqle
  let μ : Measure ℝ := q • Measure.dirac s + qc • Measure.dirac (-s)
  ⟨μ, ⟨by
    simpa [μ, ← NNReal.coe_add] using
      congrArg (fun x : NNReal => (x : ENNReal)) hq⟩⟩

@[blueprint "lem:two-point-location-model-mean-local"
  (statement := /-- Suppose that $\sigma^2>0$ and $|\theta v_z|\le\sqrt{\sigma^2}$ for every group $z$. Then the conditional mean in group $z$ under the clamped two-point location model is exactly $\theta v_z$. -/)
  (proof := /-- The parameter bound puts $(1+\theta v_z/\sqrt{\sigma^2})/2$ in $[0,1]$, so the projection in \cref{def:two-point-location-model-local} is inactive. Expanding the integral against the two Dirac masses gives the weighted average of $\sqrt{\sigma^2}$ and $-\sqrt{\sigma^2}$, which simplifies to $\theta v_z$. -/)
  (title := /-- Mean of the two-point location submodel -/)
  (latexEnv := "lemma")]
lemma two_point_location_model_mean_local {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (hvar : 0 < p.varianceBound)
    (hparam : ∀ z, |θ * v z| ≤ Real.sqrt p.varianceBound) (z : Fin K) :
    conditional_group_mean (two_point_location_model_local p v θ) z = θ * v z := by
  let s : ℝ := Real.sqrt p.varianceBound
  have hs : 0 < s := Real.sqrt_pos.2 hvar
  have hz := abs_le.mp (hparam z)
  have hlo : -1 ≤ θ * v z / s := (le_div_iff₀ hs).2 (by linarith)
  have hhi : θ * v z / s ≤ 1 := (div_le_iff₀ hs).2 (by linarith)
  have hr0 : 0 ≤ (1 + θ * v z / s) / 2 := by linarith
  have hr1 : (1 + θ * v z / s) / 2 ≤ 1 := by linarith
  have hr0' : 0 ≤ (1 + θ * v z / Real.sqrt p.varianceBound) / 2 := by
    simpa [s] using hr0
  have hr1' : (1 + θ * v z / Real.sqrt p.varianceBound) / 2 ≤ 1 := by
    simpa [s] using hr1
  rw [conditional_group_mean]
  unfold two_point_location_model_local
  simp only [min_eq_right hr1', max_eq_right hr0']
  simp [MeasureTheory.integral_add_measure]
  apply Eq.trans (MeasureTheory.integral_add_measure
    ((MeasureTheory.integrable_dirac (by simp)).smul_measure_nnreal)
    ((MeasureTheory.integrable_dirac (by simp)).smul_measure_nnreal))
  simp
  simp only [NNReal.smul_def]
  let q : NNReal :=
    ⟨(1 + θ * v z / Real.sqrt p.varianceBound) / 2, hr0'⟩
  have hqle : q ≤ 1 := hr1'
  change (q : ℝ) * Real.sqrt p.varianceBound -
      ((1 - q : NNReal) : ℝ) * Real.sqrt p.varianceBound = θ * v z
  rw [NNReal.coe_sub hqle]
  simp only [NNReal.coe_one]
  change ((1 + θ * v z / Real.sqrt p.varianceBound) / 2) *
      Real.sqrt p.varianceBound -
      (1 - (1 + θ * v z / Real.sqrt p.varianceBound) / 2) *
        Real.sqrt p.varianceBound = θ * v z
  field_simp
  ring

@[blueprint "lem:finite-measure-sum-product-left-local"
  (statement := /-- For a finite set $s$, product measure distributes over the finite sum in its left factor:
  \[
  \left(\sum_{i\in s}\mu_i\right)\otimes\nu
  =\sum_{i\in s}(\mu_i\otimes\nu).
  \] -/)
  (proof := /-- Induct on the finite set. The empty case is the zero product measure, and the insertion step follows from additivity of product measure in its left factor. -/)
  (title := /-- Left-linearity of product measure over finite sums -/)
  (latexEnv := "lemma")]
lemma finite_measure_sum_product_left_local {ι α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (s : Finset ι)
    (μ : ι → Measure α) (ν : Measure β) [∀ i, IsFiniteMeasure (μ i)] [SFinite ν] :
    (∑ i ∈ s, μ i).prod ν = ∑ i ∈ s, (μ i).prod ν := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert, ha, not_false_eq_true]
      rw [add_comm]
      rw [Measure.add_prod (μ a)]
      rw [ih, add_comm]

@[blueprint "lem:finite-measure-sum-map-local"
  (statement := /-- A measurable pushforward distributes over a finite sum of measures. -/)
  (proof := /-- Induct on the finite set, using that pushforward preserves the zero measure and addition for a measurable map. -/)
  (title := /-- Linearity of measurable pushforward over finite sums -/)
  (latexEnv := "lemma")]
lemma finite_measure_sum_map_local {ι α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (s : Finset ι)
    (μ : ι → Measure α) (f : α → β) (hf : Measurable f) :
    (∑ i ∈ s, μ i).map f = ∑ i ∈ s, (μ i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [ha, Measure.map_add, hf, ih]

@[blueprint "lem:finite-pmf-measure-dirac-expansion-local"
  (statement := /-- On a finite measurable space with measurable singletons, the measure associated with a probability mass function $q$ is the finite sum $\sum_x q(x)\delta_x$. -/)
  (proof := /-- Extensionality reduces the claim to a measurable set. The finite-space evaluation formula for the measure of a probability mass function is the sum of its masses over that set, while evaluating the weighted Dirac sum gives the same indicator sum. -/)
  (title := /-- Dirac expansion of a finite probability mass function -/)
  (latexEnv := "lemma")]
lemma finite_pmf_measure_dirac_expansion_local {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (q : PMF α) :
    q.toMeasure = ∑ x, (q x).toNNReal • Measure.dirac x := by
  ext A hA
  simp [PMF.toMeasure_apply_fintype, hA]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : x ∈ A <;> simp [h, ENNReal.coe_toNNReal (q.apply_ne_top x)]

@[blueprint "lem:source-observation-law-mixture-local"
  (statement := /-- For any conditional outcome model $P$ and source $m$, the source observation law is the finite mixture
  \[
  \sum_z q_{S,m}(z)\,(y\mapsto(z,y))_\#P_z.
  \] -/)
  (proof := /-- Expand the source PMF measure by \cref{lem:finite-pmf-measure-dirac-expansion-local}. Distribute product measure and pushforward over the finite sum using \cref{lem:finite-measure-sum-product-left-local,lem:finite-measure-sum-map-local}. For a fixed group $z$, product with $\delta_z$ fixes the first coordinate, and the coordinate marginal theorem for the finite product law sends evaluation at $z$ to $P_z$ because every other factor has total mass one. -/)
  (title := /-- Mixture representation of one source observation -/)
  (latexEnv := "lemma")]
lemma source_observation_law_mixture_local {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (P : conditional_outcome_model K)
    (m : Fin M) :
    source_observation_law p P m =
      ∑ z, (p.sourceGroup m z).toNNReal •
        (P z : Measure ℝ).map (Prod.mk z) := by
  classical
  let ν : Measure (Fin K → ℝ) := Measure.pi fun z => (P z : Measure ℝ)
  let f : Fin K × (Fin K → ℝ) → Fin K × ℝ := fun x => (x.1, x.2 x.1)
  have heval : Measurable (fun x : Fin K × (Fin K → ℝ) => x.2 x.1) := by
    have heq : (fun x : Fin K × (Fin K → ℝ) => x.2 x.1) =
        fun x => ∑ z, if x.1 = z then x.2 z else 0 := by
      funext x
      simp
    rw [heq]
    apply Finset.measurable_sum
    intro z hz
    apply Measurable.ite
    · exact measurable_fst (MeasurableSet.singleton z)
    · exact (measurable_pi_apply z).comp measurable_snd
    · exact measurable_const
  have hf : Measurable f := measurable_fst.prodMk heval
  rw [source_observation_law,
    finite_pmf_measure_dirac_expansion_local (p.sourceGroup m)]
  change ((∑ z, (p.sourceGroup m z).toNNReal • Measure.dirac z).prod ν).map f = _
  have hprod :
      (∑ z, (p.sourceGroup m z).toNNReal • Measure.dirac z).prod ν =
        ∑ z, ((p.sourceGroup m z).toNNReal • Measure.dirac z).prod ν := by
    simpa using finite_measure_sum_product_left_local
      (Finset.univ : Finset (Fin K))
      (fun z => (p.sourceGroup m z).toNNReal • Measure.dirac z) ν
  rw [hprod]
  have hmap :
      (∑ z, ((p.sourceGroup m z).toNNReal • Measure.dirac z).prod ν).map f =
        ∑ z, (((p.sourceGroup m z).toNNReal • Measure.dirac z).prod ν).map f := by
    simpa using finite_measure_sum_map_local (Finset.univ : Finset (Fin K))
      (fun z => ((p.sourceGroup m z).toNNReal • Measure.dirac z).prod ν) f hf
  rw [hmap]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Measure.prod_smul_left, Measure.map_smul]
  congr 1
  rw [Measure.dirac_prod]
  have hcoord : ν.map (Function.eval z) = (P z : Measure ℝ) := by
    simpa [ν] using Measure.pi_map_eval (fun z => (P z : Measure ℝ)) z
  calc
    (ν.map (Prod.mk z)).map f = ν.map (f ∘ Prod.mk z) :=
      Measure.map_map hf measurable_prodMk_left
    _ = ν.map (Prod.mk z ∘ Function.eval z) := by
      apply Measure.map_congr
      filter_upwards with x
      rfl
    _ = (ν.map (Function.eval z)).map (Prod.mk z) :=
      (Measure.map_map measurable_prodMk_left (measurable_pi_apply z)).symm
    _ = (P z : Measure ℝ).map (Prod.mk z) := by rw [hcoord]

@[blueprint "def:two-point-boolean-value-local"
  (statement := /-- Encode a Boolean sign as the outcome $\sqrt{\sigma^2}$ for `true` and $-\sqrt{\sigma^2}$ for `false`. -/)
  (title := /-- Boolean encoding of the two-point outcomes -/)
  (latexEnv := "definition")]
noncomputable def two_point_boolean_value_local {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (b : Bool) : ℝ :=
  if b then Real.sqrt p.varianceBound else -Real.sqrt p.varianceBound

@[blueprint "def:two-point-boolean-measure-local"
  (statement := /-- The Boolean form of the clamped two-point law gives `true` the projected mass $(1+\theta v_z/\sqrt{\sigma^2})/2$ and gives `false` the complementary mass. -/)
  (title := /-- Boolean measure for the two-point location submodel -/)
  (latexEnv := "definition")]
noncomputable def two_point_boolean_measure_local {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (z : Fin K) : Measure Bool :=
  let s : ℝ := Real.sqrt p.varianceBound
  let r : ℝ := max 0 (min 1 ((1 + θ * v z / s) / 2))
  let q : NNReal := ⟨r, le_max_left _ _⟩
  q • Measure.dirac true + (1 - q) • Measure.dirac false

@[blueprint "lem:two-point-boolean-measure-map-local"
  (statement := /-- Mapping the Boolean two-point measure through the outcome encoding recovers the corresponding conditional law in \cref{def:two-point-location-model-local}. -/)
  (proof := /-- Expand the Boolean measure and use linearity of measure pushforward. The Dirac mass at `true` maps to $\sqrt{\sigma^2}$ and the Dirac mass at `false` maps to $-\sqrt{\sigma^2}$, with exactly the coefficients in \cref{def:two-point-location-model-local}. -/)
  (title := /-- Boolean representation of the two-point conditional law -/)
  (latexEnv := "lemma")]
lemma two_point_boolean_measure_map_local {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (z : Fin K) :
    (two_point_boolean_measure_local p v θ z).map
        (two_point_boolean_value_local p) =
      (two_point_location_model_local p v θ z : Measure ℝ) := by
  unfold two_point_boolean_measure_local two_point_boolean_value_local
    two_point_location_model_local
  rw [Measure.map_add _ _ (measurable_of_finite _)]
  simp

@[blueprint "lem:two-point-boolean-measure-univ-local"
  (statement := /-- The Boolean two-point measure has total mass one. -/)
  (proof := /-- Push the measure forward by the Boolean outcome encoding. By \cref{lem:two-point-boolean-measure-map-local} the result is the probability measure in \cref{def:two-point-location-model-local}; pushforward preserves total mass. -/)
  (title := /-- Total mass of the Boolean two-point measure -/)
  (latexEnv := "lemma")]
lemma two_point_boolean_measure_univ_local {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (z : Fin K) : two_point_boolean_measure_local p v θ z Set.univ = 1 := by
  have h := congrArg (fun μ : Measure ℝ => μ Set.univ)
    (two_point_boolean_measure_map_local p v θ z)
  simpa [Measure.map_apply (measurable_of_finite _) MeasurableSet.univ] using h

@[blueprint "def:two-point-source-boolean-measure-local"
  (statement := /-- For source $m$, the finite Boolean observation law assigns group $z$ according to $q_{S,m}$ and then draws the Boolean two-point outcome for that group. -/)
  (title := /-- Finite Boolean law for one source observation -/)
  (latexEnv := "definition")]
noncomputable def two_point_source_boolean_measure_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (m : Fin M) : Measure (Fin K × Bool) :=
  ∑ z, (p.sourceGroup m z).toNNReal •
    (two_point_boolean_measure_local p v θ z).map (Prod.mk z)

@[blueprint "def:two-point-boolean-mass-local"
  (statement := /-- The nonnegative-real mass of a Boolean outcome in the clamped two-point law is the projected affine probability for `true` and its complement for `false`. -/)
  (title := /-- Atom mass in the Boolean two-point law -/)
  (latexEnv := "definition")]
noncomputable def two_point_boolean_mass_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (z : Fin K) (b : Bool) : NNReal :=
  let s : ℝ := Real.sqrt p.varianceBound
  let r : ℝ := max 0 (min 1 ((1 + θ * v z / s) / 2))
  let q : NNReal := ⟨r, le_max_left _ _⟩
  if b then q else 1 - q

@[blueprint "def:two-point-source-boolean-mass-local"
  (statement := /-- The atom mass of $(z,b)$ under source $m$ is $q_{S,m}(z)$ times the Boolean conditional mass at group $z$. -/)
  (title := /-- Atom mass in a Boolean source observation -/)
  (latexEnv := "definition")]
noncomputable def two_point_source_boolean_mass_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (m : Fin M) (x : Fin K × Bool) : NNReal :=
  (p.sourceGroup m x.1).toNNReal *
    two_point_boolean_mass_local p v θ x.1 x.2

@[blueprint "def:two-point-dataset-boolean-mass-local"
  (statement := /-- The atom mass of a Boolean sampled dataset is the product of its source-observation atom masses over all planned observations. -/)
  (title := /-- Atom mass of a Boolean sampled dataset -/)
  (latexEnv := "definition")]
noncomputable def two_point_dataset_boolean_mass_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (v : Fin K → ℝ) (θ : ℝ)
    (D : (m : Fin M) → Fin (n m) → Fin K × Bool) : NNReal :=
  ∏ m, ∏ i, two_point_source_boolean_mass_local p v θ m (D m i)

@[blueprint "lem:two-point-boolean-measure-singleton-local"
  (statement := /-- The measure of a Boolean singleton equals its atom mass in \cref{def:two-point-boolean-mass-local}. -/)
  (proof := /-- Expand the two weighted Dirac masses in \cref{def:two-point-boolean-measure-local} and split on the Boolean atom. In either case exactly one Dirac mass contributes. -/)
  (title := /-- Singleton mass of the Boolean two-point law -/)
  (latexEnv := "lemma")]
lemma two_point_boolean_measure_singleton_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (z : Fin K) (b : Bool) :
    two_point_boolean_measure_local p v θ z {b} =
      (two_point_boolean_mass_local p v θ z b : ENNReal) := by
  unfold two_point_boolean_measure_local two_point_boolean_mass_local
  cases b <;> simp

@[blueprint "lem:two-point-source-boolean-measure-singleton-local"
  (statement := /-- The finite Boolean source measure of the singleton $(z,b)$ equals the source atom mass in \cref{def:two-point-source-boolean-mass-local}. -/)
  (proof := /-- Expand the finite group mixture in \cref{def:two-point-source-boolean-measure-local}. Only the component indexed by $z$ can map into the singleton $(z,b)$; its value is the source group mass times the conditional singleton mass from \cref{lem:two-point-boolean-measure-singleton-local}. -/)
  (title := /-- Singleton mass of a Boolean source observation -/)
  (latexEnv := "lemma")]
lemma two_point_source_boolean_measure_singleton_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (m : Fin M) (x : Fin K × Bool) :
    two_point_source_boolean_measure_local p v θ m {x} =
      (two_point_source_boolean_mass_local p v θ m x : ENNReal) := by
  classical
  unfold two_point_source_boolean_measure_local
    two_point_source_boolean_mass_local
  rw [show (∑ z, (p.sourceGroup m z).toNNReal •
      (two_point_boolean_measure_local p v θ z).map (Prod.mk z)) {x} =
      ∑ z, (((p.sourceGroup m z).toNNReal •
        (two_point_boolean_measure_local p v θ z).map (Prod.mk z)) {x}) by
    simpa using Measure.finsetSum_apply (Finset.univ : Finset (Fin K))
      (fun z => (p.sourceGroup m z).toNNReal •
        (two_point_boolean_measure_local p v θ z).map (Prod.mk z)) {x}]
  simp only [Measure.smul_apply]
  simp_rw [Measure.map_apply measurable_prodMk_left (MeasurableSet.singleton x)]
  rw [Finset.sum_eq_single x.1]
  · have hpre : Prod.mk x.1 ⁻¹' ({x} : Set (Fin K × Bool)) = {x.2} := by
      ext b
      constructor
      · intro hb
        exact congrArg Prod.snd hb
      · intro hb
        have hb' : b = x.2 := by simpa using hb
        simpa [hb']
    rw [hpre, two_point_boolean_measure_singleton_local]
    change ((p.sourceGroup m x.1).toNNReal : ENNReal) *
        (two_point_boolean_mass_local p v θ x.1 x.2 : ENNReal) = _
    rfl
  · intro z hz hne
    have hpre : Prod.mk z ⁻¹' ({x} : Set (Fin K × Bool)) = ∅ := by
      ext b
      constructor
      · intro hb
        exact (hne (congrArg Prod.fst hb)).elim
      · intro hb
        simp at hb
    rw [hpre]
    simp
  · simp

@[blueprint "lem:two-point-source-boolean-measure-univ-local"
  (statement := /-- The finite Boolean law for one source observation has total mass one. -/)
  (proof := /-- Each conditional Boolean measure has mass one by \cref{lem:two-point-boolean-measure-univ-local}. Evaluating the finite source mixture therefore leaves the sum of the source PMF masses, which is one by \cref{lem:finite-pmf-measure-dirac-expansion-local}. -/)
  (title := /-- Total mass of the finite Boolean source law -/)
  (latexEnv := "lemma")]
lemma two_point_source_boolean_measure_univ_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (m : Fin M) : two_point_source_boolean_measure_local p v θ m Set.univ = 1 := by
  classical
  unfold two_point_source_boolean_measure_local
  have hall : ({false, true} : Set Bool) = Set.univ := by
    ext b
    cases b <;> simp
  rw [show (∑ z, (p.sourceGroup m z).toNNReal •
      (two_point_boolean_measure_local p v θ z).map (Prod.mk z)) Set.univ =
      ∑ z, (((p.sourceGroup m z).toNNReal •
        (two_point_boolean_measure_local p v θ z).map (Prod.mk z)) Set.univ) by
    simpa using Measure.finsetSum_apply (Finset.univ : Finset (Fin K))
      (fun z => (p.sourceGroup m z).toNNReal •
        (two_point_boolean_measure_local p v θ z).map (Prod.mk z)) Set.univ]
  simp_rw [Measure.smul_apply]
  simp_rw [Measure.map_apply measurable_prodMk_left MeasurableSet.univ]
  simp only [Set.preimage_univ, two_point_boolean_measure_univ_local,
    smul_eq_mul, mul_one]
  have h := congrArg (fun μ : Measure (Fin K) => μ Set.univ)
    (finite_pmf_measure_dirac_expansion_local (p.sourceGroup m))
  simpa using h.symm

@[blueprint "lem:two-point-source-boolean-measure-map-local"
  (statement := /-- Mapping the finite Boolean source law through $(z,b)\mapsto(z,\pm\sqrt{\sigma^2})$ gives the source observation law of the two-point conditional model. -/)
  (proof := /-- Use the mixture representation \cref{lem:source-observation-law-mixture-local} for the target source law and distribute pushforward over the finite mixture via \cref{lem:finite-measure-sum-map-local}. On each group component, composition of pushforwards and \cref{lem:two-point-boolean-measure-map-local} identify the Boolean outcome law with the corresponding real-valued conditional law. -/)
  (title := /-- Finite Boolean representation of a source observation -/)
  (latexEnv := "lemma")]
lemma two_point_source_boolean_measure_map_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (m : Fin M) :
    (two_point_source_boolean_measure_local p v θ m).map
        (fun x => (x.1, two_point_boolean_value_local p x.2)) =
      source_observation_law p (two_point_location_model_local p v θ) m := by
  classical
  let g : Fin K × Bool → Fin K × ℝ :=
    fun x => (x.1, two_point_boolean_value_local p x.2)
  have hg : Measurable g := measurable_fst.prodMk
    ((measurable_of_finite (two_point_boolean_value_local p)).comp measurable_snd)
  rw [source_observation_law_mixture_local]
  unfold two_point_source_boolean_measure_local
  change (∑ z, (p.sourceGroup m z).toNNReal •
    (two_point_boolean_measure_local p v θ z).map (Prod.mk z)).map g = _
  rw [finite_measure_sum_map_local (Finset.univ : Finset (Fin K)) _ g hg]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Measure.map_smul]
  congr 1
  rw [Measure.map_map hg measurable_prodMk_left]
  have hvalue : Measurable (two_point_boolean_value_local p) := measurable_of_finite _
  calc
    (two_point_boolean_measure_local p v θ z).map (g ∘ Prod.mk z) =
        (two_point_boolean_measure_local p v θ z).map
          (Prod.mk z ∘ two_point_boolean_value_local p) := by
      apply Measure.map_congr
      filter_upwards with b
      rfl
    _ = ((two_point_boolean_measure_local p v θ z).map
          (two_point_boolean_value_local p)).map (Prod.mk z) :=
      (Measure.map_map measurable_prodMk_left hvalue).symm
    _ = (two_point_location_model_local p v θ z : Measure ℝ).map
          (Prod.mk z) := by
      rw [two_point_boolean_measure_map_local]

@[blueprint "def:boolean-sampled-dataset-local"
  (statement := /-- A Boolean sampled dataset records, for every planned observation, its group label and a Boolean two-point outcome. -/)
  (title := /-- Finite Boolean sampled dataset -/)
  (latexEnv := "definition")]
abbrev boolean_sampled_dataset_local (K M : ℕ) (n : sampling_plan M) :=
  (m : Fin M) → Fin (n m) → Fin K × Bool

@[blueprint "def:two-point-boolean-sampling-measure-local"
  (statement := /-- The Boolean sampling measure is the finite product of the source-specific Boolean observation laws over all planned observations. -/)
  (title := /-- Product sampling law for Boolean two-point data -/)
  (latexEnv := "definition")]
noncomputable def two_point_boolean_sampling_measure_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (v : Fin K → ℝ) (θ : ℝ) : Measure (boolean_sampled_dataset_local K M n) :=
  Measure.pi fun m => Measure.pi fun _i : Fin (n m) =>
    two_point_source_boolean_measure_local p v θ m

@[blueprint "def:two-point-boolean-dataset-encode-local"
  (statement := /-- Encode a Boolean sampled dataset as a real-valued dataset by replacing each Boolean outcome by $\pm\sqrt{\sigma^2}$. -/)
  (title := /-- Encoding Boolean two-point data as real data -/)
  (latexEnv := "definition")]
noncomputable def two_point_boolean_dataset_encode_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (D : boolean_sampled_dataset_local K M n) : sampled_dataset K M n :=
  fun m i => ((D m i).1, two_point_boolean_value_local p (D m i).2)

@[blueprint "lem:two-point-boolean-sampling-measure-map-local"
  (statement := /-- Pushing the finite Boolean product sampling measure through the dataset encoding gives the sampling law of the two-point conditional model. -/)
  (proof := /-- Apply \cref{lem:two-point-source-boolean-measure-map-local} in every observation coordinate. The source measures are finite by \cref{lem:two-point-source-boolean-measure-univ-local}. The finite product pushforward theorem first combines the coordinates within each source and then combines the sources; these two applications give exactly the product law in \cref{def:sampling-law}. -/)
  (title := /-- Finite Boolean representation of the full sampling law -/)
  (latexEnv := "lemma")]
lemma two_point_boolean_sampling_measure_map_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (v : Fin K → ℝ) (θ : ℝ) :
    (two_point_boolean_sampling_measure_local p n v θ).map
        (two_point_boolean_dataset_encode_local p n) =
      sampling_law p n (two_point_location_model_local p v θ) := by
  let encObs : Fin K × Bool → Fin K × ℝ :=
    fun x => (x.1, two_point_boolean_value_local p x.2)
  have hencObs : Measurable encObs := measurable_fst.prodMk
    ((measurable_of_finite (two_point_boolean_value_local p)).comp measurable_snd)
  letI hfinSource : ∀ m, IsFiniteMeasure
      (two_point_source_boolean_measure_local p v θ m) := fun m =>
    ⟨by rw [two_point_source_boolean_measure_univ_local]; simp⟩
  have hinner : ∀ m, Measure.pi (fun _i : Fin (n m) =>
      source_observation_law p (two_point_location_model_local p v θ) m) =
      Measure.map (fun d i => encObs (d i))
        (Measure.pi fun _i : Fin (n m) =>
          two_point_source_boolean_measure_local p v θ m) := by
    intro m
    simp_rw [← two_point_source_boolean_measure_map_local p v θ m]
    symm
    exact Measure.pi_map_pi (fun _i => hencObs.aemeasurable)
  rw [sampling_law]
  unfold two_point_boolean_sampling_measure_local
  simp_rw [hinner]
  letI hfinPi : ∀ m, IsFiniteMeasure
      (Measure.pi fun _i : Fin (n m) =>
        two_point_source_boolean_measure_local p v θ m) := fun m => inferInstance
  letI hfinMap : ∀ m, IsFiniteMeasure
      (Measure.map (fun d i => encObs (d i))
        (Measure.pi fun _i : Fin (n m) =>
          two_point_source_boolean_measure_local p v θ m)) := fun m => inferInstance
  letI hSigma : ∀ m, SigmaFinite
      (Measure.map (fun d i => encObs (d i))
        (Measure.pi fun _i : Fin (n m) =>
          two_point_source_boolean_measure_local p v θ m)) := fun m => by
    letI := hfinMap m
    infer_instance
  have houter : ∀ m, Measurable
      (fun d : (i : Fin (n m)) → Fin K × Bool => fun i => encObs (d i)) := by
    intro m
    fun_prop
  unfold two_point_boolean_dataset_encode_local
  convert Measure.pi_map_pi (hμ := hSigma) (fun m => (houter m).aemeasurable) using 1

@[blueprint "lem:two-point-boolean-sampling-measure-singleton-local"
  (statement := /-- The Boolean product sampling measure of a dataset singleton equals the product atom mass in \cref{def:two-point-dataset-boolean-mass-local}. -/)
  (proof := /-- Write the dataset singleton as the dependent product of its coordinate singletons and apply the finite-product rectangle formula twice, first over observations within a source and then over sources. The source measures are finite by \cref{lem:two-point-source-boolean-measure-univ-local}. Each coordinate factor is identified by \cref{lem:two-point-source-boolean-measure-singleton-local}; the resulting product is exactly \cref{def:two-point-dataset-boolean-mass-local}. -/)
  (title := /-- Singleton mass of a Boolean sampled dataset -/)
  (latexEnv := "lemma")]
lemma two_point_boolean_sampling_measure_singleton_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (v : Fin K → ℝ) (θ : ℝ) (D : boolean_sampled_dataset_local K M n) :
    two_point_boolean_sampling_measure_local p n v θ {D} =
      (two_point_dataset_boolean_mass_local p n v θ D : ENNReal) := by
  letI hfinSource : ∀ m, IsFiniteMeasure
      (two_point_source_boolean_measure_local p v θ m) := fun m =>
    ⟨by rw [two_point_source_boolean_measure_univ_local]; simp⟩
  letI hfinPi : ∀ m, IsFiniteMeasure
      (Measure.pi fun _i : Fin (n m) =>
        two_point_source_boolean_measure_local p v θ m) := fun m => inferInstance
  have hinner (m : Fin M) : ({D m} : Set (Fin (n m) → Fin K × Bool)) =
      Set.pi Set.univ (fun i => {D m i}) := by
    ext d
    simp [funext_iff]
  have houter : ({D} : Set (boolean_sampled_dataset_local K M n)) =
      Set.pi Set.univ (fun m => {D m}) := by
    ext d
    simp [funext_iff]
  unfold two_point_boolean_sampling_measure_local
  rw [houter, Measure.pi_pi]
  simp_rw [hinner, Measure.pi_pi,
    two_point_source_boolean_measure_singleton_local]
  unfold two_point_dataset_boolean_mass_local
  norm_cast

@[blueprint "lem:two-point-location-model-variance-local"
  (statement := /-- Under the hypotheses of \cref{lem:two-point-location-model-mean-local}, the conditional variance in group $z$ is $\sigma^2-(\theta v_z)^2$. -/)
  (proof := /-- Use \cref{lem:two-point-location-model-mean-local} to center the identity random variable at $\theta v_z$. The parameter bound again makes the clamp in \cref{def:two-point-location-model-local} inactive. Expanding the centered second moment over the two Dirac atoms and using $(\sqrt{\sigma^2})^2=\sigma^2$ gives the formula. -/)
  (title := /-- Variance of the two-point location submodel -/)
  (latexEnv := "lemma")]
lemma two_point_location_model_variance_local {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (hvar : 0 < p.varianceBound)
    (hparam : ∀ z, |θ * v z| ≤ Real.sqrt p.varianceBound) (z : Fin K) :
    ProbabilityTheory.variance id
        (two_point_location_model_local p v θ z : Measure ℝ) =
      p.varianceBound - (θ * v z) ^ 2 := by
  let s : ℝ := Real.sqrt p.varianceBound
  have hs : 0 < s := Real.sqrt_pos.2 hvar
  have hz := abs_le.mp (hparam z)
  have hlo : -1 ≤ θ * v z / s := (le_div_iff₀ hs).2 (by linarith)
  have hhi : θ * v z / s ≤ 1 := (div_le_iff₀ hs).2 (by linarith)
  have hr0 : 0 ≤ (1 + θ * v z / s) / 2 := by linarith
  have hr1 : (1 + θ * v z / s) / 2 ≤ 1 := by linarith
  have hr0' : 0 ≤ (1 + θ * v z / Real.sqrt p.varianceBound) / 2 := by
    simpa [s] using hr0
  have hr1' : (1 + θ * v z / Real.sqrt p.varianceBound) / 2 ≤ 1 := by
    simpa [s] using hr1
  have hm := two_point_location_model_mean_local p v θ hvar hparam z
  rw [conditional_group_mean] at hm
  rw [ProbabilityTheory.variance_eq_integral measurable_id.aemeasurable]
  change (∫ ω, (ω - (∫ x, x ∂(two_point_location_model_local p v θ z :
      Measure ℝ))) ^ 2 ∂(two_point_location_model_local p v θ z : Measure ℝ)) = _
  rw [hm]
  unfold two_point_location_model_local
  simp only [min_eq_right hr1', max_eq_right hr0']
  simp [MeasureTheory.integral_add_measure]
  apply Eq.trans (MeasureTheory.integral_add_measure
    ((MeasureTheory.integrable_dirac (by simp)).smul_measure_nnreal)
    ((MeasureTheory.integrable_dirac (by simp)).smul_measure_nnreal))
  simp
  simp only [NNReal.smul_def]
  let q : NNReal :=
    ⟨(1 + θ * v z / Real.sqrt p.varianceBound) / 2, hr0'⟩
  have hqle : q ≤ 1 := hr1'
  change (q : ℝ) * (Real.sqrt p.varianceBound - θ * v z) ^ 2 +
      ((1 - q : NNReal) : ℝ) * (-Real.sqrt p.varianceBound - θ * v z) ^ 2 =
    p.varianceBound - (θ * v z) ^ 2
  rw [NNReal.coe_sub hqle]
  simp only [NNReal.coe_one]
  change ((1 + θ * v z / Real.sqrt p.varianceBound) / 2) *
      (Real.sqrt p.varianceBound - θ * v z) ^ 2 +
      (1 - (1 + θ * v z / Real.sqrt p.varianceBound) / 2) *
        (-Real.sqrt p.varianceBound - θ * v z) ^ 2 =
    p.varianceBound - (θ * v z) ^ 2
  field_simp
  nlinarith [Real.sq_sqrt (le_of_lt hvar)]

@[blueprint "lem:two-point-location-model-in-class-local"
  (statement := /-- Suppose that $\sigma^2>0$, $|\theta v_z|\le\sqrt{\sigma^2}$, and $|\theta v_z|\le R$ for every group $z$. Then the two-point location model belongs to the bounded conditional-mean class. -/)
  (proof := /-- Each conditional law in \cref{def:two-point-location-model-local} is supported on two finite points, so the identity is square-integrable. Its mean is $\theta v_z$ by \cref{lem:two-point-location-model-mean-local}, which obeys the assumed radius bound. Its variance is $\sigma^2-(\theta v_z)^2$ by \cref{lem:two-point-location-model-variance-local}, hence is at most $\sigma^2$. -/)
  (title := /-- Admissibility of the two-point location submodel -/)
  (latexEnv := "lemma")]
lemma two_point_location_model_in_class_local {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (hvar : 0 < p.varianceBound)
    (hparam : ∀ z, |θ * v z| ≤ Real.sqrt p.varianceBound)
    (hmean : ∀ z, |θ * v z| ≤ p.meanRadius) :
    bounded_conditional_mean_class p (two_point_location_model_local p v θ) := by
  intro z
  refine ⟨?_, ?_, ?_⟩
  · change MeasureTheory.MemLp id 2
      (two_point_location_model_local p v θ z : Measure ℝ)
    unfold two_point_location_model_local
    apply (MeasureTheory.memLp_two_iff_integrable_sq
      measurable_id.aestronglyMeasurable).2
    exact ((MeasureTheory.integrable_dirac (by simp)).smul_measure_nnreal).add_measure
      ((MeasureTheory.integrable_dirac (by simp)).smul_measure_nnreal)
  · rw [two_point_location_model_mean_local p v θ hvar hparam z]
    exact hmean z
  · rw [two_point_location_model_variance_local p v θ hvar hparam z]
    exact sub_le_self _ (sq_nonneg _)

@[blueprint "lem:finite-weighted-information-bound-local"
  (statement := /-- Let $\Omega$ be finite, let $w\colon\Omega\to\mathbb R$ be nonnegative, and let $T,S\colon\Omega\to\mathbb R$. If $d=\sum_x w(x)(T(x)-m)S(x)$ and $\sum_xw(x)S(x)^2\le I$, then
  \[
  d^2\le \left(\sum_xw(x)(T(x)-m)^2\right)I.
  \] -/)
  (proof := /-- Apply the finite-sum Cauchy--Schwarz inequality to the summands $w(x)(T(x)-m)S(x)$, with squared factors $w(x)(T(x)-m)^2$ and $w(x)S(x)^2$. Nonnegativity of $w$ makes both factors nonnegative. The covariance identity replaces the first sum by $d$, and the assumed information bound enlarges the second factor to $I$. -/)
  (title := /-- Finite weighted information inequality -/)
  (latexEnv := "lemma")]
lemma finite_weighted_information_bound_local {Ω : Type*} [Fintype Ω]
    (w T S : Ω → ℝ) (m d I : ℝ) (hw : ∀ x, 0 ≤ w x)
    (hcov : ∑ x, w x * (T x - m) * S x = d)
    (hinfo : ∑ x, w x * (S x) ^ 2 ≤ I) :
    d ^ 2 ≤ (∑ x, w x * (T x - m) ^ 2) * I := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := (Finset.univ : Finset Ω))
    (r := fun x => w x * (T x - m) * S x)
    (f := fun x => w x * (T x - m) ^ 2)
    (g := fun x => w x * (S x) ^ 2)
    (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
    (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
    (fun x _ => le_of_eq (by ring))
  calc
    d ^ 2 = (∑ x, w x * (T x - m) * S x) ^ 2 := by rw [hcov]
    _ ≤ (∑ x, w x * (T x - m) ^ 2) * (∑ x, w x * (S x) ^ 2) := hcs
    _ ≤ (∑ x, w x * (T x - m) ^ 2) * I :=
      mul_le_mul_of_nonneg_left hinfo
        (Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (sq_nonneg _)))

@[blueprint "lem:population-minimax-risk-nonnegative-local"
  (statement := /-- For every biased-source mean-estimation problem and every real budget $B$, the population minimax risk is nonnegative. -/)
  (proof := /-- Unfold the infimum in \cref{def:population-minimax-risk}. Every candidate is a supremum as in \cref{def:population-worst-case-risk}, and every member of its risk set is an integral of a square by \cref{def:population-mean-risk}. Such integrals are nonnegative; hence each supremum and then their infimum are nonnegative. -/)
  (title := /-- Nonnegativity of the population minimax risk -/)
  (latexEnv := "lemma")]
lemma population_minimax_risk_nonnegative_local {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (B : ℝ) :
    0 ≤ population_minimax_risk p B := by
  rw [population_minimax_risk]
  apply Real.sInf_nonneg
  intro r hr
  rcases hr with ⟨n, hn, estimator, hmeas, hrisk, rfl⟩
  rw [population_worst_case_risk]
  apply Real.sSup_nonneg
  intro s hs
  rcases hs with ⟨P, hP, rfl⟩
  rw [population_mean_risk]
  exact MeasureTheory.integral_nonneg (fun D => sq_nonneg _)

@[blueprint "lem:population-minimax-zero-variance-lower-local"
  (statement := /-- If the conditional-variance bound is zero, then for every plan family there is a zero little-$o(B^{-1})$ remainder for which the population leading term is eventually at most the population minimax risk. -/)
  (proof := /-- Take the remainder identically zero, which is little-$o$ of every comparison function. The leading term vanishes because it contains the variance bound as a factor, while the minimax risk is nonnegative by \cref{lem:population-minimax-risk-nonnegative-local}. -/)
  (title := /-- Population lower bound at zero variance -/)
  (latexEnv := "lemma")]
lemma population_minimax_zero_variance_lower_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (hvar : p.varianceBound = 0)
    (plans : ℝ → sampling_plan M) :
    ∃ remainder : ℝ → ℝ,
      Asymptotics.IsLittleO Filter.atTop remainder inverse_budget_rate ∧
      ∀ᶠ B in Filter.atTop,
        population_leading_risk p (plans B) B + remainder B ≤
          population_minimax_risk p B := by
  refine ⟨fun _ => 0,
    Asymptotics.isLittleO_zero inverse_budget_rate Filter.atTop, ?_⟩
  filter_upwards with B
  simpa [population_leading_risk, hvar] using
    population_minimax_risk_nonnegative_local p B

@[blueprint "lem:finite-weighted-expectation-derivative-local"
  (statement := /-- Let $\Omega$ be finite.  If each weight $w_x(\theta)$ has derivative $w'_x(\theta)$, then the weighted expectation $\sum_x w_x(\theta)T_x$ has derivative $\sum_x w'_x(\theta)T_x$. -/)
  (proof := /-- Multiply each coordinate derivative by the constant $T_x$ and apply the derivative rule for a finite sum. -/)
  (title := /-- Derivative of a finite weighted expectation -/)
  (latexEnv := "lemma")]
lemma finite_weighted_expectation_derivative_local {Ω : Type*} [Fintype Ω]
    (w dw : ℝ → Ω → ℝ) (T : Ω → ℝ) (θ : ℝ)
    (hderiv : ∀ x, HasDerivAt (fun t => w t x) (dw θ x) θ) :
    HasDerivAt (∑ x, fun t => w t x * T x) (∑ x, dw θ x * T x) θ := by
  exact HasDerivAt.sum (u := (Finset.univ : Finset Ω))
    fun x _ => (hderiv x).mul_const (T x)

@[blueprint "lem:finite-product-score-derivative-local"
  (statement := /-- Let $s$ be finite. If $f_i'(\theta)=f_i(\theta)S_i$, then
  \[
  \frac{d}{d\theta}\prod_{i\in s}f_i(\theta)
  =\left(\prod_{i\in s}f_i(\theta)\right)\left(\sum_{i\in s}S_i\right).
  \] -/)
  (proof := /-- Induct on the finite set.  The empty product has zero derivative.  At an insertion, apply the ordinary product rule to the new factor and the induction hypothesis, then distribute and collect the two score contributions. -/)
  (title := /-- Derivative of a finite product from coordinate scores -/)
  (latexEnv := "lemma")]
lemma finite_product_score_derivative_local {ι : Type*} (s : Finset ι)
    (f : ℝ → ι → ℝ) (S : ι → ℝ) (θ : ℝ)
    (hderiv : ∀ i ∈ s, HasDerivAt (fun t => f t i) (f θ i * S i) θ) :
    HasDerivAt (∏ i ∈ s, fun t => f t i)
      ((∏ i ∈ s, f θ i) * ∑ i ∈ s, S i) θ := by
  classical
  have h := HasDerivAt.finsetProd hderiv
  have heq :
      (∑ i ∈ s, (∏ j ∈ s.erase i, f θ j) * (f θ i * S i)) =
        (∏ i ∈ s, f θ i) * ∑ i ∈ s, S i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (∏ j ∈ s.erase i, f θ j) * (f θ i * S i) =
          ((∏ j ∈ s.erase i, f θ j) * f θ i) * S i := by ring
      _ = (∏ i ∈ s, f θ i) * S i := by
        rw [Finset.prod_erase_mul s (fun j => f θ j) hi]
  have h' := h
  simp only [smul_eq_mul] at h'
  rw [heq] at h'
  exact h'

@[blueprint "lem:mean-value-bias-slope-bound-local"
  (statement := /-- Let $g$ be differentiable on $\mathbb R$. If $\delta>0$, the endpoint biases relative to the line $\theta\mapsto a\theta$ are at most $u$ in absolute value, and $|g'(\theta)|\le v$ on $(-\delta,\delta)$, then
  \[
  a\le \frac{u}{\delta}+v.
  \] -/)
  (proof := /-- Apply the mean-value theorem on $[-\delta,\delta]$ to obtain $c$ with $2\delta g'(c)=g(\delta)-g(-\delta)$. The endpoint bounds give $g(\delta)-g(-\delta)\ge2a\delta-2u$, whereas the derivative bound gives $g'(c)\le v$. Combining these inequalities and dividing by the positive number $\delta$ yields the claim. -/)
  (title := /-- Mean-value control of bias and slope -/)
  (latexEnv := "lemma")]
lemma mean_value_bias_slope_bound_local
    (g g' : ℝ → ℝ) (a δ u v : ℝ) (hδ : 0 < δ)
    (hderiv : ∀ t ∈ Set.Icc (-δ) δ, HasDerivAt g (g' t) t)
    (hminus : |g (-δ) - a * (-δ)| ≤ u)
    (hplus : |g δ - a * δ| ≤ u)
    (hslope : ∀ t ∈ Set.Ioo (-δ) δ, |g' t| ≤ v) :
    a ≤ u / δ + v := by
  have hcont : ContinuousOn g (Set.Icc (-δ) δ) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcderiv⟩ := exists_hasDerivAt_eq_slope
    g g' (by linarith : -δ < δ) hcont
      (fun t ht => hderiv t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  have hceq : 2 * δ * g' c = g δ - g (-δ) := by
    rw [hcderiv]
    field_simp
    ring
  have hcupper : g' c ≤ v := le_trans (le_abs_self _) (hslope c hc)
  have hmupper : g (-δ) - a * (-δ) ≤ u := le_trans (le_abs_self _) hminus
  have hplower : -u ≤ g δ - a * δ :=
    le_trans (neg_le_neg hplus) (neg_abs_le _)
  have hmul : (a - v) * δ ≤ u := by
    nlinarith
  have hdiv : a - v ≤ u / δ := (le_div_iff₀ hδ).2 hmul
  linarith

@[blueprint "lem:finite-biased-information-bound-local"
  (statement := /-- Let $\Omega$ be finite and let $w_\theta$ be a differentiable family of probability weights. Suppose the derivative of $g(\theta)=\sum_xw_\theta(x)T(x)$ is its covariance with a centered score, the score information is at most $I$, and the squared risk for the target $a\theta$ is at most $R$ throughout $[-\delta,\delta]$. If $\delta>0$, $R\ge0$, and $I\ge0$, then
  \[
  a\le \frac{\sqrt R}{\delta}+\sqrt{RI}.
  \] -/)
  (proof := /-- At either endpoint, apply \cref{lem:finite-weighted-information-bound-local} with the constant score one and use normalization of the weights; this bounds the absolute bias by $\sqrt R$. At an interior parameter, score centering identifies the derivative covariance, so a second application of that lemma bounds $|g'(\theta)|$ by $\sqrt{RI}$. Apply the mean-value estimate \cref{lem:mean-value-bias-slope-bound-local} to these endpoint and slope bounds. -/)
  (title := /-- Finite information bound for a biased estimator -/)
  (latexEnv := "lemma")]
lemma finite_biased_information_bound_local {Ω : Type*} [Fintype Ω]
    (w : ℝ → Ω → ℝ) (T : Ω → ℝ) (S : ℝ → Ω → ℝ)
    (a δ R I : ℝ) (hδ : 0 < δ) (hR : 0 ≤ R) (hI : 0 ≤ I)
    (hw : ∀ t ∈ Set.Icc (-δ) δ, ∀ x, 0 ≤ w t x)
    (hmass : ∀ t ∈ Set.Icc (-δ) δ, ∑ x, w t x = 1)
    (hrisk : ∀ t ∈ Set.Icc (-δ) δ,
      ∑ x, w t x * (T x - a * t) ^ 2 ≤ R)
    (hderiv : ∀ t ∈ Set.Icc (-δ) δ,
      HasDerivAt (fun u => ∑ x, w u x * T x)
      (∑ x, w t x * T x * S t x) t)
    (hscore : ∀ t ∈ Set.Ioo (-δ) δ, ∑ x, w t x * S t x = 0)
    (hinfo : ∀ t ∈ Set.Ioo (-δ) δ,
      ∑ x, w t x * (S t x) ^ 2 ≤ I) :
    a ≤ Real.sqrt R / δ + Real.sqrt (R * I) := by
  let g : ℝ → ℝ := fun t => ∑ x, w t x * T x
  let g' : ℝ → ℝ := fun t => ∑ x, w t x * T x * S t x
  have hbias : ∀ t ∈ ({-δ, δ} : Set ℝ), |g t - a * t| ≤ Real.sqrt R := by
    intro t ht
    have htIcc : t ∈ Set.Icc (-δ) δ := by
      rcases ht with (rfl | rfl)
      · exact ⟨le_rfl, by linarith⟩
      · exact ⟨by linarith, le_rfl⟩
    have hcov : ∑ x, w t x * (T x - a * t) * (1 : Ω → ℝ) x =
        g t - a * t := by
      simp only [Pi.one_apply, mul_one]
      calc
        (∑ x, w t x * (T x - a * t)) =
            ∑ x, (w t x * T x - a * t * w t x) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = (∑ x, w t x * T x) - a * t * ∑ x, w t x := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
        _ = g t - a * t := by simp [g, hmass t htIcc]
    have hone : ∑ x, w t x * ((1 : Ω → ℝ) x) ^ 2 ≤ 1 := by
      simpa using le_of_eq (hmass t htIcc)
    have hsq := finite_weighted_information_bound_local
      (w t) T (1 : Ω → ℝ) (a * t) (g t - a * t) 1
      (hw t htIcc) hcov hone
    have hsqR : (g t - a * t) ^ 2 ≤ R :=
      le_trans hsq (by simpa using hrisk t htIcc)
    have hsqrt : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR
    nlinarith [sq_abs (g t - a * t), abs_nonneg (g t - a * t),
      Real.sqrt_nonneg R]
  have hslope : ∀ t ∈ Set.Ioo (-δ) δ, |g' t| ≤ Real.sqrt (R * I) := by
    intro t ht
    have htIcc : t ∈ Set.Icc (-δ) δ := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hcov : ∑ x, w t x * (T x - a * t) * S t x = g' t := by
      rw [show (∑ x, w t x * (T x - a * t) * S t x) =
          (∑ x, w t x * T x * S t x) -
            a * t * (∑ x, w t x * S t x) by
        calc
          (∑ x, w t x * (T x - a * t) * S t x) =
              ∑ x, (w t x * T x * S t x - a * t * (w t x * S t x)) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
          _ = (∑ x, w t x * T x * S t x) -
              a * t * (∑ x, w t x * S t x) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]]
      simp [g', hscore t ht]
    have hsq := finite_weighted_information_bound_local
      (w t) T (S t) (a * t) (g' t) I
      (hw t htIcc) hcov (hinfo t ht)
    have hsqRI : (g' t) ^ 2 ≤ R * I :=
      le_trans hsq (mul_le_mul_of_nonneg_right (hrisk t htIcc) hI)
    have hRI : 0 ≤ R * I := mul_nonneg hR hI
    have hsqrt : (Real.sqrt (R * I)) ^ 2 = R * I := Real.sq_sqrt hRI
    nlinarith [sq_abs (g' t), abs_nonneg (g' t), Real.sqrt_nonneg (R * I)]
  apply mean_value_bias_slope_bound_local g g' a δ
    (Real.sqrt R) (Real.sqrt (R * I)) hδ
  · intro t ht
    simpa [g, g'] using hderiv t ht
  · exact hbias (-δ) (by simp)
  · exact hbias δ (by simp)
  · exact hslope

@[blueprint "lem:finite-score-centered-from-normalization-local"
  (statement := /-- Let $w_t$ be finite weights normalized to one on $[-\delta,\delta]$. If each coordinate satisfies $w_x'(t)=w_t(x)S_t(x)$, then at every $t\in(-\delta,\delta)$ the score is centered:
  \[
  \sum_x w_t(x)S_t(x)=0.
  \] -/)
  (proof := /-- Differentiate the finite weighted expectation of the constant statistic one using \cref{lem:finite-weighted-expectation-derivative-local}. In a neighborhood of an interior point, normalization makes this expectation identically one, whose derivative is zero. Uniqueness of the derivative gives the asserted score sum. -/)
  (title := /-- Score centering from normalization -/)
  (latexEnv := "lemma")]
lemma finite_score_centered_from_normalization_local
    {Ω : Type*} [Fintype Ω] (w S : ℝ → Ω → ℝ) (δ t : ℝ)
    (ht : t ∈ Set.Ioo (-δ) δ)
    (hmass : ∀ u ∈ Set.Icc (-δ) δ, ∑ x, w u x = 1)
    (hderiv : ∀ x, HasDerivAt (fun u => w u x) (w t x * S t x) t) :
    ∑ x, w t x * S t x = 0 := by
  have hd := finite_weighted_expectation_derivative_local
    w (fun u x => w u x * S u x) (1 : Ω → ℝ) t hderiv
  have hevent :
      (∑ x, fun u => w u x * (1 : Ω → ℝ) x) =ᶠ[nhds t]
        (fun _ => (1 : ℝ)) := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo ht] with u hu
    simp only [Pi.one_apply, mul_one, Finset.sum_apply]
    exact hmass u ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  have hzero : HasDerivAt
      (∑ x, fun u => w u x * (1 : Ω → ℝ) x) 0 t :=
    (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq hevent
  have heq := hd.unique hzero
  simpa only [Pi.one_apply, mul_one] using heq

@[blueprint "def:two-point-boolean-score-local"
  (statement := /-- In the interior of the two-point family, the score of a Boolean observation $(z,b)$ is $v_z/(\sqrt{\sigma^2}+\theta v_z)$ for $b=1$ and $-v_z/(\sqrt{\sigma^2}-\theta v_z)$ for $b=0$. -/)
  (title := /-- Score of one Boolean two-point observation -/)
  (latexEnv := "definition")]
noncomputable def two_point_boolean_score_local {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (x : Fin K × Bool) : ℝ :=
  if x.2 then v x.1 / (Real.sqrt p.varianceBound + θ * v x.1)
  else -v x.1 / (Real.sqrt p.varianceBound - θ * v x.1)

@[blueprint "def:two-point-dataset-boolean-score-local"
  (statement := /-- The score of a Boolean sampled dataset is the sum of the one-observation scores over every source and planned observation. -/)
  (title := /-- Score of a Boolean sampled dataset -/)
  (latexEnv := "definition")]
noncomputable def two_point_dataset_boolean_score_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (v : Fin K → ℝ) (θ : ℝ)
    (D : boolean_sampled_dataset_local K M n) : ℝ :=
  ∑ m, ∑ i, two_point_boolean_score_local p v θ (D m i)

@[blueprint "def:two-point-source-boolean-affine-mass-local"
  (statement := /-- The unclamped real atom mass of a source observation $(z,b)$ is
  \[
  q_{S,m}(z)\frac{1+\varepsilon_b\theta v_z/\sqrt{\sigma^2}}2,
  \qquad \varepsilon_1=1,\quad \varepsilon_0=-1.
  \] -/)
  (title := /-- Affine source-observation atom mass -/)
  (latexEnv := "definition")]
noncomputable def two_point_source_boolean_affine_mass_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (m : Fin M) (x : Fin K × Bool) : ℝ :=
  pmf_real_mass (p.sourceGroup m) x.1 *
    ((1 + θ * ((if x.2 then 1 else -1) * v x.1 /
      Real.sqrt p.varianceBound)) / 2)

@[blueprint "def:two-point-dataset-boolean-affine-mass-local"
  (statement := /-- The unclamped real mass of a Boolean sampled dataset is the product of its affine source-observation atom masses. -/)
  (title := /-- Affine Boolean dataset mass -/)
  (latexEnv := "definition")]
noncomputable def two_point_dataset_boolean_affine_mass_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (v : Fin K → ℝ) (θ : ℝ)
    (D : boolean_sampled_dataset_local K M n) : ℝ :=
  ∏ m, ∏ i, two_point_source_boolean_affine_mass_local p v θ m (D m i)

@[blueprint "lem:two-point-boolean-mass-interior-local"
  (statement := /-- If $\sigma^2>0$ and $|\theta v_z|\le\sqrt{\sigma^2}$, then the clamped Boolean mass equals its affine expression: $(1+\theta v_z/\sqrt{\sigma^2})/2$ at the positive atom and its complement at the negative atom. -/)
  (proof := /-- The parameter bound places the affine probability in $[0,1]$, so both clamps are inactive.  At the negative atom, coercion of the nonnegative-real complement is justified by the same upper bound. -/)
  (title := /-- Interior formula for a Boolean atom mass -/)
  (latexEnv := "lemma")]
lemma two_point_boolean_mass_interior_local {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (hvar : 0 < p.varianceBound)
    (hparam : ∀ z, |θ * v z| ≤ Real.sqrt p.varianceBound)
    (z : Fin K) (b : Bool) :
    (two_point_boolean_mass_local p v θ z b : ℝ) =
      if b then (1 + θ * v z / Real.sqrt p.varianceBound) / 2
      else 1 - (1 + θ * v z / Real.sqrt p.varianceBound) / 2 := by
  have hs : 0 < Real.sqrt p.varianceBound := Real.sqrt_pos.2 hvar
  have hz := abs_le.mp (hparam z)
  have hlo : -1 ≤ θ * v z / Real.sqrt p.varianceBound :=
    (le_div_iff₀ hs).2 (by linarith)
  have hhi : θ * v z / Real.sqrt p.varianceBound ≤ 1 :=
    (div_le_iff₀ hs).2 (by linarith)
  have hr0 : 0 ≤ (1 + θ * v z / Real.sqrt p.varianceBound) / 2 := by
    linarith
  have hr1 : (1 + θ * v z / Real.sqrt p.varianceBound) / 2 ≤ 1 := by
    linarith
  unfold two_point_boolean_mass_local
  simp only [min_eq_right hr1, max_eq_right hr0]
  split
  · rfl
  · rw [NNReal.coe_sub hr1]
    rfl

@[blueprint "lem:two-point-source-affine-mass-interior-local"
  (statement := /-- In the interior of the two-point family, the affine real source-observation mass equals the real coercion of the clamped nonnegative-real atom mass. -/)
  (proof := /-- Expand the source factor and use \cref{lem:two-point-boolean-mass-interior-local}.  The positive atom is immediate; for the negative atom, expand the complementary affine probability and rearrange. -/)
  (title := /-- Agreement of affine and clamped source masses -/)
  (latexEnv := "lemma")]
lemma two_point_source_affine_mass_interior_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (hvar : 0 < p.varianceBound)
    (hparam : ∀ z, |θ * v z| ≤ Real.sqrt p.varianceBound)
    (m : Fin M) (x : Fin K × Bool) :
    two_point_source_boolean_affine_mass_local p v θ m x =
      (two_point_source_boolean_mass_local p v θ m x : ℝ) := by
  rcases x with ⟨z, b⟩
  unfold two_point_source_boolean_affine_mass_local
    two_point_source_boolean_mass_local
  rw [NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal]
  cases b
  · rw [two_point_boolean_mass_interior_local p v θ hvar hparam z false]
    simp only [Prod.fst, Prod.snd, Bool.false_eq, Bool.true_eq_false,
      if_false, pmf_real_mass]
    ring
  · rw [two_point_boolean_mass_interior_local p v θ hvar hparam z true]
    simp only [Prod.fst, Prod.snd, Bool.true_eq, if_true, pmf_real_mass]
    ring

@[blueprint "lem:two-point-source-affine-mass-derivative-local"
  (statement := /-- In the strict interior, the derivative of an affine source-observation mass is that mass times its score. -/)
  (proof := /-- Differentiate the affine atom mass.  For either Boolean atom, the strict parameter bound makes $\sqrt{\sigma^2}\pm\theta v_z$ nonzero.  Substituting the score from \cref{def:two-point-boolean-score-local} and clearing these denominators proves the logarithmic-derivative identity. -/)
  (title := /-- Score derivative identity for one source observation -/)
  (latexEnv := "lemma")]
lemma two_point_source_affine_mass_derivative_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (hvar : 0 < p.varianceBound)
    (hparam : ∀ z, |θ * v z| < Real.sqrt p.varianceBound)
    (m : Fin M) (x : Fin K × Bool) :
    HasDerivAt
      (fun t => two_point_source_boolean_affine_mass_local p v t m x)
      (two_point_source_boolean_affine_mass_local p v θ m x *
        two_point_boolean_score_local p v θ x) θ := by
  rcases x with ⟨z, b⟩
  have hs : Real.sqrt p.varianceBound ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hvar)
  have hp : Real.sqrt p.varianceBound + θ * v z ≠ 0 := by
    have := (abs_lt.mp (hparam z)).1
    linarith
  have hm : Real.sqrt p.varianceBound - θ * v z ≠ 0 := by
    have := (abs_lt.mp (hparam z)).2
    linarith
  cases b
  · have hlin : HasDerivAt
        (fun t => t * ((-1 : ℝ) * v z / Real.sqrt p.varianceBound))
        ((-1 : ℝ) * v z / Real.sqrt p.varianceBound) θ := by
      simpa only [Function.id_def, one_mul] using
        (hasDerivAt_id θ).mul_const
          ((-1 : ℝ) * v z / Real.sqrt p.varianceBound)
    have hd : HasDerivAt
        (fun t => two_point_source_boolean_affine_mass_local p v t m (z, false))
        (pmf_real_mass (p.sourceGroup m) z *
          (((-1 : ℝ) * v z / Real.sqrt p.varianceBound) / 2)) θ := by
      simpa [two_point_source_boolean_affine_mass_local] using
        (((hasDerivAt_const θ (1 : ℝ)).add hlin).div_const (2 : ℝ)).const_mul
          (pmf_real_mass (p.sourceGroup m) z)
    convert hd using 1
    simp [two_point_source_boolean_affine_mass_local, two_point_boolean_score_local]
    field_simp [hs, hm] <;> ring
  · have hlin : HasDerivAt
        (fun t => t * ((1 : ℝ) * v z / Real.sqrt p.varianceBound))
        ((1 : ℝ) * v z / Real.sqrt p.varianceBound) θ := by
      simpa only [Function.id_def, one_mul] using
        (hasDerivAt_id θ).mul_const
          ((1 : ℝ) * v z / Real.sqrt p.varianceBound)
    have hd : HasDerivAt
        (fun t => two_point_source_boolean_affine_mass_local p v t m (z, true))
        (pmf_real_mass (p.sourceGroup m) z *
          (((1 : ℝ) * v z / Real.sqrt p.varianceBound) / 2)) θ := by
      simpa [two_point_source_boolean_affine_mass_local] using
        (((hasDerivAt_const θ (1 : ℝ)).add hlin).div_const (2 : ℝ)).const_mul
          (pmf_real_mass (p.sourceGroup m) z)
    convert hd using 1
    simp [two_point_source_boolean_affine_mass_local, two_point_boolean_score_local]
    field_simp [hs, hp] <;> ring

@[blueprint "lem:two-point-dataset-affine-mass-derivative-local"
  (statement := /-- In the strict interior, the derivative of the affine Boolean dataset mass is the dataset mass times the sum of its observation scores. -/)
  (proof := /-- Apply \cref{lem:finite-product-score-derivative-local} within every source, using the one-observation identity \cref{lem:two-point-source-affine-mass-derivative-local}. Apply the same finite-product rule once more across sources.  The resulting nested product is the affine dataset mass, and the nested score sum is \cref{def:two-point-dataset-boolean-score-local}. -/)
  (title := /-- Score derivative identity for a Boolean dataset -/)
  (latexEnv := "lemma")]
lemma two_point_dataset_affine_mass_derivative_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (v : Fin K → ℝ) (θ : ℝ)
    (hvar : 0 < p.varianceBound)
    (hparam : ∀ z, |θ * v z| < Real.sqrt p.varianceBound)
    (D : boolean_sampled_dataset_local K M n) :
    HasDerivAt
      (fun t => two_point_dataset_boolean_affine_mass_local p n v t D)
      (two_point_dataset_boolean_affine_mass_local p n v θ D *
        two_point_dataset_boolean_score_local p n v θ D) θ := by
  have hinner : ∀ m, HasDerivAt
      (∏ i : Fin (n m), fun t =>
        two_point_source_boolean_affine_mass_local p v t m (D m i))
      ((∏ i, two_point_source_boolean_affine_mass_local p v θ m (D m i)) *
        ∑ i, two_point_boolean_score_local p v θ (D m i)) θ := by
    intro m
    exact finite_product_score_derivative_local
      (Finset.univ : Finset (Fin (n m)))
      (fun t i => two_point_source_boolean_affine_mass_local p v t m (D m i))
      (fun i => two_point_boolean_score_local p v θ (D m i)) θ
      (fun i _ => two_point_source_affine_mass_derivative_local
        p v θ hvar hparam m (D m i))
  have houter := finite_product_score_derivative_local
    (Finset.univ : Finset (Fin M))
    (fun t m => ∏ i, two_point_source_boolean_affine_mass_local p v t m (D m i))
    (fun m => ∑ i, two_point_boolean_score_local p v θ (D m i)) θ
    (fun m _ => (hinner m).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by
        simp only [Finset.prod_apply]))
  have hfinal : HasDerivAt
      (fun t => ∏ m, ∏ i,
        two_point_source_boolean_affine_mass_local p v t m (D m i))
      ((∏ m, ∏ i, two_point_source_boolean_affine_mass_local p v θ m (D m i)) *
        ∑ m, ∑ i, two_point_boolean_score_local p v θ (D m i)) θ :=
    houter.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by
        simp only [Finset.prod_apply])
  simpa only [two_point_dataset_boolean_affine_mass_local,
    two_point_dataset_boolean_score_local] using hfinal

@[blueprint "lem:two-point-dataset-affine-mass-interior-local"
  (statement := /-- In the interior of the two-point family, the affine real dataset mass equals the real coercion of the clamped nonnegative-real dataset atom mass. -/)
  (proof := /-- Expand both dataset products and apply \cref{lem:two-point-source-affine-mass-interior-local} in every observation coordinate. Coercion from nonnegative reals preserves the resulting finite products. -/)
  (title := /-- Agreement of affine and clamped dataset masses -/)
  (latexEnv := "lemma")]
lemma two_point_dataset_affine_mass_interior_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (v : Fin K → ℝ) (θ : ℝ)
    (hvar : 0 < p.varianceBound)
    (hparam : ∀ z, |θ * v z| ≤ Real.sqrt p.varianceBound)
    (D : boolean_sampled_dataset_local K M n) :
    two_point_dataset_boolean_affine_mass_local p n v θ D =
      (two_point_dataset_boolean_mass_local p n v θ D : ℝ) := by
  unfold two_point_dataset_boolean_affine_mass_local
    two_point_dataset_boolean_mass_local
  simp_rw [two_point_source_affine_mass_interior_local p v θ hvar hparam]
  norm_cast

@[blueprint "lem:two-point-dataset-affine-mass-normalized-local"
  (statement := /-- In the interior of the two-point family, the affine real dataset masses sum to one. -/)
  (proof := /-- Replace every affine mass by its clamped mass using \cref{lem:two-point-dataset-affine-mass-interior-local}. By \cref{lem:two-point-boolean-sampling-measure-singleton-local}, these are precisely the singleton masses of the Boolean product sampling measure. Its source factors have total mass one by \cref{lem:two-point-source-boolean-measure-univ-local}, so the product measure is a probability measure and its singleton masses sum to one. -/)
  (title := /-- Normalization of affine Boolean dataset masses -/)
  (latexEnv := "lemma")]
lemma two_point_dataset_affine_mass_normalized_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (v : Fin K → ℝ) (θ : ℝ)
    (hvar : 0 < p.varianceBound)
    (hparam : ∀ z, |θ * v z| ≤ Real.sqrt p.varianceBound) :
    ∑ D : boolean_sampled_dataset_local K M n,
      two_point_dataset_boolean_affine_mass_local p n v θ D = 1 := by
  simp_rw [two_point_dataset_affine_mass_interior_local p n v θ hvar hparam]
  have hsum :
      (∑ D : boolean_sampled_dataset_local K M n,
        (two_point_dataset_boolean_mass_local p n v θ D : ENNReal)) = 1 := by
    simp_rw [← two_point_boolean_sampling_measure_singleton_local p n v θ]
    rw [MeasureTheory.sum_measure_singleton]
    have hprobSource : ∀ m, IsProbabilityMeasure
        (two_point_source_boolean_measure_local p v θ m) := fun m =>
      ⟨two_point_source_boolean_measure_univ_local p v θ m⟩
    letI : ∀ m, IsProbabilityMeasure
        (two_point_source_boolean_measure_local p v θ m) := hprobSource
    letI : IsProbabilityMeasure
        (two_point_boolean_sampling_measure_local p n v θ) := by
      unfold two_point_boolean_sampling_measure_local
      infer_instance
    simpa only [Finset.coe_univ] using
      (measure_univ (μ := two_point_boolean_sampling_measure_local p n v θ))
  norm_cast at hsum ⊢

@[blueprint "lem:two-point-population-risk-finite-sum-local"
  (statement := /-- In the interior of the two-point family, the population risk of any measurable estimator equals
  \[
  \sum_D w_\theta(D)
  \left(\widehat\theta(\operatorname{enc}D)
  -\theta\sum_zq_T(z)v_z\right)^2,
  \]
  where $w_\theta$ is the affine Boolean dataset mass. -/)
  (proof := /-- The conditional mean formula \cref{lem:two-point-location-model-mean-local} identifies the target functional with $\theta\sum_zq_T(z)v_z$. Pull the sampling integral back through the Boolean encoding by \cref{lem:two-point-boolean-sampling-measure-map-local}; the product is a probability measure because its source factors have total mass one by \cref{lem:two-point-source-boolean-measure-univ-local}. Expand the integral on the finite Boolean dataset type into singleton masses, identify those masses by \cref{lem:two-point-boolean-sampling-measure-singleton-local}, and replace the clamped masses by affine masses using \cref{lem:two-point-dataset-affine-mass-interior-local}. -/)
  (title := /-- Finite-sum representation of two-point population risk -/)
  (latexEnv := "lemma")]
lemma two_point_population_risk_finite_sum_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (estimator : sampled_dataset K M n → ℝ) (hmeas : Measurable estimator)
    (v : Fin K → ℝ) (θ : ℝ)
    (hvar : 0 < p.varianceBound)
    (hparam : ∀ z, |θ * v z| ≤ Real.sqrt p.varianceBound) :
    population_mean_risk p n estimator (two_point_location_model_local p v θ) =
      ∑ D : boolean_sampled_dataset_local K M n,
        two_point_dataset_boolean_affine_mass_local p n v θ D *
          (estimator (two_point_boolean_dataset_encode_local p n D) -
            θ * ∑ z, pmf_real_mass p.targetGroup z * v z) ^ 2 := by
  have htarget :
      target_population_mean p.targetGroup (two_point_location_model_local p v θ) =
        θ * ∑ z, pmf_real_mass p.targetGroup z * v z := by
    rw [target_population_mean]
    simp_rw [two_point_location_model_mean_local p v θ hvar hparam]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  let enc := two_point_boolean_dataset_encode_local p n
  have henc : Measurable enc := measurable_of_finite enc
  let f : sampled_dataset K M n → ℝ := fun D =>
    (estimator D - θ * ∑ z, pmf_real_mass p.targetGroup z * v z) ^ 2
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  letI hprobSource : ∀ m, IsProbabilityMeasure
      (two_point_source_boolean_measure_local p v θ m) := fun m =>
    ⟨two_point_source_boolean_measure_univ_local p v θ m⟩
  letI hprobSampling : IsProbabilityMeasure
      (two_point_boolean_sampling_measure_local p n v θ) := by
    unfold two_point_boolean_sampling_measure_local
    infer_instance
  rw [population_mean_risk, htarget,
    ← two_point_boolean_sampling_measure_map_local p n v θ]
  rw [MeasureTheory.integral_map henc.aemeasurable hf.aestronglyMeasurable]
  change (∫ D, f (enc D) ∂two_point_boolean_sampling_measure_local p n v θ) = _
  rw [MeasureTheory.integral_fintype MeasureTheory.Integrable.of_finite]
  simp_rw [Measure.real_def, two_point_boolean_sampling_measure_singleton_local]
  simp_rw [ENNReal.coe_toReal, smul_eq_mul,
    ← two_point_dataset_affine_mass_interior_local p n v θ hvar hparam]
  rfl

@[blueprint "def:plan-expected-group-count-local"
  (statement := /-- For a sampling plan $n$, the expected number of sampled observations from group $z$ is $\lambda_z(n)=\sum_m n_mq_{S,m}(z)$. -/)
  (title := /-- Expected sampled group count -/)
  (latexEnv := "definition")]
noncomputable def plan_expected_group_count_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (z : Fin K) : ℝ :=
  ∑ m, n m * pmf_real_mass (p.sourceGroup m) z

@[blueprint "def:regularized-plan-direction-local"
  (statement := /-- For a target mass vector $q$, the regularized least-informative direction for plan $n$ is $v_z=q_z/(\lambda_z(n)+1)$. -/)
  (title := /-- Regularized least-informative direction -/)
  (latexEnv := "definition")]
noncomputable def regularized_plan_direction_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) (z : Fin K) : ℝ :=
  q z / (plan_expected_group_count_local p n z + 1)

@[blueprint "def:regularized-plan-harmonic-local"
  (statement := /-- The regularized harmonic quantity of a plan is
  $A_+(n,q)=\sum_z q_z^2/(\lambda_z(n)+1)$. -/)
  (title := /-- Regularized harmonic plan quantity -/)
  (latexEnv := "definition")]
noncomputable def regularized_plan_harmonic_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) : ℝ :=
  ∑ z, (q z) ^ 2 / (plan_expected_group_count_local p n z + 1)

@[blueprint "def:target-reciprocal-mass-sum-local"
  (statement := /-- For a nonnegative finite target mass vector $q$, set
  $C_q=\sum_z q_z^{-1}$, with the real inverse convention $0^{-1}=0$. -/)
  (title := /-- Reciprocal target-mass constant -/)
  (latexEnv := "definition")]
noncomputable def target_reciprocal_mass_sum_local
    {K : ℕ} (q : Fin K → ℝ) : ℝ :=
  ∑ z, (q z)⁻¹

@[blueprint "lem:finite-pmf-real-mass-sum-local"
  (statement := /-- The real masses of a probability mass function on a finite type sum to one. -/)
  (proof := /-- The extended-nonnegative masses sum to one by the defining normalization of a probability mass function. Since every mass is finite, applying the real coercion commutes with the finite sum and preserves one. -/)
  (title := /-- Normalization of finite real PMF masses -/)
  (latexEnv := "lemma")]
lemma finite_pmf_real_mass_sum_local {α : Type*} [Fintype α] (q : PMF α) :
    ∑ z, pmf_real_mass q z = 1 := by
  have hENN : (∑ z, q z) = (1 : ENNReal) :=
    (hasSum_fintype (fun z => q z)).unique (PMF.hasSum_coe_one q)
  unfold pmf_real_mass
  rw [← ENNReal.toReal_sum]
  · rw [hENN]
    simp
  · intro a ha
    exact q.apply_ne_top a

@[blueprint "lem:plan-expected-group-count-nonnegative-local"
  (statement := /-- Every expected sampled group count is nonnegative. -/)
  (proof := /-- Each summand is the product of a natural sample count and a nonnegative probability mass, so the finite sum is nonnegative. -/)
  (title := /-- Nonnegativity of expected sampled group counts -/)
  (latexEnv := "lemma")]
lemma plan_expected_group_count_nonnegative_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M) (z : Fin K) :
    0 ≤ plan_expected_group_count_local p n z := by
  unfold plan_expected_group_count_local
  exact Finset.sum_nonneg fun m _ =>
    mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg

@[blueprint "lem:regularized-plan-harmonic-nonnegative-local"
  (statement := /-- If $q$ is nonnegative, then $A_+(n,q)$ is nonnegative. -/)
  (proof := /-- Every denominator $\lambda_z(n)+1$ is positive by \cref{lem:plan-expected-group-count-nonnegative-local}, and every numerator is a square; hence every summand and their finite sum are nonnegative. -/)
  (title := /-- Nonnegativity of the regularized harmonic quantity -/)
  (latexEnv := "lemma")]
lemma regularized_plan_harmonic_nonnegative_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) :
    0 ≤ regularized_plan_harmonic_local p n q := by
  unfold regularized_plan_harmonic_local
  exact Finset.sum_nonneg fun z _ =>
    div_nonneg (sq_nonneg _) (by
      linarith [plan_expected_group_count_nonnegative_local p n z])

@[blueprint "lem:regularized-plan-harmonic-positive-pmf-local"
  (statement := /-- For a probability mass function $q$ on a nonempty finite group type, $A_+(n,q)$ is strictly positive for every plan. -/)
  (proof := /-- By \cref{lem:finite-pmf-real-mass-sum-local}, at least one group has positive real mass. Every expected group count is nonnegative by \cref{lem:plan-expected-group-count-nonnegative-local}; hence the selected squared mass divided by $\lambda_z+1$ is strictly positive, while every other summand is nonnegative. -/)
  (title := /-- Positivity of the regularized harmonic quantity -/)
  (latexEnv := "lemma")]
lemma regularized_plan_harmonic_positive_pmf_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : PMF (Fin K)) :
    0 < regularized_plan_harmonic_local p n (fun z => pmf_real_mass q z) := by
  have hsum := finite_pmf_real_mass_sum_local q
  have hex : ∃ z, pmf_real_mass q z ≠ 0 := by
    by_contra h
    push Not at h
    have : (∑ z, pmf_real_mass q z) = 0 := Finset.sum_eq_zero fun z _ => h z
    linarith
  rcases hex with ⟨z, hz⟩
  have hqz : 0 < pmf_real_mass q z :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
  have hterm : 0 < (pmf_real_mass q z) ^ 2 /
      (plan_expected_group_count_local p n z + 1) := by
    exact div_pos (sq_pos_of_pos hqz) (by
      linarith [plan_expected_group_count_nonnegative_local p n z])
  unfold regularized_plan_harmonic_local
  change 0 < ∑ j, (pmf_real_mass q j) ^ 2 /
    (plan_expected_group_count_local p n j + 1)
  have hnonneg : ∀ j, 0 ≤ (pmf_real_mass q j) ^ 2 /
      (plan_expected_group_count_local p n j + 1) := by
    intro j
    have hj := plan_expected_group_count_nonnegative_local p n j
    exact div_nonneg (sq_nonneg _) (by linarith)
  have hle : (pmf_real_mass q z) ^ 2 /
      (plan_expected_group_count_local p n z + 1) ≤
      ∑ j, (pmf_real_mass q j) ^ 2 /
        (plan_expected_group_count_local p n j + 1) :=
    Finset.single_le_sum (f := fun j => (pmf_real_mass q j) ^ 2 /
      (plan_expected_group_count_local p n j + 1))
      (fun j _ => hnonneg j)
      (Finset.mem_univ z)
  exact lt_of_lt_of_le hterm hle

@[blueprint "lem:target-reciprocal-mass-sum-positive-pmf-local"
  (statement := /-- For a probability mass function on a nonempty finite type, the reciprocal-mass constant $C_q$ is strictly positive. -/)
  (proof := /-- Some real mass is positive by \cref{lem:finite-pmf-real-mass-sum-local}. Its reciprocal is positive, and every other reciprocal is nonnegative, so their finite sum is positive. -/)
  (title := /-- Positivity of the reciprocal target-mass constant -/)
  (latexEnv := "lemma")]
lemma target_reciprocal_mass_sum_positive_pmf_local
    {K : ℕ} [NeZero K] (q : PMF (Fin K)) :
    0 < target_reciprocal_mass_sum_local (fun z => pmf_real_mass q z) := by
  have hsum := finite_pmf_real_mass_sum_local q
  have hex : ∃ z, pmf_real_mass q z ≠ 0 := by
    by_contra h
    push Not at h
    have : (∑ z, pmf_real_mass q z) = 0 := Finset.sum_eq_zero fun z _ => h z
    linarith
  rcases hex with ⟨z, hz⟩
  have hqz : 0 < pmf_real_mass q z :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
  unfold target_reciprocal_mass_sum_local
  exact lt_of_lt_of_le (inv_pos.2 hqz)
    (Finset.single_le_sum
      (fun j _ => inv_nonneg.2 ENNReal.toReal_nonneg)
      (Finset.mem_univ z))

@[blueprint "lem:regularized-direction-controlled-local"
  (statement := /-- If $q$ is nonnegative, then every coordinate of the regularized direction satisfies
  \[
  |v_z|\le C_q A_+(n,q).
  \] -/)
  (proof := /-- Expected group counts are nonnegative by \cref{lem:plan-expected-group-count-nonnegative-local}, so the direction is nonnegative. If $q_z=0$, the coordinate vanishes. Otherwise,
  $v_z=q_z^{-1}[q_z^2/(\lambda_z+1)]$. The bracketed term is at most the sum $A_+(n,q)$, which is nonnegative by \cref{lem:regularized-plan-harmonic-nonnegative-local}, while $q_z^{-1}$ is at most the nonnegative sum $C_q$. Multiplying these two inequalities proves the claim. -/)
  (title := /-- Uniform coordinate control of the regularized direction -/)
  (latexEnv := "lemma")]
lemma regularized_direction_controlled_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) (hq : ∀ z, 0 ≤ q z) (z : Fin K) :
    |regularized_plan_direction_local p n q z| ≤
      target_reciprocal_mass_sum_local q *
        regularized_plan_harmonic_local p n q := by
  have hlam1 : 0 < plan_expected_group_count_local p n z + 1 := by
    linarith [plan_expected_group_count_nonnegative_local p n z]
  have hvnonneg : 0 ≤ regularized_plan_direction_local p n q z := by
    exact div_nonneg (hq z) (le_of_lt hlam1)
  rw [abs_of_nonneg hvnonneg]
  by_cases hqz : q z = 0
  · rw [regularized_plan_direction_local, hqz, zero_div]
    exact mul_nonneg
      (by
        unfold target_reciprocal_mass_sum_local
        exact Finset.sum_nonneg fun j _ => inv_nonneg.2 (hq j))
      (regularized_plan_harmonic_nonnegative_local p n q)
  have hqpos : 0 < q z := lt_of_le_of_ne (hq z) (Ne.symm hqz)
  have htermnonneg : ∀ j,
      0 ≤ (q j) ^ 2 / (plan_expected_group_count_local p n j + 1) := by
    intro j
    exact div_nonneg (sq_nonneg _) (by
      linarith [plan_expected_group_count_nonnegative_local p n j])
  have htermle :
      (q z) ^ 2 / (plan_expected_group_count_local p n z + 1) ≤
        regularized_plan_harmonic_local p n q := by
    unfold regularized_plan_harmonic_local
    exact Finset.single_le_sum (fun j _ => htermnonneg j) (Finset.mem_univ z)
  have hinvnonneg : ∀ j, 0 ≤ (q j)⁻¹ := fun j => inv_nonneg.2 (hq j)
  have hinvle : (q z)⁻¹ ≤ target_reciprocal_mass_sum_local q := by
    unfold target_reciprocal_mass_sum_local
    exact Finset.single_le_sum (fun j _ => hinvnonneg j) (Finset.mem_univ z)
  have hAnonneg := regularized_plan_harmonic_nonnegative_local p n q
  calc
    regularized_plan_direction_local p n q z =
        (q z)⁻¹ * ((q z) ^ 2 /
          (plan_expected_group_count_local p n z + 1)) := by
      unfold regularized_plan_direction_local
      field_simp [hqz, ne_of_gt hlam1]
    _ ≤ target_reciprocal_mass_sum_local q *
        regularized_plan_harmonic_local p n q :=
      mul_le_mul hinvle htermle (htermnonneg z)
        (Finset.sum_nonneg fun j _ => hinvnonneg j)

@[blueprint "lem:regularized-plan-slope-local"
  (statement := /-- Pairing the target vector $q$ with the regularized direction gives the regularized harmonic quantity:
  $\sum_zq_zv_z=A_+(n,q)$. -/)
  (proof := /-- Substitute $v_z=q_z/(\lambda_z+1)$ in each summand and rearrange $q_z(q_z/(\lambda_z+1))=q_z^2/(\lambda_z+1)$. -/)
  (title := /-- Target slope of the regularized direction -/)
  (latexEnv := "lemma")]
lemma regularized_plan_slope_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) :
    ∑ z, q z * regularized_plan_direction_local p n q z =
      regularized_plan_harmonic_local p n q := by
  unfold regularized_plan_direction_local regularized_plan_harmonic_local
  apply Finset.sum_congr rfl
  intro z hz
  ring

@[blueprint "lem:dataset-score-information-rearrangement-local"
  (statement := /-- The dataset information sum can be regrouped by target group:
  \[
  \sum_m n_m\sum_z q_{S,m}(z)
  \frac{v_z^2}{\sigma^2-(\theta v_z)^2}
  =
  \sum_z\lambda_z(n)\frac{v_z^2}{\sigma^2-(\theta v_z)^2}.
  \] -/)
  (proof := /-- Distribute the source counts through the inner sum, interchange the two finite sums, and factor out the group-dependent quotient.  The remaining source sum is exactly the expected group count. -/)
  (title := /-- Regrouping of the dataset information -/)
  (latexEnv := "lemma")]
lemma dataset_score_information_rearrangement_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (v : Fin K → ℝ) (θ : ℝ) :
    (∑ m, n m * ∑ z, pmf_real_mass (p.sourceGroup m) z * (v z) ^ 2 /
      (p.varianceBound - (θ * v z) ^ 2)) =
      ∑ z, plan_expected_group_count_local p n z * (v z) ^ 2 /
        (p.varianceBound - (θ * v z) ^ 2) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  unfold plan_expected_group_count_local
  rw [Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  push_cast
  ring

@[blueprint "lem:regularized-direction-information-upper-local"
  (statement := /-- Let $v_z=q_z/(\lambda_z+1)$ with $q_z\ge0$. If $\rho^2<\sigma^2$ and $|\theta v_z|\le\rho$ for every group, then the dataset information satisfies
  \[
  \sum_m n_m\sum_z q_{S,m}(z)
  \frac{v_z^2}{\sigma^2-(\theta v_z)^2}
  \le
  \frac{A_+(n,q)}{\sigma^2-\rho^2}.
  \] -/)
  (proof := /-- Regroup the information by \cref{lem:dataset-score-information-rearrangement-local}. Every expected group count is nonnegative by \cref{lem:plan-expected-group-count-nonnegative-local}. For each group, the parameter bound gives
  $\sigma^2-(\theta v_z)^2\ge\sigma^2-\rho^2>0$, while $\lambda_z\le\lambda_z+1$. Substitute $v_z=q_z/(\lambda_z+1)$, cross-multiply the positive denominators, and sum the resulting inequalities. -/)
  (title := /-- Uniform information bound for the regularized direction -/)
  (latexEnv := "lemma")]
lemma regularized_direction_information_upper_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) (hq : ∀ z, 0 ≤ q z)
    (θ ρ : ℝ) (hrho : ρ ^ 2 < p.varianceBound)
    (hparam : ∀ z, |θ * regularized_plan_direction_local p n q z| ≤ ρ) :
    (∑ m, n m * ∑ z, pmf_real_mass (p.sourceGroup m) z *
      (regularized_plan_direction_local p n q z) ^ 2 /
      (p.varianceBound -
        (θ * regularized_plan_direction_local p n q z) ^ 2)) ≤
      regularized_plan_harmonic_local p n q /
        (p.varianceBound - ρ ^ 2) := by
  rw [dataset_score_information_rearrangement_local]
  unfold regularized_plan_harmonic_local
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro z hz
  let lam := plan_expected_group_count_local p n z
  have hlam : 0 ≤ lam := plan_expected_group_count_nonnegative_local p n z
  have hlam1 : 0 < lam + 1 := by linarith
  have hd0 : 0 < p.varianceBound - ρ ^ 2 := sub_pos.2 hrho
  have hrhononneg : 0 ≤ ρ := le_trans (abs_nonneg _) (hparam z)
  have hθsq : (θ * regularized_plan_direction_local p n q z) ^ 2 ≤ ρ ^ 2 := by
    have hprod : 0 ≤
        (ρ - |θ * regularized_plan_direction_local p n q z|) *
          (ρ + |θ * regularized_plan_direction_local p n q z|) :=
      mul_nonneg (sub_nonneg.2 (hparam z))
        (add_nonneg hrhononneg (abs_nonneg _))
    nlinarith [sq_abs (θ * regularized_plan_direction_local p n q z)]
  have hd : 0 < p.varianceBound -
      (θ * regularized_plan_direction_local p n q z) ^ 2 := by
    linarith
  apply (div_le_div_iff₀ hd hd0).2
  unfold regularized_plan_direction_local
  change lam * (q z / (lam + 1)) ^ 2 * (p.varianceBound - ρ ^ 2) ≤
    ((q z) ^ 2 / (lam + 1)) *
      (p.varianceBound - (θ * (q z / (lam + 1))) ^ 2)
  have hθpoly : θ ^ 2 * (q z) ^ 2 ≤ ρ ^ 2 * (lam + 1) ^ 2 := by
    unfold regularized_plan_direction_local at hθsq
    change (θ * (q z / (lam + 1))) ^ 2 ≤ ρ ^ 2 at hθsq
    field_simp [ne_of_gt hlam1] at hθsq
    nlinarith
  have hll : lam * (lam + 1) ≤ (lam + 1) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hll (le_of_lt hd0)
  have hcore : lam * (lam + 1) * (p.varianceBound - ρ ^ 2) ≤
      (lam + 1) ^ 2 * p.varianceBound - (q z) ^ 2 * θ ^ 2 := by
    nlinarith
  field_simp [ne_of_gt hlam1]
  calc
    lam * (q z) ^ 2 * (lam + 1) * (p.varianceBound - ρ ^ 2) =
        (q z) ^ 2 * (lam * (lam + 1) * (p.varianceBound - ρ ^ 2)) := by ring
    _ ≤ (q z) ^ 2 *
        ((lam + 1) ^ 2 * p.varianceBound - (q z) ^ 2 * θ ^ 2) :=
      mul_le_mul_of_nonneg_left hcore (sq_nonneg (q z))

@[blueprint "lem:two-point-source-score-centered-local"
  (statement := /-- In the strict interior of the two-point family, the score of one observation from any source has weighted mean zero. -/)
  (proof := /-- Split the finite sum into group and Boolean coordinates.  For each group, substitute the affine masses from \cref{lem:two-point-boolean-mass-interior-local}; the positive- and negative-atom score contributions cancel exactly. -/)
  (title := /-- Centering of the one-observation score -/)
  (latexEnv := "lemma")]
lemma two_point_source_score_centered_local {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (hvar : 0 < p.varianceBound)
    (hparam : ∀ z, |θ * v z| < Real.sqrt p.varianceBound)
    (m : Fin M) :
    ∑ x : Fin K × Bool,
        (two_point_source_boolean_mass_local p v θ m x : ℝ) *
          two_point_boolean_score_local p v θ x = 0 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro z hz
  have hs : 0 < Real.sqrt p.varianceBound := Real.sqrt_pos.2 hvar
  have hzlt := hparam z
  have hzle : |θ * v z| ≤ Real.sqrt p.varianceBound := le_of_lt hzlt
  have hp : Real.sqrt p.varianceBound + θ * v z ≠ 0 := by
    have := (abs_lt.mp hzlt).1
    linarith
  have hm : Real.sqrt p.varianceBound - θ * v z ≠ 0 := by
    have := (abs_lt.mp hzlt).2
    linarith
  rw [show (∑ b : Bool,
      (two_point_source_boolean_mass_local p v θ m (z, b) : ℝ) *
        two_point_boolean_score_local p v θ (z, b)) =
      (two_point_source_boolean_mass_local p v θ m (z, true) : ℝ) *
          two_point_boolean_score_local p v θ (z, true) +
        (two_point_source_boolean_mass_local p v θ m (z, false) : ℝ) *
          two_point_boolean_score_local p v θ (z, false) by
      rw [Fintype.sum_bool]]
  simp only [two_point_source_boolean_mass_local, NNReal.coe_mul]
  rw [two_point_boolean_mass_interior_local p v θ hvar (fun z => le_of_lt (hparam z))
      z true,
    two_point_boolean_mass_interior_local p v θ hvar (fun z => le_of_lt (hparam z))
      z false]
  simp [two_point_boolean_score_local]
  field_simp
  ring

@[blueprint "lem:two-point-source-score-second-moment-local"
  (statement := /-- In the strict interior of the two-point family, the second moment of the score of one source-$m$ observation is
  \[
  \sum_z q_{S,m}(z)\frac{v_z^2}{\sigma^2-(\theta v_z)^2}.
  \] -/)
  (proof := /-- Split the finite observation space into group and Boolean coordinates.  Substitute the affine atom masses from \cref{lem:two-point-boolean-mass-interior-local}.  The two Boolean terms have denominators $\sqrt{\sigma^2}\pm\theta v_z$; combining them and using $(\sqrt{\sigma^2})^2=\sigma^2$ gives the displayed summand for each group. -/)
  (title := /-- Second moment of the one-observation score -/)
  (latexEnv := "lemma")]
lemma two_point_source_score_second_moment_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (hvar : 0 < p.varianceBound)
    (hparam : ∀ z, |θ * v z| < Real.sqrt p.varianceBound)
    (m : Fin M) :
    ∑ x : Fin K × Bool,
        (two_point_source_boolean_mass_local p v θ m x : ℝ) *
          (two_point_boolean_score_local p v θ x) ^ 2 =
      ∑ z, pmf_real_mass (p.sourceGroup m) z * (v z) ^ 2 /
        (p.varianceBound - (θ * v z) ^ 2) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z hz
  have hs : 0 < Real.sqrt p.varianceBound := Real.sqrt_pos.2 hvar
  have hzlt := hparam z
  have hzle : |θ * v z| ≤ Real.sqrt p.varianceBound := le_of_lt hzlt
  have hp : Real.sqrt p.varianceBound + θ * v z ≠ 0 := by
    have := (abs_lt.mp hzlt).1
    linarith
  have hm : Real.sqrt p.varianceBound - θ * v z ≠ 0 := by
    have := (abs_lt.mp hzlt).2
    linarith
  have hvpos : 0 < p.varianceBound - (θ * v z) ^ 2 := by
    have hlo := (abs_lt.mp hzlt).1
    have hhi := (abs_lt.mp hzlt).2
    nlinarith [Real.sq_sqrt (le_of_lt hvar)]
  have hvne : p.varianceBound - (θ * v z) ^ 2 ≠ 0 := ne_of_gt hvpos
  have hvne' : p.varianceBound - θ ^ 2 * v z ^ 2 ≠ 0 := by
    simpa [mul_pow] using hvne
  have hden :
      Real.sqrt p.varianceBound ^ 2 - (θ * v z) ^ 2 ≠ 0 := by
    nlinarith [Real.sq_sqrt (le_of_lt hvar)]
  rw [show (∑ b : Bool,
      (two_point_source_boolean_mass_local p v θ m (z, b) : ℝ) *
        (two_point_boolean_score_local p v θ (z, b)) ^ 2) =
      (two_point_source_boolean_mass_local p v θ m (z, true) : ℝ) *
          (two_point_boolean_score_local p v θ (z, true)) ^ 2 +
        (two_point_source_boolean_mass_local p v θ m (z, false) : ℝ) *
          (two_point_boolean_score_local p v θ (z, false)) ^ 2 by
      rw [Fintype.sum_bool]]
  simp only [two_point_source_boolean_mass_local, NNReal.coe_mul]
  rw [two_point_boolean_mass_interior_local p v θ hvar (fun z => le_of_lt (hparam z))
      z true,
    two_point_boolean_mass_interior_local p v θ hvar (fun z => le_of_lt (hparam z))
      z false]
  simp [two_point_boolean_score_local, pmf_real_mass]
  rw [ENNReal.coe_toNNReal_eq_toReal]
  conv_rhs => rw [show p.varianceBound = Real.sqrt p.varianceBound ^ 2 by
    exact (Real.sq_sqrt (le_of_lt hvar)).symm]
  field_simp [hp, hm, hvne, hvne', hden, hs.ne']
  ring

@[blueprint "lem:two-point-source-score-integral-local"
  (statement := /-- In the strict interior, the score has integral zero under every source Boolean observation law. -/)
  (proof := /-- The source law is finite because its total mass is one by \cref{lem:two-point-source-boolean-measure-univ-local}. Expand the integral on the finite observation space into singleton masses. Identify those masses by \cref{lem:two-point-source-boolean-measure-singleton-local} and apply the centering identity \cref{lem:two-point-source-score-centered-local}. -/)
  (title := /-- Integral centering of the source score -/)
  (latexEnv := "lemma")]
lemma two_point_source_score_integral_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (hvar : 0 < p.varianceBound)
    (hparam : ∀ z, |θ * v z| < Real.sqrt p.varianceBound)
    (m : Fin M) :
    ∫ x, two_point_boolean_score_local p v θ x
        ∂two_point_source_boolean_measure_local p v θ m = 0 := by
  letI : IsFiniteMeasure (two_point_source_boolean_measure_local p v θ m) :=
    ⟨by rw [two_point_source_boolean_measure_univ_local]; simp⟩
  rw [MeasureTheory.integral_fintype MeasureTheory.Integrable.of_finite]
  simp_rw [Measure.real_def, two_point_source_boolean_measure_singleton_local]
  simpa using two_point_source_score_centered_local p v θ hvar hparam m

@[blueprint "lem:two-point-source-score-variance-local"
  (statement := /-- In the strict interior, the score variance under source $m$ is
  \[
  \sum_z q_{S,m}(z)\frac{v_z^2}{\sigma^2-(\theta v_z)^2}.
  \] -/)
  (proof := /-- By \cref{lem:two-point-source-score-integral-local}, the score is centered, so its variance is its second moment. The source law is finite by \cref{lem:two-point-source-boolean-measure-univ-local}. Expand that finite integral into singleton masses using \cref{lem:two-point-source-boolean-measure-singleton-local}, and invoke \cref{lem:two-point-source-score-second-moment-local}. -/)
  (title := /-- Variance of the source score -/)
  (latexEnv := "lemma")]
lemma two_point_source_score_variance_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (v : Fin K → ℝ) (θ : ℝ)
    (hvar : 0 < p.varianceBound)
    (hparam : ∀ z, |θ * v z| < Real.sqrt p.varianceBound)
    (m : Fin M) :
    ProbabilityTheory.variance (two_point_boolean_score_local p v θ)
        (two_point_source_boolean_measure_local p v θ m) =
      ∑ z, pmf_real_mass (p.sourceGroup m) z * (v z) ^ 2 /
        (p.varianceBound - (θ * v z) ^ 2) := by
  letI : IsFiniteMeasure (two_point_source_boolean_measure_local p v θ m) :=
    ⟨by rw [two_point_source_boolean_measure_univ_local]; simp⟩
  rw [ProbabilityTheory.variance_of_integral_eq_zero
    (measurable_of_finite _).aemeasurable
    (two_point_source_score_integral_local p v θ hvar hparam m)]
  rw [MeasureTheory.integral_fintype MeasureTheory.Integrable.of_finite]
  simp_rw [Measure.real_def, two_point_source_boolean_measure_singleton_local]
  simpa using two_point_source_score_second_moment_local p v θ hvar hparam m

@[blueprint "lem:two-point-dataset-score-variance-local"
  (statement := /-- In the strict interior, the variance of the full Boolean dataset score is
  \[
  \sum_m n_m\sum_z q_{S,m}(z)
  \frac{v_z^2}{\sigma^2-(\theta v_z)^2}.
  \] -/)
  (proof := /-- The Boolean sampling measure is the iterated product over observations and sources. Its source factors are probability measures by \cref{lem:two-point-source-boolean-measure-univ-local}. Apply the product-space variance-of-a-sum identity first within each source and then across sources. The coordinate variances are given by \cref{lem:two-point-source-score-variance-local}; summing identical observation-coordinate contributions gives the factor $n_m$. -/)
  (title := /-- Information identity for the Boolean dataset score -/)
  (latexEnv := "lemma")]
lemma two_point_dataset_score_variance_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (v : Fin K → ℝ) (θ : ℝ)
    (hvar : 0 < p.varianceBound)
    (hparam : ∀ z, |θ * v z| < Real.sqrt p.varianceBound) :
    ProbabilityTheory.variance
        (two_point_dataset_boolean_score_local p n v θ)
        (two_point_boolean_sampling_measure_local p n v θ) =
      ∑ m, n m * ∑ z, pmf_real_mass (p.sourceGroup m) z * (v z) ^ 2 /
        (p.varianceBound - (θ * v z) ^ 2) := by
  let μ : Fin M → Measure (Fin K × Bool) :=
    fun m => two_point_source_boolean_measure_local p v θ m
  let X (m : Fin M) (d : Fin (n m) → Fin K × Bool) : ℝ :=
    ∑ i, two_point_boolean_score_local p v θ (d i)
  letI hprob : ∀ m, IsProbabilityMeasure (μ m) := fun m =>
    ⟨by simpa [μ] using two_point_source_boolean_measure_univ_local p v θ m⟩
  have hmem : ∀ m, MeasureTheory.MemLp
      (two_point_boolean_score_local p v θ) 2 (μ m) := by
    intro m
    apply (MeasureTheory.memLp_two_iff_integrable_sq
      (measurable_of_finite _).aestronglyMeasurable).2
    exact MeasureTheory.Integrable.of_finite
  have hinner : ∀ m,
      ProbabilityTheory.variance (X m) (Measure.pi fun _i : Fin (n m) => μ m) =
        n m * ∑ z, pmf_real_mass (p.sourceGroup m) z * (v z) ^ 2 /
          (p.varianceBound - (θ * v z) ^ 2) := by
    intro m
    have hfun : X m =
        ∑ _i : Fin (n m), fun d =>
          two_point_boolean_score_local p v θ (d _i) := by
      funext d
      simp [X, Finset.sum_apply]
    rw [hfun, ProbabilityTheory.variance_sum_pi
      (μ := fun _i : Fin (n m) => μ m)
      (X := fun _i => two_point_boolean_score_local p v θ)
      (fun _i => hmem m)]
    rw [two_point_source_score_variance_local p v θ hvar hparam m]
    simp
  letI hprobPi : ∀ m, IsProbabilityMeasure
      (Measure.pi fun _i : Fin (n m) => μ m) := fun m => inferInstance
  have hmemOuter : ∀ m, MeasureTheory.MemLp (X m) 2
      (Measure.pi fun _i : Fin (n m) => μ m) := by
    intro m
    apply (MeasureTheory.memLp_two_iff_integrable_sq
      (measurable_of_finite _).aestronglyMeasurable).2
    exact MeasureTheory.Integrable.of_finite
  unfold two_point_boolean_sampling_measure_local
  have hfunOuter : two_point_dataset_boolean_score_local p n v θ =
      ∑ m, fun D => X m (D m) := by
    funext D
    simp [two_point_dataset_boolean_score_local, X, Finset.sum_apply]
  rw [hfunOuter, ProbabilityTheory.variance_sum_pi
    (μ := fun m => Measure.pi fun _i : Fin (n m) => μ m)
    (X := X) hmemOuter]
  simp_rw [hinner]

@[blueprint "lem:population-worst-case-regularized-information-local"
  (statement := /-- Assume $\sigma^2>0$ and choose $\rho>0$ with
  $\rho^2<\sigma^2$ and $\rho\le R$. For every plan $n$ and measurable estimator with bounded model-class risks, let $A=A_+(n,q_T)$, $C=C_{q_T}$, and $\delta=\rho/(CA)$. Then its worst-case risk $W$ satisfies
  \[
  A\le \frac{\sqrt W}{\delta}
  +\sqrt{W\frac{A}{\sigma^2-\rho^2}}.
  \] -/)
  (proof := /-- Use the regularized direction from
  \cref{def:regularized-plan-direction-local}. Positivity of $A$ and $C$ is
  \cref{lem:regularized-plan-harmonic-positive-pmf-local,lem:target-reciprocal-mass-sum-positive-pmf-local};
  together with \cref{lem:regularized-direction-controlled-local}, it ensures
  that $|\theta v_z|\le\rho$ on $[-\delta,\delta]$. Hence every two-point
  model is admissible by \cref{lem:two-point-location-model-in-class-local}.
  Rewrite its risk by
  \cref{lem:two-point-population-risk-finite-sum-local}, using
  \cref{lem:regularized-plan-slope-local} for the target slope. The affine
  masses agree with the sampling singleton masses by
  \cref{lem:two-point-dataset-affine-mass-interior-local,lem:two-point-boolean-sampling-measure-singleton-local};
  their normalization and derivative identities are
  \cref{lem:two-point-dataset-affine-mass-normalized-local,lem:two-point-dataset-affine-mass-derivative-local}.
  Differentiate the finite expectation using
  \cref{lem:finite-weighted-expectation-derivative-local}, and center the score
  with \cref{lem:finite-score-centered-from-normalization-local}. The source
  and sampling laws have total mass one by
  \cref{lem:two-point-source-boolean-measure-univ-local}. Finally identify and
  bound the score variance with
  \cref{lem:two-point-dataset-score-variance-local,lem:regularized-direction-information-upper-local},
  then apply \cref{lem:finite-biased-information-bound-local}. -/)
  (title := /-- Worst-case information inequality for the regularized direction -/)
  (latexEnv := "lemma")]
lemma population_worst_case_regularized_information_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (estimator : sampled_dataset K M n → ℝ) (hmeas : Measurable estimator)
    (hrisk : BddAbove {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
      s = population_mean_risk p n estimator P})
    (hvar : 0 < p.varianceBound) (ρ : ℝ) (hρ : 0 < ρ)
    (hρvar : ρ ^ 2 < p.varianceBound) (hρmean : ρ ≤ p.meanRadius) :
    let q := fun z => pmf_real_mass p.targetGroup z
    let A := regularized_plan_harmonic_local p n q
    let C := target_reciprocal_mass_sum_local q
    let δ := ρ / (C * A)
    A ≤ Real.sqrt (population_worst_case_risk p n estimator hrisk) / δ +
      Real.sqrt (population_worst_case_risk p n estimator hrisk *
        (A / (p.varianceBound - ρ ^ 2))) := by
  let q : Fin K → ℝ := fun z => pmf_real_mass p.targetGroup z
  let v : Fin K → ℝ := regularized_plan_direction_local p n q
  let A : ℝ := regularized_plan_harmonic_local p n q
  let C : ℝ := target_reciprocal_mass_sum_local q
  let δ : ℝ := ρ / (C * A)
  let W : ℝ := population_worst_case_risk p n estimator hrisk
  have hq : ∀ z, 0 ≤ q z := fun z => ENNReal.toReal_nonneg
  have hA : 0 < A :=
    regularized_plan_harmonic_positive_pmf_local p n p.targetGroup
  have hC : 0 < C :=
    target_reciprocal_mass_sum_positive_pmf_local p.targetGroup
  have hCA : 0 < C * A := mul_pos hC hA
  have hδ : 0 < δ := div_pos hρ hCA
  have hρsqrt : ρ < Real.sqrt p.varianceBound := by
    have hs := Real.sqrt_pos.2 hvar
    nlinarith [Real.sq_sqrt (le_of_lt hvar)]
  have hvbound : ∀ z, |v z| ≤ C * A := by
    intro z
    exact regularized_direction_controlled_local p n q hq z
  have hparamClosed : ∀ t ∈ Set.Icc (-δ) δ, ∀ z, |t * v z| ≤ ρ := by
    intro t ht z
    have htδ : |t| ≤ δ := (abs_le).2 ⟨by linarith [ht.1], ht.2⟩
    calc
      |t * v z| = |t| * |v z| := abs_mul t (v z)
      _ ≤ δ * (C * A) := mul_le_mul htδ (hvbound z)
        (abs_nonneg _) (le_of_lt hδ)
      _ = ρ := by
        dsimp [δ]
        field_simp [ne_of_gt hCA]
  have hparamOpen : ∀ t ∈ Set.Ioo (-δ) δ, ∀ z, |t * v z| < ρ := by
    intro t ht z
    have htδ : |t| < δ := (abs_lt).2 ⟨by linarith [ht.1], ht.2⟩
    calc
      |t * v z| = |t| * |v z| := abs_mul t (v z)
      _ ≤ |t| * (C * A) :=
        mul_le_mul_of_nonneg_left (hvbound z) (abs_nonneg _)
      _ < δ * (C * A) :=
        mul_lt_mul_of_pos_right htδ hCA
      _ = ρ := by
        dsimp [δ]
        field_simp [ne_of_gt hCA]
  have hclass : ∀ t ∈ Set.Icc (-δ) δ,
      bounded_conditional_mean_class p (two_point_location_model_local p v t) := by
    intro t ht
    apply two_point_location_model_in_class_local p v t hvar
    · intro z
      exact le_trans (hparamClosed t ht z) (le_of_lt hρsqrt)
    · intro z
      exact le_trans (hparamClosed t ht z) hρmean
  have hW : 0 ≤ W := by
    have hzero : ∀ z, |(0 : ℝ) * v z| ≤ Real.sqrt p.varianceBound := by simp
    have hzclass := two_point_location_model_in_class_local p v 0 hvar hzero
      (fun z => by simp [p.meanRadius_nonneg])
    have hmember : population_mean_risk p n estimator
        (two_point_location_model_local p v 0) ∈
        {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
          s = population_mean_risk p n estimator P} :=
      ⟨two_point_location_model_local p v 0, hzclass, rfl⟩
    exact le_trans (MeasureTheory.integral_nonneg fun D => sq_nonneg _)
      (le_csSup hrisk hmember)
  let w : ℝ → boolean_sampled_dataset_local K M n → ℝ :=
    fun t D => two_point_dataset_boolean_affine_mass_local p n v t D
  let T : boolean_sampled_dataset_local K M n → ℝ :=
    fun D => estimator (two_point_boolean_dataset_encode_local p n D)
  let S : ℝ → boolean_sampled_dataset_local K M n → ℝ :=
    fun t D => two_point_dataset_boolean_score_local p n v t D
  have hw : ∀ t ∈ Set.Icc (-δ) δ, ∀ D, 0 ≤ w t D := by
    intro t ht D
    rw [show w t D =
        (two_point_dataset_boolean_mass_local p n v t D : ℝ) by
      exact two_point_dataset_affine_mass_interior_local p n v t hvar
        (fun z => le_trans (hparamClosed t ht z) (le_of_lt hρsqrt)) D]
    positivity
  have hmass : ∀ t ∈ Set.Icc (-δ) δ, ∑ D, w t D = 1 := by
    intro t ht
    exact two_point_dataset_affine_mass_normalized_local p n v t hvar
      (fun z => le_trans (hparamClosed t ht z) (le_of_lt hρsqrt))
  have hwd : ∀ t ∈ Set.Icc (-δ) δ, ∀ D,
      HasDerivAt (fun u => w u D) (w t D * S t D) t := by
    intro t ht D
    exact two_point_dataset_affine_mass_derivative_local p n v t hvar
      (fun z => lt_of_le_of_lt (hparamClosed t ht z) hρsqrt) D
  have hscore : ∀ t ∈ Set.Ioo (-δ) δ, ∑ D, w t D * S t D = 0 := by
    intro t ht
    exact finite_score_centered_from_normalization_local w S δ t ht hmass
      (hwd t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  have hslope : (∑ z, pmf_real_mass p.targetGroup z * v z) = A := by
    exact regularized_plan_slope_local p n q
  have hriskFinite : ∀ t ∈ Set.Icc (-δ) δ,
      ∑ D, w t D * (T D - A * t) ^ 2 ≤ W := by
    intro t ht
    have hriskEq := two_point_population_risk_finite_sum_local
      p n estimator hmeas v t hvar
      (fun z => le_trans (hparamClosed t ht z) (le_of_lt hρsqrt))
    rw [hslope] at hriskEq
    have hmember : population_mean_risk p n estimator
        (two_point_location_model_local p v t) ∈
        {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
          s = population_mean_risk p n estimator P} :=
      ⟨two_point_location_model_local p v t, hclass t ht, rfl⟩
    change (∑ D, two_point_dataset_boolean_affine_mass_local p n v t D *
      (estimator (two_point_boolean_dataset_encode_local p n D) - A * t) ^ 2) ≤
        population_worst_case_risk p n estimator hrisk
    rw [show A * t = t * A by ring]
    rw [← hriskEq]
    exact le_csSup hrisk hmember
  have hderivExp : ∀ t ∈ Set.Icc (-δ) δ,
      HasDerivAt (fun u => ∑ D, w u D * T D)
      (∑ D, w t D * T D * S t D) t := by
    intro t ht
    have hd := finite_weighted_expectation_derivative_local
      w (fun u D => w u D * S u D) T t (hwd t ht)
    have hd' : HasDerivAt (fun u => ∑ D, w u D * T D)
        (∑ D, (w t D * S t D) * T D) t :=
      hd.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun u => by
          simp only [Finset.sum_apply])
    convert hd' using 1
    apply Finset.sum_congr rfl
    intro D hD
    ring
  have hinfo : ∀ t ∈ Set.Ioo (-δ) δ,
      ∑ D, w t D * (S t D) ^ 2 ≤ A / (p.varianceBound - ρ ^ 2) := by
    intro t ht
    let μ := two_point_boolean_sampling_measure_local p n v t
    letI hprobSource : ∀ m, IsProbabilityMeasure
        (two_point_source_boolean_measure_local p v t m) := fun m =>
      ⟨two_point_source_boolean_measure_univ_local p v t m⟩
    letI hprobSampling : IsProbabilityMeasure μ := by
      dsimp [μ]
      unfold two_point_boolean_sampling_measure_local
      infer_instance
    have htIcc : t ∈ Set.Icc (-δ) δ := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have htparam : ∀ z, |t * v z| ≤ Real.sqrt p.varianceBound :=
      fun z => le_trans (hparamClosed t htIcc z) (le_of_lt hρsqrt)
    have hzint : ∫ D, S t D ∂μ = 0 := by
      rw [MeasureTheory.integral_fintype MeasureTheory.Integrable.of_finite]
      dsimp [μ]
      simp_rw [Measure.real_def, two_point_boolean_sampling_measure_singleton_local]
      simp_rw [ENNReal.coe_toReal]
      simp_rw [← two_point_dataset_affine_mass_interior_local p n v t hvar htparam]
      simpa using hscore t ht
    have hsumvar :
        (∑ D, w t D * (S t D) ^ 2) =
          ProbabilityTheory.variance (S t) μ := by
      rw [ProbabilityTheory.variance_of_integral_eq_zero
        (measurable_of_finite _).aemeasurable hzint]
      rw [MeasureTheory.integral_fintype MeasureTheory.Integrable.of_finite]
      dsimp [μ]
      simp_rw [Measure.real_def, two_point_boolean_sampling_measure_singleton_local]
      simp_rw [ENNReal.coe_toReal]
      simp_rw [← two_point_dataset_affine_mass_interior_local p n v t hvar htparam]
      rfl
    rw [hsumvar]
    change ProbabilityTheory.variance
      (two_point_dataset_boolean_score_local p n v t)
      (two_point_boolean_sampling_measure_local p n v t) ≤ _
    rw [two_point_dataset_score_variance_local p n v t hvar
      (fun z => lt_trans (hparamOpen t ht z) hρsqrt)]
    exact regularized_direction_information_upper_local p n q hq t ρ hρvar
      (hparamClosed t htIcc)
  have hI : 0 ≤ A / (p.varianceBound - ρ ^ 2) :=
    div_nonneg (le_of_lt hA) (le_of_lt (sub_pos.2 hρvar))
  have hbound := finite_biased_information_bound_local
    w T S A δ W (A / (p.varianceBound - ρ ^ 2))
    hδ hW hI hw hmass hriskFinite hderivExp hscore hinfo
  simpa [q, A, C, δ, W] using hbound

@[blueprint "def:unregularized-plan-harmonic-local"
  (statement := /-- For a plan $n$ and target vector $q$, set
  $H(n,q)=\sum_{z:q_z\ne0}q_z^2/\lambda_z(n)$. -/)
  (title := /-- Unregularized harmonic plan quantity -/)
  (latexEnv := "definition")]
noncomputable def unregularized_plan_harmonic_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) : ℝ :=
  ∑ z, if q z = 0 then 0
    else (q z) ^ 2 / plan_expected_group_count_local p n z

@[blueprint "lem:plan-discrepancy-harmonic-local"
  (statement := /-- If $n$ is nonempty, then its discrepancy is its sample
  size times the unregularized harmonic quantity:
  $D(q,\bar q_n)=N(n)H(n,q)$. -/)
  (proof := /-- Substitute the mixture identity
  $\bar q_n(z)=\lambda_z(n)/N(n)$ from the definitions of the source
  mixture and expected group count, and simplify each nonzero target
  coordinate. -/)
  (title := /-- Discrepancy as a harmonic sum -/)
  (latexEnv := "lemma")]
lemma plan_discrepancy_harmonic_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) (hn : plan_total_samples n ≠ 0) :
    plan_discrepancy p n q =
      plan_total_samples n * unregularized_plan_harmonic_local p n q := by
  unfold plan_discrepancy unregularized_plan_harmonic_local
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hq : q z = 0
  · simp [hq]
  · simp only [hq, if_false]
    unfold source_mixture_mass
    rw [if_neg hn]
    unfold plan_expected_group_count_local
    push_cast
    field_simp

@[blueprint "lem:effective-sample-size-harmonic-local"
  (statement := /-- If a nonempty plan supports $q$, then its effective
  sample size is $H(n,q)^{-1}$. -/)
  (proof := /-- Unfold effective sample size and use
  \cref{lem:plan-discrepancy-harmonic-local}; cancellation of the positive
  sample size leaves the reciprocal harmonic quantity. -/)
  (title := /-- Effective sample size as reciprocal harmonic quantity -/)
  (latexEnv := "lemma")]
lemma effective_sample_size_harmonic_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) (hn : plan_total_samples n ≠ 0)
    (hsupp : target_supported_by_plan p n q) :
    effective_sample_size p n q =
      (unregularized_plan_harmonic_local p n q)⁻¹ := by
  rw [effective_sample_size]
  simp only [hn, hsupp, not_true_eq_false, or_false, if_false]
  rw [plan_discrepancy_harmonic_local p n q hn]
  push_cast
  field_simp

@[blueprint "lem:expected-group-count-positive-of-supported-local"
  (statement := /-- If a nonempty plan supports a positive target coordinate,
  then the expected sampled count in that coordinate is positive. -/)
  (proof := /-- The support hypothesis makes the source-mixture mass positive.
  Expanding that mass as the expected count divided by the positive total
  sample size gives the claim. -/)
  (title := /-- Positive expected count on supported coordinates -/)
  (latexEnv := "lemma")]
lemma expected_group_count_positive_of_supported_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : Fin K → ℝ) (hn : plan_total_samples n ≠ 0)
    (hsupp : target_supported_by_plan p n q)
    (z : Fin K) (hq : 0 < q z) :
    0 < plan_expected_group_count_local p n z := by
  have hs := hsupp z hq
  unfold source_mixture_mass at hs
  rw [if_neg hn] at hs
  unfold plan_expected_group_count_local
  push_cast at hs
  have hN : 0 < (plan_total_samples n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  rcases div_pos_iff.mp hs with h | h
  · exact h.1
  · linarith [h.2, hN]

@[blueprint "lem:unregularized-plan-harmonic-positive-local"
  (statement := /-- For a nonempty plan supporting a probability target,
  the unregularized harmonic quantity is strictly positive. -/)
  (proof := /-- A finite probability law has a positive coordinate by
  \cref{lem:finite-pmf-real-mass-sum-local}. Its expected count is positive by
  \cref{lem:expected-group-count-positive-of-supported-local}, so its harmonic
  summand is positive, while all remaining summands are nonnegative by
  \cref{lem:plan-expected-group-count-nonnegative-local}. -/)
  (title := /-- Positivity of the unregularized harmonic quantity -/)
  (latexEnv := "lemma")]
lemma unregularized_plan_harmonic_positive_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (q : PMF (Fin K)) (hn : plan_total_samples n ≠ 0)
    (hsupp : target_supported_by_plan p n (fun z => pmf_real_mass q z)) :
    0 < unregularized_plan_harmonic_local p n
      (fun z => pmf_real_mass q z) := by
  have hsum := finite_pmf_real_mass_sum_local q
  have hex : ∃ z, 0 < pmf_real_mass q z := by
    by_contra h
    push Not at h
    have hz : ∀ z, pmf_real_mass q z = 0 := fun z =>
      le_antisymm (h z) ENNReal.toReal_nonneg
    rw [Finset.sum_eq_zero fun z _ => hz z] at hsum
    norm_num at hsum
  rcases hex with ⟨z, hz⟩
  have hlam := expected_group_count_positive_of_supported_local p n
    (fun j => pmf_real_mass q j) hn hsupp z hz
  unfold unregularized_plan_harmonic_local
  have hnonneg : ∀ j, 0 ≤ if pmf_real_mass q j = 0 then 0
      else (pmf_real_mass q j) ^ 2 /
        plan_expected_group_count_local p n j := by
    intro j
    split_ifs with hj
    · exact le_rfl
    · exact div_nonneg (sq_nonneg _) (plan_expected_group_count_nonnegative_local p n j)
  have hterm : 0 < (if pmf_real_mass q z = 0 then 0
      else (pmf_real_mass q z) ^ 2 /
        plan_expected_group_count_local p n z) := by
    rw [if_neg (ne_of_gt hz)]
    exact div_pos (sq_pos_of_pos hz) hlam
  exact lt_of_lt_of_le hterm
    (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ z))

@[blueprint "lem:regularized-harmonic-supported-lower-local"
  (statement := /-- For a nonempty plan supporting a probability target,
  [
  A_+(n,q)\ge \frac{H(n,q)}{1+C_q^2H(n,q)}.
  ] -/)
  (proof := /-- Each supported nonzero coordinate has positive expected count
  by \cref{lem:expected-group-count-positive-of-supported-local}. The
  corresponding unregularized summand is bounded by $H$, while $q_z^{-1}$ is
  bounded by $C_q$, whose positivity follows from
  \cref{lem:target-reciprocal-mass-sum-positive-pmf-local}. Hence
  $\lambda_z^{-1}\le C_q^2H$, and cross-multiplication bounds the
  unregularized summand by $(1+C_q^2H)$ times its regularized counterpart.
  The remaining summands are nonnegative by
  \cref{lem:plan-expected-group-count-nonnegative-local}. Summing and using
  \cref{lem:unregularized-plan-harmonic-positive-local} proves the claim. -/)
  (title := /-- Regularized harmonic lower comparison on supported plans -/)
  (latexEnv := "lemma")]
lemma regularized_harmonic_supported_lower_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (qpmf : PMF (Fin K)) (hn : plan_total_samples n ≠ 0)
    (hsupp : target_supported_by_plan p n
      (fun z => pmf_real_mass qpmf z)) :
    let q := fun z => pmf_real_mass qpmf z
    let H := unregularized_plan_harmonic_local p n q
    let C := target_reciprocal_mass_sum_local q
    H / (1 + C ^ 2 * H) ≤ regularized_plan_harmonic_local p n q := by
  let q : Fin K → ℝ := fun z => pmf_real_mass qpmf z
  let H := unregularized_plan_harmonic_local p n q
  let C := target_reciprocal_mass_sum_local q
  have hH : 0 < H :=
    unregularized_plan_harmonic_positive_local p n qpmf hn hsupp
  have hC : 0 < C :=
    target_reciprocal_mass_sum_positive_pmf_local qpmf
  have hden : 0 < 1 + C ^ 2 * H := by positivity
  apply (div_le_iff₀ hden).2
  change H ≤ regularized_plan_harmonic_local p n q * (1 + C ^ 2 * H)
  conv_lhs =>
    rw [show H = ∑ z, if q z = 0 then 0
      else (q z) ^ 2 / plan_expected_group_count_local p n z by
        rfl]
  unfold regularized_plan_harmonic_local
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro z hz
  by_cases hqz : q z = 0
  · change (if q z = 0 then 0 else _) ≤
      (q z) ^ 2 / (plan_expected_group_count_local p n z + 1) *
        (1 + C ^ 2 * H)
    simp [hqz, le_of_lt hden]
  have hqpos : 0 < q z :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hqz)
  have hlam : 0 < plan_expected_group_count_local p n z :=
    expected_group_count_positive_of_supported_local p n q hn hsupp z hqpos
  have htermle :
      (q z) ^ 2 / plan_expected_group_count_local p n z ≤ H := by
    dsimp only [H]
    unfold unregularized_plan_harmonic_local
    have hnonneg : ∀ j, 0 ≤ if q j = 0 then 0
        else (q j) ^ 2 / plan_expected_group_count_local p n j := by
      intro j
      by_cases hj : q j = 0
      · simp [hj]
      · rw [if_neg hj]
        exact div_nonneg (sq_nonneg _)
          (plan_expected_group_count_nonnegative_local p n j)
    simpa [hqz] using
      (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ z))
  have hinvle : (q z)⁻¹ ≤ C := by
    dsimp only [C]
    unfold target_reciprocal_mass_sum_local
    exact Finset.single_le_sum
      (fun j _ => inv_nonneg.2 ENNReal.toReal_nonneg)
      (Finset.mem_univ z)
  have hinv : 1 / plan_expected_group_count_local p n z ≤ C ^ 2 * H := by
    have hsq : (q z)⁻¹ ^ 2 ≤ C ^ 2 := by nlinarith [inv_pos.2 hqpos]
    have hmul := mul_le_mul hsq htermle
      (div_nonneg (sq_nonneg _) (le_of_lt hlam)) (sq_nonneg C)
    field_simp [hqz, ne_of_gt hlam] at hmul ⊢
    nlinarith
  change (if q z = 0 then 0 else
      (q z) ^ 2 / plan_expected_group_count_local p n z) ≤
    (q z) ^ 2 / (plan_expected_group_count_local p n z + 1) *
      (1 + C ^ 2 * H)
  rw [if_neg hqz]
  have hlam1 : 0 < plan_expected_group_count_local p n z + 1 := by linarith
  field_simp [ne_of_gt hlam, ne_of_gt hlam1]
  field_simp [ne_of_gt hlam] at hinv
  nlinarith [sq_nonneg (q z)]

@[blueprint "lem:regularized-harmonic-unsupported-lower-local"
  (statement := /-- If a plan does not support a probability target, then
  $A_+(n,q)\ge C_q^{-2}$. -/)
  (proof := /-- Choose a positive target coordinate whose mixture mass is not
  positive. Nonnegativity forces its expected count to be zero, including for
  the empty plan. Its regularized summand is therefore $q_z^2$. Since
  $q_z^{-1}\le C_q$ and $C_q>0$ by
  \cref{lem:target-reciprocal-mass-sum-positive-pmf-local}, one has
  $C_q^{-2}\le q_z^2$. The full sum is at least this coordinate by
  \cref{lem:plan-expected-group-count-nonnegative-local}. -/)
  (title := /-- Regularized lower bound for unsupported plans -/)
  (latexEnv := "lemma")]
lemma regularized_harmonic_unsupported_lower_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (qpmf : PMF (Fin K))
    (hnsupp : ¬ target_supported_by_plan p n
      (fun z => pmf_real_mass qpmf z)) :
    let q := fun z => pmf_real_mass qpmf z
    let C := target_reciprocal_mass_sum_local q
    1 / C ^ 2 ≤ regularized_plan_harmonic_local p n q := by
  let q : Fin K → ℝ := fun z => pmf_real_mass qpmf z
  let C := target_reciprocal_mass_sum_local q
  unfold target_supported_by_plan at hnsupp
  push Not at hnsupp
  rcases hnsupp with ⟨z, hqpos, hmix⟩
  have hmixnonneg : 0 ≤ source_mixture_mass p n z := by
    unfold source_mixture_mass
    split_ifs
    · exact le_rfl
    · exact div_nonneg
        (plan_expected_group_count_nonnegative_local p n z)
        (Nat.cast_nonneg _)
  have hmixzero : source_mixture_mass p n z = 0 :=
    le_antisymm hmix hmixnonneg
  have hlamzero : plan_expected_group_count_local p n z = 0 := by
    by_cases hn : plan_total_samples n = 0
    · unfold plan_expected_group_count_local
      have hall : ∀ m, n m = 0 := by
        intro m
        have hm : n m ≤ plan_total_samples n := by
          unfold plan_total_samples
          exact Finset.single_le_sum (fun j _ => Nat.zero_le (n j))
            (Finset.mem_univ m)
        omega
      simp [hall]
    · unfold source_mixture_mass at hmixzero
      rw [if_neg hn] at hmixzero
      have hN : (plan_total_samples n : ℝ) ≠ 0 := by exact_mod_cast hn
      exact (div_eq_zero_iff.mp hmixzero).resolve_right hN
  have hC : 0 < C :=
    target_reciprocal_mass_sum_positive_pmf_local qpmf
  have hinvle : (q z)⁻¹ ≤ C := by
    dsimp only [C]
    unfold target_reciprocal_mass_sum_local
    exact Finset.single_le_sum
      (fun j _ => inv_nonneg.2 ENNReal.toReal_nonneg)
      (Finset.mem_univ z)
  have hq : 0 < q z := hqpos
  have hcoord : 1 / C ^ 2 ≤ (q z) ^ 2 := by
    have hs : (q z)⁻¹ ^ 2 ≤ C ^ 2 := by
      nlinarith [inv_pos.2 hq]
    field_simp [ne_of_gt hC, ne_of_gt hq] at hs ⊢
    nlinarith
  calc
    1 / C ^ 2 ≤ (q z) ^ 2 := hcoord
    _ = (q z) ^ 2 / (plan_expected_group_count_local p n z + 1) := by
      rw [hlamzero]
      ring
    _ ≤ regularized_plan_harmonic_local p n q := by
      unfold regularized_plan_harmonic_local
      exact Finset.single_le_sum
        (fun j _ => div_nonneg (sq_nonneg _)
          (add_nonneg (plan_expected_group_count_nonnegative_local p n j)
            zero_le_one))
        (Finset.mem_univ z)

@[blueprint "lem:regularized-harmonic-uniform-lower-local"
  (statement := /-- Let $x\ge0$. If every supported nonempty plan has
  $H(n,q)\ge x$, then every plan, supported or not, satisfies
  [
  A_+(n,q)\ge \frac{x}{1+C_q^2x}.
  ] -/)
  (proof := /-- For supported nonempty plans, apply
  \cref{lem:regularized-harmonic-supported-lower-local} and monotonicity of
  $u\mapsto u/(1+C_q^2u)$. Empty plans are unsupported for a probability
  target by \cref{lem:finite-pmf-real-mass-sum-local}; positivity of the
  harmonic and reciprocal-mass constants is supplied by
  \cref{lem:unregularized-plan-harmonic-positive-local,lem:target-reciprocal-mass-sum-positive-pmf-local}.
  For unsupported plans,
  \cref{lem:regularized-harmonic-unsupported-lower-local} applies, and
  $x/(1+C_q^2x)\le C_q^{-2}$. -/)
  (title := /-- Uniform regularized harmonic lower comparison -/)
  (latexEnv := "lemma")]
lemma regularized_harmonic_uniform_lower_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (qpmf : PMF (Fin K)) (x : ℝ) (hx : 0 ≤ x)
    (hcompare : target_supported_by_plan p n
        (fun z => pmf_real_mass qpmf z) →
      plan_total_samples n ≠ 0 →
      x ≤ unregularized_plan_harmonic_local p n
        (fun z => pmf_real_mass qpmf z)) :
    let q := fun z => pmf_real_mass qpmf z
    let C := target_reciprocal_mass_sum_local q
    x / (1 + C ^ 2 * x) ≤ regularized_plan_harmonic_local p n q := by
  let q : Fin K → ℝ := fun z => pmf_real_mass qpmf z
  let C := target_reciprocal_mass_sum_local q
  have hC : 0 < C :=
    target_reciprocal_mass_sum_positive_pmf_local qpmf
  have hdx : 0 < 1 + C ^ 2 * x := by positivity
  by_cases hsupp : target_supported_by_plan p n q
  · have hn : plan_total_samples n ≠ 0 := by
      intro hn
      have hsum := finite_pmf_real_mass_sum_local qpmf
      have hex : ∃ z, 0 < q z := by
        by_contra h
        push Not at h
        have hz : ∀ z, q z = 0 := fun z =>
          le_antisymm (h z) ENNReal.toReal_nonneg
        rw [Finset.sum_eq_zero fun z _ => hz z] at hsum
        norm_num at hsum
      rcases hex with ⟨z, hz⟩
      have := hsupp z hz
      unfold source_mixture_mass at this
      simp [hn] at this
    have hHpos := unregularized_plan_harmonic_positive_local p n qpmf hn hsupp
    have hxH := hcompare hsupp hn
    have hdH : 0 < 1 + C ^ 2 *
        unregularized_plan_harmonic_local p n q := by positivity
    have hmono :
        x / (1 + C ^ 2 * x) ≤
          unregularized_plan_harmonic_local p n q /
            (1 + C ^ 2 * unregularized_plan_harmonic_local p n q) := by
      apply (div_le_div_iff₀ hdx hdH).2
      nlinarith
    exact le_trans hmono
      (regularized_harmonic_supported_lower_local p n qpmf hn hsupp)
  · have hu := regularized_harmonic_unsupported_lower_local p n qpmf hsupp
    have hxc : x / (1 + C ^ 2 * x) ≤ 1 / C ^ 2 := by
      apply (div_le_div_iff₀ hdx (sq_pos_of_pos hC)).2
      nlinarith [sq_pos_of_pos hC]
    exact le_trans hxc hu

@[blueprint "def:uniform-source-plan-local"
  (statement := /-- The uniform source plan with multiplicity $t$ takes
  exactly $t$ observations from every source. -/)
  (title := /-- Uniform source-covering plan -/)
  (latexEnv := "definition")]
def uniform_source_plan_local {M : ℕ} (t : ℕ) : sampling_plan M :=
  fun _ => t

@[blueprint "def:total-source-cost-local"
  (statement := /-- The total cost of taking one observation from every
  source is $c_\Sigma=\sum_m c_m$. -/)
  (title := /-- Total one-round source cost -/)
  (latexEnv := "definition")]
noncomputable def total_source_cost_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) : ℝ :=
  ∑ m, p.cost m

@[blueprint "lem:total-source-cost-positive-local"
  (statement := /-- The total one-round source cost is positive. -/)
  (proof := /-- Every source cost is strictly positive, and the finite source
  type is nonempty. -/)
  (title := /-- Positivity of total source cost -/)
  (latexEnv := "lemma")]
lemma total_source_cost_positive_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) :
    0 < total_source_cost_local p := by
  unfold total_source_cost_local
  exact Finset.sum_pos (fun m _ => p.cost_pos m) Finset.univ_nonempty

@[blueprint "lem:uniform-source-plan-cost-local"
  (statement := /-- A uniform source plan of multiplicity $t$ costs
  $t c_\Sigma$. -/)
  (proof := /-- Expand the finite cost sum and factor out the common
  multiplicity. -/)
  (title := /-- Cost of a uniform source plan -/)
  (latexEnv := "lemma")]
lemma uniform_source_plan_cost_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (t : ℕ) :
    plan_cost p.cost (uniform_source_plan_local t) =
      t * total_source_cost_local p := by
  unfold plan_cost uniform_source_plan_local total_source_cost_local
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

@[blueprint "lem:uniform-source-plan-support-local"
  (statement := /-- Every positive-multiplicity uniform source plan supports
  every probability target. -/)
  (proof := /-- For each positive target coordinate, source coverage supplies
  one source assigning it positive mass. Thus its expected count under the
  uniform plan is positive. The total sample size is also positive, so the
  induced mixture mass is positive. -/)
  (title := /-- Support supplied by uniform source sampling -/)
  (latexEnv := "lemma")]
lemma uniform_source_plan_support_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (q : Fin K → ℝ)
    (t : ℕ) (ht : 0 < t) :
    target_supported_by_plan p (uniform_source_plan_local t) q := by
  intro z hq
  unfold source_mixture_mass
  have htotal : plan_total_samples (uniform_source_plan_local (M := M) t) ≠ 0 := by
    unfold plan_total_samples uniform_source_plan_local
    simp [NeZero.ne M, Nat.ne_of_gt ht]
  rw [if_neg htotal]
  have hN : 0 < (plan_total_samples
      (uniform_source_plan_local (M := M) t) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero htotal
  apply div_pos
  · rcases p.source_covers z with ⟨m, hm⟩
    unfold uniform_source_plan_local
    exact Finset.sum_pos'
      (fun j _ => mul_nonneg (Nat.cast_nonneg _)
        ENNReal.toReal_nonneg)
      ⟨m, Finset.mem_univ m, mul_pos (by exact_mod_cast ht) hm⟩
  · exact hN

@[blueprint "lem:uniform-source-plan-harmonic-scale-local"
  (statement := /-- For $t>0$, the harmonic quantity of the multiplicity-$t$
  uniform source plan is $t^{-1}$ times that of one round. -/)
  (proof := /-- Every expected group count is multiplied by $t$. Substitute
  this identity in each nonzero-target harmonic summand and factor out
  $t^{-1}$. -/)
  (title := /-- Harmonic scaling of uniform source sampling -/)
  (latexEnv := "lemma")]
lemma uniform_source_plan_harmonic_scale_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (q : Fin K → ℝ)
    (t : ℕ) (ht : 0 < t) :
    unregularized_plan_harmonic_local p
        (uniform_source_plan_local t) q =
      unregularized_plan_harmonic_local p
        (uniform_source_plan_local 1) q / t := by
  unfold unregularized_plan_harmonic_local
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hq : q z = 0
  · simp [hq]
  · simp only [hq, if_false]
    unfold plan_expected_group_count_local uniform_source_plan_local
    push_cast
    rw [← Finset.mul_sum]
    field_simp [Nat.ne_of_gt ht]

@[blueprint "def:regularized-information-profile-local"
  (statement := /-- For constants $C,d,\rho>0$, define
  \[
  G_{C,d,\rho}(a)=
  \frac{da}{(1+C\sqrt{da}/\rho)^2}.
  \] -/)
  (title := /-- Explicit regularized information lower profile -/)
  (latexEnv := "definition")]
noncomputable def regularized_information_profile_local
    (C d ρ a : ℝ) : ℝ :=
  d * a / (1 + C * Real.sqrt (d * a) / ρ) ^ 2

@[blueprint "lem:regularized-information-profile-bound-local"
  (statement := /-- If $C,d,\rho,a>0$, $W\ge0$, and
  \[
  a\le \frac{\sqrt W}{\rho/(Ca)}
    +\sqrt{W(a/d)},
  \]
  then $G_{C,d,\rho}(a)\le W$. -/)
  (proof := /-- Put $u=\sqrt{da}$ and $y=\sqrt W$. Multiplying the assumed
  inequality by $u$ and using
  $u\sqrt{W(a/d)}=ya$ gives
  $u\le y(1+Cu/\rho)$. The factor in parentheses is positive, so division
  and squaring yield the asserted bound. -/)
  (title := /-- Solving the regularized information inequality -/)
  (latexEnv := "lemma")]
lemma regularized_information_profile_bound_local
    (C d ρ a W : ℝ) (hC : 0 < C) (hd : 0 < d) (hρ : 0 < ρ)
    (ha : 0 < a) (hW : 0 ≤ W)
    (hineq : a ≤ Real.sqrt W / (ρ / (C * a)) +
      Real.sqrt (W * (a / d))) :
    regularized_information_profile_local C d ρ a ≤ W := by
  let u := Real.sqrt (d * a)
  let y := Real.sqrt W
  let r := Real.sqrt (W * (a / d))
  have hu : 0 < u := Real.sqrt_pos.2 (mul_pos hd ha)
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = d * a := by
    exact Real.sq_sqrt (le_of_lt (mul_pos hd ha))
  have hy2 : y ^ 2 = W := Real.sq_sqrt hW
  have hr2 : r ^ 2 = W * (a / d) := by
    exact Real.sq_sqrt (mul_nonneg hW (div_nonneg (le_of_lt ha) (le_of_lt hd)))
  have hru : r * u = y * a := by
    have hleft : 0 ≤ r * u := mul_nonneg hr (le_of_lt hu)
    have hright : 0 ≤ y * a := mul_nonneg hy (le_of_lt ha)
    have heq : (r * u) ^ 2 = (y * a) ^ 2 := by
      rw [mul_pow, hr2, hu2, mul_pow, hy2]
      field_simp [ne_of_gt hd]
    nlinarith [sq_nonneg (r * u + y * a)]
  have hineq' : a ≤ y * C * a / ρ + r := by
    dsimp only [y, r]
    convert hineq using 1
    field_simp [ne_of_gt hC, ne_of_gt hρ, ne_of_gt ha]
  have hm := mul_le_mul_of_nonneg_right hineq' (le_of_lt hu)
  have huk : u ≤ y * (1 + C * u / ρ) := by
    rw [add_mul, hru] at hm
    field_simp [ne_of_gt hρ] at hm ⊢
    nlinarith
  have hk : 0 < 1 + C * u / ρ := by positivity
  have hratio : u / (1 + C * u / ρ) ≤ y :=
    (div_le_iff₀ hk).2 (by simpa [mul_comm] using huk)
  have hratio0 : 0 ≤ u / (1 + C * u / ρ) :=
    div_nonneg (le_of_lt hu) (le_of_lt hk)
  have hsq : (u / (1 + C * u / ρ)) ^ 2 ≤ y ^ 2 := by
    nlinarith [mul_self_le_mul_self hratio0 hratio]
  unfold regularized_information_profile_local
  change d * a / (1 + C * u / ρ) ^ 2 ≤ W
  rw [← hu2, ← hy2]
  simpa [div_pow] using hsq

@[blueprint "lem:regularized-information-profile-monotone-local"
  (statement := /-- For $C\ge0$, $d>0$, and $\rho>0$, the profile
  $a\mapsto G_{C,d,\rho}(a)$ is increasing on $[0,\infty)$. -/)
  (proof := /-- Write the profile as
  $(u/(1+Cu/\rho))^2$ with $u=\sqrt{da}$. Both the square root and
  $u\mapsto u/(1+Cu/\rho)$ are increasing; the latter assertion follows by
  cross-multiplication, since the mixed terms cancel. -/)
  (title := /-- Monotonicity of the information lower profile -/)
  (latexEnv := "lemma")]
lemma regularized_information_profile_monotone_local
    (C d ρ a b : ℝ) (hC : 0 ≤ C) (hd : 0 < d) (hρ : 0 < ρ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    regularized_information_profile_local C d ρ a ≤
      regularized_information_profile_local C d ρ b := by
  have hb : 0 ≤ b := le_trans ha hab
  let u := Real.sqrt (d * a)
  let v := Real.sqrt (d * b)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have huv : u ≤ v := Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left hab (le_of_lt hd))
  have hu2 : u ^ 2 = d * a := Real.sq_sqrt (mul_nonneg (le_of_lt hd) ha)
  have hv2 : v ^ 2 = d * b := Real.sq_sqrt (mul_nonneg (le_of_lt hd) hb)
  have hku : 0 < 1 + C * u / ρ := by positivity
  have hkv : 0 < 1 + C * v / ρ := by positivity
  have hfrac : u / (1 + C * u / ρ) ≤ v / (1 + C * v / ρ) := by
    apply (div_le_div_iff₀ hku hkv).2
    field_simp [ne_of_gt hρ]
    nlinarith
  have hsq : (u / (1 + C * u / ρ)) ^ 2 ≤
      (v / (1 + C * v / ρ)) ^ 2 := by
    nlinarith [mul_self_le_mul_self
      (div_nonneg hu (le_of_lt hku)) hfrac]
  unfold regularized_information_profile_local
  change d * a / (1 + C * u / ρ) ^ 2 ≤
    d * b / (1 + C * v / ρ) ^ 2
  rw [← hu2, ← hv2]
  simpa [div_pow] using hsq

@[blueprint "lem:population-worst-case-profile-lower-local"
  (statement := /-- Suppose $\sigma^2>0$ and
  $0<\rho\le R$ with $\rho^2<\sigma^2$. For every measurable estimator and
  every $0<x\le A_+(n,q_T)$, its worst-case risk is at least
  $G_{C_{q_T},\sigma^2-\rho^2,\rho}(x)$. -/)
  (proof := /-- Apply
  \cref{lem:population-worst-case-regularized-information-local} and solve its
  scalar inequality with
  \cref{lem:regularized-information-profile-bound-local}. The worst-case risk
  is nonnegative because it dominates the risk of the centered two-point
  model from \cref{lem:two-point-location-model-in-class-local}. Positivity of
  the harmonic and reciprocal-mass constants follows from
  \cref{lem:regularized-plan-harmonic-positive-pmf-local,lem:target-reciprocal-mass-sum-positive-pmf-local}.
  Finally use
  \cref{lem:regularized-information-profile-monotone-local} and
  $x\le A_+(n,q_T)$. -/)
  (title := /-- Explicit profile lower bound for worst-case population risk -/)
  (latexEnv := "lemma")]
lemma population_worst_case_profile_lower_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (estimator : sampled_dataset K M n → ℝ) (hmeas : Measurable estimator)
    (hrisk : BddAbove {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
      s = population_mean_risk p n estimator P})
    (hvar : 0 < p.varianceBound) (ρ : ℝ) (hρ : 0 < ρ)
    (hρvar : ρ ^ 2 < p.varianceBound) (hρmean : ρ ≤ p.meanRadius)
    (x : ℝ) (hx : 0 < x)
    (hxA : x ≤ regularized_plan_harmonic_local p n
      (fun z => pmf_real_mass p.targetGroup z)) :
    regularized_information_profile_local
        (target_reciprocal_mass_sum_local
          (fun z => pmf_real_mass p.targetGroup z))
        (p.varianceBound - ρ ^ 2) ρ x ≤
      population_worst_case_risk p n estimator hrisk := by
  let q : Fin K → ℝ := fun z => pmf_real_mass p.targetGroup z
  let A := regularized_plan_harmonic_local p n q
  let C := target_reciprocal_mass_sum_local q
  let W := population_worst_case_risk p n estimator hrisk
  have hA : 0 < A :=
    regularized_plan_harmonic_positive_pmf_local p n p.targetGroup
  have hC : 0 < C :=
    target_reciprocal_mass_sum_positive_pmf_local p.targetGroup
  have hd : 0 < p.varianceBound - ρ ^ 2 := sub_pos.2 hρvar
  have hW : 0 ≤ W := by
    let v : Fin K → ℝ := regularized_plan_direction_local p n q
    have hzero : ∀ z, |(0 : ℝ) * v z| ≤ Real.sqrt p.varianceBound := by simp
    have hzclass := two_point_location_model_in_class_local p v 0 hvar hzero
      (fun z => by simp [p.meanRadius_nonneg])
    have hmember : population_mean_risk p n estimator
        (two_point_location_model_local p v 0) ∈
        {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
          s = population_mean_risk p n estimator P} :=
      ⟨two_point_location_model_local p v 0, hzclass, rfl⟩
    exact le_trans (MeasureTheory.integral_nonneg fun D => sq_nonneg _)
      (le_csSup hrisk hmember)
  have hineq := population_worst_case_regularized_information_local
    p n estimator hmeas hrisk hvar ρ hρ hρvar hρmean
  dsimp only at hineq
  have hprofileA :
      regularized_information_profile_local C
          (p.varianceBound - ρ ^ 2) ρ A ≤ W := by
    apply regularized_information_profile_bound_local C
      (p.varianceBound - ρ ^ 2) ρ A W hC hd hρ hA hW
    simpa [q, A, C, W] using hineq
  exact le_trans
    (regularized_information_profile_monotone_local C
      (p.varianceBound - ρ ^ 2) ρ x A (le_of_lt hC) hd hρ
      (le_of_lt hx) hxA)
    hprofileA

@[blueprint "def:normalized-optimal-harmonic-local"
  (statement := /-- For a selected plan family, let
  \[
  x(B)=\frac{C_c(n(B))}{B}H(n(B),q_T).
  \] -/)
  (title := /-- Budget-normalized optimal harmonic quantity -/)
  (latexEnv := "definition")]
noncomputable def normalized_optimal_harmonic_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M)
    (plans : ℝ → sampling_plan M) (B : ℝ) : ℝ :=
  plan_cost p.cost (plans B) / B *
    unregularized_plan_harmonic_local p (plans B)
      (fun z => pmf_real_mass p.targetGroup z)

@[blueprint "lem:optimal-plan-supported-above-cover-cost-local"
  (statement := /-- At every budget at least $c_\Sigma$, a target-effective-
  sample-size optimal plan is nonempty and supports the target. -/)
  (proof := /-- The one-round uniform source plan is feasible by
  \cref{lem:uniform-source-plan-cost-local} and supports the target by
  \cref{lem:uniform-source-plan-support-local}. Its harmonic quantity is
  positive by \cref{lem:unregularized-plan-harmonic-positive-local}, so its
  effective sample size is positive by
  \cref{lem:effective-sample-size-harmonic-local}. Optimality forces the
  selected plan to have positive effective sample size, which excludes both
  emptiness and failure of target support. -/)
  (title := /-- Eventual support of target-optimal plans -/)
  (latexEnv := "lemma")]
lemma optimal_plan_supported_above_cover_cost_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (B : ℝ)
    (nopt : sampling_plan M)
    (hB : total_source_cost_local p ≤ B)
    (hopt : optimal_sampling_plan p
      (fun z => pmf_real_mass p.targetGroup z) B nopt) :
    plan_total_samples nopt ≠ 0 ∧
      target_supported_by_plan p nopt
        (fun z => pmf_real_mass p.targetGroup z) := by
  let ncover : sampling_plan M := uniform_source_plan_local 1
  have hcost : budget_feasible_plan p B ncover := by
    unfold budget_feasible_plan
    rw [show plan_cost p.cost ncover = total_source_cost_local p by
      simpa [ncover] using uniform_source_plan_cost_local p 1]
    exact hB
  have hcover : target_supported_by_plan p ncover
      (fun z => pmf_real_mass p.targetGroup z) :=
    uniform_source_plan_support_local p _ 1 Nat.zero_lt_one
  have hncover : plan_total_samples ncover ≠ 0 := by
    unfold ncover plan_total_samples uniform_source_plan_local
    simp [NeZero.ne M]
  have hHcover : 0 < unregularized_plan_harmonic_local p ncover
      (fun z => pmf_real_mass p.targetGroup z) :=
    unregularized_plan_harmonic_positive_local p ncover p.targetGroup
      hncover hcover
  have heffcover : 0 < effective_sample_size p ncover
      (fun z => pmf_real_mass p.targetGroup z) := by
    rw [effective_sample_size_harmonic_local p ncover _ hncover hcover]
    exact inv_pos.2 hHcover
  have heffopt : 0 < effective_sample_size p nopt
      (fun z => pmf_real_mass p.targetGroup z) :=
    lt_of_lt_of_le heffcover (hopt.2 ncover hcost)
  constructor
  · intro hn
    rw [effective_sample_size] at heffopt
    simp [hn] at heffopt
  · by_contra hs
    rw [effective_sample_size] at heffopt
    simp [hs] at heffopt

@[blueprint "lem:normalized-optimal-harmonic-comparison-local"
  (statement := /-- Above the covering cost, the normalized optimal harmonic
  quantity $x(B)$ is positive, is at most the optimal harmonic quantity, and
  is at most $H(n,q_T)$ for every supported nonempty budget-feasible plan
  $n$. -/)
  (proof := /-- By
  \cref{lem:optimal-plan-supported-above-cover-cost-local}, the selected plan
  is supported and nonempty. Its positive costs and feasibility put its
  expenditure fraction in $(0,1]$, proving the first two assertions.
  Positivity of both harmonic quantities is
  \cref{lem:unregularized-plan-harmonic-positive-local}.
  For another supported plan, rewrite both effective sample sizes by
  \cref{lem:effective-sample-size-harmonic-local}; optimality and positivity
  reverse the reciprocal inequality, and multiplication by the expenditure
  fraction gives the last assertion. -/)
  (title := /-- Comparison properties of the normalized optimum -/)
  (latexEnv := "lemma")]
lemma normalized_optimal_harmonic_comparison_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M)
    (plans : ℝ → sampling_plan M) (B : ℝ)
    (hBpos : 0 < B) (hBcover : total_source_cost_local p ≤ B)
    (hopt : optimal_sampling_plan p
      (fun z => pmf_real_mass p.targetGroup z) B (plans B)) :
    let x := normalized_optimal_harmonic_local p plans B
    let Hopt := unregularized_plan_harmonic_local p (plans B)
      (fun z => pmf_real_mass p.targetGroup z)
    0 < x ∧ x ≤ Hopt ∧
      ∀ n, budget_feasible_plan p B n →
        target_supported_by_plan p n
          (fun z => pmf_real_mass p.targetGroup z) →
        plan_total_samples n ≠ 0 →
        x ≤ unregularized_plan_harmonic_local p n
          (fun z => pmf_real_mass p.targetGroup z) := by
  let q : Fin K → ℝ := fun z => pmf_real_mass p.targetGroup z
  let x := normalized_optimal_harmonic_local p plans B
  let Hopt := unregularized_plan_harmonic_local p (plans B) q
  obtain ⟨hnopt, hsopt⟩ :=
    optimal_plan_supported_above_cover_cost_local p B (plans B)
      hBcover hopt
  have hHopt : 0 < Hopt :=
    unregularized_plan_harmonic_positive_local p (plans B) p.targetGroup
      hnopt hsopt
  have hcostnonneg : 0 < plan_cost p.cost (plans B) := by
    unfold plan_cost
    have hex : ∃ m, 0 < (plans B m : ℝ) := by
      by_contra h
      push Not at h
      have hz : ∀ m, plans B m = 0 := fun m => by
        have hzr : (plans B m : ℝ) = 0 :=
          le_antisymm (h m) (Nat.cast_nonneg _)
        exact_mod_cast hzr
      unfold plan_total_samples at hnopt
      simp [hz] at hnopt
    rcases hex with ⟨m, hm⟩
    exact Finset.sum_pos'
      (fun j _ => mul_nonneg (le_of_lt (p.cost_pos j)) (Nat.cast_nonneg _))
      ⟨m, Finset.mem_univ m, mul_pos (p.cost_pos m) hm⟩
  have hfracpos : 0 < plan_cost p.cost (plans B) / B :=
    div_pos hcostnonneg hBpos
  have hfracle : plan_cost p.cost (plans B) / B ≤ 1 := by
    apply (div_le_one hBpos).2
    exact hopt.1
  have hxdef : x = plan_cost p.cost (plans B) / B * Hopt := rfl
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have hxH : x ≤ Hopt := by
    rw [hxdef]
    nlinarith [mul_le_mul_of_nonneg_right hfracle (le_of_lt hHopt)]
  refine ⟨hxpos, hxH, ?_⟩
  intro n hnfeas hsupp hn
  have hHn : 0 < unregularized_plan_harmonic_local p n q :=
    unregularized_plan_harmonic_positive_local p n p.targetGroup hn hsupp
  have heff := hopt.2 n hnfeas
  rw [effective_sample_size_harmonic_local p n q hn hsupp,
    effective_sample_size_harmonic_local p (plans B) q hnopt hsopt] at heff
  have hHH : Hopt ≤ unregularized_plan_harmonic_local p n q := by
    apply (inv_le_inv₀ hHn hHopt).mp
    exact heff
  exact le_trans hxH hHH

@[blueprint "lem:population-leading-risk-normalized-harmonic-local"
  (statement := /-- Above the covering cost, the population leading risk at
  the selected optimal plan is exactly $\sigma^2x(B)$. -/)
  (proof := /-- The selected plan is supported and nonempty by
  \cref{lem:optimal-plan-supported-above-cover-cost-local}. Substitute
  \cref{lem:plan-discrepancy-harmonic-local} and the definition of average
  cost; the total sample size cancels, leaving the normalized harmonic
  quantity. -/)
  (title := /-- Leading risk in normalized harmonic form -/)
  (latexEnv := "lemma")]
lemma population_leading_risk_normalized_harmonic_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M)
    (plans : ℝ → sampling_plan M) (B : ℝ)
    (hBcover : total_source_cost_local p ≤ B)
    (hopt : optimal_sampling_plan p
      (fun z => pmf_real_mass p.targetGroup z) B (plans B)) :
    population_leading_risk p (plans B) B =
      p.varianceBound * normalized_optimal_harmonic_local p plans B := by
  obtain ⟨hn, hs⟩ :=
    optimal_plan_supported_above_cover_cost_local p B (plans B)
      hBcover hopt
  unfold population_leading_risk normalized_optimal_harmonic_local
    average_plan_cost
  rw [if_neg hn,
    plan_discrepancy_harmonic_local p (plans B) _ hn]
  push_cast
  field_simp [show (plan_total_samples (plans B) : ℝ) ≠ 0 by exact_mod_cast hn]

@[blueprint "lem:normalized-optimal-harmonic-eventual-bound-local"
  (statement := /-- Along any target-optimal plan family, $x(B)>0$
  eventually and
  \[
  x(B)\le \frac{2c_\Sigma H(n^{(1)},q_T)}{B}
  \]
  eventually, where $n^{(1)}$ takes one observation from every source. -/)
  (proof := /-- For large $B$, take
  $t=\lfloor B/c_\Sigma\rfloor$. Positivity of
  \cref{lem:total-source-cost-positive-local} gives
  $t\ge B/(2c_\Sigma)>0$. The multiplicity-$t$ uniform plan is feasible by
  \cref{lem:uniform-source-plan-cost-local}, supports the target by
  \cref{lem:uniform-source-plan-support-local}, and has harmonic quantity
  $H(n^{(1)},q_T)/t$ by
  \cref{lem:uniform-source-plan-harmonic-scale-local}. Apply
  \cref{lem:normalized-optimal-harmonic-comparison-local} and the lower bound
  on $t$; positivity of the comparison harmonic follows from
  \cref{lem:unregularized-plan-harmonic-positive-local}. -/)
  (title := /-- Inverse-budget bound for the normalized optimum -/)
  (latexEnv := "lemma")]
lemma normalized_optimal_harmonic_eventual_bound_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M)
    (plans : ℝ → sampling_plan M)
    (hplans : ∀ B, 0 < B →
      optimal_sampling_plan p
        (fun z => pmf_real_mass p.targetGroup z) B (plans B)) :
    ∀ᶠ B in Filter.atTop,
      0 < normalized_optimal_harmonic_local p plans B ∧
      normalized_optimal_harmonic_local p plans B ≤
        (2 * total_source_cost_local p *
          unregularized_plan_harmonic_local p
            (uniform_source_plan_local 1)
            (fun z => pmf_real_mass p.targetGroup z)) / B := by
  let C := total_source_cost_local p
  let H₁ := unregularized_plan_harmonic_local p
    (uniform_source_plan_local 1)
    (fun z => pmf_real_mass p.targetGroup z)
  have hC : 0 < C := total_source_cost_positive_local p
  filter_upwards [Filter.eventually_ge_atTop (2 * C)] with B hB
  have hBpos : 0 < B := lt_of_lt_of_le (by positivity : 0 < 2 * C) hB
  have hxratio : 2 ≤ B / C := by
    apply (le_div_iff₀ hC).2
    nlinarith
  let t : ℕ := ⌊B / C⌋₊
  have ht : 0 < t := Nat.floor_pos.2 (le_trans (by norm_num) hxratio)
  have htupper : (t : ℝ) ≤ B / C :=
    Nat.floor_le (div_nonneg (le_of_lt hBpos) (le_of_lt hC))
  have htlower : B / (2 * C) ≤ (t : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (B / C)
    change B / C < (t : ℝ) + 1 at hfloor
    rw [show B / (2 * C) = (B / C) / 2 by
      field_simp [ne_of_gt hC]]
    nlinarith
  let nt : sampling_plan M := uniform_source_plan_local t
  have hntfeas : budget_feasible_plan p B nt := by
    unfold budget_feasible_plan
    rw [show plan_cost p.cost nt = t * C by
      simpa [nt, C] using uniform_source_plan_cost_local p t]
    have := mul_le_mul_of_nonneg_right htupper (le_of_lt hC)
    field_simp [ne_of_gt hC] at this
    simpa [mul_comm] using this
  have hntsupp : target_supported_by_plan p nt
      (fun z => pmf_real_mass p.targetGroup z) :=
    uniform_source_plan_support_local p _ t ht
  have hntnonempty : plan_total_samples nt ≠ 0 := by
    unfold nt plan_total_samples uniform_source_plan_local
    simp [NeZero.ne M, Nat.ne_of_gt ht]
  have hcomp := normalized_optimal_harmonic_comparison_local p plans B
    hBpos (le_trans (le_mul_of_one_le_left (le_of_lt hC)
      (by norm_num : (1 : ℝ) ≤ 2)) hB) (hplans B hBpos)
  dsimp only at hcomp
  refine ⟨hcomp.1, ?_⟩
  have hxHt := hcomp.2.2 nt hntfeas hntsupp hntnonempty
  rw [uniform_source_plan_harmonic_scale_local p _ t ht] at hxHt
  change normalized_optimal_harmonic_local p plans B ≤
    2 * C * H₁ / B
  have hbound : H₁ / (t : ℝ) ≤ 2 * C * H₁ / B := by
    have hH₁ : 0 < H₁ :=
      unregularized_plan_harmonic_positive_local p
        (uniform_source_plan_local 1) p.targetGroup
        (by
          unfold plan_total_samples uniform_source_plan_local
          simp [NeZero.ne M])
        (uniform_source_plan_support_local p _ 1 Nat.zero_lt_one)
    apply (div_le_div_iff₀ (by exact_mod_cast ht) hBpos).2
    have hm := mul_le_mul_of_nonneg_right htlower (le_of_lt hH₁)
    field_simp [ne_of_gt hC] at hm
    nlinarith
  exact le_trans hxHt hbound

@[blueprint "def:asymptotic-information-ratio-local"
  (statement := /-- For variance level $\sigma^2$, reciprocal-mass constant
  $C$, and $x\ge0$, set
  \[
  R_{\sigma^2,C}(x)=
  \frac{(\sigma^2-\sqrt x)/(1+C^2x)}
  {\left(1+C\sqrt{(\sigma^2-\sqrt x)\sqrt x/(1+C^2x)}\right)^2}.
  \] -/)
  (title := /-- Asymptotic scalar information ratio -/)
  (latexEnv := "definition")]
noncomputable def asymptotic_information_ratio_local
    (σ C x : ℝ) : ℝ :=
  ((σ - Real.sqrt x) / (1 + C ^ 2 * x)) /
    (1 + C * Real.sqrt
      ((σ - Real.sqrt x) * Real.sqrt x / (1 + C ^ 2 * x))) ^ 2

@[blueprint "def:asymptotic-information-lower-local"
  (statement := /-- Define the scalar lower approximation
  $L_{\sigma^2,C}(x)=xR_{\sigma^2,C}(x)$. -/)
  (title := /-- Asymptotic scalar information lower approximation -/)
  (latexEnv := "definition")]
noncomputable def asymptotic_information_lower_local
    (σ C x : ℝ) : ℝ :=
  x * asymptotic_information_ratio_local σ C x

@[blueprint "lem:asymptotic-information-profile-identity-local"
  (statement := /-- If $x>0$ and $\sqrt x<\sigma^2$, put
  $\rho=\sqrt{\sqrt x}$, $d=\sigma^2-\sqrt x$, and
  $a=x/(1+C^2x)$. Then
  $L_{\sigma^2,C}(x)=G_{C,d,\rho}(a)$. -/)
  (proof := /-- The identities $\rho^2=\sqrt x$ and
  $(\sqrt x)^2=x$ show
  \[
  \frac{\sqrt{da}}{\rho}
  =\sqrt{\frac{d\sqrt x}{1+C^2x}}.
  \]
  Substitute this equality in the definition of the profile and collect the
  factor $x$. -/)
  (title := /-- Profile identity at the fourth-root localization scale -/)
  (latexEnv := "lemma")]
lemma asymptotic_information_profile_identity_local
    (σ C x : ℝ) (hx : 0 < x) (hσ : Real.sqrt x < σ) :
    asymptotic_information_lower_local σ C x =
      regularized_information_profile_local C
        (σ - Real.sqrt x) (Real.sqrt (Real.sqrt x))
        (x / (1 + C ^ 2 * x)) := by
  let s := Real.sqrt x
  let ρ := Real.sqrt s
  let d := σ - s
  let D := 1 + C ^ 2 * x
  let a := x / D
  have hs : 0 < s := Real.sqrt_pos.2 hx
  have hρ : 0 < ρ := Real.sqrt_pos.2 hs
  have hd : 0 < d := sub_pos.2 hσ
  have hD : 0 < D := by
    dsimp only [D]
    nlinarith [sq_nonneg C]
  have hs2 : s ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
  have hρ2 : ρ ^ 2 = s := Real.sq_sqrt (le_of_lt hs)
  have ha : 0 < a := div_pos hx hD
  have hsqrt :
      Real.sqrt (d * a) / ρ =
        Real.sqrt (d * s / D) := by
    have hl : 0 ≤ Real.sqrt (d * a) / ρ :=
      div_nonneg (Real.sqrt_nonneg _) (le_of_lt hρ)
    have hr : 0 ≤ Real.sqrt (d * s / D) := Real.sqrt_nonneg _
    have hl2 : (Real.sqrt (d * a) / ρ) ^ 2 = d * s / D := by
      rw [div_pow, Real.sq_sqrt (mul_nonneg (le_of_lt hd) (le_of_lt ha)),
        hρ2]
      dsimp only [a]
      field_simp [ne_of_gt hs, ne_of_gt hD]
      nlinarith
    have hr2 : (Real.sqrt (d * s / D)) ^ 2 = d * s / D :=
      Real.sq_sqrt (div_nonneg
        (mul_nonneg (le_of_lt hd) (le_of_lt hs)) (le_of_lt hD))
    nlinarith [sq_nonneg
      (Real.sqrt (d * a) / ρ + Real.sqrt (d * s / D))]
  unfold asymptotic_information_lower_local
    asymptotic_information_ratio_local
    regularized_information_profile_local
  dsimp only [s, ρ, d, D, a] at hsqrt
  have hsqrt' :
      Real.sqrt ((σ - Real.sqrt x) * x / (1 + C ^ 2 * x)) /
          Real.sqrt (Real.sqrt x) =
        Real.sqrt ((σ - Real.sqrt x) * Real.sqrt x /
          (1 + C ^ 2 * x)) := by
    convert hsqrt using 1 <;> ring_nf
  have hCterm :
      C * Real.sqrt ((σ - Real.sqrt x) * (x / (1 + C ^ 2 * x))) /
          Real.sqrt (Real.sqrt x) =
        C * Real.sqrt ((σ - Real.sqrt x) * Real.sqrt x /
          (1 + C ^ 2 * x)) := by
    rw [mul_div_assoc, hsqrt]
  rw [hCterm]
  ring

@[blueprint "lem:asymptotic-information-lower-little-o-local"
  (statement := /-- Suppose $x(B)>0$ eventually and
  $x(B)\le K/B$ eventually for some $K>0$. Then
  \[
  L_{\sigma^2,C}(x(B))-\sigma^2x(B)=o(B^{-1}).
  \] -/)
  (proof := /-- The squeeze theorem gives $x(B)\to0$. Continuity of square
  root and the rational expression defining
  \cref{def:asymptotic-information-ratio-local} gives
  $R_{\sigma^2,C}(x(B))\to\sigma^2$. Since the displayed difference equals
  $x(B)(R_{\sigma^2,C}(x(B))-\sigma^2)$, the bound $x(B)\le K/B$ and the
  preceding convergence verify the $\varepsilon$-definition of little-o. -/)
  (title := /-- Little-o error of the scalar information approximation -/)
  (latexEnv := "lemma")]
lemma asymptotic_information_lower_little_o_local
    (σ C K : ℝ) (x : ℝ → ℝ) (hK : 0 < K)
    (hxbound : ∀ᶠ B in Filter.atTop, 0 < x B ∧ x B ≤ K / B) :
    (fun B => asymptotic_information_lower_local σ C (x B) - σ * x B)
      =o[Filter.atTop] inverse_budget_rate := by
  have hinv : Filter.Tendsto (fun B : ℝ => B⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have hupper : Filter.Tendsto (fun B : ℝ => K / B)
      Filter.atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul hinv :
      Filter.Tendsto (fun B : ℝ => K * B⁻¹)
        Filter.atTop (nhds (K * 0))) using 1 <;>
      simp [div_eq_mul_inv]
  have hxzero : Filter.Tendsto x Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
    · filter_upwards [hxbound] with B hB
      exact le_of_lt hB.1
    · filter_upwards [hxbound] with B hB
      exact hB.2
  have hcont : ContinuousAt (asymptotic_information_ratio_local σ C) 0 := by
    unfold asymptotic_information_ratio_local
    fun_prop (disch := norm_num)
  have hratio : Filter.Tendsto
      (fun B => asymptotic_information_ratio_local σ C (x B))
      Filter.atTop (nhds σ) := by
    simpa [Function.comp_def, asymptotic_information_ratio_local] using
      hcont.tendsto.comp hxzero
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hcK : 0 < c / K := div_pos hc hK
  have herr := (Metric.tendsto_nhds.1 hratio) (c / K) hcK
  filter_upwards [hxbound, herr,
    Filter.eventually_gt_atTop (0 : ℝ)] with B hB he hBpos
  rw [show asymptotic_information_lower_local σ C (x B) - σ * x B =
      x B * (asymptotic_information_ratio_local σ C (x B) - σ) by
    unfold asymptotic_information_lower_local
    ring]
  simp only [Real.norm_eq_abs, inverse_budget_rate]
  rw [abs_mul, abs_of_pos hB.1,
    abs_of_pos (one_div_pos.2 hBpos)]
  have herrabs :
      |asymptotic_information_ratio_local σ C (x B) - σ| ≤ c / K := by
    simpa [Real.dist_eq] using le_of_lt he
  calc
    x B * |asymptotic_information_ratio_local σ C (x B) - σ| ≤
        (K / B) * (c / K) :=
      mul_le_mul hB.2 herrabs (abs_nonneg _)
        (le_trans (le_of_lt hB.1) hB.2)
    _ = c * (1 / B) := by field_simp [ne_of_gt hK, ne_of_gt hBpos]

@[blueprint "lem:population-minimax-candidate-nonempty-local"
  (statement := /-- For every nonnegative budget, the candidate set defining
  the population minimax risk is nonempty. -/)
  (proof := /-- Use the empty plan and the constant-zero estimator. The plan
  costs zero. Every model-class target mean has absolute value at most $R$:
  apply the triangle inequality, the coordinate mean bounds, and
  \cref{lem:finite-pmf-real-mass-sum-local}. Thus every risk is at most
  $R^2$, so the risk set is bounded above and supplies a minimax candidate. -/)
  (title := /-- Nonemptiness of the population minimax candidate set -/)
  (latexEnv := "lemma")]
lemma population_minimax_candidate_nonempty_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (B : ℝ) (hB : 0 ≤ B) :
    {r : ℝ | ∃ n : sampling_plan M, budget_feasible_plan p B n ∧
      ∃ estimator : sampled_dataset K M n → ℝ, Measurable estimator ∧
        ∃ hrisk : BddAbove {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
          s = population_mean_risk p n estimator P},
          r = population_worst_case_risk p n estimator hrisk}.Nonempty := by
  let n0 : sampling_plan M := fun _ => 0
  let estimator : sampled_dataset K M n0 → ℝ := fun _ => 0
  have hnfeas : budget_feasible_plan p B n0 := by
    unfold budget_feasible_plan plan_cost n0
    simpa using hB
  have htarget : ∀ P, bounded_conditional_mean_class p P →
      |target_population_mean p.targetGroup P| ≤ p.meanRadius := by
    intro P hP
    unfold target_population_mean
    calc
      |∑ z, pmf_real_mass p.targetGroup z * conditional_group_mean P z| ≤
          ∑ z, |pmf_real_mass p.targetGroup z *
            conditional_group_mean P z| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ z, pmf_real_mass p.targetGroup z *
            |conditional_group_mean P z| := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [abs_mul, abs_of_nonneg
          (show 0 ≤ pmf_real_mass p.targetGroup z from ENNReal.toReal_nonneg)]
      _ ≤ ∑ z, pmf_real_mass p.targetGroup z * p.meanRadius := by
        apply Finset.sum_le_sum
        intro z hz
        exact mul_le_mul_of_nonneg_left (hP z).2.1 ENNReal.toReal_nonneg
      _ = p.meanRadius := by
        rw [← Finset.sum_mul, finite_pmf_real_mass_sum_local]
        ring
  have hrisk : BddAbove {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
      s = population_mean_risk p n0 estimator P} := by
    refine ⟨p.meanRadius ^ 2, ?_⟩
    intro s hs
    rcases hs with ⟨P, hP, rfl⟩
    have ht := htarget P hP
    have hsq : target_population_mean p.targetGroup P ^ 2 ≤
        p.meanRadius ^ 2 := by
      have hm := mul_self_le_mul_self
        (abs_nonneg (target_population_mean p.targetGroup P)) ht
      nlinarith [sq_abs (target_population_mean p.targetGroup P)]
    letI hsource : ∀ m, IsProbabilityMeasure
        (source_observation_law p P m) := fun m =>
      ⟨by
        unfold source_observation_law
        have heval : Measurable
            (fun x : Fin K × (Fin K → ℝ) => x.2 x.1) := by
          have heq : (fun x : Fin K × (Fin K → ℝ) => x.2 x.1) =
              fun x => ∑ z, if x.1 = z then x.2 z else 0 := by
            funext x
            simp
          rw [heq]
          apply Finset.measurable_sum
          intro z hz
          exact Measurable.ite
            (measurable_fst (MeasurableSet.singleton z))
            ((measurable_pi_apply z).comp measurable_snd)
            measurable_const
        have hf : Measurable
            (fun x : Fin K × (Fin K → ℝ) => (x.1, x.2 x.1)) :=
          measurable_fst.prodMk heval
        rw [Measure.map_apply_of_aemeasurable hf.aemeasurable
          MeasurableSet.univ]
        simp⟩
    letI : IsProbabilityMeasure (sampling_law p n0 P) := by
      unfold sampling_law
      infer_instance
    rw [population_mean_risk]
    simp only [estimator, zero_sub, neg_sq]
    rw [MeasureTheory.integral_const]
    simpa using hsq
  exact ⟨population_worst_case_risk p n0 estimator hrisk,
    n0, hnfeas, estimator, measurable_const, hrisk, rfl⟩

@[blueprint "lem:population-minimax-profile-lower-local"
  (statement := /-- At a budget above the covering cost, let $x(B)$ be the
  normalized harmonic optimum and set $a=x/(1+C_{q_T}^2x)$. If
  $0<\rho\le R$ and $\rho^2<\sigma^2$, then
  \[
  G_{C_{q_T},\sigma^2-\rho^2,\rho}(a)
  \le \mathcal R^*_{\mathrm{PM}}(B).
  \] -/)
  (proof := /-- Fix any candidate plan and estimator in the infimum. The
  comparison in
  \cref{lem:normalized-optimal-harmonic-comparison-local}, together with
  \cref{lem:regularized-harmonic-uniform-lower-local}, gives $a\le A_+$ for
  that plan, including unsupported plans; the reciprocal-mass constant is
  positive by \cref{lem:target-reciprocal-mass-sum-positive-pmf-local}. Apply
  \cref{lem:population-worst-case-profile-lower-local}. The candidate set is
  nonempty by \cref{lem:population-minimax-candidate-nonempty-local}, so the
  defining property of its infimum yields the result. -/)
  (title := /-- Uniform profile lower bound for population minimax risk -/)
  (latexEnv := "lemma")]
lemma population_minimax_profile_lower_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M)
    (plans : ℝ → sampling_plan M) (B : ℝ)
    (hBpos : 0 < B) (hBcover : total_source_cost_local p ≤ B)
    (hopt : optimal_sampling_plan p
      (fun z => pmf_real_mass p.targetGroup z) B (plans B))
    (hvar : 0 < p.varianceBound) (ρ : ℝ) (hρ : 0 < ρ)
    (hρvar : ρ ^ 2 < p.varianceBound) (hρmean : ρ ≤ p.meanRadius) :
    let x := normalized_optimal_harmonic_local p plans B
    let C := target_reciprocal_mass_sum_local
      (fun z => pmf_real_mass p.targetGroup z)
    let a := x / (1 + C ^ 2 * x)
    regularized_information_profile_local C
        (p.varianceBound - ρ ^ 2) ρ a ≤
      population_minimax_risk p B := by
  let x := normalized_optimal_harmonic_local p plans B
  let q : Fin K → ℝ := fun z => pmf_real_mass p.targetGroup z
  let C := target_reciprocal_mass_sum_local q
  let a := x / (1 + C ^ 2 * x)
  have hcomp := normalized_optimal_harmonic_comparison_local p plans B
    hBpos hBcover hopt
  dsimp only at hcomp
  have hx : 0 < x := hcomp.1
  have hC : 0 < C :=
    target_reciprocal_mass_sum_positive_pmf_local p.targetGroup
  have hden : 0 < 1 + C ^ 2 * x := by positivity
  have ha : 0 < a := div_pos hx hden
  rw [population_minimax_risk]
  apply le_csInf
  · exact population_minimax_candidate_nonempty_local p B (le_of_lt hBpos)
  · intro r hr
    rcases hr with ⟨n, hnfeas, estimator, hmeas, hrisk, rfl⟩
    have haA : a ≤ regularized_plan_harmonic_local p n q := by
      apply regularized_harmonic_uniform_lower_local p n p.targetGroup x
        (le_of_lt hx)
      intro hs hn
      exact hcomp.2.2 n hnfeas hs hn
    exact population_worst_case_profile_lower_local p n estimator hmeas hrisk
      hvar ρ hρ hρvar hρmean a ha haA

@[blueprint "lem:population-minimax-effective-sample-lower-bound"
  (statement := /-- Let $K$ and $M$ be positive integers, let $p$ be a biased-source mean-estimation problem with $K$ groups, $M$ sources, and mean radius $R>0$, and let $n_T\colon\mathbb R\to\mathbb N^M$ be such that, for every $B>0$, the plan $n_T(B)$ maximizes the effective sample size for the target mass $q_T$ among all integer plans of cost at most $B$. There exists a function $\ell_{\mathrm{PM}}\colon\mathbb R\to\mathbb R$ such that $\ell_{\mathrm{PM}}=o(B^{-1})$ as $B\to\infty$ and, for all sufficiently large $B$,
  \[
  \frac{\sigma^2\bar c(n_T(B))D(q_T,\bar q_{n_T(B)})}{B}
  +\ell_{\mathrm{PM}}(B)
  \le \mathcal R^*_{\mathrm{PM}}(B,\mathcal P(R,\sigma^2)).
  \] -/)
  (proof := /-- If $\sigma^2=0$, apply
  \cref{lem:population-minimax-zero-variance-lower-local}. Suppose
  $\sigma^2>0$, and write $x(B)$ for the budget-normalized optimal harmonic
  quantity. Its reciprocal-mass constant and the one-round covering harmonic
  are positive by
  \cref{lem:target-reciprocal-mass-sum-positive-pmf-local,lem:unregularized-plan-harmonic-positive-local};
  the total covering cost is positive by
  \cref{lem:total-source-cost-positive-local}, and the one-round plan supports
  the target by \cref{lem:uniform-source-plan-support-local}. Consequently
  \cref{lem:normalized-optimal-harmonic-eventual-bound-local} gives
  $0<x(B)\le K_0/B$ eventually.

  Set $\rho(B)=\sqrt{\sqrt{x(B)}}$ and
  $a(B)=x(B)/(1+C_{q_T}^2x(B))$. For all sufficiently large budgets,
  $\rho(B)\le R$ and $\rho(B)^2<\sigma^2$. The uniform minimax information
  bound \cref{lem:population-minimax-profile-lower-local} then gives
  \[
  G_{C_{q_T},\sigma^2-\rho(B)^2,\rho(B)}(a(B))
  \le \mathcal R^*_{\mathrm{PM}}(B).
  \]
  By \cref{lem:asymptotic-information-profile-identity-local}, its left-hand
  side is $L_{\sigma^2,C_{q_T}}(x(B))$. Define the remainder to be this
  quantity minus $\sigma^2x(B)$. It is little-$o(B^{-1})$ by
  \cref{lem:asymptotic-information-lower-little-o-local}, while
  \cref{lem:population-leading-risk-normalized-harmonic-local} identifies
  $\sigma^2x(B)$ with the required population leading risk. Substitution
  yields the eventual inequality. -/)
  (title := /-- Population minimax lower bound at a target-optimal plan -/)
  (latexEnv := "lemma")]
lemma population_minimax_effective_sample_lower_bound {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (hmean : 0 < p.meanRadius)
    (plans : ℝ → sampling_plan M)
    (hplans : ∀ B, 0 < B →
      optimal_sampling_plan p (fun z => pmf_real_mass p.targetGroup z) B (plans B)) :
    ∃ remainder : ℝ → ℝ,
      Asymptotics.IsLittleO Filter.atTop remainder inverse_budget_rate ∧
      ∀ᶠ B in Filter.atTop,
        population_leading_risk p (plans B) B + remainder B ≤
          population_minimax_risk p B := by
  by_cases hvarzero : p.varianceBound = 0
  · exact population_minimax_zero_variance_lower_local p hvarzero plans
  have hvar : 0 < p.varianceBound :=
    lt_of_le_of_ne p.varianceBound_nonneg (Ne.symm hvarzero)
  let x : ℝ → ℝ := normalized_optimal_harmonic_local p plans
  let C := target_reciprocal_mass_sum_local
    (fun z => pmf_real_mass p.targetGroup z)
  let H₁ := unregularized_plan_harmonic_local p
    (uniform_source_plan_local 1)
    (fun z => pmf_real_mass p.targetGroup z)
  let K₀ := 2 * total_source_cost_local p * H₁
  have hC : 0 < C :=
    target_reciprocal_mass_sum_positive_pmf_local p.targetGroup
  have hH₁ : 0 < H₁ :=
    unregularized_plan_harmonic_positive_local p
      (uniform_source_plan_local 1) p.targetGroup
      (by
        unfold plan_total_samples uniform_source_plan_local
        simp [NeZero.ne M])
      (uniform_source_plan_support_local p _ 1 Nat.zero_lt_one)
  have hK₀ : 0 < K₀ := by
    dsimp only [K₀]
    exact mul_pos
      (mul_pos (by norm_num) (total_source_cost_positive_local p)) hH₁
  have hxbound : ∀ᶠ B in Filter.atTop,
      0 < x B ∧ x B ≤ K₀ / B := by
    simpa [x, K₀, H₁] using
      normalized_optimal_harmonic_eventual_bound_local p plans hplans
  let remainder : ℝ → ℝ := fun B =>
    asymptotic_information_lower_local p.varianceBound C (x B) -
      p.varianceBound * x B
  have hremainder :
      Asymptotics.IsLittleO Filter.atTop remainder inverse_budget_rate := by
    dsimp only [remainder]
    exact asymptotic_information_lower_little_o_local
      p.varianceBound C K₀ x hK₀ hxbound
  refine ⟨remainder, hremainder, ?_⟩
  let ε := min (p.varianceBound ^ 2) (p.meanRadius ^ 4)
  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min (sq_pos_of_pos hvar) (pow_pos hmean 4)
  filter_upwards [hxbound,
    Filter.eventually_ge_atTop (total_source_cost_local p),
    Filter.eventually_gt_atTop (K₀ / ε)] with B hxb hBcover hBlarge
  have hBpos : 0 < B := by
    have hquot : 0 < K₀ / ε := div_pos hK₀ hε
    exact lt_trans hquot hBlarge
  have hKdiv : K₀ / B < ε := by
    apply (div_lt_iff₀ hBpos).2
    have := (div_lt_iff₀ hε).mp hBlarge
    nlinarith
  have hxε : x B < ε := lt_of_le_of_lt hxb.2 hKdiv
  let s := Real.sqrt (x B)
  let ρ := Real.sqrt s
  have hs : 0 < s := Real.sqrt_pos.2 hxb.1
  have hρ : 0 < ρ := Real.sqrt_pos.2 hs
  have hs2 : s ^ 2 = x B := Real.sq_sqrt (le_of_lt hxb.1)
  have hρ2 : ρ ^ 2 = s := Real.sq_sqrt (le_of_lt hs)
  have hsvar : s < p.varianceBound := by
    have hxvar : x B < p.varianceBound ^ 2 :=
      lt_of_lt_of_le hxε (min_le_left _ _)
    nlinarith
  have hρmean : ρ ≤ p.meanRadius := by
    have hxmean : x B < p.meanRadius ^ 4 :=
      lt_of_lt_of_le hxε (min_le_right _ _)
    have hsmean : s < p.meanRadius ^ 2 := by
      nlinarith [sq_nonneg (p.meanRadius ^ 2 - s)]
    nlinarith
  have hρvar : ρ ^ 2 < p.varianceBound := by
    rw [hρ2]
    exact hsvar
  have hopt := hplans B hBpos
  have hprofile := population_minimax_profile_lower_local p plans B
    hBpos hBcover hopt hvar ρ hρ hρvar hρmean
  dsimp only at hprofile
  have hid := asymptotic_information_profile_identity_local
    p.varianceBound C (x B) hxb.1 hsvar
  rw [population_leading_risk_normalized_harmonic_local
    p plans B hBcover hopt]
  dsimp only [remainder]
  change p.varianceBound * x B +
      (asymptotic_information_lower_local p.varianceBound C (x B) -
        p.varianceBound * x B) ≤ population_minimax_risk p B
  rw [show p.varianceBound * x B +
      (asymptotic_information_lower_local p.varianceBound C (x B) -
        p.varianceBound * x B) =
      asymptotic_information_lower_local p.varianceBound C (x B) by ring]
  rw [hid]
  simpa [x, C, s, ρ] using hprofile

@[blueprint "lem:population-minimax-uniform-post-stratified-risk-upper-local"
  (statement := /-- Let $K$ and $M$ be positive integers, let $p$ be a biased-source mean-estimation problem, and let $n_T\colon\mathbb R\to\mathbb N^M$ be target-effective-sample-size optimal at every positive budget. There is a constant $A\in\mathbb R$ such that, for all sufficiently large $B$ and every $P\in\mathcal P_p(R,\sigma^2)$,
  \[
  \operatorname{Risk}_{\mathrm{PM}}((n_T(B),\widehat\theta_{\mathrm{PS}}),P)
  \le L_{\mathrm{PM}}(n_T(B),B)+\frac{A}{B^2}.
  \] -/)
  (proof := /-- The target normalization in \cref{lem:post-stratified-pmf-real-mass-sum-local} supplies a positive target coordinate, and source coverage supplies a source with positive mass there. The one-round comparison constants are positive by \cref{lem:post-stratified-total-source-cost-positive-local,lem:post-stratified-uniform-source-plan-support-local,lem:post-stratified-plan-harmonic-positive-local}. The harmonic estimate in \cref{lem:post-stratified-optimal-harmonic-eventual-bound-local} is uniform in the conditional model. For each positive target coordinate, \cref{lem:post-stratified-expected-group-count-positive-local} and the harmonic estimate bound its inverse expected count by a constant multiple of $B^{-1}$. Hence the explicit correction in \cref{lem:post-stratified-finite-plan-moment-upper-local} is at most $A_2/B^2$, uniformly over all bounded conditional models. Finally, \cref{lem:post-stratified-optimal-plan-cost-gap-local,lem:post-stratified-leading-risk-harmonic-local} bound the difference between the harmonic leading term and the budget-normalized population leading risk by another constant multiple of $B^{-2}$. Adding the two bounds gives a single constant $A$ independent of $P$. -/)
  (title := /-- Uniform second-order post-stratified risk bound -/)
  (latexEnv := "lemma")]
lemma population_minimax_uniform_post_stratified_risk_upper_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (plans : ℝ → sampling_plan M)
    (hplans : ∀ B, 0 < B → optimal_sampling_plan p
      (fun z => pmf_real_mass p.targetGroup z) B (plans B)) :
    ∃ A : ℝ, ∀ᶠ B in Filter.atTop, ∀ P,
      bounded_conditional_mean_class p P →
        population_mean_risk p (plans B)
            (post_stratified_estimator p.targetGroup) P ≤
          population_leading_risk p (plans B) B + A / B ^ 2 := by
  let q : Fin K → ℝ := fun z => pmf_real_mass p.targetGroup z
  let C := post_stratified_total_source_cost_local p
  let H₁ := post_stratified_plan_harmonic_local p
    (post_stratified_uniform_source_plan_local 1) q
  let KH := 2 * C * H₁
  have hC : 0 < C := post_stratified_total_source_cost_positive_local p
  have hH₁ : 0 < H₁ :=
    post_stratified_plan_harmonic_positive_local p
      (post_stratified_uniform_source_plan_local 1) p.targetGroup
      (by
        unfold plan_total_samples post_stratified_uniform_source_plan_local
        simp [NeZero.ne M])
      (post_stratified_uniform_source_plan_support_local p _ 1 Nat.zero_lt_one)
  have hKH : 0 < KH := by
    dsimp only [KH]
    positivity
  have hqsum := post_stratified_pmf_real_mass_sum_local p.targetGroup
  have hqexists : ∃ z, 0 < q z := by
    by_contra h
    push Not at h
    have hz : ∀ z, q z = 0 := fun z =>
      le_antisymm (h z) ENNReal.toReal_nonneg
    have : (∑ z, q z) = 0 := Finset.sum_eq_zero fun z _ => hz z
    dsimp only [q] at this
    linarith
  rcases hqexists with ⟨z₀, hz₀⟩
  rcases p.source_covers z₀ with ⟨m₀, hm₀⟩
  let A₂ : ℝ := ∑ z, if q z = 0 then 0 else
    (3 * p.varianceBound * (q z) ^ 2 + 2 * p.meanRadius ^ 2 * q z) *
      KH ^ 2 / (q z) ^ 4
  let A : ℝ := p.varianceBound * KH * p.cost m₀ + A₂
  refine ⟨A, ?_⟩
  have hcontrol := post_stratified_optimal_harmonic_eventual_bound_local
    p plans hplans
  dsimp only [C, H₁, KH] at hcontrol
  filter_upwards [hcontrol,
    Filter.eventually_ge_atTop C,
    Filter.eventually_gt_atTop (0 : ℝ)] with B hB hBcover hBpos
  have hHbound : post_stratified_plan_harmonic_local p (plans B) q ≤ KH / B := by
    simpa [KH, C, H₁] using hB.2.2
  have hopt := hplans B hBpos
  have hcostle : plan_cost p.cost (plans B) ≤ B := hopt.1
  have hgapnonneg : 0 ≤ B - plan_cost p.cost (plans B) := sub_nonneg.2 hcostle
  have hgap : B - plan_cost p.cost (plans B) < p.cost m₀ :=
    post_stratified_optimal_plan_cost_gap_local p B (plans B)
      (by simpa [C] using hBcover)
      hopt z₀ hz₀ m₀ hm₀
  have hsecond : post_stratified_plan_second_order_local p (plans B) ≤ A₂ / B ^ 2 := by
    unfold post_stratified_plan_second_order_local
    dsimp only [A₂]
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro z hz
    by_cases hqz : q z = 0
    · simp [q, hqz]
    · have hqpos : 0 < q z :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hqz)
      have hlam : 0 < post_stratified_expected_group_count_local p (plans B) z :=
        post_stratified_expected_group_count_positive_local p (plans B) q
          hB.1 hB.2.1 z hqpos
      have htermle : q z ^ 2 /
          post_stratified_expected_group_count_local p (plans B) z ≤
          post_stratified_plan_harmonic_local p (plans B) q := by
        unfold post_stratified_plan_harmonic_local
        have hnonneg : ∀ j, 0 ≤ if q j = 0 then 0 else
            q j ^ 2 / post_stratified_expected_group_count_local p (plans B) j := by
          intro j
          by_cases hqj : q j = 0
          · rw [if_pos hqj]
          · rw [if_neg hqj]
            exact div_nonneg (sq_nonneg _) (by
              unfold post_stratified_expected_group_count_local
              exact Finset.sum_nonneg fun m _ =>
                mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)
        have hs := Finset.single_le_sum
          (fun j _ => hnonneg j) (Finset.mem_univ z)
        simpa [hqz] using hs
      have hcross : B * q z ^ 2 ≤ KH *
          post_stratified_expected_group_count_local p (plans B) z := by
        have := le_trans htermle hHbound
        field_simp [ne_of_gt hlam, ne_of_gt hBpos] at this
        nlinarith
      have hinv : 1 / post_stratified_expected_group_count_local p (plans B) z ≤
          KH / (q z ^ 2 * B) := by
        apply (div_le_div_iff₀ hlam (mul_pos (sq_pos_of_pos hqpos) hBpos)).2
        nlinarith
      have hinvnonneg : 0 ≤ 1 /
          post_stratified_expected_group_count_local p (plans B) z := by positivity
      have hinvright : 0 ≤ KH / (q z ^ 2 * B) := by positivity
      have hinvsq := mul_self_le_mul_self hinvnonneg hinv
      have hinvsq' : 1 /
          post_stratified_expected_group_count_local p (plans B) z ^ 2 ≤
          KH ^ 2 / (q z ^ 4 * B ^ 2) := by
        calc
          1 / post_stratified_expected_group_count_local p (plans B) z ^ 2 =
              (1 / post_stratified_expected_group_count_local p (plans B) z) ^ 2 := by ring
          _ ≤ (KH / (q z ^ 2 * B)) ^ 2 := by
            simpa [pow_two] using hinvsq
          _ = KH ^ 2 / (q z ^ 4 * B ^ 2) := by ring
      have hcoef : 0 ≤ 3 * p.varianceBound * q z ^ 2 +
          2 * p.meanRadius ^ 2 * q z := by
        exact add_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) p.varianceBound_nonneg) (sq_nonneg _))
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (le_of_lt hqpos))
      rw [if_neg hqz, if_neg hqz]
      calc
        (3 * p.varianceBound * pmf_real_mass p.targetGroup z ^ 2 +
            2 * p.meanRadius ^ 2 * pmf_real_mass p.targetGroup z) /
            post_stratified_expected_group_count_local p (plans B) z ^ 2 =
          (3 * p.varianceBound * q z ^ 2 + 2 * p.meanRadius ^ 2 * q z) *
            (1 / post_stratified_expected_group_count_local p (plans B) z ^ 2) := by
              dsimp only [q]
              ring
        _ ≤ (3 * p.varianceBound * q z ^ 2 + 2 * p.meanRadius ^ 2 * q z) *
            (KH ^ 2 / (q z ^ 4 * B ^ 2)) :=
          mul_le_mul_of_nonneg_left hinvsq' hcoef
        _ = (3 * p.varianceBound * q z ^ 2 + 2 * p.meanRadius ^ 2 * q z) *
            KH ^ 2 / q z ^ 4 / B ^ 2 := by ring
  have hHcost : p.varianceBound *
      post_stratified_plan_harmonic_local p (plans B) q ≤
      population_leading_risk p (plans B) B +
        (p.varianceBound * KH * p.cost m₀) / B ^ 2 := by
    rw [post_stratified_leading_risk_harmonic_local p (plans B) B hB.1]
    let H := post_stratified_plan_harmonic_local p (plans B) q
    let d := B - plan_cost p.cost (plans B)
    have hHnonneg : 0 ≤ H := by
      exact le_of_lt (post_stratified_plan_harmonic_positive_local p
        (plans B) p.targetGroup hB.1 hB.2.1)
    have hgaple : d ≤ p.cost m₀ := le_of_lt hgap
    have hprod : H * d ≤ (KH / B) * p.cost m₀ :=
      mul_le_mul hHbound hgaple hgapnonneg (div_nonneg (le_of_lt hKH) (le_of_lt hBpos))
    have hdiv : H * d / B ≤ (KH / B) * p.cost m₀ / B :=
      div_le_div_of_nonneg_right hprod (le_of_lt hBpos)
    have hscaled := mul_le_mul_of_nonneg_left hdiv p.varianceBound_nonneg
    have hid : H = plan_cost p.cost (plans B) / B * H + H * d / B := by
      dsimp only [d]
      field_simp [ne_of_gt hBpos]
      ring
    calc
      p.varianceBound * H = p.varianceBound *
          (plan_cost p.cost (plans B) / B * H + H * d / B) :=
        congrArg (fun x => p.varianceBound * x) hid
      _ = p.varianceBound * (plan_cost p.cost (plans B) / B) * H +
            p.varianceBound * (H * d / B) := by ring
      _ ≤ p.varianceBound * (plan_cost p.cost (plans B) / B) * H +
          p.varianceBound * ((KH / B) * p.cost m₀ / B) :=
        by
          simpa [add_comm, add_left_comm] using
            add_le_add_left hscaled
              (p.varianceBound * (plan_cost p.cost (plans B) / B) * H)
      _ = p.varianceBound * (plan_cost p.cost (plans B) / B) * H +
          p.varianceBound * KH * p.cost m₀ / B ^ 2 := by ring
  intro P hP
  have hfinite := post_stratified_finite_plan_moment_upper_local
    p (plans B) P hP hB.1 hB.2.1
  calc
    population_mean_risk p (plans B)
        (post_stratified_estimator p.targetGroup) P ≤
      p.varianceBound * post_stratified_plan_harmonic_local p (plans B) q +
        post_stratified_plan_second_order_local p (plans B) := hfinite
    _ ≤ (population_leading_risk p (plans B) B +
          (p.varianceBound * KH * p.cost m₀) / B ^ 2) + A₂ / B ^ 2 :=
      add_le_add hHcost hsecond
    _ = population_leading_risk p (plans B) B + A / B ^ 2 := by
      dsimp only [A]
      ring

@[blueprint "lem:population-minimax-effective-sample-upper-bound-local"
  (statement := /-- Let $K$ and $M$ be positive integers, let $p$ be a biased-source mean-estimation problem, and let $n_T\colon\mathbb R\to\mathbb N^M$ be target-effective-sample-size optimal at every positive budget. There exists $u\colon\mathbb R\to\mathbb R$ such that $u=o(B^{-1})$ as $B\to\infty$ and, for all sufficiently large $B$,
  \[
  \mathcal R^*_{\mathrm{PM}}(B,\mathcal P(R,\sigma^2))
  \le L_{\mathrm{PM}}(n_T(B),B)+u(B).
  \] -/)
  (proof := /-- By \cref{lem:population-minimax-uniform-post-stratified-risk-upper-local}, one constant $A$ bounds the post-stratified risk for every model by the population leading risk plus $A/B^2$ at all sufficiently large budgets. Replace $A$ by $|A|$; the remainder $u(B)=|A|/B^2$ is little-$o(B^{-1})$ by \cref{lem:post-stratified-inverse-square-little-o-local}. At a sufficiently large positive budget, use the selected plan and the post-stratified estimator, whose measurability is \cref{lem:post-stratified-estimator-measurable}. The uniform risk inequality bounds the supremum in \cref{def:population-worst-case-risk}. The candidate set in \cref{def:population-minimax-risk} is bounded below by zero because each member is a supremum of the nonnegative square integrals in \cref{def:population-mean-risk}. Therefore the defining infimum is at most this post-stratified candidate, which is at most the leading risk plus $u(B)$. -/)
  (title := /-- Population minimax upper bound at a target-optimal plan -/)
  (latexEnv := "lemma")]
lemma population_minimax_effective_sample_upper_bound_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (plans : ℝ → sampling_plan M)
    (hplans : ∀ B, 0 < B → optimal_sampling_plan p
      (fun z => pmf_real_mass p.targetGroup z) B (plans B)) :
    ∃ remainder : ℝ → ℝ,
      Asymptotics.IsLittleO Filter.atTop remainder inverse_budget_rate ∧
      ∀ᶠ B in Filter.atTop,
        population_minimax_risk p B ≤
          population_leading_risk p (plans B) B + remainder B := by
  obtain ⟨A, hA⟩ :=
    population_minimax_uniform_post_stratified_risk_upper_local p plans hplans
  refine ⟨fun B => |A| / B ^ 2,
    post_stratified_inverse_square_little_o_local |A|, ?_⟩
  filter_upwards [hA, Filter.eventually_gt_atTop (0 : ℝ)] with B hbound hBpos
  let estimator : sampled_dataset K M (plans B) → ℝ :=
    post_stratified_estimator p.targetGroup
  have hrisk : BddAbove {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
      s = population_mean_risk p (plans B) estimator P} := by
    refine ⟨population_leading_risk p (plans B) B + |A| / B ^ 2, ?_⟩
    intro s hs
    rcases hs with ⟨P, hP, rfl⟩
    calc
      population_mean_risk p (plans B) estimator P ≤
          population_leading_risk p (plans B) B + A / B ^ 2 := hbound P hP
      _ ≤ population_leading_risk p (plans B) B + |A| / B ^ 2 := by
        gcongr
        exact le_abs_self A
  have hleading : 0 ≤ population_leading_risk p (plans B) B := by
    have havg : 0 ≤ average_plan_cost p.cost (plans B) := by
      unfold average_plan_cost
      split_ifs
      · exact le_rfl
      · exact div_nonneg
          (by
            unfold plan_cost
            exact Finset.sum_nonneg fun m _ =>
              mul_nonneg (le_of_lt (p.cost_pos m)) (Nat.cast_nonneg _))
          (Nat.cast_nonneg _)
    have hdisc : 0 ≤ plan_discrepancy p (plans B)
        (fun z => pmf_real_mass p.targetGroup z) := by
      unfold plan_discrepancy
      apply Finset.sum_nonneg
      intro z hz
      split_ifs
      · exact le_rfl
      · apply div_nonneg (sq_nonneg _)
        unfold source_mixture_mass
        split_ifs
        · exact le_rfl
        · exact div_nonneg
            (Finset.sum_nonneg fun m _ =>
              mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)
            (Nat.cast_nonneg _)
    unfold population_leading_risk
    exact div_nonneg
      (mul_nonneg (mul_nonneg p.varianceBound_nonneg havg) hdisc)
      (le_of_lt hBpos)
  have hupper_nonneg :
      0 ≤ population_leading_risk p (plans B) B + |A| / B ^ 2 :=
    add_nonneg hleading (div_nonneg (abs_nonneg A) (sq_nonneg B))
  have hworst :
      population_worst_case_risk p (plans B) estimator hrisk ≤
        population_leading_risk p (plans B) B + |A| / B ^ 2 := by
    rw [population_worst_case_risk]
    apply Real.sSup_le
    · intro s hs
      rcases hs with ⟨P, hP, rfl⟩
      calc
        population_mean_risk p (plans B) estimator P ≤
            population_leading_risk p (plans B) B + A / B ^ 2 := hbound P hP
        _ ≤ population_leading_risk p (plans B) B + |A| / B ^ 2 := by
          gcongr
          exact le_abs_self A
    · exact hupper_nonneg
  let candidates : Set ℝ :=
    {r : ℝ | ∃ n : sampling_plan M, budget_feasible_plan p B n ∧
      ∃ estimate : sampled_dataset K M n → ℝ, Measurable estimate ∧
        ∃ hset : BddAbove {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
          s = population_mean_risk p n estimate P},
          r = population_worst_case_risk p n estimate hset}
  have hcandidates : BddBelow candidates := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨n, hn, estimate, hmeas, hset, rfl⟩
    rw [population_worst_case_risk]
    apply Real.sSup_nonneg
    intro s hs
    rcases hs with ⟨P, hP, rfl⟩
    rw [population_mean_risk]
    exact MeasureTheory.integral_nonneg (fun D => sq_nonneg _)
  have hcandidate :
      population_worst_case_risk p (plans B) estimator hrisk ∈ candidates := by
    exact ⟨plans B, (hplans B hBpos).1, estimator,
      post_stratified_estimator_measurable p.targetGroup (plans B),
      hrisk, rfl⟩
  rw [population_minimax_risk]
  change sInf candidates ≤ _
  exact le_trans (csInf_le hcandidates hcandidate) hworst

@[blueprint "lem:population-minimax-effective-sample-asymptotics"
  (statement := /-- Let $K$ and $M$ be positive integers, let $p$ be a biased-source mean-estimation problem with $K$ groups, $M$ sources, and mean radius $R>0$, and let $n_T\colon\mathbb R\to\mathbb N^M$ be a family such that, for every $B>0$, the plan $n_T(B)$ maximizes the effective sample size for the target mass $q_T$ among all integer plans of cost at most $B$. Then, as $B\to\infty$,
  \[
  \mathcal R^*_{\mathrm{PM}}(B,\mathcal P(R,\sigma^2))
  -\frac{\sigma^2\bar c(n_T(B))D(q_T,\bar q_{n_T(B)})}{B}
  =o(B^{-1}).
  \] -/)
  (proof := /-- By \cref{lem:population-minimax-effective-sample-lower-bound}, there is a function $\ell=o(B^{-1})$ such that, eventually, the population leading risk plus $\ell(B)$ is at most the population minimax risk. By \cref{lem:population-minimax-effective-sample-upper-bound-local}, there is a function $u=o(B^{-1})$ giving the reverse eventual inequality. Hence, if $d(B)$ denotes the minimax risk minus the leading risk, then eventually $\ell(B)\le d(B)\le u(B)$. For every $c>0$, the two little-$o$ estimates eventually give $|\ell(B)|\le c|B^{-1}|$ and $|u(B)|\le c|B^{-1}|$. The preceding squeeze implies $|d(B)|\le c|B^{-1}|$, which is precisely $d=o(B^{-1})$. -/)
  (title := /-- Population minimax effective-sample-size asymptotics -/)
  (latexEnv := "lemma")]
lemma population_minimax_effective_sample_asymptotics {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (hmean : 0 < p.meanRadius)
    (plans : ℝ → sampling_plan M)
    (hplans : ∀ B, 0 < B →
      optimal_sampling_plan p (fun z => pmf_real_mass p.targetGroup z) B (plans B)) :
    Asymptotics.IsLittleO Filter.atTop
      (fun B => population_minimax_risk p B - population_leading_risk p (plans B) B)
      inverse_budget_rate := by
  obtain ⟨lower, hlower_small, hlower⟩ :=
    population_minimax_effective_sample_lower_bound p hmean plans hplans
  obtain ⟨upper, hupper_small, hupper⟩ :=
    population_minimax_effective_sample_upper_bound_local p plans hplans
  rw [Asymptotics.isLittleO_iff] at hlower_small hupper_small ⊢
  intro c hc
  filter_upwards [hlower, hupper, hlower_small hc, hupper_small hc] with
      B hlower_bound hupper_bound hlower_norm hupper_norm
  simp only [Real.norm_eq_abs] at hlower_norm hupper_norm ⊢
  rw [abs_le]
  constructor
  · have hlower_neg := neg_le_of_abs_le hlower_norm
    linarith
  · have hupper_pos := le_of_abs_le hupper_norm
    linarith

@[blueprint "def:compact-quartic-prior-density-refinement"
  (statement := /-- For $a>0$, define the compact quartic density
  \[
  \pi_a(x)=\frac{15}{16a^5}(a^2-x^2)^2\mathbf 1_{(-a,a]}(x).
  \]
  The half-open interval is used only to make the density agree literally with an interval integral; its endpoint values do not affect the associated measure. -/)
  (title := /-- Compact quartic prior density -/)
  (latexEnv := "definition")]
noncomputable def compact_quartic_prior_density_refinement (a x : ℝ) : ℝ :=
  if x ∈ Set.Ioc (-a) a then
    (15 / (16 * a ^ 5)) * (a ^ 2 - x ^ 2) ^ 2
  else 0

@[blueprint "lem:compact-quartic-prior-density-integral-refinement"
  (statement := /-- If $a>0$, then the compact quartic density $\pi_a$ is integrable and has integral one. -/)
  (proof := /-- On $(-a,a]$ the density is a polynomial. Its primitive is
  \[
  \frac{15}{16a^5}\left(a^4x-\frac{2a^2x^3}{3}+\frac{x^5}{5}\right).
  \]
  The fundamental theorem of calculus evaluates the integral from $-a$ to $a$ as one. Integrability follows from continuity of the polynomial on the compact interval. -/)
  (title := /-- Normalization of the compact quartic prior -/)
  (latexEnv := "lemma")]
lemma compact_quartic_prior_density_integral_refinement
    (a : ℝ) (ha : 0 < a) :
    Integrable (compact_quartic_prior_density_refinement a) ∧
      (∫ x, compact_quartic_prior_density_refinement a x) = 1 := by
  letI : AddCommGroup ℝ := Real.normedCommRing.toAddCommGroup
  letI : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
  let c : ℝ := 15 / (16 * a ^ 5)
  let f : ℝ → ℝ := fun x => c * (a ^ 2 - x ^ 2) ^ 2
  have hfcont : Continuous f := by
    fun_prop
  have hfintIcc : IntegrableOn f (Set.Icc (-a) a) :=
    hfcont.integrableOn_Icc
  have hfintIoc : IntegrableOn f (Set.Ioc (-a) a) := by
    rwa [← integrableOn_Icc_iff_integrableOn_Ioc]
  have hdensity :
      compact_quartic_prior_density_refinement a =
        Set.indicator (Set.Ioc (-a) a) f := by
    funext x
    by_cases hx : x ∈ Set.Ioc (-a) a
    · simp [compact_quartic_prior_density_refinement, f, c, hx]
    · simp [compact_quartic_prior_density_refinement, f, hx]
  have hint : Integrable (compact_quartic_prior_density_refinement a) := by
    rw [hdensity]
    exact hfintIoc.integrable_indicator measurableSet_Ioc
  refine ⟨hint, ?_⟩
  rw [hdensity, MeasureTheory.integral_indicator measurableSet_Ioc]
  rw [← intervalIntegral.integral_of_le (by linarith : -a ≤ a)]
  have hderiv : ∀ x, HasDerivAt
      (fun y : ℝ =>
        c * (a ^ 4 * y - 2 * a ^ 2 * y ^ 3 / 3 + y ^ 5 / 5))
      (f x) x := by
    intro x
    have hlin := (hasDerivAt_id x).const_mul (a ^ 4)
    have hcubic :=
      (((hasDerivAt_id x).pow 3).const_mul (2 * a ^ 2)).div_const 3
    have hquintic := ((hasDerivAt_id x).pow 5).div_const 5
    have hraw := (hlin.sub hcubic).add hquintic
    have hscaled := (hasDerivAt_const x c).mul hraw
    convert hscaled using 1
    · funext y
      simp [Function.id_def]
    · dsimp only [f, Function.id_def]
      rw [zero_mul, zero_add]
      norm_num only [Nat.cast_ofNat, Nat.reduceSub]
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -a) (b := a)
    (f := fun y : ℝ =>
      c * (a ^ 4 * y - 2 * a ^ 2 * y ^ 3 / 3 + y ^ 5 / 5))
    (f' := f) (fun x _ => hderiv x)
    (hfcont.intervalIntegrable (-a) a)]
  dsimp only [c]
  field_simp [ne_of_gt ha]
  ring

@[blueprint "lem:compact-quartic-prior-density-regularity-refinement"
  (statement := /-- For every $a>0$, the compact quartic density is nonnegative and measurable. -/)
  (proof := /-- On its defining interval the density is a positive constant times a square, because $a^5>0$; off that interval it is zero. Measurability follows by combining measurability of the interval with continuity of the polynomial. -/)
  (title := /-- Positivity and measurability of the compact quartic prior -/)
  (latexEnv := "lemma")]
lemma compact_quartic_prior_density_regularity_refinement
    (a : ℝ) (ha : 0 < a) :
    (∀ x, 0 ≤ compact_quartic_prior_density_refinement a x) ∧
      Measurable (compact_quartic_prior_density_refinement a) := by
  constructor
  · intro x
    unfold compact_quartic_prior_density_refinement
    split_ifs
    · exact mul_nonneg (by positivity) (sq_nonneg _)
    · exact le_rfl
  · unfold compact_quartic_prior_density_refinement
    apply Measurable.ite measurableSet_Ioc
    · fun_prop
    · exact measurable_const

@[blueprint "def:compact-quartic-prior-measure-refinement"
  (statement := /-- The compact quartic prior measure is Lebesgue measure with density $\pi_a$. -/)
  (title := /-- Compact quartic prior measure -/)
  (latexEnv := "definition")]
noncomputable def compact_quartic_prior_measure_refinement (a : ℝ) : Measure ℝ :=
  volume.withDensity fun x =>
    ((compact_quartic_prior_density_refinement a x).toNNReal : ENNReal)

@[blueprint "lem:compact-quartic-prior-probability-refinement"
  (statement := /-- If $a>0$, then the compact quartic prior measure has total mass one. -/)
  (proof := /-- Express the total mass of the density measure as the Lebesgue integral of its nonnegative density. The normalization is \\cref{lem:compact-quartic-prior-density-integral-refinement}, and nonnegativity is \\cref{lem:compact-quartic-prior-density-regularity-refinement}. -/)
  (title := /-- Probability normalization of the compact quartic prior -/)
  (latexEnv := "lemma")]
lemma compact_quartic_prior_probability_refinement
    (a : ℝ) (ha : 0 < a) :
    IsProbabilityMeasure (compact_quartic_prior_measure_refinement a) := by
  let f := compact_quartic_prior_density_refinement a
  have hf := compact_quartic_prior_density_integral_refinement a ha
  have hreg := compact_quartic_prior_density_regularity_refinement a ha
  constructor
  rw [compact_quartic_prior_measure_refinement,
    MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  have hcoe : ∀ x, ((f x).toNNReal : ENNReal) = ENNReal.ofReal (f x) := by
    intro x
    rw [Real.toNNReal_of_nonneg (hreg.1 x),
      ENNReal.ofReal_eq_coe_nnreal (hreg.1 x)]
  change (∫⁻ x, ((f x).toNNReal : ENNReal)) = 1
  simp_rw [hcoe]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    hf.1 (Filter.Eventually.of_forall hreg.1)]
  rw [hf.2]
  norm_num

@[blueprint "def:compact-quartic-prior-score-refinement"
  (statement := /-- On the interior of its support, the score of the compact quartic prior is
  $s_a(x)=-4x/(a^2-x^2)$; define it to be zero off the interior. -/)
  (title := /-- Score of the compact quartic prior -/)
  (latexEnv := "definition")]
noncomputable def compact_quartic_prior_score_refinement (a x : ℝ) : ℝ :=
  if x ∈ Set.Ioo (-a) a then -4 * x / (a ^ 2 - x ^ 2) else 0

@[blueprint "lem:compact-quartic-prior-information-refinement"
  (statement := /-- If $a>0$, the second moment of the compact quartic prior score is $10/a^2$. -/)
  (proof := /-- Multiply the squared score by the prior density. On $(-a,a)$ the factors $(a^2-x^2)^2$ cancel, leaving $15x^2/a^5$. Integrating this quadratic over $(-a,a)$ gives $10/a^2$; the endpoints and the complement contribute zero. The density-measure integral formula uses \\cref{lem:compact-quartic-prior-density-regularity-refinement}. -/)
  (title := /-- Information of the compact quartic prior -/)
  (latexEnv := "lemma")]
lemma compact_quartic_prior_information_refinement
    (a : ℝ) (ha : 0 < a) :
    (∫ x, (compact_quartic_prior_score_refinement a x) ^ 2
        ∂(compact_quartic_prior_measure_refinement a)) = 10 / a ^ 2 := by
  let d := compact_quartic_prior_density_refinement a
  let q : ℝ → NNReal := fun x => (d x).toNNReal
  have hreg := compact_quartic_prior_density_regularity_refinement a ha
  have hqmeas : Measurable q := by
    exact continuous_real_toNNReal.measurable.comp hreg.2
  have hsmeas : Measurable (compact_quartic_prior_score_refinement a) := by
    unfold compact_quartic_prior_score_refinement
    apply Measurable.ite measurableSet_Ioo
    · fun_prop
    · exact measurable_const
  let g : ℝ → ℝ := fun x =>
    d x * (compact_quartic_prior_score_refinement a x) ^ 2
  have hpoint :
      g =
        Set.indicator (Set.Ioo (-a) a)
          (fun x => (15 / (a ^ 5)) * x ^ 2) := by
    funext x
    by_cases hx : x ∈ Set.Ioo (-a) a
    · rcases hx with ⟨hxleft, hxright⟩
      have hxmem : x ∈ Set.Ioo (-a) a := ⟨hxleft, hxright⟩
      have hxIoc : x ∈ Set.Ioc (-a) a :=
        ⟨hxleft, le_of_lt hxright⟩
      have hxpos : 0 < a ^ 2 - x ^ 2 := by
        nlinarith
      simp only [g, d, compact_quartic_prior_density_refinement,
        compact_quartic_prior_score_refinement, hxmem, hxIoc,
        Set.indicator_of_mem, if_true]
      field_simp [ne_of_gt ha, ne_of_gt hxpos]
      ring
    · have hs0 : compact_quartic_prior_score_refinement a x = 0 := by
        rw [compact_quartic_prior_score_refinement]
        exact if_neg hx
      simp [g, hs0, hx]
  have hgint : Integrable g := by
    rw [hpoint]
    have hpIcc : IntegrableOn
        (fun x : ℝ => (15 / (a ^ 5)) * x ^ 2) (Set.Icc (-a) a) :=
      (by fun_prop : Continuous
        (fun x : ℝ => (15 / (a ^ 5)) * x ^ 2)).integrableOn_Icc
    have hpIoo : IntegrableOn
        (fun x : ℝ => (15 / (a ^ 5)) * x ^ 2) (Set.Ioo (-a) a) :=
      hpIcc.mono_set Set.Ioo_subset_Icc_self
    exact hpIoo.integrable_indicator measurableSet_Ioo
  have hgintegral : (∫ x, g x) = 10 / a ^ 2 := by
    rw [hpoint, MeasureTheory.integral_indicator measurableSet_Ioo,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le (by linarith : -a ≤ a)]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    field_simp [ne_of_gt ha]
    ring
  rw [compact_quartic_prior_measure_refinement,
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (hsmeas.pow_const 2).aestronglyMeasurable]
  change ENNReal.toReal
      (∫⁻ x, ENNReal.ofReal
        ((compact_quartic_prior_score_refinement a x) ^ 2)
          ∂volume.withDensity fun x => (q x : ENNReal)) = 10 / a ^ 2
  rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul
    volume hqmeas.coe_nnreal_ennreal
    ((hsmeas.pow_const 2).ennreal_ofReal)]
  have hlintegrand : ∀ x,
      ((q x : ENNReal) *
        ENNReal.ofReal ((compact_quartic_prior_score_refinement a x) ^ 2)) =
      ENNReal.ofReal (g x) := by
    intro x
    have hqd : (q x : ℝ) = d x :=
      Real.coe_toNNReal _ (hreg.1 x)
    rw [show (q x : ENNReal) = ENNReal.ofReal (d x) by
      rw [← hqd, ENNReal.ofReal_coe_nnreal]]
    rw [← ENNReal.ofReal_mul (hreg.1 x)]
  simp only [Pi.mul_apply]
  simp_rw [hlintegrand]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgint
    (Filter.Eventually.of_forall fun x =>
      mul_nonneg (hreg.1 x) (sq_nonneg _))]
  rw [hgintegral, ENNReal.toReal_ofReal]
  positivity

@[blueprint "def:compact-gaussian-location-model-refinement"
  (statement := /-- For a mean vector $\mu\in\mathbb R^K$ and a nonnegative variance $v$, assign to group $z$ the Gaussian probability law $\mathcal N(\mu_z,v)$. -/)
  (title := /-- Gaussian conditional location model -/)
  (latexEnv := "definition")]
noncomputable def compact_gaussian_location_model_refinement
    {K : ℕ} (μ : Fin K → ℝ) (v : NNReal) :
    conditional_outcome_model K := fun z =>
  ⟨ProbabilityTheory.gaussianReal (μ z) v, inferInstance⟩

@[blueprint "lem:compact-gaussian-location-model-in-class-refinement"
  (statement := /-- If $|\mu_z|\le R$ for every group and $v\le\sigma^2$, then the Gaussian location model with mean vector $\mu$ and variance $v$ belongs to $\mathcal P_p(R,\sigma^2)$. -/)
  (proof := /-- Gaussian laws have all finite moments, their means equal their location parameters, and their variances equal their variance parameters. Substitution into \\cref{def:bounded-conditional-mean-class} gives the result. -/)
  (title := /-- Membership of the Gaussian location submodel -/)
  (latexEnv := "lemma")]
lemma compact_gaussian_location_model_in_class_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (μ : Fin K → ℝ) (v : NNReal)
    (hμ : ∀ z, |μ z| ≤ p.meanRadius)
    (hv : (v : ℝ) ≤ p.varianceBound) :
    bounded_conditional_mean_class p
      (compact_gaussian_location_model_refinement μ v) := by
  intro z
  refine ⟨?_, ?_, ?_⟩
  · exact ProbabilityTheory.memLp_id_gaussianReal' 2 (by simp)
  · simpa [conditional_group_mean,
      compact_gaussian_location_model_refinement] using hμ z
  · simpa [compact_gaussian_location_model_refinement] using hv

@[blueprint "lem:integrated-score-information-lower-refinement"
  (statement := /-- Let $e$ and $S$ be real functions on a measure space. If $e^2$, $S^2$, and $eS$ are integrable, $\int eS=1$, $\int S^2\le I$, and $I>0$, then
  \[
  \frac1I\le\int e^2.
  \] -/)
  (proof := /-- The square $(e-S/I)^2$ has nonnegative integral. Expanding it and using $\int eS=1$ and $\int S^2\le I$ gives
  $0\le\int e^2-I^{-1}$, which is the claimed inequality. -/)
  (title := /-- Integrated score information inequality -/)
  (latexEnv := "lemma")]
lemma integrated_score_information_lower_refinement
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (e S : Ω → ℝ) (I : ℝ)
    (he2 : Integrable (fun x => (e x) ^ 2) μ)
    (hS2 : Integrable (fun x => (S x) ^ 2) μ)
    (heS : Integrable (fun x => e x * S x) μ)
    (hid : (∫ x, e x * S x ∂μ) = 1)
    (hinfo : (∫ x, (S x) ^ 2 ∂μ) ≤ I)
    (hI : 0 < I) :
    1 / I ≤ ∫ x, (e x) ^ 2 ∂μ := by
  have hform :
      (fun x => (e x - S x / I) ^ 2) =
        fun x => (e x) ^ 2 - (2 / I) * (e x * S x) +
          (1 / I ^ 2) * (S x) ^ 2 := by
    funext x
    field_simp [ne_of_gt hI]
    ring
  have hsquare : Integrable (fun x => (e x - S x / I) ^ 2) μ := by
    rw [hform]
    exact (he2.sub (heS.const_mul (2 / I))).add
      (hS2.const_mul (1 / I ^ 2))
  have hsquare_nonneg : 0 ≤ ∫ x, (e x - S x / I) ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hexpand :
      (∫ x, (e x - S x / I) ^ 2 ∂μ) =
        (∫ x, (e x) ^ 2 ∂μ) -
          (2 / I) * (∫ x, e x * S x ∂μ) +
          (1 / I ^ 2) * (∫ x, (S x) ^ 2 ∂μ) := by
    rw [hform]
    have hdecomp :
        (fun x => (e x) ^ 2 - (2 / I) * (e x * S x) +
          (1 / I ^ 2) * (S x) ^ 2) =
          ((fun y : Ω => (e y) ^ 2) -
            (fun y : Ω => (2 / I) * (e y * S y))) +
              (fun y : Ω => (1 / I ^ 2) * (S y) ^ 2) := by
      funext x
      rfl
    rw [hdecomp]
    let A : Ω → ℝ :=
      (fun y => (e y) ^ 2) - fun y => (2 / I) * (e y * S y)
    let B : Ω → ℝ := fun y => (1 / I ^ 2) * (S y) ^ 2
    have hA : Integrable A μ := he2.sub (heS.const_mul (2 / I))
    have hB : Integrable B μ := hS2.const_mul (1 / I ^ 2)
    have hAint : MeasureTheory.integral μ A =
        (∫ x, (e x) ^ 2 ∂μ) - (2 / I) * (∫ x, e x * S x ∂μ) := by
      rw [show A = fun y => (e y) ^ 2 - (2 / I) * (e y * S y) by
        funext y
        rfl]
      rw [MeasureTheory.integral_sub he2 (heS.const_mul (2 / I)),
        MeasureTheory.integral_const_mul]
    have hBint : MeasureTheory.integral μ B =
        (1 / I ^ 2) * (∫ x, (S x) ^ 2 ∂μ) := by
      rw [show B = fun y => (1 / I ^ 2) * (S y) ^ 2 by
        funext y
        rfl]
      rw [MeasureTheory.integral_const_mul]
    change MeasureTheory.integral μ (A + B) = _
    calc
      MeasureTheory.integral μ (A + B) =
          MeasureTheory.integral μ A + MeasureTheory.integral μ B :=
        MeasureTheory.integral_add hA hB
      _ = _ := by
        rw [hAint, hBint]
  rw [hexpand, hid] at hsquare_nonneg
  have hscaled : (1 / I ^ 2) * (∫ x, (S x) ^ 2 ∂μ) ≤ 1 / I := by
    have hnonneg : 0 ≤ 1 / I ^ 2 := by positivity
    calc
      (1 / I ^ 2) * (∫ x, (S x) ^ 2 ∂μ) ≤
          (1 / I ^ 2) * I :=
        mul_le_mul_of_nonneg_left hinfo hnonneg
      _ = 1 / I := by field_simp [ne_of_gt hI]
  have htwo : 2 / I = 2 * (1 / I) := by ring
  rw [htwo] at hsquare_nonneg
  linarith

section

@[reducible, blueprint "def:compact-refinement-real-add-instance"
  (statement := /-- Within the Gaussian derivative refinement, use the additive-group structure projected from the normed ring structure on $\mathbb R$. -/)
  (title := /-- Local real additive structure for Gaussian differentiation -/)
  (latexEnv := "definition")]
noncomputable local instance compact_refinement_real_add_instance : AddCommGroup ℝ :=
  Real.normedCommRing.toAddCommGroup

attribute [local instance 2000] compact_refinement_real_add_instance

@[reducible, blueprint "def:compact-refinement-real-module-instance"
  (statement := /-- Within the Gaussian derivative refinement, use the scalar-module structure projected from the normed algebra structure on $\mathbb R$. -/)
  (title := /-- Local real module structure for Gaussian differentiation -/)
  (latexEnv := "definition")]
noncomputable local instance compact_refinement_real_module_instance : Module ℝ ℝ :=
  (NormedAlgebra.toNormedSpace ℝ).toModule

attribute [local instance 2000] compact_refinement_real_module_instance

@[blueprint "lem:gaussian-pdf-mean-score-derivative-refinement"
  (statement := /-- For $v>0$, differentiating the density of $\mathcal N(\mu,v)$ with respect to its mean gives
  \[
  \frac{\partial}{\partial\mu}\varphi_{\mu,v}(y)
  =\varphi_{\mu,v}(y)\frac{y-\mu}{v}.
  \] -/)
  (proof := /-- Differentiate the explicit Gaussian density. The derivative of $-(y-\mu)^2/(2v)$ is $(y-\mu)/v$, and the exponential chain rule supplies the density factor. -/)
  (title := /-- Mean derivative of the Gaussian density -/)
  (latexEnv := "lemma")]
lemma gaussian_pdf_mean_score_derivative_refinement
    (v : NNReal) (hv : 0 < v) (μ y : ℝ) :
    HasDerivAt
      (fun t => ProbabilityTheory.gaussianPDFReal t v y)
      (ProbabilityTheory.gaussianPDFReal μ v y * ((y - μ) / (v : ℝ))) μ := by
  have hsub := (hasDerivAt_const μ y).sub (hasDerivAt_id μ)
  have hsq := hsub.pow 2
  have hneg := hsq.neg
  have hdiv := hneg.div_const (2 * (v : ℝ))
  have hexp := hdiv.exp
  have hconst : HasDerivAt
      (fun _ : ℝ => (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) 0 μ :=
    hasDerivAt_const μ _
  have hmul := hconst.mul hexp
  have hpow :
      ((fun x : ℝ => y) - id) ^ 2 =
        fun x => (y - x) ^ 2 := by
    funext x
    rfl
  rw [hpow] at hmul
  simp only [Function.id_def, Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat,
    Nat.reduceSub, pow_one, one_mul, zero_sub, neg_neg] at hmul
  convert hmul using 1
  · funext t
    rfl
  · rw [ProbabilityTheory.gaussianPDFReal_def]
    simp only [Pi.neg_apply, zero_mul, zero_add]
    ring_nf

end

@[blueprint "lem:measurable-equiv-map-with-density-refinement"
  (statement := /-- If $e\colon X\to Y$ is a measurable equivalence and $f\colon X\to[0,\infty]$ is measurable, then transporting the measure with density $f$ through $e$ gives the transported base measure with density $f\circ e^{-1}$. -/)
  (proof := /-- Evaluate both measures on an arbitrary measurable set. The change-of-variables formula for lower integrals under the measurable equivalence identifies the integral over the set with the integral of $f$ over its inverse image. -/)
  (title := /-- Transport of a density through a measurable equivalence -/)
  (latexEnv := "lemma")]
lemma measurable_equiv_map_with_density_refinement
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (f : X → ENNReal)
    (hf : Measurable f) :
    (μ.withDensity f).map e =
      (μ.map e).withDensity (f ∘ e.symm) := by
  ext A hA
  rw [Measure.map_apply e.measurable hA,
    MeasureTheory.withDensity_apply _ (e.measurable hA),
    MeasureTheory.withDensity_apply _ hA,
    MeasureTheory.setLIntegral_map hA
      (hf.comp e.symm.measurable) e.measurable]
  simp only [Function.comp_apply, e.symm_apply_apply]

@[blueprint "lem:finite-pi-with-density-refinement"
  (statement := /-- For a finite family of sigma-finite measures $(\mu_i)_{i\in[r]}$ and measurable densities $f_i$, the product of the density measures is the product base measure with density $x\mapsto\prod_i f_i(x_i)$. -/)
  (proof := /-- Induct on the number of coordinates. The empty product is a Dirac mass with unit density. In the successor step, split off one coordinate by the canonical measurable equivalence, transport the density using \cref{lem:measurable-equiv-map-with-density-refinement}, apply the induction hypothesis to the remaining coordinates, and combine the two factors by the product-density formula. -/)
  (title := /-- Density of a finite product measure -/)
  (latexEnv := "lemma")]
lemma finite_pi_with_density_refinement
    {r : ℕ} {Ω : Fin r → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, Ω i → NNReal) (hf : ∀ i, Measurable (f i)) :
    Measure.pi (fun i => (μ i).withDensity fun x => (f i x : ENNReal)) =
      (Measure.pi μ).withDensity
        (fun x => ((∏ i, f i (x i) : NNReal) : ENNReal)) := by
  induction r with
  | zero =>
      rw [Measure.pi_of_empty
        (fun i : Fin 0 => (μ i).withDensity fun x => (f i x : ENNReal))
        (fun i => Fin.elim0 i),
        Measure.pi_of_empty μ (fun i => Fin.elim0 i)]
      simp
  | succ n ih =>
      let i : Fin (n + 1) := 0
      let e := MeasurableEquiv.piFinSuccAbove Ω i
      have hfull : Measurable (fun x : (j : Fin (n + 1)) → Ω j =>
          (∏ j, f j (x j) : NNReal)) :=
        Finset.measurable_prod _ fun j _ =>
          (hf j).comp (measurable_pi_apply j)
      apply e.measurableEmbedding.map_injective
      rw [(MeasureTheory.measurePreserving_piFinSuccAbove
        (fun j => (μ j).withDensity fun x => (f j x : ENNReal)) i).map_eq]
      rw [measurable_equiv_map_with_density_refinement e (Measure.pi μ)
        _ hfull.coe_nnreal_ennreal]
      rw [(MeasureTheory.measurePreserving_piFinSuccAbove μ i).map_eq]
      rw [ih (fun j => μ (i.succAbove j))
        (fun j => f (i.succAbove j)) (fun j => hf (i.succAbove j))]
      have htail : Measurable (fun x : (j : Fin n) → Ω (i.succAbove j) =>
          (∏ j, f (i.succAbove j) (x j) : NNReal)) :=
        Finset.measurable_prod _ fun j _ =>
          (hf (i.succAbove j)).comp (measurable_pi_apply j)
      rw [MeasureTheory.prod_withDensity (hf i).coe_nnreal_ennreal
        htail.coe_nnreal_ennreal]
      congr 1
      funext x
      simp [e, i.prod_univ_succAbove]

@[blueprint "def:compact-gaussian-observation-density-refinement"
  (statement := /-- For a mean vector $\mu$ and variance $v$, the nonnegative density assigned to an observed pair $(z,y)$ is the Gaussian density with mean $\mu_z$ and variance $v$. -/)
  (title := /-- Gaussian density of a labelled observation -/)
  (latexEnv := "definition")]
noncomputable def compact_gaussian_observation_density_refinement
    {K : ℕ} (μ : Fin K → ℝ) (v : NNReal) (x : Fin K × ℝ) : NNReal :=
  (ProbabilityTheory.gaussianPDFReal (μ x.1) v x.2).toNNReal

@[blueprint "def:compact-gaussian-source-base-refinement"
  (statement := /-- The fixed base measure for observations from source $m$ is the finite sum, over groups $z$, of source mass $q_{S,m}(z)$ times Lebesgue measure embedded on the fibre $\{z\}\times\mathbb R$. -/)
  (title := /-- Fixed base measure for a labelled source observation -/)
  (latexEnv := "definition")]
noncomputable def compact_gaussian_source_base_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (m : Fin M) :
    Measure (Fin K × ℝ) :=
  Measure.sum fun z => (p.sourceGroup m z).toNNReal •
    volume.map (Prod.mk z)

@[blueprint "def:compact-gaussian-source-base-sigma-finite-refinement"
  (statement := /-- Every fixed labelled-source base measure is sigma-finite. -/)
  (title := /-- Sigma-finiteness of the labelled-source base -/)
  (latexEnv := "definition")]
noncomputable instance compact_gaussian_source_base_sigma_finite_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (m : Fin M) :
    SigmaFinite (compact_gaussian_source_base_refinement p m) := by
  unfold compact_gaussian_source_base_refinement
  letI hsmul : ∀ z : Fin K,
      SigmaFinite ((p.sourceGroup m z).toNNReal •
        volume.map (Prod.mk z)) := fun z => by
    letI hmap : SigmaFinite (volume.map (Prod.mk z)) :=
      (show MeasurableEmbedding (Prod.mk z : ℝ → Fin K × ℝ) from
        measurableEmbedding_prodMk_left z).sigmaFinite_map
    exact MeasureTheory.SMul.sigmaFinite
      (μ := (volume : Measure ℝ).map (Prod.mk z))
      (p.sourceGroup m z).toNNReal
  exact MeasureTheory.sum.sigmaFinite _

@[blueprint "lem:compact-gaussian-fibre-density-refinement"
  (statement := /-- If $v>0$, weighting the embedded Lebesgue measure on the fibre $\{z\}\times\mathbb R$ by the labelled Gaussian density yields the embedded Gaussian law $\mathcal N(\mu_z,v)$. -/)
  (proof := /-- Evaluate both measures on a measurable set. The lower-integral change of variables through $y\mapsto(z,y)$ reduces the left side to the Gaussian density integral over the inverse image. Since the real Gaussian density is nonnegative, its nonnegative-real coercion is the extended Gaussian density defining the Gaussian measure. -/)
  (title := /-- Gaussian density on a fixed label fibre -/)
  (latexEnv := "lemma")]
lemma compact_gaussian_fibre_density_refinement
    {K : ℕ} (μ : Fin K → ℝ) (v : NNReal) (hv : 0 < v)
    (z : Fin K) :
    (volume.map (Prod.mk z)).withDensity
        (fun x =>
          (compact_gaussian_observation_density_refinement μ v x : ENNReal)) =
      (ProbabilityTheory.gaussianReal (μ z) v).map (Prod.mk z) := by
  have hv0 : v ≠ 0 := ne_of_gt hv
  rw [ProbabilityTheory.gaussianReal, if_neg hv0]
  ext A hA
  have hdens : Measurable (fun x : Fin K × ℝ =>
      (compact_gaussian_observation_density_refinement μ v x : ENNReal)) := by
    unfold compact_gaussian_observation_density_refinement
    fun_prop
  rw [MeasureTheory.withDensity_apply _ hA,
    MeasureTheory.setLIntegral_map hA hdens measurable_prodMk_left,
    Measure.map_apply measurable_prodMk_left hA,
    MeasureTheory.withDensity_apply _
      (measurable_prodMk_left hA)]
  apply MeasureTheory.setLIntegral_congr_fun
    (measurable_prodMk_left hA)
  intro y hy
  unfold compact_gaussian_observation_density_refinement
  change ((ProbabilityTheory.gaussianPDFReal (μ z) v y).toNNReal : ENNReal) =
    ProbabilityTheory.gaussianPDF (μ z) v y
  rw [ProbabilityTheory.gaussianPDF_def]
  change ((ProbabilityTheory.gaussianPDFReal (μ z) v y).toNNReal : ENNReal) =
    ENNReal.ofReal (ProbabilityTheory.gaussianPDFReal (μ z) v y)
  have hnonneg := ProbabilityTheory.gaussianPDFReal_nonneg (μ z) v y
  rw [Real.toNNReal_of_nonneg hnonneg,
    ← ENNReal.ofReal_eq_coe_nnreal hnonneg]

@[blueprint "lem:compact-gaussian-source-density-refinement"
  (statement := /-- If $v>0$, the source-$m$ observation law under the Gaussian location model has density $(z,y)\mapsto\varphi_{\mu_z,v}(y)$ with respect to its fixed labelled-source base measure. -/)
  (proof := /-- Expand the source law as the finite group mixture by \cref{lem:source-observation-law-mixture-local}. Distribute the density construction over the finite sum and over each scalar multiple. On every group fibre, identify the density measure by \cref{lem:compact-gaussian-fibre-density-refinement}; the resulting finite mixture is exactly the source observation law. -/)
  (title := /-- Fixed-base density of a Gaussian source observation -/)
  (latexEnv := "lemma")]
lemma compact_gaussian_source_density_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (μ : Fin K → ℝ)
    (v : NNReal) (hv : 0 < v) (m : Fin M) :
    source_observation_law p
        (compact_gaussian_location_model_refinement μ v) m =
      (compact_gaussian_source_base_refinement p m).withDensity
        (fun x =>
          (compact_gaussian_observation_density_refinement μ v x : ENNReal)) := by
  rw [source_observation_law_mixture_local]
  unfold compact_gaussian_location_model_refinement
  unfold compact_gaussian_source_base_refinement
  rw [MeasureTheory.Measure.sum_fintype]
  induction (Finset.univ : Finset (Fin K)) using Finset.induction_on with
  | empty => simp
  | @insert z s hz ih =>
      simp only [Finset.sum_insert, hz, not_false_eq_true]
      rw [MeasureTheory.withDensity_add_measure]
      have hscaled :
          (((p.sourceGroup m z).toNNReal •
              volume.map (Prod.mk z)).withDensity
            (fun x =>
              (compact_gaussian_observation_density_refinement μ v x : ENNReal))) =
            (p.sourceGroup m z).toNNReal •
              ((volume.map (Prod.mk z)).withDensity
                (fun x =>
                  (compact_gaussian_observation_density_refinement μ v x : ENNReal))) := by
        ext A hA
        simp [MeasureTheory.withDensity_apply, hA]
      rw [hscaled, compact_gaussian_fibre_density_refinement μ v hv z, ih]
      rfl

@[blueprint "def:compact-gaussian-sampling-base-refinement"
  (statement := /-- The fixed base measure for a sampling plan is the iterated finite product of the labelled-source base measures over observations within sources and then over sources. -/)
  (title := /-- Fixed base measure for a sampled dataset -/)
  (latexEnv := "definition")]
noncomputable def compact_gaussian_sampling_base_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M) :
    Measure (sampled_dataset K M n) :=
  Measure.pi fun m =>
    Measure.pi fun _i : Fin (n m) => compact_gaussian_source_base_refinement p m

@[blueprint "def:compact-gaussian-sampling-density-refinement"
  (statement := /-- The Gaussian likelihood of a dataset relative to the fixed sampling base is the product of its labelled Gaussian observation densities. -/)
  (title := /-- Gaussian likelihood of a sampled dataset -/)
  (latexEnv := "definition")]
noncomputable def compact_gaussian_sampling_density_refinement
    {K M : ℕ} {n : sampling_plan M}
    (μ : Fin K → ℝ) (v : NNReal) (D : sampled_dataset K M n) : NNReal :=
  ∏ m, ∏ i, compact_gaussian_observation_density_refinement μ v (D m i)

@[blueprint "lem:compact-gaussian-sampling-density-measure-refinement"
  (statement := /-- If $v>0$, the full heterogeneous sampling law of the Gaussian location model is the fixed sampling base measure weighted by the product Gaussian likelihood. -/)
  (proof := /-- Apply \cref{lem:compact-gaussian-source-density-refinement} to every observation coordinate. Within each source, combine the coordinate densities with \cref{lem:finite-pi-with-density-refinement}. Apply the same finite-product density identity once more across sources; the two nested products are precisely the dataset likelihood. -/)
  (title := /-- Fixed-base likelihood of the Gaussian sampling law -/)
  (latexEnv := "lemma")]
lemma compact_gaussian_sampling_density_measure_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (μ : Fin K → ℝ) (v : NNReal) (hv : 0 < v) :
    sampling_law p n (compact_gaussian_location_model_refinement μ v) =
      (compact_gaussian_sampling_base_refinement p n).withDensity
        (fun D =>
          (compact_gaussian_sampling_density_refinement μ v D : ENNReal)) := by
  have hobs : Measurable
      (compact_gaussian_observation_density_refinement μ v) := by
    unfold compact_gaussian_observation_density_refinement
    fun_prop
  have hinner : ∀ m : Fin M,
      Measure.pi (fun _i : Fin (n m) =>
          source_observation_law p
            (compact_gaussian_location_model_refinement μ v) m) =
        (Measure.pi fun _i : Fin (n m) =>
          compact_gaussian_source_base_refinement p m).withDensity
            (fun d => ((∏ i,
              compact_gaussian_observation_density_refinement μ v (d i) : NNReal) :
                ENNReal)) := by
    intro m
    simp_rw [compact_gaussian_source_density_refinement p μ v hv m]
    exact finite_pi_with_density_refinement
      (fun _i : Fin (n m) => compact_gaussian_source_base_refinement p m)
      (fun _i => compact_gaussian_observation_density_refinement μ v)
      (fun _i => hobs)
  have houterMeas : ∀ m : Fin M, Measurable
      (fun d : Fin (n m) → Fin K × ℝ =>
        (∏ i, compact_gaussian_observation_density_refinement μ v (d i) : NNReal)) := by
    intro m
    exact Finset.measurable_prod _ fun i _ =>
      hobs.comp (measurable_pi_apply i)
  rw [sampling_law]
  simp_rw [hinner]
  rw [finite_pi_with_density_refinement
    (fun m => Measure.pi fun _i : Fin (n m) =>
      compact_gaussian_source_base_refinement p m)
    (fun m d => ∏ i,
      compact_gaussian_observation_density_refinement μ v (d i))
    houterMeas]
  rfl

@[blueprint "def:compact-gaussian-sampling-density-real-refinement"
  (statement := /-- The real-valued Gaussian likelihood of a dataset is the product of the real Gaussian densities of all its labelled observations. -/)
  (title := /-- Real Gaussian likelihood of a sampled dataset -/)
  (latexEnv := "definition")]
noncomputable def compact_gaussian_sampling_density_real_refinement
    {K M : ℕ} {n : sampling_plan M}
    (μ : Fin K → ℝ) (v : NNReal) (D : sampled_dataset K M n) : ℝ :=
  ∏ m, ∏ i, ProbabilityTheory.gaussianPDFReal (μ (D m i).1) v (D m i).2

@[blueprint "def:compact-gaussian-data-score-refinement"
  (statement := /-- The likelihood score in mean coordinate $z$ is the sum, over observations carrying label $z$, of $(Y-\mu_z)/v$. -/)
  (title := /-- Coordinate score of the Gaussian dataset likelihood -/)
  (latexEnv := "definition")]
noncomputable def compact_gaussian_data_score_refinement
    {K M : ℕ} {n : sampling_plan M}
    (μ : Fin K → ℝ) (v : NNReal) (D : sampled_dataset K M n)
    (z : Fin K) : ℝ :=
  ∑ m, ∑ i, if (D m i).1 = z then ((D m i).2 - μ z) / (v : ℝ) else 0

@[blueprint "lem:compact-gaussian-sampling-density-coe-refinement"
  (statement := /-- The real coercion of the nonnegative Gaussian sampling density equals the product of the real Gaussian densities. -/)
  (proof := /-- Every real Gaussian density is nonnegative, so coercing its nonnegative-real projection returns the original density. Coercion commutes with both finite products. -/)
  (title := /-- Real coercion of the Gaussian likelihood -/)
  (latexEnv := "lemma")]
lemma compact_gaussian_sampling_density_coe_refinement
    {K M : ℕ} {n : sampling_plan M}
    (μ : Fin K → ℝ) (v : NNReal) (D : sampled_dataset K M n) :
    (compact_gaussian_sampling_density_refinement μ v D : ℝ) =
      compact_gaussian_sampling_density_real_refinement μ v D := by
  unfold compact_gaussian_sampling_density_refinement
  unfold compact_gaussian_sampling_density_real_refinement
  simp_rw [NNReal.coe_prod]
  apply Finset.prod_congr rfl
  intro m hm
  apply Finset.prod_congr rfl
  intro i hi
  unfold compact_gaussian_observation_density_refinement
  exact Real.coe_toNNReal _
    (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)

@[blueprint "lem:compact-gaussian-sampling-score-derivative-refinement"
  (statement := /-- If $v>0$, differentiating the real dataset likelihood after varying only mean coordinate $z$ gives the likelihood times the coordinate data score. -/)
  (proof := /-- For an observation labelled $z$, use \cref{lem:gaussian-pdf-mean-score-derivative-refinement}; for every other label the factor is constant. Apply \cref{lem:finite-product-score-derivative-local} first to the observations within each source and then to the product over sources. The two resulting finite score sums combine into the dataset score. -/)
  (title := /-- Coordinate derivative of the Gaussian dataset likelihood -/)
  (latexEnv := "lemma")]
lemma compact_gaussian_sampling_score_derivative_refinement
    {K M : ℕ} {n : sampling_plan M}
    (μ : Fin K → ℝ) (v : NNReal) (hv : 0 < v)
    (D : sampled_dataset K M n) (z : Fin K) (t : ℝ) :
    HasDerivAt
      (fun s => compact_gaussian_sampling_density_real_refinement
        (Function.update μ z s) v D)
      (compact_gaussian_sampling_density_real_refinement
          (Function.update μ z t) v D *
        compact_gaussian_data_score_refinement
          (Function.update μ z t) v D z) t := by
  letI : AddCommGroup ℝ := Real.normedCommRing.toAddCommGroup
  letI : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
  have hfactor : ∀ m : Fin M, ∀ i : Fin (n m),
      HasDerivAt
        (fun s => ProbabilityTheory.gaussianPDFReal
          ((Function.update μ z s) (D m i).1) v (D m i).2)
        (ProbabilityTheory.gaussianPDFReal
            ((Function.update μ z t) (D m i).1) v (D m i).2 *
          (if (D m i).1 = z then
            ((D m i).2 - t) / (v : ℝ) else 0)) t := by
    intro m i
    by_cases hlabel : (D m i).1 = z
    · subst hlabel
      simpa using gaussian_pdf_mean_score_derivative_refinement
        v hv t (D m i).2
    · have hconst : HasDerivAt
          (fun _ : ℝ => ProbabilityTheory.gaussianPDFReal
            (μ (D m i).1) v (D m i).2) 0 t :=
        hasDerivAt_const t _
      simpa [hlabel, Function.update_of_ne (Ne.symm hlabel)] using hconst
  have hinner : ∀ m : Fin M, HasDerivAt
      (fun s => ∏ i, ProbabilityTheory.gaussianPDFReal
        ((Function.update μ z s) (D m i).1) v (D m i).2)
      ((∏ i, ProbabilityTheory.gaussianPDFReal
          ((Function.update μ z t) (D m i).1) v (D m i).2) *
        ∑ i, if (D m i).1 = z then
          ((D m i).2 - t) / (v : ℝ) else 0) t := by
    intro m
    have h := finite_product_score_derivative_local Finset.univ
        (fun s i => ProbabilityTheory.gaussianPDFReal
          ((Function.update μ z s) (D m i).1) v (D m i).2)
        (fun i => if (D m i).1 = z then
          ((D m i).2 - t) / (v : ℝ) else 0) t
        (fun i hi => hfactor m i)
    convert h using 1
    all_goals first | rfl | (funext s; simp only [Finset.prod_apply])
  have houter := finite_product_score_derivative_local Finset.univ
    (fun s m => ∏ i, ProbabilityTheory.gaussianPDFReal
      ((Function.update μ z s) (D m i).1) v (D m i).2)
    (fun m => ∑ i, if (D m i).1 = z then
      ((D m i).2 - t) / (v : ℝ) else 0) t
    (fun m hm => hinner m)
  convert houter using 1
  · funext s
    unfold compact_gaussian_sampling_density_real_refinement
    simp only [Finset.prod_apply]
  · simp only [compact_gaussian_sampling_density_real_refinement,
      compact_gaussian_data_score_refinement, Function.update_self]

@[blueprint "def:compact-quartic-prior-polynomial-refinement"
  (statement := /-- The quartic polynomial agreeing with the compact prior density on its support is $q_a(t)=15(a^2-t^2)^2/(16a^5)$. -/)
  (title := /-- Supporting quartic polynomial of the compact prior -/)
  (latexEnv := "definition")]
noncomputable def compact_quartic_prior_polynomial_refinement
    (a t : ℝ) : ℝ :=
  (15 / (16 * a ^ 5)) * (a ^ 2 - t ^ 2) ^ 2

@[blueprint "lem:compact-quartic-prior-polynomial-on-support-refinement"
  (statement := /-- On $[-a,a]$, the compact quartic prior density equals its supporting quartic polynomial. -/)
  (proof := /-- At every point strictly to the right of $-a$, the defining interval indicator is one. At the remaining endpoint $-a$, both the density and the quartic polynomial vanish. -/)
  (title := /-- Polynomial form of the compact prior on its support -/)
  (latexEnv := "lemma")]
lemma compact_quartic_prior_polynomial_on_support_refinement
    (a t : ℝ) (ht : t ∈ Set.Icc (-a) a) :
    compact_quartic_prior_density_refinement a t =
      compact_quartic_prior_polynomial_refinement a t := by
  rcases ht with ⟨htl, htr⟩
  by_cases hstrict : -a < t
  · simp [compact_quartic_prior_density_refinement,
      compact_quartic_prior_polynomial_refinement, hstrict, htr]
  · have htneg : t = -a := by linarith
    subst t
    simp [compact_quartic_prior_density_refinement,
      compact_quartic_prior_polynomial_refinement]

@[blueprint "lem:compact-quartic-prior-polynomial-derivative-refinement"
  (statement := /-- If $a>0$, then on $[-a,a]$ the derivative of the supporting quartic polynomial is the prior density times the compact prior score. -/)
  (proof := /-- Differentiate the quartic polynomial. In the open interval, cancel one factor $a^2-t^2$ against the score denominator and use \cref{lem:compact-quartic-prior-polynomial-on-support-refinement}. At either endpoint, the polynomial derivative and the density--score product both vanish. -/)
  (title := /-- Score derivative identity for the compact prior -/)
  (latexEnv := "lemma")]
lemma compact_quartic_prior_polynomial_derivative_refinement
    (a : ℝ) (ha : 0 < a) (t : ℝ) (ht : t ∈ Set.Icc (-a) a) :
    HasDerivAt (compact_quartic_prior_polynomial_refinement a)
      (compact_quartic_prior_density_refinement a t *
        compact_quartic_prior_score_refinement a t) t := by
  let c : ℝ := 15 / (16 * a ^ 5)
  have hbase := (hasDerivAt_const t (a ^ 2)).sub ((hasDerivAt_id t).pow 2)
  have hsquare := hbase.pow 2
  have hscaled := hsquare.const_mul c
  convert hscaled using 1 <;> try rfl
  case e'_9 =>
    by_cases hinter : t ∈ Set.Ioo (-a) a
    · have hpos : 0 < a ^ 2 - t ^ 2 := by
        rcases hinter with ⟨hl, hr⟩
        nlinarith
      rw [compact_quartic_prior_polynomial_on_support_refinement a t ht]
      simp only [compact_quartic_prior_score_refinement, hinter, if_true]
      dsimp only [c, compact_quartic_prior_polynomial_refinement]
      simp only [Function.id_def, Pi.sub_apply, Pi.pow_apply,
        Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul, zero_sub]
      field_simp [ne_of_gt ha, ne_of_gt hpos]
      ring
    · have hend : t = -a ∨ t = a := by
        rcases ht with ⟨hl, hr⟩
        rw [Set.mem_Ioo, not_and_or] at hinter
        rcases hinter with hleft | hright
        · exact Or.inl (le_antisymm (le_of_not_gt hleft) hl)
        · exact Or.inr (le_antisymm hr (le_of_not_gt hright))
      rcases hend with rfl | rfl <;>
        simp [c, compact_quartic_prior_density_refinement,
          compact_quartic_prior_score_refinement]

@[blueprint "lem:compact-gaussian-pointwise-score-integration-refinement"
  (statement := /-- Fix a dataset $D$, a coordinate $z$, and all other mean coordinates. For $a,v>0$, integrating the estimation error times the sum of the Gaussian likelihood score and compact-prior score against the likelihood and quartic prior density over $[-a,a]$ equals the corresponding likelihood mass integral. -/)
  (proof := /-- Let $L(t)$ be the Gaussian dataset likelihood after replacing coordinate $z$ by $t$, and let $q_a$ be the supporting quartic polynomial. The likelihood derivative is \cref{lem:compact-gaussian-sampling-score-derivative-refinement}; the prior derivative is \cref{lem:compact-quartic-prior-polynomial-derivative-refinement}. Apply the product rule to $(T-t)L(t)q_a(t)$ and integrate its derivative over $[-a,a]$. The boundary term vanishes because $q_a(\pm a)=0$. Substitute the two score derivative identities and use \cref{lem:compact-quartic-prior-polynomial-on-support-refinement} to obtain the stated equality. -/)
  (title := /-- Pointwise score integration by parts -/)
  (latexEnv := "lemma")]
lemma compact_gaussian_pointwise_score_integration_refinement
    {K M : ℕ} {n : sampling_plan M}
    (μ : Fin K → ℝ) (v : NNReal) (hv : 0 < v)
    (a : ℝ) (ha : 0 < a) (D : sampled_dataset K M n)
    (z : Fin K) (T : ℝ) :
    (∫ t in (-a)..a,
        (T - t) *
          (compact_gaussian_data_score_refinement
              (Function.update μ z t) v D z +
            compact_quartic_prior_score_refinement a t) *
          compact_gaussian_sampling_density_real_refinement
              (Function.update μ z t) v D *
          compact_quartic_prior_density_refinement a t) =
      ∫ t in (-a)..a,
        compact_gaussian_sampling_density_real_refinement
            (Function.update μ z t) v D *
          compact_quartic_prior_density_refinement a t := by
  let L : ℝ → ℝ := fun t =>
    compact_gaussian_sampling_density_real_refinement
      (Function.update μ z t) v D
  let S : ℝ → ℝ := fun t =>
    compact_gaussian_data_score_refinement (Function.update μ z t) v D z
  let q : ℝ → ℝ := compact_quartic_prior_polynomial_refinement a
  let c : ℝ := 15 / (16 * a ^ 5)
  let q' : ℝ → ℝ := fun t => c * (2 * (a ^ 2 - t ^ 2) * (-2 * t))
  let F : ℝ → ℝ := fun t => (T - t) * L t * q t
  let F' : ℝ → ℝ := fun t =>
    -L t * q t + (T - t) * (L t * S t * q t + L t * q' t)
  have hL : ∀ t, HasDerivAt L (L t * S t) t := by
    intro t
    exact compact_gaussian_sampling_score_derivative_refinement μ v hv D z t
  have hq : ∀ t, HasDerivAt q (q' t) t := by
    intro t
    dsimp only [q, q', c, compact_quartic_prior_polynomial_refinement]
    convert ((((hasDerivAt_const t (a ^ 2)).sub
      ((hasDerivAt_id t).pow 2)).pow 2).const_mul
        (15 / (16 * a ^ 5))) using 1 <;> try rfl
    case e'_9 =>
      simp only [Function.id_def, Pi.sub_apply, Pi.pow_apply,
        Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul, zero_sub]
      ring
  have hF : ∀ t, HasDerivAt F (F' t) t := by
    intro t
    have herr := (hasDerivAt_const t T).sub (hasDerivAt_id t)
    have hprod := (herr.mul (hL t)).mul (hq t)
    convert hprod using 1 <;> try rfl
    case e'_9 =>
      simp only [F', Function.id_def, Pi.sub_apply, Pi.mul_apply,
        zero_sub, one_mul]
      ring
  have hLcont : Continuous L := continuous_iff_continuousAt.2 fun t =>
    (hL t).continuousAt
  have hScont : Continuous S := by
    dsimp only [S]
    unfold compact_gaussian_data_score_refinement
    apply continuous_finset_sum
    intro m hm
    apply continuous_finset_sum
    intro i hi
    split_ifs <;> fun_prop
  have hqcont : Continuous q := by
    dsimp only [q]
    unfold compact_quartic_prior_polynomial_refinement
    fun_prop
  have hq'cont : Continuous q' := by
    dsimp only [q', c]
    fun_prop
  have hF'cont : Continuous F' := by
    dsimp only [F']
    exact (hLcont.neg.mul hqcont).add
      ((continuous_const.sub continuous_id).mul
        (((hLcont.mul hScont).mul hqcont).add (hLcont.mul hq'cont)))
  have hF'int : IntervalIntegrable F' volume (-a) a :=
    hF'cont.intervalIntegrable _ _
  have hzero : (∫ t in (-a)..a, F' t) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hF t) hF'int]
    simp [F, q, compact_quartic_prior_polynomial_refinement]
  have hqrel : ∀ t ∈ Set.Icc (-a) a,
      q' t = compact_quartic_prior_density_refinement a t *
        compact_quartic_prior_score_refinement a t := by
    intro t ht
    have hderiv := compact_quartic_prior_polynomial_derivative_refinement
      a ha t ht
    have hraw := hq t
    exact hraw.unique hderiv
  have hpoint : Set.EqOn
      (fun t =>
        (T - t) *
          (compact_gaussian_data_score_refinement
              (Function.update μ z t) v D z +
            compact_quartic_prior_score_refinement a t) *
          compact_gaussian_sampling_density_real_refinement
              (Function.update μ z t) v D *
          compact_quartic_prior_density_refinement a t)
      (fun t => F' t + L t * q t) (Set.Icc (-a) a) := by
    intro t ht
    change (T - t) *
        (S t + compact_quartic_prior_score_refinement a t) * L t *
          compact_quartic_prior_density_refinement a t =
      F' t + L t * q t
    have hdq := compact_quartic_prior_polynomial_on_support_refinement a t ht
    have hqscore : q' t = q t * compact_quartic_prior_score_refinement a t := by
      rw [hqrel t ht, hdq]
    rw [hdq]
    dsimp only [F']
    rw [hqscore]
    ring
  have hab : -a ≤ a := by linarith
  rw [intervalIntegral.integral_congr (by
    simpa [Set.uIcc_of_le hab] using hpoint)]
  change (∫ x in (-a)..a, F' x + L x * q x) = _
  have hLqint : IntervalIntegrable (fun x => L x * q x) volume (-a) a :=
    (hLcont.mul hqcont).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hF'int hLqint]
  rw [hzero, zero_add]
  apply intervalIntegral.integral_congr
  intro t ht
  change L t * q t = L t * compact_quartic_prior_density_refinement a t
  rw [compact_quartic_prior_polynomial_on_support_refinement a t (by
    simpa [Set.uIcc_of_le hab] using ht)]

@[blueprint "lem:compact-gaussian-source-integral-refinement"
  (statement := /-- Under a Gaussian location model, the integral of a measurable function of one labelled source observation is the finite source-group mixture of its fibrewise Gaussian integrals, provided every fibre function is integrable. -/)
  (proof := /-- Expand the source observation law by \cref{lem:source-observation-law-mixture-local}. Integrability is preserved by the fibre embedding and by the nonnegative source-mass scalar. Linearity in the finite sum and the pushforward change-of-variables formula then give the displayed mixture identity. -/)
  (title := /-- Fibrewise integration under a Gaussian source law -/)
  (latexEnv := "lemma")]
lemma compact_gaussian_source_integral_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (μ : Fin K → ℝ)
    (v : NNReal) (m : Fin M) (f : Fin K × ℝ → ℝ)
    (hfmeas : Measurable f)
    (hfint : ∀ j, Integrable (fun y => f (j, y))
      (ProbabilityTheory.gaussianReal (μ j) v)) :
    (∫ x, f x ∂source_observation_law p
        (compact_gaussian_location_model_refinement μ v) m) =
      ∑ j, pmf_real_mass (p.sourceGroup m) j *
        ∫ y, f (j, y) ∂ProbabilityTheory.gaussianReal (μ j) v := by
  rw [source_observation_law_mixture_local]
  change (∫ x, f x ∂∑ j, (p.sourceGroup m j).toNNReal •
      (ProbabilityTheory.gaussianReal (μ j) v).map (Prod.mk j)) = _
  rw [MeasureTheory.integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [MeasureTheory.integral_smul_nnreal_measure]
    rw [MeasureTheory.integral_map measurable_prodMk_left.aemeasurable
      hfmeas.aestronglyMeasurable]
    simp only [smul_eq_mul, NNReal.smul_def, pmf_real_mass]
    rw [ENNReal.coe_toNNReal_eq_toReal]
  · intro j hj
    exact ((MeasureTheory.integrable_map_measure
      hfmeas.aestronglyMeasurable measurable_prodMk_left.aemeasurable).2
        (hfint j)).smul_measure_nnreal

@[blueprint "def:compact-gaussian-observation-score-refinement"
  (statement := /-- The contribution of one labelled observation $(j,y)$ to mean-coordinate score $z$ is $(y-\mu_z)/v$ when $j=z$ and zero otherwise. -/)
  (title := /-- Coordinate score of one Gaussian observation -/)
  (latexEnv := "definition")]
noncomputable def compact_gaussian_observation_score_refinement
    {K : ℕ} (μ : Fin K → ℝ) (v : NNReal) (z : Fin K)
    (x : Fin K × ℝ) : ℝ :=
  if x.1 = z then (x.2 - μ z) / (v : ℝ) else 0

@[blueprint "lem:compact-gaussian-source-score-moments-refinement"
  (statement := /-- If $v>0$, the coordinate-$z$ score of one source-$m$ Gaussian observation is square-integrable, has mean zero, and has second moment $q_{S,m}(z)/v$. -/)
  (proof := /-- Expand the source law as the finite mixture from \cref{lem:source-observation-law-mixture-local} to prove square-integrability. Then apply \cref{lem:compact-gaussian-source-integral-refinement} to the score and its square. Every fibre except $z$ vanishes. On fibre $z$, the Gaussian mean identity centres the score, while the Gaussian variance identity and the variance-as-centred-square formula give second moment $1/v$. -/)
  (title := /-- Moments of one Gaussian source score -/)
  (latexEnv := "lemma")]
lemma compact_gaussian_source_score_moments_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (μ : Fin K → ℝ)
    (v : NNReal) (hv : 0 < v) (m : Fin M) (z : Fin K) :
    MeasureTheory.MemLp (compact_gaussian_observation_score_refinement μ v z) 2
        (source_observation_law p
          (compact_gaussian_location_model_refinement μ v) m) ∧
      (∫ x, compact_gaussian_observation_score_refinement μ v z x
          ∂source_observation_law p
            (compact_gaussian_location_model_refinement μ v) m) = 0 ∧
      (∫ x, (compact_gaussian_observation_score_refinement μ v z x) ^ 2
          ∂source_observation_law p
            (compact_gaussian_location_model_refinement μ v) m) =
        pmf_real_mass (p.sourceGroup m) z / (v : ℝ) := by
  have hvreal : (0 : ℝ) < v := by exact_mod_cast hv
  have hscoreMeas : Measurable
      (compact_gaussian_observation_score_refinement μ v z) := by
    unfold compact_gaussian_observation_score_refinement
    apply Measurable.ite
    · exact measurable_fst (MeasurableSet.singleton z)
    · fun_prop
    · exact measurable_const
  have hfiberMem : ∀ j, MeasureTheory.MemLp
      (fun y => compact_gaussian_observation_score_refinement μ v z (j, y)) 2
      (ProbabilityTheory.gaussianReal (μ j) v) := by
    intro j
    by_cases hj : j = z
    · subst j
      simp only [compact_gaussian_observation_score_refinement, if_true]
      have hdiff := (ProbabilityTheory.memLp_id_gaussianReal'
        (μ := μ z) (v := v) 2 (by simp)).sub
        (MeasureTheory.memLp_const
          (μ := ProbabilityTheory.gaussianReal (μ z) v) (μ z))
      simpa [id_eq, div_eq_mul_inv] using
        hdiff.mul_const ((v : ℝ)⁻¹)
    · simp [compact_gaussian_observation_score_refinement, hj]
  have hscoreSqInt : Integrable
      (fun x => (compact_gaussian_observation_score_refinement μ v z x) ^ 2)
      (source_observation_law p
        (compact_gaussian_location_model_refinement μ v) m) := by
    rw [source_observation_law_mixture_local]
    unfold compact_gaussian_location_model_refinement
    apply MeasureTheory.integrable_finsetSum_measure.2
    intro j hj
    have hcomp : Integrable
        (fun y => (compact_gaussian_observation_score_refinement μ v z (j, y)) ^ 2)
        (ProbabilityTheory.gaussianReal (μ j) v) :=
      (MeasureTheory.memLp_two_iff_integrable_sq
        ((hscoreMeas.comp measurable_prodMk_left).aestronglyMeasurable)).1
          (hfiberMem j)
    exact ((MeasureTheory.integrable_map_measure
      (hscoreMeas.pow_const 2).aestronglyMeasurable
      measurable_prodMk_left.aemeasurable).2 hcomp).smul_measure_nnreal
  have hmem : MeasureTheory.MemLp
      (compact_gaussian_observation_score_refinement μ v z) 2
      (source_observation_law p
        (compact_gaussian_location_model_refinement μ v) m) :=
    (MeasureTheory.memLp_two_iff_integrable_sq
      hscoreMeas.aestronglyMeasurable).2 hscoreSqInt
  refine ⟨hmem, ?_, ?_⟩
  · rw [compact_gaussian_source_integral_refinement p μ v m
      (compact_gaussian_observation_score_refinement μ v z)
      hscoreMeas (fun j => (hfiberMem j).integrable one_le_two)]
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hjz : j = z
    · subst j
      simp only [compact_gaussian_observation_score_refinement, if_true]
      rw [MeasureTheory.integral_div, MeasureTheory.integral_sub,
        ProbabilityTheory.integral_id_gaussianReal]
      · simp
      · exact (ProbabilityTheory.memLp_id_gaussianReal' 2 (by simp)).integrable
          one_le_two
      · exact MeasureTheory.integrable_const _
    · simp [compact_gaussian_observation_score_refinement, hjz]
  · rw [compact_gaussian_source_integral_refinement p μ v m
      (fun x => (compact_gaussian_observation_score_refinement μ v z x) ^ 2)
      (hscoreMeas.pow_const 2) (fun j =>
        (MeasureTheory.memLp_two_iff_integrable_sq
          ((hscoreMeas.comp measurable_prodMk_left).aestronglyMeasurable)).1
            (hfiberMem j))]
    rw [Finset.sum_eq_single z]
    · simp only [compact_gaussian_observation_score_refinement, if_true]
      have hvarint := ProbabilityTheory.variance_eq_integral
        (μ := ProbabilityTheory.gaussianReal (μ z) v) measurable_id.aemeasurable
      simp only [id_eq] at hvarint
      rw [ProbabilityTheory.integral_id_gaussianReal,
        ProbabilityTheory.variance_id_gaussianReal] at hvarint
      rw [show (fun y : ℝ => ((y - μ z) / (v : ℝ)) ^ 2) =
          fun y => (1 / (v : ℝ) ^ 2) * (y - μ z) ^ 2 by
        funext y
        ring]
      rw [MeasureTheory.integral_const_mul, ← hvarint]
      field_simp [ne_of_gt hvreal]
    · intro j hj hjz
      simp [compact_gaussian_observation_score_refinement, hjz]
    · intro hznot
      exact (hznot (Finset.mem_univ z)).elim

@[blueprint "lem:compact-gaussian-dataset-score-moments-refinement"
  (statement := /-- If $v>0$, the coordinate-$z$ Gaussian dataset score is square-integrable, has mean zero, and has second moment $\lambda_z(n)/v$. -/)
  (proof := /-- The mixture formula \cref{lem:source-observation-law-mixture-local}, together with the finite probability-mass normalization \cref{lem:finite-pmf-real-mass-sum-local}, shows that every source-observation factor is a probability measure. Write the dataset score as the sum of the one-observation scores from \cref{lem:compact-gaussian-source-score-moments-refinement}. Coordinate projections from each finite product are measure preserving, so the summands retain their $L^2$ bounds and zero means. Applying the variance formula for independent finite-product sums first within each source and then across sources gives $\sum_m n_mq_{S,m}(z)/v=\lambda_z(n)/v$. -/)
  (title := /-- Moments of the Gaussian dataset score -/)
  (latexEnv := "lemma")]
lemma compact_gaussian_dataset_score_moments_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (μ : Fin K → ℝ) (v : NNReal) (hv : 0 < v) (z : Fin K) :
    MeasureTheory.MemLp
        (fun D => compact_gaussian_data_score_refinement μ v D z) 2
        (sampling_law p n (compact_gaussian_location_model_refinement μ v)) ∧
      (∫ D, compact_gaussian_data_score_refinement μ v D z
          ∂sampling_law p n
            (compact_gaussian_location_model_refinement μ v)) = 0 ∧
      (∫ D, (compact_gaussian_data_score_refinement μ v D z) ^ 2
          ∂sampling_law p n
            (compact_gaussian_location_model_refinement μ v)) =
        plan_expected_group_count_local p n z / (v : ℝ) := by
  let ν : Fin M → Measure (Fin K × ℝ) := fun m =>
    source_observation_law p (compact_gaussian_location_model_refinement μ v) m
  let X (m : Fin M) (d : Fin (n m) → Fin K × ℝ) : ℝ :=
    ∑ i, compact_gaussian_observation_score_refinement μ v z (d i)
  letI hνprob : ∀ m, IsProbabilityMeasure (ν m) := fun m =>
    ⟨by
      dsimp only [ν]
      rw [source_observation_law_mixture_local]
      have hm : ∀ x : Fin K,
          (Measure.map (Prod.mk x)
            (compact_gaussian_location_model_refinement μ v x : Measure ℝ))
              Set.univ = 1 := by
        intro x
        rw [Measure.map_apply measurable_prodMk_left MeasurableSet.univ]
        simp
      rw [show (∑ x : Fin K, (p.sourceGroup m x).toNNReal •
          Measure.map (Prod.mk x)
            (compact_gaussian_location_model_refinement μ v x : Measure ℝ)) =
          ∑ x ∈ (Finset.univ : Finset (Fin K)),
            (p.sourceGroup m x).toNNReal •
              Measure.map (Prod.mk x)
                (compact_gaussian_location_model_refinement μ v x : Measure ℝ)
            by simp]
      rw [MeasureTheory.Measure.finsetSum_apply]
      simp only [Measure.smul_apply, hm, NNReal.smul_def, mul_one,
        ENNReal.smul_one, Finset.sum_filter, Finset.mem_univ, ↓reduceIte]
      norm_cast
      apply NNReal.eq
      push_cast
      simpa [pmf_real_mass] using
        finite_pmf_real_mass_sum_local (p.sourceGroup m)⟩
  have hsource : ∀ m,
      MeasureTheory.MemLp
          (compact_gaussian_observation_score_refinement μ v z) 2 (ν m) ∧
        (∫ x, compact_gaussian_observation_score_refinement μ v z x ∂ν m) = 0 ∧
        (∫ x, (compact_gaussian_observation_score_refinement μ v z x) ^ 2
            ∂ν m) =
          pmf_real_mass (p.sourceGroup m) z / (v : ℝ) := by
    intro m
    exact compact_gaussian_source_score_moments_refinement p μ v hv m z
  have hinnerMem : ∀ m, MeasureTheory.MemLp (X m) 2
      (Measure.pi fun _i : Fin (n m) => ν m) := by
    intro m
    have heach : ∀ i : Fin (n m), MeasureTheory.MemLp
        (fun d : Fin (n m) → Fin K × ℝ =>
          compact_gaussian_observation_score_refinement μ v z (d i)) 2
        (Measure.pi fun _i : Fin (n m) => ν m) := by
      intro i
      exact (hsource m).1.comp_measurePreserving
        (MeasureTheory.measurePreserving_eval (fun _i : Fin (n m) => ν m) i)
    simpa [X] using MeasureTheory.memLp_finsetSum Finset.univ
      (fun i hi => heach i)
  have hinnerMean : ∀ m,
      (∫ d, X m d ∂Measure.pi fun _i : Fin (n m) => ν m) = 0 := by
    intro m
    have heval : ∀ i : Fin (n m),
        (∫ d, compact_gaussian_observation_score_refinement μ v z (d i)
            ∂Measure.pi fun _i : Fin (n m) => ν m) = 0 := by
      intro i
      have hpres :=
        MeasureTheory.measurePreserving_eval (fun _i : Fin (n m) => ν m) i
      calc
        (∫ d, compact_gaussian_observation_score_refinement μ v z (d i)
            ∂Measure.pi fun _i : Fin (n m) => ν m) =
            ∫ x, compact_gaussian_observation_score_refinement μ v z x
              ∂Measure.map (fun d => d i)
                (Measure.pi fun _i : Fin (n m) => ν m) := by
          symm
          exact MeasureTheory.integral_map
            (measurable_pi_apply i).aemeasurable
            (hpres.map_eq.symm ▸ (hsource m).1.aestronglyMeasurable)
        _ = ∫ x, compact_gaussian_observation_score_refinement μ v z x
              ∂ν m := by rw [hpres.map_eq]
        _ = 0 := (hsource m).2.1
    calc
      (∫ d, X m d ∂Measure.pi fun _i : Fin (n m) => ν m) =
          ∑ i, ∫ d, compact_gaussian_observation_score_refinement μ v z (d i)
            ∂Measure.pi fun _i : Fin (n m) => ν m := by
        dsimp only [X]
        simpa only [Finset.sum_apply] using
          MeasureTheory.integral_finsetSum
            (μ := Measure.pi fun _i : Fin (n m) => ν m)
            (f := fun i d =>
              compact_gaussian_observation_score_refinement μ v z (d i))
            Finset.univ
            (fun i hi => ((hsource m).1.comp_measurePreserving
              (MeasureTheory.measurePreserving_eval
                (fun _i : Fin (n m) => ν m) i)).integrable one_le_two)
      _ = 0 := by simp [heval]
  have hinnerVar : ∀ m,
      ProbabilityTheory.variance (X m)
          (Measure.pi fun _i : Fin (n m) => ν m) =
        n m * (pmf_real_mass (p.sourceGroup m) z / (v : ℝ)) := by
    intro m
    have hfun : X m = ∑ _i : Fin (n m), fun d =>
        compact_gaussian_observation_score_refinement μ v z (d _i) := by
      funext d
      simp [X, Finset.sum_apply]
    rw [hfun, ProbabilityTheory.variance_sum_pi
      (μ := fun _i : Fin (n m) => ν m)
      (X := fun _i => compact_gaussian_observation_score_refinement μ v z)
      (fun _i => (hsource m).1)]
    simp_rw [ProbabilityTheory.variance_of_integral_eq_zero
      (hsource m).1.aestronglyMeasurable.aemeasurable (hsource m).2.1]
    simp_rw [(hsource m).2.2]
    simp
  letI hinnerProb : ∀ m, IsProbabilityMeasure
      (Measure.pi fun _i : Fin (n m) => ν m) := fun m => inferInstance
  have houterMem : ∀ m, MeasureTheory.MemLp
      (fun D : sampled_dataset K M n => X m (D m)) 2
      (Measure.pi fun m => Measure.pi fun _i : Fin (n m) => ν m) := by
    intro m
    exact (hinnerMem m).comp_measurePreserving
      (MeasureTheory.measurePreserving_eval
        (fun m => Measure.pi fun _i : Fin (n m) => ν m) m)
  have hdataMem : MeasureTheory.MemLp
      (fun D => compact_gaussian_data_score_refinement μ v D z) 2
      (sampling_law p n (compact_gaussian_location_model_refinement μ v)) := by
    unfold sampling_law
    change MeasureTheory.MemLp _ 2
      (Measure.pi fun m => Measure.pi fun _i : Fin (n m) => ν m)
    have hsum := MeasureTheory.memLp_finsetSum Finset.univ
      (fun m hm => houterMem m)
    simpa [compact_gaussian_data_score_refinement,
      compact_gaussian_observation_score_refinement, X, Finset.sum_apply] using hsum
  have hdataMean :
      (∫ D, compact_gaussian_data_score_refinement μ v D z
          ∂sampling_law p n
            (compact_gaussian_location_model_refinement μ v)) = 0 := by
    unfold sampling_law
    change (∫ D, compact_gaussian_data_score_refinement μ v D z
      ∂Measure.pi fun m => Measure.pi fun _i : Fin (n m) => ν m) = 0
    have hfun : (fun D =>
        compact_gaussian_data_score_refinement μ v D z) =
        ∑ m, fun D => X m (D m) := by
      funext D
      simp [compact_gaussian_data_score_refinement,
        compact_gaussian_observation_score_refinement, X, Finset.sum_apply]
    rw [hfun]
    have heval : ∀ m,
        (∫ D, X m (D m)
            ∂Measure.pi fun m => Measure.pi fun _i : Fin (n m) => ν m) = 0 := by
      intro m
      have hpres := MeasureTheory.measurePreserving_eval
        (fun m => Measure.pi fun _i : Fin (n m) => ν m) m
      calc
        (∫ D, X m (D m)
            ∂Measure.pi fun m => Measure.pi fun _i : Fin (n m) => ν m) =
            ∫ d, X m d ∂Measure.map (fun D => D m)
              (Measure.pi fun m => Measure.pi fun _i : Fin (n m) => ν m) := by
          symm
          exact MeasureTheory.integral_map
            (measurable_pi_apply m).aemeasurable
            (hpres.map_eq.symm ▸ (hinnerMem m).aestronglyMeasurable)
        _ = ∫ d, X m d ∂Measure.pi fun _i : Fin (n m) => ν m := by
          rw [hpres.map_eq]
        _ = 0 := hinnerMean m
    calc
      integral (Measure.pi fun m => Measure.pi fun _i : Fin (n m) => ν m)
          (∑ m, fun D => X m (D m)) =
          ∫ D, ∑ m, X m (D m)
            ∂Measure.pi fun m => Measure.pi fun _i : Fin (n m) => ν m := by
        congr 1
        funext D
        simp only [Finset.sum_apply]
      _ =
          ∑ m, ∫ D, X m (D m)
            ∂Measure.pi fun m => Measure.pi fun _i : Fin (n m) => ν m := by
        simpa only [Finset.sum_apply] using
          MeasureTheory.integral_finsetSum
            (μ := Measure.pi fun m =>
              Measure.pi fun _i : Fin (n m) => ν m)
            (f := fun m D => X m (D m)) Finset.univ
            (fun m hm => (houterMem m).integrable one_le_two)
      _ = 0 := by simp [heval]
  refine ⟨hdataMem, hdataMean, ?_⟩
  rw [← ProbabilityTheory.variance_of_integral_eq_zero
    hdataMem.aestronglyMeasurable.aemeasurable hdataMean]
  unfold sampling_law
  change ProbabilityTheory.variance
      (compact_gaussian_data_score_refinement μ v (n := n) · z)
      (Measure.pi fun m => Measure.pi fun _i : Fin (n m) => ν m) = _
  rw [show (fun D => compact_gaussian_data_score_refinement μ v D z) =
      ∑ m, fun D => X m (D m) by
    funext D
    simp [compact_gaussian_data_score_refinement,
      compact_gaussian_observation_score_refinement, X, Finset.sum_apply]]
  rw [ProbabilityTheory.variance_sum_pi
    (μ := fun m => Measure.pi fun _i : Fin (n m) => ν m)
    (X := X) hinnerMem]
  simp_rw [hinnerVar]
  unfold plan_expected_group_count_local
  calc
    (∑ m, (n m : ℝ) *
        (pmf_real_mass (p.sourceGroup m) z / (v : ℝ))) =
        ∑ m, ((n m : ℝ) * pmf_real_mass (p.sourceGroup m) z) / (v : ℝ) := by
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = (∑ m, (n m : ℝ) * pmf_real_mass (p.sourceGroup m) z) /
        (v : ℝ) := by
      simpa using (Finset.sum_div Finset.univ
        (fun m => (n m : ℝ) * pmf_real_mass (p.sourceGroup m) z)
        (v : ℝ)).symm

@[blueprint "lem:compact-quartic-prior-ae-support-refinement"
  (statement := /-- If $a>0$, the compact quartic prior is almost surely supported on $[-a,a]$. -/)
  (proof := /-- By \cref{lem:compact-quartic-prior-density-regularity-refinement}, the quartic density is measurable and nonnegative. The almost-everywhere characterization for density measures therefore reduces the claim to points where this density is nonzero. Outside $[-a,a]$ its defining interval indicator vanishes, so every such point belongs to the claimed interval. -/)
  (title := /-- Almost-sure support of the compact quartic prior -/)
  (latexEnv := "lemma")]
lemma compact_quartic_prior_ae_support_refinement (a : ℝ) (ha : 0 < a) :
    ∀ᵐ x ∂compact_quartic_prior_measure_refinement a, x ∈ Set.Icc (-a) a := by
  rw [compact_quartic_prior_measure_refinement]
  have hreg := compact_quartic_prior_density_regularity_refinement a ha
  apply (MeasureTheory.ae_withDensity_iff
    (continuous_real_toNNReal.measurable.comp hreg.2).coe_nnreal_ennreal).2
  filter_upwards with x
  intro hx
  by_contra hmem
  have hout : x ∉ Set.Ioc (-a) a := by
    intro hin
    exact hmem ⟨le_of_lt hin.1, hin.2⟩
  simp [compact_quartic_prior_density_refinement, hout] at hx

@[blueprint "lem:compact-quartic-prior-score-memlp-refinement"
  (statement := /-- If $a>0$, the compact quartic prior score belongs to $L^2$ of the compact prior measure. -/)
  (proof := /-- The density is measurable and nonnegative by \cref{lem:compact-quartic-prior-density-regularity-refinement}. Multiplying the measurable score's square by that density cancels the denominator on $(-a,a)$ and gives the integrable compactly supported quadratic $15x^2/a^5$; off that interval the product vanishes. The density-measure characterization of integrability then yields the asserted $L^2$ membership. -/)
  (title := /-- Square-integrability of the compact prior score -/)
  (latexEnv := "lemma")]
lemma compact_quartic_prior_score_memlp_refinement (a : ℝ) (ha : 0 < a) :
    MeasureTheory.MemLp (compact_quartic_prior_score_refinement a) 2
      (compact_quartic_prior_measure_refinement a) := by
  let d := compact_quartic_prior_density_refinement a
  let q : ℝ → NNReal := fun x => (d x).toNNReal
  let g : ℝ → ℝ := fun x =>
    d x * (compact_quartic_prior_score_refinement a x) ^ 2
  have hreg := compact_quartic_prior_density_regularity_refinement a ha
  have hsmeas : Measurable (compact_quartic_prior_score_refinement a) := by
    unfold compact_quartic_prior_score_refinement
    apply Measurable.ite measurableSet_Ioo
    · fun_prop
    · exact measurable_const
  have hpoint :
      g =
        Set.indicator (Set.Ioo (-a) a)
          (fun x => (15 / (a ^ 5)) * x ^ 2) := by
    funext x
    by_cases hx : x ∈ Set.Ioo (-a) a
    · have hxIoc : x ∈ Set.Ioc (-a) a := ⟨hx.1, le_of_lt hx.2⟩
      have hxpos : 0 < a ^ 2 - x ^ 2 := by nlinarith [hx.1, hx.2]
      simp only [g, d, compact_quartic_prior_density_refinement,
        compact_quartic_prior_score_refinement, hx, hxIoc,
        Set.indicator_of_mem, if_true]
      field_simp [ne_of_gt ha, ne_of_gt hxpos]
      ring
    · have hs0 : compact_quartic_prior_score_refinement a x = 0 := by
        simp [compact_quartic_prior_score_refinement, hx]
      simp [g, hs0, hx]
  have hgint : Integrable g := by
    rw [hpoint]
    have hpIcc : IntegrableOn
        (fun x : ℝ => (15 / (a ^ 5)) * x ^ 2) (Set.Icc (-a) a) :=
      (by fun_prop : Continuous
        (fun x : ℝ => (15 / (a ^ 5)) * x ^ 2)).integrableOn_Icc
    exact (hpIcc.mono_set Set.Ioo_subset_Icc_self).integrable_indicator
      measurableSet_Ioo
  apply (MeasureTheory.memLp_two_iff_integrable_sq
    hsmeas.aestronglyMeasurable).2
  rw [compact_quartic_prior_measure_refinement]
  have hqmeas : Measurable q :=
    continuous_real_toNNReal.measurable.comp hreg.2
  rw [MeasureTheory.integrable_withDensity_iff_integrable_smul hqmeas]
  have hfun : (fun x => q x • (compact_quartic_prior_score_refinement a x) ^ 2) =
      g := by
    funext x
    change (q x : ℝ) * (compact_quartic_prior_score_refinement a x) ^ 2 =
      d x * (compact_quartic_prior_score_refinement a x) ^ 2
    rw [Real.coe_toNNReal _ (hreg.1 x)]
  rwa [hfun]

@[blueprint "lem:compact-gaussian-pointwise-prior-score-integration-refinement"
  (statement := /-- Fixing a dataset, a coordinate, and all other means, the compact-prior integral of estimation error times total coordinate score and Gaussian likelihood equals the compact-prior likelihood integral. -/)
  (proof := /-- The density is measurable and nonnegative by \cref{lem:compact-quartic-prior-density-regularity-refinement}. Rewrite both prior integrals as Lebesgue integrals weighted by this density. It vanishes off $(-a,a]$, so the integrals reduce to the corresponding interval integrals on $[-a,a]$, where the desired equality is \cref{lem:compact-gaussian-pointwise-score-integration-refinement}. -/)
  (title := /-- Pointwise score identity under the compact prior -/)
  (latexEnv := "lemma")]
lemma compact_gaussian_pointwise_prior_score_integration_refinement
    {K M : ℕ} {n : sampling_plan M}
    (μ : Fin K → ℝ) (v : NNReal) (hv : 0 < v)
    (a : ℝ) (ha : 0 < a) (D : sampled_dataset K M n)
    (z : Fin K) (T : ℝ) :
    (∫ t,
        (T - t) *
          (compact_gaussian_data_score_refinement
              (Function.update μ z t) v D z +
            compact_quartic_prior_score_refinement a t) *
          compact_gaussian_sampling_density_real_refinement
              (Function.update μ z t) v D
        ∂compact_quartic_prior_measure_refinement a) =
      ∫ t, compact_gaussian_sampling_density_real_refinement
          (Function.update μ z t) v D
        ∂compact_quartic_prior_measure_refinement a := by
  let q := compact_quartic_prior_density_refinement a
  let qnn : ℝ → NNReal := fun t => (q t).toNNReal
  have hreg := compact_quartic_prior_density_regularity_refinement a ha
  have hqnn : Measurable qnn :=
    continuous_real_toNNReal.measurable.comp hreg.2
  rw [compact_quartic_prior_measure_refinement]
  rw [integral_withDensity_eq_integral_smul hqnn,
    integral_withDensity_eq_integral_smul hqnn]
  simp only [NNReal.smul_def]
  simp_rw [show ∀ t, (qnn t : ℝ) = q t by
    intro t
    exact Real.coe_toNNReal _ (hreg.1 t)]
  let F : ℝ → ℝ := fun t =>
    (T - t) *
      (compact_gaussian_data_score_refinement
          (Function.update μ z t) v D z +
        compact_quartic_prior_score_refinement a t) *
      compact_gaussian_sampling_density_real_refinement
          (Function.update μ z t) v D
  let L : ℝ → ℝ := fun t =>
    compact_gaussian_sampling_density_real_refinement
      (Function.update μ z t) v D
  have hFind : (fun t => q t * F t) =
      Set.indicator (Set.Ioc (-a) a) (fun t => q t * F t) := by
    funext t
    by_cases ht : t ∈ Set.Ioc (-a) a
    · simp [ht]
    · simp [q, compact_quartic_prior_density_refinement, ht]
  have hLind : (fun t => q t * L t) =
      Set.indicator (Set.Ioc (-a) a) (fun t => q t * L t) := by
    funext t
    by_cases ht : t ∈ Set.Ioc (-a) a
    · simp [ht]
    · simp [q, compact_quartic_prior_density_refinement, ht]
  change (∫ t, q t * F t) = ∫ t, q t * L t
  rw [hFind, hLind, MeasureTheory.integral_indicator measurableSet_Ioc,
    MeasureTheory.integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -a ≤ a),
    ← intervalIntegral.integral_of_le (by linarith : -a ≤ a)]
  have hpoint := compact_gaussian_pointwise_score_integration_refinement
    μ v hv a ha D z T
  convert hpoint using 1 <;>
    apply intervalIntegral.integral_congr <;>
    intro t ht <;>
    dsimp only [F, L, q] <;>
    ring

@[blueprint "def:compact-gaussian-joint-measure-refinement"
  (statement := /-- The compact-prior Gaussian joint law is the product of the parameter prior and fixed sampling base, weighted by the Gaussian sampling likelihood. -/)
  (title := /-- Compact-prior Gaussian joint law -/)
  (latexEnv := "definition")]
noncomputable def compact_gaussian_joint_measure_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (a : ℝ) (v : NNReal) :
    Measure ((Fin K → ℝ) × sampled_dataset K M n) :=
  ((Measure.pi fun _z : Fin K => compact_quartic_prior_measure_refinement a).prod
      (compact_gaussian_sampling_base_refinement p n)).withDensity
    (fun x => (compact_gaussian_sampling_density_refinement x.1 v x.2 : ENNReal))

@[blueprint "lem:compact-gaussian-joint-density-measurable-refinement"
  (statement := /-- The Gaussian sampling likelihood is jointly measurable in the mean vector and dataset. -/)
  (proof := /-- Expand the finite product likelihood. Each observation label is finite-valued and measurable; partitioning by that label makes evaluation of the mean vector measurable. The real Gaussian density and projection to the nonnegative reals are continuous, and finite products preserve measurability. -/)
  (title := /-- Joint measurability of the Gaussian likelihood -/)
  (latexEnv := "lemma")]
lemma compact_gaussian_joint_density_measurable_refinement
    {K M : ℕ} {n : sampling_plan M} (v : NNReal) :
    Measurable (fun x : (Fin K → ℝ) × sampled_dataset K M n =>
      compact_gaussian_sampling_density_refinement x.1 v x.2) := by
  unfold compact_gaussian_sampling_density_refinement
  apply Finset.measurable_prod
  intro m hm
  apply Finset.measurable_prod
  intro i hi
  unfold compact_gaussian_observation_density_refinement
  have hmcoord : Measurable
      (fun x : (Fin K → ℝ) × sampled_dataset K M n => x.2 m) :=
    (measurable_pi_apply m).comp measurable_snd
  have hcoord : Measurable
      (fun x : (Fin K → ℝ) × sampled_dataset K M n => x.2 m i) :=
    (measurable_pi_apply i).comp hmcoord
  have hmean : Measurable
      (fun x : (Fin K → ℝ) × sampled_dataset K M n => x.1 (x.2 m i).1) := by
    have heq : (fun x : (Fin K → ℝ) × sampled_dataset K M n =>
        x.1 (x.2 m i).1) =
        fun x => ∑ z, if (x.2 m i).1 = z then x.1 z else 0 := by
      funext x
      simp
    rw [heq]
    apply Finset.measurable_sum
    intro z hz
    apply Measurable.ite
    · exact hcoord.fst (MeasurableSet.singleton z)
    · exact (measurable_pi_apply z).comp measurable_fst
    · exact measurable_const
  exact continuous_real_toNNReal.measurable.comp
    (ProbabilityTheory.measurable_uncurry_gaussianPDFReal.comp
      (hmean.prodMk (measurable_const.prodMk hcoord.snd)))

@[blueprint "lem:compact-gaussian-source-probability-refinement"
  (statement := /-- Every labelled source-observation law in the Gaussian location model is a probability measure. -/)
  (proof := /-- Expand the source law by \cref{lem:source-observation-law-mixture-local}. Every embedded Gaussian fibre has mass one, and \cref{lem:finite-pmf-real-mass-sum-local} states that the finite source masses sum to one. -/)
  (title := /-- Probability normalization of a Gaussian source law -/)
  (latexEnv := "lemma")]
lemma compact_gaussian_source_probability_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (μ : Fin K → ℝ)
    (v : NNReal) (m : Fin M) :
    IsProbabilityMeasure
      (source_observation_law p
        (compact_gaussian_location_model_refinement μ v) m) := by
  constructor
  rw [source_observation_law_mixture_local]
  have hm : ∀ x : Fin K,
      (Measure.map (Prod.mk x)
        (compact_gaussian_location_model_refinement μ v x : Measure ℝ))
          Set.univ = 1 := by
    intro x
    rw [Measure.map_apply measurable_prodMk_left MeasurableSet.univ]
    simp
  rw [show (∑ x : Fin K, (p.sourceGroup m x).toNNReal •
      (compact_gaussian_location_model_refinement μ v x : Measure ℝ).map
        (Prod.mk x)) =
      ∑ x ∈ (Finset.univ : Finset (Fin K)),
        (p.sourceGroup m x).toNNReal •
          (compact_gaussian_location_model_refinement μ v x : Measure ℝ).map
            (Prod.mk x) by simp]
  rw [MeasureTheory.Measure.finsetSum_apply]
  simp only [Measure.smul_apply, hm, ENNReal.smul_one,
    Finset.sum_filter, Finset.mem_univ, ↓reduceIte]
  norm_cast
  apply NNReal.eq
  push_cast
  simpa [pmf_real_mass] using
    finite_pmf_real_mass_sum_local (p.sourceGroup m)

@[blueprint "lem:compact-gaussian-sampling-probability-refinement"
  (statement := /-- The full heterogeneous Gaussian sampling law is a probability measure. -/)
  (proof := /-- Every observation factor is a probability measure by \cref{lem:compact-gaussian-source-probability-refinement}; both finite product layers therefore have total mass one. -/)
  (title := /-- Probability normalization of the Gaussian sampling law -/)
  (latexEnv := "lemma")]
lemma compact_gaussian_sampling_probability_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (μ : Fin K → ℝ) (v : NNReal) :
    IsProbabilityMeasure
      (sampling_law p n (compact_gaussian_location_model_refinement μ v)) := by
  letI : ∀ m : Fin M, IsProbabilityMeasure
      (source_observation_law p
        (compact_gaussian_location_model_refinement μ v) m) :=
    fun m => compact_gaussian_source_probability_refinement p μ v m
  unfold sampling_law
  infer_instance

@[blueprint "lem:compact-quartic-prior-product-eval-refinement"
  (statement := /-- Evaluation at any coordinate sends the finite product compact prior to its one-dimensional compact-prior factor. -/)
  (proof := /-- Each coordinate factor is a probability measure by \cref{lem:compact-quartic-prior-probability-refinement}; the standard coordinate-projection theorem for finite product measures is therefore measure preserving. -/)
  (title := /-- Coordinate marginal of the compact product prior -/)
  (latexEnv := "lemma")]
lemma compact_quartic_prior_product_eval_refinement
    {K : ℕ} (a : ℝ) (ha : 0 < a) (z : Fin K) :
    MeasurePreserving (fun μ : Fin K → ℝ => μ z)
      (Measure.pi fun _z : Fin K => compact_quartic_prior_measure_refinement a)
      (compact_quartic_prior_measure_refinement a) := by
  letI : ∀ _z : Fin K,
      IsProbabilityMeasure (compact_quartic_prior_measure_refinement a) :=
    fun _z => compact_quartic_prior_probability_refinement a ha
  refine ⟨measurable_pi_apply z, ?_⟩
  classical
  rw [Measure.pi_map_eval, Finset.prod_eq_one, one_smul]
  intro i hi
  exact (compact_quartic_prior_probability_refinement a ha).measure_univ

@[blueprint "lem:compact-gaussian-joint-score-information-refinement"
  (statement := /-- If $a,v>0$, the sum of the Gaussian data score and compact-prior score in coordinate $z$ belongs to $L^2$ of the joint law and has second moment $\lambda_z(n)/v+10/a^2$. -/)
  (proof := /-- The prior factors are probability measures by \cref{lem:compact-quartic-prior-probability-refinement}, and their coordinate marginal is identified by \cref{lem:compact-quartic-prior-product-eval-refinement}. Conditional on the mean vector, \cref{lem:compact-gaussian-dataset-score-moments-refinement} centres the data score and gives second moment $\lambda_z(n)/v$; normalization of the sampling law is \cref{lem:compact-gaussian-sampling-probability-refinement}. The prior-score cross term therefore vanishes, its second moment is $10/a^2$ by \cref{lem:compact-quartic-prior-information-refinement}, and its $L^2$ bound is \cref{lem:compact-quartic-prior-score-memlp-refinement}. Joint measurability follows from \cref{lem:compact-gaussian-joint-density-measurable-refinement}; Fubini and the fixed-base representation \cref{lem:compact-gaussian-sampling-density-measure-refinement} then yield the asserted joint $L^2$ identity. -/)
  (title := /-- Information of the compact-prior Gaussian joint score -/)
  (latexEnv := "lemma")]
lemma compact_gaussian_joint_score_information_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (a : ℝ) (ha : 0 < a) (v : NNReal) (hv : 0 < v) (z : Fin K) :
    MeasureTheory.MemLp
        (fun x : (Fin K → ℝ) × sampled_dataset K M n =>
          compact_gaussian_data_score_refinement x.1 v x.2 z +
            compact_quartic_prior_score_refinement a (x.1 z)) 2
        (compact_gaussian_joint_measure_refinement p n a v) ∧
      (∫ x,
          (compact_gaussian_data_score_refinement x.1 v x.2 z +
            compact_quartic_prior_score_refinement a (x.1 z)) ^ 2
          ∂compact_gaussian_joint_measure_refinement p n a v) =
        plan_expected_group_count_local p n z / (v : ℝ) + 10 / a ^ 2 := by
  let π : Measure (Fin K → ℝ) :=
    Measure.pi fun _z : Fin K => compact_quartic_prior_measure_refinement a
  let β : Measure (sampled_dataset K M n) :=
    compact_gaussian_sampling_base_refinement p n
  let L : (Fin K → ℝ) × sampled_dataset K M n → NNReal := fun x =>
    compact_gaussian_sampling_density_refinement x.1 v x.2
  let Sd : (Fin K → ℝ) × sampled_dataset K M n → ℝ := fun x =>
    compact_gaussian_data_score_refinement x.1 v x.2 z
  let Sp : (Fin K → ℝ) × sampled_dataset K M n → ℝ := fun x =>
    compact_quartic_prior_score_refinement a (x.1 z)
  let S : (Fin K → ℝ) × sampled_dataset K M n → ℝ := fun x =>
    Sd x + Sp x
  letI : ∀ _z : Fin K,
      IsProbabilityMeasure (compact_quartic_prior_measure_refinement a) :=
    fun _z => compact_quartic_prior_probability_refinement a ha
  letI hπprob : IsProbabilityMeasure π := by
    dsimp only [π]
    infer_instance
  letI hβfinite : SigmaFinite β := by
    dsimp only [β, compact_gaussian_sampling_base_refinement]
    letI : ∀ m : Fin M, SigmaFinite
        (Measure.pi fun _i : Fin (n m) =>
          compact_gaussian_source_base_refinement p m) := fun m => by
      infer_instance
    infer_instance
  letI hsampling : ∀ μ : Fin K → ℝ, IsProbabilityMeasure
      (sampling_law p n (compact_gaussian_location_model_refinement μ v)) :=
    fun μ => compact_gaussian_sampling_probability_refinement p n μ v
  have hLmeas : Measurable L :=
    compact_gaussian_joint_density_measurable_refinement v
  have hSdmeas : Measurable Sd := by
    dsimp only [Sd]
    unfold compact_gaussian_data_score_refinement
    apply Finset.measurable_sum
    intro m hm
    apply Finset.measurable_sum
    intro i hi
    have hmcoord : Measurable
        (fun x : (Fin K → ℝ) × sampled_dataset K M n => x.2 m) :=
      (measurable_pi_apply m).comp measurable_snd
    have hcoord : Measurable
        (fun x : (Fin K → ℝ) × sampled_dataset K M n => x.2 m i) :=
      (measurable_pi_apply i).comp hmcoord
    apply Measurable.ite
    · exact hcoord.fst (MeasurableSet.singleton z)
    · exact (hcoord.snd.sub
        ((measurable_pi_apply z).comp measurable_fst)).div measurable_const
    · exact measurable_const
  have hSpmeas : Measurable Sp := by
    dsimp only [Sp]
    unfold compact_quartic_prior_score_refinement
    apply Measurable.ite
    · exact ((measurable_pi_apply z).comp measurable_fst)
        (measurableSet_Ioo)
    · fun_prop
    · exact measurable_const
  have hSmeas : Measurable S := hSdmeas.add hSpmeas
  have hdata : ∀ μ,
      MeasureTheory.MemLp
          (fun D => compact_gaussian_data_score_refinement μ v D z) 2
          (sampling_law p n (compact_gaussian_location_model_refinement μ v)) ∧
        (∫ D, compact_gaussian_data_score_refinement μ v D z
            ∂sampling_law p n
              (compact_gaussian_location_model_refinement μ v)) = 0 ∧
        (∫ D, (compact_gaussian_data_score_refinement μ v D z) ^ 2
            ∂sampling_law p n
              (compact_gaussian_location_model_refinement μ v)) =
          plan_expected_group_count_local p n z / (v : ℝ) := by
    intro μ
    exact compact_gaussian_dataset_score_moments_refinement p n μ v hv z
  have hsectionMem : ∀ μ, MeasureTheory.MemLp
      (fun D => S (μ, D)) 2
      (sampling_law p n (compact_gaussian_location_model_refinement μ v)) := by
    intro μ
    change MeasureTheory.MemLp
      ((fun D => compact_gaussian_data_score_refinement μ v D z) +
        (fun _D => compact_quartic_prior_score_refinement a (μ z))) 2
      (sampling_law p n (compact_gaussian_location_model_refinement μ v))
    exact (hdata μ).1.add (MeasureTheory.memLp_const
        (μ := sampling_law p n
          (compact_gaussian_location_model_refinement μ v))
        (compact_quartic_prior_score_refinement a (μ z)))
  have hsectionSq : ∀ μ, Integrable (fun D => (S (μ, D)) ^ 2)
      (sampling_law p n (compact_gaussian_location_model_refinement μ v)) := by
    intro μ
    exact (MeasureTheory.memLp_two_iff_integrable_sq
      ((hSmeas.comp measurable_prodMk_left).aestronglyMeasurable)).1
        (hsectionMem μ)
  have hinner : ∀ μ,
      (∫ D, (S (μ, D)) ^ 2
          ∂sampling_law p n (compact_gaussian_location_model_refinement μ v)) =
        plan_expected_group_count_local p n z / (v : ℝ) +
          (compact_quartic_prior_score_refinement a (μ z)) ^ 2 := by
    intro μ
    let c := compact_quartic_prior_score_refinement a (μ z)
    let sd : sampled_dataset K M n → ℝ := fun D =>
      compact_gaussian_data_score_refinement μ v D z
    have hsd := hdata μ
    have hsdint : Integrable sd
        (sampling_law p n (compact_gaussian_location_model_refinement μ v)) :=
      hsd.1.integrable one_le_two
    have hsdsq : Integrable (fun D => (sd D) ^ 2)
        (sampling_law p n (compact_gaussian_location_model_refinement μ v)) :=
      (MeasureTheory.memLp_two_iff_integrable_sq
        hsd.1.aestronglyMeasurable).1 hsd.1
    have hcross : Integrable (fun D => 2 * c * sd D)
        (sampling_law p n (compact_gaussian_location_model_refinement μ v)) :=
      hsdint.const_mul (2 * c)
    have hc : Integrable (fun _D : sampled_dataset K M n => c ^ 2)
        (sampling_law p n (compact_gaussian_location_model_refinement μ v)) :=
      MeasureTheory.integrable_const _
    have hdecomp : (fun D => (S (μ, D)) ^ 2) =
        ((fun D => (sd D) ^ 2) + (fun D => 2 * c * sd D)) +
          (fun _D => c ^ 2) := by
      funext D
      dsimp only [S, Sd, Sp, sd, c]
      change (compact_gaussian_data_score_refinement μ v D z +
          compact_quartic_prior_score_refinement a (μ z)) ^ 2 =
        compact_gaussian_data_score_refinement μ v D z ^ 2 +
          2 * compact_quartic_prior_score_refinement a (μ z) *
            compact_gaussian_data_score_refinement μ v D z +
          compact_quartic_prior_score_refinement a (μ z) ^ 2
      ring
    rw [hdecomp]
    calc
      MeasureTheory.integral
          (sampling_law p n (compact_gaussian_location_model_refinement μ v))
          (((fun D => (sd D) ^ 2) + (fun D => 2 * c * sd D)) +
            (fun _D => c ^ 2)) =
          (∫ D, (sd D) ^ 2 + 2 * c * sd D
            ∂sampling_law p n
              (compact_gaussian_location_model_refinement μ v)) +
          ∫ _D, c ^ 2
            ∂sampling_law p n
              (compact_gaussian_location_model_refinement μ v) :=
        MeasureTheory.integral_add (hsdsq.add hcross) hc
      _ = ((∫ D, (sd D) ^ 2
            ∂sampling_law p n
              (compact_gaussian_location_model_refinement μ v)) +
          ∫ D, 2 * c * sd D
            ∂sampling_law p n
              (compact_gaussian_location_model_refinement μ v)) +
          ∫ _D, c ^ 2
            ∂sampling_law p n
              (compact_gaussian_location_model_refinement μ v) := by
        rw [MeasureTheory.integral_add hsdsq hcross]
      _ = _ := by
        rw [MeasureTheory.integral_const_mul, hsd.2.1, hsd.2.2,
          MeasureTheory.integral_const]
        simp [c]
  have hLsection : ∀ μ, Measurable (fun D => L (μ, D)) :=
    fun μ => hLmeas.comp measurable_prodMk_left
  have hweightedSection : ∀ μ, Integrable
      (fun D => L (μ, D) • (S (μ, D)) ^ 2) β := by
    intro μ
    have hs := hsectionSq μ
    rw [compact_gaussian_sampling_density_measure_refinement p n μ v hv] at hs
    exact (MeasureTheory.integrable_withDensity_iff_integrable_smul
      (hLsection μ)).1 hs
  have hinnerBase : ∀ μ,
      (∫ D, L (μ, D) • (S (μ, D)) ^ 2 ∂β) =
        plan_expected_group_count_local p n z / (v : ℝ) +
          (compact_quartic_prior_score_refinement a (μ z)) ^ 2 := by
    intro μ
    rw [← integral_withDensity_eq_integral_smul (hLsection μ)]
    rw [← compact_gaussian_sampling_density_measure_refinement p n μ v hv]
    exact hinner μ
  have hweightedMeas : Measurable
      (fun x => L x • (S x) ^ 2) := by
    change Measurable (fun x => (L x : ℝ) * (S x) ^ 2)
    exact hLmeas.coe_nnreal_real.mul (hSmeas.pow_const 2)
  have hpriorScore :=
    compact_quartic_prior_score_memlp_refinement a ha
  have houterInt : Integrable
      (fun μ : Fin K → ℝ =>
        plan_expected_group_count_local p n z / (v : ℝ) +
          (compact_quartic_prior_score_refinement a (μ z)) ^ 2) π := by
    have hscorePi : MeasureTheory.MemLp
        (fun μ : Fin K → ℝ =>
          compact_quartic_prior_score_refinement a (μ z)) 2 π :=
      hpriorScore.comp_measurePreserving
        (compact_quartic_prior_product_eval_refinement a ha z)
    exact (MeasureTheory.integrable_const _).add hscorePi.integrable_sq
  have hweighted : Integrable (fun x => L x • (S x) ^ 2) (π.prod β) := by
    apply (MeasureTheory.integrable_prod_iff
      hweightedMeas.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall hweightedSection
    · have hnorm : (fun μ =>
          ∫ D, ‖L (μ, D) • (S (μ, D)) ^ 2‖ ∂β) =
          fun μ => plan_expected_group_count_local p n z / (v : ℝ) +
            (compact_quartic_prior_score_refinement a (μ z)) ^ 2 := by
        funext μ
        rw [show (fun D => ‖L (μ, D) • (S (μ, D)) ^ 2‖) =
            fun D => L (μ, D) • (S (μ, D)) ^ 2 by
          funext D
          rw [Real.norm_eq_abs, abs_of_nonneg]
          exact mul_nonneg (NNReal.coe_nonneg _) (sq_nonneg _)]
        exact hinnerBase μ
      rw [hnorm]
      exact houterInt
  have hjointSq : Integrable (fun x => (S x) ^ 2)
      (compact_gaussian_joint_measure_refinement p n a v) := by
    unfold compact_gaussian_joint_measure_refinement
    change Integrable (fun x => (S x) ^ 2)
      ((π.prod β).withDensity fun x => (L x : ENNReal))
    exact (MeasureTheory.integrable_withDensity_iff_integrable_smul hLmeas).2
      hweighted
  have hscorePiIntegral :
      (∫ μ, (compact_quartic_prior_score_refinement a (μ z)) ^ 2 ∂π) =
        10 / a ^ 2 := by
    have hpres := compact_quartic_prior_product_eval_refinement a ha z
    calc
      (∫ μ, (compact_quartic_prior_score_refinement a (μ z)) ^ 2 ∂π) =
          ∫ t, (compact_quartic_prior_score_refinement a t) ^ 2
            ∂Measure.map (fun μ : Fin K → ℝ => μ z) π := by
        symm
        exact MeasureTheory.integral_map
          (measurable_pi_apply z).aemeasurable
          (hpres.map_eq.symm ▸ hpriorScore.integrable_sq.aestronglyMeasurable)
      _ = ∫ t, (compact_quartic_prior_score_refinement a t) ^ 2
            ∂compact_quartic_prior_measure_refinement a := by
        rw [hpres.map_eq]
      _ = 10 / a ^ 2 :=
        compact_quartic_prior_information_refinement a ha
  refine ⟨(MeasureTheory.memLp_two_iff_integrable_sq
    hSmeas.aestronglyMeasurable).2 hjointSq, ?_⟩
  unfold compact_gaussian_joint_measure_refinement
  change (∫ x, (S x) ^ 2
      ∂(π.prod β).withDensity fun x => (L x : ENNReal)) = _
  rw [integral_withDensity_eq_integral_smul hLmeas]
  rw [MeasureTheory.integral_prod _ hweighted]
  simp_rw [hinnerBase]
  change (∫ μ, plan_expected_group_count_local p n z / (v : ℝ) +
      (compact_quartic_prior_score_refinement a (μ z)) ^ 2 ∂π) = _
  have hscorePiMem := hpriorScore.comp_measurePreserving
    (compact_quartic_prior_product_eval_refinement a ha z)
  calc
    (∫ μ, plan_expected_group_count_local p n z / (v : ℝ) +
        (compact_quartic_prior_score_refinement a (μ z)) ^ 2 ∂π) =
        (∫ _μ, plan_expected_group_count_local p n z / (v : ℝ) ∂π) +
          ∫ μ, (compact_quartic_prior_score_refinement a (μ z)) ^ 2 ∂π :=
      MeasureTheory.integral_add (MeasureTheory.integrable_const _)
        hscorePiMem.integrable_sq
    _ = _ := by
      rw [MeasureTheory.integral_const, hscorePiIntegral]
      simp [Measure.real_def]

@[blueprint "lem:compact-gaussian-joint-group-loss-bound-refinement"
  (statement := /-- If the compact prior is supported inside the allowed mean radius and $0<v<\sigma^2$, then the estimator's joint Bayes group loss is integrable and is at most its worst-case group risk. -/)
  (proof := /-- The prior factors are normalized by \cref{lem:compact-quartic-prior-probability-refinement}. Their coordinate marginal \cref{lem:compact-quartic-prior-product-eval-refinement} transfers the almost-sure support statement \cref{lem:compact-quartic-prior-ae-support-refinement} to the product prior. Thus every corresponding Gaussian model is admissible by \cref{lem:compact-gaussian-location-model-in-class-refinement}. The likelihood is jointly measurable by \cref{lem:compact-gaussian-joint-density-measurable-refinement}, and \cref{lem:compact-gaussian-sampling-density-measure-refinement} rewrites its fixed-base sections as sampling laws. The assumed class-wise loss integrability and the supremum bound dominate the conditional risks almost surely; Fubini and integration of this constant over the product probability measure give both assertions. -/)
  (title := /-- Joint Bayes loss bounded by worst-case risk -/)
  (latexEnv := "lemma")]
lemma compact_gaussian_joint_group_loss_bound_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (estimator : sampled_dataset K M n → (Fin K → ℝ))
    (hmeas : Measurable estimator)
    (hriskint : group_risk_integrable p n estimator)
    (hrisk : BddAbove {s : ℝ | ∃ P,
      bounded_conditional_mean_class p P ∧
      s = group_means_risk p n estimator P})
    (a : ℝ) (ha : 0 < a) (haR : a ≤ p.meanRadius)
    (v : NNReal) (hv : 0 < v) (hvR : (v : ℝ) < p.varianceBound) :
    Integrable
        (fun x : (Fin K → ℝ) × sampled_dataset K M n =>
          ∑ z, (estimator x.2 z - x.1 z) ^ 2)
        (compact_gaussian_joint_measure_refinement p n a v) ∧
      (∫ x, ∑ z, (estimator x.2 z - x.1 z) ^ 2
          ∂compact_gaussian_joint_measure_refinement p n a v) ≤
        group_worst_case_risk p n estimator hrisk := by
  let π : Measure (Fin K → ℝ) :=
    Measure.pi fun _z : Fin K => compact_quartic_prior_measure_refinement a
  let β : Measure (sampled_dataset K M n) :=
    compact_gaussian_sampling_base_refinement p n
  let L : (Fin K → ℝ) × sampled_dataset K M n → NNReal := fun x =>
    compact_gaussian_sampling_density_refinement x.1 v x.2
  let loss : (Fin K → ℝ) × sampled_dataset K M n → ℝ := fun x =>
    ∑ z, (estimator x.2 z - x.1 z) ^ 2
  let W := group_worst_case_risk p n estimator hrisk
  letI : ∀ _z : Fin K,
      IsProbabilityMeasure (compact_quartic_prior_measure_refinement a) :=
    fun _z => compact_quartic_prior_probability_refinement a ha
  letI hπprob : IsProbabilityMeasure π := by
    dsimp only [π]
    infer_instance
  letI hβfinite : SigmaFinite β := by
    dsimp only [β, compact_gaussian_sampling_base_refinement]
    letI : ∀ m : Fin M, SigmaFinite
        (Measure.pi fun _i : Fin (n m) =>
          compact_gaussian_source_base_refinement p m) := fun m => by
      infer_instance
    infer_instance
  letI hsampling : ∀ μ : Fin K → ℝ, IsProbabilityMeasure
      (sampling_law p n (compact_gaussian_location_model_refinement μ v)) :=
    fun μ => compact_gaussian_sampling_probability_refinement p n μ v
  have hLmeas : Measurable L :=
    compact_gaussian_joint_density_measurable_refinement v
  have hlossmeas : Measurable loss := by
    dsimp only [loss]
    apply Finset.measurable_sum
    intro z hz
    exact ((((measurable_pi_apply z).comp hmeas).comp measurable_snd).sub
      ((measurable_pi_apply z).comp measurable_fst)).pow_const 2
  have hsupport : ∀ᵐ μ ∂π, ∀ z, μ z ∈ Set.Icc (-a) a := by
    have h : ∀ᵐ μ ∂π, ∀ z ∈ (Set.univ : Set (Fin K)),
        μ z ∈ Set.Icc (-a) a := by
      rw [Filter.eventually_all_finite Set.finite_univ]
      intro z hz
      exact (compact_quartic_prior_product_eval_refinement a ha z).quasiMeasurePreserving.ae
        (compact_quartic_prior_ae_support_refinement a ha)
    filter_upwards [h] with μ hμ
    exact fun z => hμ z (Set.mem_univ z)
  have hclass : ∀ᵐ μ ∂π,
      bounded_conditional_mean_class p
        (compact_gaussian_location_model_refinement μ v) := by
    filter_upwards [hsupport] with μ hμ
    apply compact_gaussian_location_model_in_class_refinement p μ v
    · intro z
      exact le_trans ((abs_le).2 ⟨by linarith [(hμ z).1], (hμ z).2⟩) haR
    · exact le_of_lt hvR
  have hcondInt : ∀ᵐ μ ∂π, Integrable (fun D => loss (μ, D))
      (sampling_law p n (compact_gaussian_location_model_refinement μ v)) := by
    filter_upwards [hclass] with μ hμ
    have h := hriskint
      (compact_gaussian_location_model_refinement μ v) hμ
    simpa [loss, conditional_group_mean,
      compact_gaussian_location_model_refinement] using h
  have hW : 0 ≤ W := by
    let μ0 : Fin K → ℝ := fun _ => 0
    have hμ0 : bounded_conditional_mean_class p
        (compact_gaussian_location_model_refinement μ0 v) :=
      compact_gaussian_location_model_in_class_refinement p μ0 v
        (fun z => by simp [μ0, p.meanRadius_nonneg]) (le_of_lt hvR)
    have hmember : group_means_risk p n estimator
        (compact_gaussian_location_model_refinement μ0 v) ∈
        {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
          s = group_means_risk p n estimator P} :=
      ⟨compact_gaussian_location_model_refinement μ0 v, hμ0, rfl⟩
    exact le_trans (MeasureTheory.integral_nonneg fun D =>
      Finset.sum_nonneg fun z hz => sq_nonneg _)
      (le_csSup hrisk hmember)
  have hcondLE : ∀ᵐ μ ∂π,
      group_means_risk p n estimator
          (compact_gaussian_location_model_refinement μ v) ≤ W := by
    filter_upwards [hclass] with μ hμ
    exact le_csSup hrisk
      ⟨compact_gaussian_location_model_refinement μ v, hμ, rfl⟩
  have hLsection : ∀ μ, Measurable (fun D => L (μ, D)) :=
    fun μ => hLmeas.comp measurable_prodMk_left
  have hweightedSection : ∀ᵐ μ ∂π,
      Integrable (fun D => L (μ, D) • loss (μ, D)) β := by
    filter_upwards [hcondInt] with μ hμ
    rw [compact_gaussian_sampling_density_measure_refinement p n μ v hv] at hμ
    exact (MeasureTheory.integrable_withDensity_iff_integrable_smul
      (hLsection μ)).1 hμ
  have hinnerBase : ∀ μ,
      (∫ D, L (μ, D) • loss (μ, D) ∂β) =
        group_means_risk p n estimator
          (compact_gaussian_location_model_refinement μ v) := by
    intro μ
    rw [← integral_withDensity_eq_integral_smul (hLsection μ)]
    rw [← compact_gaussian_sampling_density_measure_refinement p n μ v hv]
    unfold group_means_risk
    simp [loss, conditional_group_mean,
      compact_gaussian_location_model_refinement]
  have hweightedMeas : Measurable (fun x => L x • loss x) := by
    change Measurable (fun x => (L x : ℝ) * loss x)
    exact hLmeas.coe_nnreal_real.mul hlossmeas
  have houterAES : AEStronglyMeasurable
      (fun μ => ∫ D, ‖L (μ, D) • loss (μ, D)‖ ∂β) π :=
    hweightedMeas.aestronglyMeasurable.norm.integral_prod_right'
  have houterBound : ∀ᵐ μ ∂π,
      ‖∫ D, ‖L (μ, D) • loss (μ, D)‖ ∂β‖ ≤ W := by
    filter_upwards [hcondLE] with μ hμ
    have hnonneg : ∀ D, 0 ≤ L (μ, D) • loss (μ, D) := by
      intro D
      exact mul_nonneg (NNReal.coe_nonneg _)
        (Finset.sum_nonneg fun z hz => sq_nonneg _)
    have heq :
        (∫ D, ‖L (μ, D) • loss (μ, D)‖ ∂β) =
          group_means_risk p n estimator
            (compact_gaussian_location_model_refinement μ v) := by
      rw [show (fun D => ‖L (μ, D) • loss (μ, D)‖) =
          fun D => L (μ, D) • loss (μ, D) by
        funext D
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg D)]]
      exact hinnerBase μ
    rw [heq, Real.norm_eq_abs, abs_of_nonneg
      (by
        unfold group_means_risk
        exact MeasureTheory.integral_nonneg fun D =>
          Finset.sum_nonneg fun z hz => sq_nonneg _)]
    exact hμ
  have houterInt : Integrable
      (fun μ => ∫ D, ‖L (μ, D) • loss (μ, D)‖ ∂β) π :=
    (MeasureTheory.integrable_const W).mono' houterAES houterBound
  have hweighted : Integrable (fun x => L x • loss x) (π.prod β) := by
    apply (MeasureTheory.integrable_prod_iff
      hweightedMeas.aestronglyMeasurable).2
    exact ⟨hweightedSection, houterInt⟩
  have hjoint : Integrable loss
      (compact_gaussian_joint_measure_refinement p n a v) := by
    unfold compact_gaussian_joint_measure_refinement
    change Integrable loss ((π.prod β).withDensity fun x => (L x : ENNReal))
    exact (MeasureTheory.integrable_withDensity_iff_integrable_smul hLmeas).2
      hweighted
  refine ⟨hjoint, ?_⟩
  unfold compact_gaussian_joint_measure_refinement
  change (∫ x, loss x ∂(π.prod β).withDensity fun x => (L x : ENNReal)) ≤ W
  rw [integral_withDensity_eq_integral_smul hLmeas]
  rw [MeasureTheory.integral_prod _ hweighted]
  simp_rw [hinnerBase]
  have hriskAES : AEStronglyMeasurable
      (fun μ => group_means_risk p n estimator
        (compact_gaussian_location_model_refinement μ v)) π := by
    have heq : (fun μ => group_means_risk p n estimator
        (compact_gaussian_location_model_refinement μ v)) =
        fun μ => ∫ D, L (μ, D) • loss (μ, D) ∂β := by
      funext μ
      exact (hinnerBase μ).symm
    rw [heq]
    exact hweightedMeas.aestronglyMeasurable.integral_prod_right'
  have hriskInt : Integrable
      (fun μ => group_means_risk p n estimator
        (compact_gaussian_location_model_refinement μ v)) π := by
    apply (MeasureTheory.integrable_const W).mono' hriskAES
    filter_upwards [hcondLE] with μ hμ
    have hnonneg : 0 ≤ group_means_risk p n estimator
        (compact_gaussian_location_model_refinement μ v) := by
      unfold group_means_risk
      exact MeasureTheory.integral_nonneg fun D =>
        Finset.sum_nonneg fun z hz => sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hμ
  calc
    (∫ μ, group_means_risk p n estimator
        (compact_gaussian_location_model_refinement μ v) ∂π) ≤
        ∫ _μ, W ∂π :=
      MeasureTheory.integral_mono_ae hriskInt (MeasureTheory.integrable_const W)
        hcondLE
    _ = W := by
      rw [MeasureTheory.integral_const]
      simp [Measure.real_def]

@[blueprint "lem:compact-gaussian-joint-score-identity-refinement"
  (statement := /-- If the coordinate squared error is integrable under the compact-prior Gaussian joint law, then its product with the total coordinate score is integrable and has integral one. -/)
  (proof := /-- The error and total score are in $L^2$, the latter by \cref{lem:compact-gaussian-joint-score-information-refinement}, so their product is integrable. The prior and sampling factors are normalized by \cref{lem:compact-quartic-prior-probability-refinement,lem:compact-gaussian-sampling-probability-refinement}; joint likelihood measurability is \cref{lem:compact-gaussian-joint-density-measurable-refinement}. Rewrite the joint integral through \cref{lem:compact-gaussian-sampling-density-measure-refinement}, using \cref{lem:compact-gaussian-sampling-density-coe-refinement} to identify its real likelihood. Fubini exposes the parameter integral. The update pushforward \cref{lem:finite-product-coordinate-update-map} and reintegration identity \cref{lem:finite-product-coordinate-reintegration} isolate coordinate $z$; after interchanging the parameter integrals, \cref{lem:compact-gaussian-pointwise-prior-score-integration-refinement} replaces error times score by likelihood. Reassembling the product prior and integrating the normalized likelihood gives one. -/)
  (title := /-- Integrated compact-prior Gaussian score identity -/)
  (latexEnv := "lemma")]
lemma compact_gaussian_joint_score_identity_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (estimator : sampled_dataset K M n → (Fin K → ℝ))
    (hmeas : Measurable estimator)
    (a : ℝ) (ha : 0 < a) (v : NNReal) (hv : 0 < v) (z : Fin K)
    (herr2 : Integrable
      (fun x : (Fin K → ℝ) × sampled_dataset K M n =>
        (estimator x.2 z - x.1 z) ^ 2)
      (compact_gaussian_joint_measure_refinement p n a v)) :
    Integrable
        (fun x : (Fin K → ℝ) × sampled_dataset K M n =>
          (estimator x.2 z - x.1 z) *
            (compact_gaussian_data_score_refinement x.1 v x.2 z +
              compact_quartic_prior_score_refinement a (x.1 z)))
        (compact_gaussian_joint_measure_refinement p n a v) ∧
      (∫ x,
          (estimator x.2 z - x.1 z) *
            (compact_gaussian_data_score_refinement x.1 v x.2 z +
              compact_quartic_prior_score_refinement a (x.1 z))
          ∂compact_gaussian_joint_measure_refinement p n a v) = 1 := by
  let prior : Measure ℝ := compact_quartic_prior_measure_refinement a
  let π : Measure (Fin K → ℝ) := Measure.pi fun _z : Fin K => prior
  let β : Measure (sampled_dataset K M n) :=
    compact_gaussian_sampling_base_refinement p n
  let L : (Fin K → ℝ) × sampled_dataset K M n → NNReal := fun x =>
    compact_gaussian_sampling_density_refinement x.1 v x.2
  let e : (Fin K → ℝ) × sampled_dataset K M n → ℝ := fun x =>
    estimator x.2 z - x.1 z
  let S : (Fin K → ℝ) × sampled_dataset K M n → ℝ := fun x =>
    compact_gaussian_data_score_refinement x.1 v x.2 z +
      compact_quartic_prior_score_refinement a (x.1 z)
  letI : IsProbabilityMeasure prior :=
    compact_quartic_prior_probability_refinement a ha
  letI : ∀ _z : Fin K, IsProbabilityMeasure prior := fun _z => inferInstance
  letI hπprob : IsProbabilityMeasure π := by
    dsimp only [π]
    infer_instance
  letI hβfinite : SigmaFinite β := by
    dsimp only [β, compact_gaussian_sampling_base_refinement]
    letI : ∀ m : Fin M, SigmaFinite
        (Measure.pi fun _i : Fin (n m) =>
          compact_gaussian_source_base_refinement p m) := fun m => by
      infer_instance
    infer_instance
  have hLmeas : Measurable L :=
    compact_gaussian_joint_density_measurable_refinement v
  have hemeas : Measurable e :=
    ((((measurable_pi_apply z).comp hmeas).comp measurable_snd).sub
      ((measurable_pi_apply z).comp measurable_fst))
  have heMem : MeasureTheory.MemLp e 2
      (compact_gaussian_joint_measure_refinement p n a v) :=
    (MeasureTheory.memLp_two_iff_integrable_sq
      hemeas.aestronglyMeasurable).2 herr2
  have hscore :=
    compact_gaussian_joint_score_information_refinement p n a ha v hv z
  have hSMem : MeasureTheory.MemLp S 2
      (compact_gaussian_joint_measure_refinement p n a v) := by
    exact hscore.1
  have heS : Integrable (fun x => e x * S x)
      (compact_gaussian_joint_measure_refinement p n a v) := by
    change Integrable (e * S)
      (compact_gaussian_joint_measure_refinement p n a v)
    exact heMem.integrable_mul hSMem
  refine ⟨heS, ?_⟩
  have hweighted : Integrable (fun x => L x • (e x * S x)) (π.prod β) := by
    unfold compact_gaussian_joint_measure_refinement at heS
    change Integrable (fun x => e x * S x)
      ((π.prod β).withDensity fun x => (L x : ENNReal)) at heS
    exact (MeasureTheory.integrable_withDensity_iff_integrable_smul hLmeas).1 heS
  have hLsection : ∀ μ, Measurable (fun D => L (μ, D)) :=
    fun μ => hLmeas.comp measurable_prodMk_left
  have hLsectionInt : ∀ μ, Integrable (fun D => (L (μ, D) : ℝ)) β := by
    intro μ
    have hconst : Integrable (fun _D : sampled_dataset K M n => (1 : ℝ))
        (sampling_law p n (compact_gaussian_location_model_refinement μ v)) := by
      letI := compact_gaussian_sampling_probability_refinement p n μ v
      exact MeasureTheory.integrable_const _
    rw [compact_gaussian_sampling_density_measure_refinement p n μ v hv] at hconst
    have hsmul := (MeasureTheory.integrable_withDensity_iff_integrable_smul
      (hLsection μ)).1 hconst
    simpa only [NNReal.smul_def, smul_eq_mul, mul_one] using hsmul
  have hLinner : ∀ μ, (∫ D, (L (μ, D) : ℝ) ∂β) = 1 := by
    intro μ
    rw [show (fun D => (L (μ, D) : ℝ)) =
        fun D => L (μ, D) • (1 : ℝ) by
      funext D
      simp only [NNReal.smul_def, smul_eq_mul, mul_one]]
    rw [← integral_withDensity_eq_integral_smul (hLsection μ)]
    rw [← compact_gaussian_sampling_density_measure_refinement p n μ v hv]
    letI := compact_gaussian_sampling_probability_refinement p n μ v
    rw [MeasureTheory.integral_const]
    simp [Measure.real_def]
  have hLweighted : Integrable (fun x => (L x : ℝ)) (π.prod β) := by
    apply (MeasureTheory.integrable_prod_iff
      hLmeas.coe_nnreal_real.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall hLsectionInt
    · have heq : (fun μ => ∫ D, ‖(L (μ, D) : ℝ)‖ ∂β) =
          fun _μ => (1 : ℝ) := by
        funext μ
        rw [show (fun D => ‖(L (μ, D) : ℝ)‖) =
            fun D => (L (μ, D) : ℝ) by
          funext D
          rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]]
        exact hLinner μ
      rw [heq]
      exact MeasureTheory.integrable_const _
  have hsections : ∀ᵐ D ∂β,
      Integrable (fun μ => L (μ, D) • (e (μ, D) * S (μ, D))) π ∧
        Integrable (fun μ => (L (μ, D) : ℝ)) π := by
    filter_upwards [hweighted.prod_left_ae, hLweighted.prod_left_ae]
      with D hD hLD
    exact ⟨hD, hLD⟩
  have hinnerEq : ∀ᵐ D ∂β,
      (∫ μ, L (μ, D) • (e (μ, D) * S (μ, D)) ∂π) =
        ∫ μ, (L (μ, D) : ℝ) ∂π := by
    filter_upwards [hsections] with D hD
    let f : (Fin K → ℝ) → ℝ := fun μ =>
      L (μ, D) • (e (μ, D) * S (μ, D))
    let g : (Fin K → ℝ) → ℝ := fun μ => (L (μ, D) : ℝ)
    have hf : Integrable f π := hD.1
    have hg : Integrable g π := hD.2
    have hmeasUpdate :
        Measurable (fun q : (Fin K → ℝ) × ℝ =>
          Function.update q.1 z q.2) := measurable_update' (a := z)
    have hpres : MeasurePreserving
        (fun q : ℝ × (Fin K → ℝ) => Function.update q.2 z q.1)
        (prior.prod π) π := by
      have hfun :
          (fun q : ℝ × (Fin K → ℝ) => Function.update q.2 z q.1) =
            (fun q : (Fin K → ℝ) × ℝ =>
              Function.update q.1 z q.2) ∘ Prod.swap := rfl
      refine ⟨by rw [hfun]; exact hmeasUpdate.comp measurable_swap, ?_⟩
      simpa [prior, π] using finite_product_coordinate_update_map
        (fun _z : Fin K => compact_quartic_prior_measure_refinement a) z
    have hfcomp : Integrable
        (fun q : ℝ × (Fin K → ℝ) => f (Function.update q.2 z q.1))
        (prior.prod π) :=
      (hpres.integrable_comp hf.aestronglyMeasurable).mpr hf
    have hgcomp : Integrable
        (fun q : ℝ × (Fin K → ℝ) => g (Function.update q.2 z q.1))
        (prior.prod π) :=
      (hpres.integrable_comp hg.aestronglyMeasurable).mpr hg
    calc
      (∫ μ, f μ ∂π) =
          ∫ t, ∫ μ, f (Function.update μ z t) ∂π ∂prior :=
        (finite_product_coordinate_reintegration
          (fun _z : Fin K => prior) z f hf).symm
      _ = ∫ μ, ∫ t, f (Function.update μ z t) ∂prior ∂π := by
        rw [← MeasureTheory.integral_prod _ hfcomp,
          MeasureTheory.integral_prod_symm _ hfcomp]
      _ = ∫ μ, ∫ t, g (Function.update μ z t) ∂prior ∂π := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with μ
        have hp :=
          compact_gaussian_pointwise_prior_score_integration_refinement
            μ v hv a ha D z (estimator D z)
        simpa [f, g, L, e, S, NNReal.smul_def,
          compact_gaussian_sampling_density_coe_refinement,
          mul_comm, mul_left_comm, mul_assoc] using hp
      _ = ∫ t, ∫ μ, g (Function.update μ z t) ∂π ∂prior := by
        rw [← MeasureTheory.integral_prod_symm _ hgcomp,
          MeasureTheory.integral_prod _ hgcomp]
      _ = ∫ μ, g μ ∂π :=
        finite_product_coordinate_reintegration
          (fun _z : Fin K => prior) z g hg
  unfold compact_gaussian_joint_measure_refinement
  change (∫ x, e x * S x
      ∂(π.prod β).withDensity fun x => (L x : ENNReal)) = 1
  rw [integral_withDensity_eq_integral_smul hLmeas]
  rw [MeasureTheory.integral_prod_symm _ hweighted]
  rw [MeasureTheory.integral_congr_ae hinnerEq]
  rw [← MeasureTheory.integral_prod_symm _ hLweighted]
  rw [MeasureTheory.integral_prod _ hLweighted]
  simp_rw [hLinner]
  rw [MeasureTheory.integral_const]
  simp [Measure.real_def]

@[blueprint "lem:compact-gaussian-coordinate-information-refinement"
  (statement := /-- For $a,v>0$, any estimator coordinate with integrable squared error under the compact-prior Gaussian joint law has Bayes risk at least
  \[
  \frac{v}{\lambda_z(n)+v(10/a^2)}.
  \] -/)
  (proof := /-- The total coordinate score has integrable square and information $\lambda_z(n)/v+10/a^2$ by \cref{lem:compact-gaussian-joint-score-information-refinement}. Its product with the estimator error is integrable and has integral one by \cref{lem:compact-gaussian-joint-score-identity-refinement}. Positivity of $\lambda_z(n)$ is \cref{lem:plan-expected-group-count-nonnegative-local}. Apply \cref{lem:integrated-score-information-lower-refinement} and clear the positive factor $v$ in the denominator. -/)
  (title := /-- Coordinate compact-prior information inequality -/)
  (latexEnv := "lemma")]
lemma compact_gaussian_coordinate_information_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (estimator : sampled_dataset K M n → (Fin K → ℝ))
    (hmeas : Measurable estimator)
    (a : ℝ) (ha : 0 < a) (v : NNReal) (hv : 0 < v) (z : Fin K)
    (herr2 : Integrable
      (fun x : (Fin K → ℝ) × sampled_dataset K M n =>
        (estimator x.2 z - x.1 z) ^ 2)
      (compact_gaussian_joint_measure_refinement p n a v)) :
    (v : ℝ) /
        (plan_expected_group_count_local p n z + (v : ℝ) * (10 / a ^ 2)) ≤
      ∫ x, (estimator x.2 z - x.1 z) ^ 2
        ∂compact_gaussian_joint_measure_refinement p n a v := by
  let e : (Fin K → ℝ) × sampled_dataset K M n → ℝ := fun x =>
    estimator x.2 z - x.1 z
  let S : (Fin K → ℝ) × sampled_dataset K M n → ℝ := fun x =>
    compact_gaussian_data_score_refinement x.1 v x.2 z +
      compact_quartic_prior_score_refinement a (x.1 z)
  let I := plan_expected_group_count_local p n z / (v : ℝ) + 10 / a ^ 2
  have hscore :=
    compact_gaussian_joint_score_information_refinement p n a ha v hv z
  have hS2 : Integrable (fun x => (S x) ^ 2)
      (compact_gaussian_joint_measure_refinement p n a v) :=
    hscore.1.integrable_sq
  have hid := compact_gaussian_joint_score_identity_refinement
    p n estimator hmeas a ha v hv z herr2
  have hvreal : (0 : ℝ) < v := by exact_mod_cast hv
  have hI : 0 < I := by
    dsimp only [I]
    have hlam := plan_expected_group_count_nonnegative_local p n z
    have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
    positivity
  have hraw := integrated_score_information_lower_refinement
    (compact_gaussian_joint_measure_refinement p n a v)
    e S I herr2 hS2 hid.1 hid.2 (by
      dsimp only [I, S]
      exact le_of_eq hscore.2) hI
  have heq :
      1 / I =
        (v : ℝ) /
          (plan_expected_group_count_local p n z + (v : ℝ) * (10 / a ^ 2)) := by
    dsimp only [I]
    field_simp [ne_of_gt hvreal]
  rwa [heq] at hraw

@[blueprint "lem:compact-product-prior-information-inequality"
  (statement := /-- Let $K$ and $M$ be positive integers, and let $p$ be a biased-source mean-estimation problem with mean radius $R>0$ and variance bound $\sigma^2>0$. There exists a constant $I_\pi>0$ such that, for every $v\in(0,\sigma^2)$, every sampling plan $n$, and every measurable estimator $\widehat\mu$ of the $K$ conditional means whose squared group loss is integrable under every model in $\mathcal P_p(R,\sigma^2)$ and whose set of risks over this class is bounded above,
  \[
  \sum_{z\in[K]}\frac{v}{\lambda_z(n)+vI_\pi}
  \leq \sup_{P\in\mathcal P_p(R,\sigma^2)}
  \operatorname{Risk}_{\mathrm{GM}}((n,\widehat\mu),P),
  \qquad
  \lambda_z(n)=\sum_m n_mq_{S,m}(z).
  \]
  where the supremum is the real supremum associated with any witness that the risk set is bounded above. -/)
  (proof := /-- Set $a=R/2$ and $I_\pi=10/a^2$, which are positive because $R>0$. Fix $v\in(0,\sigma^2)$, a sampling plan, an estimator, and the prescribed integrability and boundedness witnesses. By \cref{lem:compact-gaussian-joint-group-loss-bound-refinement}, the squared group loss is integrable under the compact-prior Gaussian joint law of \cref{def:compact-gaussian-joint-measure-refinement}, and its joint integral is at most the real supremum in \cref{def:group-worst-case-risk}. Since every coordinatewise squared error is nonnegative and bounded above by the squared group loss, each coordinatewise squared error is integrable under the same joint law.

  For every group $z$, \cref{lem:compact-gaussian-coordinate-information-refinement} therefore gives
  \[
  \frac{v}{\lambda_z(n)+vI_\pi}
  \leq
  \int (\widehat\mu_z-\mu_z)^2\,d\mathbb P_{\pi,v},
  \]
  where $\lambda_z(n)$ is the expected sampled group count of \cref{def:plan-expected-group-count-local}. Summing these inequalities over the finite group set and using finite linearity of the integral identifies the sum of the coordinatewise joint errors with the joint squared group loss. The preceding joint-loss bound then yields the asserted inequality. -/)
  (title := /-- Compact-product-prior information inequality -/)
  (latexEnv := "lemma")]
lemma compact_product_prior_information_inequality
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (hmean : 0 < p.meanRadius)
    (hvar : 0 < p.varianceBound) :
    ∃ priorInformation : ℝ, 0 < priorInformation ∧
      ∀ noiseVariance : ℝ, 0 < noiseVariance →
        noiseVariance < p.varianceBound →
          ∀ n : sampling_plan M,
            ∀ estimator : sampled_dataset K M n → (Fin K → ℝ),
              Measurable estimator →
                group_risk_integrable p n estimator →
                ∀ hrisk : BddAbove {s : ℝ | ∃ P,
                    bounded_conditional_mean_class p P ∧
                    s = group_means_risk p n estimator P},
                  (∑ z, noiseVariance /
                      (plan_expected_group_count_local p n z +
                        noiseVariance * priorInformation)) ≤
                    group_worst_case_risk p n estimator hrisk := by
  let a := p.meanRadius / 2
  have ha : 0 < a := by
    dsimp only [a]
    linarith
  have haR : a ≤ p.meanRadius := by
    dsimp only [a]
    linarith
  refine ⟨10 / a ^ 2, by positivity, ?_⟩
  intro noiseVariance hnoise hnoiseR n estimator hmeas hriskint hrisk
  let v : NNReal := ⟨noiseVariance, le_of_lt hnoise⟩
  have hv : 0 < v := by
    exact_mod_cast hnoise
  have hvcoe : (v : ℝ) = noiseVariance := rfl
  have hvR : (v : ℝ) < p.varianceBound := by
    rw [hvcoe]
    exact hnoiseR
  have hgroup := compact_gaussian_joint_group_loss_bound_refinement
    p n estimator hmeas hriskint hrisk a ha haR v hv hvR
  have herr : ∀ z, Integrable
      (fun x : (Fin K → ℝ) × sampled_dataset K M n =>
        (estimator x.2 z - x.1 z) ^ 2)
      (compact_gaussian_joint_measure_refinement p n a v) := by
    intro z
    have hemeas : Measurable
        (fun x : (Fin K → ℝ) × sampled_dataset K M n =>
          (estimator x.2 z - x.1 z) ^ 2) :=
      (((((measurable_pi_apply z).comp hmeas).comp measurable_snd).sub
        ((measurable_pi_apply z).comp measurable_fst)).pow_const 2)
    apply hgroup.1.mono' hemeas.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum
      (fun j _ => sq_nonneg (estimator x.2 j - x.1 j))
      (Finset.mem_univ z)
  have hcoord : ∀ z,
      noiseVariance /
          (plan_expected_group_count_local p n z +
            noiseVariance * (10 / a ^ 2)) ≤
        ∫ x, (estimator x.2 z - x.1 z) ^ 2
          ∂compact_gaussian_joint_measure_refinement p n a v := by
    intro z
    have hz := compact_gaussian_coordinate_information_refinement
      p n estimator hmeas a ha v hv z (herr z)
    rw [hvcoe] at hz
    exact hz
  calc
    (∑ z, noiseVariance /
        (plan_expected_group_count_local p n z +
          noiseVariance * (10 / a ^ 2))) ≤
        ∑ z, ∫ x, (estimator x.2 z - x.1 z) ^ 2
          ∂compact_gaussian_joint_measure_refinement p n a v :=
      Finset.sum_le_sum fun z hz => hcoord z
    _ = ∫ x, ∑ z, (estimator x.2 z - x.1 z) ^ 2
          ∂compact_gaussian_joint_measure_refinement p n a v := by
      symm
      simpa only [Finset.sum_apply] using
        MeasureTheory.integral_finsetSum
          (μ := compact_gaussian_joint_measure_refinement p n a v)
          (f := fun z x => (estimator x.2 z - x.1 z) ^ 2)
          Finset.univ (fun z hz => herr z)
    _ ≤ group_worst_case_risk p n estimator hrisk := hgroup.2

@[blueprint "lem:heterogeneous-gaussian-bayes-risk-lower-bound"
  (statement := /-- Let $K$ and $M$ be positive integers, and let $p$ be a biased-source mean-estimation problem with mean radius $R>0$ and variance bound $\sigma^2>0$. There exists a constant $I_\pi>0$ such that, for all sufficiently large real $B$, every sampling plan $n$, every measurable vector estimator $\widehat\mu$ whose squared group loss is integrable under every model in $\mathcal P_p(R,\sigma^2)$, and every witness that its set of model-class risks is bounded above satisfy
  \[
  \sum_{z\in[K]}\frac{(1-B^{-1})\sigma^2}
  {\lambda_z(n)+(1-B^{-1})\sigma^2I_\pi}
  \leq \sup_{P\in\mathcal P_p(R,\sigma^2)}
  \operatorname{Risk}_{\mathrm{GM}}((n,\widehat\mu),P).
  \]
  Here the supremum is the real supremum determined by the chosen boundedness witness. -/)
  (proof := /-- Apply \cref{lem:compact-product-prior-information-inequality} and retain its constant $I_\pi$. Since $\sigma^2>0$, the inequalities $0<(1-B^{-1})\sigma^2<\sigma^2$ hold for all sufficiently large $B$. On that eventual set, substitute $v_B=(1-B^{-1})\sigma^2$ into the finite-plan information inequality. Its quantifiers are uniform in the plan, the estimator, the integrability witness, and the boundedness witness, so the resulting eventual assertion has precisely the stated simultaneous scope. -/)
  (title := /-- Heterogeneous Gaussian Bayes-risk lower bound -/)
  (latexEnv := "lemma")]
lemma heterogeneous_gaussian_bayes_risk_lower_bound
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (hmean : 0 < p.meanRadius)
    (hvar : 0 < p.varianceBound) :
    ∃ priorInformation : ℝ, 0 < priorInformation ∧
      ∀ᶠ B in Filter.atTop,
        ∀ n : sampling_plan M,
          ∀ estimator : sampled_dataset K M n → (Fin K → ℝ),
            Measurable estimator →
              group_risk_integrable p n estimator →
              ∀ hrisk : BddAbove {s : ℝ | ∃ P,
                  bounded_conditional_mean_class p P ∧
                  s = group_means_risk p n estimator P},
                (∑ z, ((1 - B⁻¹) * p.varianceBound) /
                    (plan_expected_group_count_local p n z +
                      ((1 - B⁻¹) * p.varianceBound) * priorInformation)) ≤
                  group_worst_case_risk p n estimator hrisk := by
  rcases compact_product_prior_information_inequality p hmean hvar with
    ⟨priorInformation, hpriorInformation, hbound⟩
  refine ⟨priorInformation, hpriorInformation, ?_⟩
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with B hBlarge
  have hBpos : 0 < B := lt_trans (by norm_num) hBlarge
  have hnoise : 0 < (1 - B⁻¹) * p.varianceBound := by
    apply mul_pos _ hvar
    have hBinv : B⁻¹ < 1 := by
      rw [inv_lt_one₀ hBpos]
      exact hBlarge
    linarith
  have hnoiseR : (1 - B⁻¹) * p.varianceBound < p.varianceBound := by
    apply mul_lt_of_lt_one_left hvar
    exact sub_lt_self 1 (inv_pos.mpr hBpos)
  exact hbound ((1 - B⁻¹) * p.varianceBound) hnoise hnoiseR

@[blueprint "lem:uniform-regularized-harmonic-lower-refinement"
  (statement := /-- Let $K$ and $M$ be positive integers, let $p$ be a biased-source mean-estimation problem, let $n\in\mathbb N^M$, and put $u_K(z)=K^{-1}$. Fix $a>0$ and $x\geq0$. If $x\leq\sum_z u_K(z)^2/\lambda_z(n)$ whenever $n$ is nonempty and supports $u_K$, then
  \[
  \frac{x}{1+aK^2x}\leq
  \sum_{z\in[K]}\frac{u_K(z)^2}{\lambda_z(n)+a}.
  \] -/)
  (proof := /-- Suppose first that $n$ supports $u_K$. Since every coordinate of $u_K$ is positive, the plan is nonempty, and \cref{lem:expected-group-count-positive-of-supported-local} gives $\lambda_z(n)>0$ for every $z$. Writing $H=\sum_z u_K(z)^2/\lambda_z(n)$, each summand is at most $H$; because $u_K(z)=K^{-1}$, this implies $\lambda_z(n)^{-1}\leq K^2H$. Hence
  \[
  \frac{u_K(z)^2}{\lambda_z(n)}\leq
  (1+aK^2H)\frac{u_K(z)^2}{\lambda_z(n)+a}.
  \]
  Summing and using the monotonicity of $t\mapsto t/(1+aK^2t)$ on $[0,\infty)$ gives the result from $x\leq H$.

  If $n$ does not support $u_K$, choose $z$ whose mixture mass is zero. Nonnegativity from \cref{lem:plan-expected-group-count-nonnegative-local} forces $\lambda_z(n)=0$. The corresponding regularized summand is $1/(aK^2)$, while $x/(1+aK^2x)\leq1/(aK^2)$; all remaining summands are nonnegative by the same lemma. -/)
  (title := /-- Uniform regularized harmonic lower comparison -/)
  (latexEnv := "lemma")]
lemma uniform_regularized_harmonic_lower_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (n : sampling_plan M)
    (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x)
    (hcompare : target_supported_by_plan p n (uniform_group_mass K) →
      plan_total_samples n ≠ 0 →
      x ≤ unregularized_plan_harmonic_local p n (uniform_group_mass K)) :
    x / (1 + a * (K : ℝ) ^ 2 * x) ≤
      ∑ z, (uniform_group_mass K z) ^ 2 /
        (plan_expected_group_count_local p n z + a) := by
  let u : Fin K → ℝ := uniform_group_mass K
  let κ : ℝ := (K : ℝ) ^ 2
  let H := unregularized_plan_harmonic_local p n u
  have hK : 0 < (K : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  have hκ : 0 < κ := sq_pos_of_pos hK
  have hu : ∀ z, 0 < u z := by
    intro z
    dsimp only [u]
    unfold uniform_group_mass
    exact one_div_pos.mpr hK
  by_cases hsupp : target_supported_by_plan p n u
  · have hn : plan_total_samples n ≠ 0 := by
      intro hn
      rcases (Finset.univ_nonempty : (Finset.univ : Finset (Fin K)).Nonempty) with
        ⟨z, hz⟩
      have hm := hsupp z (hu z)
      unfold source_mixture_mass at hm
      simp [hn] at hm
    have hlam : ∀ z, 0 < plan_expected_group_count_local p n z := by
      intro z
      exact expected_group_count_positive_of_supported_local p n u hn hsupp z (hu z)
    have hHpos : 0 < H := by
      dsimp only [H]
      unfold unregularized_plan_harmonic_local
      apply Finset.sum_pos
      · intro z hz
        rw [if_neg (ne_of_gt (hu z))]
        exact div_pos (sq_pos_of_pos (hu z)) (hlam z)
      · exact Finset.univ_nonempty
    have hAH : H / (1 + a * κ * H) ≤
        ∑ z, (u z) ^ 2 /
          (plan_expected_group_count_local p n z + a) := by
      have hden : 0 < 1 + a * κ * H := by positivity
      apply (div_le_iff₀ hden).2
      change H ≤ (∑ z, (u z) ^ 2 /
        (plan_expected_group_count_local p n z + a)) * (1 + a * κ * H)
      conv_lhs =>
        rw [show H = ∑ z, if u z = 0 then 0
          else (u z) ^ 2 / plan_expected_group_count_local p n z by rfl]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro z hz
      have htermle : (u z) ^ 2 /
          plan_expected_group_count_local p n z ≤ H := by
        dsimp only [H]
        unfold unregularized_plan_harmonic_local
        simp_rw [if_neg (ne_of_gt (hu _))]
        exact Finset.single_le_sum
          (fun j _ => le_of_lt
            (div_pos (sq_pos_of_pos (hu j)) (hlam j)))
          (Finset.mem_univ z)
      have hinv : 1 / plan_expected_group_count_local p n z ≤ κ * H := by
        dsimp only [u, κ] at htermle ⊢
        unfold uniform_group_mass at htermle
        field_simp [ne_of_gt hK, ne_of_gt (hlam z)] at htermle ⊢
        nlinarith
      rw [if_neg (ne_of_gt (hu z))]
      have hdenz : 0 < plan_expected_group_count_local p n z + a := by
        linarith [hlam z]
      have hratio :
          (plan_expected_group_count_local p n z + a) /
              plan_expected_group_count_local p n z ≤
            1 + a * κ * H := by
        calc
          (plan_expected_group_count_local p n z + a) /
                plan_expected_group_count_local p n z =
              1 + a * (1 / plan_expected_group_count_local p n z) := by
            field_simp [ne_of_gt (hlam z)]
          _ ≤ 1 + a * (κ * H) := by gcongr
          _ = 1 + a * κ * H := by ring
      calc
        (u z) ^ 2 / plan_expected_group_count_local p n z =
            ((u z) ^ 2 /
              (plan_expected_group_count_local p n z + a)) *
              ((plan_expected_group_count_local p n z + a) /
                plan_expected_group_count_local p n z) := by
          field_simp [ne_of_gt (hlam z), ne_of_gt hdenz]
        _ ≤ ((u z) ^ 2 /
              (plan_expected_group_count_local p n z + a)) *
              (1 + a * κ * H) := by
          exact mul_le_mul_of_nonneg_left hratio
            (div_nonneg (sq_nonneg _) (le_of_lt hdenz))
    have hxH : x ≤ H := hcompare hsupp hn
    have hdenx : 0 < 1 + a * κ * x := by positivity
    have hdenH : 0 < 1 + a * κ * H := by positivity
    have hmono : x / (1 + a * κ * x) ≤ H / (1 + a * κ * H) := by
      apply (div_le_div_iff₀ hdenx hdenH).2
      nlinarith
    simpa [u, κ] using le_trans hmono hAH
  · unfold target_supported_by_plan at hsupp
    push Not at hsupp
    rcases hsupp with ⟨z, hz, hmix⟩
    have hmixnonneg : 0 ≤ source_mixture_mass p n z := by
      unfold source_mixture_mass
      split_ifs
      · exact le_rfl
      · exact div_nonneg
          (plan_expected_group_count_nonnegative_local p n z)
          (Nat.cast_nonneg _)
    have hmixzero : source_mixture_mass p n z = 0 :=
      le_antisymm hmix hmixnonneg
    have hlamzero : plan_expected_group_count_local p n z = 0 := by
      by_cases hn : plan_total_samples n = 0
      · unfold plan_expected_group_count_local
        have hall : ∀ m, n m = 0 := by
          intro m
          have hm : n m ≤ plan_total_samples n := by
            unfold plan_total_samples
            exact Finset.single_le_sum (fun j _ => Nat.zero_le (n j))
              (Finset.mem_univ m)
          omega
        simp [hall]
      · unfold source_mixture_mass at hmixzero
        rw [if_neg hn] at hmixzero
        have hN : (plan_total_samples n : ℝ) ≠ 0 := by exact_mod_cast hn
        exact (div_eq_zero_iff.mp hmixzero).resolve_right hN
    have hdenx : 0 < 1 + a * κ * x := by positivity
    have hcap : x / (1 + a * κ * x) ≤ 1 / (a * κ) := by
      apply (div_le_div_iff₀ hdenx (mul_pos ha hκ)).2
      nlinarith
    calc
      x / (1 + a * κ * x) ≤ 1 / (a * κ) := hcap
      _ = (u z) ^ 2 /
          (plan_expected_group_count_local p n z + a) := by
        rw [hlamzero]
        simp only [zero_add]
        dsimp only [u, κ]
        unfold uniform_group_mass
        field_simp [ne_of_gt ha, ne_of_gt hK]
      _ ≤ ∑ j, (u j) ^ 2 /
          (plan_expected_group_count_local p n j + a) := by
        exact Finset.single_le_sum
          (fun j _ => div_nonneg (sq_nonneg _)
            (add_nonneg
              (plan_expected_group_count_nonnegative_local p n j)
              (le_of_lt ha)))
          (Finset.mem_univ z)

@[blueprint "lem:scaled-regularized-variance-remainder-little-o-refinement"
  (statement := /-- Let $\sigma,I,\kappa,K_0>0$, and suppose that $0<x(B)\leq K_0/B$ for all sufficiently large $B$. Then
  \[
  \kappa\left(
  \frac{(1-B^{-1})\sigma x(B)}
  {1+(1-B^{-1})\sigma I\kappa x(B)}-\sigma x(B)
  \right)=o(B^{-1}).
  \] -/)
  (proof := /-- The bound on $x$ squeezes $x(B)$ to zero. Since $B^{-1}\to0$, continuity of the rational function gives
  \[
  \frac{(1-B^{-1})\sigma}
  {1+(1-B^{-1})\sigma I\kappa x(B)}\longrightarrow\sigma.
  \]
  Factor the displayed remainder as $\kappa x(B)$ times the difference between this ratio and $\sigma$. Given $c>0$, the ratio difference is eventually at most $c/(\kappa K_0)$ in absolute value, while $x(B)\leq K_0/B$; their product is therefore at most $c/B$, which is the defining little-o estimate relative to \cref{def:inverse-budget-rate}. -/)
  (title := /-- Little-o regularized variance correction -/)
  (latexEnv := "lemma")]
lemma scaled_regularized_variance_remainder_little_o_refinement
    (σ I κ K₀ : ℝ) (x : ℝ → ℝ)
    (hσ : 0 < σ) (hI : 0 < I) (hκ : 0 < κ) (hK₀ : 0 < K₀)
    (hxbound : ∀ᶠ B in Filter.atTop, 0 < x B ∧ x B ≤ K₀ / B) :
    (fun B => κ * (((1 - B⁻¹) * σ * x B) /
      (1 + (1 - B⁻¹) * σ * I * κ * x B) - σ * x B))
      =o[Filter.atTop] inverse_budget_rate := by
  have hinv : Filter.Tendsto (fun B : ℝ => B⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have hupper : Filter.Tendsto (fun B : ℝ => K₀ / B)
      Filter.atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul hinv :
      Filter.Tendsto (fun B : ℝ => K₀ * B⁻¹)
        Filter.atTop (nhds (K₀ * 0))) using 1 <;>
      simp [div_eq_mul_inv]
  have hxzero : Filter.Tendsto x Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
    · filter_upwards [hxbound] with B hB
      exact le_of_lt hB.1
    · filter_upwards [hxbound] with B hB
      exact hB.2
  have hv : Filter.Tendsto (fun B : ℝ => (1 - B⁻¹) * σ)
      Filter.atTop (nhds σ) := by
    convert (tendsto_const_nhds.sub hinv).mul_const σ using 1 <;> norm_num
  have hden : Filter.Tendsto
      (fun B : ℝ => 1 + (1 - B⁻¹) * σ * I * κ * x B)
      Filter.atTop (nhds 1) := by
    convert tendsto_const_nhds.add
      (((hv.mul_const I).mul_const κ).mul hxzero) using 1 <;> norm_num
  have hratio : Filter.Tendsto
      (fun B : ℝ => ((1 - B⁻¹) * σ) /
        (1 + (1 - B⁻¹) * σ * I * κ * x B))
      Filter.atTop (nhds σ) := by
    convert hv.div hden (by norm_num : (1 : ℝ) ≠ 0) using 1
    · funext B
      rfl
    · simp
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hcscale : 0 < c / (κ * K₀) := div_pos hc (mul_pos hκ hK₀)
  have herr := (Metric.tendsto_nhds.1 hratio) (c / (κ * K₀)) hcscale
  filter_upwards [hxbound, herr,
    Filter.eventually_gt_atTop (0 : ℝ)] with B hB he hBpos
  rw [show κ * (((1 - B⁻¹) * σ * x B) /
      (1 + (1 - B⁻¹) * σ * I * κ * x B) - σ * x B) =
      κ * x B * (((1 - B⁻¹) * σ) /
        (1 + (1 - B⁻¹) * σ * I * κ * x B) - σ) by ring]
  simp only [Real.norm_eq_abs, inverse_budget_rate]
  rw [abs_mul, abs_mul, abs_of_pos hκ, abs_of_pos hB.1,
    abs_of_pos (one_div_pos.2 hBpos)]
  have herrabs :
      |((1 - B⁻¹) * σ) /
          (1 + (1 - B⁻¹) * σ * I * κ * x B) - σ| ≤
        c / (κ * K₀) := by
    simpa [Real.dist_eq] using le_of_lt he
  calc
    κ * x B * |((1 - B⁻¹) * σ) /
        (1 + (1 - B⁻¹) * σ * I * κ * x B) - σ| ≤
        κ * (K₀ / B) * (c / (κ * K₀)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hB.2 (le_of_lt hκ)) herrabs
        (abs_nonneg _)
        (mul_nonneg (le_of_lt hκ) (le_trans (le_of_lt hB.1) hB.2))
    _ = c * (1 / B) := by
      field_simp [ne_of_gt hκ, ne_of_gt hK₀, ne_of_gt hBpos]

@[blueprint "lem:uniform-heterogeneous-information-asymptotics"
  (statement := /-- Let $K$ and $M$ be positive integers, let $p$ be a biased-source mean-estimation problem with variance bound $\sigma^2>0$, and let $n_U\colon\mathbb R\to\mathbb N^M$ be such that, for every $B>0$, the plan $n_U(B)$ maximizes the effective sample size for the uniform mass $u_K$ among all integer plans of cost at most $B$. For every fixed $I>0$, there exists a function $a_I\colon\mathbb R\to\mathbb R$ satisfying $a_I(B)=o(B^{-1})$ as $B\to\infty$ such that, for all sufficiently large real $B$ and every integer plan $n\in\mathbb N^M$ of cost at most $B$,
  \[
  \frac{K^2\sigma^2\bar c(n_U(B))D(u_K,\bar q_{n_U(B)})}{B}+a_I(B)
  \leq
  \sum_{z\in[K]}\frac{(1-B^{-1})\sigma^2}
  {\lambda_z(n)+(1-B^{-1})\sigma^2I}.
  \]
  The remainder is independent of $n$. -/)
  (proof := /-- Realize $u_K$ as a probability mass function and replace the target-group field of $p$ by this law, leaving the source laws, costs, and variance bound unchanged. Set
  \[
  x(B)=\frac{C(n_U(B))}{B}
  \sum_{z\in[K]}\frac{u_K(z)^2}{\lambda_z(n_U(B))},
  \qquad \kappa=K^2.
  \]
  The one-round plan taking one observation from every source supports $u_K$ by \cref{lem:uniform-source-plan-support-local}; its harmonic quantity is positive by \cref{lem:unregularized-plan-harmonic-positive-local}, and its cost is positive by \cref{lem:total-source-cost-positive-local}. Consequently \cref{lem:normalized-optimal-harmonic-eventual-bound-local} provides a constant $K_0>0$ such that, eventually,
  \[
  0<x(B)\leq K_0/B.
  \]

  Put $v_B=(1-B^{-1})\sigma^2$ and define
  \[
  a_I(B)=\kappa\left(
  \frac{v_Bx(B)}{1+v_BI\kappa x(B)}-\sigma^2x(B)
  \right).
  \]
  By \cref{lem:scaled-regularized-variance-remainder-little-o-refinement}, this function is $o(B^{-1})$.

  Fix a sufficiently large $B$ and a budget-feasible plan $n$. The comparison in \cref{lem:normalized-optimal-harmonic-comparison-local} shows that, whenever $n$ is nonempty and supports $u_K$,
  \[
  x(B)\leq\sum_z\frac{u_K(z)^2}{\lambda_z(n)}.
  \]
  Applying \cref{lem:uniform-regularized-harmonic-lower-refinement} with $a=v_BI$ gives, without any support assumption on $n$,
  \[
  \frac{x(B)}{1+v_BI K^2x(B)}
  \leq\sum_z\frac{u_K(z)^2}{\lambda_z(n)+v_BI}.
  \]
  Multiplication by $K^2v_B$ turns the right-hand side into
  $\sum_zv_B/(\lambda_z(n)+v_BI)$. Finally,
  \cref{lem:population-leading-risk-normalized-harmonic-local} identifies the selected group leading term with $K^2\sigma^2x(B)$. Adding the displayed definition of $a_I(B)$ therefore yields the asserted inequality, uniformly over all feasible $n$. -/)
  (title := /-- Uniform heterogeneous information asymptotics -/)
  (latexEnv := "lemma")]
lemma uniform_heterogeneous_information_asymptotics
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (hvar : 0 < p.varianceBound)
    (plans : ℝ → sampling_plan M)
    (hplans : ∀ B, 0 < B →
      optimal_sampling_plan p (uniform_group_mass K) B (plans B))
    (priorInformation : ℝ) (hpriorInformation : 0 < priorInformation) :
    ∃ remainder : ℝ → ℝ,
      Asymptotics.IsLittleO Filter.atTop remainder inverse_budget_rate ∧
      ∀ᶠ B in Filter.atTop,
        ∀ n : sampling_plan M, budget_feasible_plan p B n →
          group_leading_risk p (plans B) B + remainder B ≤
            ∑ z, ((1 - B⁻¹) * p.varianceBound) /
              (plan_expected_group_count_local p n z +
                ((1 - B⁻¹) * p.varianceBound) * priorInformation) := by
  let u : PMF (Fin K) :=
    ⟨fun _ => (K : ENNReal)⁻¹, by
      convert hasSum_fintype (fun _ : Fin K => (K : ENNReal)⁻¹) using 1 <;> simp
      exact (ENNReal.mul_inv_cancel (NeZero.natCast_ne K ENNReal)
        (ENNReal.natCast_ne_top K)).symm⟩
  let pu : biased_source_mean_problem K M := { p with targetGroup := u }
  have hu : (fun z => pmf_real_mass u z) = uniform_group_mass K := by
    funext z
    change ((K : ENNReal)⁻¹).toReal = (1 : ℝ) / K
    rw [ENNReal.toReal_inv]
    simp
  have hplansu : ∀ B, 0 < B →
      optimal_sampling_plan pu
        (fun z => pmf_real_mass pu.targetGroup z) B (plans B) := by
    intro B hB
    simpa [pu, hu, optimal_sampling_plan, budget_feasible_plan,
      effective_sample_size, target_supported_by_plan, source_mixture_mass,
      plan_discrepancy, plan_cost] using hplans B hB
  let x : ℝ → ℝ := normalized_optimal_harmonic_local pu plans
  let κ : ℝ := (K : ℝ) ^ 2
  let K₀ := 2 * total_source_cost_local pu *
    unregularized_plan_harmonic_local pu (uniform_source_plan_local 1)
      (fun z => pmf_real_mass pu.targetGroup z)
  have hκ : 0 < κ := by
    dsimp only [κ]
    exact sq_pos_of_pos (by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K))
  have hH₁ : 0 < unregularized_plan_harmonic_local pu
      (uniform_source_plan_local 1)
      (fun z => pmf_real_mass pu.targetGroup z) := by
    exact unregularized_plan_harmonic_positive_local pu
      (uniform_source_plan_local 1) u
      (by
        unfold plan_total_samples uniform_source_plan_local
        simp [NeZero.ne M])
      (by
        simpa [pu] using
          (uniform_source_plan_support_local pu
            (fun z => pmf_real_mass u z) 1 Nat.zero_lt_one))
  have hK₀ : 0 < K₀ := by
    dsimp only [K₀]
    exact mul_pos
      (mul_pos (by norm_num) (total_source_cost_positive_local pu)) hH₁
  have hxbound : ∀ᶠ B in Filter.atTop, 0 < x B ∧ x B ≤ K₀ / B := by
    simpa [x, K₀] using
      normalized_optimal_harmonic_eventual_bound_local pu plans hplansu
  let remainder : ℝ → ℝ := fun B => κ *
    (((1 - B⁻¹) * p.varianceBound * x B) /
      (1 + (1 - B⁻¹) * p.varianceBound * priorInformation * κ * x B) -
      p.varianceBound * x B)
  have hremainder :
      Asymptotics.IsLittleO Filter.atTop remainder inverse_budget_rate := by
    dsimp only [remainder]
    exact scaled_regularized_variance_remainder_little_o_refinement
      p.varianceBound priorInformation κ K₀ x hvar hpriorInformation hκ hK₀ hxbound
  refine ⟨remainder, hremainder, ?_⟩
  filter_upwards [hxbound,
    Filter.eventually_ge_atTop (total_source_cost_local pu),
    Filter.eventually_gt_atTop (1 : ℝ)] with B hx hBcover hBlarge
  have hBpos : 0 < B := lt_trans (by norm_num) hBlarge
  have hv : 0 < (1 - B⁻¹) * p.varianceBound := by
    apply mul_pos _ hvar
    have hBinv : B⁻¹ < 1 := by
      rw [inv_lt_one₀ hBpos]
      exact hBlarge
    linarith
  have hopt := hplansu B hBpos
  have hcomp := normalized_optimal_harmonic_comparison_local pu plans B
    hBpos hBcover hopt
  dsimp only at hcomp
  have hlead : group_leading_risk p (plans B) B =
      κ * p.varianceBound * x B := by
    calc
      group_leading_risk p (plans B) B =
          κ * population_leading_risk pu (plans B) B := by
        simp [group_leading_risk, population_leading_risk, pu, hu, κ,
          plan_discrepancy, source_mixture_mass]
        ring
      _ = κ * p.varianceBound * x B := by
        rw [population_leading_risk_normalized_harmonic_local
          pu plans B hBcover hopt]
        simp [pu, x]
        ring
  intro n hnfeas
  have hnfeasu : budget_feasible_plan pu B n := by
    simpa [pu, budget_feasible_plan, plan_cost] using hnfeas
  have hreg := uniform_regularized_harmonic_lower_refinement pu n
    ((1 - B⁻¹) * p.varianceBound * priorInformation) (x B)
    (mul_pos hv hpriorInformation) (le_of_lt hx.1)
    (by
      intro hsupp hn
      have hsuppu : target_supported_by_plan pu n
          (fun z => pmf_real_mass pu.targetGroup z) := by
        simpa [pu, hu] using hsupp
      have h := hcomp.2.2 n hnfeasu hsuppu hn
      simpa [pu, hu] using h)
  have hmul := mul_le_mul_of_nonneg_left hreg
    (mul_nonneg (le_of_lt hκ) (le_of_lt hv))
  have hscale : κ * ((1 - B⁻¹) * p.varianceBound) *
      (∑ z, (uniform_group_mass K z) ^ 2 /
        (plan_expected_group_count_local pu n z +
          (1 - B⁻¹) * p.varianceBound * priorInformation)) =
      ∑ z, ((1 - B⁻¹) * p.varianceBound) /
        (plan_expected_group_count_local p n z +
          ((1 - B⁻¹) * p.varianceBound) * priorInformation) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    dsimp only [κ]
    unfold uniform_group_mass
    simp only [pu, plan_expected_group_count_local]
    field_simp [NeZero.natCast_ne K ℝ]
  rw [hscale] at hmul
  have hbound : κ *
      (((1 - B⁻¹) * p.varianceBound * x B) /
        (1 + (1 - B⁻¹) * p.varianceBound * priorInformation * κ * x B)) ≤
      ∑ z, ((1 - B⁻¹) * p.varianceBound) /
        (plan_expected_group_count_local p n z +
          ((1 - B⁻¹) * p.varianceBound) * priorInformation) := by
    dsimp only [κ] at hmul ⊢
    simpa only [mul_div_assoc, mul_assoc] using hmul
  rw [hlead]
  dsimp only [remainder]
  rw [show κ * p.varianceBound * x B +
      κ * (((1 - B⁻¹) * p.varianceBound * x B) /
        (1 + (1 - B⁻¹) * p.varianceBound * priorInformation * κ * x B) -
        p.varianceBound * x B) =
      κ * (((1 - B⁻¹) * p.varianceBound * x B) /
        (1 + (1 - B⁻¹) * p.varianceBound * priorInformation * κ * x B)) by
    ring]
  exact hbound

@[blueprint "lem:heterogeneous-product-multivariate-bayesian-information-lower-bound"
  (statement := /-- Let $K$ and $M$ be positive integers, let $p$ be a biased-source mean-estimation problem with mean radius $R>0$, and let $n_U(B)$ maximize the effective sample size of the uniform mass $u_K$ among all integer plans of cost at most $B$, for every $B>0$. There exists a function $e\colon\mathbb R\to\mathbb R$ such that $e(B)=o(B^{-1})$ and, for all sufficiently large $B$, the following assertion holds simultaneously for every budget-feasible plan $n$, every measurable estimator $\widehat\mu$ of the $K$ conditional means whose squared loss is integrable under every model in $\mathcal P_p(R,\sigma^2)$, and every proof that the risks of $\widehat\mu$ over this class are bounded above:
  \[
  \frac{K^2\sigma^2\bar c(n_U(B))D(u_K,\bar q_{n_U(B)})}{B}+e(B)
  \leq \sup_{P\in\mathcal P_p(R,\sigma^2)}
  \operatorname{Risk}_{\mathrm{GM}}((n,\widehat\mu),P).
  \]
  Thus the remainder is uniform both in the heterogeneous integer allocation and in every finite-risk, possibly biased estimator. -/)
  (proof := /-- If $\sigma^2=0$, the leading term in \cref{def:group-leading-risk} vanishes. Let $P_0$ be the Gaussian conditional model with zero mean vector and zero variance. It belongs to the bounded conditional-mean class by \cref{lem:compact-gaussian-location-model-in-class-refinement}. Its risk, defined in \cref{def:group-means-risk}, is the integral of a finite sum of squares and is therefore nonnegative. Since this risk is a member of the set whose supremum is \cref{def:group-worst-case-risk}, that supremum is nonnegative. Thus the identically zero remainder gives the conclusion.

  Suppose that $\sigma^2>0$. By \cref{lem:heterogeneous-gaussian-bayes-risk-lower-bound}, there is a constant $I_\pi>0$ and an eventual set of budgets on which the worst-case risk of every measurable estimator satisfying \cref{def:group-risk-integrable} under every plan dominates the regularized harmonic sum
  \[
  \sum_z\frac{(1-B^{-1})\sigma^2}
  {\lambda_z(n)+(1-B^{-1})\sigma^2I_\pi}.
  \]
  Apply \cref{lem:uniform-heterogeneous-information-asymptotics} with this $I_\pi$. It supplies a function $e=o(B^{-1})$ and an eventual set on which the selected uniform-optimal leading term plus $e(B)$ is at most the same regularized harmonic sum for every budget-feasible plan. Intersect the two eventual sets. Transitivity of the two inequalities then gives, simultaneously for every feasible plan, measurable estimator, integrability witness, and boundedness witness, the asserted lower bound by its worst-case group-means risk. -/)
  (title := /-- Uniform multivariate Bayesian information bound for heterogeneous sampling -/)
  (latexEnv := "lemma")]
lemma heterogeneous_product_multivariate_bayesian_information_lower_bound
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (hmean : 0 < p.meanRadius)
    (plans : ℝ → sampling_plan M)
    (hplans : ∀ B, 0 < B →
      optimal_sampling_plan p (uniform_group_mass K) B (plans B)) :
    ∃ remainder : ℝ → ℝ,
      Asymptotics.IsLittleO Filter.atTop remainder inverse_budget_rate ∧
      ∀ᶠ B in Filter.atTop,
        ∀ n : sampling_plan M, budget_feasible_plan p B n →
          ∀ estimator : sampled_dataset K M n → (Fin K → ℝ),
            Measurable estimator →
              group_risk_integrable p n estimator →
              ∀ hrisk : BddAbove {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
                  s = group_means_risk p n estimator P},
                group_leading_risk p (plans B) B + remainder B ≤
                  group_worst_case_risk p n estimator hrisk := by
  by_cases hvarzero : p.varianceBound = 0
  · refine ⟨fun _ => 0,
      Asymptotics.isLittleO_zero inverse_budget_rate Filter.atTop, ?_⟩
    filter_upwards with B
    intro n hn estimator hmeas hriskint hrisk
    have hlead : group_leading_risk p (plans B) B = 0 := by
      simp [group_leading_risk, hvarzero]
    rw [hlead, zero_add]
    let μ0 : Fin K → ℝ := fun _ => 0
    let P0 : conditional_outcome_model K :=
      compact_gaussian_location_model_refinement μ0 0
    have hP0 : bounded_conditional_mean_class p P0 := by
      apply compact_gaussian_location_model_in_class_refinement p μ0 0
      · intro z
        simp [μ0, p.meanRadius_nonneg]
      · simpa using p.varianceBound_nonneg
    calc
      0 ≤ group_means_risk p n estimator P0 := by
        unfold group_means_risk
        exact MeasureTheory.integral_nonneg fun D =>
          Finset.sum_nonneg fun z hz => sq_nonneg _
      _ ≤ group_worst_case_risk p n estimator hrisk := by
        unfold group_worst_case_risk
        exact le_csSup hrisk ⟨P0, hP0, rfl⟩
  · have hvar : 0 < p.varianceBound :=
      lt_of_le_of_ne p.varianceBound_nonneg (Ne.symm hvarzero)
    obtain ⟨priorInformation, hpriorInformation, hbayes⟩ :=
      heterogeneous_gaussian_bayes_risk_lower_bound p hmean hvar
    obtain ⟨remainder, hremainder, hinformation⟩ :=
      uniform_heterogeneous_information_asymptotics p hvar plans hplans
        priorInformation hpriorInformation
    refine ⟨remainder, hremainder, ?_⟩
    filter_upwards [hbayes, hinformation] with B hbayesB hinformationB
    intro n hn estimator hmeas hriskint hrisk
    exact le_trans (hinformationB n hn)
      (hbayesB n estimator hmeas hriskint hrisk)

@[blueprint "lem:group-minimax-candidate-nonempty-local"
  (statement := /-- Let $K$ and $M$ be positive integers, let $p$ be a biased-source mean-estimation problem, and let $B\geq 0$. The set of finite worst-case risks over budget-feasible plans and measurable vector-valued estimators satisfying the integrability and bounded-risk conditions in the definition of the group minimax risk is nonempty. -/)
  (proof := /-- Take the zero sampling plan and the constant-zero vector estimator. The plan has zero cost and is therefore feasible. Under every conditional model, the loss is the constant $\sum_z\mu_P(z)^2$, so it is integrable under the probability sampling law. The bound $|\mu_P(z)|\leq R$ from \cref{def:bounded-conditional-mean-class} gives
  \[
  \sum_z\mu_P(z)^2\leq KR^2.
  \]
  Thus the model-class risk set is bounded above, and the associated worst-case risk is an element of the candidate set in \cref{def:group-minimax-risk}. -/)
  (title := /-- Nonemptiness of the group minimax candidate set -/)
  (latexEnv := "lemma")]
lemma group_minimax_candidate_nonempty_local
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (B : ℝ) (hB : 0 ≤ B) :
    {r : ℝ | ∃ n : sampling_plan M, budget_feasible_plan p B n ∧
      ∃ estimator : sampled_dataset K M n → (Fin K → ℝ), Measurable estimator ∧
        group_risk_integrable p n estimator ∧
        ∃ hrisk : BddAbove {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
          s = group_means_risk p n estimator P},
          r = group_worst_case_risk p n estimator hrisk}.Nonempty := by
  let n0 : sampling_plan M := fun _ => 0
  let estimator : sampled_dataset K M n0 → (Fin K → ℝ) := fun _ _ => 0
  have hnfeas : budget_feasible_plan p B n0 := by
    unfold budget_feasible_plan plan_cost n0
    simpa using hB
  have hsampling (P : conditional_outcome_model K) :
      IsProbabilityMeasure (sampling_law p n0 P) := by
    letI hsource : ∀ m, IsProbabilityMeasure
        (source_observation_law p P m) := fun m =>
      ⟨by
        unfold source_observation_law
        have heval : Measurable
            (fun x : Fin K × (Fin K → ℝ) => x.2 x.1) := by
          have heq : (fun x : Fin K × (Fin K → ℝ) => x.2 x.1) =
              fun x => ∑ z, if x.1 = z then x.2 z else 0 := by
            funext x
            simp
          rw [heq]
          apply Finset.measurable_sum
          intro z hz
          exact Measurable.ite
            (measurable_fst (MeasurableSet.singleton z))
            ((measurable_pi_apply z).comp measurable_snd)
            measurable_const
        have hf : Measurable
            (fun x : Fin K × (Fin K → ℝ) => (x.1, x.2 x.1)) :=
          measurable_fst.prodMk heval
        rw [Measure.map_apply_of_aemeasurable hf.aemeasurable
          MeasurableSet.univ]
        simp⟩
    unfold sampling_law
    infer_instance
  have hint : group_risk_integrable p n0 estimator := by
    rw [group_risk_integrable]
    intro P hP
    letI := hsampling P
    simpa [estimator] using
      (MeasureTheory.integrable_const
        (μ := sampling_law p n0 P)
        (∑ z, (0 - conditional_group_mean P z) ^ 2))
  have hrisk : BddAbove {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
      s = group_means_risk p n0 estimator P} := by
    refine ⟨(K : ℝ) * p.meanRadius ^ 2, ?_⟩
    intro s hs
    rcases hs with ⟨P, hP, rfl⟩
    have hsum : (∑ z, conditional_group_mean P z ^ 2) ≤
        (K : ℝ) * p.meanRadius ^ 2 := by
      calc
        (∑ z, conditional_group_mean P z ^ 2) ≤
            ∑ _z : Fin K, p.meanRadius ^ 2 := by
          apply Finset.sum_le_sum
          intro z hz
          have hm := mul_self_le_mul_self
            (abs_nonneg (conditional_group_mean P z)) (hP z).2.1
          nlinarith [sq_abs (conditional_group_mean P z)]
        _ = (K : ℝ) * p.meanRadius ^ 2 := by simp
    letI := hsampling P
    rw [group_means_risk]
    simp only [estimator, zero_sub, neg_sq]
    rw [MeasureTheory.integral_const]
    simpa using hsum
  exact ⟨group_worst_case_risk p n0 estimator hrisk,
    n0, hnfeas, estimator, measurable_const, hint, hrisk, rfl⟩

@[blueprint "lem:group-minimax-effective-sample-lower-bound"
  (statement := /-- Let $K$ and $M$ be positive integers, let $p$ be a biased-source mean-estimation problem with mean radius $R>0$, and let $n_U\colon\mathbb R\to\mathbb N^M$ be a family such that, for every $B>0$, the plan $n_U(B)$ is budget-feasible and maximizes the effective sample size for the uniform mass $u_K$ among all integer plans of cost at most $B$. Then there exists a function $\ell_{\mathrm{GM}}\colon\mathbb R\to\mathbb R$ such that $\ell_{\mathrm{GM}}(B)=o(B^{-1})$ as $B\to\infty$ and, for all sufficiently large $B$,
  \[
  \frac{K^2\sigma^2\bar c(n_U(B))D(u_K,\bar q_{n_U(B)})}{B}
  +\ell_{\mathrm{GM}}(B)
  \le \mathcal R^*_{\mathrm{GM}}(B,\mathcal P_p(R,\sigma^2)).
  \] -/)
  (proof := /-- Apply \cref{lem:heterogeneous-product-multivariate-bayesian-information-lower-bound} to the prescribed optimal family. It supplies a function $\ell_{\mathrm{GM}}=o(B^{-1})$ and, for every sufficiently large $B$, a lower bound by the selected leading term plus $\ell_{\mathrm{GM}}(B)$ for the worst-case risk of every measurable finite-risk vector estimator under every budget-feasible plan.

  Restrict further to sufficiently large nonnegative budgets and unfold the infimum in \cref{def:group-minimax-risk}. Its candidate set is nonempty by \cref{lem:group-minimax-candidate-nonempty-local}. Every member of that set comes with a budget-feasible plan, a measurable estimator, the integrability condition \cref{def:group-risk-integrable}, and a boundedness witness. The uniform bound above therefore places the selected leading term plus $\ell_{\mathrm{GM}}(B)$ below every member, so the defining lower-bound property of the real infimum gives
  \[
  \frac{K^2\sigma^2\bar c(n_U(B))D(u_K,\bar q_{n_U(B)})}{B}
  +\ell_{\mathrm{GM}}(B)
  \leq \mathcal R^*_{\mathrm{GM}}(B,\mathcal P_p(R,\sigma^2)).
  \]
  This is the required eventual inequality, with the same little-o remainder. -/)
  (title := /-- Group minimax lower bound at a uniform-optimal plan -/)
  (latexEnv := "lemma")]
lemma group_minimax_effective_sample_lower_bound {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (hmean : 0 < p.meanRadius)
    (plans : ℝ → sampling_plan M)
    (hplans : ∀ B, 0 < B →
      optimal_sampling_plan p (uniform_group_mass K) B (plans B)) :
    ∃ remainder : ℝ → ℝ,
      Asymptotics.IsLittleO Filter.atTop remainder inverse_budget_rate ∧
      ∀ᶠ B in Filter.atTop,
        group_leading_risk p (plans B) B + remainder B ≤
          group_minimax_risk p B := by
  obtain ⟨remainder, hremainder, hlower⟩ :=
    heterogeneous_product_multivariate_bayesian_information_lower_bound
      p hmean plans hplans
  refine ⟨remainder, hremainder, ?_⟩
  filter_upwards [hlower, Filter.eventually_ge_atTop (0 : ℝ)] with
    B hlowerB hB
  rw [group_minimax_risk]
  apply le_csInf
  · exact group_minimax_candidate_nonempty_local p B hB
  · intro r hr
    rcases hr with ⟨n, hn, estimator, hmeas, hint, hrisk, rfl⟩
    exact hlowerB n hn estimator hmeas hint hrisk

@[blueprint "lem:group-vector-risk-uniform-second-order-refinement"
  (statement := /-- Let $K$ and $M$ be positive integers, let $p$ be a biased-source mean-estimation problem, and let $n_U\colon\mathbb R\to\mathbb N^M$ be uniform-effective-sample-size optimal at every positive budget. There is a nonnegative constant $A$ such that, for all sufficiently large $B$ and every $P\in\mathcal P_p(R,\sigma^2)$,
  \[
  \operatorname{Risk}_{\mathrm{GM}}((n_U(B),\widehat\theta_{\mathrm{VM}}),P)
  \le L_{\mathrm{GM}}(n_U(B),B)+\frac{A}{B^2}.
  \] -/)
  (proof := /-- Replace the target law by the uniform law. The resulting plans remain optimal, so \cref{lem:population-minimax-uniform-post-stratified-risk-upper-local} gives a single second-order constant, uniform over the bounded model class. For each sign vector, push every group outcome forward by multiplication by its sign. This transformation preserves the model class and sends the sampling law to the corresponding signed sampling law. The scalar post-stratified error for the signed model is the signed uniform average of the coordinate errors. Averaging its square over all sign vectors cancels the cross terms and, after multiplication by $K^2$, equals the vector squared loss. Measurability follows from \cref{lem:post-stratified-estimator-measurable,lem:vector-of-means-estimator-measurable}, while \cref{lem:vector-of-means-group-risk-integrable} justifies the finite-sum integral identities. Summing the uniform scalar bounds gives the asserted vector bound with a nonnegative inverse-square constant. -/)
  (title := /-- Uniform second-order vector-of-means risk bound -/)
  (latexEnv := "lemma")]
lemma group_vector_risk_uniform_second_order_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (plans : ℝ → sampling_plan M)
    (hplans : ∀ B, 0 < B →
      optimal_sampling_plan p (uniform_group_mass K) B (plans B)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ B in Filter.atTop, ∀ P,
      bounded_conditional_mean_class p P →
        group_means_risk p (plans B) vector_of_means_estimator P ≤
          group_leading_risk p (plans B) B + A / B ^ 2 := by
  let u : PMF (Fin K) :=
    ⟨fun _ => (K : ENNReal)⁻¹, by
      convert hasSum_fintype (fun _ : Fin K => (K : ENNReal)⁻¹) using 1 <;> simp
      exact (ENNReal.mul_inv_cancel (NeZero.natCast_ne K ENNReal)
        (ENNReal.natCast_ne_top K)).symm⟩
  let pu : biased_source_mean_problem K M := { p with targetGroup := u }
  have hu : (fun z => pmf_real_mass u z) = uniform_group_mass K := by
    funext z
    change ((K : ENNReal)⁻¹).toReal = (1 : ℝ) / K
    rw [ENNReal.toReal_inv]
    simp
  have hp : ∀ B, 0 < B →
      optimal_sampling_plan pu (fun z => pmf_real_mass pu.targetGroup z) B (plans B) := by
    intro B hB
    simpa [pu, hu, optimal_sampling_plan, budget_feasible_plan,
      effective_sample_size, target_supported_by_plan, source_mixture_mass,
      plan_discrepancy] using hplans B hB
  obtain ⟨A, hA⟩ :=
    population_minimax_uniform_post_stratified_risk_upper_local pu plans hp
  let scale : ℝ := (K : ℝ) ^ 2 / Fintype.card (Fin K → Bool)
  let A' : ℝ := scale * Fintype.card (Fin K → Bool) * |A|
  have hscale : 0 < scale := by
    have hk : 0 < (K : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
    have hc : 0 < (Fintype.card (Fin K → Bool) : ℝ) := by positivity
    dsimp [scale]
    positivity
  refine ⟨A', by dsimp [A']; positivity, ?_⟩
  filter_upwards [hA, Filter.eventually_gt_atTop (0 : ℝ)] with B hbound hB
  intro P hP
  let sign (s : Fin K → Bool) (z : Fin K) : ℝ := if s z then -1 else 1
  let signedModel (s : Fin K → Bool) : conditional_outcome_model K := fun z =>
    (P z).map ((measurable_const.mul measurable_id :
      Measurable (fun y : ℝ => sign s z * y)).aemeasurable)
  let signedVector (s : Fin K → Bool) (y : Fin K → ℝ) : Fin K → ℝ :=
    fun z => sign s z * y z
  let signedPair (s : Fin K → Bool) (x : Fin K × ℝ) : Fin K × ℝ :=
    (x.1, sign s x.1 * x.2)
  let signedData (s : Fin K → Bool) {n : sampling_plan M}
      (D : sampled_dataset K M n) : sampled_dataset K M n :=
    fun m i => signedPair s (D m i)
  have hsignedVector_meas : ∀ s, Measurable (signedVector s) := by
    intro s
    fun_prop
  have hsignedPair_meas : ∀ s, Measurable (signedPair s) := by
    intro s
    fun_prop
  have hsignedData_meas : ∀ s (n : sampling_plan M),
      Measurable (signedData s : sampled_dataset K M n → sampled_dataset K M n) := by
    intro s n
    fun_prop
  have hsource : ∀ s m, source_observation_law pu (signedModel s) m =
      Measure.map (signedPair s) (source_observation_law p P m) := by
    intro s m
    let select : Fin K × (Fin K → ℝ) → Fin K × ℝ := fun x => (x.1, x.2 x.1)
    have heval : Measurable (fun x : Fin K × (Fin K → ℝ) => x.2 x.1) := by
      have hsum : Measurable (fun x : Fin K × (Fin K → ℝ) =>
          ∑ z, if x.1 = z then x.2 z else 0) := by
        apply Finset.measurable_sum Finset.univ
        intro z hz
        exact Measurable.ite ((measurableSet_singleton z).preimage measurable_fst)
          (by fun_prop) measurable_const
      convert hsum using 1
      funext x
      simp
    have hselect : Measurable select := measurable_fst.prodMk heval
    have hpi : Measure.pi (fun z => Measure.map (fun y : ℝ => sign s z * y)
        (P z : Measure ℝ)) =
        Measure.map (signedVector s) (Measure.pi fun z => (P z : Measure ℝ)) := by
      symm
      exact Measure.pi_map_pi (fun z =>
        (measurable_const.mul measurable_id).aemeasurable)
    rw [source_observation_law, source_observation_law]
    change Measure.map select
        ((p.sourceGroup m).toMeasure.prod
          (Measure.pi fun z => Measure.map (fun y : ℝ => sign s z * y) (P z : Measure ℝ))) = _
    rw [hpi]
    calc
      Measure.map select ((p.sourceGroup m).toMeasure.prod
          (Measure.map (signedVector s) (Measure.pi fun z => (P z : Measure ℝ)))) =
          Measure.map select
            ((Measure.map id (p.sourceGroup m).toMeasure).prod
              (Measure.map (signedVector s) (Measure.pi fun z => (P z : Measure ℝ)))) := by simp
      _ = Measure.map select
          (Measure.map (Prod.map id (signedVector s))
            ((p.sourceGroup m).toMeasure.prod (Measure.pi fun z => (P z : Measure ℝ)))) := by
          rw [Measure.map_prod_map _ _ measurable_id (hsignedVector_meas s)]
      _ = Measure.map (select ∘ Prod.map id (signedVector s))
          ((p.sourceGroup m).toMeasure.prod (Measure.pi fun z => (P z : Measure ℝ))) := by
          rw [Measure.map_map hselect (measurable_id.prodMap (hsignedVector_meas s))]
      _ = Measure.map (signedPair s ∘ select)
          ((p.sourceGroup m).toMeasure.prod (Measure.pi fun z => (P z : Measure ℝ))) := by
          congr 1
      _ = Measure.map (signedPair s)
          (Measure.map select
            ((p.sourceGroup m).toMeasure.prod (Measure.pi fun z => (P z : Measure ℝ)))) := by
          rw [Measure.map_map (hsignedPair_meas s) hselect]
  have hsampling : ∀ s (n : sampling_plan M),
      sampling_law pu n (signedModel s) =
        Measure.map (signedData s) (sampling_law p n P) := by
    intro s n
    letI hfinSource : ∀ m, IsFiniteMeasure (source_observation_law p P m) := fun m => by
      rw [source_observation_law]
      infer_instance
    have hinner : ∀ m, Measure.pi (fun _i : Fin (n m) =>
        source_observation_law pu (signedModel s) m) =
        Measure.map (fun d i => signedPair s (d i))
          (Measure.pi fun _i : Fin (n m) => source_observation_law p P m) := by
      intro m
      simp_rw [hsource s m]
      symm
      exact Measure.pi_map_pi (fun _i => (hsignedPair_meas s).aemeasurable)
    rw [sampling_law, sampling_law]
    simp_rw [hinner]
    symm
    letI hfinPi : ∀ m, IsFiniteMeasure
        (Measure.pi fun _i : Fin (n m) => source_observation_law p P m) :=
      fun m => inferInstance
    letI hfinMap : ∀ m, IsFiniteMeasure
        (Measure.map (fun d i => signedPair s (d i))
          (Measure.pi fun _i : Fin (n m) => source_observation_law p P m)) :=
      fun m => inferInstance
    letI hSigma : ∀ m, SigmaFinite
        (Measure.map (fun d i => signedPair s (d i))
          (Measure.pi fun _i : Fin (n m) => source_observation_law p P m)) :=
      fun m => by
        letI := hfinMap m
        infer_instance
    have houter : ∀ m, Measurable
        (fun d : (i : Fin (n m)) → Fin K × ℝ => fun i => signedPair s (d i)) := by
      intro m
      fun_prop
    convert Measure.pi_map_pi (hμ := hSigma) (fun m => (houter m).aemeasurable) using 1
  have hsclass : ∀ s, bounded_conditional_mean_class pu (signedModel s) := by
    intro s z
    have hmap : AEMeasurable (fun y : ℝ => sign s z * y) (P z : Measure ℝ) :=
      (measurable_const.mul measurable_id).aemeasurable
    have hInt : Integrable (fun y : ℝ => y) (P z : Measure ℝ) := by
      simpa [Function.id_def] using (hP z).1.integrable (by norm_num)
    have hmean : conditional_group_mean (signedModel s) z =
        sign s z * conditional_group_mean P z := by
      change (∫ y, id y ∂Measure.map (fun y : ℝ => sign s z * y) (P z : Measure ℝ)) = _
      rw [MeasureTheory.integral_map hmap measurable_id.aestronglyMeasurable]
      simp only [Function.id_def]
      rw [integral_const_mul_of_integrable hInt]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · change MemLp id 2 (Measure.map (fun y : ℝ => sign s z * y) (P z : Measure ℝ))
      rw [MeasureTheory.memLp_map_measure_iff measurable_id.aestronglyMeasurable hmap]
      simpa [Function.comp_def] using (hP z).1.const_mul (sign s z)
    · rw [hmean]
      cases hsz : s z <;> simpa [pu, sign, hsz] using (hP z).2.1
    · change ProbabilityTheory.variance id
        (Measure.map (fun y : ℝ => sign s z * y) (P z : Measure ℝ)) ≤ p.varianceBound
      rw [ProbabilityTheory.variance_id_map hmap,
        ProbabilityTheory.variance_const_mul]
      cases hsz : s z <;> simpa [sign, hsz, Function.id_def] using (hP z).2.2
  have hsignedMean : ∀ s z, conditional_group_mean (signedModel s) z =
      sign s z * conditional_group_mean P z := by
    intro s z
    have hmap : AEMeasurable (fun y : ℝ => sign s z * y) (P z : Measure ℝ) :=
      (measurable_const.mul measurable_id).aemeasurable
    have hInt : Integrable (fun y : ℝ => y) (P z : Measure ℝ) := by
      simpa [Function.id_def] using (hP z).1.integrable (by norm_num)
    change (∫ y, id y ∂Measure.map (fun y : ℝ => sign s z * y) (P z : Measure ℝ)) = _
    rw [MeasureTheory.integral_map hmap measurable_id.aestronglyMeasurable]
    simp only [Function.id_def]
    rw [integral_const_mul_of_integrable hInt]
    rfl
  have hobsCount : ∀ s (n : sampling_plan M) (D : sampled_dataset K M n) z,
      observed_group_count (signedData s D) z = observed_group_count D z := by
    intro s n D z
    simp [observed_group_count, signedData, signedPair]
  have hobsSum : ∀ s (n : sampling_plan M) (D : sampled_dataset K M n) z,
      observed_group_sum (signedData s D) z = sign s z * observed_group_sum D z := by
    intro s n D z
    simp only [observed_group_sum, signedData, signedPair]
    simp_rw [show ∀ m i, (if (D m i).1 = z then sign s (D m i).1 * (D m i).2 else 0) =
        sign s z * (if (D m i).1 = z then (D m i).2 else 0) by
      intro m i
      split_ifs with h
      · rw [h]
      · simp]
    simp [Finset.mul_sum]
  have hobsMean : ∀ s (n : sampling_plan M) (D : sampled_dataset K M n) z,
      observed_group_mean (signedData s D) z = sign s z * observed_group_mean D z := by
    intro s n D z
    rw [observed_group_mean, observed_group_mean, hobsCount, hobsSum]
    split_ifs <;> ring
  have hscalarLoss : ∀ s (n : sampling_plan M) (D : sampled_dataset K M n),
      (post_stratified_estimator u (signedData s D) -
          target_population_mean u (signedModel s)) ^ 2 =
        (∑ z, (1 / (K : ℝ)) *
          sign s z * (observed_group_mean D z - conditional_group_mean P z)) ^ 2 := by
    intro s n D
    rw [post_stratified_estimator, target_population_mean]
    simp_rw [hu, hobsMean, hsignedMean]
    simp only [uniform_group_mass]
    congr 1
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  let flipAt (z : Fin K) : (Fin K → Bool) ≃ (Fin K → Bool) := {
    toFun := fun s j => if j = z then !(s j) else s j
    invFun := fun s j => if j = z then !(s j) else s j
    left_inv := by
      intro s
      funext j
      by_cases h : j = z <;> simp [h]
    right_inv := by
      intro s
      funext j
      by_cases h : j = z <;> simp [h] }
  have horth : ∀ z w, (∑ s : Fin K → Bool, sign s z * sign s w) =
      if z = w then Fintype.card (Fin K → Bool) else 0 := by
    intro z w
    by_cases hzw : z = w
    · subst w
      simp only [if_pos rfl]
      simp_rw [show ∀ s : Fin K → Bool, sign s z * sign s z = 1 by
        intro s
        cases h : s z <;> simp [sign, h]]
      simp
    · simp only [if_neg hzw]
      let f : (Fin K → Bool) → ℝ := fun s => sign s z * sign s w
      have hreindex : ∑ s, f (flipAt z s) = ∑ s, f s :=
        Equiv.sum_comp (flipAt z) f
      have hneg : ∀ s, f (flipAt z s) = -f s := by
        intro s
        have hwz : w ≠ z := Ne.symm hzw
        cases hsz : s z <;> cases hsw : s w <;>
          simp [f, flipAt, sign, hzw, hwz, hsz, hsw]
      have hsumneg : ∑ s, f (flipAt z s) = ∑ s, -f s :=
        Finset.sum_congr rfl (fun s _ => hneg s)
      have heq : ∑ s, f s = -∑ s, f s := by
        rw [Finset.sum_neg_distrib] at hsumneg
        exact hreindex.symm.trans hsumneg
      have hz : ∑ s, f s = 0 := by linarith
      simpa [f] using hz
  have hrad : ∀ e : Fin K → ℝ,
      scale * ∑ s : Fin K → Bool, (∑ z, (1 / (K : ℝ)) * sign s z * e z) ^ 2 =
        ∑ z, (e z) ^ 2 := by
    intro e
    let a : (Fin K → Bool) → Fin K → ℝ := fun s z =>
      (1 / (K : ℝ)) * sign s z * e z
    have hexpand : ∀ s, (∑ z, a s z) ^ 2 = ∑ z, ∑ w, a s z * a s w := by
      intro s
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.mul_sum]
    have hreorder : scale * ∑ s, ∑ z, ∑ w, a s z * a s w =
        ∑ z, ∑ w, scale * ∑ s, a s z * a s w := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.sum_comm]
    change scale * ∑ s, (∑ z, a s z) ^ 2 = ∑ z, (e z) ^ 2
    simp_rw [hexpand]
    rw [hreorder]
    apply Finset.sum_congr rfl
    intro z hz
    calc
      (∑ w, scale * ∑ s, a s z * a s w) =
          ∑ w, if z = w then (e z) ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro w hw
        have hfactor : (∑ s, a s z * a s w) =
            ((1 / (K : ℝ)) ^ 2 * e z * e w) * ∑ s, sign s z * sign s w := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          simp [a]
          ring
        rw [hfactor, horth]
        by_cases hzw : z = w
        · subst w
          simp only [if_pos rfl, Nat.cast_ofNat]
          have hk : (K : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne K
          have hc : (Fintype.card (Fin K → Bool) : ℝ) ≠ 0 := by
            exact_mod_cast Fintype.card_ne_zero
          dsimp [scale]
          field_simp
        · simp [hzw]
      _ = (e z) ^ 2 := by simp
  let n := plans B
  let μ := sampling_law p n P
  let err : sampled_dataset K M n → Fin K → ℝ := fun D z =>
    observed_group_mean D z - conditional_group_mean P z
  let loss : (Fin K → Bool) → sampled_dataset K M n → ℝ := fun s D =>
    (∑ z, (1 / (K : ℝ)) * sign s z * err D z) ^ 2
  let vloss : sampled_dataset K M n → ℝ := fun D => ∑ z, (err D z) ^ 2
  have herr_meas : ∀ z, Measurable (fun D : sampled_dataset K M n => err D z) := by
    intro z
    exact ((measurable_pi_apply z).comp
      (vector_of_means_estimator_measurable n)).sub measurable_const
  have hloss_meas : ∀ s, Measurable (loss s) := by
    intro s
    apply Measurable.pow_const
    apply Finset.measurable_sum Finset.univ
    intro z hz
    exact (measurable_const.mul measurable_const).mul (herr_meas z)
  have hpoint : ∀ D, scale * ∑ s, loss s D = vloss D := by
    intro D
    exact hrad (err D)
  have hriskrepr : ∀ s, population_mean_risk pu n (post_stratified_estimator u)
      (signedModel s) = ∫ D, loss s D ∂μ := by
    intro s
    rw [population_mean_risk, hsampling]
    change (∫ D, (post_stratified_estimator u D -
      target_population_mean u (signedModel s)) ^ 2
        ∂Measure.map (signedData s) (sampling_law p n P)) = _
    have hm : AEStronglyMeasurable (fun D : sampled_dataset K M n =>
        (post_stratified_estimator u D - target_population_mean u (signedModel s)) ^ 2)
        (Measure.map (signedData s) (sampling_law p n P)) :=
      (((post_stratified_estimator_measurable u n).sub measurable_const).pow_const 2).aestronglyMeasurable
    rw [MeasureTheory.integral_map (hsignedData_meas s n).aemeasurable hm]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with D
    exact hscalarLoss s n D
  have hscalar_bound : ∀ s : Fin K → Bool,
      population_mean_risk pu n (post_stratified_estimator u) (signedModel s) ≤
        population_leading_risk pu n B + |A| / B ^ 2 := by
    intro s
    refine le_trans (hbound (signedModel s) (hsclass s)) ?_
    gcongr
    exact le_abs_self A
  have hsum_bound : (∑ s, population_mean_risk pu n
        (post_stratified_estimator u) (signedModel s)) ≤
      ∑ s : Fin K → Bool, (population_leading_risk pu n B + |A| / B ^ 2) := by
    apply Finset.sum_le_sum
    intro s hs
    exact hscalar_bound s
  have hlead : group_leading_risk p n B + A' / B ^ 2 =
      scale * ∑ s : Fin K → Bool,
        (population_leading_risk pu n B + |A| / B ^ 2) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [mul_add]
    have hmain : group_leading_risk p n B =
        scale * ((Fintype.card (Fin K → Bool) : ℝ) *
          population_leading_risk pu n B) := by
      simp [group_leading_risk, population_leading_risk, pu, hu, scale,
        plan_discrepancy, source_mixture_mass]
      field_simp
    rw [hmain]
    dsimp only [A']
    rw [Finset.card_univ]
    ring
  rw [hlead]
  have hvi : Integrable vloss μ := by
    have hi := (vector_of_means_group_risk_integrable p n) P hP
    simpa [vloss, err, vector_of_means_estimator, μ] using hi
  have hloss_int : ∀ s, Integrable (loss s) μ := by
    intro s
    apply Integrable.mono_nonneg ((hvi.const_mul (scale⁻¹)))
      (hloss_meas s).aestronglyMeasurable
    · filter_upwards with D
      exact sq_nonneg _
    · filter_upwards with D
      have hle : loss s D ≤ ∑ t, loss t D :=
        Finset.single_le_sum (fun t _ => (show 0 ≤ loss t D from sq_nonneg _))
          (Finset.mem_univ s)
      rw [inv_mul_eq_div]
      apply (le_div_iff₀ hscale).2
      calc
        loss s D * scale = scale * loss s D := by ring
        _ ≤ scale * ∑ t, loss t D :=
          mul_le_mul_of_nonneg_left hle (le_of_lt hscale)
        _ = vloss D := hpoint D
  rw [group_means_risk]
  change (∫ D, vloss D ∂μ) ≤ _
  simp_rw [← hpoint]
  rw [integral_const_mul_of_integrable
    (MeasureTheory.integrable_finsetSum Finset.univ (fun s _ => hloss_int s))]
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun s _ => hloss_int s)]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hscale)
  simpa only [hriskrepr] using hsum_bound

@[blueprint "lem:group-minimax-effective-sample-upper-bound-refinement"
  (statement := /-- Under the hypotheses of \cref{lem:group-vector-risk-uniform-second-order-refinement}, there exists $u=o(B^{-1})$ such that, for all sufficiently large $B$,
  \[
  \mathcal R^*_{\mathrm{GM}}(B,\mathcal P_p(R,\sigma^2))
  \le L_{\mathrm{GM}}(n_U(B),B)+u(B).
  \] -/)
  (proof := /-- Apply \cref{lem:group-vector-risk-uniform-second-order-refinement} and take $u(B)=A/B^2$, which is little-$o(B^{-1})$ by \cref{lem:post-stratified-inverse-square-little-o-local}. At each sufficiently large positive budget, the vector-of-means estimator is measurable by \cref{lem:vector-of-means-estimator-measurable} and has integrable group loss by \cref{lem:vector-of-means-group-risk-integrable}. The uniform risk estimate bounds its worst-case risk. This gives an admissible candidate in the infimum defining the group minimax risk; nonnegativity of all group risks supplies the lower boundedness needed for the real infimum. -/)
  (title := /-- Group minimax upper bound at a uniform-optimal plan -/)
  (latexEnv := "lemma")]
lemma group_minimax_effective_sample_upper_bound_refinement
    {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (plans : ℝ → sampling_plan M)
    (hplans : ∀ B, 0 < B →
      optimal_sampling_plan p (uniform_group_mass K) B (plans B)) :
    ∃ remainder : ℝ → ℝ,
      Asymptotics.IsLittleO Filter.atTop remainder inverse_budget_rate ∧
      ∀ᶠ B in Filter.atTop,
        group_minimax_risk p B ≤
          group_leading_risk p (plans B) B + remainder B := by
  obtain ⟨A, hAnonneg, hA⟩ :=
    group_vector_risk_uniform_second_order_refinement p plans hplans
  refine ⟨fun B => A / B ^ 2,
    post_stratified_inverse_square_little_o_local A, ?_⟩
  filter_upwards [hA, Filter.eventually_gt_atTop (0 : ℝ)] with B hbound hBpos
  let estimator : sampled_dataset K M (plans B) → (Fin K → ℝ) :=
    vector_of_means_estimator
  have hrisk : BddAbove {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
      s = group_means_risk p (plans B) estimator P} := by
    refine ⟨group_leading_risk p (plans B) B + A / B ^ 2, ?_⟩
    intro s hs
    rcases hs with ⟨P, hP, rfl⟩
    exact hbound P hP
  have hleading : 0 ≤ group_leading_risk p (plans B) B := by
    have havg : 0 ≤ average_plan_cost p.cost (plans B) := by
      unfold average_plan_cost
      split_ifs
      · exact le_rfl
      · exact div_nonneg
          (by
            unfold plan_cost
            exact Finset.sum_nonneg fun m _ =>
              mul_nonneg (le_of_lt (p.cost_pos m)) (Nat.cast_nonneg _))
          (Nat.cast_nonneg _)
    have hdisc : 0 ≤ plan_discrepancy p (plans B) (uniform_group_mass K) := by
      unfold plan_discrepancy
      apply Finset.sum_nonneg
      intro z hz
      split_ifs
      · exact le_rfl
      · apply div_nonneg (sq_nonneg _)
        unfold source_mixture_mass
        split_ifs
        · exact le_rfl
        · exact div_nonneg
            (Finset.sum_nonneg fun m _ =>
              mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)
            (Nat.cast_nonneg _)
    unfold group_leading_risk
    exact div_nonneg
      (mul_nonneg (mul_nonneg
        (mul_nonneg (sq_nonneg (K : ℝ)) p.varianceBound_nonneg) havg) hdisc)
      (le_of_lt hBpos)
  have hupper_nonneg :
      0 ≤ group_leading_risk p (plans B) B + A / B ^ 2 :=
    add_nonneg hleading (div_nonneg hAnonneg (sq_nonneg B))
  have hworst :
      group_worst_case_risk p (plans B) estimator hrisk ≤
        group_leading_risk p (plans B) B + A / B ^ 2 := by
    rw [group_worst_case_risk]
    apply Real.sSup_le
    · intro s hs
      rcases hs with ⟨P, hP, rfl⟩
      exact hbound P hP
    · exact hupper_nonneg
  let candidates : Set ℝ :=
    {r : ℝ | ∃ n : sampling_plan M, budget_feasible_plan p B n ∧
      ∃ estimate : sampled_dataset K M n → (Fin K → ℝ), Measurable estimate ∧
        group_risk_integrable p n estimate ∧
        ∃ hset : BddAbove {s : ℝ | ∃ P, bounded_conditional_mean_class p P ∧
          s = group_means_risk p n estimate P},
          r = group_worst_case_risk p n estimate hset}
  have hcandidates : BddBelow candidates := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨n, hn, estimate, hmeas, hint, hset, rfl⟩
    rw [group_worst_case_risk]
    apply Real.sSup_nonneg
    intro s hs
    rcases hs with ⟨P, hP, rfl⟩
    rw [group_means_risk]
    exact MeasureTheory.integral_nonneg (fun D => Finset.sum_nonneg fun z _ => sq_nonneg _)
  have hcandidate :
      group_worst_case_risk p (plans B) estimator hrisk ∈ candidates := by
    exact ⟨plans B, (hplans B hBpos).1, estimator,
      vector_of_means_estimator_measurable (plans B),
      vector_of_means_group_risk_integrable p (plans B), hrisk, rfl⟩
  rw [group_minimax_risk]
  change sInf candidates ≤ _
  exact le_trans (csInf_le hcandidates hcandidate) hworst

@[blueprint "lem:group-minimax-effective-sample-asymptotics"
  (statement := /-- Let $K$ and $M$ be positive integers, let $p$ be a biased-source mean-estimation problem with $K$ groups and $M$ sources whose mean radius satisfies $R>0$, and let $n_U\colon\mathbb R\to\mathbb N^M$ be a family of sampling plans. Suppose that, for every $B>0$, the plan $n_U(B)$ is budget-feasible and maximizes the effective sample size for the uniform mass $u_K$ among all budget-feasible integer plans. Then, as $B\to\infty$,
  \[
  \mathcal R^*_{\mathrm{GM}}(B,\mathcal P_p(R,\sigma^2))
  -\frac{K^2\sigma^2\bar c(n_U(B))D(u_K,\bar q_{n_U(B)})}{B}
  =o(B^{-1}).
  \] -/)
  (proof := /-- By \cref{lem:group-minimax-effective-sample-lower-bound}, there is a function $\ell=o(B^{-1})$ such that, eventually, the group leading risk plus $\ell(B)$ is at most the group minimax risk. The uniform vector-risk estimate and the minimax construction in \cref{lem:group-minimax-effective-sample-upper-bound-refinement} supply a function $u=o(B^{-1})$ giving the reverse eventual inequality. Hence, if $d(B)$ denotes the minimax risk minus the leading risk, then eventually $\ell(B)\le d(B)\le u(B)$. For every $c>0$, the two little-o estimates eventually give $|\ell(B)|\le c|B^{-1}|$ and $|u(B)|\le c|B^{-1}|$. The preceding squeeze implies $|d(B)|\le c|B^{-1}|$, which is precisely $d=o(B^{-1})$. -/)
  (title := /-- Group minimax effective-sample-size asymptotics -/)
  (latexEnv := "lemma")]
lemma group_minimax_effective_sample_asymptotics {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (hmean : 0 < p.meanRadius)
    (plans : ℝ → sampling_plan M)
    (hplans : ∀ B, 0 < B →
      optimal_sampling_plan p (uniform_group_mass K) B (plans B)) :
    Asymptotics.IsLittleO Filter.atTop
      (fun B => group_minimax_risk p B - group_leading_risk p (plans B) B)
      inverse_budget_rate := by
  obtain ⟨lower, hlower_small, hlower⟩ :=
    group_minimax_effective_sample_lower_bound p hmean plans hplans
  obtain ⟨upper, hupper_small, hupper⟩ :=
    group_minimax_effective_sample_upper_bound_refinement p plans hplans
  rw [Asymptotics.isLittleO_iff] at hlower_small hupper_small ⊢
  intro c hc
  filter_upwards [hlower, hupper, hlower_small hc, hupper_small hc] with
      B hlower_bound hupper_bound hlower_norm hupper_norm
  simp only [Real.norm_eq_abs] at hlower_norm hupper_norm ⊢
  rw [abs_le]
  constructor
  · have hlower_neg := neg_le_of_abs_le hlower_norm
    linarith
  · have hupper_pos := le_of_abs_le hupper_norm
    linarith

@[blueprint "thm:minimax-optimal-data-collection-under-budget"
  (statement := /-- For every biased-source mean-estimation problem with strictly positive mean radius $R>0$, there exist target-optimal plans $n_T^*(B)$ and uniform-optimal plans $n_U^*(B)$ for all $B>0$. The associated post-stratified and vector-of-means estimators are measurable. For every $P\in\mathcal P(R,\sigma^2)$ their risks obey, respectively,
  \[
  \operatorname{Risk}_{\mathrm{PM}}((n_T^*(B),\widehat\theta_{\mathrm{PS}}),P)
  \le \frac{\sigma^2\bar c(n_T^*(B))D(q_T,\bar q_{n_T^*(B)})}{B}+o(B^{-1})
  \]
  and
  \[
  \operatorname{Risk}_{\mathrm{GM}}((n_U^*(B),\widehat\theta_{\mathrm{VM}}),P)
  \le \frac{K^2\sigma^2\bar c(n_U^*(B))D(u_K,\bar q_{n_U^*(B)})}{B}+o(B^{-1}).
  \]
  Moreover, each displayed leading term differs from the corresponding budget-constrained minimax risk by $o(B^{-1})$ as $B\to\infty$. -/)
  (proof := /-- Choose the target-optimal and uniform-optimal plan families supplied by \cref{lem:target-optimal-plan-family-exists,lem:uniform-optimal-plan-family-exists}. Their stated estimators are admissible by \cref{lem:post-stratified-estimator-measurable,lem:vector-of-means-estimator-measurable}. For every conditional model in the bounded class, apply \cref{lem:post-stratified-optimal-risk-upper,lem:vector-of-means-optimal-risk-upper} to obtain the two little-o risk remainders and their inequalities. The hypothesis $R>0$ permits application of \cref{lem:population-minimax-effective-sample-asymptotics,lem:group-minimax-effective-sample-asymptotics}, which gives the two minimax identifications at the same selected plan families. These eight conclusions are precisely the asserted conjunction. -/)
  (title := /-- Minimax-optimal data collection under a budget -/)
  (latexEnv := "theorem")]
theorem minimax_optimal_data_collection_under_budget {K M : ℕ} [NeZero K] [NeZero M]
    (p : biased_source_mean_problem K M) (hmean : 0 < p.meanRadius) :
    ∃ targetPlans uniformPlans : ℝ → sampling_plan M,
      (∀ B, 0 < B →
        optimal_sampling_plan p (fun z => pmf_real_mass p.targetGroup z) B (targetPlans B)) ∧
      (∀ B, 0 < B →
        optimal_sampling_plan p (uniform_group_mass K) B (uniformPlans B)) ∧
      (∀ B, Measurable
        (post_stratified_estimator p.targetGroup : sampled_dataset K M (targetPlans B) → ℝ)) ∧
      (∀ B, Measurable
        (vector_of_means_estimator : sampled_dataset K M (uniformPlans B) → (Fin K → ℝ))) ∧
      (∀ P, bounded_conditional_mean_class p P →
        ∃ remainder : ℝ → ℝ,
          Asymptotics.IsLittleO Filter.atTop remainder inverse_budget_rate ∧
          ∀ B, 0 < B →
            population_mean_risk p (targetPlans B)
                (post_stratified_estimator p.targetGroup) P ≤
              population_leading_risk p (targetPlans B) B + remainder B) ∧
      Asymptotics.IsLittleO Filter.atTop
        (fun B => population_minimax_risk p B -
          population_leading_risk p (targetPlans B) B)
        inverse_budget_rate ∧
      (∀ P, bounded_conditional_mean_class p P →
        ∃ remainder : ℝ → ℝ,
          Asymptotics.IsLittleO Filter.atTop remainder inverse_budget_rate ∧
          ∀ B, 0 < B →
            group_means_risk p (uniformPlans B) vector_of_means_estimator P ≤
              group_leading_risk p (uniformPlans B) B + remainder B) ∧
      Asymptotics.IsLittleO Filter.atTop
        (fun B => group_minimax_risk p B - group_leading_risk p (uniformPlans B) B)
        inverse_budget_rate := by
  obtain ⟨targetPlans, htarget⟩ := target_optimal_plan_family_exists p
  obtain ⟨uniformPlans, huniform⟩ := uniform_optimal_plan_family_exists p
  exact ⟨targetPlans, uniformPlans, htarget, huniform,
    fun B => post_stratified_estimator_measurable p.targetGroup (targetPlans B),
    fun B => vector_of_means_estimator_measurable (uniformPlans B),
    post_stratified_optimal_risk_upper p targetPlans htarget,
    population_minimax_effective_sample_asymptotics p hmean targetPlans htarget,
    vector_of_means_optimal_risk_upper p uniformPlans huniform,
    group_minimax_effective_sample_asymptotics p hmean uniformPlans huniform⟩

import Architect
import Mathlib.Analysis.Convex.Integral
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Topology.MetricSpace.Defs

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators
open MeasureTheory

@[blueprint "def:metric-election"
  (statement := /-- Let $C$ be a type of candidates, let $(V,\mu)$ be a measurable probability space of voters, and let $P$ be a metric space equipped with its Borel $\sigma$-algebra. A continuum metric election assigns a point of $P$ to every candidate and a measurable point of $P$ to every voter. The distance from a voter to each candidate is assumed integrable. For $\mu$-almost every voter, every two distinct candidates have different distances from that voter, and hence induce a strict ranking. -/)
  (title := /-- Continuum metric election -/)
  (latexEnv := "definition")]
structure metric_election (Candidate Voter Point : Type*)
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point] where
  candidatePoint : Candidate → Point
  voterPoint : Voter → Point
  voterMeasure : ProbabilityMeasure Voter
  voterPoint_measurable : Measurable voterPoint
  voter_distance_integrable : ∀ c,
    Integrable (fun i => dist (voterPoint i) (candidatePoint c))
      voterMeasure
  strict_rankings : ∀ᵐ i ∂(voterMeasure : Measure Voter),
    ∀ a b, a ≠ b →
      dist (voterPoint i) (candidatePoint a) ≠
        dist (voterPoint i) (candidatePoint b)

@[blueprint "def:social-cost"
  (statement := /-- For a metric election $E$ and candidate $c$, define
  \[
    \operatorname{SC}_E(c)=\int_V d(i,c)\,d\mu(i).
  \]
  The integral is finite by the integrability assumption in \cref{def:metric-election}. -/)
  (title := /-- Social cost -/)
  (latexEnv := "definition")]
noncomputable def social_cost {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (c : Candidate) : ℝ :=
  ∫ i, dist (E.voterPoint i) (E.candidatePoint c) ∂E.voterMeasure

@[blueprint "def:normalized-bias"
  (statement := /-- For a voter $i$ and candidates $a,b$, define the normalized bias
  \[
    B_i(a,b)=\frac{d(i,a)-d(i,b)}{d(a,b)}.
  \]
  Negative bias favors $a$, while positive bias favors $b$. -/)
  (title := /-- Normalized pairwise bias -/)
  (latexEnv := "definition")]
noncomputable def normalized_bias {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (i : Voter)
    (a b : Candidate) : ℝ :=
  (dist (E.voterPoint i) (E.candidatePoint a) -
      dist (E.voterPoint i) (E.candidatePoint b)) /
    dist (E.candidatePoint a) (E.candidatePoint b)

@[blueprint "def:first-bias-mass"
  (statement := /-- For a deliberating group $g:\operatorname{Fin}(k)\to V$ and ordered candidates $a,b$, let $A_g(a,b)$ be the sum of the absolute normalized biases of the group members who prefer $a$ to $b$. -/)
  (title := /-- Bias mass favoring the first candidate -/)
  (latexEnv := "definition")]
noncomputable def first_bias_mass {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) {k : ℕ}
    (g : Fin k → Voter) (a b : Candidate) : ℝ :=
  ∑ j, max (-normalized_bias E (g j) a b) 0

@[blueprint "def:second-bias-mass"
  (statement := /-- For a deliberating group $g:\operatorname{Fin}(k)\to V$ and ordered candidates $a,b$, let $B_g(a,b)$ be the sum of the absolute normalized biases of the group members who prefer $b$ to $a$. -/)
  (title := /-- Bias mass favoring the second candidate -/)
  (latexEnv := "definition")]
noncomputable def second_bias_mass {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) {k : ℕ}
    (g : Fin k → Voter) (a b : Candidate) : ℝ :=
  ∑ j, max (normalized_bias E (g j) a b) 0

@[blueprint "def:random-choice-group-probability"
  (statement := /-- In the Random Choice deliberation model, a fixed group $g$ chooses the first candidate $a$ over $b$ with probability
  \[
    \frac{A_g(a,b)}{A_g(a,b)+B_g(a,b)}.
  \]
  If $k>0$ and $a\ne b$, the almost-everywhere strict-ranking hypothesis in \cref{def:metric-election} ensures that the denominator is nonzero for $\mu^{\otimes k}$-almost every group. -/)
  (title := /-- Random Choice probability for a fixed group -/)
  (latexEnv := "definition")]
noncomputable def random_choice_group_probability {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) {k : ℕ}
    (g : Fin k → Voter) (a b : Candidate) : ℝ :=
  first_bias_mass E g a b /
    (first_bias_mass E g a b + second_bias_mass E g a b)

@[blueprint "def:random-choice-win-probability"
  (statement := /-- Let $\mu^{\otimes k}$ be the product probability measure on ordered groups $g:\operatorname{Fin}(k)\to V$. The exactly estimable deliberation probability is
  \[
    p_k(a,b)=\int_{V^k}\frac{A_g(a,b)}{A_g(a,b)+B_g(a,b)}
      \,d\mu^{\otimes k}(g).
  \]
  Thus the members of every deliberating group are sampled independently with replacement from the entire continuum electorate. -/)
  (title := /-- Random Choice deliberation win probability -/)
  (latexEnv := "definition")]
noncomputable def random_choice_win_probability {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (k : ℕ)
    (a b : Candidate) : ℝ :=
  ∫ g, random_choice_group_probability E g a b ∂
    (ProbabilityMeasure.pi (fun _ : Fin k => E.voterMeasure) :
      Measure (Fin k → Voter))

@[blueprint "def:deliberation-dominates"
  (statement := /-- Candidate $a$ dominates candidate $b$ in the size-$k$ deliberation tournament when $p_k(a,b)\geq 1/2$. -/)
  (title := /-- Deliberation tournament edge -/)
  (latexEnv := "definition")]
def deliberation_dominates {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (k : ℕ)
    (a b : Candidate) : Prop :=
  (1 / 2 : ℝ) ≤ random_choice_win_probability E k a b

@[blueprint "def:copeland-score"
  (statement := /-- The Copeland score of $a$ is the number of distinct candidates $b$ dominated by $a$ in the deliberation tournament. -/)
  (title := /-- Copeland score -/)
  (latexEnv := "definition")]
noncomputable def copeland_score {Candidate Voter Point : Type*}
    [Fintype Candidate] [DecidableEq Candidate]
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (k : ℕ)
    (a : Candidate) : ℕ := by
  classical
  exact (Finset.univ.filter fun b =>
    b ≠ a ∧ deliberation_dominates E k a b).card

@[blueprint "def:tournament-covers"
  (statement := /-- In the deliberation tournament, candidate $a$ covers a distinct candidate $b$ if $a$ dominates $b$ and every candidate dominated by $b$ is also dominated by $a$. -/)
  (title := /-- Covering relation -/)
  (latexEnv := "definition")]
def tournament_covers {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (k : ℕ)
    (a b : Candidate) : Prop :=
  a ≠ b ∧ deliberation_dominates E k a b ∧
    ∀ c, deliberation_dominates E k b c →
      deliberation_dominates E k a c

@[blueprint "def:uncovered-candidate"
  (statement := /-- A candidate is uncovered if no distinct candidate covers it in the deliberation tournament. -/)
  (title := /-- Uncovered candidate -/)
  (latexEnv := "definition")]
def uncovered_candidate {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (k : ℕ)
    (a : Candidate) : Prop :=
  ¬ ∃ b, tournament_covers E k b a

@[blueprint "def:copeland-winner"
  (statement := /-- A Copeland output is an uncovered candidate whose Copeland score is at least that of every uncovered candidate. This predicate permits arbitrary tie-breaking among such candidates. -/)
  (title := /-- Copeland output from the uncovered set -/)
  (latexEnv := "definition")]
def copeland_winner {Candidate Voter Point : Type*}
    [Fintype Candidate] [DecidableEq Candidate]
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (k : ℕ)
    (a : Candidate) : Prop :=
  uncovered_candidate E k a ∧
    ∀ b, uncovered_candidate E k b →
      copeland_score E k b ≤ copeland_score E k a

@[blueprint "def:social-optimum"
  (statement := /-- A candidate $c^*$ is socially optimal when $\operatorname{SC}_E(c^*)\leq\operatorname{SC}_E(c)$ for every candidate $c$. -/)
  (title := /-- Socially optimal candidate -/)
  (latexEnv := "definition")]
def social_optimum {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (optimal : Candidate) : Prop :=
  ∀ c, social_cost E optimal ≤ social_cost E c

@[blueprint "def:copeland-distortion-at-most"
  (statement := /-- The size-$k$ Random Choice Copeland rule has distortion at most $D$ on $E$ when every Copeland output $w$ and every social optimum $c^*$ satisfy
  \[
    \operatorname{SC}_E(w)\leq D\operatorname{SC}_E(c^*).
  \]
  Universal quantification over metric elections gives the usual worst-case metric distortion guarantee. -/)
  (title := /-- Copeland distortion bound -/)
  (latexEnv := "definition")]
def copeland_distortion_at_most {Candidate Voter Point : Type*}
    [Fintype Candidate] [DecidableEq Candidate]
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (k : ℕ) (D : ℝ) : Prop :=
  ∀ winner optimal,
    copeland_winner E k winner → social_optimum E optimal →
      social_cost E winner ≤ D * social_cost E optimal

@[blueprint "def:random-choice-program-term"
  (statement := /-- For integers $k,\ell$ and parameters $\omega,\alpha\in\mathbb R$, define the $\ell$th summand of the Random Choice optimization constraint by
  \[
  {k\choose\ell}\alpha^\ell(1-\alpha)^{k-\ell}
  \frac{\ell\omega}{\ell\omega+k-\ell}.
  \] -/)
  (title := /-- Random Choice program summand -/)
  (latexEnv := "definition")]
noncomputable def random_choice_program_term
    (k ell : ℕ) (omega alpha : ℝ) : ℝ :=
  (Nat.choose k ell : ℝ) * alpha ^ ell * (1 - alpha) ^ (k - ell) *
    (((ell : ℝ) * omega) /
      ((ell : ℝ) * omega + ((k - ell : ℕ) : ℝ)))

@[blueprint "def:random-choice-program-feasible"
  (statement := /-- A pair $(\omega,\alpha)$ is feasible for the size-$k$ program if $0\leq\omega,\alpha\leq1$ and
  \[
    \sum_{\ell=1}^k {k\choose\ell}\alpha^\ell(1-\alpha)^{k-\ell}
      \frac{\ell\omega}{\ell\omega+k-\ell}\geq\frac12.
  \] -/)
  (title := /-- Feasible region of the Random Choice program -/)
  (latexEnv := "definition")]
def random_choice_program_feasible (k : ℕ) (omega alpha : ℝ) : Prop :=
  0 ≤ omega ∧ omega ≤ 1 ∧ 0 ≤ alpha ∧ alpha ≤ 1 ∧
    (1 / 2 : ℝ) ≤ (Finset.range k).sum (fun j =>
      random_choice_program_term k (j + 1) omega alpha)

@[blueprint "def:random-choice-program-objective"
  (statement := /-- The objective of the Random Choice program is $(1-\alpha)-\alpha\omega$. -/)
  (title := /-- Objective of the Random Choice program -/)
  (latexEnv := "definition")]
def random_choice_program_objective (omega alpha : ℝ) : ℝ :=
  (1 - alpha) - alpha * omega

@[blueprint "def:random-choice-program-bound"
  (statement := /-- A number $\zeta$ bounds the size-$k$ Random Choice program if every feasible pair $(\omega,\alpha)$ has objective at most $\zeta$. -/)
  (title := /-- Upper bound for the Random Choice program -/)
  (latexEnv := "definition")]
def random_choice_program_bound (k : ℕ) (zeta : ℝ) : Prop :=
  ∀ omega alpha,
    random_choice_program_feasible k omega alpha →
      random_choice_program_objective omega alpha ≤ zeta

@[blueprint "def:admissible-threshold"
  (statement := /-- A distortion threshold $\zeta$ is admissible when $0\leq\zeta<1$. -/)
  (title := /-- Admissible distortion threshold -/)
  (latexEnv := "definition")]
def admissible_threshold (zeta : ℝ) : Prop :=
  0 ≤ zeta ∧ zeta < 1

@[blueprint "def:distortion-factor"
  (statement := /-- The distortion factor associated with $\zeta<1$ is
  \[
    \Delta(\zeta)=\left(\frac{1+\zeta}{1-\zeta}\right)^2.
  \] -/)
  (title := /-- Distortion factor associated with a threshold -/)
  (latexEnv := "definition")]
noncomputable def distortion_factor (zeta : ℝ) : ℝ :=
  ((1 + zeta) / (1 - zeta)) ^ 2

@[blueprint "def:pairwise-distortion-control"
  (statement := /-- Pairwise distortion control at threshold $\zeta$ means: $\zeta$ is admissible; every pair of distinct candidates is oriented in at least one direction by the deliberation tournament; and every edge $a\succ b$ satisfies
  \[
    (1-\zeta)\operatorname{SC}_E(a)
      \leq(1+\zeta)\operatorname{SC}_E(b).
  \] -/)
  (title := /-- Pairwise social-cost control -/)
  (latexEnv := "definition")]
def pairwise_distortion_control {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (k : ℕ) (zeta : ℝ) : Prop :=
  admissible_threshold zeta ∧
    (∀ a b, a ≠ b →
      deliberation_dominates E k a b ∨ deliberation_dominates E k b a) ∧
    ∀ a b, a ≠ b → deliberation_dominates E k a b →
      (1 - zeta) * social_cost E a ≤
        (1 + zeta) * social_cost E b

@[blueprint "lem:random-choice-program-bound-two-generic"
  (statement := /-- There exists $\zeta_2\in\mathbb R$ with $0\leq\zeta_2<1$ such that every pair $\omega,\alpha\in\mathbb R$ feasible for the size-two Random Choice program of \cref{def:random-choice-program-feasible} satisfies
  \[
    (1-\alpha)-\alpha\omega\leq\zeta_2,
  \]
  and
  \[
    \left(\frac{1+\zeta_2}{1-\zeta_2}\right)^2\leq3.344.
  \] -/)
  (proof := /-- Set $\zeta_2=2929/10000$ and
  $T=1-\zeta_2=7071/10000$. The inequalities
  $0\leq\zeta_2<1$ give \cref{def:admissible-threshold}. Let
  $(\omega,\alpha)$ satisfy
  \cref{def:random-choice-program-feasible} for $k=2$. Expanding
  \cref{def:random-choice-program-term} shows first that $\omega>0$ and
  then that the feasibility constraint is
  \[
    \frac12\leq
    P_\omega(\alpha):=
      2\alpha(1-\alpha)\frac{\omega}{1+\omega}+\alpha^2.
  \]
  For $0\leq a\leq b\leq1$, the identity
  \[
    P_\omega(b)-P_\omega(a)=
      \frac{(b-a)\bigl(2\omega+(a+b)(1-\omega)\bigr)}{1+\omega}
  \]
  is nonnegative when $0<\omega\leq1$; hence $P_\omega$ is
  nondecreasing on $[0,1]$.
  Suppose that the bound in
  \cref{def:random-choice-program-bound,def:random-choice-program-objective}
  fails. Then $\alpha(1+\omega)<T$. For
  $\beta=T/(1+\omega)$ one has
  $0\leq\alpha<\beta\leq1$, and hence
  $P_\omega(\alpha)\leq P_\omega(\beta)$. Exact reduction to a common
  denominator gives
  \[
    \frac12-P_\omega(\beta)=
    \frac{50000000\omega^3+8580000\omega^2+
      58579041\omega+959}
    {100000000(1+\omega)^3}>0,
  \]
  contradicting feasibility. Thus $\zeta_2$ satisfies
  \cref{def:random-choice-program-bound}. Finally,
  \cref{def:distortion-factor} and exact cross-multiplication give
  \[
    \Delta(\zeta_2)=\frac{167159041}{49999041}
      <\frac{418}{125}=3.344,
  \]
  because
  \[
    418\cdot49999041-125\cdot167159041=4719013>0.
  \]
  -/)
  (title := /-- Certified program bound for groups of size two -/)
  (latexEnv := "lemma")]
lemma random_choice_program_bound_two_generic :
    ∃ zeta : ℝ, admissible_threshold zeta ∧
      random_choice_program_bound 2 zeta ∧ distortion_factor zeta ≤ 3.344 := by
  refine ⟨2929 / 10000, by norm_num [admissible_threshold], ?_,
    by norm_num [distortion_factor]⟩
  rintro omega alpha ⟨homega0, homega1, halpha0, halpha1, hsum⟩
  norm_num [random_choice_program_term, random_choice_program_objective,
    Finset.sum_range_succ] at hsum ⊢
  have homega_ne : omega ≠ 0 := by
    intro homega
    subst omega
    norm_num at hsum
  have homega_pos : 0 < omega := lt_of_le_of_ne homega0 (Ne.symm homega_ne)
  rw [div_self (mul_ne_zero (by norm_num) homega_ne)] at hsum
  by_contra hobjective
  simp only [not_le] at hobjective
  let beta : ℝ := (7071 / 10000) / (1 + omega)
  have hdenom : 0 < 1 + omega := by linarith
  have hbeta0 : 0 ≤ beta := by
    exact div_nonneg (by norm_num) (le_of_lt hdenom)
  have hbeta1 : beta ≤ 1 := by
    rw [show beta = (7071 / 10000) / (1 + omega) by rfl]
    exact (div_le_one₀ hdenom).2 (by linarith)
  have halpha_beta : alpha < beta := by
    rw [show beta = (7071 / 10000) / (1 + omega) by rfl]
    apply (lt_div_iff₀ hdenom).2
    nlinarith
  have hbracket :
      0 ≤ 2 * omega + (alpha + beta) * (1 - omega) := by
    positivity
  have hfactor :
      0 ≤ (beta - alpha) *
        (2 * omega + (alpha + beta) * (1 - omega)) :=
    mul_nonneg (sub_nonneg.mpr (le_of_lt halpha_beta)) hbracket
  have hmono_identity :
      (2 * beta * (1 - beta) * (omega / (omega + 1)) + beta ^ 2) -
          (2 * alpha * (1 - alpha) * (omega / (omega + 1)) + alpha ^ 2) =
        (beta - alpha) *
          (2 * omega + (alpha + beta) * (1 - omega)) / (1 + omega) := by
    field_simp
    ring
  have hfactor_div :
      0 ≤ (beta - alpha) *
        (2 * omega + (alpha + beta) * (1 - omega)) / (1 + omega) :=
    div_nonneg hfactor (le_of_lt hdenom)
  have hmono :
      2 * alpha * (1 - alpha) * (omega / (omega + 1)) + alpha ^ 2 ≤
        2 * beta * (1 - beta) * (omega / (omega + 1)) + beta ^ 2 := by
    nlinarith [hmono_identity, hfactor_div]
  have hcertificate_identity :
      (1 / 2 : ℝ) -
          (2 * beta * (1 - beta) * (omega / (omega + 1)) + beta ^ 2) =
        (50000000 * omega ^ 3 + 8580000 * omega ^ 2 +
            58579041 * omega + 959) /
          (100000000 * (1 + omega) ^ 3) := by
    dsimp [beta]
    field_simp [ne_of_gt hdenom]
    ring
  have hnumerator :
      0 < 50000000 * omega ^ 3 + 8580000 * omega ^ 2 +
        58579041 * omega + 959 := by
    positivity
  have hdenominator : 0 < 100000000 * (1 + omega) ^ 3 := by
    positivity
  have hcertificate :
      0 < (50000000 * omega ^ 3 + 8580000 * omega ^ 2 +
          58579041 * omega + 959) /
        (100000000 * (1 + omega) ^ 3) :=
    div_pos hnumerator hdenominator
  norm_num at hsum
  nlinarith [hmono, hcertificate_identity, hcertificate]

@[blueprint "lem:random-choice-program-bound-three"
  (statement := /-- There exists an admissible threshold $\zeta_3$ that bounds the Random Choice program for $k=3$ and satisfies $\Delta(\zeta_3)\leq2.31$. -/)
  (proof := /-- Set $\zeta_3=2063/10000$. The defining inequalities in \cref{def:admissible-threshold} hold, and exact rational arithmetic in \cref{def:distortion-factor} gives $((1+\zeta_3)/(1-\zeta_3))^2\leq231/100$. Let $(\omega,\alpha)$ satisfy \cref{def:random-choice-program-feasible} for $k=3$, and expand its sum using \cref{def:random-choice-program-term}. If $\omega=0$, every summand is zero under the field convention for division by zero, contradicting feasibility. Thus $\omega>0$. Put $c_1=\omega/(\omega+2)$ and $c_2=2\omega/(2\omega+1)$. The bounds $0<\omega\leq1$ imply $0\leq c_1\leq c_2\leq1$, and the expanded constraint is $1/2\leq P_\omega(\alpha)$, where
  \[
    P_\omega(a)=3a(1-a)^2c_1+3a^2(1-a)c_2+a^3.
  \]
  Rewrite this polynomial as
  \[
    P_\omega(a)=c_1\bigl(1-(1-a)^3\bigr)
      +(c_2-c_1)(3a^2-2a^3)+(1-c_2)a^3.
  \]
  Each of the three displayed polynomials in $a$ is nondecreasing on $[0,1]$, and all three coefficients are nonnegative; hence $P_\omega$ is nondecreasing there. Suppose that the bound in \cref{def:random-choice-program-bound,def:random-choice-program-objective} failed. Then $\alpha(1+\omega)<7937/10000$. For $\beta=(7937/10000)/(1+\omega)$ one has $0\leq\alpha\leq\beta\leq1$, so $P_\omega(\alpha)\leq P_\omega(\beta)$. Direct clearing of the positive denominator gives
  \[
  \frac12-P_\omega(\beta)=
  \frac{10^{12}\omega^5+737800000000\omega^4+3374258140000\omega^3
    +975601988094\omega^2+1339137883812\omega+1988094}
  {10^{12}(1+\omega)^3(\omega+2)(2\omega+1)}>0.
  \]
  This contradicts $1/2\leq P_\omega(\alpha)$, and therefore every feasible objective is at most $2063/10000$, as required. -/)
  (title := /-- Reported numerical program bound for groups of size three -/)
  (latexEnv := "lemma")]
lemma random_choice_program_bound_three :
    ∃ zeta : ℝ, admissible_threshold zeta ∧
      random_choice_program_bound 3 zeta ∧ distortion_factor zeta ≤ 2.31 := by
  refine ⟨0.2063, by norm_num [admissible_threshold], ?_,
    by norm_num [distortion_factor]⟩
  rintro omega alpha ⟨hw0, hw1, ha0, ha1, hfeas⟩
  norm_num [random_choice_program_feasible, random_choice_program_term,
    random_choice_program_objective, Finset.sum_range_succ] at hfeas ⊢
  rcases eq_or_lt_of_le hw0 with rfl | hw0
  · norm_num at hfeas
  have hd1 : 0 < omega + 2 := by positivity
  have hd2 : 0 < 2 * omega + 1 := by positivity
  have hd3 : 3 * omega ≠ 0 := by positivity
  rw [div_self hd3] at hfeas
  have hc₁0 : 0 ≤ omega / (omega + 2) := by positivity
  have hc₁c₂ :
      omega / (omega + 2) ≤ 2 * omega / (2 * omega + 1) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    nlinarith [sq_nonneg omega]
  have hc₂1 : 2 * omega / (2 * omega + 1) ≤ 1 := by
    apply (div_le_iff₀ hd2).2
    linarith
  have hmono (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
      3 * a * (1 - a) ^ 2 * (omega / (omega + 2)) +
          3 * a ^ 2 * (1 - a) * (2 * omega / (2 * omega + 1)) + a ^ 3 ≤
        3 * b * (1 - b) ^ 2 * (omega / (omega + 2)) +
          3 * b ^ 2 * (1 - b) * (2 * omega / (2 * omega + 1)) + b ^ 3 := by
    have hb0 : 0 ≤ b := ha.trans hab
    have ha1 : a ≤ 1 := hab.trans hb
    have hF₁ : 1 - (1 - a) ^ 3 ≤ 1 - (1 - b) ^ 3 := by
      have hleft : 0 ≤ (1 - a) - (1 - b) := by linarith
      have hright : 0 ≤
          (1 - a) ^ 2 + (1 - a) * (1 - b) + (1 - b) ^ 2 := by
        positivity
      have hprod : 0 ≤ ((1 - a) - (1 - b)) *
          ((1 - a) ^ 2 + (1 - a) * (1 - b) + (1 - b) ^ 2) := by
        exact mul_nonneg hleft hright
      nlinarith
    have hF₂ : 3 * a ^ 2 - 2 * a ^ 3 ≤ 3 * b ^ 2 - 2 * b ^ 3 := by
      have haa : 0 ≤ a * (1 - a) := mul_nonneg ha (sub_nonneg.mpr ha1)
      have hbb : 0 ≤ b * (1 - b) := mul_nonneg hb0 (sub_nonneg.mpr hb)
      have hab' : 0 ≤ (a + b) * (2 - a - b) :=
        mul_nonneg (add_nonneg ha hb0) (by linarith)
      have hq : 0 ≤ a * (1 - a) + b * (1 - b) +
          (a + b) * (2 - a - b) := by positivity
      have hprod : 0 ≤ (b - a) *
          (3 * (a + b) - 2 * (a ^ 2 + a * b + b ^ 2)) := by
        nlinarith
      nlinarith
    have hF₃ : a ^ 3 ≤ b ^ 3 := by
      have hprod : 0 ≤ (b - a) * (b ^ 2 + b * a + a ^ 2) := by
        positivity
      nlinarith
    have hsum : 0 ≤
        (omega / (omega + 2)) *
            ((1 - (1 - b) ^ 3) - (1 - (1 - a) ^ 3)) +
          (2 * omega / (2 * omega + 1) - omega / (omega + 2)) *
            ((3 * b ^ 2 - 2 * b ^ 3) - (3 * a ^ 2 - 2 * a ^ 3)) +
          (1 - 2 * omega / (2 * omega + 1)) * (b ^ 3 - a ^ 3) := by
      positivity
    nlinarith
  by_contra hgoal
  have ht : alpha * (1 + omega) < 7937 / 10000 := by
    have hgoal' := lt_of_not_ge hgoal
    nlinarith
  let beta : ℝ := (7937 / 10000) / (1 + omega)
  have hden : 0 < 1 + omega := by positivity
  have hab : alpha ≤ beta := by
    change alpha ≤ (7937 / 10000) / (1 + omega)
    apply (le_div_iff₀ hden).2
    nlinarith
  have hb0 : 0 ≤ beta := by
    change 0 ≤ (7937 / 10000) / (1 + omega)
    positivity
  have hb1 : beta ≤ 1 := by
    change (7937 / 10000) / (1 + omega) ≤ 1
    apply (div_le_iff₀ hden).2
    nlinarith
  have hpmono := hmono alpha beta ha0 hab hb1
  have hboundary :
      3 * beta * (1 - beta) ^ 2 * (omega / (omega + 2)) +
          3 * beta ^ 2 * (1 - beta) * (2 * omega / (2 * omega + 1)) +
          beta ^ 3 < 1 / 2 := by
    dsimp [beta]
    field_simp
    norm_num
    nlinarith [sq_nonneg omega, pow_nonneg hw0.le 3,
      pow_nonneg hw0.le 4, pow_nonneg hw0.le 5]
  nlinarith

@[blueprint "lem:random-choice-program-bound-four"
  (statement := /-- For group size four, there exists $\zeta\in\mathbb R$ with
  $0\leq\zeta<1$ such that every pair $(\omega,\alpha)$ feasible for the
  size-four Random Choice program satisfies
  $(1-\alpha)-\alpha\omega\leq\zeta$, and
  $((1+\zeta)/(1-\zeta))^2\leq1901/1000$. -/)
  (proof := /-- Specialize the optimization program in
  \cref{def:random-choice-program-feasible,def:random-choice-program-objective}
  to $k=4$, and set $\zeta_4=199/1250$.  If $\omega=0$, the
  feasibility sum is zero, so no pair with $\omega=0$ is feasible.  Suppose
  henceforth that $0<\omega\leq1$, and put
  \[
    c_1=\frac{\omega}{\omega+3},\qquad
    c_2=\frac{\omega}{\omega+1},\qquad
    c_3=\frac{3\omega}{3\omega+1}.
  \]
  The left-hand side of the feasibility constraint is
  \[
  \begin{aligned}
  P_\omega(a)={}&c_1\bigl(1-(1-a)^4\bigr)
    +(c_2-c_1)(6a^2-8a^3+3a^4)\\
    &+(c_3-c_2)(4a^3-3a^4)+(1-c_3)a^4.
  \end{aligned}
  \]
  Here $0\leq c_1\leq c_2\leq c_3\leq1$.  To prove monotonicity without
  invoking calculus, fix $0\leq a\leq b\leq1$ and put $d=b-a$ and
  $u=1-b$.  The increments of the four parenthesized polynomials, in the
  displayed order, factor as
  \[
  \begin{aligned}
  d(4u^3+6u^2d+4ud^2+d^3),\qquad
  d(12au^2+12aud+4ad^2+6u^2d+4ud^2+d^3),\\
  d(12a^2u+6a^2d+12aud+4ad^2+4ud^2+d^3),\qquad
  d(4a^3+6a^2d+4ad^2+d^3).
  \end{aligned}
  \]
  Every term is nonnegative, as are the coefficients $c_1$,
  $c_2-c_1$, $c_3-c_2$, and $1-c_3$.  Hence $P_\omega$ is
  nondecreasing on $[0,1]$.

  If a feasible pair violated the claimed objective bound, then
  $\alpha(1+\omega)<1051/1250$.  With
  $\beta=(1051/1250)/(1+\omega)$, one has
  $0\leq\alpha<\beta\leq1$, and hence
  $1/2\leq P_\omega(\alpha)\leq P_\omega(\beta)$.  Exact reduction to a
  common denominator instead gives
  \[
  \frac12-P_\omega(\beta)=\frac{
  3662109375000\omega^7+5884765625000\omega^6
  +25643075000000\omega^5+20369830860000\omega^4
  +29568274247603\omega^3+8852003817191\omega^2
  +5518261807809\omega+1679267397}
  {2441406250000(1+\omega)^5(\omega+3)(3\omega+1)}>0,
  \]
  a contradiction.  Consequently $\zeta_4$ satisfies
  \cref{def:admissible-threshold,def:random-choice-program-bound}.  Finally,
  \cref{def:distortion-factor} yields
  \[
    \Delta(\zeta_4)=\frac{2099601}{1104601}
      <\frac{1901}{1000}=1.901,
  \]
  since $1901\cdot1104601-1000\cdot2099601=245501>0$. -/)
  (title := /-- Certified program bound for groups of size four -/)
  (latexEnv := "lemma")]
lemma random_choice_program_bound_four
    : ∃ zeta : ℝ, admissible_threshold zeta ∧
      random_choice_program_bound 4 zeta ∧ distortion_factor zeta ≤ 1.901 := by
  refine ⟨199 / 1250, by norm_num [admissible_threshold], ?_,
    by norm_num [distortion_factor]⟩
  rintro omega alpha ⟨hw0, hw1, ha0, ha1, hfeas⟩
  norm_num [random_choice_program_feasible, random_choice_program_term,
    random_choice_program_objective, Finset.sum_range_succ] at hfeas ⊢
  rcases eq_or_lt_of_le hw0 with rfl | hw0
  · norm_num at hfeas
  have hd1 : 0 < omega + 3 := by positivity
  have hd2 : 0 < omega + 1 := by positivity
  have hd3 : 0 < 3 * omega + 1 := by positivity
  have hd4 : 4 * omega ≠ 0 := by positivity
  rw [div_self hd4] at hfeas
  norm_num [Nat.choose] at hfeas
  have htwo : 2 * omega / (2 * omega + 2) = omega / (omega + 1) := by
    field_simp [ne_of_gt hd2]
    <;> ring
  rw [htwo] at hfeas
  have hc₁0 : 0 ≤ omega / (omega + 3) := by positivity
  have hc₁c₂ : omega / (omega + 3) ≤ omega / (omega + 1) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    nlinarith [sq_nonneg omega]
  have hc₂c₃ : omega / (omega + 1) ≤ 3 * omega / (3 * omega + 1) := by
    apply (div_le_div_iff₀ hd2 hd3).2
    nlinarith [sq_nonneg omega]
  have hc₃1 : 3 * omega / (3 * omega + 1) ≤ 1 := by
    apply (div_le_one₀ hd3).2
    linarith
  have hmono (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
      4 * a * (1 - a) ^ 3 * (omega / (omega + 3)) +
            6 * a ^ 2 * (1 - a) ^ 2 * (omega / (omega + 1)) +
          4 * a ^ 3 * (1 - a) * (3 * omega / (3 * omega + 1)) + a ^ 4 ≤
        4 * b * (1 - b) ^ 3 * (omega / (omega + 3)) +
            6 * b ^ 2 * (1 - b) ^ 2 * (omega / (omega + 1)) +
          4 * b ^ 3 * (1 - b) * (3 * omega / (3 * omega + 1)) + b ^ 4 := by
    have hb0 : 0 ≤ b := ha.trans hab
    have ha1 : a ≤ 1 := hab.trans hb
    have hF₁ : 1 - (1 - a) ^ 4 ≤ 1 - (1 - b) ^ 4 := by
      have hq : 0 ≤ 4 * (1 - b) ^ 3 +
          6 * (1 - b) ^ 2 * (b - a) +
          4 * (1 - b) * (b - a) ^ 2 + (b - a) ^ 3 := by
        positivity
      have hp := mul_nonneg (sub_nonneg.mpr hab) hq
      nlinarith
    have hF₂ : 6 * a ^ 2 - 8 * a ^ 3 + 3 * a ^ 4 ≤
        6 * b ^ 2 - 8 * b ^ 3 + 3 * b ^ 4 := by
      have hq : 0 ≤ 12 * a * (1 - b) ^ 2 +
          12 * a * (1 - b) * (b - a) + 4 * a * (b - a) ^ 2 +
          6 * (1 - b) ^ 2 * (b - a) +
          4 * (1 - b) * (b - a) ^ 2 + (b - a) ^ 3 := by
        positivity
      have hp := mul_nonneg (sub_nonneg.mpr hab) hq
      nlinarith
    have hF₃ : 4 * a ^ 3 - 3 * a ^ 4 ≤ 4 * b ^ 3 - 3 * b ^ 4 := by
      have hq : 0 ≤ 12 * a ^ 2 * (1 - b) +
          6 * a ^ 2 * (b - a) + 12 * a * (1 - b) * (b - a) +
          4 * a * (b - a) ^ 2 + 4 * (1 - b) * (b - a) ^ 2 +
          (b - a) ^ 3 := by
        positivity
      have hp := mul_nonneg (sub_nonneg.mpr hab) hq
      nlinarith
    have hF₄ : a ^ 4 ≤ b ^ 4 := by
      have hq : 0 ≤ 4 * a ^ 3 + 6 * a ^ 2 * (b - a) +
          4 * a * (b - a) ^ 2 + (b - a) ^ 3 := by
        positivity
      have hp := mul_nonneg (sub_nonneg.mpr hab) hq
      nlinarith
    have hsum : 0 ≤
        (omega / (omega + 3)) *
            ((1 - (1 - b) ^ 4) - (1 - (1 - a) ^ 4)) +
          (omega / (omega + 1) - omega / (omega + 3)) *
            ((6 * b ^ 2 - 8 * b ^ 3 + 3 * b ^ 4) -
              (6 * a ^ 2 - 8 * a ^ 3 + 3 * a ^ 4)) +
          (3 * omega / (3 * omega + 1) - omega / (omega + 1)) *
            ((4 * b ^ 3 - 3 * b ^ 4) - (4 * a ^ 3 - 3 * a ^ 4)) +
          (1 - 3 * omega / (3 * omega + 1)) * (b ^ 4 - a ^ 4) := by
      positivity
    nlinarith
  by_contra hgoal
  have ht : alpha * (1 + omega) < 1051 / 1250 := by
    have hgoal' := lt_of_not_ge hgoal
    nlinarith
  let beta : ℝ := (1051 / 1250) / (1 + omega)
  have hden : 0 < 1 + omega := by positivity
  have hab : alpha ≤ beta := by
    change alpha ≤ (1051 / 1250) / (1 + omega)
    apply (le_div_iff₀ hden).2
    nlinarith
  have hb0 : 0 ≤ beta := by
    change 0 ≤ (1051 / 1250) / (1 + omega)
    positivity
  have hb1 : beta ≤ 1 := by
    change (1051 / 1250) / (1 + omega) ≤ 1
    apply (div_le_iff₀ hden).2
    nlinarith
  have hpmono := hmono alpha beta ha0 hab hb1
  have hboundary :
      4 * beta * (1 - beta) ^ 3 * (omega / (omega + 3)) +
            6 * beta ^ 2 * (1 - beta) ^ 2 * (omega / (omega + 1)) +
          4 * beta ^ 3 * (1 - beta) * (3 * omega / (3 * omega + 1)) +
        beta ^ 4 < 1 / 2 := by
    dsimp [beta]
    field_simp
    norm_num
    nlinarith [sq_nonneg omega, pow_nonneg hw0.le 3,
      pow_nonneg hw0.le 4, pow_nonneg hw0.le 5,
      pow_nonneg hw0.le 6, pow_nonneg hw0.le 7]
  nlinarith

@[blueprint "lem:random-choice-scalar-replacement-bound"
  (statement := /-- Let $A,B,x,\omega\in\mathbb R$ satisfy $A,B\geq0$, $A+B>0$, $-1\leq x\leq1$, and $0\leq\omega\leq1$. Writing $x_+=\max\{x,0\}$ and $x_-=\max\{-x,0\}$, the one-coordinate Random Choice ratio is bounded by the affine tangent majorant obtained from replacing $x$ by $1$ or $-\omega$. -/)
  (proof := /-- Split according to the sign of $x$. For $x\geq0$, clear the positive denominators and use the chord bound for $A/(A+B+x)$ together with the tangent bound at $\omega$ for $(A+t)/(A+B+t)$ evaluated at $t=0$. For $x\leq0$, clear the same denominators and apply the tangent bound at $\omega$ directly with $t=-x$. The hypotheses on $A+B$, $x$, and $\omega$ make every cleared denominator positive. -/)
  (title := /-- Scalar two-point replacement bound -/)
  (latexEnv := "lemma")]
lemma random_choice_scalar_replacement_bound
    (A B x omega : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B)
    (hx_lower : -1 ≤ x) (hx_upper : x ≤ 1)
    (homega_nonneg : 0 ≤ omega) (homega_le : omega ≤ 1) :
    (A + max (-x) 0) / (A + max (-x) 0 + B + max x 0) ≤
      max x 0 * (A / (A + B + 1)) +
        (1 - max x 0) * ((A + omega) / (A + omega + B)) +
        B / (A + B + omega) ^ 2 *
          (max (-x) 0 - (1 - max x 0) * omega) := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    have hCx : 0 < A + B + x := by linarith
    have hC1 : 0 < A + B + 1 := by linarith
    have hCw : 0 < A + B + omega := by linarith
    have hdiff :
        (x * (A / (A + B + 1)) +
              (1 - x) * ((A + omega) / (A + omega + B)) +
              B / (A + B + omega) ^ 2 * (0 - (1 - x) * omega)) -
            A / (A + B + x) =
          A * x * (1 - x) /
              ((A + B) * (A + B + 1) * (A + B + x)) +
            (1 - x) * B * omega ^ 2 /
              ((A + B) * (A + B + omega) ^ 2) := by
      rw [show A + omega + B = A + B + omega by ring]
      field_simp [ne_of_gt hAB, ne_of_gt hCx, ne_of_gt hC1, ne_of_gt hCw]
      ring
    have hnonneg :
        0 ≤
          (x * (A / (A + B + 1)) +
                (1 - x) * ((A + omega) / (A + omega + B)) +
                B / (A + B + omega) ^ 2 * (0 - (1 - x) * omega)) -
              A / (A + B + x) := by
      rw [hdiff]
      positivity
    norm_num at hnonneg ⊢
    linarith
  · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
    have hCnx : 0 < A + B - x := by linarith
    have hCw : 0 < A + B + omega := by linarith
    have hdiff :
        ((A + omega) / (A + omega + B) +
              B / (A + B + omega) ^ 2 * (-x - omega)) -
            (A - x) / (A + B - x) =
          B * (x + omega) ^ 2 /
            ((A + B + omega) ^ 2 * (A + B - x)) := by
      rw [show A + omega + B = A + B + omega by ring]
      field_simp [ne_of_gt hCnx, ne_of_gt hCw]
      ring
    have hnonneg :
        0 ≤
          ((A + omega) / (A + omega + B) +
                B / (A + B + omega) ^ 2 * (-x - omega)) -
              (A - x) / (A + B - x) := by
      rw [hdiff]
      positivity
    norm_num at hnonneg ⊢
    ring_nf at hnonneg ⊢
    linarith

@[blueprint "lem:random-choice-one-coordinate-integral-bound"
  (statement := /-- Let $D$ be an integrable real random variable with $-1\leq D\leq1$ almost everywhere. Put $P=\int D_+$, $N=\int D_-$, $\alpha=1-P$, and $\omega=N/\alpha$, and suppose $0<\alpha$ and $0\leq\omega\leq1$. For all $A,B\geq0$ with $A+B>0$, integrating one Random Choice coordinate is bounded above by replacing that coordinate by $1$ with mass $P$ and by $-\omega$ with mass $\alpha$. -/)
  (proof := /-- Apply \cref{lem:random-choice-scalar-replacement-bound} almost everywhere and integrate. The positive-part coefficient integrates to $P$, the complementary coefficient integrates to $1-P=\alpha$, and the affine tangent-error term integrates to $N-\alpha\omega=0$. Integrability follows from the assumed integrability of $D$, closure under positive and negative parts, and the fact that every displayed ratio lies in $[0,1]$ because $A,B\geq0$ and $A+B>0$. -/)
  (title := /-- Integrated one-coordinate replacement -/)
  (latexEnv := "lemma")]
lemma random_choice_one_coordinate_integral_bound
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsProbabilityMeasure mu]
    (D : X → ℝ) (hD : Integrable D mu)
    (hDbounds : ∀ᵐ x ∂mu, -1 ≤ D x ∧ D x ≤ 1)
    (P N alpha omega A B : ℝ)
    (hP : P = ∫ x, max (D x) 0 ∂mu)
    (hN : N = ∫ x, max (-(D x)) 0 ∂mu)
    (halpha : alpha = 1 - P) (halpha_pos : 0 < alpha)
    (homega : omega = N / alpha)
    (homega_nonneg : 0 ≤ omega) (homega_le : omega ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B) :
    (∫ x, (A + max (-(D x)) 0) /
        (A + max (-(D x)) 0 + B + max (D x) 0) ∂mu) ≤
      P * (A / (A + B + 1)) +
        alpha * ((A + omega) / (A + omega + B)) := by
  have hp_int : Integrable (fun x => max (D x) 0) mu :=
    hD.sup (integrable_const 0)
  have hn_int : Integrable (fun x => max (-(D x)) 0) mu :=
    hD.neg.sup (integrable_const 0)
  have hone_sub_p_int : Integrable (fun x => 1 - max (D x) 0) mu :=
    (integrable_const 1).sub hp_int
  have herr_int : Integrable
      (fun x => max (-(D x)) 0 - (1 - max (D x) 0) * omega) mu :=
    hn_int.sub (hone_sub_p_int.mul_const omega)
  have hrhs_int : Integrable
      (fun x =>
        max (D x) 0 * (A / (A + B + 1)) +
          (1 - max (D x) 0) * ((A + omega) / (A + omega + B)) +
          B / (A + B + omega) ^ 2 *
            (max (-(D x)) 0 - (1 - max (D x) 0) * omega)) mu :=
    ((hp_int.mul_const _).add (hone_sub_p_int.mul_const _)).add
      (herr_int.const_mul _)
  have hratio_meas : AEStronglyMeasurable
      (fun x => (A + max (-(D x)) 0) /
        (A + max (-(D x)) 0 + B + max (D x) 0)) mu := by
    have hnum : AEMeasurable (fun x => A + max (-(D x)) 0) mu := by
      fun_prop
    have hdenom : AEMeasurable
        (fun x => A + max (-(D x)) 0 + B + max (D x) 0) mu := by
      fun_prop
    exact (hnum.div hdenom).aestronglyMeasurable
  have hratio_int : Integrable
      (fun x => (A + max (-(D x)) 0) /
        (A + max (-(D x)) 0 + B + max (D x) 0)) mu := by
    refine Integrable.mono' (integrable_const 1) hratio_meas ?_
    filter_upwards with x
    have hn : 0 ≤ max (-(D x)) 0 := le_max_right _ _
    have hp : 0 ≤ max (D x) 0 := le_max_right _ _
    have hden : 0 < A + max (-(D x)) 0 + B + max (D x) 0 := by
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) hden.le)]
    exact (div_le_one hden).2 (by linarith)
  have hpoint : ∀ᵐ x ∂mu,
      (A + max (-(D x)) 0) /
          (A + max (-(D x)) 0 + B + max (D x) 0) ≤
        max (D x) 0 * (A / (A + B + 1)) +
          (1 - max (D x) 0) * ((A + omega) / (A + omega + B)) +
          B / (A + B + omega) ^ 2 *
            (max (-(D x)) 0 - (1 - max (D x) 0) * omega) := by
    filter_upwards [hDbounds] with x hx
    exact random_choice_scalar_replacement_bound A B (D x) omega hA hB hAB
      hx.1 hx.2 homega_nonneg homega_le
  calc
    (∫ x, (A + max (-(D x)) 0) /
        (A + max (-(D x)) 0 + B + max (D x) 0) ∂mu) ≤
        ∫ x,
          (max (D x) 0 * (A / (A + B + 1)) +
            (1 - max (D x) 0) * ((A + omega) / (A + omega + B)) +
            B / (A + B + omega) ^ 2 *
              (max (-(D x)) 0 - (1 - max (D x) 0) * omega)) ∂mu :=
      integral_mono_ae hratio_int hrhs_int hpoint
    _ = P * (A / (A + B + 1)) +
        alpha * ((A + omega) / (A + omega + B)) := by
      have hp_eq : (∫ x, max (D x) 0 ∂mu) = P := hP.symm
      have hq_eq : (∫ x, 1 - max (D x) 0 ∂mu) = alpha := by
        rw [integral_sub (integrable_const 1) hp_int, integral_const,
          measureReal_univ_eq_one, hp_eq, halpha]
        simp
      have herr_eq :
          (∫ x, max (-(D x)) 0 - (1 - max (D x) 0) * omega ∂mu) = 0 := by
        rw [integral_sub hn_int (hone_sub_p_int.mul_const _), integral_mul_const,
          hq_eq, ← hN, homega]
        field_simp
        ring
      have hfirst :
          (∫ x, max (D x) 0 * (A / (A + B + 1)) +
            (1 - max (D x) 0) * ((A + omega) / (A + omega + B)) ∂mu) =
            P * (A / (A + B + 1)) +
              alpha * ((A + omega) / (A + omega + B)) := by
        rw [integral_add (hp_int.mul_const _) (hone_sub_p_int.mul_const _),
          integral_mul_const, integral_mul_const, hp_eq, hq_eq]
      have hthird :
          (∫ x, B / (A + B + omega) ^ 2 *
            (max (-(D x)) 0 - (1 - max (D x) 0) * omega) ∂mu) = 0 := by
        rw [integral_const_mul, herr_eq, mul_zero]
      have hsplit :
          (∫ x, (max (D x) 0 * (A / (A + B + 1)) +
              (1 - max (D x) 0) * ((A + omega) / (A + omega + B))) +
            B / (A + B + omega) ^ 2 *
              (max (-(D x)) 0 - (1 - max (D x) 0) * omega) ∂mu) =
            (∫ x, max (D x) 0 * (A / (A + B + 1)) +
              (1 - max (D x) 0) * ((A + omega) / (A + omega + B)) ∂mu) +
            ∫ x, B / (A + B + omega) ^ 2 *
              (max (-(D x)) 0 - (1 - max (D x) 0) * omega) ∂mu := by
        simpa only [Pi.add_apply] using
          integral_add ((hp_int.mul_const _).add (hone_sub_p_int.mul_const _))
            (herr_int.const_mul _)
      rw [hsplit, hfirst, hthird, add_zero]

@[blueprint "def:random-choice-bias-ratio"
  (statement := /-- For an offset pair $A,B\in\mathbb R$, a bias function $D:X\to\mathbb R$, and an ordered $n$-tuple $g$, define the Random Choice ratio after adding the negative and positive bias masses of the coordinates of $g$ to $A$ and $B$, respectively. -/)
  (title := /-- Offset Random Choice bias ratio -/)
  (latexEnv := "definition")]
noncomputable def random_choice_bias_ratio {X : Type*} {n : ℕ}
    (D : X → ℝ) (g : Fin n → X) (A B : ℝ) : ℝ :=
  (A + ∑ j, max (-(D (g j))) 0) /
    (A + ∑ j, max (-(D (g j))) 0 + B + ∑ j, max (D (g j)) 0)

@[blueprint "def:random-choice-replacement-value"
  (statement := /-- Recursively define the expected offset ratio after replacing each of $n$ independent bias coordinates by $1$ with mass $1-\alpha$ and by $-\omega$ with mass $\alpha$. -/)
  (title := /-- Recursive two-point replacement value -/)
  (latexEnv := "definition")]
noncomputable def random_choice_replacement_value : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ
  | 0, A, B, _, _ => A / (A + B)
  | n + 1, A, B, alpha, omega =>
      (1 - alpha) * random_choice_replacement_value n A (B + 1) alpha omega +
        alpha * random_choice_replacement_value n (A + omega) B alpha omega

@[blueprint "lem:random-choice-product-replacement-bound"
  (statement := /-- Let $D$ be a measurable integrable random variable in $[-1,1]$, and let $P,N,\alpha,\omega$ be its positive mass, negative mass, residual mass, and normalized negative mass as in \cref{lem:random-choice-one-coordinate-integral-bound}. For every $n\in\mathbb N$ and every $A,B\geq0$ with $A+B>0$, the product integral of the offset Random Choice ratio is at most the recursive two-point replacement value. -/)
  (proof := /-- Induct on $n$. The case $n=0$ is the integral of the constant specified by \cref{def:random-choice-bias-ratio}. For the successor step, use the measure-preserving head--tail decomposition of the finite product and Fubini's theorem. For almost every fixed tail, apply \cref{lem:random-choice-one-coordinate-integral-bound} to the head coordinate with offsets enlarged by the tail's negative and positive masses. Integrate this inequality over the tail and invoke the induction hypothesis for the two resulting offset ratios. The defining recursion in \cref{def:random-choice-replacement-value} is exactly the resulting convex combination. -/)
  (title := /-- Product two-point replacement bound -/)
  (latexEnv := "lemma")]
lemma random_choice_product_replacement_bound
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsProbabilityMeasure mu]
    (D : X → ℝ) (hDmeas : Measurable D) (hD : Integrable D mu)
    (hDbounds : ∀ᵐ x ∂mu, -1 ≤ D x ∧ D x ≤ 1)
    (P N alpha omega : ℝ)
    (hP : P = ∫ x, max (D x) 0 ∂mu)
    (hN : N = ∫ x, max (-(D x)) 0 ∂mu)
    (halpha : alpha = 1 - P) (halpha_pos : 0 < alpha)
    (homega : omega = N / alpha)
    (homega_nonneg : 0 ≤ omega) (homega_le : omega ≤ 1) :
    ∀ (n : ℕ) (A B : ℝ), 0 ≤ A → 0 ≤ B → 0 < A + B →
      (∫ g, random_choice_bias_ratio D g A B ∂
        (Measure.pi (fun _ : Fin n => mu))) ≤
      random_choice_replacement_value n A B alpha omega := by
  intro n
  induction n with
  | zero =>
      intro A B hA hB hAB
      simp [random_choice_bias_ratio, random_choice_replacement_value]
  | succ n ih =>
      intro A B hA hB hAB
      let tailMeasure : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => mu)
      let F : X × (Fin n → X) → ℝ := fun z =>
        random_choice_bias_ratio D (Fin.cons z.1 z.2) A B
      have hFmeas : AEStronglyMeasurable F (mu.prod tailMeasure) := by
        have hcoord : ∀ j : Fin (n + 1),
            Measurable (fun z : X × (Fin n → X) =>
              D ((@Fin.cons n (fun _ : Fin (n + 1) => X) z.1 z.2) j)) := by
          intro j
          refine Fin.cases ?_ (fun i => ?_) j
          · simpa [Function.comp_def] using hDmeas.comp measurable_fst
          · simpa [Function.comp_def] using
              hDmeas.comp ((measurable_pi_apply i).comp measurable_snd)
        have : Measurable F := by
          have hnmeas : Measurable (fun z : X × (Fin n → X) =>
              ∑ j : Fin (n + 1),
                max (-(D ((@Fin.cons n (fun _ : Fin (n + 1) => X) z.1 z.2) j))) 0) :=
            Finset.measurable_sum _ fun j _ => (hcoord j).neg.max measurable_const
          have hpmeas : Measurable (fun z : X × (Fin n → X) =>
              ∑ j : Fin (n + 1),
                max (D ((@Fin.cons n (fun _ : Fin (n + 1) => X) z.1 z.2) j)) 0) :=
            Finset.measurable_sum _ fun j _ => (hcoord j).max measurable_const
          dsimp [F, random_choice_bias_ratio]
          exact (measurable_const.add hnmeas).div
            (((measurable_const.add hnmeas).add measurable_const).add hpmeas)
        exact this.aestronglyMeasurable
      have hFint : Integrable F (mu.prod tailMeasure) := by
        refine Integrable.mono' (integrable_const 1) hFmeas ?_
        filter_upwards with z
        have hn : 0 ≤ ∑ j : Fin (n + 1),
            max (-(D ((@Fin.cons n (fun _ : Fin (n + 1) => X) z.1 z.2) j))) 0 :=
          Finset.sum_nonneg fun _ _ => le_max_right _ _
        have hp : 0 ≤ ∑ j : Fin (n + 1),
            max (D ((@Fin.cons n (fun _ : Fin (n + 1) => X) z.1 z.2) j)) 0 :=
          Finset.sum_nonneg fun _ _ => le_max_right _ _
        have hden : 0 < A + (∑ j : Fin (n + 1),
              max (-(D ((@Fin.cons n (fun _ : Fin (n + 1) => X) z.1 z.2) j))) 0) +
            B + ∑ j : Fin (n + 1),
              max (D ((@Fin.cons n (fun _ : Fin (n + 1) => X) z.1 z.2) j)) 0 := by
          linarith
        dsimp [F, random_choice_bias_ratio]
        rw [abs_of_nonneg (div_nonneg (by linarith) hden.le)]
        exact (div_le_one hden).2 (by linarith)
      have hchange :
          (∫ g, random_choice_bias_ratio D g A B ∂
              (Measure.pi (fun _ : Fin (n + 1) => mu))) =
            ∫ z, F z ∂mu.prod tailMeasure := by
        have hmp := measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => mu) (0 : Fin (n + 1))
        have h := hmp.integral_comp' F
        simpa [F, tailMeasure] using h
      rw [hchange, integral_prod_symm F hFint]
      have hinner : ∀ᵐ g ∂tailMeasure,
          (∫ x, F (x, g) ∂mu) ≤
            P * random_choice_bias_ratio D g A (B + 1) +
              alpha * random_choice_bias_ratio D g (A + omega) B := by
        filter_upwards with g
        let A' : ℝ := A + ∑ j, max (-(D (g j))) 0
        let B' : ℝ := B + ∑ j, max (D (g j)) 0
        have hA' : 0 ≤ A' := by
          dsimp [A']
          have hn : 0 ≤ ∑ j, max (-(D (g j))) 0 :=
            Finset.sum_nonneg fun _ _ => le_max_right _ _
          linarith
        have hB' : 0 ≤ B' := by
          dsimp [B']
          have hp : 0 ≤ ∑ j, max (D (g j)) 0 :=
            Finset.sum_nonneg fun _ _ => le_max_right _ _
          linarith
        have hAB' : 0 < A' + B' := by
          dsimp [A', B']
          have hn : 0 ≤ ∑ j, max (-(D (g j))) 0 :=
            Finset.sum_nonneg fun _ _ => le_max_right _ _
          have hp : 0 ≤ ∑ j, max (D (g j)) 0 :=
            Finset.sum_nonneg fun _ _ => le_max_right _ _
          linarith
        have hone := random_choice_one_coordinate_integral_bound mu D hD hDbounds
          P N alpha omega A' B' hP hN halpha halpha_pos homega
          homega_nonneg homega_le hA' hB' hAB'
        dsimp [F, A', B'] at hone ⊢
        simpa [random_choice_bias_ratio, Fin.sum_univ_succ, add_assoc, add_left_comm,
          add_comm] using hone
      have hleft_int : Integrable
          (fun g : Fin n → X => random_choice_bias_ratio D g A (B + 1))
          tailMeasure := by
        have hmeas : AEStronglyMeasurable
            (fun g : Fin n → X => random_choice_bias_ratio D g A (B + 1))
            tailMeasure := by
          have : Measurable
              (fun g : Fin n → X => random_choice_bias_ratio D g A (B + 1)) := by
            dsimp [random_choice_bias_ratio]
            fun_prop
          exact this.aestronglyMeasurable
        refine Integrable.mono' (integrable_const 1) hmeas ?_
        filter_upwards with g
        have hn : 0 ≤ ∑ j, max (-(D (g j))) 0 :=
          Finset.sum_nonneg fun _ _ => le_max_right _ _
        have hp : 0 ≤ ∑ j, max (D (g j)) 0 :=
          Finset.sum_nonneg fun _ _ => le_max_right _ _
        have hden : 0 < A + (∑ j, max (-(D (g j))) 0) + (B + 1) +
            ∑ j, max (D (g j)) 0 := by linarith
        rw [random_choice_bias_ratio, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg (by linarith) hden.le)]
        exact (div_le_one hden).2 (by linarith)
      have hright_int : Integrable
          (fun g : Fin n → X => random_choice_bias_ratio D g (A + omega) B)
          tailMeasure := by
        have hmeas : AEStronglyMeasurable
            (fun g : Fin n → X => random_choice_bias_ratio D g (A + omega) B)
            tailMeasure := by
          have : Measurable
              (fun g : Fin n → X => random_choice_bias_ratio D g (A + omega) B) := by
            dsimp [random_choice_bias_ratio]
            fun_prop
          exact this.aestronglyMeasurable
        refine Integrable.mono' (integrable_const 1) hmeas ?_
        filter_upwards with g
        have hn : 0 ≤ ∑ j, max (-(D (g j))) 0 :=
          Finset.sum_nonneg fun _ _ => le_max_right _ _
        have hp : 0 ≤ ∑ j, max (D (g j)) 0 :=
          Finset.sum_nonneg fun _ _ => le_max_right _ _
        have hden : 0 < A + omega + (∑ j, max (-(D (g j))) 0) + B +
            ∑ j, max (D (g j)) 0 := by linarith
        rw [random_choice_bias_ratio, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg (by linarith) hden.le)]
        exact (div_le_one hden).2 (by linarith)
      have houter_int : Integrable (fun g : Fin n → X => ∫ x, F (x, g) ∂mu)
          tailMeasure := hFint.integral_prod_right
      have hrhs_int : Integrable
          (fun g : Fin n → X =>
            P * random_choice_bias_ratio D g A (B + 1) +
              alpha * random_choice_bias_ratio D g (A + omega) B) tailMeasure :=
        (hleft_int.const_mul P).add (hright_int.const_mul alpha)
      calc
        (∫ g, ∫ x, F (x, g) ∂mu ∂tailMeasure) ≤
            ∫ g, (P * random_choice_bias_ratio D g A (B + 1) +
              alpha * random_choice_bias_ratio D g (A + omega) B) ∂tailMeasure :=
          integral_mono_ae houter_int hrhs_int hinner
        _ = P * (∫ g, random_choice_bias_ratio D g A (B + 1) ∂tailMeasure) +
            alpha * (∫ g, random_choice_bias_ratio D g (A + omega) B ∂tailMeasure) := by
          rw [integral_add (hleft_int.const_mul P) (hright_int.const_mul alpha),
            integral_const_mul, integral_const_mul]
        _ ≤ P * random_choice_replacement_value n A (B + 1) alpha omega +
            alpha * random_choice_replacement_value n (A + omega) B alpha omega := by
          have hP_nonneg : 0 ≤ P := by
            rw [hP]
            exact integral_nonneg fun _ => le_max_right _ _
          have halpha_nonneg : 0 ≤ alpha := halpha_pos.le
          have hih_left := ih A (B + 1) hA (by linarith) (by linarith)
          have hih_right := ih (A + omega) B (by linarith) hB (by linarith)
          have hih_left' :
              (∫ g, random_choice_bias_ratio D g A (B + 1) ∂tailMeasure) ≤
                random_choice_replacement_value n A (B + 1) alpha omega := by
            simpa [tailMeasure] using hih_left
          have hih_right' :
              (∫ g, random_choice_bias_ratio D g (A + omega) B ∂tailMeasure) ≤
                random_choice_replacement_value n (A + omega) B alpha omega := by
            simpa [tailMeasure] using hih_right
          exact add_le_add (mul_le_mul_of_nonneg_left hih_left' hP_nonneg)
            (mul_le_mul_of_nonneg_left hih_right' halpha_nonneg)
        _ = random_choice_replacement_value (n + 1) A B alpha omega := by
          rw [show P = 1 - alpha by linarith [halpha]]
          rfl

@[blueprint "lem:random-choice-replacement-value-binomial"
  (statement := /-- For every $n\in\mathbb N$ and $A,B,\alpha,\omega\in\mathbb R$, the recursive two-point replacement value is the binomial sum over the number $\ell$ of coordinates equal to $-\omega$. -/)
  (proof := /-- Induct on $n$. Split the successor sum into its endpoint terms and its interior terms. The two branches of \cref{def:random-choice-replacement-value} contribute, respectively, the cases in which the new coordinate equals $1$ and $-\omega$. Reindex the second branch by $\ell\mapsto\ell+1$ and combine the two coefficients by Pascal's identity for $\binom{n+1}{\ell}$. -/)
  (title := /-- Binomial expansion of the replacement recursion -/)
  (latexEnv := "lemma")]
lemma random_choice_replacement_value_binomial
    (n : ℕ) (A B alpha omega : ℝ) :
    random_choice_replacement_value n A B alpha omega =
      (Finset.range (n + 1)).sum (fun ell =>
        (Nat.choose n ell : ℝ) * alpha ^ ell * (1 - alpha) ^ (n - ell) *
          ((A + (ell : ℝ) * omega) /
            (A + (ell : ℝ) * omega + B + ((n - ell : ℕ) : ℝ)))) := by
  induction n generalizing A B with
  | zero =>
      simp [random_choice_replacement_value]
  | succ n ih =>
      rw [random_choice_replacement_value, ih, ih]
      let q : ℕ → ℕ → ℝ → ℝ → ℝ := fun m ell C D' =>
        (Nat.choose m ell : ℝ) * alpha ^ ell * (1 - alpha) ^ (m - ell) *
          ((C + (ell : ℝ) * omega) /
            (C + (ell : ℝ) * omega + D' + ((m - ell : ℕ) : ℝ)))
      change
        (1 - alpha) * (Finset.range (n + 1)).sum (fun ell => q n ell A (B + 1)) +
            alpha * (Finset.range (n + 1)).sum (fun ell => q n ell (A + omega) B) =
          (Finset.range (n + 2)).sum (fun ell => q (n + 1) ell A B)
      have hfirst :
          (Finset.range (n + 1)).sum (fun ell => q n ell A (B + 1)) =
            (Finset.range n).sum (fun ell => q n (ell + 1) A (B + 1)) +
              q n 0 A (B + 1) := Finset.sum_range_succ' _ n
      have hsecond :
          (Finset.range (n + 1)).sum (fun ell => q n ell (A + omega) B) =
            (Finset.range n).sum (fun ell => q n ell (A + omega) B) +
              q n n (A + omega) B := Finset.sum_range_succ _ n
      have htarget :
          (Finset.range (n + 2)).sum (fun ell => q (n + 1) ell A B) =
            ((Finset.range n).sum (fun ell => q (n + 1) (ell + 1) A B) +
              q (n + 1) 0 A B) + q (n + 1) (n + 1) A B := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ']
      have hzero :
          (1 - alpha) * q n 0 A (B + 1) = q (n + 1) 0 A B := by
        dsimp [q]
        simp
        rw [pow_succ]
        ring
      have hlast :
          alpha * q n n (A + omega) B = q (n + 1) (n + 1) A B := by
        dsimp [q]
        simp [pow_succ]
        ring
      have hinter :
          (1 - alpha) *
              (Finset.range n).sum (fun ell => q n (ell + 1) A (B + 1)) +
            alpha * (Finset.range n).sum (fun ell => q n ell (A + omega) B) =
          (Finset.range n).sum (fun ell => q (n + 1) (ell + 1) A B) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ell hell
        have hell' : ell < n := Finset.mem_range.mp hell
        have hsub : n - (ell + 1) + 1 = n - ell := by omega
        have hsub' : n + 1 - (ell + 1) = n - ell := by omega
        have hcast : (((n - (ell + 1) : ℕ) : ℝ) + 1) = ((n - ell : ℕ) : ℝ) := by
          exact_mod_cast hsub
        have hdeneq :
            A + (((ell : ℝ) + (1 : ℝ)) * omega) + (B + 1) +
                ((n - (ell + 1) : ℕ) : ℝ) =
              A + (((ell : ℝ) + (1 : ℝ)) * omega) + B + ((n - ell : ℕ) : ℝ) := by
          rw [← hcast]
          ring
        have hpow :
            (1 - alpha) * (1 - alpha) ^ (n - (ell + 1)) =
              (1 - alpha) ^ (n - ell) := by
          rw [← hsub, pow_succ]
          ring
        dsimp [q]
        rw [Nat.choose_succ_succ, Nat.cast_add, hsub', pow_succ alpha ell]
        push_cast
        norm_num at hdeneq ⊢
        rw [hdeneq]
        ring_nf at hpow ⊢
        linear_combination
          (alpha * alpha ^ ell * (Nat.choose n (1 + ell) : ℝ) *
            ((A + (ell : ℝ) * omega + omega) /
              (A + (ell : ℝ) * omega + omega + B + ((n - ell : ℕ) : ℝ)))) * hpow
      rw [hfirst, hsecond, htarget, mul_add, mul_add]
      linear_combination hinter + hzero + hlast

@[blueprint "lem:random-choice-zero-offset-product-bound"
  (statement := /-- Under the hypotheses of \cref{lem:random-choice-product-replacement-bound}, assume additionally that $D\ne0$ almost everywhere, $\omega>0$, and $k\geq2$. Then the zero-offset product integral of the Random Choice ratio is at most the $k$-coordinate recursive two-point replacement value. -/)
  (proof := /-- Write $k=n+1$, where $n\geq1$, and decompose the product in \cref{def:random-choice-bias-ratio} into a head coordinate and an $n$-coordinate tail. A fixed tail has positive total bias mass almost everywhere because its zeroth coordinate is nonzero almost everywhere. Apply \cref{lem:random-choice-one-coordinate-integral-bound} to the head coordinate. The two resulting tail integrals have offsets $(0,1)$ and $(\omega,0)$, so \cref{lem:random-choice-product-replacement-bound} applies to both. Their weighted sum is the defining recursion in \cref{def:random-choice-replacement-value}. -/)
  (title := /-- Zero-offset product replacement bound -/)
  (latexEnv := "lemma")]
lemma random_choice_zero_offset_product_bound
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsProbabilityMeasure mu]
    (D : X → ℝ) (hDmeas : Measurable D) (hD : Integrable D mu)
    (hDbounds : ∀ᵐ x ∂mu, -1 ≤ D x ∧ D x ≤ 1)
    (hDne : ∀ᵐ x ∂mu, D x ≠ 0)
    (P N alpha omega : ℝ)
    (hP : P = ∫ x, max (D x) 0 ∂mu)
    (hN : N = ∫ x, max (-(D x)) 0 ∂mu)
    (halpha : alpha = 1 - P) (halpha_pos : 0 < alpha)
    (homega : omega = N / alpha)
    (homega_pos : 0 < omega) (homega_le : omega ≤ 1)
    (k : ℕ) (hk : 2 ≤ k) :
    (∫ g, random_choice_bias_ratio D g 0 0 ∂
      (Measure.pi (fun _ : Fin k => mu))) ≤
      random_choice_replacement_value k 0 0 alpha omega := by
  cases k with
  | zero => omega
  | succ n =>
      have hn : 1 ≤ n := by omega
      let tailMeasure : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => mu)
      let F : X × (Fin n → X) → ℝ := fun z =>
        random_choice_bias_ratio D (Fin.cons z.1 z.2) 0 0
      have hFmeas : AEStronglyMeasurable F (mu.prod tailMeasure) := by
        have hcoord : ∀ j : Fin (n + 1),
            Measurable (fun z : X × (Fin n → X) =>
              D ((@Fin.cons n (fun _ : Fin (n + 1) => X) z.1 z.2) j)) := by
          intro j
          refine Fin.cases ?_ (fun i => ?_) j
          · simpa [Function.comp_def] using hDmeas.comp measurable_fst
          · simpa [Function.comp_def] using
              hDmeas.comp ((measurable_pi_apply i).comp measurable_snd)
        have hnmeas : Measurable (fun z : X × (Fin n → X) =>
            ∑ j : Fin (n + 1),
              max (-(D ((@Fin.cons n (fun _ : Fin (n + 1) => X) z.1 z.2) j))) 0) :=
          Finset.measurable_sum _ fun j _ => (hcoord j).neg.max measurable_const
        have hpmeas : Measurable (fun z : X × (Fin n → X) =>
            ∑ j : Fin (n + 1),
              max (D ((@Fin.cons n (fun _ : Fin (n + 1) => X) z.1 z.2) j)) 0) :=
          Finset.measurable_sum _ fun j _ => (hcoord j).max measurable_const
        dsimp [F, random_choice_bias_ratio]
        exact (measurable_const.add hnmeas).div
          (((measurable_const.add hnmeas).add measurable_const).add hpmeas) |>.aestronglyMeasurable
      have hFint : Integrable F (mu.prod tailMeasure) := by
        refine Integrable.mono' (integrable_const 1) hFmeas ?_
        filter_upwards with z
        have hneg : 0 ≤ ∑ j : Fin (n + 1),
            max (-(D ((@Fin.cons n (fun _ : Fin (n + 1) => X) z.1 z.2) j))) 0 :=
          Finset.sum_nonneg fun _ _ => le_max_right _ _
        have hpos : 0 ≤ ∑ j : Fin (n + 1),
            max (D ((@Fin.cons n (fun _ : Fin (n + 1) => X) z.1 z.2) j)) 0 :=
          Finset.sum_nonneg fun _ _ => le_max_right _ _
        dsimp [F, random_choice_bias_ratio]
        simp only [zero_add, add_zero]
        rw [abs_of_nonneg (div_nonneg hneg (add_nonneg hneg hpos))]
        by_cases hzero :
            (∑ j : Fin (n + 1),
              max (-(D ((@Fin.cons n (fun _ : Fin (n + 1) => X) z.1 z.2) j))) 0) +
              ∑ j : Fin (n + 1),
                max (D ((@Fin.cons n (fun _ : Fin (n + 1) => X) z.1 z.2) j)) 0 = 0
        · simp [hzero]
        · exact (div_le_one (lt_of_le_of_ne (add_nonneg hneg hpos) (Ne.symm hzero))).2
            (by linarith)
      have hchange :
          (∫ g, random_choice_bias_ratio D g 0 0 ∂
              (Measure.pi (fun _ : Fin (n + 1) => mu))) =
            ∫ z, F z ∂mu.prod tailMeasure := by
        have hmp := measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => mu) (0 : Fin (n + 1))
        have h := hmp.integral_comp' F
        simpa [F, tailMeasure] using h
      rw [hchange, integral_prod_symm F hFint]
      let j0 : Fin n := ⟨0, hn⟩
      have htailne : ∀ᵐ g ∂tailMeasure, D (g j0) ≠ 0 := by
        dsimp [tailMeasure]
        exact (Measure.quasiMeasurePreserving_eval (μ := fun _ : Fin n => mu) j0).ae hDne
      have hinner : ∀ᵐ g ∂tailMeasure,
          (∫ x, F (x, g) ∂mu) ≤
            P * random_choice_bias_ratio D g 0 1 +
              alpha * random_choice_bias_ratio D g omega 0 := by
        filter_upwards [htailne] with g hg
        let A' : ℝ := ∑ j, max (-(D (g j))) 0
        let B' : ℝ := ∑ j, max (D (g j)) 0
        have hA' : 0 ≤ A' := Finset.sum_nonneg fun _ _ => le_max_right _ _
        have hB' : 0 ≤ B' := Finset.sum_nonneg fun _ _ => le_max_right _ _
        have hmass : 0 < max (-(D (g j0))) 0 + max (D (g j0)) 0 := by
          rcases lt_or_gt_of_ne hg with hneg | hpos
          · rw [max_eq_left (neg_nonneg.mpr hneg.le), max_eq_right hneg.le]
            linarith
          · rw [max_eq_right (neg_nonpos.mpr hpos.le), max_eq_left hpos.le]
            linarith
        have hAterm : max (-(D (g j0))) 0 ≤ A' := by
          dsimp [A']
          exact Finset.single_le_sum
            (fun i _ => le_max_right (-(D (g i))) 0) (Finset.mem_univ j0)
        have hBterm : max (D (g j0)) 0 ≤ B' := by
          dsimp [B']
          exact Finset.single_le_sum
            (fun i _ => le_max_right (D (g i)) 0) (Finset.mem_univ j0)
        have hAB' : 0 < A' + B' := by linarith
        have hone := random_choice_one_coordinate_integral_bound mu D hD hDbounds
          P N alpha omega A' B' hP hN halpha halpha_pos homega
          homega_pos.le homega_le hA' hB' hAB'
        dsimp [F, A', B'] at hone ⊢
        simpa [random_choice_bias_ratio, Fin.sum_univ_succ, add_assoc, add_left_comm,
          add_comm] using hone
      have hleft_int : Integrable
          (fun g : Fin n → X => random_choice_bias_ratio D g 0 1) tailMeasure := by
        have hmeas : AEStronglyMeasurable
            (fun g : Fin n → X => random_choice_bias_ratio D g 0 1) tailMeasure := by
          have : Measurable
              (fun g : Fin n → X => random_choice_bias_ratio D g 0 1) := by
            dsimp [random_choice_bias_ratio]
            fun_prop
          exact this.aestronglyMeasurable
        refine Integrable.mono' (integrable_const 1) hmeas ?_
        filter_upwards with g
        have hneg : 0 ≤ ∑ j, max (-(D (g j))) 0 :=
          Finset.sum_nonneg fun _ _ => le_max_right _ _
        have hpos : 0 ≤ ∑ j, max (D (g j)) 0 :=
          Finset.sum_nonneg fun _ _ => le_max_right _ _
        have hden : 0 < (∑ j, max (-(D (g j))) 0) + 1 +
            ∑ j, max (D (g j)) 0 := by linarith
        simp only [random_choice_bias_ratio, zero_add]
        rw [Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hneg hden.le)]
        exact (div_le_one hden).2 (by linarith)
      have hright_int : Integrable
          (fun g : Fin n → X => random_choice_bias_ratio D g omega 0) tailMeasure := by
        have hmeas : AEStronglyMeasurable
            (fun g : Fin n → X => random_choice_bias_ratio D g omega 0) tailMeasure := by
          have : Measurable
              (fun g : Fin n → X => random_choice_bias_ratio D g omega 0) := by
            dsimp [random_choice_bias_ratio]
            fun_prop
          exact this.aestronglyMeasurable
        refine Integrable.mono' (integrable_const 1) hmeas ?_
        filter_upwards with g
        have hneg : 0 ≤ ∑ j, max (-(D (g j))) 0 :=
          Finset.sum_nonneg fun _ _ => le_max_right _ _
        have hpos : 0 ≤ ∑ j, max (D (g j)) 0 :=
          Finset.sum_nonneg fun _ _ => le_max_right _ _
        have hden : 0 < omega + (∑ j, max (-(D (g j))) 0) +
            ∑ j, max (D (g j)) 0 := by linarith
        simp only [random_choice_bias_ratio, add_zero]
        rw [Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg (by linarith) hden.le)]
        exact (div_le_one hden).2 (by linarith)
      have houter_int : Integrable (fun g : Fin n → X => ∫ x, F (x, g) ∂mu)
          tailMeasure := hFint.integral_prod_right
      have hrhs_int : Integrable
          (fun g : Fin n → X => P * random_choice_bias_ratio D g 0 1 +
            alpha * random_choice_bias_ratio D g omega 0) tailMeasure :=
        (hleft_int.const_mul P).add (hright_int.const_mul alpha)
      have hprod := random_choice_product_replacement_bound mu D hDmeas hD hDbounds
        P N alpha omega hP hN halpha halpha_pos homega homega_pos.le homega_le
      calc
        (∫ g, ∫ x, F (x, g) ∂mu ∂tailMeasure) ≤
            ∫ g, (P * random_choice_bias_ratio D g 0 1 +
              alpha * random_choice_bias_ratio D g omega 0) ∂tailMeasure :=
          integral_mono_ae houter_int hrhs_int hinner
        _ = P * (∫ g, random_choice_bias_ratio D g 0 1 ∂tailMeasure) +
            alpha * (∫ g, random_choice_bias_ratio D g omega 0 ∂tailMeasure) := by
          rw [integral_add (hleft_int.const_mul P) (hright_int.const_mul alpha),
            integral_const_mul, integral_const_mul]
        _ ≤ P * random_choice_replacement_value n 0 1 alpha omega +
            alpha * random_choice_replacement_value n omega 0 alpha omega := by
          have hP_nonneg : 0 ≤ P := by
            rw [hP]
            exact integral_nonneg fun _ => le_max_right _ _
          have hl := hprod n 0 1 (by norm_num) (by norm_num) (by norm_num)
          have hr := hprod n omega 0 homega_pos.le (by norm_num) (by simpa using homega_pos)
          have hl' : (∫ g, random_choice_bias_ratio D g 0 1 ∂tailMeasure) ≤
              random_choice_replacement_value n 0 1 alpha omega := by
            simpa [tailMeasure] using hl
          have hr' : (∫ g, random_choice_bias_ratio D g omega 0 ∂tailMeasure) ≤
              random_choice_replacement_value n omega 0 alpha omega := by
            simpa [tailMeasure] using hr
          exact add_le_add (mul_le_mul_of_nonneg_left hl' hP_nonneg)
            (mul_le_mul_of_nonneg_left hr' halpha_pos.le)
        _ = random_choice_replacement_value (n + 1) 0 0 alpha omega := by
          rw [show P = 1 - alpha by linarith [halpha]]
          simp [random_choice_replacement_value]

@[blueprint "lem:random-choice-win-probability-complement"
  (statement := /-- Let $E$ be a continuum metric election, let $k>0$, and let $a\ne b$. Then the size-$k$ Random Choice win probabilities in the two orientations are complementary:
  \[
    p_k(a,b)+p_k(b,a)=1.
  \] -/)
  (proof := /-- Set $D(i)=B_i(a,b)$ as in \cref{def:normalized-bias}. Reversing the candidates negates $D$, and therefore interchanges the first and second bias masses in \cref{def:first-bias-mass,def:second-bias-mass}. Since $k>0$, choose one group coordinate. The strict-ranking hypothesis in \cref{def:metric-election} implies that its bias is nonzero almost everywhere, so the sum of the two group bias masses is positive almost everywhere. Consequently, the two ratios in \cref{def:random-choice-group-probability} add to one almost everywhere. Both ratios are measurable and bounded by one in absolute value, hence integrable. Integrating the almost-everywhere identity in the product probability space and applying \cref{def:random-choice-win-probability} proves the assertion. -/)
  (title := /-- Complementarity of Random Choice win probabilities -/)
  (latexEnv := "lemma")]
lemma random_choice_win_probability_complement
    {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (k : ℕ) (hk : 0 < k)
    (a b : Candidate) (hab : a ≠ b) :
    random_choice_win_probability E k a b +
      random_choice_win_probability E k b a = 1 := by
  have hcp : E.candidatePoint a ≠ E.candidatePoint b := by
    intro heq
    obtain ⟨i, hi⟩ := E.strict_rankings.exists
    exact (hi a b hab) (by rw [heq])
  have hd : 0 < dist (E.candidatePoint a) (E.candidatePoint b) :=
    dist_pos.mpr hcp
  let D : Voter → ℝ := fun i => normalized_bias E i a b
  let A : (Fin k → Voter) → ℝ :=
    fun g => ∑ j, max (-(D (g j))) 0
  let B : (Fin k → Voter) → ℝ :=
    fun g => ∑ j, max (D (g j)) 0
  let groupMeasure : Measure (Fin k → Voter) :=
    Measure.pi (fun _ : Fin k => (E.voterMeasure : Measure Voter))
  have hDmeas : Measurable D := by
    dsimp [D, normalized_bias]
    exact
      ((((continuous_id.dist continuous_const).measurable).comp
          E.voterPoint_measurable).sub
        (((continuous_id.dist continuous_const).measurable).comp
          E.voterPoint_measurable)).div measurable_const
  have hcoord : ∀ j : Fin k, Measurable (fun g : Fin k → Voter => D (g j)) := by
    intro j
    exact hDmeas.comp (measurable_pi_apply j)
  have hAmeas : Measurable A := by
    dsimp [A]
    exact Finset.measurable_sum _ fun j _ =>
      (hcoord j).neg.max measurable_const
  have hBmeas : Measurable B := by
    dsimp [B]
    exact Finset.measurable_sum _ fun j _ =>
      (hcoord j).max measurable_const
  have hreverse : ∀ i, normalized_bias E i b a = -D i := by
    intro i
    dsimp [D, normalized_bias]
    rw [dist_comm (E.candidatePoint b) (E.candidatePoint a)]
    ring
  have habprob : ∀ g,
      random_choice_group_probability E g a b = A g / (A g + B g) := by
    intro g
    simp [random_choice_group_probability, first_bias_mass, second_bias_mass,
      A, B, D]
  have hbaprob : ∀ g,
      random_choice_group_probability E g b a = B g / (B g + A g) := by
    intro g
    simp [random_choice_group_probability, first_bias_mass, second_bias_mass,
      A, B, hreverse]
  let j0 : Fin k := ⟨0, hk⟩
  have hDne : ∀ᵐ i ∂(E.voterMeasure : Measure Voter), D i ≠ 0 := by
    filter_upwards [E.strict_rankings] with i hi
    dsimp [D, normalized_bias]
    exact div_ne_zero (sub_ne_zero.mpr (hi a b hab)) (ne_of_gt hd)
  have hcoordne : ∀ᵐ g ∂groupMeasure, D (g j0) ≠ 0 := by
    dsimp [groupMeasure]
    exact (Measure.quasiMeasurePreserving_eval
      (μ := fun _ : Fin k => (E.voterMeasure : Measure Voter)) j0).ae hDne
  have hdenpos : ∀ᵐ g ∂groupMeasure, 0 < A g + B g := by
    filter_upwards [hcoordne] with g hg
    have hterm :
        0 < max (-(D (g j0))) 0 + max (D (g j0)) 0 := by
      rcases lt_or_gt_of_ne hg with hneg | hpos
      · rw [max_eq_left (neg_pos.mpr hneg).le, max_eq_right hneg.le]
        linarith
      · rw [max_eq_right (neg_nonpos.mpr hpos.le), max_eq_left hpos.le]
        linarith
    have hAle : max (-(D (g j0))) 0 ≤ A g := by
      dsimp [A]
      exact Finset.single_le_sum
        (fun j (_ : j ∈ Finset.univ) => le_max_right (-(D (g j))) 0)
        (Finset.mem_univ j0)
    have hBle : max (D (g j0)) 0 ≤ B g := by
      dsimp [B]
      exact Finset.single_le_sum
        (fun j (_ : j ∈ Finset.univ) => le_max_right (D (g j)) 0)
        (Finset.mem_univ j0)
    linarith
  have hpoint : ∀ᵐ g ∂groupMeasure,
      random_choice_group_probability E g a b +
        random_choice_group_probability E g b a = 1 := by
    filter_upwards [hdenpos] with g hden
    rw [habprob, hbaprob]
    have hden' : B g + A g ≠ 0 := by linarith
    field_simp [ne_of_gt hden, hden']
    ring
  have hABint : Integrable (fun g => A g / (A g + B g)) groupMeasure := by
    have hmeas : AEStronglyMeasurable (fun g => A g / (A g + B g))
        groupMeasure :=
      (hAmeas.div (hAmeas.add hBmeas)).aestronglyMeasurable
    refine Integrable.mono' (integrable_const 1) hmeas ?_
    filter_upwards with g
    have hA : 0 ≤ A g := by
      dsimp [A]
      exact Finset.sum_nonneg fun _ _ => le_max_right _ _
    have hB : 0 ≤ B g := by
      dsimp [B]
      exact Finset.sum_nonneg fun _ _ => le_max_right _ _
    by_cases hzero : A g + B g = 0
    · have hAzero : A g = 0 := by linarith
      simp [hAzero]
    · have hden : 0 < A g + B g := lt_of_le_of_ne (by positivity) (Ne.symm hzero)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hA hden.le)]
      exact (div_le_one hden).2 (by linarith)
  have hBAint : Integrable (fun g => B g / (B g + A g)) groupMeasure := by
    have hmeas : AEStronglyMeasurable (fun g => B g / (B g + A g))
        groupMeasure :=
      (hBmeas.div (hBmeas.add hAmeas)).aestronglyMeasurable
    refine Integrable.mono' (integrable_const 1) hmeas ?_
    filter_upwards with g
    have hA : 0 ≤ A g := by
      dsimp [A]
      exact Finset.sum_nonneg fun _ _ => le_max_right _ _
    have hB : 0 ≤ B g := by
      dsimp [B]
      exact Finset.sum_nonneg fun _ _ => le_max_right _ _
    by_cases hzero : B g + A g = 0
    · have hBzero : B g = 0 := by linarith
      simp [hBzero]
    · have hden : 0 < B g + A g := lt_of_le_of_ne (by positivity) (Ne.symm hzero)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hB hden.le)]
      exact (div_le_one hden).2 (by linarith)
  have habint : Integrable
      (fun g => random_choice_group_probability E g a b) groupMeasure := by
    simpa only [habprob] using hABint
  have hbaint : Integrable
      (fun g => random_choice_group_probability E g b a) groupMeasure := by
    simpa only [hbaprob] using hBAint
  rw [random_choice_win_probability, random_choice_win_probability,
    ProbabilityMeasure.toMeasure_pi]
  change (∫ g, random_choice_group_probability E g a b ∂groupMeasure) +
      (∫ g, random_choice_group_probability E g b a ∂groupMeasure) = 1
  rw [← integral_add habint hbaint, integral_congr_ae hpoint]
  simp [groupMeasure, measureReal_univ_eq_one]

@[blueprint "lem:random-choice-program-controls-pairwise"
  (statement := /-- Let $E$ be a continuum metric election, let $k\geq2$, and let $\zeta$ be an admissible threshold. If $\zeta$ bounds the size-$k$ Random Choice program, then the size-$k$ deliberation tournament of $E$ satisfies pairwise distortion control at threshold $\zeta$. -/)
  (proof := /-- Fix distinct candidates $a,b$, write $\mu$ for the voter probability measure in \cref{def:metric-election}, and set $D(i)=B_i(a,b)$ as in \cref{def:normalized-bias}. The strict-ranking hypothesis implies that the candidate points of $a$ and $b$ are distinct, so their distance $d(a,b)$ is positive. The triangle inequality gives $|D|\leq1$ almost everywhere, and integrability together with \cref{def:social-cost} gives
  \[
    \operatorname{SC}_E(a)-\operatorname{SC}_E(b)
      =d(a,b)\int D\,d\mu.
  \]

  Denote the positive and negative parts of $D$ by $D_+=\max(D,0)$ and $D_-=\max(-D,0)$, and put
  \[
    P=\int D_+\,d\mu,\qquad N=\int D_-\,d\mu,\qquad
    \alpha=1-P,\qquad \omega=\frac{N}{\alpha}.
  \]
  Since $D_++D_-=|D|\leq1$, one has $0\leq P,N$ and $P+N\leq1$. If $\alpha=0$, then $D=1$ almost everywhere; if $N=0$, then $D\geq0$ almost everywhere and the strict-ranking hypothesis makes this inequality strict almost everywhere. In either case every group chooses $b$ over $a$ with probability one, contrary to $a$ dominating $b$. Hence $0<\alpha\leq1$ and $0<\omega\leq1$.

  We next compare the product integral in \cref{def:random-choice-win-probability} with a two-point distribution. Hold all but one of the $k$ bias coordinates fixed, and let $A$ and $B$ be, respectively, the total negative and positive bias masses in the fixed coordinates. Because $k\geq2$ and rankings are strict almost everywhere, $A+B>0$ for almost every choice of those coordinates. The conditional group-choice function from \cref{def:random-choice-group-probability,def:random-choice-bias-ratio} is
  \[
    \Phi(x)=\frac{A+x_-}{A+x_-+B+x_+}.
  \]
  On $0\leq x\leq1$, the function $\Phi(x)=A/(A+B+x)$ is convex, so the chord inequality gives
  \[
    \Phi(x)\leq(1-x)\Phi(0)+x\Phi(1).
  \]
  On $-1\leq x\leq0$, the function $t\mapsto\Phi(-t)=(A+t)/(A+B+t)$ is concave for $0\leq t\leq1$. After integrating the chord inequality over the positive part of $D$, combine its coefficient $(1-D_+)$ at $0$ with the negative part of the voter measure. This residual positive measure has total mass $1-P=\alpha$ and first negative moment $N$. Jensen's inequality for the concave function $t\mapsto\Phi(-t)$ therefore yields
  \[
    \int\Phi(D(i))\,d\mu(i)
      \leq P\Phi(1)+\alpha\Phi(-N/\alpha)
      =(1-\alpha)\Phi(1)+\alpha\Phi(-\omega).
  \]
  Thus replacing this coordinate by a variable equal to $1$ with probability $1-\alpha$ and to $-\omega$ with probability $\alpha$ can only increase the probability of choosing $a$.

  The successive replacement and its Fubini justification are precisely \cref{lem:random-choice-zero-offset-product-bound}: the product integral is bounded by the recursive value in \cref{def:random-choice-replacement-value}. By \cref{lem:random-choice-replacement-value-binomial}, this value is the expectation for $k$ independent copies of the two-point variable. If exactly $\ell$ copies equal $-\omega$, the negative and positive bias masses are $\ell\omega$ and $k-\ell$, respectively. The $\ell=0$ term vanishes, and hence
  \[
    p_k(a,b)\leq
    \sum_{\ell=1}^k {k\choose\ell}\alpha^\ell(1-\alpha)^{k-\ell}
      \frac{\ell\omega}{\ell\omega+k-\ell}.
  \]
  Since domination means $p_k(a,b)\geq1/2$, the preceding bounds show that $(\omega,\alpha)$ is feasible in \cref{def:random-choice-program-feasible}. Moreover, by \cref{def:random-choice-program-objective},
  \[
    \int D\,d\mu=P-N=(1-\alpha)-\alpha\omega,
  \]
  and the assumed bound \cref{def:random-choice-program-bound} gives $\int D\,d\mu\leq\zeta$. The triangle inequality also yields
  $d(a,b)\leq\operatorname{SC}_E(a)+\operatorname{SC}_E(b)$. Since admissibility in \cref{def:admissible-threshold} gives $\zeta\geq0$, the preceding identities imply
  \[
    (1-\zeta)\operatorname{SC}_E(a)
      \leq(1+\zeta)\operatorname{SC}_E(b).
  \]
  Finally, \cref{lem:random-choice-win-probability-complement} shows that the two win probabilities of every distinct pair sum to one; hence at least one orientation has probability at least $1/2$. Together with the assumed admissibility, these assertions are exactly \cref{def:pairwise-distortion-control}. -/)
  (title := /-- Program control implies pairwise distortion control -/)
  (latexEnv := "lemma")]
lemma random_choice_program_controls_pairwise
    {Candidate Voter Point : Type*}
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (k : ℕ) (zeta : ℝ)
    (hk : 2 ≤ k) (hzeta : admissible_threshold zeta)
    (hbound : random_choice_program_bound k zeta) :
    pairwise_distortion_control E k zeta := by
  have hedge : ∀ a b, a ≠ b → deliberation_dominates E k a b →
      (1 - zeta) * social_cost E a ≤ (1 + zeta) * social_cost E b := by
    intro a b hab hdom
    have hcp : E.candidatePoint a ≠ E.candidatePoint b := by
      intro heq
      obtain ⟨i, hi⟩ := E.strict_rankings.exists
      exact (hi a b hab) (by rw [heq])
    have hd : 0 < dist (E.candidatePoint a) (E.candidatePoint b) :=
      dist_pos.mpr hcp
    let D : Voter → ℝ := fun i => normalized_bias E i a b
    have hgroup_eq :
        (fun g : Fin k → Voter => random_choice_group_probability E g a b) =
          fun g => random_choice_bias_ratio D g 0 0 := by
      funext g
      simp [random_choice_group_probability, first_bias_mass, second_bias_mass,
        random_choice_bias_ratio, D]
    have hDmeas : Measurable D := by
      dsimp [D, normalized_bias]
      exact
        ((((continuous_id.dist continuous_const).measurable).comp
            E.voterPoint_measurable).sub
          (((continuous_id.dist continuous_const).measurable).comp
            E.voterPoint_measurable)).div measurable_const
    have hD : Integrable D E.voterMeasure := by
      dsimp [D, normalized_bias]
      exact ((E.voter_distance_integrable a).sub
        (E.voter_distance_integrable b)).div_const _
    have hDbounds : ∀ᵐ i ∂(E.voterMeasure : Measure Voter),
        -1 ≤ D i ∧ D i ≤ 1 := by
      filter_upwards with i
      have habs :
          |dist (E.voterPoint i) (E.candidatePoint a) -
            dist (E.voterPoint i) (E.candidatePoint b)| ≤
            dist (E.candidatePoint a) (E.candidatePoint b) := by
        simpa [dist_comm] using
          abs_dist_sub_le (E.candidatePoint a) (E.candidatePoint b) (E.voterPoint i)
      have hquot : |D i| ≤ 1 := by
        dsimp [D, normalized_bias]
        rw [abs_div, abs_of_nonneg dist_nonneg]
        exact (div_le_one hd).2 habs
      exact abs_le.mp hquot
    have hDne : ∀ᵐ i ∂(E.voterMeasure : Measure Voter), D i ≠ 0 := by
      filter_upwards [E.strict_rankings] with i hi
      dsimp [D, normalized_bias]
      exact div_ne_zero (sub_ne_zero.mpr (hi a b hab)) (ne_of_gt hd)
    let P : ℝ := ∫ i, max (D i) 0 ∂E.voterMeasure
    let N : ℝ := ∫ i, max (-(D i)) 0 ∂E.voterMeasure
    let alpha : ℝ := 1 - P
    let omega : ℝ := N / alpha
    have hp_int : Integrable (fun i => max (D i) 0) E.voterMeasure :=
      hD.sup (integrable_const 0)
    have hn_int : Integrable (fun i => max (-(D i)) 0) E.voterMeasure :=
      hD.neg.sup (integrable_const 0)
    have hP_nonneg : 0 ≤ P := by
      dsimp [P]
      exact integral_nonneg fun _ => le_max_right _ _
    have hN_nonneg : 0 ≤ N := by
      dsimp [N]
      exact integral_nonneg fun _ => le_max_right _ _
    have hPN : P + N ≤ 1 := by
      have hpoint : ∀ᵐ i ∂(E.voterMeasure : Measure Voter),
          max (D i) 0 + max (-(D i)) 0 ≤ 1 := by
        filter_upwards [hDbounds] with i hi
        rcases le_total 0 (D i) with hpos | hneg
        · rw [max_eq_left hpos, max_eq_right (neg_nonpos.mpr hpos)]
          simpa using hi.2
        · rw [max_eq_right hneg, max_eq_left (neg_nonneg.mpr hneg)]
          linarith [hi.1]
      have hint := integral_mono_ae (hp_int.add hn_int) (integrable_const 1) hpoint
      have hint' :
          (∫ i, max (D i) 0 ∂E.voterMeasure) +
              (∫ i, max (-(D i)) 0 ∂E.voterMeasure) ≤
            ∫ _ : Voter, (1 : ℝ) ∂E.voterMeasure := by
        rw [← integral_add hp_int hn_int]
        simpa only [Pi.add_apply] using hint
      simpa only [P, N, integral_const, measureReal_univ_eq_one, one_smul] using hint'
    have hN_pos : 0 < N := by
      apply lt_of_le_of_ne hN_nonneg
      intro hNzero
      have hnegzero : (fun i => max (-(D i)) 0) =ᵐ[
          (E.voterMeasure : Measure Voter)] 0 :=
        (integral_eq_zero_iff_of_nonneg_ae
          (Filter.Eventually.of_forall fun _ => le_max_right _ _) hn_int).mp (by
            simpa [N] using hNzero.symm)
      have hgroupzero : ∀ᵐ g ∂(Measure.pi (fun _ : Fin k =>
          (E.voterMeasure : Measure Voter))),
          ∀ j, max (-(D (g j))) 0 = 0 := by
        rw [ae_all_iff]
        intro j
        exact (Measure.quasiMeasurePreserving_eval
          (μ := fun _ : Fin k => (E.voterMeasure : Measure Voter)) j).ae hnegzero
      have hratiozero : ∀ᵐ g ∂(Measure.pi (fun _ : Fin k =>
          (E.voterMeasure : Measure Voter))),
          random_choice_bias_ratio D g 0 0 = 0 := by
        filter_upwards [hgroupzero] with g hg
        simp [random_choice_bias_ratio, hg]
      have hwinzero : random_choice_win_probability E k a b = 0 := by
        rw [random_choice_win_probability, hgroup_eq,
          ProbabilityMeasure.toMeasure_pi]
        rw [integral_congr_ae hratiozero]
        simp
      unfold deliberation_dominates at hdom
      rw [hwinzero] at hdom
      norm_num at hdom
    have hN_le_alpha : N ≤ alpha := by
      dsimp [alpha]
      linarith [hPN]
    have halpha_pos : 0 < alpha := lt_of_lt_of_le hN_pos hN_le_alpha
    have halpha_le : alpha ≤ 1 := by
      dsimp [alpha]
      linarith
    have homega_pos : 0 < omega := by
      dsimp [omega]
      positivity
    have homega_le : omega ≤ 1 := by
      dsimp [omega]
      exact (div_le_one halpha_pos).2 hN_le_alpha
    have hproduct := random_choice_zero_offset_product_bound
      (E.voterMeasure : Measure Voter) D hDmeas hD hDbounds hDne
      P N alpha omega rfl rfl rfl halpha_pos rfl homega_pos homega_le k hk
    have hbinomial := random_choice_replacement_value_binomial k 0 0 alpha omega
    have hprogram :
        random_choice_win_probability E k a b ≤
          (Finset.range k).sum (fun j =>
            random_choice_program_term k (j + 1) omega alpha) := by
      rw [random_choice_win_probability, hgroup_eq,
        ProbabilityMeasure.toMeasure_pi]
      calc
        (∫ g, random_choice_bias_ratio D g 0 0 ∂
          (Measure.pi (fun _ : Fin k =>
            (E.voterMeasure : Measure Voter)))) ≤
            random_choice_replacement_value k 0 0 alpha omega := hproduct
        _ = (Finset.range (k + 1)).sum (fun ell =>
            (Nat.choose k ell : ℝ) * alpha ^ ell * (1 - alpha) ^ (k - ell) *
              (((ell : ℝ) * omega) /
                ((ell : ℝ) * omega + ((k - ell : ℕ) : ℝ)))) := by
          simpa using hbinomial
        _ = (Finset.range k).sum (fun j =>
            random_choice_program_term k (j + 1) omega alpha) := by
          rw [Finset.sum_range_succ']
          simp [random_choice_program_term, hk]
    have hfeasible : random_choice_program_feasible k omega alpha := by
      refine ⟨homega_pos.le, homega_le, halpha_pos.le, halpha_le, ?_⟩
      exact le_trans hdom hprogram
    have hobjective : random_choice_program_objective omega alpha ≤ zeta :=
      hbound omega alpha hfeasible
    have hDsplit : (∫ i, D i ∂E.voterMeasure) = P - N := by
      have heq : D = (fun i => max (D i) 0 - max (-(D i)) 0) := by
        funext i
        rcases le_total 0 (D i) with hpos | hneg
        · rw [max_eq_left hpos, max_eq_right (neg_nonpos.mpr hpos)]
          ring
        · rw [max_eq_right hneg, max_eq_left (neg_nonneg.mpr hneg)]
          ring
      rw [heq, integral_sub hp_int hn_int]
    have hmean : (∫ i, D i ∂E.voterMeasure) ≤ zeta := by
      rw [hDsplit]
      have hrel : N = alpha * omega := by
        dsimp [omega]
        field_simp [ne_of_gt halpha_pos]
      dsimp [random_choice_program_objective] at hobjective
      dsimp [alpha] at hrel ⊢
      linarith
    have hcostdiff :
        social_cost E a - social_cost E b =
          dist (E.candidatePoint a) (E.candidatePoint b) *
            (∫ i, D i ∂E.voterMeasure) := by
      dsimp [social_cost, D, normalized_bias]
      rw [integral_div, integral_sub (E.voter_distance_integrable a)
        (E.voter_distance_integrable b)]
      field_simp [ne_of_gt hd]
    have htriangle :
        dist (E.candidatePoint a) (E.candidatePoint b) ≤
          social_cost E a + social_cost E b := by
      have hpoint : ∀ᵐ i ∂(E.voterMeasure : Measure Voter),
          dist (E.candidatePoint a) (E.candidatePoint b) ≤
            dist (E.voterPoint i) (E.candidatePoint a) +
              dist (E.voterPoint i) (E.candidatePoint b) := by
        filter_upwards with i
        simpa [dist_comm] using
          dist_triangle (E.candidatePoint a) (E.voterPoint i) (E.candidatePoint b)
      have hint := integral_mono_ae (integrable_const _)
        ((E.voter_distance_integrable a).add (E.voter_distance_integrable b)) hpoint
      simpa [social_cost, integral_add (E.voter_distance_integrable a)
        (E.voter_distance_integrable b), measureReal_univ_eq_one] using hint
    have hsca : 0 ≤ social_cost E a := integral_nonneg fun _ => dist_nonneg
    have hscb : 0 ≤ social_cost E b := integral_nonneg fun _ => dist_nonneg
    have hzeta_nonneg : 0 ≤ zeta := hzeta.1
    have hscaled :
        dist (E.candidatePoint a) (E.candidatePoint b) *
            (∫ i, D i ∂E.voterMeasure) ≤
          zeta * (social_cost E a + social_cost E b) := by
      calc
        dist (E.candidatePoint a) (E.candidatePoint b) *
            (∫ i, D i ∂E.voterMeasure) ≤
            dist (E.candidatePoint a) (E.candidatePoint b) * zeta :=
          mul_le_mul_of_nonneg_left hmean hd.le
        _ ≤ zeta * (social_cost E a + social_cost E b) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left htriangle hzeta_nonneg
    nlinarith [hcostdiff]
  refine ⟨hzeta, ?_, hedge⟩
  intro a b hab
  have hcomp := random_choice_win_probability_complement E k
    (lt_of_lt_of_le (by norm_num) hk) a b hab
  unfold deliberation_dominates
  rcases le_total (1 / 2 : ℝ) (random_choice_win_probability E k a b) with
    hleft | hright
  · exact Or.inl hleft
  · exact Or.inr (by linarith)

@[blueprint "lem:copeland-distortion-of-pairwise-control"
  (statement := /-- Let $E$ be a continuum metric election on a finite candidate set, and suppose that its size-$k$ deliberation tournament has pairwise distortion control at $\zeta$. If $D\geq\Delta(\zeta)$, then every permitted output of the uncovered-set Copeland rule has social cost at most $D$ times the optimal social cost. -/)
  (proof := /-- Let $w$ be a Copeland output and let $o$ be a social optimum. By \cref{def:copeland-winner,def:uncovered-candidate}, $w$ is uncovered. Put $r=(1+\zeta)/(1-\zeta)$. Admissibility in \cref{def:pairwise-distortion-control} gives $1-\zeta>0$ and $r\geq1$. Dividing the edge inequality in that definition by $1-\zeta$ shows that $a\succ b$ implies $\operatorname{SC}_E(a)\leq r\operatorname{SC}_E(b)$. Social costs are nonnegative by their integral representation in \cref{def:social-cost}. Hence, if $w=o$, then $\operatorname{SC}_E(w)\leq r^2\operatorname{SC}_E(o)$. Suppose that $w\ne o$. If $w\succ o$, the edge estimate and $r\leq r^2$ give the same bound. Otherwise, completeness gives $o\succ w$. Since $w$ is uncovered, \cref{def:tournament-covers} implies that there is a candidate $y$ such that $w\succ y$ but not $o\succ y$. The relations $o\succ w$ and not $o\succ y$ imply $y\ne w$, while $w\succ y$ and not $w\succ o$ imply $y\ne o$. Completeness therefore gives $y\succ o$. Applying the edge estimate along $w\succ y\succ o$ yields $\operatorname{SC}_E(w)\leq r^2\operatorname{SC}_E(o)=\Delta(\zeta)\operatorname{SC}_E(o)$ by \cref{def:distortion-factor}. Finally, $\Delta(\zeta)\leq D$ and nonnegativity of $\operatorname{SC}_E(o)$ give the bound in \cref{def:copeland-distortion-at-most}. -/)
  (title := /-- Pairwise control yields the squared Copeland bound -/)
  (latexEnv := "lemma")]
lemma copeland_distortion_of_pairwise_control
    {Candidate Voter Point : Type*}
    [Fintype Candidate] [DecidableEq Candidate]
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) (k : ℕ)
    (zeta D : ℝ)
    (hcontrol : pairwise_distortion_control E k zeta)
    (hfactor : distortion_factor zeta ≤ D) :
    copeland_distortion_at_most E k D := by
  classical
  rintro winner optimal hwinner hoptimal
  rcases hcontrol with
    ⟨⟨hzeta_nonneg, hzeta_lt_one⟩, hcomplete, hedge⟩
  let r : ℝ := (1 + zeta) / (1 - zeta)
  have hdenom_pos : 0 < 1 - zeta := sub_pos.mpr hzeta_lt_one
  have hr_one : 1 ≤ r := by
    dsimp [r]
    apply (le_div_iff₀ hdenom_pos).2
    linarith
  have hr_nonneg : 0 ≤ r := by
    linarith
  have hr_le_square : r ≤ r ^ 2 := by
    nlinarith [mul_nonneg hr_nonneg (sub_nonneg.mpr hr_one)]
  have hone_le_square : 1 ≤ r ^ 2 := le_trans hr_one hr_le_square
  have hcost_nonneg : ∀ c, 0 ≤ social_cost E c := by
    intro c
    unfold social_cost
    exact integral_nonneg fun _ => dist_nonneg
  have edge_bound {a b : Candidate} (hab : a ≠ b)
      (hdom : deliberation_dominates E k a b) :
      social_cost E a ≤ r * social_cost E b := by
    have h := hedge a b hab hdom
    calc
      social_cost E a =
          ((1 - zeta) * social_cost E a) / (1 - zeta) := by
            field_simp
      _ ≤ ((1 + zeta) * social_cost E b) / (1 - zeta) :=
        (div_le_div_iff_of_pos_right hdenom_pos).2 h
      _ = r * social_cost E b := by
        dsimp [r]
        ring
  change r ^ 2 ≤ D at hfactor
  have hbound :
      social_cost E winner ≤ r ^ 2 * social_cost E optimal := by
    by_cases hsame : winner = optimal
    · subst winner
      simpa using
        (mul_le_mul_of_nonneg_right hone_le_square
          (hcost_nonneg optimal))
    · by_cases hdirect : deliberation_dominates E k winner optimal
      · exact (edge_bound hsame hdirect).trans
          (mul_le_mul_of_nonneg_right hr_le_square
            (hcost_nonneg optimal))
      · have hreverse : deliberation_dominates E k optimal winner :=
          (hcomplete winner optimal hsame).resolve_left hdirect
        have hnot_all :
            ¬ ∀ c, deliberation_dominates E k winner c →
              deliberation_dominates E k optimal c := by
          intro hall
          exact hwinner.1
            ⟨optimal, Ne.symm hsame, hreverse, hall⟩
        push Not at hnot_all
        rcases hnot_all with
          ⟨middle, hwinner_middle, hoptimal_middle⟩
        have hwinner_middle_ne : winner ≠ middle := by
          intro heq
          subst middle
          exact hoptimal_middle hreverse
        have hmiddle_optimal_ne : middle ≠ optimal := by
          intro heq
          subst middle
          exact hdirect hwinner_middle
        have hmiddle_optimal :
            deliberation_dominates E k middle optimal :=
          (hcomplete middle optimal hmiddle_optimal_ne).resolve_right
            hoptimal_middle
        calc
          social_cost E winner ≤ r * social_cost E middle :=
            edge_bound hwinner_middle_ne hwinner_middle
          _ ≤ r * (r * social_cost E optimal) :=
            mul_le_mul_of_nonneg_left
              (edge_bound hmiddle_optimal_ne hmiddle_optimal)
              hr_nonneg
          _ = r ^ 2 * social_cost E optimal := by
            ring
  exact hbound.trans
    (mul_le_mul_of_nonneg_right hfactor (hcost_nonneg optimal))

@[blueprint "lem:random-choice-direct-copeland-two"
  (statement := /-- Let $E$ be a continuum metric election on a nonempty finite candidate set. For groups of size two, every output of the uncovered-set Copeland rule for the Random Choice model has social cost at most $3.344$ times the minimum social cost. -/)
  (proof := /-- Choose the threshold $\zeta_2$ supplied by
  \cref{lem:random-choice-program-bound-two-generic}. It is admissible, it
  bounds every feasible instance of the size-two Random Choice program, and
  its distortion factor satisfies $\Delta(\zeta_2)\leq3.344$. Since $2\leq2$,
  \cref{lem:random-choice-program-controls-pairwise} turns the first two
  properties into pairwise distortion control for the size-two deliberation
  tournament. Applying
  \cref{lem:copeland-distortion-of-pairwise-control} to that control together
  with the factor estimate proves the assertion with $D=3.344$. -/)
  (title := /-- Copeland distortion for groups of size two -/)
  (latexEnv := "lemma")]
lemma random_choice_direct_copeland_two
    {Candidate Voter Point : Type*}
    [Fintype Candidate] [DecidableEq Candidate] [Nonempty Candidate]
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) :
    copeland_distortion_at_most E 2 3.344 := by
  obtain ⟨zeta, hzeta, hbound, hfactor⟩ :=
    random_choice_program_bound_two_generic
  exact copeland_distortion_of_pairwise_control E 2 zeta 3.344
    (random_choice_program_controls_pairwise E 2 zeta le_rfl hzeta hbound)
    hfactor

@[blueprint "lem:random-choice-direct-copeland-four"
  (statement := /-- Let $E$ be a continuum metric election whose candidate
  type is finite and nonempty. For groups of size four, every permitted
  output $w$ of the uncovered-set Copeland rule for the Random Choice model
  and every social optimum $o$ satisfy
  $\operatorname{SC}_E(w)\leq 1.901\operatorname{SC}_E(o)$. -/)
  (proof := /-- Choose $\zeta_4$ from
  \cref{lem:random-choice-program-bound-four}.  Since $2\leq4$, apply
  \cref{lem:random-choice-program-controls-pairwise} to its admissibility
  and program-bound properties.  This gives pairwise distortion control at
  threshold $\zeta_4$.  The same lemma also supplies
  $\Delta(\zeta_4)\leq1901/1000$. Applying
  \cref{lem:copeland-distortion-of-pairwise-control} together with this
  factor estimate gives the asserted bound $D=1901/1000$. -/)
  (title := /-- Copeland distortion for groups of size four -/)
  (latexEnv := "lemma")]
lemma random_choice_direct_copeland_four
    {Candidate Voter Point : Type*}
    [Fintype Candidate] [DecidableEq Candidate] [Nonempty Candidate]
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) :
    copeland_distortion_at_most E 4 1.901 := by
  obtain ⟨zeta, hzeta, hbound, hfactor⟩ :=
    random_choice_program_bound_four
  exact copeland_distortion_of_pairwise_control E 4 zeta 1.901
    (random_choice_program_controls_pairwise E 4 zeta (by norm_num) hzeta
      hbound)
    hfactor

@[blueprint "thm:random-choice-copeland-small-group-distortion"
  (statement := /-- Let $E$ be any continuum metric electorate on a nonempty
  finite set of candidates. Voters are distributed according to an arbitrary
  probability measure, and every deliberating group is sampled independently
  with replacement from that measure. In the Random Choice deliberation
  model, Copeland distortion is at most $3.344$ for group size $2$, at most
  $2.31$ for group size $3$, and at most $1.901$ for group size $4$. Each
  bound holds for every permitted tie-breaking among maximum-score
  candidates in the uncovered set. -/)
  (proof := /-- The size-two assertion is
  \cref{lem:random-choice-direct-copeland-two}, and the size-four assertion
  is \cref{lem:random-choice-direct-copeland-four}. For size three, choose
  the admissible threshold supplied by
  \cref{lem:random-choice-program-bound-three}. Apply
  \cref{lem:random-choice-program-controls-pairwise} to obtain pairwise
  distortion control, and then apply
  \cref{lem:copeland-distortion-of-pairwise-control} with $D=2.31$.
  Combining these three conclusions gives the stated conjunction. -/)
  (title := /-- Random Choice Copeland distortion for small groups -/)
  (latexEnv := "theorem")]
theorem random_choice_copeland_small_group_distortion
    {Candidate Voter Point : Type*}
    [Fintype Candidate] [DecidableEq Candidate] [Nonempty Candidate]
    [MeasurableSpace Voter] [MetricSpace Point]
    [MeasurableSpace Point] [BorelSpace Point]
    (E : metric_election Candidate Voter Point) :
      copeland_distortion_at_most E 2 3.344 ∧
      copeland_distortion_at_most E 3 2.31 ∧
      copeland_distortion_at_most E 4 1.901 := by
  refine ⟨random_choice_direct_copeland_two E, ?_,
    random_choice_direct_copeland_four E⟩
  obtain ⟨zeta, hzeta, hbound, hfactor⟩ := random_choice_program_bound_three
  exact copeland_distortion_of_pairwise_control E 3 zeta 2.31
    (random_choice_program_controls_pairwise E 3 zeta (by norm_num) hzeta
      hbound)
    hfactor

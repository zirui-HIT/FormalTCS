import Architect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.SubGaussian

set_option linter.all false
set_option maxHeartbeats 500000

universe u

@[blueprint "def:hypothesis-selection-total-variation-distance"
  (statement := /-- Let $\mathcal{X}$ be a measurable space and let $P$ and $Q$ be probability measures on $\mathcal{X}$. Their total-variation distance is the supremum, over all measurable sets $S \subseteq \mathcal{X}$, of $\max\{P(S)-Q(S),Q(S)-P(S)\}$. The differences are taken in the extended nonnegative reals. -/)
  (title := /-- Total-variation distance -/)
  (latexEnv := "definition")]
noncomputable def hypothesis_selection_total_variation_distance
    {X : Type u} [MeasurableSpace X]
    (P Q : MeasureTheory.ProbabilityMeasure X) : ENNReal :=
  ⨆ (s : Set X) (_hs : MeasurableSet s),
    max ((P s : NNReal) - (Q s : NNReal) : ENNReal)
      ((Q s : NNReal) - (P s : NNReal) : ENNReal)

@[blueprint "def:hypothesis-selection-optimum"
  (statement := /-- Let $n$ be a positive integer, let $P$ be a probability measure on a measurable space $\mathcal{X}$, and let $H=(H_i)_{i\in [n]}$ be a family of probability measures on $\mathcal{X}$. Define $\operatorname{OPT}(P,H)$ to be $\inf_{i\in[n]} d_{\mathrm{TV}}(P,H_i)$. -/)
  (title := /-- Best total-variation error in the hypothesis class -/)
  (latexEnv := "definition")]
noncomputable def hypothesis_selection_optimum
    {X : Type u} [MeasurableSpace X] {n : ℕ}
    (P : MeasureTheory.ProbabilityMeasure X)
    (H : Fin n → MeasureTheory.ProbabilityMeasure X) : ENNReal :=
  ⨅ i : Fin n, hypothesis_selection_total_variation_distance P (H i)

@[blueprint "def:hypothesis-selection-hypothesis-oracle"
  (statement := /-- Let $H=(H_i)_{i\in[n]}$ be a finite family of probability measures on a measurable space $\mathcal{X}$. An oracle presentation consists of a probability space $(\Omega,\mathbb{P})$, measurable sampling maps $S_{i,k}:\Omega\to\mathcal{X}$ for $i\in[n]$ and $k\in\mathbb{N}$, and measurable pdf or pmf functions $q_i:\mathcal{X}\to\mathbb{R}_{\geq 0}\cup\{\infty\}$. Each sampling map has pushforward law $H_i$. Moreover, relative to a disclosed reference measure $\mu$, one has $H_i=\mu[q_i]$ for every $i$, where $\mu[q_i]$ denotes the measure with density $q_i$ with respect to $\mu$. These identities make both oracle operations semantically inseparable from the family $H$. -/)
  (title := /-- Certified oracle presentation of the hypotheses -/)
  (latexEnv := "definition")]
structure hypothesis_selection_hypothesis_oracle
    (X : Type u) [MeasurableSpace X] (n : ℕ)
    (H : Fin n → MeasureTheory.ProbabilityMeasure X) where
  Randomness : Type u
  randomnessMeasurable : MeasurableSpace Randomness
  randomnessLaw :
    @MeasureTheory.ProbabilityMeasure Randomness randomnessMeasurable
  sample : Fin n → ℕ → Randomness → X
  sampleMeasurable : ∀ i seed,
    @Measurable Randomness X randomnessMeasurable _ (sample i seed)
  sampleLaw : ∀ i seed s, MeasurableSet s →
    randomnessLaw ((sample i seed) ⁻¹' s) = H i s
  referenceMeasure : MeasureTheory.Measure X
  pdfQuery : Fin n → X → ENNReal
  pdfQueryMeasurable : ∀ i, Measurable (pdfQuery i)
  pdfQueryLaw : ∀ i,
    referenceMeasure.withDensity (pdfQuery i) =
      (H i : MeasureTheory.Measure X)

@[blueprint "def:hypothesis-selection-oracle-answer"
  (statement := /-- The answer register of a hypothesis-selection machine is either empty, contains a target sample, contains a sample returned by a hypothesis oracle, or contains the value returned by a pdf or pmf query. Keeping answers in an explicit register ensures that inspecting and processing an answer occurs only during subsequent machine transitions. -/)
  (title := /-- Oracle-answer register -/)
  (latexEnv := "definition")]
inductive hypothesis_selection_oracle_answer (X : Type u) : Type u where
  | empty : hypothesis_selection_oracle_answer X
  | targetSample (x : X) : hypothesis_selection_oracle_answer X
  | hypothesisSample (x : X) : hypothesis_selection_oracle_answer X
  | hypothesisPdf (q : ENNReal) : hypothesis_selection_oracle_answer X

@[blueprint "def:hypothesis-selection-machine-instruction"
  (statement := /-- Fix a state space, a target-sample budget $m$, and $n$ hypotheses on $\mathcal{X}$. One machine instruction either halts with an index in $[n]$, performs one internal transition, requests one of the $m$ target samples, requests a seeded sample from one of the hypotheses, or requests a pdf or pmf value at a specified point. A request records only the state in which execution resumes; the returned value is placed in the machine's answer register rather than supplied to a host-language continuation. -/)
  (title := /-- Instructions for the oracle machine -/)
  (latexEnv := "definition")]
inductive hypothesis_selection_machine_instruction
    (X : Type u) (n sampleCount : ℕ) (State : Type u) : Type u where
  | output (i : Fin n) :
      hypothesis_selection_machine_instruction X n sampleCount State
  | step (nextState : State) :
      hypothesis_selection_machine_instruction X n sampleCount State
  | targetSample (j : Fin sampleCount) (resumeState : State) :
      hypothesis_selection_machine_instruction X n sampleCount State
  | hypothesisSample (i : Fin n) (seed : ℕ) (resumeState : State) :
      hypothesis_selection_machine_instruction X n sampleCount State
  | hypothesisPdf (i : Fin n) (x : X) (resumeState : State) :
      hypothesis_selection_machine_instruction X n sampleCount State

@[blueprint "def:hypothesis-selection-computation"
  (statement := /-- A hypothesis-selection computation is a clocked oracle machine. It has a state space, an initial state, and an instruction decoder which reads the current state and answer register. One invocation of the decoder executes exactly one instruction. In particular, after an oracle request places a value in the answer register, every stage of processing that value must be represented by further state transitions and is therefore visible to the machine clock. -/)
  (title := /-- Clocked oracle-machine computation -/)
  (latexEnv := "definition")]
structure hypothesis_selection_computation
    (X : Type u) (n sampleCount : ℕ) : Type (u + 1) where
  State : Type u
  initialState : State
  instruction :
    State → hypothesis_selection_oracle_answer X →
      hypothesis_selection_machine_instruction X n sampleCount State

@[blueprint "def:hypothesis-selection-computation-evaluate"
  (statement := /-- Given a certified presentation of $H$, a target-sample vector, and an oracle-randomness outcome, the fuelled evaluator executes at most the specified number of clock transitions. Each invocation of the instruction decoder consumes one unit of fuel. A target or hypothesis sample, or a pdf or pmf answer, is installed in the answer register by its request transition and can influence the output only when a later, separately charged transition reads that register. -/)
  (title := /-- Fuelled evaluation of the oracle machine -/)
  (latexEnv := "definition")]
def hypothesis_selection_computation_evaluate
    {X : Type u} [MeasurableSpace X] {n sampleCount : ℕ}
    {H : Fin n → MeasureTheory.ProbabilityMeasure X}
    (O : hypothesis_selection_hypothesis_oracle X n H)
    (ω : Fin sampleCount → X) (r : O.Randomness)
    (C : hypothesis_selection_computation X n sampleCount) :
    ℕ → C.State → hypothesis_selection_oracle_answer X → Option (Fin n)
  | 0, _, _ => none
  | fuel + 1, state, answer =>
      match C.instruction state answer with
      | .output i => some i
      | .step nextState =>
          hypothesis_selection_computation_evaluate O ω r C fuel nextState .empty
      | .targetSample j resumeState =>
          hypothesis_selection_computation_evaluate O ω r C fuel resumeState
            (.targetSample (ω j))
      | .hypothesisSample i seed resumeState =>
          hypothesis_selection_computation_evaluate O ω r C fuel resumeState
            (.hypothesisSample (O.sample i seed r))
      | .hypothesisPdf i x resumeState =>
          hypothesis_selection_computation_evaluate O ω r C fuel resumeState
            (.hypothesisPdf (O.pdfQuery i x))

@[blueprint "def:hypothesis-selection-computation-cost"
  (statement := /-- Suppose a clocked oracle machine halts on fixed target samples and fixed oracle randomness. Its operational cost is the least fuel for which the evaluator returns an output. This cost counts every decoded instruction, including each oracle request and every subsequent transition that reads or processes its answer. -/)
  (title := /-- Halting time of an oracle-machine computation -/)
  (latexEnv := "definition")]
noncomputable def hypothesis_selection_computation_cost
    {X : Type u} [MeasurableSpace X] {n sampleCount : ℕ}
    {H : Fin n → MeasureTheory.ProbabilityMeasure X}
    (O : hypothesis_selection_hypothesis_oracle X n H)
    (ω : Fin sampleCount → X) (r : O.Randomness)
    (C : hypothesis_selection_computation X n sampleCount)
    (halts : ∃ fuel, ∃ i,
      hypothesis_selection_computation_evaluate O ω r C fuel
        C.initialState .empty = some i) : ℕ :=
  Nat.find halts

@[blueprint "def:hypothesis-selection-algorithm"
  (statement := /-- Fix a certified oracle presentation $O$ of $H=(H_i)_{i\in[n]}$. A proper sample-based hypothesis-selection algorithm consists of a target-sample count and a clocked oracle machine which halts for every target-sample vector and every outcome in the randomness space of $O$. The presentation is a parameter of the algorithm, so an algorithm cannot substitute sampling or pdf/pmf operations unrelated to $H$. -/)
  (title := /-- Proper selector over a certified oracle -/)
  (latexEnv := "definition")]
structure hypothesis_selection_algorithm
    (X : Type u) [MeasurableSpace X] (n : ℕ)
    (H : Fin n → MeasureTheory.ProbabilityMeasure X)
    (O : hypothesis_selection_hypothesis_oracle X n H) where
  sampleCount : ℕ
  program : hypothesis_selection_computation X n sampleCount
  halts : ∀ (ω : Fin sampleCount → X) (r : O.Randomness),
    ∃ fuel, ∃ i,
      hypothesis_selection_computation_evaluate O ω r program fuel
        program.initialState .empty = some i

@[blueprint "def:hypothesis-selection-selected-index"
  (statement := /-- The index selected by a proper hypothesis-selection algorithm on a target-sample vector and an oracle-randomness outcome is the output returned at the machine's least halting fuel. -/)
  (title := /-- Index returned by a hypothesis selector -/)
  (latexEnv := "definition")]
noncomputable def hypothesis_selection_selected_index
    {X : Type u} [MeasurableSpace X] {n : ℕ}
    {H : Fin n → MeasureTheory.ProbabilityMeasure X}
    {O : hypothesis_selection_hypothesis_oracle X n H}
    (A : hypothesis_selection_algorithm X n H O)
    (ω : Fin A.sampleCount → X) (r : O.Randomness) : Fin n :=
  Classical.choose (Nat.find_spec (A.halts ω r))

@[blueprint "def:hypothesis-selection-execution-cost"
  (statement := /-- The execution cost of a proper hypothesis-selection algorithm on a target-sample vector and an oracle-randomness outcome is the least number of clock transitions required to halt. It is derived from the evaluator and the machine's termination proof, rather than supplied as a separate annotation. -/)
  (title := /-- Execution cost of a hypothesis selector -/)
  (latexEnv := "definition")]
noncomputable def hypothesis_selection_execution_cost
    {X : Type u} [MeasurableSpace X] {n : ℕ}
    {H : Fin n → MeasureTheory.ProbabilityMeasure X}
    {O : hypothesis_selection_hypothesis_oracle X n H}
    (A : hypothesis_selection_algorithm X n H O)
    (ω : Fin A.sampleCount → X) (r : O.Randomness) : ℕ :=
  hypothesis_selection_computation_cost O ω r A.program (A.halts ω r)

@[blueprint "def:hypothesis-selection-sample-law"
  (statement := /-- Let $P$ be a probability measure on a measurable space $\mathcal{X}$ and let $m$ be a natural number. The law of an ordered sample of size $m$ drawn independently from $P$ is the product probability measure $P^{\otimes m}$ on $\mathcal{X}^m$. -/)
  (title := /-- Law of an independent finite sample -/)
  (latexEnv := "definition")]
noncomputable def hypothesis_selection_sample_law
    {X : Type u} [MeasurableSpace X]
    (P : MeasureTheory.ProbabilityMeasure X) (m : ℕ) :
    MeasureTheory.ProbabilityMeasure (Fin m → X) :=
  MeasureTheory.ProbabilityMeasure.pi (fun _ : Fin m ↦ P)

@[blueprint "def:hypothesis-selection-good-sample-set"
  (statement := /-- Fix a target probability measure $P$, hypotheses $H=(H_i)_{i\in[n]}$, a certified presentation $O$, an additive error $\varepsilon$, and a proper selector $A$. The good-outcome set consists of the pairs $(\omega,r)$ of a target-sample vector and an oracle-randomness outcome for which the selected hypothesis satisfies $d_{\mathrm{TV}}(P,H_{A(\omega,r)})\leq 3\operatorname{OPT}(P,H)+\varepsilon$. -/)
  (title := /-- Random outcomes attaining factor three -/)
  (latexEnv := "definition")]
noncomputable def hypothesis_selection_good_sample_set
    {X : Type u} [MeasurableSpace X] {n : ℕ}
    (P : MeasureTheory.ProbabilityMeasure X)
    (H : Fin n → MeasureTheory.ProbabilityMeasure X) (ε : ℝ)
    (O : hypothesis_selection_hypothesis_oracle X n H)
    (A : hypothesis_selection_algorithm X n H O) :
    Set ((Fin A.sampleCount → X) × O.Randomness) :=
  {outcome |
    hypothesis_selection_total_variation_distance P
        (H (hypothesis_selection_selected_index A outcome.1 outcome.2)) ≤
      3 * hypothesis_selection_optimum P H + ENNReal.ofReal ε}

@[blueprint "def:hypothesis-selection-guarantee"
  (statement := /-- Fix $\varepsilon>0$ and $\delta\in(0,1)$. A proper selector $A$ has the factor-three guarantee for $P$ and a certified presentation $O$ of $H$ if its good-outcome set is measurable and has probability at least $1-\delta$ under the product of the independent target-sample law $P^{\otimes m}$ and the oracle-randomness law of $O$. Thus randomness used for sampling the hypotheses is included in the success probability. -/)
  (title := /-- Factor-three statistical guarantee -/)
  (latexEnv := "definition")]
noncomputable def hypothesis_selection_guarantee
    {X : Type u} [MeasurableSpace X] {n : ℕ}
    (P : MeasureTheory.ProbabilityMeasure X)
    (H : Fin n → MeasureTheory.ProbabilityMeasure X) (ε δ : ℝ)
    (O : hypothesis_selection_hypothesis_oracle X n H)
    (A : hypothesis_selection_algorithm X n H O) : Prop :=
  letI : MeasurableSpace O.Randomness := O.randomnessMeasurable
  MeasurableSet (hypothesis_selection_good_sample_set P H ε O A) ∧
    Real.toNNReal (1 - δ) ≤
      (hypothesis_selection_sample_law P A.sampleCount).prod O.randomnessLaw
        (hypothesis_selection_good_sample_set P H ε O A)

@[blueprint "def:hypothesis-selection-resource-bounds"
  (statement := /-- Let $c_s,c_t>0$ and $k\in\mathbb{N}$. A selector $A$ satisfies the advertised resource bounds at parameters $(n,\varepsilon,\delta)$ if its target-sample count is at most $c_s\log(n/\delta)/\varepsilon^2$ and, for every target-sample vector and every oracle-randomness outcome, its least halting time is at most $c_t\max\{1,n/(\varepsilon^2\delta)\}$ times the $k$-th power of the logarithm of the larger of $2$ and $n/(\varepsilon^2\delta)$. The maximum with $1$ gives the exact all-parameter formulation of the soft asymptotic running-time bound while respecting the unit cost of a halting computation. -/)
  (title := /-- Explicit sample and soft-linear running-time bounds -/)
  (latexEnv := "definition")]
def hypothesis_selection_resource_bounds
    {X : Type u} [MeasurableSpace X] {n : ℕ}
    {H : Fin n → MeasureTheory.ProbabilityMeasure X}
    {O : hypothesis_selection_hypothesis_oracle X n H}
    (ε δ cSample cTime : ℝ) (polylogExponent : ℕ)
    (A : hypothesis_selection_algorithm X n H O) : Prop :=
  (A.sampleCount : ℝ) ≤
      cSample * Real.log ((n : ℝ) / δ) / ε ^ 2 ∧
    ∀ (ω : Fin A.sampleCount → X) (r : O.Randomness),
      (hypothesis_selection_execution_cost A ω r : ℝ) ≤
        cTime * max 1 ((n : ℝ) / (ε ^ 2 * δ)) *
          Real.log (max 2 ((n : ℝ) / (ε ^ 2 * δ))) ^ polylogExponent

@[blueprint "def:hypothesis-selection-fast-statement"
  (statement := /-- There exist universal positive constants $c_s,c_t$ and a universal exponent $k\in\mathbb{N}$ such that, for every $n\geq 1$, every measurable space $\mathcal{X}$, every family $H=(H_i)_{i\in[n]}$ of probability measures, every certified sample-and-pdf/pmf presentation $O$ of $H$, every $\varepsilon>0$, and every $\delta\in(0,1)$ satisfying $\delta>1/n$, there is a proper selector over $O$. Its target-sample count is at most $c_s\log(n/\delta)/\varepsilon^2$; its clocked running time is at most $c_t\max\{1,n/(\varepsilon^2\delta)\}$ times a $k$-th power of the logarithm of the larger of $2$ and $n/(\varepsilon^2\delta)$; and, uniformly for every unknown probability measure $P$, it returns a member of $H$ at total-variation distance at most $3\operatorname{OPT}(P,H)+\varepsilon$ with probability at least $1-\delta$. -/)
  (title := /-- Uniform fast hypothesis-selection assertion -/)
  (latexEnv := "definition")]
def hypothesis_selection_fast_statement : Prop :=
  ∃ cSample cTime : ℝ,
    0 < cSample ∧ 0 < cTime ∧
      ∃ polylogExponent : ℕ,
        ∀ (n : ℕ) (_hn : 0 < n) (X : Type u) [MeasurableSpace X]
          (H : Fin n → MeasureTheory.ProbabilityMeasure X)
          (O : hypothesis_selection_hypothesis_oracle X n H) (ε δ : ℝ),
          0 < ε → 0 < δ → δ < 1 → 1 / (n : ℝ) < δ →
            ∃ A : hypothesis_selection_algorithm X n H O,
              hypothesis_selection_resource_bounds
                  ε δ cSample cTime polylogExponent A ∧
                ∀ P : MeasureTheory.ProbabilityMeasure X,
                  hypothesis_selection_guarantee P H ε δ O A

@[blueprint "lem:fast-hypothesis-selector-construction"
  (statement := /-- There exist positive real constants $c_s,c_t$ and an exponent $k\in\mathbb{N}$ such that, for every positive integer $n$, every measurable space $\mathcal{X}$, every family $H=(H_i)_{i\in[n]}$ of probability measures on $\mathcal{X}$, every certified sample-and-density oracle presentation $O$ of $H$, every $\varepsilon>0$, and every $\delta\in(0,1)$ satisfying $1/n<\delta$, there is a proper selector $A$ over $O$. Its target-sample count is at most $c_s\log(n/\delta)/\varepsilon^2$; for every target-sample vector and oracle-randomness outcome, its execution cost is at most $c_t\max\{1,n/(\varepsilon^2\delta)\}\log(\max\{2,n/(\varepsilon^2\delta)\})^k$; and, for every probability measure $P$ on $\mathcal{X}$, it returns a member of $H$ at total-variation distance at most $3\operatorname{OPT}(P,H)+\varepsilon$ with probability at least $1-\delta$. -/)
  (proof := /-- Take $c_s=64+1/\log 2$, $c_t=1024$, and $k=0$. Total variation is at most one and satisfies the triangle inequality. If $\varepsilon\geq 1$, the constant selector using no target samples therefore suffices. Suppose instead that $0<\varepsilon<1$. For every ordered pair of hypotheses, choose a measurable set whose probability gap is within $\varepsilon/2$ of their total-variation distance. With $m=\lceil 64\log(n/\delta)/\varepsilon^2\rceil$, select the hypothesis minimizing the largest discrepancy, over these finitely many witness sets, between its probability and the empirical target frequency. This finite argmin is measurable. Hoeffding's sub-Gaussian moment bound for every indicator, followed by a union bound over the $n^2$ witness sets, shows that all empirical frequencies differ from their target probabilities by less than $\varepsilon/4$ with probability at least $1-\delta$. On this event, comparison with a best hypothesis, the witness inequalities, and the triangle inequality give total-variation error at most $3\operatorname{OPT}+\varepsilon$. Implement the selector as a clocked machine which requests the $m$ target samples successively, stores them in a finite buffer, and then outputs the argmin. An induction on the request list proves that it returns the stated selector in exactly $2m+1$ transitions. The ceiling estimate gives the asserted sample bound, while $\log(n/\delta)\leq n/\delta$ and $\varepsilon,\delta<1$ give $2m+1\leq 1024\max\{1,n/(\varepsilon^2\delta)\}$. Since the output is independent of oracle randomness, the measurable good set is the product of its target-sample section with the whole oracle-randomness space, so the product-law probability bound follows from the simultaneous concentration event. -/)
  (title := /-- Construction and analysis of the fast selector -/)
  (latexEnv := "lemma")]
lemma fast_hypothesis_selector_construction :
    hypothesis_selection_fast_statement := by
  classical
  unfold hypothesis_selection_fast_statement
  refine ⟨64 + 1 / Real.log 2, 1024, by positivity, by norm_num, 0, ?_⟩
  intro n hn X _ H O ε δ hε hδ hδ_one hnδ
  have tv_le_one : ∀ P Q : MeasureTheory.ProbabilityMeasure X,
      hypothesis_selection_total_variation_distance P Q ≤ 1 := by
    intro P Q
    unfold hypothesis_selection_total_variation_distance
    refine iSup_le fun s => iSup_le fun hs => max_le ?_ ?_
    · exact (tsub_le_self.trans (by exact_mod_cast P.apply_le_one s))
    · exact (tsub_le_self.trans (by exact_mod_cast Q.apply_le_one s))
  have measure_gap_eq : ∀ P Q : MeasureTheory.ProbabilityMeasure X,
      ∀ s : Set X,
        (max ((((P s : NNReal) - (Q s : NNReal) : NNReal) : ENNReal))
          ((((Q s : NNReal) - (P s : NNReal) : NNReal) : ENNReal))).toReal =
            |((P s : NNReal) : ℝ) - ((Q s : NNReal) : ℝ)| := by
    intro P Q s
    rw [ENNReal.toReal_max (by simp) (by simp)]
    simp only [ENNReal.coe_toReal]
    by_cases hab : (P s : NNReal) ≤ (Q s : NNReal)
    · have habR : ((P s : NNReal) : ℝ) ≤ (Q s : NNReal) := by
        exact_mod_cast hab
      rw [tsub_eq_zero_of_le hab, NNReal.coe_zero,
        NNReal.coe_sub (r₁ := Q s) (r₂ := P s) hab,
        max_eq_right (show (0 : ℝ) ≤
          ((Q s : NNReal) : ℝ) - (P s : NNReal) by positivity),
        abs_of_nonpos (sub_nonpos.mpr habR)]
      ring
    · have hba : (Q s : NNReal) ≤ (P s : NNReal) := le_of_not_ge hab
      have hbaR : ((Q s : NNReal) : ℝ) ≤ (P s : NNReal) := by
        exact_mod_cast hba
      rw [tsub_eq_zero_of_le hba, NNReal.coe_zero,
        NNReal.coe_sub (r₁ := P s) (r₂ := Q s) hba,
        max_eq_left (show (0 : ℝ) ≤
          ((P s : NNReal) : ℝ) - (Q s : NNReal) by positivity),
        abs_of_nonneg (sub_nonneg.mpr hbaR)]
  have measurable_gap_le_tv : ∀ P Q : MeasureTheory.ProbabilityMeasure X,
      ∀ s : Set X, MeasurableSet s →
        |((P s : NNReal) : ℝ) - ((Q s : NNReal) : ℝ)| ≤
          (hypothesis_selection_total_variation_distance P Q).toReal := by
    intro P Q s hs
    have htv_ne : hypothesis_selection_total_variation_distance P Q ≠ ⊤ :=
      ne_top_of_le_ne_top (by norm_num) (tv_le_one P Q)
    have hpoint :
        max ((((P s : NNReal) - (Q s : NNReal) : NNReal) : ENNReal))
            ((((Q s : NNReal) - (P s : NNReal) : NNReal) : ENNReal)) ≤
          hypothesis_selection_total_variation_distance P Q := by
      exact le_iSup_of_le s (le_iSup_of_le hs (by rfl))
    rw [← measure_gap_eq P Q s]
    exact ENNReal.toReal_mono htv_ne hpoint
  have tv_triangle : ∀ P Q R : MeasureTheory.ProbabilityMeasure X,
      hypothesis_selection_total_variation_distance P R ≤
        hypothesis_selection_total_variation_distance P Q +
          hypothesis_selection_total_variation_distance Q R := by
    intro P Q R
    unfold hypothesis_selection_total_variation_distance
    refine iSup_le fun s => iSup_le fun hs => max_le ?_ ?_
    · calc
        (((P s : NNReal) - (R s : NNReal) : NNReal) : ENNReal) ≤
            (((P s : NNReal) - (Q s : NNReal) : NNReal) : ENNReal) +
              (((Q s : NNReal) - (R s : NNReal) : NNReal) : ENNReal) :=
          by
            exact_mod_cast (tsub_le_tsub_add_tsub :
              (P s : NNReal) - (R s : NNReal) ≤
                ((P s : NNReal) - (Q s : NNReal)) +
                  ((Q s : NNReal) - (R s : NNReal)))
        _ ≤ (⨆ (s : Set X) (_hs : MeasurableSet s),
              max ((((P s : NNReal) - (Q s : NNReal) : NNReal) : ENNReal))
                ((((Q s : NNReal) - (P s : NNReal) : NNReal) : ENNReal))) +
            (⨆ (s : Set X) (_hs : MeasurableSet s),
              max ((((Q s : NNReal) - (R s : NNReal) : NNReal) : ENNReal))
                ((((R s : NNReal) - (Q s : NNReal) : NNReal) : ENNReal))) := by
          apply add_le_add
          · exact le_iSup_of_le s (le_iSup_of_le hs (le_max_left _ _))
          · exact le_iSup_of_le s (le_iSup_of_le hs (le_max_left _ _))
    · calc
        (((R s : NNReal) - (P s : NNReal) : NNReal) : ENNReal) ≤
            (((Q s : NNReal) - (P s : NNReal) : NNReal) : ENNReal) +
              (((R s : NNReal) - (Q s : NNReal) : NNReal) : ENNReal) := by
          exact_mod_cast (show (R s : NNReal) - (P s : NNReal) ≤
              ((Q s : NNReal) - (P s : NNReal)) +
                ((R s : NNReal) - (Q s : NNReal)) by
            simpa [add_comm] using (tsub_le_tsub_add_tsub :
              (R s : NNReal) - (P s : NNReal) ≤
                ((R s : NNReal) - (Q s : NNReal)) +
                  ((Q s : NNReal) - (P s : NNReal))))
        _ ≤ (⨆ (s : Set X) (_hs : MeasurableSet s),
              max ((((P s : NNReal) - (Q s : NNReal) : NNReal) : ENNReal))
                ((((Q s : NNReal) - (P s : NNReal) : NNReal) : ENNReal))) +
            (⨆ (s : Set X) (_hs : MeasurableSet s),
              max ((((Q s : NNReal) - (R s : NNReal) : NNReal) : ENNReal))
                ((((R s : NNReal) - (Q s : NNReal) : NNReal) : ENNReal))) := by
          apply add_le_add
          · exact le_iSup_of_le s (le_iSup_of_le hs (le_max_right _ _))
          · exact le_iSup_of_le s (le_iSup_of_le hs (le_max_right _ _))
  have exists_tv_witness : ∀ P Q : MeasureTheory.ProbabilityMeasure X,
      ∀ η : ℝ, 0 < η →
        ∃ s : Set X, MeasurableSet s ∧
          (hypothesis_selection_total_variation_distance P Q).toReal ≤
            |((P s : NNReal) : ℝ) - ((Q s : NNReal) : ℝ)| + η := by
    intro P Q η hη
    let D := hypothesis_selection_total_variation_distance P Q
    have hD_ne : D ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (tv_le_one P Q)
    by_cases hsmall : D.toReal ≤ η
    · refine ⟨∅, MeasurableSet.empty, ?_⟩
      simpa using hsmall
    · have hηD : η < D.toReal := lt_of_not_ge hsmall
      have hdiff : 0 < D.toReal - η := sub_pos.mpr hηD
      have hbase : ENNReal.ofReal (D.toReal - η) < D :=
        (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hdiff) hD_ne).2 (by linarith)
      dsimp [D] at hbase
      rw [hypothesis_selection_total_variation_distance, lt_iSup_iff] at hbase
      obtain ⟨s, hbase⟩ := hbase
      rw [lt_iSup_iff] at hbase
      obtain ⟨hs, hgap⟩ := hbase
      refine ⟨s, hs, ?_⟩
      have hgapReal : D.toReal - η <
          (max ((((P s : NNReal) - (Q s : NNReal) : NNReal) : ENNReal))
            ((((Q s : NNReal) - (P s : NNReal) : NNReal) : ENNReal))).toReal := by
        rw [← ENNReal.toReal_ofReal (le_of_lt hdiff)]
        exact (ENNReal.toReal_lt_toReal (by simp) (by simp)).2 hgap
      rw [measure_gap_eq P Q s] at hgapReal
      linarith
  by_cases hlarge : 1 ≤ ε
  · let i₀ : Fin n := ⟨0, hn⟩
    let C : hypothesis_selection_computation X n 0 :=
      { State := X
        initialState := Classical.choice (H i₀).nonempty
        instruction := fun _ _ => .output i₀ }
    let A : hypothesis_selection_algorithm X n H O :=
      { sampleCount := 0
        program := C
        halts := by
          intro ω r
          exact ⟨1, i₀, by simp [C, hypothesis_selection_computation_evaluate]⟩ }
    refine ⟨A, ?_, ?_⟩
    · constructor
      · simp only [A, hypothesis_selection_resource_bounds]
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have hratio : 1 < (n : ℝ) / δ :=
          (lt_div_iff₀ hδ).2 (by simpa using (lt_of_lt_of_le hδ_one hnR))
        norm_num
        exact div_nonneg (mul_nonneg (by positivity)
          (Real.log_nonneg (le_of_lt hratio))) (sq_nonneg ε)
      · intro ω r
        simp only [A, hypothesis_selection_execution_cost,
          hypothesis_selection_computation_cost]
        have hcost : Nat.find (A.halts ω r) ≤ 1 := by
          apply Nat.find_le
          exact ⟨i₀, by simp [A, C, hypothesis_selection_computation_evaluate]⟩
        have hcostReal : (Nat.find (A.halts ω r) : ℝ) ≤ 1 := by exact_mod_cast hcost
        simpa using hcostReal.trans (by
          have hmax : (1 : ℝ) ≤ max 1 ((n : ℝ) / (ε ^ 2 * δ)) := le_max_left _ _
          norm_num
          linarith)
    · intro P
      have hgood : hypothesis_selection_good_sample_set P H ε O A = Set.univ := by
        ext outcome
        simp only [hypothesis_selection_good_sample_set, Set.mem_setOf_eq,
          Set.mem_univ, iff_true]
        calc
          hypothesis_selection_total_variation_distance P
              (H (hypothesis_selection_selected_index A outcome.1 outcome.2)) ≤ 1 :=
            tv_le_one _ _
          _ ≤ ENNReal.ofReal ε := ENNReal.one_le_ofReal.mpr hlarge
          _ ≤ 3 * hypothesis_selection_optimum P H + ENNReal.ofReal ε := by
            exact le_add_self
      simp [hypothesis_selection_guarantee, hgood, le_of_lt hδ]
  · have hε_one : ε < 1 := lt_of_not_ge hlarge
    have bernoulli_concentration : ∀ (P : MeasureTheory.ProbabilityMeasure X)
        (m : ℕ) (s : Set X), MeasurableSet s → ∀ a : ℝ, 0 ≤ a →
          (hypothesis_selection_sample_law P m : MeasureTheory.Measure (Fin m → X)).real
              {ω | a ≤ |(∑ j : Fin m, s.indicator 1 (ω j)) /
                  (m : ℝ) - ((P s : NNReal) : ℝ)|} ≤
            2 * Real.exp (-2 * (m : ℝ) * a ^ 2) := by
      intro P m s hs a ha
      by_cases hm : m = 0
      · subst m
        exact MeasureTheory.measureReal_le_one.trans (by norm_num)
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        let μ : MeasureTheory.Measure (Fin m → X) :=
          hypothesis_selection_sample_law P m
        let Y : Fin m → (Fin m → X) → ℝ := fun j ω =>
          s.indicator 1 (ω j)
        have hYmeas : ∀ j, Measurable (Y j) := by
          intro j
          exact (measurable_const.indicator hs).comp (measurable_pi_apply j)
        have hYint : ∀ j, ∫ ω, Y j ω ∂μ = ((P s : NNReal) : ℝ) := by
          intro j
          dsimp [μ, hypothesis_selection_sample_law, Y]
          rw [MeasureTheory.integral_comp_eval (measurable_const.indicator hs).aestronglyMeasurable]
          exact MeasureTheory.integral_indicator_one (μ := (P : MeasureTheory.Measure X)) hs
        have hYindep : ProbabilityTheory.iIndepFun Y μ := by
          dsimp [μ, hypothesis_selection_sample_law, Y]
          exact ProbabilityTheory.iIndepFun_pi
            (fun _ => (measurable_const.indicator hs).aemeasurable)
        let Z : Fin m → (Fin m → X) → ℝ := fun j ω => Y j ω - ∫ z, Y j z ∂μ
        let c : NNReal := 1 / 4
        have hZindep : ProbabilityTheory.iIndepFun Z μ := by
          exact hYindep.comp
            (fun j x => x - ∫ z, Y j z ∂μ)
            (fun _ => measurable_id.sub_const _)
        have hZsub : ∀ j : Fin m,
            ProbabilityTheory.HasSubgaussianMGF (Z j)
              c μ := by
          intro j
          dsimp [c]
          convert ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
              (μ := μ) (X := Y j) (a := 0) (b := 1)
              (hYmeas j).aemeasurable
              (Filter.Eventually.of_forall fun ω => by
                by_cases hx : ω j ∈ s <;> simp [Y, hx]) using 1 <;>
            norm_num [Z]
        have hsum := ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun
          hZindep (s := (Finset.univ : Finset (Fin m)))
          (c := fun _ => c)
          (fun j _ => hZsub j)
        have hu := hsum.measure_ge_le (ε := (m : ℝ) * a)
          (mul_nonneg (by positivity) ha)
        have hl := hsum.neg.measure_ge_le (ε := (m : ℝ) * a)
          (mul_nonneg (by positivity) ha)
        have hset :
            {ω | a ≤ |(∑ j : Fin m, s.indicator 1 (ω j)) /
                (m : ℝ) - ((P s : NNReal) : ℝ)|} =
              {ω | (m : ℝ) * a ≤ ∑ j : Fin m, Z j ω} ∪
                {ω | (m : ℝ) * a ≤ -(∑ j : Fin m, Z j ω)} := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_union]
          simp_rw [Z, hYint]
          rw [Finset.sum_sub_distrib]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
          constructor
          · intro h
            rcases (le_total 0
              ((∑ j : Fin m, Y j ω) / (m : ℝ) - ((P s : NNReal) : ℝ))) with hp | hp
            · left
              rw [abs_of_nonneg hp] at h
              field_simp at h ⊢
              nlinarith
            · right
              rw [abs_of_nonpos hp] at h
              field_simp at h ⊢
              nlinarith
          · intro h
            rcases h with h | h
            · rw [abs_of_nonneg]
              · field_simp at h ⊢
                nlinarith
              · field_simp at h ⊢
                nlinarith
            · rw [abs_of_nonpos]
              · field_simp at h ⊢
                nlinarith
              · field_simp at h ⊢
                nlinarith
        rw [hset]
        calc
          μ.real ({ω | (m : ℝ) * a ≤ ∑ j : Fin m, Z j ω} ∪
              {ω | (m : ℝ) * a ≤ -(∑ j : Fin m, Z j ω)}) ≤
              μ.real {ω | (m : ℝ) * a ≤ ∑ j : Fin m, Z j ω} +
                μ.real {ω | (m : ℝ) * a ≤ -(∑ j : Fin m, Z j ω)} :=
            MeasureTheory.measureReal_union_le _ _
          _ ≤ Real.exp (-((m : ℝ) * a) ^ 2 /
                (2 * ((↑(∑ _j : Fin m, c) : ℝ)))) +
              Real.exp (-((m : ℝ) * a) ^ 2 /
                (2 * ((↑(∑ _j : Fin m, c) : ℝ)))) := by
            simpa only [Pi.neg_apply] using add_le_add hu hl
          _ = 2 * Real.exp (-2 * (m : ℝ) * a ^ 2) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            norm_num [c, hm]
            field_simp
            ring_nf
    have hn_ne_one : n ≠ 1 := by
      intro hn1
      subst n
      norm_num at hnδ
      linarith
    have hn_two : 2 ≤ n := by omega
    choose S hSmeas hSapprox using fun i j =>
      exists_tv_witness (H i) (H j) (ε / 2) (by positivity)
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hratio : 1 < (n : ℝ) / δ :=
      (lt_div_iff₀ hδ).2 (by simpa using (lt_of_lt_of_le hδ_one hnR))
    let sampleBase : ℝ := 64 * Real.log ((n : ℝ) / δ) / ε ^ 2
    let m : ℕ := ⌈sampleBase⌉₊
    have hbase_pos : 0 < sampleBase := by
      dsimp [sampleBase]
      exact div_pos (mul_pos (by norm_num) (Real.log_pos hratio)) (sq_pos_of_pos hε)
    have hmpos : 0 < m := by
      dsimp [m]
      exact Nat.ceil_pos.mpr hbase_pos
    have hbase_le_m : sampleBase ≤ (m : ℝ) := by
      dsimp [m]
      exact Nat.le_ceil sampleBase
    have hlogtwo_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hscaled_log : Real.log 2 ≤ Real.log ((n : ℝ) / δ) / ε ^ 2 := by
      have hlog : Real.log 2 ≤ Real.log ((n : ℝ) / δ) := by
        apply Real.log_le_log (by norm_num)
        have hnRtwo : (2 : ℝ) ≤ n := by exact_mod_cast hn_two
        have hnlt : (n : ℝ) < (n : ℝ) / δ := by
          apply (lt_div_iff₀ hδ).2
          nlinarith
        exact hnRtwo.trans hnlt.le
      have hεsq : ε ^ 2 ≤ 1 := by nlinarith [sq_nonneg ε]
      have hεsqpos : 0 < ε ^ 2 := sq_pos_of_pos hε
      apply (le_div_iff₀ hεsqpos).2
      nlinarith [Real.log_pos hratio]
    have hm_bound : (m : ℝ) ≤
        (64 + 1 / Real.log 2) * Real.log ((n : ℝ) / δ) / ε ^ 2 := by
      have hceil : (m : ℝ) < sampleBase + 1 := by
        dsimp [m]
        exact Nat.ceil_lt_add_one hbase_pos.le
      have hone : 1 ≤ Real.log ((n : ℝ) / δ) / ε ^ 2 / Real.log 2 :=
        (le_div_iff₀ hlogtwo_pos).2 (by simpa using hscaled_log)
      have hlogtwo_le_one : Real.log 2 ≤ 1 := by
        nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      dsimp [sampleBase] at hceil ⊢
      have hBpos : 0 < Real.log ((n : ℝ) / δ) / ε ^ 2 :=
        div_pos (Real.log_pos hratio) (sq_pos_of_pos hε)
      calc
        (m : ℝ) ≤ 64 * (Real.log ((n : ℝ) / δ) / ε ^ 2) + 1 := by
          have h := le_of_lt hceil
          rw [show 64 * Real.log ((n : ℝ) / δ) / ε ^ 2 =
            64 * (Real.log ((n : ℝ) / δ) / ε ^ 2) by ring] at h
          exact h
        _ ≤ (64 + 1 / Real.log 2) *
            (Real.log ((n : ℝ) / δ) / ε ^ 2) := by
          calc
            64 * (Real.log ((n : ℝ) / δ) / ε ^ 2) + 1 ≤
                64 * (Real.log ((n : ℝ) / δ) / ε ^ 2) +
                  Real.log ((n : ℝ) / δ) / ε ^ 2 / Real.log 2 :=
              by nlinarith
            _ = (64 + 1 / Real.log 2) *
                (Real.log ((n : ℝ) / δ) / ε ^ 2) := by ring
        _ = (64 + 1 / Real.log 2) * Real.log ((n : ℝ) / δ) / ε ^ 2 := by ring
    let empirical : (Fin m → X) → Set X → ℝ := fun ω s =>
      (∑ j : Fin m, s.indicator 1 (ω j)) / (m : ℝ)
    have hemp_meas : ∀ i j : Fin n,
        Measurable (fun ω : Fin m → X => empirical ω (S i j)) := by
      intro i j
      dsimp [empirical]
      apply Measurable.div_const
      exact Finset.measurable_sum _ fun k _ =>
        (measurable_const.indicator (hSmeas i j)).comp (measurable_pi_apply k)
    let first : Fin n := ⟨0, hn⟩
    have hpairs : (Finset.univ : Finset (Fin n × Fin n)).Nonempty :=
      ⟨(first, first), Finset.mem_univ _⟩
    let score : (Fin m → X) → Fin n → ℝ := fun ω i =>
      (Finset.univ : Finset (Fin n × Fin n)).sup'
        hpairs
        (fun p => |empirical ω (S p.1 p.2) - ((H i (S p.1 p.2) : NNReal) : ℝ)|)
    have hscore_meas : ∀ i : Fin n, Measurable (fun ω => score ω i) := by
      intro i
      have hs := Finset.measurable_sup' hpairs
        (f := fun p ω =>
          |empirical ω (S p.1 p.2) - ((H i (S p.1 p.2) : NNReal) : ℝ)|)
        (fun p hp => ((hemp_meas p.1 p.2).sub_const _).abs)
      rw [show (fun ω => score ω i) =
          (Finset.univ : Finset (Fin n × Fin n)).sup' hpairs
            (fun p ω => |empirical ω (S p.1 p.2) -
              ((H i (S p.1 p.2) : NNReal) : ℝ)|) by
        funext ω
        dsimp [score]
        exact (Finset.sup'_apply hpairs
          (fun p (ω : Fin m → X) => |empirical ω (S p.1 p.2) -
            ((H i (S p.1 p.2) : NNReal) : ℝ)|) ω).symm]
      exact hs
    have measurable_sample_argmin : ∀ (k : ℕ), 0 < k →
        ∀ (candidateScore : (Fin m → X) → Fin k → ℝ),
          (∀ i, Measurable (fun ω => candidateScore ω i)) →
            ∃ f : (Fin m → X) → Fin k,
              Measurable f ∧
                (∀ ω i, candidateScore ω (f ω) ≤ candidateScore ω i) ∧
                  Measurable (fun ω => candidateScore ω (f ω)) := by
      intro k
      induction k with
      | zero => intro hk; omega
      | succ k ih =>
          intro hk candidateScore hcand
          by_cases hkzero : k = 0
          · subst k
            let f : (Fin m → X) → Fin 1 := fun _ => 0
            refine ⟨f, measurable_const, ?_, ?_⟩
            · intro ω i
              fin_cases i
              exact le_rfl
            · simpa [f] using hcand 0
          · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
            obtain ⟨g, hg, hgmin, hgval⟩ :=
              ih hkpos (fun ω i => candidateScore ω i.succ) (fun i => hcand i.succ)
            let j : (Fin m → X) → Fin (k + 1) := fun ω => (g ω).succ
            have hj : Measurable j := by
              exact (measurable_of_finite (fun i : Fin k => i.succ)).comp hg
            have hjval : Measurable (fun ω => candidateScore ω (j ω)) := by
              simpa [j] using hgval
            let f : (Fin m → X) → Fin (k + 1) := fun ω =>
              if candidateScore ω 0 ≤ candidateScore ω (j ω) then 0 else j ω
            have hf : Measurable f := by
              exact Measurable.ite (measurableSet_le (hcand 0) hjval)
                measurable_const hj
            refine ⟨f, hf, ?_, ?_⟩
            · intro ω i
              refine Fin.cases ?_ (fun i => ?_) i
              · simp only [f]
                split_ifs with h
                · exact le_rfl
                · exact le_of_not_ge h
              · simp only [f]
                split_ifs with h
                · exact h.trans (hgmin ω i)
                · exact hgmin ω i
            · rw [show (fun ω => candidateScore ω (f ω)) = fun ω =>
                  if candidateScore ω 0 ≤ candidateScore ω (j ω) then
                    candidateScore ω 0 else candidateScore ω (j ω) by
                funext ω
                by_cases h : candidateScore ω 0 ≤ candidateScore ω (j ω) <;>
                  simp [f, h]]
              exact Measurable.ite (measurableSet_le (hcand 0) hjval)
                (hcand 0) hjval
    obtain ⟨selector, hselector_meas, hselector_min, hselector_score_meas⟩ :=
      measurable_sample_argmin n hn score hscore_meas
    let uniformEvent (P : MeasureTheory.ProbabilityMeasure X) : Set (Fin m → X) :=
      {ω | ∀ i j : Fin n,
        |empirical ω (S i j) - ((P (S i j) : NNReal) : ℝ)| < ε / 4}
    have huniform_meas : ∀ P : MeasureTheory.ProbabilityMeasure X,
        MeasurableSet (uniformEvent P) := by
      intro P
      dsimp [uniformEvent]
      rw [show {ω | ∀ i j : Fin n,
          |empirical ω (S i j) - ((P (S i j) : NNReal) : ℝ)| < ε / 4} =
          ⋂ i, ⋂ j, {ω | |empirical ω (S i j) -
            ((P (S i j) : NNReal) : ℝ)| < ε / 4} by
        ext ω
        simp]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
        measurableSet_lt ((hemp_meas i j).sub_const _).abs measurable_const
    letI : Nonempty (Fin n) := ⟨first⟩
    have selector_good : ∀ (P : MeasureTheory.ProbabilityMeasure X)
        (ω : Fin m → X), ω ∈ uniformEvent P →
          hypothesis_selection_total_variation_distance P (H (selector ω)) ≤
            3 * hypothesis_selection_optimum P H + ENNReal.ofReal ε := by
      intro P ω hω
      change ∀ i j : Fin n,
        |empirical ω (S i j) - ((P (S i j) : NNReal) : ℝ)| < ε / 4 at hω
      obtain ⟨best, hbest_mem, hbest⟩ :=
        (Finset.univ : Finset (Fin n)).exists_min_image
          (fun i => (hypothesis_selection_total_variation_distance P (H i)).toReal)
          Finset.univ_nonempty
      have htv_ne (i : Fin n) :
          hypothesis_selection_total_variation_distance P (H i) ≠ ⊤ :=
        ne_top_of_le_ne_top (by norm_num) (tv_le_one _ _)
      have hopt_le : hypothesis_selection_optimum P H ≤
          hypothesis_selection_total_variation_distance P (H best) := by
        exact iInf_le _ best
      have hopt_ne : hypothesis_selection_optimum P H ≠ ⊤ :=
        ne_top_of_le_ne_top (htv_ne best) hopt_le
      have hbest_eq : hypothesis_selection_total_variation_distance P (H best) =
          hypothesis_selection_optimum P H := by
        apply le_antisymm
        · apply le_iInf
          intro i
          exact (ENNReal.toReal_le_toReal (htv_ne best) (htv_ne i)).1
            (hbest i (Finset.mem_univ i))
        · exact hopt_le
      have hscore_best : score ω best ≤
          (hypothesis_selection_optimum P H).toReal + ε / 4 := by
        dsimp [score]
        apply Finset.sup'_le
        intro p hp
        calc
          |empirical ω (S p.1 p.2) - ((H best (S p.1 p.2) : NNReal) : ℝ)| ≤
              |empirical ω (S p.1 p.2) - ((P (S p.1 p.2) : NNReal) : ℝ)| +
                |((P (S p.1 p.2) : NNReal) : ℝ) -
                  ((H best (S p.1 p.2) : NNReal) : ℝ)| := by
            exact abs_sub_le _ _ _
          _ ≤ ε / 4 +
              (hypothesis_selection_total_variation_distance P (H best)).toReal := by
            exact add_le_add (hω p.1 p.2).le
              (measurable_gap_le_tv P (H best) (S p.1 p.2) (hSmeas _ _))
          _ = (hypothesis_selection_optimum P H).toReal + ε / 4 := by
            rw [hbest_eq]
            ring
      have hscore_selected : score ω (selector ω) ≤
          (hypothesis_selection_optimum P H).toReal + ε / 4 :=
        (hselector_min ω best).trans hscore_best
      let chosenPair : Fin n × Fin n := (selector ω, best)
      have hchosen_selected :
          |empirical ω (S chosenPair.1 chosenPair.2) -
              ((H (selector ω) (S chosenPair.1 chosenPair.2) : NNReal) : ℝ)| ≤
            score ω (selector ω) := by
        dsimp [score]
        exact Finset.le_sup' (f := fun p =>
          |empirical ω (S p.1 p.2) - ((H (selector ω) (S p.1 p.2) : NNReal) : ℝ)|)
          (Finset.mem_univ chosenPair)
      have hchosen_best :
          |empirical ω (S chosenPair.1 chosenPair.2) -
              ((H best (S chosenPair.1 chosenPair.2) : NNReal) : ℝ)| ≤ score ω best := by
        dsimp [score]
        exact Finset.le_sup' (f := fun p =>
          |empirical ω (S p.1 p.2) - ((H best (S p.1 p.2) : NNReal) : ℝ)|)
          (Finset.mem_univ chosenPair)
      have hpair_real :
          (hypothesis_selection_total_variation_distance
              (H (selector ω)) (H best)).toReal ≤
            2 * (hypothesis_selection_optimum P H).toReal + ε := by
        calc
          (hypothesis_selection_total_variation_distance
              (H (selector ω)) (H best)).toReal ≤
              |((H (selector ω) (S chosenPair.1 chosenPair.2) : NNReal) : ℝ) -
                ((H best (S chosenPair.1 chosenPair.2) : NNReal) : ℝ)| + ε / 2 := by
            simpa [chosenPair] using hSapprox (selector ω) best
          _ ≤ (score ω (selector ω) + score ω best) + ε / 2 := by
            have htriangle :
                |((H (selector ω) (S chosenPair.1 chosenPair.2) : NNReal) : ℝ) -
                    ((H best (S chosenPair.1 chosenPair.2) : NNReal) : ℝ)| ≤
                  |empirical ω (S chosenPair.1 chosenPair.2) -
                    ((H (selector ω) (S chosenPair.1 chosenPair.2) : NNReal) : ℝ)| +
                  |empirical ω (S chosenPair.1 chosenPair.2) -
                    ((H best (S chosenPair.1 chosenPair.2) : NNReal) : ℝ)| := by
              calc
                |((H (selector ω) (S chosenPair.1 chosenPair.2) : NNReal) : ℝ) -
                    ((H best (S chosenPair.1 chosenPair.2) : NNReal) : ℝ)| ≤
                    |((H (selector ω) (S chosenPair.1 chosenPair.2) : NNReal) : ℝ) -
                      empirical ω (S chosenPair.1 chosenPair.2)| +
                    |empirical ω (S chosenPair.1 chosenPair.2) -
                      ((H best (S chosenPair.1 chosenPair.2) : NNReal) : ℝ)| :=
                  abs_sub_le _ _ _
                _ = _ := by
                  rw [abs_sub_comm
                    (((H (selector ω) (S chosenPair.1 chosenPair.2) : NNReal) : ℝ))]
            linarith
          _ ≤ 2 * (hypothesis_selection_optimum P H).toReal + ε := by
            linarith
      have hpair_ne : hypothesis_selection_total_variation_distance
          (H (selector ω)) (H best) ≠ ⊤ :=
        ne_top_of_le_ne_top (by norm_num) (tv_le_one _ _)
      have htri := tv_triangle P (H best) (H (selector ω))
      have htri_real :
          (hypothesis_selection_total_variation_distance P (H (selector ω))).toReal ≤
            (hypothesis_selection_total_variation_distance P (H best)).toReal +
              (hypothesis_selection_total_variation_distance
                (H best) (H (selector ω))).toReal := by
        rw [← ENNReal.toReal_add (htv_ne best) (by
          exact ne_top_of_le_ne_top (by norm_num) (tv_le_one _ _))]
        exact ENNReal.toReal_mono (by
          exact ENNReal.add_ne_top.mpr ⟨htv_ne best,
            ne_top_of_le_ne_top (by norm_num) (tv_le_one _ _)⟩) htri
      have hpair_symm : hypothesis_selection_total_variation_distance
          (H best) (H (selector ω)) =
            hypothesis_selection_total_variation_distance (H (selector ω)) (H best) := by
        unfold hypothesis_selection_total_variation_distance
        congr with s
        congr with hs
        exact max_comm _ _
      rw [hpair_symm] at htri_real
      have hfinal_real :
          (hypothesis_selection_total_variation_distance P (H (selector ω))).toReal ≤
            3 * (hypothesis_selection_optimum P H).toReal + ε := by
        rw [hbest_eq] at htri_real
        linarith
      have hrhs_ne : 3 * hypothesis_selection_optimum P H + ENNReal.ofReal ε ≠ ⊤ := by
        exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) hopt_ne,
          ENNReal.ofReal_ne_top⟩
      apply (ENNReal.toReal_le_toReal
        (ne_top_of_le_ne_top (by norm_num) (tv_le_one _ _)) hrhs_ne).1
      rw [ENNReal.toReal_add (ENNReal.mul_ne_top (by norm_num) hopt_ne)
        ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hε.le]
      norm_num
      exact hfinal_real
    have huniform_prob : ∀ P : MeasureTheory.ProbabilityMeasure X,
        Real.toNNReal (1 - δ) ≤
          hypothesis_selection_sample_law P m (uniformEvent P) := by
      intro P
      let badEvent : Fin n × Fin n → Set (Fin m → X) := fun p =>
        {ω | ε / 4 ≤
          |empirical ω (S p.1 p.2) - ((P (S p.1 p.2) : NNReal) : ℝ)|}
      have hbad_eq : (uniformEvent P)ᶜ = ⋃ p, badEvent p := by
        ext ω
        simp [uniformEvent, badEvent, not_lt]
      have htail : 2 * Real.exp (-2 * (m : ℝ) * (ε / 4) ^ 2) ≤
          2 * Real.exp (-8 * Real.log ((n : ℝ) / δ)) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        have hbase : 64 * Real.log ((n : ℝ) / δ) / ε ^ 2 ≤ (m : ℝ) := by
          simpa [sampleBase] using hbase_le_m
        have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
        have hbase_mul : 64 * Real.log ((n : ℝ) / δ) ≤ (m : ℝ) * ε ^ 2 :=
          (div_le_iff₀ hεsq).1 hbase
        nlinarith
      have hexp : Real.exp (-8 * Real.log ((n : ℝ) / δ)) =
          (δ / (n : ℝ)) ^ 8 := by
        rw [show -8 * Real.log ((n : ℝ) / δ) =
            -(Real.log ((n : ℝ) / δ) * 8) by ring,
          Real.exp_neg]
        rw [mul_comm (Real.log ((n : ℝ) / δ)) 8]
        change (Real.exp (((8 : ℕ) : ℝ) * Real.log ((n : ℝ) / δ)))⁻¹ =
          (δ / (n : ℝ)) ^ 8
        rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
        field_simp
      have hδpow : δ ^ 8 ≤ δ := by
        calc
          δ ^ 8 = δ * δ ^ 7 := by ring
          _ ≤ δ * 1 := mul_le_mul_of_nonneg_left
            (pow_le_one₀ hδ.le hδ_one.le) hδ.le
          _ = δ := mul_one δ
      have hn6 : (2 : ℝ) ≤ (n : ℝ) ^ 6 := by
        have hnRtwo : (2 : ℝ) ≤ n := by exact_mod_cast hn_two
        nlinarith [sq_nonneg ((n : ℝ) ^ 2), mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 2) hnRtwo]
      have htotal_tail : (n : ℝ) ^ 2 *
          (2 * Real.exp (-2 * (m : ℝ) * (ε / 4) ^ 2)) ≤ δ := by
        calc
          (n : ℝ) ^ 2 * (2 * Real.exp (-2 * (m : ℝ) * (ε / 4) ^ 2)) ≤
              (n : ℝ) ^ 2 * (2 * Real.exp (-8 * Real.log ((n : ℝ) / δ))) :=
            mul_le_mul_of_nonneg_left htail (sq_nonneg _)
          _ = 2 * δ ^ 8 / (n : ℝ) ^ 6 := by
            rw [hexp]
            field_simp
          _ ≤ δ := by
            apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 6)).2
            calc
              2 * δ ^ 8 ≤ 2 * δ := mul_le_mul_of_nonneg_left hδpow (by norm_num)
              _ ≤ δ * (n : ℝ) ^ 6 := by
                simpa [mul_comm] using mul_le_mul_of_nonneg_left hn6 hδ.le
      have hbad_real :
          (hypothesis_selection_sample_law P m : MeasureTheory.Measure (Fin m → X)).real
              ((uniformEvent P)ᶜ) ≤ δ := by
        rw [hbad_eq]
        calc
          (hypothesis_selection_sample_law P m : MeasureTheory.Measure (Fin m → X)).real
              (⋃ p, badEvent p) ≤
              ∑ p : Fin n × Fin n,
                (hypothesis_selection_sample_law P m :
                  MeasureTheory.Measure (Fin m → X)).real (badEvent p) :=
            MeasureTheory.measureReal_iUnion_fintype_le _
          _ ≤ ∑ _p : Fin n × Fin n,
              2 * Real.exp (-2 * (m : ℝ) * (ε / 4) ^ 2) := by
            apply Finset.sum_le_sum
            intro p hp
            simpa [badEvent, empirical] using
              bernoulli_concentration P m (S p.1 p.2) (hSmeas _ _) (ε / 4) (by positivity)
          _ = (n : ℝ) ^ 2 *
              (2 * Real.exp (-2 * (m : ℝ) * (ε / 4) ^ 2)) := by
            simp [Fintype.card_prod]
            ring
          _ ≤ δ := htotal_tail
      have hgood_real : 1 - δ ≤
          (hypothesis_selection_sample_law P m : MeasureTheory.Measure (Fin m → X)).real
            (uniformEvent P) := by
        have hcomp := MeasureTheory.measureReal_compl (μ :=
          (hypothesis_selection_sample_law P m : MeasureTheory.Measure (Fin m → X)))
          (huniform_meas P)
        rw [MeasureTheory.measureReal_univ_eq_one] at hcomp
        linarith
      rw [← NNReal.coe_le_coe]
      simpa [Real.coe_toNNReal (1 - δ) (sub_nonneg.mpr hδ_one.le)] using hgood_real
    let defaultPoint : X := Classical.choice (H first).nonempty
    let C : hypothesis_selection_computation X n m :=
      { State := List (Fin m) × (Fin m → X)
        initialState := (List.ofFn id, fun _ => defaultPoint)
        instruction := fun state answer =>
          match state, answer with
          | ([], buffer), _ => .output (selector buffer)
          | (j :: js, buffer), .empty => .targetSample j (j :: js, buffer)
          | (j :: js, buffer), .targetSample x =>
              .step (js, Function.update buffer j x)
          | (_, _), _ => .output first }
    have fold_update_apply : ∀ (ω : Fin m → X) (js : List (Fin m))
        (buffer : Fin m → X) (j : Fin m),
        (js.foldl (fun b k => Function.update b k (ω k)) buffer) j =
          if j ∈ js then ω j else buffer j := by
      intro ω js
      induction js with
      | nil => simp
      | cons k js ih =>
          intro buffer j
          simp only [List.foldl_cons, ih]
          by_cases hj : j ∈ js <;> by_cases hjk : j = k <;>
            simp [hj, hjk]
    have filled_eq : ∀ (ω : Fin m → X),
        (List.ofFn id).foldl
            (fun b j => Function.update b j (ω j)) (fun _ => defaultPoint) = ω := by
      intro ω
      funext j
      rw [fold_update_apply]
      simp
    have evaluate_loop : ∀ (ω : Fin m → X) (r : O.Randomness)
        (js : List (Fin m)) (buffer : Fin m → X),
        hypothesis_selection_computation_evaluate O ω r C
            (2 * js.length + 1) (js, buffer) .empty =
          some (selector (js.foldl
            (fun b j => Function.update b j (ω j)) buffer)) := by
      intro ω r js
      induction js with
      | nil =>
          intro buffer
          simp [C, hypothesis_selection_computation_evaluate]
      | cons j js ih =>
          intro buffer
          rw [show 2 * (j :: js).length + 1 = (2 * js.length + 1) + 2 by
            simp
            omega]
          change hypothesis_selection_computation_evaluate O ω r C
              (2 * js.length + 1) (js, Function.update buffer j (ω j)) .empty =
            some (selector (js.foldl
              (fun b k => Function.update b k (ω k))
              (Function.update buffer j (ω j))))
          exact ih (Function.update buffer j (ω j))
    have evaluate_unique : ∀ (ω : Fin m → X) (r : O.Randomness)
        (js : List (Fin m)) (buffer : Fin m → X) (fuel : ℕ) (i : Fin n),
        hypothesis_selection_computation_evaluate O ω r C fuel
            (js, buffer) .empty = some i →
          i = selector (js.foldl
            (fun b j => Function.update b j (ω j)) buffer) := by
      intro ω r js
      induction js with
      | nil =>
          intro buffer fuel i h
          cases fuel with
          | zero => simp [hypothesis_selection_computation_evaluate] at h
          | succ fuel =>
              simp [C, hypothesis_selection_computation_evaluate] at h
              exact h.symm
      | cons j js ih =>
          intro buffer fuel i h
          cases fuel with
          | zero => simp [hypothesis_selection_computation_evaluate] at h
          | succ fuel =>
              cases fuel with
              | zero => simp [C, hypothesis_selection_computation_evaluate] at h
              | succ fuel =>
                  have h' : hypothesis_selection_computation_evaluate O ω r C fuel
                      (js, Function.update buffer j (ω j)) .empty = some i := by
                    simpa [C, hypothesis_selection_computation_evaluate] using h
                  simpa only [List.foldl_cons] using
                    ih (Function.update buffer j (ω j)) fuel i h'
    let A : hypothesis_selection_algorithm X n H O :=
      { sampleCount := m
        program := C
        halts := by
          intro ω r
          refine ⟨2 * m + 1, selector ω, ?_⟩
          simpa [C, filled_eq ω] using
            evaluate_loop ω r (List.ofFn id) (fun _ => defaultPoint) }
    have selected_eq : ∀ (ω : Fin m → X) (r : O.Randomness),
        hypothesis_selection_selected_index A ω r = selector ω := by
      intro ω r
      unfold hypothesis_selection_selected_index
      have hrun := Classical.choose_spec (Nat.find_spec (A.halts ω r))
      have hu := evaluate_unique ω r (List.ofFn id) (fun _ => defaultPoint)
        (Nat.find (A.halts ω r))
        (Classical.choose (Nat.find_spec (A.halts ω r))) (by
          simpa [A, C] using hrun)
      simpa [filled_eq ω] using hu
    have cost_le : ∀ (ω : Fin m → X) (r : O.Randomness),
        hypothesis_selection_execution_cost A ω r ≤ 2 * m + 1 := by
      intro ω r
      unfold hypothesis_selection_execution_cost
      unfold hypothesis_selection_computation_cost
      apply Nat.find_le
      refine ⟨selector ω, ?_⟩
      simpa [A, C, filled_eq ω] using
        evaluate_loop ω r (List.ofFn id) (fun _ => defaultPoint)
    let q : ℝ := (n : ℝ) / (ε ^ 2 * δ)
    have hq_pos : 0 < q := by
      dsimp [q]
      positivity
    have hεsq_le_one : ε ^ 2 ≤ 1 := by nlinarith [sq_nonneg ε]
    have hdenom_le_one : ε ^ 2 * δ ≤ 1 :=
      mul_le_one₀ hεsq_le_one hδ.le hδ_one.le
    have hq_one : 1 ≤ q := by
      apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hε) hδ)).2
      simpa only [one_mul] using hdenom_le_one.trans hnR
    have hlog_le_ratio : Real.log ((n : ℝ) / δ) ≤ (n : ℝ) / δ := by
      have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (n : ℝ) / δ)
      linarith
    have hbase_q : sampleBase ≤ 64 * q := by
      calc
        sampleBase = 64 * Real.log ((n : ℝ) / δ) / ε ^ 2 := rfl
        _ ≤ 64 * ((n : ℝ) / δ) / ε ^ 2 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlog_le_ratio (by norm_num))
            (sq_nonneg ε)
        _ = 64 * q := by
          dsimp [q]
          field_simp
    have hm_q : (m : ℝ) ≤ 65 * q := by
      have hm_lt : (m : ℝ) < sampleBase + 1 := by
        dsimp [m]
        exact Nat.ceil_lt_add_one hbase_pos.le
      calc
        (m : ℝ) ≤ sampleBase + 1 := hm_lt.le
        _ ≤ 64 * q + q := add_le_add hbase_q hq_one
        _ = 65 * q := by ring
    refine ⟨A, ?_, ?_⟩
    · constructor
      · change (m : ℝ) ≤
          (64 + 1 / Real.log 2) * Real.log ((n : ℝ) / δ) / ε ^ 2
        exact hm_bound
      · intro ω r
        change (hypothesis_selection_execution_cost A ω r : ℝ) ≤
          1024 * max 1 q * Real.log (max 2 q) ^ 0
        rw [pow_zero, mul_one]
        have hcost_real : (hypothesis_selection_execution_cost A ω r : ℝ) ≤
            2 * (m : ℝ) + 1 := by
          exact_mod_cast cost_le ω r
        have hq_max : q ≤ max 1 q := le_max_right _ _
        calc
          (hypothesis_selection_execution_cost A ω r : ℝ) ≤
              2 * (m : ℝ) + 1 := hcost_real
          _ ≤ 131 * q := by nlinarith
          _ ≤ 1024 * max 1 q := by nlinarith
    · intro P
      letI : MeasurableSpace O.Randomness := O.randomnessMeasurable
      unfold hypothesis_selection_guarantee
      let goodBase : Set (Fin m → X) :=
        {ω | hypothesis_selection_total_variation_distance P (H (selector ω)) ≤
          3 * hypothesis_selection_optimum P H + ENNReal.ofReal ε}
      have hgoodBase_meas : MeasurableSet goodBase := by
        change MeasurableSet (selector ⁻¹'
          {i : Fin n | hypothesis_selection_total_variation_distance P (H i) ≤
            3 * hypothesis_selection_optimum P H + ENNReal.ofReal ε})
        apply hselector_meas
        exact Set.toFinite
          {i : Fin n | hypothesis_selection_total_variation_distance P (H i) ≤
            3 * hypothesis_selection_optimum P H + ENNReal.ofReal ε} |>.measurableSet
      have hgood_eq : hypothesis_selection_good_sample_set P H ε O A =
          goodBase ×ˢ (Set.univ : Set O.Randomness) := by
        ext outcome
        simp [hypothesis_selection_good_sample_set, goodBase, A, selected_eq]
      constructor
      · rw [hgood_eq]
        exact hgoodBase_meas.prod MeasurableSet.univ
      · calc
          Real.toNNReal (1 - δ) ≤
              hypothesis_selection_sample_law P m (uniformEvent P) := huniform_prob P
          _ ≤ hypothesis_selection_sample_law P m goodBase := by
            change hypothesis_selection_sample_law P m (uniformEvent P) ≤
              hypothesis_selection_sample_law P m
                {ω | hypothesis_selection_total_variation_distance P (H (selector ω)) ≤
                  3 * hypothesis_selection_optimum P H + ENNReal.ofReal ε}
            exact MeasureTheory.ProbabilityMeasure.apply_mono _
              (fun ω hω => selector_good P ω hω)
          _ = (hypothesis_selection_sample_law P A.sampleCount).prod
              O.randomnessLaw (hypothesis_selection_good_sample_set P H ε O A) := by
            rw [hgood_eq]
            simp [A, hgoodBase_meas]

@[blueprint "thm:fast"
  (statement := /-- For every integer $n\geq 1$, every family of $n$ known probability distributions, every additive error $\varepsilon>0$, and every failure probability $\delta\in(0,1)$ with $\delta>1/n$, there exists a proper hypothesis-selection algorithm which uses $O(\log(n/\delta)/\varepsilon^2)$ samples, returns a hypothesis at total-variation distance at most $3\operatorname{OPT}+\varepsilon$ from the unknown target with probability at least $1-\delta$, and runs in time $\widetilde{O}(n/(\varepsilon^2\delta))$. -/)
  (proof := /-- Apply \cref{lem:fast-hypothesis-selector-construction}, whose conclusion is exactly the uniform assertion encoded by the present theorem. -/)
  (title := /-- Fast proper hypothesis selection with optimal factor three -/)
  (latexEnv := "theorem")]
theorem fast : hypothesis_selection_fast_statement := by
  exact fast_hypothesis_selector_construction

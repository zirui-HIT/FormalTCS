import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.SubGaussian

set_option linter.all false
set_option maxHeartbeats 500000

universe u

noncomputable def hypothesis_selection_total_variation_distance
    {X : Type u} [MeasurableSpace X]
    (P Q : MeasureTheory.ProbabilityMeasure X) : ENNReal :=
  ⨆ (s : Set X) (_hs : MeasurableSet s),
    max ((P s : NNReal) - (Q s : NNReal) : ENNReal)
      ((Q s : NNReal) - (P s : NNReal) : ENNReal)

noncomputable def hypothesis_selection_optimum
    {X : Type u} [MeasurableSpace X] {n : ℕ}
    (P : MeasureTheory.ProbabilityMeasure X)
    (H : Fin n → MeasureTheory.ProbabilityMeasure X) : ENNReal :=
  ⨅ i : Fin n, hypothesis_selection_total_variation_distance P (H i)

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

inductive hypothesis_selection_oracle_answer (X : Type u) : Type u where
  | empty : hypothesis_selection_oracle_answer X
  | targetSample (x : X) : hypothesis_selection_oracle_answer X
  | hypothesisSample (x : X) : hypothesis_selection_oracle_answer X
  | hypothesisPdf (q : ENNReal) : hypothesis_selection_oracle_answer X

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

structure hypothesis_selection_computation
    (X : Type u) (n sampleCount : ℕ) : Type (u + 1) where
  State : Type u
  initialState : State
  instruction :
    State → hypothesis_selection_oracle_answer X →
      hypothesis_selection_machine_instruction X n sampleCount State

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

noncomputable def hypothesis_selection_selected_index
    {X : Type u} [MeasurableSpace X] {n : ℕ}
    {H : Fin n → MeasureTheory.ProbabilityMeasure X}
    {O : hypothesis_selection_hypothesis_oracle X n H}
    (A : hypothesis_selection_algorithm X n H O)
    (ω : Fin A.sampleCount → X) (r : O.Randomness) : Fin n :=
  Classical.choose (Nat.find_spec (A.halts ω r))

noncomputable def hypothesis_selection_execution_cost
    {X : Type u} [MeasurableSpace X] {n : ℕ}
    {H : Fin n → MeasureTheory.ProbabilityMeasure X}
    {O : hypothesis_selection_hypothesis_oracle X n H}
    (A : hypothesis_selection_algorithm X n H O)
    (ω : Fin A.sampleCount → X) (r : O.Randomness) : ℕ :=
  hypothesis_selection_computation_cost O ω r A.program (A.halts ω r)

noncomputable def hypothesis_selection_sample_law
    {X : Type u} [MeasurableSpace X]
    (P : MeasureTheory.ProbabilityMeasure X) (m : ℕ) :
    MeasureTheory.ProbabilityMeasure (Fin m → X) :=
  MeasureTheory.ProbabilityMeasure.pi (fun _ : Fin m ↦ P)

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

theorem fast : hypothesis_selection_fast_statement := by sorry

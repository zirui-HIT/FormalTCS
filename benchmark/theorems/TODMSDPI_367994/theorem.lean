import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Independence.Conditional

set_option linter.all false
set_option maxHeartbeats 500000

open MeasureTheory

noncomputable def mutual_information
    {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure Ω) (U : Ω → S) (V : Ω → T) : ENNReal :=
  (InformationTheory.klDiv
    (Measure.map (fun ω => (U ω, V ω)) μ)
    ((Measure.map U μ).prod (Measure.map V μ)))

noncomputable def conditional_mutual_information
    {Ω S T R : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [MeasurableSpace T] [StandardBorelSpace T] [Nonempty T]
    [MeasurableSpace R]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Ω → S) (V : Ω → T) (W : Ω → R) : ENNReal :=
  InformationTheory.klDiv
    (Measure.map (fun ω => ((U ω, W ω), V ω)) μ)
    ((Measure.map (fun ω => (U ω, W ω)) μ).compProd
      (ProbabilityTheory.Kernel.prodMkLeft S
        (ProbabilityTheory.condDistrib V W μ)))

noncomputable def total_variation_distance
    {S : Type*} [MeasurableSpace S] (ν ξ : Measure S) : ℝ :=
  sSup {r : ℝ | ∃ E : Set S, MeasurableSet E ∧
    r = |(ν E).toReal - (ξ E).toReal|}

def strong_data_processing_inequality
    {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Ω → S) (B : Ω → T) (ρ : ℝ) : Prop :=
  Measurable A ∧ Measurable B ∧ 0 ≤ ρ ∧ ρ ≤ 1 ∧
      ∀ (N : Type) [MeasurableSpace N]
        (K : ProbabilityTheory.Kernel T N)
        [ProbabilityTheory.IsMarkovKernel K] (hB : Measurable B),
        let ν := μ.compProd (ProbabilityTheory.Kernel.comap K B hB)
        mutual_information ν Prod.snd (fun ωz => A ωz.1) ≤
          ENNReal.ofReal ρ *
            mutual_information ν Prod.snd (fun ωz => B ωz.1)

noncomputable def approximate_strong_data_processing_inequality
    {Ω S T : Type*} [MeasurableSpace Ω] [TopologicalSpace S]
    [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S] [T2Space S]
    [MeasurableSpace T] [StandardBorelSpace T] [Nonempty T]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → S) (B : Ω → T) (ρ δ : ℝ) : Prop :=
  Measurable A ∧ Measurable B ∧ 0 ≤ δ ∧ δ ≤ 1 ∧
    ∃ (κ : Measure ((S × T) × T)) (hκ : IsProbabilityMeasure κ),
      letI : IsProbabilityMeasure κ := hκ
      Measure.map Prod.fst κ =
          Measure.map (fun ω => (A ω, B ω)) μ ∧
        strong_data_processing_inequality κ
          (fun z => z.1.1) Prod.snd ρ ∧
        ∀ a ∈ (Measure.map (fun z => z.1.1) κ).support,
          total_variation_distance
            (ProbabilityTheory.condDistrib Prod.snd (fun z => z.1.1) κ a)
            (ProbabilityTheory.condDistrib (fun z => z.1.2)
              (fun z => z.1.1) κ a) ≤ δ

noncomputable def information_error_penalty (M : Type*) (η : ℝ) : EReal :=
  letI : Decidable (Finite M) := Classical.propDecidable (Finite M)
  if η = 0 then 0
  else if Finite M then
    ((8 * η * Real.log ((Nat.card M : ℝ) / η) : ℝ) : EReal)
  else ⊤

noncomputable def learning_problem_sampling_law
    {Ω Θ X : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace X]
    (n : ℕ) (μ : Measure Ω) (Ψ : Measure Θ)
    (P : ProbabilityTheory.Kernel Θ X)
    (parameter : Ω → Θ) (training : Ω → Fin n → X) (test : Ω → X) : Prop :=
  IsProbabilityMeasure Ψ ∧ ProbabilityTheory.IsMarkovKernel P ∧
    Measurable parameter ∧ Measurable training ∧ Measurable test ∧
      ∀ (A : Set Θ) (B : Fin n → Set X) (C : Set X),
        MeasurableSet A → (∀ i, MeasurableSet (B i)) → MeasurableSet C →
          μ {ω |
              parameter ω ∈ A ∧
                (∀ i, training ω i ∈ B i) ∧ test ω ∈ C} =
            ∫⁻ θ in A, (∏ i, P θ (B i)) * P θ C ∂Ψ

structure learning_algorithm
    (Train M : Type*) [MeasurableSpace Train] [MeasurableSpace M] where
  kernel : ProbabilityTheory.Kernel Train M
  markov : ProbabilityTheory.IsMarkovKernel kernel

noncomputable def learning_algorithm_joint_measure
    {Ω Train M : Type*} [MeasurableSpace Ω] [MeasurableSpace Train]
    [MeasurableSpace M]
    (μ : Measure Ω) (training : Ω → Train) (hTraining : Measurable training)
    (algorithm : learning_algorithm Train M) : Measure (Ω × M) :=
  μ.compProd (ProbabilityTheory.Kernel.comap algorithm.kernel training hTraining)

noncomputable def classification_error
    {Ω X M : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace M]
    (μ : Measure Ω) (output : Ω → M) (test : Ω → X)
    (predict : M → X → Bool) : ℝ :=
  ((μ {ω | predict (output ω) (test ω) = false}).toReal +
    (((Measure.map output μ).prod (Measure.map test μ))
      {pair | predict pair.1 pair.2 = true}).toReal) / 2

noncomputable def excess_memorization
    {Ω Θ Train M : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MeasurableSpace Train] [StandardBorelSpace Train]
    [Nonempty Train] [MeasurableSpace M]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (parameter : Ω → Θ) (training : Ω → Train)
    (hTraining : Measurable training)
    (algorithm : learning_algorithm Train M) : ENNReal :=
  letI : ProbabilityTheory.IsMarkovKernel algorithm.kernel := algorithm.markov
  let κ := ProbabilityTheory.Kernel.comap algorithm.kernel training hTraining
  letI : ProbabilityTheory.IsMarkovKernel κ := inferInstance
  letI : ProbabilityTheory.IsFiniteKernel κ := inferInstance
  let ν := μ.compProd κ
  letI : IsFiniteMeasure ν := inferInstance
  conditional_mutual_information ν Prod.snd
    (fun ωz => training ωz.1) (fun ωz => parameter ωz.1)

noncomputable def excess_memorization_correction
    (M : Type*) (τ ε ρ δ : ℝ) : EReal :=
  (((1 - τ) / ρ : ℝ) : EReal) * information_error_penalty M δ +
    information_error_penalty M ε

noncomputable def classification_capacity_constant (α : ℝ) : EReal :=
  if α ≤ 0 then ⊤
  else ((((1 - 2 * α) * Real.log ((1 - α) / α) : ℝ) : EReal))

noncomputable def minimal_necessary_memorization
    {Ω Θ X Train M : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MeasurableSpace X] [MeasurableSpace Train] [StandardBorelSpace Train]
    [Nonempty Train] [MeasurableSpace M]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (parameter : Ω → Θ) (training : Ω → Train)
    (test : Ω → X) (hTraining : Measurable training) (hTest : Measurable test)
    (predict : M → X → Bool)
    (hPredict : Measurable (fun pair : M × X => predict pair.1 pair.2))
    (α : ℝ) : EReal :=
  ⨅ algorithm : learning_algorithm Train M,
    let ν := learning_algorithm_joint_measure μ training hTraining algorithm
    if classification_error ν Prod.snd (fun ωz => test ωz.1) predict ≤ α then
      (excess_memorization μ parameter training hTraining algorithm : EReal)
    else ⊤

theorem minimal_necessary_memorization_lower_bound
    {Ω Θ X : Type*} {M : Type} (n : ℕ) [MeasurableSpace Ω] [TopologicalSpace Θ]
    [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ] [T2Space Θ]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [T2Space X] [Nonempty X]
    [StandardBorelSpace (Fin n → X)] [MeasurableSpace M]
    [MeasurableSingletonClass M]
    [MeasurableSpace.CountablyGenerated M]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Ψ : Measure Θ) (P : ProbabilityTheory.Kernel Θ X)
    (parameter : Ω → Θ) (training : Ω → Fin n → X) (test : Ω → X)
    (hSampling : learning_problem_sampling_law
      n μ Ψ P parameter training test)
    (predict : M → X → Bool)
    (hPredict : Measurable (fun pair : M × X => predict pair.1 pair.2))
    (τ ε ρ δ α : ℝ)
    (hData : approximate_strong_data_processing_inequality
      μ parameter training τ ε)
    (hTest : approximate_strong_data_processing_inequality
      μ test training ρ δ)
    (hρ : 0 < ρ)
    (hα : α < 1 / 2) :
    minimal_necessary_memorization (M := M) μ parameter training test
        hData.2.1 hTest.1 predict hPredict α ≥
      (((1 - τ) / ρ : ℝ) : EReal) *
        classification_capacity_constant α -
        excess_memorization_correction M τ ε ρ δ := by sorry

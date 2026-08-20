import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Set.Countable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Filter.AtTopBot.Defs

set_option linter.all false
set_option maxHeartbeats 500000

abbrev language := Set String

abbrev input_stream := ℕ → String

def observed_prefix (input : input_stream) (n : ℕ) : language :=
  Set.range (fun i : Fin n ↦ input i)

def stream_enumerates_language (input : input_stream) (target : language) : Prop :=
  Set.range input = target

structure generated_language_stream where
  at_time : ℕ → language

instance generated_language_stream_measurable_space :
    MeasurableSpace generated_language_stream :=
  ⊤

structure continual_language_generator where
  law : input_stream → MeasureTheory.Measure generated_language_stream
  is_probability : ∀ input, MeasureTheory.IsProbabilityMeasure (law input)

def agree_through {α : Type*} (n : ℕ) (left right : ℕ → α) : Prop :=
  ∀ i, i ≤ n → left i = right i

def input_prefix_agreement {α : Type*} (n : ℕ) (left right : ℕ → α) : Prop :=
  ∀ i, i < n → left i = right i

def output_prefix_event (n : ℕ) (event : Set generated_language_stream) : Prop :=
  ∀ left right,
    agree_through n left.at_time right.at_time →
      (left ∈ event ↔ right ∈ event)

def continual_generator_causal (generator : continual_language_generator) : Prop :=
  ∀ n input input',
    input_prefix_agreement n input input' →
      ∀ event,
        output_prefix_event n event →
          generator.law input event = generator.law input' event

def neighboring_streams (left right : input_stream) : Prop :=
  ∃ i, left i ≠ right i ∧ ∀ j, j ≠ i → left j = right j

def pure_stream_differential_privacy
    (ε : ℝ) (generator : continual_language_generator) : Prop :=
  ∀ input input',
    neighboring_streams input input' →
      ∀ event,
        MeasurableSet event →
          generator.law input event ≤
            ENNReal.ofReal (Real.exp ε) * generator.law input' event

def continual_release_private
    (ε : ℝ) (generator : continual_language_generator) : Prop :=
  continual_generator_causal generator ∧
    pure_stream_differential_privacy ε generator

def generates_language_in_limit
    (generator : continual_language_generator) (target : language) : Prop :=
  ∀ input,
    stream_enumerates_language input target →
      generator.law input
          {output |
            ∀ᶠ n in Filter.atTop,
              output.at_time n ⊆ target \ observed_prefix input n} =
        1

def generates_collection_in_limit
    (generator : continual_language_generator) (collection : Set language) : Prop :=
  ∀ target ∈ collection, generates_language_in_limit generator target

theorem private_online_generation
    (ε : ℝ) (hε : 0 < ε) :
    ∃ generator : continual_language_generator,
      ∀ collection : Set language, collection.Countable →
        continual_release_private ε generator ∧
          generates_collection_in_limit generator collection := by sorry

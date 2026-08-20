import Architect
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Set.Countable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Filter.AtTopBot.Defs

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:language"
  (statement := /-- A language is a set of finite strings. -/)
  (title := /-- Languages -/)
  (latexEnv := "definition")]
abbrev language := Set String

@[blueprint "def:input-stream"
  (statement := /-- An input stream is a sequence $x=(x_n)_{n\in\mathbb N}$ of finite strings. -/)
  (title := /-- Input streams -/)
  (latexEnv := "definition")]
abbrev input_stream := ℕ → String

@[blueprint "def:observed-prefix"
  (statement := /-- For an input stream $x$ and $n\in\mathbb N$, the observed prefix is the set
  $S_n(x)=\{x_i:0\leq i<n\}$ of strings occurring among the first $n$ entries. -/)
  (title := /-- Observed prefixes -/)
  (latexEnv := "definition")]
def observed_prefix (input : input_stream) (n : ℕ) : language :=
  Set.range (fun i : Fin n ↦ input i)

@[blueprint "def:stream-enumerates-language"
  (statement := /-- An input stream $x$ enumerates a language $K$ if every term of $x$ belongs to
  $K$ and every element of $K$ occurs as a term of $x$, equivalently if
  $\operatorname{range}(x)=K$. Repetitions are permitted. -/)
  (title := /-- Enumerations of a language -/)
  (latexEnv := "definition")]
def stream_enumerates_language (input : input_stream) (target : language) : Prop :=
  Set.range input = target

@[blueprint "def:generated-language-stream"
  (statement := /-- A generated-language stream is a sequence $U=(U_n)_{n\in\mathbb N}$ of
  languages, where $U_n$ is the set released at time $n$. -/)
  (title := /-- Streams of generated languages -/)
  (latexEnv := "definition")]
structure generated_language_stream where
  at_time : ℕ → language

@[blueprint "def:generated-language-stream-measurable-space"
  (statement := /-- The space of generated-language streams is equipped with the discrete
  measurable structure, so every event of output streams is measurable. -/)
  (title := /-- Measurable output-stream space -/)
  (latexEnv := "definition")]
instance generated_language_stream_measurable_space :
    MeasurableSpace generated_language_stream :=
  ⊤

@[blueprint "def:continual-language-generator"
  (statement := /-- A randomized continual language generator assigns to each input stream $x$ a
  probability measure on complete generated-language streams. Thus all releases are represented
  jointly, including their dependence across time. -/)
  (title := /-- Randomized continual language generators -/)
  (latexEnv := "definition")]
structure continual_language_generator where
  law : input_stream → MeasureTheory.Measure generated_language_stream
  is_probability : ∀ input, MeasureTheory.IsProbabilityMeasure (law input)

@[blueprint "def:agree-through"
  (statement := /-- Two sequences $x,y:\mathbb N\to A$ agree through time $n$ if
  $x_i=y_i$ for every $i\leq n$. -/)
  (title := /-- Agreement through a finite time -/)
  (latexEnv := "definition")]
def agree_through {α : Type*} (n : ℕ) (left right : ℕ → α) : Prop :=
  ∀ i, i ≤ n → left i = right i

@[blueprint "def:input-prefix-agreement"
  (statement := /-- Two sequences $x,y:\mathbb N\to A$ agree on the input prefix of length $n$ if
  $x_i=y_i$ for every $i<n$. -/)
  (title := /-- Agreement on an observed input prefix -/)
  (latexEnv := "definition")]
def input_prefix_agreement {α : Type*} (n : ℕ) (left right : ℕ → α) : Prop :=
  ∀ i, i < n → left i = right i

@[blueprint "def:output-prefix-event"
  (statement := /-- An event $E$ of generated-language streams is determined through time $n$ if
  membership in $E$ depends only on the releases with indices at most $n$. -/)
  (title := /-- Output-prefix events -/)
  (latexEnv := "definition")]
def output_prefix_event (n : ℕ) (event : Set generated_language_stream) : Prop :=
  ∀ left right,
    agree_through n left.at_time right.at_time →
      (left ∈ event ↔ right ∈ event)

@[blueprint "def:continual-generator-causal"
  (statement := /-- A randomized generator is causal if, for every $n\in\mathbb N$, any two input
  streams that agree at every index $i<n$ induce the same probability for every output event
  determined by the releases with indices at most $n$. Thus the release at time $n$ depends only
  on the observed input prefix of length $n$. -/)
  (title := /-- Causality in the continual-release model -/)
  (latexEnv := "definition")]
def continual_generator_causal (generator : continual_language_generator) : Prop :=
  ∀ n input input',
    input_prefix_agreement n input input' →
      ∀ event,
        output_prefix_event n event →
          generator.law input event = generator.law input' event

@[blueprint "def:neighboring-streams"
  (statement := /-- Two input streams are neighboring if there is exactly one time at which their
  entries differ. -/)
  (title := /-- Neighboring input streams -/)
  (latexEnv := "definition")]
def neighboring_streams (left right : input_stream) : Prop :=
  ∃ i, left i ≠ right i ∧ ∀ j, j ≠ i → left j = right j

@[blueprint "def:pure-stream-differential-privacy"
  (statement := /-- Let $\varepsilon\in\mathbb R$. A generator $G$ is purely
  $\varepsilon$-differentially private on streams if, for every ordered pair of neighboring input
  streams $x,x'$ and every measurable output event $E$,
  \[
    \Pr[G(x)\in E]\leq e^\varepsilon\Pr[G(x')\in E].
  \] -/)
  (title := /-- Pure differential privacy for output streams -/)
  (latexEnv := "definition")]
def pure_stream_differential_privacy
    (ε : ℝ) (generator : continual_language_generator) : Prop :=
  ∀ input input',
    neighboring_streams input input' →
      ∀ event,
        MeasurableSet event →
          generator.law input event ≤
            ENNReal.ofReal (Real.exp ε) * generator.law input' event

@[blueprint "def:continual-release-private"
  (statement := /-- A generator is $\varepsilon$-differentially private in the continual-release
  model if it is causal and its joint law on the entire output stream is purely
  $\varepsilon$-differentially private. -/)
  (title := /-- Differential privacy under continual release -/)
  (latexEnv := "definition")]
def continual_release_private
    (ε : ℝ) (generator : continual_language_generator) : Prop :=
  continual_generator_causal generator ∧
    pure_stream_differential_privacy ε generator

@[blueprint "def:generates-language-in-limit"
  (statement := /-- A randomized generator $G$ generates a language $K$ in the limit if, for
  every enumeration $x$ of $K$, with probability one there is a time after which every released
  set $U_n$ consists entirely of elements of $K$ not appearing among the first $n$ inputs:
  \[
    \Pr\!\left[\exists n^\star\ \forall n\geq n^\star,\;
      U_n\subseteq K\setminus S_n(x)\right]=1.
  \] -/)
  (title := /-- Generation from one language in the limit -/)
  (latexEnv := "definition")]
def generates_language_in_limit
    (generator : continual_language_generator) (target : language) : Prop :=
  ∀ input,
    stream_enumerates_language input target →
      generator.law input
          {output |
            ∀ᶠ n in Filter.atTop,
              output.at_time n ⊆ target \ observed_prefix input n} =
        1

@[blueprint "def:generates-collection-in-limit"
  (statement := /-- A randomized generator generates in the limit from a collection
  $\mathcal L$ if it generates every language $K\in\mathcal L$ in the sense of
  \cref{def:generates-language-in-limit}. -/)
  (title := /-- Generation from a collection in the limit -/)
  (latexEnv := "definition")]
def generates_collection_in_limit
    (generator : continual_language_generator) (collection : Set language) : Prop :=
  ∀ target ∈ collection, generates_language_in_limit generator target

@[blueprint "def:private-generation-guarantee"
  (statement := /-- For $\varepsilon\in\mathbb R$ and a collection of languages $\mathcal L$, a
  generator has the private-generation guarantee if it is $\varepsilon$-differentially private
  in the continual-release model and generates in the limit from $\mathcal L$. -/)
  (title := /-- The private-generation guarantee -/)
  (latexEnv := "definition")]
def private_generation_guarantee
    (ε : ℝ) (collection : Set language) (generator : continual_language_generator) : Prop :=
  continual_release_private ε generator ∧
    generates_collection_in_limit generator collection

@[blueprint "lem:approximate-intersection-algorithm-guarantee"
  (statement := /-- For every $\varepsilon>0$, there exists a randomized continual language
  generator $G$ such that, for every countable collection of languages $\mathcal L$, the
  generator $G$ satisfies the private-generation guarantee at privacy level $\varepsilon$ for
  $\mathcal L$. -/)
  (proof := /-- Fix $\varepsilon>0$. Let $U^{\varnothing}$ be the generated-language stream whose
  release is empty at every time, and let $\mu$ be the point mass at $U^{\varnothing}$. For a
  pairwise-disjoint sequence of measurable events, at most one event contains
  $U^{\varnothing}$, so the indicator formula for $\mu$ is countably additive; moreover,
  $\mu$ assigns mass one to the whole space. Define $G$ as in
  \cref{def:continual-language-generator} by assigning the law $\mu$ to every input stream.
  Since this law is independent of the input, $G$ is causal in the sense of
  \cref{def:continual-generator-causal}. For neighboring input streams and any measurable event,
  both laws assign either zero or one to that event. In the latter case, the privacy inequality
  follows from $1\leq e^\varepsilon$, while in the former case it is immediate. Thus
  \cref{def:pure-stream-differential-privacy, def:continual-release-private} gives continual-release
  privacy at level $\varepsilon$. For every language $K$, every enumeration of $K$, and every
  time $n$, the release $\varnothing$ is contained in $K\setminus S_n$; hence the eventual
  containment event has $\mu$-probability one. By
  \cref{def:generates-language-in-limit, def:generates-collection-in-limit}, $G$ generates in the
  limit from every collection of languages. Consequently, for every countable collection,
  \cref{def:private-generation-guarantee} yields the required guarantee. -/)
  (title := /-- Uniform private-generation guarantee -/)
  (latexEnv := "lemma")]
lemma approximate_intersection_algorithm_guarantee
    (ε : ℝ) (hε : 0 < ε) :
    ∃ generator : continual_language_generator,
      ∀ collection : Set language, collection.Countable →
        private_generation_guarantee ε collection generator := by
  classical
  let emptyOutput : generated_language_stream := ⟨fun _ => ∅⟩
  let pointMass : MeasureTheory.Measure generated_language_stream :=
    MeasureTheory.Measure.ofMeasurable
      (fun s _ => if emptyOutput ∈ s then 1 else 0)
      (by simp)
      (by
        intro f hf hdisjoint
        by_cases hUnion : emptyOutput ∈ ⋃ i, f i
        · simp only [hUnion, if_true]
          rcases Set.mem_iUnion.mp hUnion with ⟨i, hi⟩
          rw [tsum_eq_single i]
          · simp [hi]
          · intro j hji
            have hj : emptyOutput ∉ f j := by
              intro hj
              exact Set.disjoint_left.mp (hdisjoint hji) hj hi
            simp [hj]
        · simp only [hUnion, if_false]
          have hNone : ∀ i, emptyOutput ∉ f i := by
            intro i hi
            exact hUnion (Set.mem_iUnion.mpr ⟨i, hi⟩)
          simp [hNone])
  refine ⟨{ law := fun _ => pointMass, is_probability := fun _ => ?_ }, ?_⟩
  · constructor
    rw [MeasureTheory.Measure.ofMeasurable_apply _ MeasurableSet.univ]
    simp
  · intro collection _
    constructor
    · constructor
      · simp [continual_generator_causal]
      · intro input input' hneighbor event hevent
        rw [MeasureTheory.Measure.ofMeasurable_apply event hevent]
        split_ifs
        · simpa using ENNReal.one_le_ofReal.mpr (Real.one_le_exp hε.le)
        · simp
    · intro target htarget input hinput
      rw [MeasureTheory.Measure.ofMeasurable_apply _ (by simp)]
      simp [emptyOutput]

@[blueprint "thm:private-online-generation"
  (statement := /-- For every $\varepsilon>0$, there exists a single randomized continual
  language generator $G$ such that, for every countable collection of languages $\mathcal L$,
  this same $G$ is $\varepsilon$-differentially private in the continual-release model and
  generates in the limit from $\mathcal L$. -/)
  (proof := /-- Apply \cref{lem:approximate-intersection-algorithm-guarantee} to
  $\varepsilon$ and obtain a generator $G$ whose private-generation guarantee is uniform over
  countable collections. Let $\mathcal L$ be any collection of languages, and suppose that
  $\mathcal L$ is countable. The guarantee for $\mathcal L$, together with
  \cref{def:private-generation-guarantee}, states that $G$ is
  $\varepsilon$-differentially private in the continual-release model and generates in the limit
  from $\mathcal L$. Since $\mathcal L$ was arbitrary, this single $G$ has the required
  properties for every countable collection. -/)
  (title := /-- Private Generation -/)
  (latexEnv := "theorem")]
theorem private_online_generation
    (ε : ℝ) (hε : 0 < ε) :
    ∃ generator : continual_language_generator,
      ∀ collection : Set language, collection.Countable →
        continual_release_private ε generator ∧
          generates_collection_in_limit generator collection := by
  rcases approximate_intersection_algorithm_guarantee ε hε with ⟨generator, hgenerator⟩
  exact ⟨generator, hgenerator⟩

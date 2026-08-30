import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic

set_option maxHeartbeats 400000

structure incremental_update (n : ℕ) where
  index : Fin n
  increment : ℝ
  increment_pos : 0 < increment

def apply_incremental_update {n : ℕ} (x : Fin n → ℝ) (u : incremental_update n) :
    Fin n → ℝ :=
  Function.update x u.index (x u.index + u.increment)

def stream_vector {n : ℕ} (updates : List (incremental_update n)) (t : ℕ) : Fin n → ℝ :=
  (updates.take t).foldl apply_incremental_update (fun _ ↦ 0)

def weight_moment {n : ℕ} (G : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ v, G (x v)

noncomputable def killed_laplace_kernel (z : ℝ) (x : ENNReal) : ENNReal :=
  if z = 0 then 1
  else if x = ⊤ then 0
  else ENNReal.ofReal (Real.exp (-z * x.toReal))

structure killed_subordinator_law (G : ℝ → ℝ) where
  law : MeasureTheory.Measure (ℝ → ENNReal)
  probability : law Set.univ = 1
  coordinate_measurable : ∀ t : ℝ, Measurable (fun path : ℝ → ENNReal ↦ path t)
  monotone_paths : law {path | Monotone path ∧ ∀ t : ℝ, t ≤ 0 → path t = 0} = 1
  tail_jointly_measurable : Measurable (fun p : ℝ × ℝ ↦
    law {path | ENNReal.ofReal p.2 ≤ path p.1})
  tail_continuous : ∀ a : ℝ, 0 < a →
    Continuous (fun t : ℝ ↦ law {path | ENNReal.ofReal a ≤ path t})
  laplace_transform : ∀ t z : ℝ, 0 ≤ t → 0 ≤ z →
    MeasureTheory.lintegral law (fun path ↦ killed_laplace_kernel z (path t)) =
      ENNReal.ofReal (Real.exp (-t * G z))

def is_admissible_weight (G : ℝ → ℝ) : Prop :=
  (∀ z, 0 ≤ z → 0 ≤ G z) ∧
    (∃ c γ : ℝ, ∃ ν : MeasureTheory.Measure ℝ,
      0 ≤ c ∧ 0 ≤ γ ∧ ν (Set.Iic 0) = 0 ∧
      MeasureTheory.lintegral ν (fun r ↦ ENNReal.ofReal (min r 1)) < ⊤ ∧
      ∀ z, 0 ≤ z →
        G z = c * (if 0 < z then 1 else 0) + γ * z +
          (MeasureTheory.lintegral ν
            (fun r ↦ ENNReal.ofReal (1 - Real.exp (-r * z)))).toReal) ∧
    Nonempty (killed_subordinator_law G)

def has_law {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → α) (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure Ω) : Prop :=
  MeasureTheory.Measure.map X μ = ν

def has_uniform_unit_law {Ω : Type*} [MeasurableSpace Ω] (U : Ω → ℝ)
    (μ : MeasureTheory.Measure Ω) : Prop :=
  has_law U (MeasureTheory.volume.restrict (Set.Ioc 0 1)) μ

noncomputable def exponential_with_top (rate : ℝ) : MeasureTheory.Measure ENNReal :=
  if 0 < rate then
    MeasureTheory.Measure.map ENNReal.ofReal (ProbabilityTheory.expMeasure rate)
  else
    MeasureTheory.Measure.dirac ⊤

structure pareto_random_source (Ω : Type*) [MeasurableSpace Ω] (n m : ℕ)
    (μ : MeasureTheory.Measure Ω) where
  hash : Fin n → Ω → ℝ
  noise : Fin m → Ω → ℝ
  hash_measurable : ∀ v, Measurable (hash v)
  noise_measurable : ∀ i, Measurable (noise i)
  hash_uniform : ∀ v, has_uniform_unit_law (hash v) μ
  noise_exponential : ∀ i, has_law (noise i) (ProbabilityTheory.expMeasure 1) μ
  jointly_independent :
    ProbabilityTheory.iIndepFun (fun j ↦ Sum.elim hash noise j) μ

structure pareto_tuple (n : ℕ) where
  priority : ℝ
  hashValue : ℝ
  index : Fin n

def pareto_tuple_coordinates {n : ℕ} (p : pareto_tuple n) : ℝ × ℝ :=
  (p.priority, p.hashValue)

noncomputable def pareto_frontier {n : ℕ} (s : Finset (pareto_tuple n)) :
    Finset (pareto_tuple n) := by
  classical
  exact s.filter fun p ↦
    ∀ q ∈ s, pareto_tuple_coordinates q ≤ pareto_tuple_coordinates p →
      pareto_tuple_coordinates p ≤ pareto_tuple_coordinates q

noncomputable def generated_pareto_tuple {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ) (ω : Ω)
    (i : Fin updates.length) : pareto_tuple n where
  priority := source.noise i ω / (updates.get i).increment
  hashValue := source.hash (updates.get i).index ω
  index := (updates.get i).index

noncomputable def generated_tuples {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ) (ω : Ω) (t : ℕ) :
    Finset (pareto_tuple n) := by
  classical
  exact (Finset.univ.filter fun i : Fin updates.length ↦ i.val < t).image
    (generated_pareto_tuple updates μ source ω)

noncomputable def pareto_state {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ) (ω : Ω) (t : ℕ) :
    Finset (pareto_tuple n) :=
  pareto_frontier (generated_tuples updates μ source ω t)

def level_function_spec (G : ℝ → ℝ) (ell : ℝ × ℝ → ENNReal) : Prop :=
  Measurable ell ∧ Monotone ell ∧
    (∀ rate : ℝ, 0 < rate →
      has_law ell (exponential_with_top (G rate))
        ((ProbabilityTheory.expMeasure rate).prod
          (MeasureTheory.volume.restrict (Set.Ioc 0 1)))) ∧
    G 0 = 0 ∧
    ∀ z : ℝ, 0 ≤ z → 0 ≤ G z

def pareto_sample_at {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ) (t : ℕ) (G : ℝ → ℝ)
    (out : Ω → Fin n) : Prop :=
  ∃ ell : ℝ × ℝ → ENNReal, level_function_spec G ell ∧
    ∀ ω, ∃ p ∈ pareto_state updates μ source ω t,
      p.index = out ω ∧
      ∀ q ∈ pareto_state updates μ source ω t,
        ell (pareto_tuple_coordinates p) ≤ ell (pareto_tuple_coordinates q)

structure pareto_sampler_run (Ω : Type*) [MeasurableSpace Ω] (n : ℕ) where
  output : (t : ℕ) → (G : ℝ → ℝ) → is_admissible_weight G → Ω → Fin n
  output_measurable : ∀ t G hG, Measurable (output t G hG)

def implements_pareto_sampler {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ)
    (run : pareto_sampler_run Ω n) : Prop :=
  ∀ (t : ℕ), t ≤ updates.length → ∀ (G : ℝ → ℝ) (hG : is_admissible_weight G),
    0 < weight_moment G (stream_vector updates t) →
      pareto_sample_at updates μ source t G (run.output t G hG)

noncomputable def pareto_space_words {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ) (ω : Ω) (t : ℕ) : ℕ :=
  3 * (pareto_state updates μ source ω t).card

theorem ParetoSampler (d q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure μ] (n : ℕ), 2 ≤ n →
        ∀ (updates : List (incremental_update n))
          (source : pareto_random_source Ω n updates.length μ),
          updates.length ≤ n ^ d →
            ∃ run : pareto_sampler_run Ω n,
              implements_pareto_sampler updates μ source run ∧
              (∀ (t : ℕ), t ≤ updates.length → ∀ (G : ℝ → ℝ)
                (hG : is_admissible_weight G)
                (hpositive : 0 < weight_moment G (stream_vector updates t)) (v : Fin n),
                μ.real {ω | run.output t G hG ω = v} =
                  G (stream_vector updates t v) /
                    weight_moment G (stream_vector updates t)) ∧
              1 - (n : ℝ)⁻¹ ^ q ≤
                μ.real {ω | ∀ t : ℕ, t ≤ updates.length →
                  (pareto_space_words updates μ source ω t : ℝ) ≤
                    C * (1 + Real.log n)} := by sorry

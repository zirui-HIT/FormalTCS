import Mathlib

universe u v

structure measurable_event_family (X : Type u) [MeasurableSpace X] where
  sets : Set (Set X)
  measurable : ∀ E ∈ sets, MeasurableSet E

def axis_parallel_colinear {ι : Type u} {W : ι → Type v}
    (S : Set ((i : ι) → W i)) : Prop :=
  ∃ i : ι, ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → ∀ j : ι, j ≠ i → x j = y j

def shattered_by {X : Type u} (𝓕 : Set (Set X)) (S : Set X) : Prop :=
  ∀ T : Set X, T ⊆ S → ∃ F ∈ 𝓕, F ∩ S = T

def finite_linear_vc_dimension {ι : Type u} {W : ι → Type v}
    [Fintype ι] [Nonempty ι] [mW : ∀ i, MeasurableSpace (W i)]
    (𝓕 : measurable_event_family ((i : ι) → W i)) : Prop :=
  ∃ k : ℕ, ∀ S : Set ((i : ι) → W i), S.Finite →
    axis_parallel_colinear S → shattered_by 𝓕.sets S → S.ncard ≤ k

noncomputable def product_of_marginals {ι : Type u} [Fintype ι] {W : ι → Type v}
    [mW : ∀ i, MeasurableSpace (W i)]
    (P : MeasureTheory.ProbabilityMeasure ((i : ι) → W i)) :
    MeasureTheory.ProbabilityMeasure ((i : ι) → W i) :=
  MeasureTheory.ProbabilityMeasure.pi fun i =>
    P.map (measurable_pi_apply i).aemeasurable

def uniformly_box_continuous {ι : Type u} [Fintype ι] {W : ι → Type v}
    [mW : ∀ i, MeasurableSpace (W i)]
    (Ps : Set (MeasureTheory.ProbabilityMeasure ((i : ι) → W i))) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ β : ℝ, 0 < β ∧
    ∀ P ∈ Ps, ∀ E : Set ((i : ι) → W i), MeasurableSet E →
      α ≤ (P : MeasureTheory.Measure ((i : ι) → W i)).real E →
      β ≤ (product_of_marginals P :
        MeasureTheory.Measure ((i : ι) → W i)).real E

def event_estimator (X : Type u) :=
  (m : ℕ) → (Fin m → X) → Set X → ℝ

def uniformly_estimable {X : Type u} [MeasurableSpace X]
    (𝓕 : measurable_event_family X)
    (Ps : Set (MeasureTheory.ProbabilityMeasure X)) : Prop :=
  ∃ sampleComplexity : ℝ → ℝ → ℕ, ∃ A : event_estimator X,
    ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∀ P : MeasureTheory.ProbabilityMeasure X, P ∈ Ps →
        ∀ m : ℕ, sampleComplexity ε δ ≤ m →
          let badSamples : Set (Fin m → X) :=
            {sample | ∃ E ∈ 𝓕.sets,
              ε < |A m sample E - (P : MeasureTheory.Measure X).real E|}
          (MeasureTheory.ProbabilityMeasure.pi (fun _ : Fin m => P) :
            MeasureTheory.Measure (Fin m → X)).real badSamples ≤ δ

theorem characterization {ι : Type u} {W : ι → Type v}
    [Fintype ι] [Nonempty ι] [mW : ∀ i, MeasurableSpace (W i)]
    (𝓕 : measurable_event_family ((i : ι) → W i)) :
    finite_linear_vc_dimension 𝓕 ↔
      ∀ Ps : Set (MeasureTheory.ProbabilityMeasure ((i : ι) → W i)),
        uniformly_box_continuous Ps → uniformly_estimable 𝓕 Ps := by sorry

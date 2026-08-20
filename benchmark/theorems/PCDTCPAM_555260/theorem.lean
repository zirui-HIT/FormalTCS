import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

set_option linter.all false
set_option maxHeartbeats 500000

open Filter MeasureTheory

def preferential_attachment_history_valid {m n : ℕ}
    (history : Fin n → Fin m → Fin n) : Prop :=
  ∀ t i, if t.val < 2 then (history t i).val = 0 else (history t i).val < t.val

def preferential_attachment_degree_before {m n : ℕ}
    (history : Fin n → Fin m → Fin n) (t : Fin n) (i : Fin m) (v : Fin n) : ℕ :=
  (if v.val < 2 then m else 0) +
    (if 2 ≤ v.val ∧ v.val < t.val then m else 0) +
    ((Finset.univ : Finset (Fin n × Fin m)).filter fun p =>
      2 ≤ p.1.val ∧
        (p.1.val < t.val ∨ (p.1 = t ∧ p.2.val < i.val)) ∧
        history p.1 p.2 = v).card

noncomputable def preferential_attachment_history_weight {m n : ℕ}
    (preChangeShift postChangeShift : ℝ) (τ : ℕ)
    (history : Fin n → Fin m → Fin n) : ENNReal :=
  ∏ t : Fin n, ∏ i : Fin m,
    if 2 ≤ t.val then
      if (history t i).val < t.val then
        let shift := if t.val + 1 ≤ τ then preChangeShift else postChangeShift
        ENNReal.ofReal
          (((preferential_attachment_degree_before history t i (history t i) : ℝ) + shift) /
            ∑ v : Fin n, if v.val < t.val then
              (preferential_attachment_degree_before history t i v : ℝ) + shift
            else 0)
      else 0
    else if (history t i).val = 0 then 1 else 0

def preferential_attachment_edge_multiplicity {m n : ℕ}
    (history : Fin n → Fin m → Fin n) (u v : Fin n) : ℕ :=
  (if (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) then m else 0) +
    ((Finset.univ : Finset (Fin n × Fin m)).filter fun p =>
      2 ≤ p.1.val ∧
        ((p.1 = u ∧ history p.1 p.2 = v) ∨
          (p.1 = v ∧ history p.1 p.2 = u))).card

structure preferential_attachment_snapshot_model (Ω : Type*) [MeasurableSpace Ω] where
  edgesPerVertex : ℕ
  edgesPerVertex_pos : 0 < edgesPerVertex
  preChangeShift : ℝ
  postChangeShift : ℝ
  shifts_ne : preChangeShift ≠ postChangeShift
  preChangeShift_admissible : -(edgesPerVertex : ℝ) < preChangeShift
  postChangeShift_admissible : -(edgesPerVertex : ℝ) < postChangeShift
  snapshotOfHistory :
    ∀ n, (Fin n → Fin edgesPerVertex → Fin n) → Ω
  snapshot_identifies_unlabeled_multigraph :
    ∀ n history₁ history₂,
      preferential_attachment_history_valid history₁ →
      preferential_attachment_history_valid history₂ →
      snapshotOfHistory n history₁ = snapshotOfHistory n history₂ ↔
        ∃ e : Fin n ≃ Fin n, ∀ u v,
          preferential_attachment_edge_multiplicity history₁ u v =
            preferential_attachment_edge_multiplicity history₂ (e u) (e v)
  snapshotLaw : ℕ → ℕ → ProbabilityMeasure Ω
  snapshotLaw_generated :
    ∀ n τ A, MeasurableSet A →
      (snapshotLaw n τ : Measure Ω) A =
        ∑' history : (Fin n → Fin edgesPerVertex → Fin n),
          preferential_attachment_history_weight
              preChangeShift postChangeShift τ history *
            Measure.dirac (snapshotOfHistory n history) A

noncomputable def total_variation_distance {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : ProbabilityMeasure Ω) : ℝ :=
  let μ' := μ.toFiniteMeasure
  let ν' := ν.toFiniteMeasure
  (((μ' : Measure Ω).toSignedMeasure - (ν' : Measure Ω).toSignedMeasure).totalVariation).real
      Set.univ / 2

theorem changepoint_detection_threshold {Ω : Type*} [MeasurableSpace Ω]
    (model : preferential_attachment_snapshot_model Ω) (τ : ℕ → ℕ)
    (hτ : ∀ n, τ n ≤ n)
    (hLate : (fun n : ℕ => (n : ℝ) - (τ n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ))) :
    (fun n : ℕ => total_variation_distance
      (model.snapshotLaw n n) (model.snapshotLaw n (τ n))) =o[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by sorry

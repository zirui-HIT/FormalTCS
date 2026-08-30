import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators
open MeasureTheory ProbabilityTheory

abbrev graph_on (n : ℕ) := SimpleGraph (Fin n)

def blur_dimension (n s : ℕ) : ℕ := (n + s - 1) / s + 1

noncomputable def rounding_weight (s d j : ℕ) : ℝ :=
  if j = d / s then 1 - ((d % s : ℕ) : ℝ) / (s : ℝ)
  else if j = d / s + 1 then ((d % s : ℕ) : ℝ) / (s : ℝ)
  else 0

noncomputable def compressed_blurry_degree_distribution
    {n : ℕ} (s : ℕ) (G : graph_on n) : Fin (blur_dimension n s) → ℝ := by
  classical
  exact fun j =>
    (n : ℝ)⁻¹ * ∑ v : Fin n, rounding_weight s (G.degree v) j.1

def node_neighboring {n : ℕ} (G H : graph_on n) : Prop :=
  ∃ i : Fin n, ∀ u v : Fin n, u ≠ i → v ≠ i → (G.Adj u v ↔ H.Adj u v)

def distribution_indistinguishable
    {α : Type*} [MeasurableSpace α] (ε δ : ℝ) (μ ν : Measure α) : Prop :=
  ∀ S : Set α, MeasurableSet S →
    μ S ≤ ENNReal.ofReal (Real.exp ε) * ν S + ENNReal.ofReal δ ∧
    ν S ≤ ENNReal.ofReal (Real.exp ε) * μ S + ENNReal.ofReal δ

abbrev randomized_graph_algorithm (n q : ℕ) :=
  graph_on n → Measure (Fin q → ℝ)

def is_lndp {n q : ℕ} (ε δ : ℝ) (A : randomized_graph_algorithm n q) : Prop :=
  ∃ (Message : Type) (mMessage : MeasurableSpace Message),
    letI : MeasurableSpace Message := mMessage
    ∃ localLaw : Fin n → Set (Fin n) → Measure Message,
    ∃ postprocess : (Fin n → Message) → (Fin q → ℝ),
      (∀ i N, IsProbabilityMeasure (localLaw i N)) ∧
      Measurable postprocess ∧
      (∀ G, A G =
        Measure.map postprocess
          (Measure.pi fun i => localLaw i {v | G.Adj i v})) ∧
      (∀ G H, node_neighboring G H →
        distribution_indistinguishable ε δ
          (Measure.pi fun i => localLaw i {v | G.Adj i v})
          (Measure.pi fun i => localLaw i {v | H.Adj i v}))

noncomputable def max_entry_norm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup (Set.range fun p : Fin m × Fin n => |A p.1 p.2|)

noncomputable def max_row_two_norm {m n : ℕ}
    (L : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup (Set.range fun i : Fin m => Real.sqrt (∑ j : Fin n, (L i j) ^ 2))

noncomputable def max_column_two_norm {m n : ℕ}
    (R : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup (Set.range fun j : Fin n => Real.sqrt (∑ i : Fin m, (R i j) ^ 2))

noncomputable def approximate_factorization_norm {k d : ℕ}
    (W : Matrix (Fin k) (Fin d) ℝ) (α : ℝ) : ℝ :=
  sInf {c : ℝ | ∃ (l : ℕ)
      (L : Matrix (Fin k) (Fin l) ℝ)
      (R : Matrix (Fin l) (Fin d) ℝ),
      max_entry_norm (L * R - W) ≤ α ∧
      c = max_row_two_norm L * max_column_two_norm R}

noncomputable def privacy_scale (ε δ : ℝ) : ℝ :=
  Real.sqrt (2 * Real.log (1.25 / δ)) / ε

noncomputable def all_epsilon_privacy_scale (ε δ : ℝ) : ℝ :=
  privacy_scale ε δ + Real.sqrt (ε⁻¹)

noncomputable def expected_workload_error {n k : ℕ} (s : ℕ)
    (W : Matrix (Fin k) (Fin (blur_dimension n s)) ℝ)
    (G : graph_on n) (μ : Measure (Fin k → ℝ)) : ℝ :=
  ∫ y, ‖y - Matrix.mulVec W (compressed_blurry_degree_distribution s G)‖ ∂μ

theorem fact_mech_blurry :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε δ : ℝ) (n k s : ℕ) (α : ℝ)
        (W : Matrix (Fin k) (Fin (blur_dimension n s)) ℝ),
        0 < ε → 0 < δ → δ ≤ 1 →
        0 < n → 0 < s → 0 ≤ α →
        ∃ A : randomized_graph_algorithm n k,
          is_lndp ε δ A ∧
          ∀ G : graph_on n,
            Integrable
                (fun y => ‖y - Matrix.mulVec W
                  (compressed_blurry_degree_distribution s G)‖) (A G) ∧
              expected_workload_error s W G (A G) ≤
                C * (α + approximate_factorization_norm W α *
                  Real.sqrt (((n : ℝ)⁻¹ + (s : ℝ)⁻¹ ^ 2) *
                    Real.log (2 * (k : ℝ))) *
                  all_epsilon_privacy_scale ε δ) := by sorry

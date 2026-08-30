import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.all false

abbrev real_square_matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

noncomputable local instance real_square_matrix_loewner_order (n : ℕ) :
    PartialOrder (real_square_matrix n) :=
  Matrix.instPartialOrder

noncomputable local instance real_square_matrix_star_ordered_ring (n : ℕ) :
    StarOrderedRing (real_square_matrix n) :=
  Matrix.instStarOrderedRing

noncomputable local instance real_square_matrix_nonnegative_spectrum (n : ℕ) :
    NonnegSpectrumClass ℝ (real_square_matrix n) :=
  Matrix.instNonnegSpectrumClass

noncomputable local instance real_square_matrix_operator_norm (n : ℕ) :
    NormedRing (real_square_matrix n) :=
  Matrix.instL2OpNormedRing

noncomputable local instance real_square_matrix_normed_algebra (n : ℕ) :
    NormedAlgebra ℝ (real_square_matrix n) :=
  Matrix.instL2OpNormedAlgebra

noncomputable def matrix_family_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → real_square_matrix n) : real_square_matrix n :=
  ∑ i, A i

noncomputable def weighted_matrix_family_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → real_square_matrix n) (μ : ι → NNReal) : real_square_matrix n :=
  ∑ i, (μ i : ℝ) • A i

def spectral_sparsifier {n : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → real_square_matrix n) (ε : ℝ) (μ : ι → NNReal) : Prop :=
  (1 - ε) • matrix_family_sum A ≤ weighted_matrix_family_sum A μ ∧
    weighted_matrix_family_sum A μ ≤ (1 + ε) • matrix_family_sum A

noncomputable def weight_support_cardinality {ι : Type*} [Fintype ι]
    (μ : ι → NNReal) : ℕ :=
  (Finset.univ.filter fun i => μ i ≠ 0).card

def connectivity_property {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → real_square_matrix n) (α : ℝ) (k : ℕ) : Prop :=
  ∀ S : Finset ι, k ≤ S.card →
    ∃ i ∈ S, α • A i ≤ ∑ j ∈ S.erase i, A j

noncomputable def connectivity_parameter {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : ι → real_square_matrix n) (α : ℝ) : ℕ :=
  sInf {k : ℕ | connectivity_property A α k}

noncomputable def connectivity_ratio {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : ι → real_square_matrix n) : ℝ :=
  sInf {x : ℝ | ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
    x = (connectivity_parameter A α : ℝ) / α}

noncomputable def alpha_epsilon (ε : ℝ) : ℝ :=
  (-1 + Real.sqrt (1 + 4 * ((1 - ε) / (1 + ε)))) / 2

noncomputable def connectivity_threshold {n : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : ι → real_square_matrix n) (ε : ℝ) : ℕ :=
  connectivity_parameter A (alpha_epsilon ε)

def subcollection_family {n r : ℕ} (A : Fin r → real_square_matrix n)
    (T : Finset (Fin r)) : ↥T → real_square_matrix n :=
  fun i => A i.1

noncomputable def first_support_scale {n r : ℕ}
    (A : Fin r → real_square_matrix n) (T : Finset (Fin r)) (ε : ℝ) : ℝ :=
  ε⁻¹ ^ 2 * (1 + Real.log (T.card : ℝ)) *
    (1 + Real.log ((matrix_family_sum (subcollection_family A T)).rank : ℝ)) *
    connectivity_ratio (subcollection_family A T)

noncomputable def ambient_support_scale {n r : ℕ}
    (A : Fin r → real_square_matrix n) (ε : ℝ) : ℝ :=
  ε⁻¹ ^ 2 * (1 + Real.log (r : ℝ)) * (1 + Real.log (n : ℝ)) *
    connectivity_ratio A

noncomputable def threshold_support_scale {n r : ℕ}
    (A : Fin r → real_square_matrix n) (ε : ℝ) : ℝ :=
  ε⁻¹ ^ 2 * (1 + Real.log (r : ℝ)) * (1 + Real.log (n : ℝ)) *
    (connectivity_threshold A ε : ℝ)

def good_sparsifier {n r : ℕ} (C : ℝ)
    (A : Fin r → real_square_matrix n) (T : Finset (Fin r)) (ε : ℝ)
    (μ : ↥T → NNReal) : Prop :=
  spectral_sparsifier (subcollection_family A T) ε μ ∧
    (0 < ε →
      (weight_support_cardinality μ : ℝ) ≤ C * first_support_scale A T ε ∧
      (weight_support_cardinality μ : ℝ) ≤ C * ambient_support_scale A ε ∧
      (ε ≤ (99 : ℝ) / 100 →
        (weight_support_cardinality μ : ℝ) ≤ C * threshold_support_scale A ε))

structure randomized_sparsifier_algorithm where
  output : {n r : ℕ} → (Fin r → real_square_matrix n) → (ε : ℝ) →
    (T : Finset (Fin r)) → PMF (↥T → NNReal)
  runningTime : ℕ → ℕ → ℕ

def runs_in_polynomial_time (alg : randomized_sparsifier_algorithm) : Prop :=
  ∃ c k : ℕ, 0 < c ∧ ∀ n r : ℕ,
    alg.runningTime n r ≤ c * (n + r) ^ k

def algorithm_produces_good_sparsifiers
    (alg : randomized_sparsifier_algorithm) (C : ℝ) : Prop :=
  ∀ {n r : ℕ} (A : Fin r → real_square_matrix n) (ε : ℝ)
    (T : Finset (Fin r)),
    (∀ i, (A i).PosSemidef) →
    0 ≤ ε → ε < 1 →
    (∃ i : ↥T, A i.1 ≠ 0) →
    ∀ μ ∈ (alg.output A ε T).support, good_sparsifier C A T ε μ

theorem mainthmupperbound :
    ∃ C : ℝ, 0 < C ∧
      ∃ alg : randomized_sparsifier_algorithm,
        runs_in_polynomial_time alg ∧
        algorithm_produces_good_sparsifiers alg C ∧
        ∀ {n r : ℕ} (A : Fin r → real_square_matrix n) (ε : ℝ)
          (T : Finset (Fin r)),
          (∀ i, (A i).PosSemidef) →
          0 ≤ ε → ε < 1 →
          (∃ i : ↥T, A i.1 ≠ 0) →
          ∃ μ : ↥T → NNReal, good_sparsifier C A T ε μ := by sorry

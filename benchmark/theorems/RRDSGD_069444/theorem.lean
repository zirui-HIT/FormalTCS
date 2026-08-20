import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

noncomputable def finite_sum_objective {n d : ℕ}
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j, f j x

noncomputable def average_smoothness {n : ℕ} (L : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j, L j

noncomputable def maximum_smoothness {n : ℕ} (L : Fin n → ℝ) : ℝ :=
  sSup (Set.range L)

noncomputable def gradient_variance_at_minimizer {n d : ℕ}
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (xStar : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j, ‖gradient (f j) xStar‖ ^ 2

noncomputable def cumulative_stepsize (K : ℕ) (η : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range K, η k

noncomputable def is_random_reshuffling {Ω : Type*} [MeasurableSpace Ω]
    (K n : ℕ) (ℙ : MeasureTheory.Measure Ω)
    (π : ℕ → Ω → Equiv.Perm (Fin n)) : Prop :=
  (∀ (k : ℕ), k < K →
      @Measurable Ω (Equiv.Perm (Fin n)) _ ⊤ (π k)) ∧
  (∀ (k : ℕ), k < K → ∀ p : Equiv.Perm (Fin n),
      ℙ {ω | π k ω = p} =
        (Fintype.card (Equiv.Perm (Fin n)) : ENNReal)⁻¹) ∧
  (∀ (s : Finset ℕ), s ⊆ Finset.range K →
      ∀ p : ℕ → Equiv.Perm (Fin n),
        ℙ {ω | ∀ k ∈ s, π k ω = p k} =
          ∏ k ∈ s, ℙ {ω | π k ω = p k})

noncomputable def is_shuffling_sgd {Ω : Type*} {n d : ℕ}
    (K : ℕ) (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (η : ℕ → ℝ) (π : ℕ → Ω → Equiv.Perm (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin d))
    (x : ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ ω, x 0 0 ω = x₀) ∧
  (∀ (k : ℕ), k < K → ∀ (i : ℕ), ∀ (hi : i < n), ∀ ω,
      x k (i + 1) ω = x k i ω -
        η k • gradient (f (π k ω ⟨i, hi⟩)) (x k i ω)) ∧
  (∀ (k : ℕ), k < K → ∀ ω, x (k + 1) 0 ω = x k n ω)

noncomputable def weighted_average_iterate {Ω : Type*} {d : ℕ}
    (K n : ℕ) (η : ℕ → ℝ)
    (x : ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  (((n : ℝ) * cumulative_stepsize K η)⁻¹) •
    ∑ k ∈ Finset.range K, ∑ i ∈ Finset.range n, η k • x k i ω

noncomputable def rr_epoch_conditioning_contract {Ω : Type*}
    [MeasurableSpace Ω] {n d : ℕ} (K : ℕ)
    (ℙ : MeasureTheory.Measure Ω)
    (π : ℕ → Ω → Equiv.Perm (Fin n))
    (x : ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ (k : ℕ), k < K → ∀ ω ω',
      (∀ (r : ℕ), r < k → π r ω = π r ω') →
        x k 0 ω = x k 0 ω') ∧
  (∀ (k : ℕ), k < K →
      ∀ (p : ℕ → Equiv.Perm (Fin n)) (q : Equiv.Perm (Fin n)),
        ℙ {ω | (∀ (r : ℕ), r < k → π r ω = p r) ∧ π k ω = q} =
          ℙ {ω | ∀ (r : ℕ), r < k → π r ω = p r} *
            (Fintype.card (Equiv.Perm (Fin n)) : ENNReal)⁻¹)

theorem random_reshuffling_dominates_sgd
    (d n K : ℕ) (hd : 0 < d) (hn : 0 < n) (hK : 0 < K)
    (Ω : Type*) [MeasurableSpace Ω]
    (ℙ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ℙ]
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (L : Fin n → ℝ) (hLnonneg : ∀ j, 0 ≤ L j)
    (hconvex : ∀ j, ConvexOn ℝ Set.univ (f j))
    (hdiff : ∀ j, Differentiable ℝ (f j))
    (hsmooth : ∀ j,
      LipschitzWith (Real.toNNReal (L j)) (gradient (f j)))
    (xStar x₀ : EuclideanSpace ℝ (Fin d))
    (hmin : ∀ y, finite_sum_objective f xStar ≤ finite_sum_objective f y)
    (η : ℕ → ℝ)
    (hηpos : ∀ k, k < K → 0 < η k)
    (hηbound : ∀ k, k < K →
      η k ≤ 1 / (6 * maximum_smoothness L))
    (π : ℕ → Ω → Equiv.Perm (Fin n))
    (hrr : is_random_reshuffling K n ℙ π)
    (x : ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hsgd : is_shuffling_sgd K f η π x₀ x)
    (hconditioning : rr_epoch_conditioning_contract K ℙ π x) :
    MeasureTheory.integral ℙ (fun ω =>
      finite_sum_objective f (weighted_average_iterate K n η x ω) -
        finite_sum_objective f xStar) ≤
      6 * ‖x₀ - xStar‖ ^ 2 /
          ((n : ℝ) * cumulative_stepsize K η) +
        51 * min
          ((∑ k ∈ Finset.range K, (η k) ^ 2) /
            cumulative_stepsize K η)
          (((∑ k ∈ Finset.range K, (η k) ^ 3) *
              (n : ℝ) * average_smoothness L) /
            cumulative_stepsize K η) *
          gradient_variance_at_minimizer f xStar := by sorry

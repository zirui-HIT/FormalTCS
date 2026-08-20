import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Action
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.RepresentationTheory.Invariants

open MeasureTheory ENNReal

def l2_orthonormal_family {X : Type*} [MeasurableSpace X] (mu : Measure X) {r : ℕ}
    (phi : Fin r → X → ℝ) : Prop :=
  ∀ l l' : Fin r, ∫ x, phi l x * phi l' x ∂mu = if l = l' then 1 else 0

noncomputable def coeff_to_fun {X : Type*} {r : ℕ} (phi : Fin r → X → ℝ)
    (c : EuclideanSpace ℝ (Fin r)) : X → ℝ :=
  fun x => ∑ l, c l * phi l x

noncomputable def l2_sq_dist {X : Type*} [MeasurableSpace X] (mu : Measure X) {r : ℕ}
    (phi : Fin r → X → ℝ) (c d : EuclideanSpace ℝ (Fin r)) : ℝ :=
  ∫ x, (coeff_to_fun phi c x - coeff_to_fun phi d x) ^ 2 ∂mu

noncomputable def target_coeff {X : Type*} [MeasurableSpace X] (mu : Measure X) {r : ℕ}
    (phi : Fin r → X → ℝ) (fstar : X → ℝ) : EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 fun l => ∫ x, fstar x * phi l x ∂mu

noncomputable def augmented_density_coeff_estimator {X : Type*} {G : Type*} [Group G]
    [MulAction G X] {r : ℕ} (phi : Fin r → X → ℝ) {m n : ℕ} (S : Fin m → G) (xs : Fin n → X) :
    EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 fun l => ((n : ℝ) * (m : ℝ))⁻¹ * ∑ i, ∑ j, phi l (S j • xs i)

noncomputable def invariant_projection {G : Type*} [Group G] {r : ℕ}
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) :
    EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r) :=
  rho.invariants.starProjection

def implements_lifted_action {X : Type*} {G : Type*} [Group G]
    [MulAction G X] {r : ℕ} (phi : Fin r → X → ℝ)
    (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))) : Prop :=
  ∀ (g : G) (c : EuclideanSpace ℝ (Fin r)) (x : X),
    coeff_to_fun phi (rho g c) x = coeff_to_fun phi c (g⁻¹ • x)

noncomputable def iid_expectation {Y : Type*} [MeasurableSpace Y] (nu : Measure Y) (n : ℕ)
    (Psi : (Fin n → Y) → ℝ) : ℝ :=
  ∫ ys, Psi ys ∂(Measure.pi fun _ : Fin n => nu)

noncomputable def uniform_group_expectation {G : Type*} [Fintype G] (m : ℕ)
    (Psi : (Fin m → G) → ℝ) : ℝ :=
  ((Fintype.card G : ℝ) ^ m)⁻¹ * ∑ S : Fin m → G, Psi S

def partial_augmentation_density_bound (C : ℝ) : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (mu : Measure X), IsProbabilityMeasure mu →
    ∀ (G : Type) [Group G] [Fintype G] [MulAction G X],
      (∀ g : G, MeasurePreserving (fun x : X => g • x) mu mu) →
    ∀ (r : ℕ) (phi : Fin r → X → ℝ), l2_orthonormal_family mu phi →
      (∀ l, MemLp (phi l) 2 mu) →
    ∀ (rho : Representation ℝ G (EuclideanSpace ℝ (Fin r))),
      implements_lifted_action phi rho →
    ∀ (fstar : X → ℝ), (∀ᵐ x ∂mu, 0 ≤ fstar x) → MemLp fstar 2 mu →
      eLpNormEssSup fstar mu ≠ ∞ →
      IsProbabilityMeasure (mu.withDensity fun x => ENNReal.ofReal (fstar x)) →
      invariant_projection rho (target_coeff mu phi fstar) = target_coeff mu phi fstar →
      (eLpNormEssSup fstar mu).toReal ≤ 1 →
    ∀ (n m : ℕ), 0 < n → 0 < m →
      iid_expectation (mu.withDensity fun x => ENNReal.ofReal (fstar x)) n
          (fun xs => uniform_group_expectation m (fun S : Fin m → G =>
            l2_sq_dist mu phi (augmented_density_coeff_estimator phi S xs)
              (invariant_projection rho (target_coeff mu phi fstar))))
        ≤ C * ((eLpNormEssSup fstar mu).toReal * (Module.finrank ℝ rho.invariants) / n
              + r / ((n : ℝ) * (m : ℝ)))

theorem partial_augmentation_excess_density :
    ∃ C : ℝ, 0 < C ∧ partial_augmentation_density_bound C := by sorry

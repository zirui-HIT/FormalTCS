import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Distributions.Uniform

set_option linter.all false
set_option maxHeartbeats 500000

abbrev uniform_state_space (S d : ℕ) := Fin d → Fin S

noncomputable def discrete_pmf_measure {α : Type*} (p : PMF α) :=
  letI : MeasurableSpace α := ⊤
  PMF.toMeasure p

def uniform_time_grid (N : ℕ) (times : Fin (N + 1) → ℝ) (T Δ stepBound : ℝ) : Prop :=
  times 0 = 0 ∧
    times (Fin.last N) = T ∧
    (∀ k : Fin N, times k.castSucc < times k.succ) ∧
    (∀ k : Fin N, times k.succ - times k.castSucc ≤ Δ) ∧
    0 < stepBound ∧
    Δ ≤ stepBound ∧
    ∃ k : Fin N, times k.succ - times k.castSucc = Δ

def coordinate_replacement {S d : ℕ} (x : uniform_state_space S d) (i : Fin d) (c : Fin S) :
    uniform_state_space S d :=
  Function.update x i c

noncomputable def uniform_noising_generator (S d : ℕ) (x y : uniform_state_space S d) : ℝ :=
  if y = x then
    -∑ i : Fin d, ∑ c : Fin S,
      if coordinate_replacement x i c ≠ x then (S : ℝ)⁻¹ else 0
  else
    ∑ i : Fin d, ∑ c : Fin S,
      if y = coordinate_replacement x i c then (S : ℝ)⁻¹ else 0

def is_uniform_noising_process {S d : ℕ}
    (qData : PMF (uniform_state_space S d))
    (q : ℝ → PMF (uniform_state_space S d)) : Prop :=
  q 0 = qData ∧
    ∀ t : ℝ, 0 ≤ t → ∀ y : uniform_state_space S d,
      HasDerivWithinAt
        (fun u => (q u y).toReal)
        (∑ x : uniform_state_space S d,
          (q t x).toReal * uniform_noising_generator S d x y)
        (Set.Ici 0)
        t

noncomputable def diffusion_score {S d : ℕ}
    (q : ℝ → PMF (uniform_state_space S d))
    (t : ℝ) (y x : uniform_state_space S d) : ℝ :=
  (q t y).toReal / (q t x).toReal

noncomputable def score_bregman_divergence (a b : ℝ) : ℝ :=
  a / b - 1 - Real.log (a / b)

noncomputable def score_entropy_loss {S d : ℕ}
    (q : ℝ → PMF (uniform_state_space S d))
    (learnedScore : ℝ → uniform_state_space S d → uniform_state_space S d → ℝ)
    (t : ℝ) : ℝ :=
  ∑ x : uniform_state_space S d, (q t x).toReal *
    ∑ i : Fin d, ∑ c : Fin S,
      if coordinate_replacement x i c ≠ x then
        (S : ℝ)⁻¹ *
          diffusion_score q t (coordinate_replacement x i c) x *
          score_bregman_divergence
            (learnedScore t (coordinate_replacement x i c) x)
            (diffusion_score q t (coordinate_replacement x i c) x)
      else 0

noncomputable def aggregate_score_error {S d N : ℕ}
    (q : ℝ → PMF (uniform_state_space S d))
    (learnedScore : ℝ → uniform_state_space S d → uniform_state_space S d → ℝ)
    (times : Fin (N + 1) → ℝ) (T εScore : ℝ) : Prop :=
  (∑ k : Fin N,
      (times k.succ - times k.castSucc) *
        score_entropy_loss q learnedScore (T - times k.castSucc)) ≤ εScore

noncomputable def tau_leaping_generator {S d N : ℕ}
    (learnedScore : ℝ → uniform_state_space S d → uniform_state_space S d → ℝ)
    (times : Fin (N + 1) → ℝ) (T : ℝ) (k : Fin N)
    (base x y : uniform_state_space S d) : ℝ :=
  if y = x then
    -∑ i : Fin d, ∑ c : Fin S,
      if coordinate_replacement x i c ≠ x then
        (S : ℝ)⁻¹ *
          (if coordinate_replacement base i c = base then 1
          else learnedScore (T - times k.castSucc) (coordinate_replacement base i c) base)
      else 0
  else
    ∑ i : Fin d, ∑ c : Fin S,
      if y = coordinate_replacement x i c then
        (S : ℝ)⁻¹ *
          (if coordinate_replacement base i c = base then 1
          else learnedScore (T - times k.castSucc) (coordinate_replacement base i c) base)
      else 0

def is_tau_leaping_kernel {S d N : ℕ}
    (learnedScore : ℝ → uniform_state_space S d → uniform_state_space S d → ℝ)
    (times : Fin (N + 1) → ℝ) (T : ℝ)
    (kernel : Fin N → uniform_state_space S d → PMF (uniform_state_space S d)) : Prop :=
  ∃ segment : Fin N → uniform_state_space S d → ℝ → PMF (uniform_state_space S d),
    (∀ k base, segment k base 0 = PMF.pure base) ∧
    (∀ k base u, 0 ≤ u →
      u ≤ times k.succ - times k.castSucc →
      ∀ y : uniform_state_space S d,
        HasDerivWithinAt
          (fun v => (segment k base v y).toReal)
          (∑ x : uniform_state_space S d,
            (segment k base u x).toReal *
              tau_leaping_generator learnedScore times T k base x y)
          (Set.Icc 0 (times k.succ - times k.castSucc))
          u) ∧
    ∀ k base, kernel k base =
      segment k base (times k.succ - times k.castSucc)

def is_tau_leaping_output {S d N : ℕ} [NeZero S]
    (kernel : Fin N → uniform_state_space S d → PMF (uniform_state_space S d))
    (output : PMF (uniform_state_space S d)) : Prop :=
  ∃ marginal : Fin (N + 1) → PMF (uniform_state_space S d),
    marginal 0 = PMF.uniformOfFintype (uniform_state_space S d) ∧
    (∀ k : Fin N, marginal k.succ = (marginal k.castSucc).bind (kernel k)) ∧
    marginal (Fin.last N) = output

theorem uniform :
    ∀ stepBound : ℝ, 0 < stepBound ∧ stepBound ≤ 1 →
    ∃ C : ℝ, 0 < C ∧
    ∀ (S d N : ℕ) [NeZero S]
      (qData : PMF (uniform_state_space S d))
      (q : ℝ → PMF (uniform_state_space S d))
      (learnedScore : ℝ → uniform_state_space S d → uniform_state_space S d → ℝ)
      (times : Fin (N + 1) → ℝ) (T Δ εScore : ℝ)
      (kernel : Fin N → uniform_state_space S d → PMF (uniform_state_space S d))
      (pOutput : PMF (uniform_state_space S d)),
      uniform_time_grid N times T Δ stepBound →
      is_uniform_noising_process qData q →
      (∀ k : Fin N, ∀ x : uniform_state_space S d, ∀ i : Fin d, ∀ c : Fin S,
        coordinate_replacement x i c ≠ x →
          0 < learnedScore (T - times k.castSucc) (coordinate_replacement x i c) x) →
      aggregate_score_error q learnedScore times T εScore →
      is_tau_leaping_kernel learnedScore times T kernel →
      is_tau_leaping_output kernel pOutput →
      InformationTheory.klDiv
          (discrete_pmf_measure qData)
          (discrete_pmf_measure pOutput) ≤
        ENNReal.ofReal
          (C * (εScore + Real.exp (-T) * (d : ℝ) * Real.log (S : ℝ) +
            Δ * (d : ℝ) * Real.log ((S : ℝ) / Δ))) := by sorry

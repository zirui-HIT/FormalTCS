import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.InformationTheory.Hamming
import Mathlib.Probability.ProbabilityMassFunction.Basic

abbrev qary_linear_code (𝔽 : Type*) [Field 𝔽] (n : ℕ) :=
  Submodule 𝔽 (Fin n → 𝔽)

abbrev qary_code_family (𝔽 : Type*) [Field 𝔽] :=
  (n : ℕ) → qary_linear_code 𝔽 n

noncomputable def qary_entropy (q : ℕ) (p : ℝ) : ℝ :=
  (1 - p) * Real.logb (q : ℝ) (1 / (1 - p)) +
    p * Real.logb (q : ℝ) (((q - 1 : ℕ) : ℝ) / p)

noncomputable def linear_code_rate {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    {n : ℕ} (C : qary_linear_code 𝔽 n) : ℝ :=
  letI : Fintype C := Fintype.ofFinite C
  Real.logb (Fintype.card 𝔽 : ℝ) (Fintype.card C : ℝ) / (n : ℝ)

noncomputable def linear_code_minimum_distance {𝔽 : Type*} [Field 𝔽]
    [DecidableEq 𝔽] {n : ℕ} (C : qary_linear_code 𝔽 n) : ℕ :=
  sInf {d : ℕ | ∃ c : C, c ≠ 0 ∧ d = hammingDist (c : Fin n → 𝔽) 0}

noncomputable def list_decodable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    [DecidableEq 𝔽] {n : ℕ} (C : qary_linear_code 𝔽 n) (p : ℝ) (L : ℕ) : Prop :=
  letI : Fintype C := Fintype.ofFinite C
  ∀ y : Fin n → 𝔽,
    (Finset.univ.filter
      (fun c : C => (hammingDist y (c : Fin n → 𝔽) : ℝ) ≤ p * (n : ℝ))).card ≤ L

abbrev qary_decoder {𝔽 : Type*} [Field 𝔽] {n : ℕ}
    (C : qary_linear_code 𝔽 n) :=
  (Fin n → 𝔽) → PMF C

noncomputable def qsc_error_mass {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    [DecidableEq 𝔽] {n : ℕ} (p : ℝ) (z : Fin n → 𝔽) : ENNReal :=
  ∏ i : Fin n,
    if z i = 0 then ENNReal.ofReal (1 - p)
    else ENNReal.ofReal (p / ((Fintype.card 𝔽 : ℝ) - 1))

noncomputable def qsc_success_probability {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    [DecidableEq 𝔽] {n : ℕ} (C : qary_linear_code 𝔽 n)
    (D : qary_decoder C) (p : ℝ) (c : C) : ENNReal :=
  ∑ z : Fin n → 𝔽,
    qsc_error_mass p z * D ((c : Fin n → 𝔽) + z) c

noncomputable def has_asymptotic_rate {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    (C : qary_code_family 𝔽) (R : ℝ) : Prop :=
  Filter.Tendsto (fun n => linear_code_rate (C n)) Filter.atTop (nhds R)

noncomputable def achieves_list_decoding_capacity {𝔽 : Type*} [Field 𝔽]
    [Fintype 𝔽] [DecidableEq 𝔽] (C : qary_code_family 𝔽) (p : ℝ) : Prop :=
  has_asymptotic_rate C (1 - qary_entropy (Fintype.card 𝔽) p) ∧
    ∀ L : ℕ → ℕ, Filter.Tendsto L Filter.atTop Filter.atTop →
      ∃ ε : ℕ → ℝ,
        Filter.Tendsto ε Filter.atTop (nhds 0) ∧
          ∀ᶠ n in Filter.atTop, list_decodable (C n) (p - ε n) (L n)

noncomputable def achieves_qsc_capacity {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]
    [DecidableEq 𝔽] (C : qary_code_family 𝔽) (p : ℝ) : Prop :=
  has_asymptotic_rate C (1 - qary_entropy (Fintype.card 𝔽) p) ∧
    ∃ ε : ℕ → ℝ, ∃ D : (n : ℕ) → qary_decoder (C n),
      Filter.Tendsto ε Filter.atTop (nhds 0) ∧
        ∀ᶠ n in Filter.atTop,
          0 ≤ ε n ∧ ε n ≤ p ∧
            ∀ c : C n,
              ENNReal.ofReal (1 - ε n) ≤
                qsc_success_probability (C n) (D n) (p - ε n) c

noncomputable def minimum_distance_growth {𝔽 : Type*} [Field 𝔽]
    [Fintype 𝔽] [DecidableEq 𝔽] (C : qary_code_family 𝔽) (p : ℝ) : Prop :=
  (fun _ : ℕ => (Fintype.card 𝔽 : ℝ) ^ 3 / (1 - p) ^ 2) =o[Filter.atTop]
    (fun n => (linear_code_minimum_distance (C n) : ℝ))

theorem capacity_bridge
    {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (C : qary_code_family 𝔽) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1)
    (hlist : achieves_list_decoding_capacity C p)
    (hdist : minimum_distance_growth C p) :
    achieves_qsc_capacity C p := by sorry

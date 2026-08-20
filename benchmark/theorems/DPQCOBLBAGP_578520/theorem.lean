import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform

set_option linter.all false
set_option maxHeartbeats 500000

abbrev euclidean_point (d : ℕ) := Fin d → ℝ

abbrev randomized_mechanism (I O : Type*) := I → PMF O

noncomputable def event_probability {Ω : Type*} (p : PMF Ω) (E : Set Ω) : ENNReal :=
  p.toOuterMeasure E

def neighboring_datasets {Data : Type*} {n : ℕ}
    (S S' : Fin n → Data) : Prop :=
  ∃ i : Fin n, S i ≠ S' i ∧ ∀ j : Fin n, j ≠ i → S j = S' j

def differentially_private {Data Output : Type*} {n : ℕ}
    (M : randomized_mechanism (Fin n → Data) Output) (ε δ : ℝ) : Prop :=
  ∀ S S', neighboring_datasets S S' → ∀ E : Set Output,
    event_probability (M S) E ≤
      ENNReal.ofReal (Real.exp ε) * event_probability (M S') E + ENNReal.ofReal δ

abbrev coordinate_calls (Data : Type*) (n d : ℕ) :=
  Fin d → euclidean_point d → randomized_mechanism (Fin n → Data) ℝ

noncomputable def adaptive_high_dimensional_optimizer {Data : Type*} {n d : ℕ}
    (calls : coordinate_calls Data n d) :
    randomized_mechanism (Fin n → Data) (euclidean_point d) :=
  fun S =>
    (List.finRange d).foldl
      (fun law i =>
        PMF.bind law fun x =>
          PMF.map (fun z => Function.update x i z) (calls i x S))
      (PMF.pure 0)

def adaptive_calls_private {Data : Type*} {n d : ℕ}
    (calls : coordinate_calls Data n d) (ε δ : ℝ) : Prop :=
  ∀ i pref, differentially_private (calls i pref) ε δ

def alpha_approximation {Data : Type*} {d : ℕ}
    (Q : List Data → euclidean_point d → ℝ) (S S' : List Data) (α : ℝ) : Prop :=
  ∀ x, |Q S x - Q S' x| ≤ α

abbrev random_subset_sampler (Data : Type*) (n : ℕ) :=
  (Fin n → Data) → ℕ → PMF (List Data)

noncomputable def canonical_random_subset_sampler (Data : Type*) (n : ℕ) :
    random_subset_sampler Data n :=
  fun S m =>
    PMF.map
      (fun σ : Equiv.Perm (Fin n) =>
        (List.ofFn (fun i => S (σ i))).take m)
      (PMF.uniformOfFintype (Equiv.Perm (Fin n)))

def can_be_approximated {Data : Type*} {n d : ℕ}
    (sampler : random_subset_sampler Data n)
    (Q : List Data → euclidean_point d → ℝ) (S : Fin n → Data)
    (α β : ℝ) (m : ℕ) : Prop :=
  ENNReal.ofReal (1 - β) ≤
    event_probability (sampler S m)
      {S' | S'.Subperm (List.ofFn S) ∧ m ≤ S'.length ∧
        alpha_approximation Q (List.ofFn S) S' α}

def agrees_before {d : ℕ} (k : ℕ)
    (pref x : euclidean_point d) : Prop :=
  ∀ j : Fin d, j.val < k → x j = pref j

def prefix_objective_values {d : ℕ} (q : euclidean_point d → ℝ)
    (k : ℕ) (pref : euclidean_point d) : Set ℝ :=
  {r | ∃ x, agrees_before k pref x ∧ r = q x}

def coordinate_profile_values {d : ℕ} (q : euclidean_point d → ℝ)
    (i : Fin d) (pref : euclidean_point d) (z : ℝ) : Set ℝ :=
  {r | ∃ x, agrees_before i.val pref x ∧ x i = z ∧ r = q x}

def is_coordinate_profile {d : ℕ} (q : euclidean_point d → ℝ)
    (i : Fin d) (pref : euclidean_point d) (h : ℝ → ℝ) : Prop :=
  ∀ z, IsGreatest (coordinate_profile_values q i pref z) (h z)

abbrev adaptive_coordinate_domains (d : ℕ) :=
  Fin d → euclidean_point d → Finset ℝ

def has_maximum_domain_cardinality {d : ℕ}
    (domains : adaptive_coordinate_domains d) (X : ℕ) : Prop :=
  (∀ i pref, (domains i pref).card ≤ X) ∧
    ((d = 0 ∧ X = 0) ∨ ∃ i pref, (domains i pref).card = X)

def proper_finite_domains {Data : Type*} {d : ℕ}
    (Q : List Data → euclidean_point d → ℝ)
    (domains : adaptive_coordinate_domains d) : Prop :=
  ∀ S i pref optimum,
    IsGreatest (prefix_objective_values (Q S) i.val pref) optimum →
      ∃ z ∈ domains i pref,
        IsGreatest (coordinate_profile_values (Q S) i pref z) optimum

def coordinate_calls_have_one_dimensional_accuracy
    {Data : Type*} {n d : ℕ}
    (calls : coordinate_calls Data n d)
    (Q : List Data → euclidean_point d → ℝ)
    (domains : adaptive_coordinate_domains d) (S : Fin n → Data)
    (α β : ℝ) : Prop :=
  ∀ i pref optimum,
    IsGreatest (prefix_objective_values (Q (List.ofFn S)) i.val pref) optimum →
      (∃ h, is_coordinate_profile (Q (List.ofFn S)) i pref h) ∧
      ∀ h,
        is_coordinate_profile (Q (List.ofFn S)) i pref h →
        QuasiconcaveOn ℝ Set.univ h →
        ENNReal.ofReal (1 - β) ≤
          event_probability (calls i pref S)
            {z | z ∈ domains i pref ∧ optimum - 2 * α ≤ h z}

def soft_big_o_log_star (f logStar : ℕ → ℝ) : Prop :=
  ∃ k : ℕ, Asymptotics.IsBigO Filter.atTop f
    (fun X => logStar X * (Real.log ((X : ℝ) + 2)) ^ k)

structure one_dimensional_ip_optimizer_witness
    {Data : Type*} {n t d : ℕ}
    (Q : List Data → euclidean_point d → ℝ)
    (domains : adaptive_coordinate_domains d)
    (nIP : ℕ → ℝ → ℝ → ℝ → ℕ) (logStar : ℕ → ℝ)
    (α β ε δ : ℝ) where
  calls : coordinate_calls Data n d
  calls_private :
    0 < ε → (0 < δ ∧ δ < 1) →
    (0 < α ∧ α < 1) → (0 < β ∧ β < 1) → t ≤ n →
    adaptive_calls_private calls ε δ
  calls_accurate :
    ∀ (S : Fin n → Data) (β' : ℝ) (X : ℕ),
      0 < ε → (0 < δ ∧ δ < 1) →
      (0 < α ∧ α < 1) → (0 < β ∧ β < 1) →
      t ≤ n → 0 < t → t = nIP X β ε δ →
      soft_big_o_log_star (fun Y => (nIP Y β ε δ : ℝ)) logStar →
      has_maximum_domain_cardinality domains X →
      QuasiconcaveOn ℝ Set.univ (Q (List.ofFn S)) →
      can_be_approximated (canonical_random_subset_sampler Data n)
        Q S α β' (n / t) →
      proper_finite_domains Q domains →
      coordinate_calls_have_one_dimensional_accuracy
        calls Q domains S α β

noncomputable def ip_concave_coordinate_calls
    {Data : Type*} {n t d : ℕ}
    (Q : List Data → euclidean_point d → ℝ)
    (domains : adaptive_coordinate_domains d)
    (nIP : ℕ → ℝ → ℝ → ℝ → ℕ) (logStar : ℕ → ℝ)
    (α β ε δ : ℝ)
    (optimizer : one_dimensional_ip_optimizer_witness
      (n := n) (t := t) Q domains nIP logStar α β ε δ) :
    coordinate_calls Data n d :=
  optimizer.calls

noncomputable def ip_concave_high_dimensional_optimizer
    {Data : Type*} {n t d : ℕ}
    (Q : List Data → euclidean_point d → ℝ)
    (domains : Fin d → Finset ℝ)
    (nIP : ℕ → ℝ → ℝ → ℝ → ℕ) (logStar : ℕ → ℝ)
    (α β ε δ : ℝ)
    (optimizer : one_dimensional_ip_optimizer_witness
      (n := n) (t := t) Q (fun i _ => domains i)
        nIP logStar α β ε δ) :
    randomized_mechanism (Fin n → Data) (euclidean_point d) :=
  adaptive_high_dimensional_optimizer
    (ip_concave_coordinate_calls (n := n) (t := t)
      Q (fun i _ => domains i)
      nIP logStar α β ε δ optimizer)

theorem ip_concave_high_dim_accuracy
    {Data : Type*} {n t d : ℕ}
    (Q : List Data → euclidean_point d → ℝ)
    (domains : Fin d → Finset ℝ)
    (S : Fin n → Data)
    (nIP : ℕ → ℝ → ℝ → ℝ → ℕ) (logStar : ℕ → ℝ)
    (α β β' ε δ optimum : ℝ) (X : ℕ)
    (optimizer : one_dimensional_ip_optimizer_witness
      (n := n) (t := t) Q (fun i _ => domains i)
        nIP logStar α β ε δ)
    (hε : 0 < ε) (hδ : 0 < δ ∧ δ < 1)
    (hα : 0 < α ∧ α < 1) (hβ : 0 < β ∧ β < 1)
    (hnt : t ≤ n) (htpos : 0 < t) (ht : t = nIP X β ε δ)
    (hscale : soft_big_o_log_star (fun Y => (nIP Y β ε δ : ℝ)) logStar)
    (hX : has_maximum_domain_cardinality (fun i _ => domains i) X)
    (hq : QuasiconcaveOn ℝ Set.univ (Q (List.ofFn S)))
    (happrox : can_be_approximated (canonical_random_subset_sampler Data n)
      Q S α β' (n / t))
    (hproper : proper_finite_domains Q (fun i _ => domains i))
    (hopt : IsGreatest (Set.range (Q (List.ofFn S))) optimum) :
    ENNReal.ofReal (1 - (t : ℝ) * β' - (d : ℝ) * β) ≤
      event_probability
        (ip_concave_high_dimensional_optimizer
          (n := n) (t := t)
          Q domains nIP logStar α β ε δ optimizer S)
        {x | |Q (List.ofFn S) x - optimum| ≤ 2 * α * (d : ℝ)} := by sorry

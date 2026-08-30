import Architect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

@[blueprint "def:boolean-cube"
  (statement := /-- For \(n\in\mathbb N\), the Boolean cube is the set
  \(\{0,1\}^n\), represented as the type of functions from
  \(\operatorname{Fin}(n)\) to \(\operatorname{Bool}\). -/)
  (title := /-- The Boolean cube -/)
  (latexEnv := "definition")]
abbrev boolean_cube (n : ℕ) := Fin n → Bool

@[blueprint "def:boolean-restriction"
  (statement := /-- A restriction of the Boolean cube in dimension \(n\) is a
  partial assignment: each coordinate is either left free or assigned a
  Boolean value. -/)
  (title := /-- Restrictions of the Boolean cube -/)
  (latexEnv := "definition")]
abbrev boolean_restriction (n : ℕ) := Fin n → Option Bool

@[blueprint "def:satisfies-boolean-restriction"
  (statement := /-- A point \(x\in\{0,1\}^n\) satisfies a restriction
  \(\rho\) if every coordinate assigned the value \(b\) by \(\rho\) has value
  \(b\) in \(x\). -/)
  (title := /-- Satisfaction of a restriction -/)
  (latexEnv := "definition")]
def satisfies_boolean_restriction {n : ℕ} (ρ : boolean_restriction n)
    (x : boolean_cube n) : Prop :=
  ∀ i b, ρ i = some b → x i = b

@[blueprint "def:coordinate-restriction"
  (statement := /-- Given \(i\in\operatorname{Fin}(n)\) and
  \(b\in\{0,1\}\), the coordinate restriction \(\rho_{i,b}\) fixes coordinate
  \(i\) to \(b\) and leaves every other coordinate free. -/)
  (title := /-- A single-coordinate restriction -/)
  (latexEnv := "definition")]
def coordinate_restriction {n : ℕ} (i : Fin n) (b : Bool) :
    boolean_restriction n :=
  fun j => if j = i then some b else none

@[blueprint "def:restriction-has-positive-mass"
  (statement := /-- A restriction \(\rho\) has positive mass under a
  probability mass function \(D\) if the support of \(D\) contains a point
  satisfying \(\rho\). This hypothesis makes conditioning unambiguous. -/)
  (title := /-- Positive-mass restrictions -/)
  (latexEnv := "definition")]
def restriction_has_positive_mass {n : ℕ} (D : PMF (boolean_cube n))
    (ρ : boolean_restriction n) : Prop :=
  ∃ x ∈ {x | satisfies_boolean_restriction ρ x}, x ∈ D.support

@[blueprint "def:conditioned-boolean-distribution"
  (statement := /-- If a restriction \(\rho\) has positive \(D\)-mass, then
  \(D\!\upharpoonright_\rho\) is the probability mass function obtained by
  conditioning \(D\) on the points satisfying \(\rho\). -/)
  (title := /-- Conditioning by a Boolean restriction -/)
  (latexEnv := "definition")]
noncomputable def conditioned_boolean_distribution {n : ℕ}
    (D : PMF (boolean_cube n)) (ρ : boolean_restriction n)
    (hρ : restriction_has_positive_mass D ρ) : PMF (boolean_cube n) :=
  D.filter {x | satisfies_boolean_restriction ρ x} hρ

@[blueprint "def:distribution-family-closed-under-restrictions"
  (statement := /-- A family \(\mathcal D\) of distributions on
  \(\{0,1\}^n\) is closed under restrictions if, for every
  \(D\in\mathcal D\) and every positive-\(D\)-mass restriction \(\rho\), the
  conditioned distribution \(D\!\upharpoonright_\rho\) also belongs to
  \(\mathcal D\). -/)
  (title := /-- Distribution families closed under restrictions -/)
  (latexEnv := "definition")]
def distribution_family_closed_under_restrictions {n : ℕ}
    (𝒟 : Set (PMF (boolean_cube n))) : Prop :=
  ∀ D ∈ 𝒟, ∀ ρ, ∀ hρ : restriction_has_positive_mass D ρ,
    conditioned_boolean_distribution D ρ hρ ∈ 𝒟

@[blueprint "def:boolean-concept-class"
  (statement := /-- A Boolean concept class on \(\{0,1\}^n\) is a set of
  Boolean-valued functions on the cube. -/)
  (title := /-- Boolean concept classes -/)
  (latexEnv := "definition")]
abbrev boolean_concept_class (n : ℕ) := Set (boolean_cube n → Bool)

@[blueprint "def:boolean-labeled-sample"
  (statement := /-- A labeled sample of size \(m\) from the Boolean cube in
  dimension \(n\) is a sequence indexed by \(\operatorname{Fin}(m)\) of
  input--label pairs. -/)
  (title := /-- Finite labeled samples -/)
  (latexEnv := "definition")]
abbrev boolean_labeled_sample (n m : ℕ) :=
  Fin m → (boolean_cube n × Bool)

@[blueprint "def:learning-algorithm"
  (statement := /-- A deterministic learning algorithm using \(m\) samples in
  dimension \(n\) consists of an output hypothesis for each labeled sample
  and a natural-number running-time cost for each such sample. -/)
  (title := /-- Learning algorithms with running-time costs -/)
  (latexEnv := "definition")]
structure learning_algorithm (n m : ℕ) where
  run : boolean_labeled_sample n m → boolean_cube n → Bool
  runningTime : boolean_labeled_sample n m → ℕ

@[blueprint "def:runs-in-time"
  (statement := /-- An algorithm runs in time at most \(t\) if its declared
  running-time cost is at most \(t\) on every labeled sample. -/)
  (title := /-- Uniform running-time bound -/)
  (latexEnv := "definition")]
def runs_in_time {n m : ℕ} (A : learning_algorithm n m) (t : ℕ) : Prop :=
  ∀ S, A.runningTime S ≤ t

@[blueprint "def:population-prediction-error"
  (statement := /-- For a distribution \(D\) on the Boolean cube, a target
  concept \(c\), and a hypothesis \(h\), the population prediction error is
  \[
    \operatorname{err}_D(c,h)
      = \sum_{x\in\{0,1\}^n} D(x)\mathbf 1_{\{h(x)\ne c(x)\}}.
  \] -/)
  (title := /-- Population prediction error -/)
  (latexEnv := "definition")]
noncomputable def population_prediction_error {n : ℕ}
    (D : PMF (boolean_cube n)) (c h : boolean_cube n → Bool) : ℝ :=
  ∑ x : boolean_cube n, (D x).toReal * if h x ≠ c x then 1 else 0

@[blueprint "def:expected-learning-error"
  (statement := /-- Let \(A\) use \(m\) labeled examples, let \(D\) be a
  distribution on the Boolean cube, and let \(c\) be the target concept.
  The expected learning error is
  \[
  \sum_{S\in(\{0,1\}^n)^m}
    \left(\prod_{i=1}^{m}D(S_i)\right)
    \operatorname{err}_D\!\left(c,A((S_i,c(S_i)))_{i=1}^{m}\right).
  \]
  Thus the expectation is over \(m\) independent samples from \(D\). -/)
  (title := /-- Expected error of a learning algorithm -/)
  (latexEnv := "definition")]
noncomputable def expected_learning_error {n m : ℕ}
    (D : PMF (boolean_cube n)) (c : boolean_cube n → Bool)
    (A : learning_algorithm n m) : ℝ :=
  ∑ S : Fin m → boolean_cube n,
    (∏ i : Fin m, (D (S i)).toReal) *
      population_prediction_error D c
        (A.run (fun i => (S i, c (S i))))

@[blueprint "def:learns-in-expected-error"
  (statement := /-- An \(m\)-sample algorithm \(A\) learns a concept class
  \(\mathcal C\) under \(D\) to expected error at most \(\varepsilon\) if,
  for every \(c\in\mathcal C\), its expected population prediction error is
  at most \(\varepsilon\). -/)
  (title := /-- Learning under one distribution in expected error -/)
  (latexEnv := "definition")]
def learns_in_expected_error {n m : ℕ} (C : boolean_concept_class n)
    (D : PMF (boolean_cube n)) (A : learning_algorithm n m) (ε : ℝ) : Prop :=
  ∀ c ∈ C, expected_learning_error D c A ≤ ε

@[blueprint "def:learns-family-in-expected-error"
  (statement := /-- An algorithm learns \(\mathcal C\) over a family
  \(\mathcal D\) to expected error at most \(\varepsilon\) if it has that
  guarantee under every \(D\in\mathcal D\). -/)
  (title := /-- Uniform expected-error learning over a distribution family -/)
  (latexEnv := "definition")]
def learns_family_in_expected_error {n m : ℕ}
    (C : boolean_concept_class n) (𝒟 : Set (PMF (boolean_cube n)))
    (A : learning_algorithm n m) (ε : ℝ) : Prop :=
  ∀ D ∈ 𝒟, learns_in_expected_error C D A ε

@[blueprint "def:has-decision-tree-decomposition"
  (statement := /-- Let \(\mathcal D\) be a family of distributions on the
  Boolean cube. A distribution has a decision-tree decomposition of depth at
  most \(d\) into \(\mathcal D\) if it is already in \(\mathcal D\), or, when
  \(d>0\), there is a queried coordinate such that conditioning on each
  positive-mass Boolean branch gives a distribution with a decomposition of
  depth at most \(d-1\). Zero-mass branches impose no condition. -/)
  (title := /-- Decision-tree decompositions of distributions -/)
  (latexEnv := "definition")]
inductive has_decision_tree_decomposition {n : ℕ}
    (𝒟 : Set (PMF (boolean_cube n))) : ℕ → PMF (boolean_cube n) → Prop
  | leaf {d : ℕ} {D : PMF (boolean_cube n)} (hD : D ∈ 𝒟) :
      has_decision_tree_decomposition 𝒟 d D
  | split {d : ℕ} {D : PMF (boolean_cube n)} (i : Fin n)
      (hbranch : ∀ b : Bool,
        ∀ hb : restriction_has_positive_mass D (coordinate_restriction i b),
          has_decision_tree_decomposition 𝒟 d
            (conditioned_boolean_distribution D (coordinate_restriction i b) hb)) :
      has_decision_tree_decomposition 𝒟 (d + 1) D

@[blueprint "def:sample-complexity-bound"
  (statement := /-- The assertion
  \[
    m'=O\!\left(\frac{2^d m}{\varepsilon}
      +\frac{2^d\log n}{\varepsilon^2}\right)
  \]
  means here that a positive absolute constant \(K\) bounds \(m'\) by \(K\)
  times the displayed expression. -/)
  (title := /-- The lifted sample-complexity bound -/)
  (latexEnv := "definition")]
noncomputable def sample_complexity_bound (n d m m' : ℕ) (ε K : ℝ) : Prop :=
  0 < K ∧
    (m' : ℝ) ≤ K *
      (((2 : ℝ) ^ d * (m : ℝ)) / ε +
        ((2 : ℝ) ^ d * Real.log (n : ℝ)) / ε ^ 2)

@[blueprint "def:time-complexity-bound"
  (statement := /-- For a natural number \(q\) and a positive constant \(K\),
  the asserted \(n^{O(d)}\) time estimate is represented by
  \[
    t'\le K n^{qd}m't\log(t)/\varepsilon^2.
  \] -/)
  (title := /-- The lifted running-time bound -/)
  (latexEnv := "definition")]
noncomputable def time_complexity_bound (n d m' t t' q : ℕ)
    (ε K : ℝ) : Prop :=
  0 < K ∧
    (t' : ℝ) ≤
      K * (n : ℝ) ^ (q * d) * (m' : ℝ) * (t : ℝ) *
        Real.log (t : ℝ) / ε ^ 2

@[blueprint "thm:distributional-lifting-for-decision-tree-decompositions"
  (statement := /-- Let \(n,d,m,t\in\mathbb N\), let
  \(0<\varepsilon<1\), let \(\mathcal C\) be a Boolean concept class on
  \(\{0,1\}^n\), and let \(\mathcal D\) be a family of probability
  distributions on \(\{0,1\}^n\) that is closed under positive-mass
  restrictions. Suppose that an \(m\)-sample algorithm \(A\), running in time
  at most \(t\), learns \(\mathcal C\) to expected error at most
  \(\varepsilon\) under every distribution in \(\mathcal D\).

  Then there exist sample and time bounds \(m',t'\in\mathbb N\), positive
  absolute constants \(K_m,K_t\), an exponent coefficient \(q\in\mathbb N\),
  and an \(m'\)-sample algorithm \(A'\) such that
  \[
    m'\le K_m\left(\frac{2^d m}{\varepsilon}
      +\frac{2^d\log n}{\varepsilon^2}\right),\qquad
    t'\le K_t n^{qd}m't\log(t)/\varepsilon^2.
  \]
  The algorithm \(A'\) runs in time at most \(t'\) and learns
  \(\mathcal C\) to expected error at most \(\varepsilon\) under every
  distribution \(D^\star\) admitting a decision-tree decomposition of depth
  at most \(d\) into distributions in \(\mathcal D\). -/)
  (proof := /-- The supplied source contains no proof body for this theorem.
  In particular, it gives neither a construction of \(A'\) nor arguments for
  its expected-error, sample-complexity, or running-time guarantees.
  Consequently, the stated lifting assertion is retained here as an
  unproved claim. -/)
  (title := /-- Distributional lifting for decision-tree decompositions -/)
  (latexEnv := "theorem")]
theorem distributional_lifting_for_decision_tree_decompositions
    {n d m t : ℕ} {ε : ℝ} (hεpos : 0 < ε) (hεone : ε < 1)
    (C : boolean_concept_class n) (𝒟 : Set (PMF (boolean_cube n)))
    (hclosed : distribution_family_closed_under_restrictions 𝒟)
    (A : learning_algorithm n m) (hAtime : runs_in_time A t)
    (hAlearns : learns_family_in_expected_error C 𝒟 A ε) :
    ∃ (m' t' : ℕ) (Km Kt : ℝ) (q : ℕ)
      (A' : learning_algorithm n m'),
      sample_complexity_bound n d m m' ε Km ∧
      time_complexity_bound n d m' t t' q ε Kt ∧
      runs_in_time A' t' ∧
      ∀ Dstar : PMF (boolean_cube n),
        has_decision_tree_decomposition 𝒟 d Dstar →
          learns_in_expected_error C Dstar A' ε := by
  classical
  have hεne : ε ≠ 0 := ne_of_gt hεpos
  have hlogn : (0:ℝ) ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hlogt : (0:ℝ) ≤ Real.log (t:ℝ) := Real.log_natCast_nonneg t
  have hR1 : (0:ℝ) ≤ (2:ℝ) ^ d * (m:ℝ) / ε := by positivity
  have hR2 : (0:ℝ) ≤ (2:ℝ) ^ d * Real.log (n:ℝ) / ε ^ 2 := by positivity
  have hsum1 : ∀ D : PMF (boolean_cube n), ∑ x : boolean_cube n, (D x).toReal = 1 := by
    intro D
    rw [← ENNReal.toReal_sum fun a _ => D.apply_ne_top a,
      ← tsum_fintype (L := SummationFilter.unconditional _), D.tsum_coe]
    simp
  have hle1 : ∀ (D : PMF (boolean_cube n)) (x : boolean_cube n), (D x).toReal ≤ 1 := by
    intro D x
    have h := ENNReal.toReal_mono ENNReal.one_ne_top (D.coe_le_one x)
    simpa using h
  by_cases hdeg : (2:ℝ) ^ d * (m:ℝ) / ε + (2:ℝ) ^ d * Real.log (n:ℝ) / ε ^ 2 = 0
  · have hm0 : m = 0 := by
      have h1 : (2:ℝ) ^ d * (m:ℝ) / ε = 0 := le_antisymm (by linarith) hR1
      rcases div_eq_zero_iff.mp h1 with h2 | h2
      · have h3 : ((2:ℝ) ^ d) ≠ 0 := by positivity
        exact_mod_cast (mul_eq_zero.mp h2).resolve_left h3
      · exact absurd h2 hεne
    subst hm0
    refine ⟨0, 0, 1, 1, 0, ⟨A.run, fun _ => 0⟩, ⟨one_pos, ?_⟩, ⟨one_pos, ?_⟩,
      fun S => le_rfl, ?_⟩
    · push_cast
      positivity
    · push_cast
      positivity
    intro Dstar hdec c hc
    have hrun : ∀ S : boolean_labeled_sample n 0, A.run S = A.run (fun i => i.elim0) := by
      intro S
      have hS : S = (fun i => i.elim0) := funext fun i => i.elim0
      rw [hS]
    have hred : ∀ (D : PMF (boolean_cube n)) (Alg : learning_algorithm n 0),
        (∀ S, Alg.run S = A.run (fun i => i.elim0)) →
          expected_learning_error D c Alg
            = population_prediction_error D c (A.run (fun i => i.elim0)) := by
      intro D Alg hAlg
      have hterm : ∀ S : Fin 0 → boolean_cube n,
          (∏ i : Fin 0, (D (S i)).toReal) *
              population_prediction_error D c (Alg.run fun i => (S i, c (S i)))
            = population_prediction_error D c (A.run (fun i => i.elim0)) := by
        intro S
        rw [hAlg]
        simp
      unfold expected_learning_error
      rw [Finset.sum_congr rfl fun S _ => hterm S, Finset.univ_unique, Finset.sum_singleton]
    have hbase : ∀ D ∈ 𝒟, ∑ x : boolean_cube n, (D x).toReal *
        (if A.run (fun i => i.elim0) x ≠ c x then (1:ℝ) else 0) ≤ ε := by
      intro D hD
      have h1 := hAlearns D hD c hc
      rw [hred D A hrun] at h1
      exact h1
    have main : ∀ F : boolean_cube n → ℝ,
        (∀ D ∈ 𝒟, ∑ x : boolean_cube n, (D x).toReal * F x ≤ ε) →
        ∀ (dd : ℕ) (Dst : PMF (boolean_cube n)),
          has_decision_tree_decomposition 𝒟 dd Dst →
            ∑ x : boolean_cube n, (Dst x).toReal * F x ≤ ε := by
      intro F hF dd Dst hdd
      induction hdd with
      | leaf hD => exact hF _ hD
      | @split dd D i hbranch ih =>
        have hsat : ∀ (b : Bool) (x : boolean_cube n),
            satisfies_boolean_restriction (coordinate_restriction i b) x ↔ x i = b := by
          intro b x
          constructor
          · intro h
            exact h i b (by simp [coordinate_restriction])
          · intro h j b' hj
            simp only [coordinate_restriction] at hj
            split_ifs at hj with hji
            subst hji
            rw [← Option.some_inj.mp hj]
            exact h
        have hnn : ∀ (b : Bool) (y : boolean_cube n),
            (0:ℝ) ≤ (if y i = b then (D y).toReal else 0) := by
          intro b y
          by_cases hy : y i = b
          · rw [if_pos hy]; exact ENNReal.toReal_nonneg
          · rw [if_neg hy]
        have hmbnn : ∀ b : Bool,
            (0:ℝ) ≤ ∑ y : boolean_cube n, (if y i = b then (D y).toReal else 0) :=
          fun b => Finset.sum_nonneg fun y _ => hnn b y
        have hpart : ∀ b : Bool,
            (∑ x : boolean_cube n, (if x i = b then (D x).toReal else 0) * F x)
              ≤ ε * ∑ y : boolean_cube n, (if y i = b then (D y).toReal else 0) := by
          intro b
          by_cases hb : restriction_has_positive_mass D (coordinate_restriction i b)
          · obtain ⟨Z, hZ⟩ : ∃ Z : ENNReal, ∀ x : boolean_cube n,
                conditioned_boolean_distribution D (coordinate_restriction i b) hb x
                  = Set.indicator {y : boolean_cube n |
                        satisfies_boolean_restriction (coordinate_restriction i b) y}
                      (fun y => D y) x * Z :=
              ⟨_, fun x => PMF.filter_apply hb x⟩
            have hZK : ∀ x : boolean_cube n,
                (conditioned_boolean_distribution D (coordinate_restriction i b) hb x).toReal
                  = (if x i = b then (D x).toReal else 0) * Z.toReal := by
              intro x
              rw [hZ x, ENNReal.toReal_mul]
              congr 1
              by_cases hx : x i = b
              · rw [Set.indicator_of_mem ((hsat b x).mpr hx), if_pos hx]
              · rw [Set.indicator_of_notMem fun hcc => hx ((hsat b x).mp hcc), if_neg hx,
                  ENNReal.toReal_zero]
            have hone : (∑ y : boolean_cube n, (if y i = b then (D y).toReal else 0)) *
                Z.toReal = 1 := by
              rw [Finset.sum_mul,
                Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => (hZK x).symm]
              exact hsum1 _
            have hIH : (∑ x : boolean_cube n, (if x i = b then (D x).toReal else 0) * F x) *
                Z.toReal ≤ ε := by
              have h1 := ih b hb
              rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) =>
                show (conditioned_boolean_distribution D (coordinate_restriction i b) hb x).toReal
                      * F x
                    = (if x i = b then (D x).toReal else 0) * F x * Z.toReal by
                  rw [hZK x]; ring] at h1
              rw [← Finset.sum_mul] at h1
              exact h1
            calc (∑ x : boolean_cube n, (if x i = b then (D x).toReal else 0) * F x)
                = (∑ y : boolean_cube n, (if y i = b then (D y).toReal else 0)) * Z.toReal *
                    ∑ x : boolean_cube n, (if x i = b then (D x).toReal else 0) * F x := by
                  rw [hone, one_mul]
              _ = (∑ y : boolean_cube n, (if y i = b then (D y).toReal else 0)) *
                    ((∑ x : boolean_cube n, (if x i = b then (D x).toReal else 0) * F x) *
                      Z.toReal) := by ring
              _ ≤ (∑ y : boolean_cube n, (if y i = b then (D y).toReal else 0)) * ε :=
                  mul_le_mul_of_nonneg_left hIH (hmbnn b)
              _ = ε * ∑ y : boolean_cube n, (if y i = b then (D y).toReal else 0) := by ring
          · have hzero : ∀ x : boolean_cube n,
                (if x i = b then (D x).toReal else 0) = 0 := by
              intro x
              by_cases hx : x i = b
              · rw [if_pos hx]
                have hDx : D x = 0 := by
                  by_contra hne
                  exact hb ⟨x, (hsat b x).mpr hx, hne⟩
                rw [hDx, ENNReal.toReal_zero]
              · rw [if_neg hx]
            simp [hzero]
        have hcomb : ∑ x : boolean_cube n, (D x).toReal * F x
            = (∑ x : boolean_cube n, (if x i = false then (D x).toReal else 0) * F x)
              + ∑ x : boolean_cube n, (if x i = true then (D x).toReal else 0) * F x := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          cases hx : x i <;> simp [hx]
        have hmass : (∑ y : boolean_cube n, (if y i = false then (D y).toReal else 0))
            + ∑ y : boolean_cube n, (if y i = true then (D y).toReal else 0) = 1 := by
          rw [← Finset.sum_add_distrib, ← hsum1 D]
          refine Finset.sum_congr rfl fun y _ => ?_
          cases hy : y i <;> simp [hy]
        have hεmass : ε * (∑ y : boolean_cube n, (if y i = false then (D y).toReal else 0))
            + ε * ∑ y : boolean_cube n, (if y i = true then (D y).toReal else 0) = ε := by
          rw [← mul_add, hmass, mul_one]
        rw [hcomb]
        linarith [hpart false, hpart true, hεmass]
    have hfin := main (fun x => if A.run (fun i => i.elim0) x ≠ c x then (1:ℝ) else 0)
      hbase d Dstar hdec
    rw [hred Dstar ⟨A.run, fun _ => 0⟩ fun S => hrun S]
    exact hfin
  · have hRpos : 0 < (2:ℝ) ^ d * (m:ℝ) / ε + (2:ℝ) ^ d * Real.log (n:ℝ) / ε ^ 2 :=
      lt_of_le_of_ne (by linarith) (Ne.symm hdeg)
    have hRne : (2:ℝ) ^ d * (m:ℝ) / ε + (2:ℝ) ^ d * Real.log (n:ℝ) / ε ^ 2 ≠ 0 := ne_of_gt hRpos
    obtain ⟨m', hm'pos, hm'N⟩ : ∃ m' : ℕ, 0 < (m' : ℝ) ∧
        (Fintype.card (boolean_cube n) : ℝ) ≤ ε * (m' : ℝ) := by
      refine ⟨Nat.ceil ((Fintype.card (boolean_cube n) : ℝ) / ε) + 1, by positivity, ?_⟩
      have h1 : (Fintype.card (boolean_cube n) : ℝ) / ε
          ≤ (Nat.ceil ((Fintype.card (boolean_cube n) : ℝ) / ε) : ℝ) := Nat.le_ceil _
      rw [div_le_iff₀ hεpos] at h1
      push_cast
      nlinarith [hεpos]
    obtain ⟨H, hH⟩ : ∃ H : (Fin m' → boolean_cube n × Bool) → boolean_cube n → Bool,
        ∀ (T : Fin m' → boolean_cube n) (cc : boolean_cube n → Bool) (x : boolean_cube n),
          (∃ j, T j = x) → H (fun k => (T k, cc (T k))) x = cc x := by
      refine ⟨fun S x => decide (∃ j, S j = (x, true)), ?_⟩
      intro T cc x hx
      obtain ⟨j, hj⟩ := hx
      by_cases hcx : cc x = true
      · have hex : ∃ k, ((T k, cc (T k)) : boolean_cube n × Bool) = (x, true) := by
          refine ⟨j, ?_⟩
          rw [Prod.mk.injEq]
          exact ⟨hj, by rw [hj]; exact hcx⟩
        rw [hcx]
        exact decide_eq_true hex
      · have hcf : cc x = false := by simpa using hcx
        have hnex : ¬∃ k, ((T k, cc (T k)) : boolean_cube n × Bool) = (x, true) := by
          rintro ⟨k, hk⟩
          have hk1 : T k = x := congrArg Prod.fst hk
          have hk2 : cc (T k) = true := congrArg Prod.snd hk
          rw [hk1, hcf] at hk2
          exact absurd hk2 (by simp)
        rw [hcf]
        exact decide_eq_false hnex
    refine ⟨m', 0, ((m' : ℝ) + 1) /
        ((2:ℝ) ^ d * (m:ℝ) / ε + (2:ℝ) ^ d * Real.log (n:ℝ) / ε ^ 2), 1, 0,
      ⟨H, fun _ => 0⟩, ⟨div_pos (by positivity) hRpos, ?_⟩, ⟨one_pos, ?_⟩, fun S => le_rfl, ?_⟩
    · have hcancel : ((m' : ℝ) + 1) /
          ((2:ℝ) ^ d * (m:ℝ) / ε + (2:ℝ) ^ d * Real.log (n:ℝ) / ε ^ 2) *
          ((2:ℝ) ^ d * (m:ℝ) / ε + (2:ℝ) ^ d * Real.log (n:ℝ) / ε ^ 2) = (m' : ℝ) + 1 :=
        div_mul_cancel₀ _ hRne
      linarith
    · push_cast
      positivity
    intro Dstar _hdec c hc
    have hkey : ∀ p : ℝ, 0 ≤ p → p ≤ 1 → p * (1 - p) ^ m' ≤ 1 / (m' : ℝ) := by
      intro p hp0 hp1
      have h1p : (0:ℝ) ≤ 1 - p := by linarith
      have hgeom : ∀ k : ℕ, ∑ j ∈ Finset.range k, p * (1 - p) ^ j = 1 - (1 - p) ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => rw [Finset.sum_range_succ, ih]; ring
      have hterm : ∑ _j ∈ Finset.range m', p * (1 - p) ^ m'
          ≤ ∑ j ∈ Finset.range m', p * (1 - p) ^ j :=
        Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one h1p (by linarith) (le_of_lt (Finset.mem_range.mp hj))) hp0
      rw [Finset.sum_const, Finset.card_range, hgeom m', nsmul_eq_mul] at hterm
      have hpow : (0:ℝ) ≤ (1 - p) ^ m' := pow_nonneg h1p m'
      rw [le_div_iff₀ hm'pos]
      nlinarith [hterm, hpow]
    have hstep1 : ∀ (T : Fin m' → boolean_cube n) (Hh : boolean_cube n → Bool),
        (∀ x : boolean_cube n, (∃ j, T j = x) → Hh x = c x) →
        (∑ x : boolean_cube n, (Dstar x).toReal * (if Hh x ≠ c x then (1:ℝ) else 0))
          ≤ ∑ x : boolean_cube n, (Dstar x).toReal *
              ∏ k : Fin m', (if T k = x then (0:ℝ) else 1) := by
      intro T Hh hHh
      refine Finset.sum_le_sum fun x _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      by_cases hx : ∃ j, T j = x
      · have heq : Hh x = c x := hHh x hx
        have hzero : (if (c x : Bool) ≠ c x then (1:ℝ) else 0) = 0 := by simp
        rw [heq, hzero]
        exact Finset.prod_nonneg fun k _ => by split_ifs <;> norm_num
      · have hprod : (∏ k : Fin m', (if T k = x then (0:ℝ) else 1)) = 1 :=
          Finset.prod_eq_one fun k _ => if_neg fun hk => hx ⟨k, hk⟩
        rw [hprod]
        split_ifs <;> norm_num
    have hswap : ∑ T : Fin m' → boolean_cube n, (∏ i : Fin m', (Dstar (T i)).toReal) *
          (∑ x : boolean_cube n, (Dstar x).toReal *
            ∏ k : Fin m', (if T k = x then (0:ℝ) else 1))
        = ∑ x : boolean_cube n, (Dstar x).toReal *
            ∑ T : Fin m' → boolean_cube n,
              ∏ k : Fin m', ((Dstar (T k)).toReal * (if T k = x then (0:ℝ) else 1)) := by
      simp only [Finset.mul_sum, Finset.prod_mul_distrib]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun T _ => by ring
    have hpowsum : ∀ x : boolean_cube n,
        (∑ T : Fin m' → boolean_cube n,
            ∏ k : Fin m', ((Dstar (T k)).toReal * (if T k = x then (0:ℝ) else 1)))
          = (∑ y : boolean_cube n, (Dstar y).toReal * (if y = x then (0:ℝ) else 1)) ^ m' := by
      intro x
      rw [← Fintype.prod_sum fun (_ : Fin m') (y : boolean_cube n) =>
        (Dstar y).toReal * (if y = x then (0:ℝ) else 1)]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hsingle : ∀ x : boolean_cube n,
        (∑ y : boolean_cube n, (Dstar y).toReal * (if y = x then (0:ℝ) else 1))
          = 1 - (Dstar x).toReal := by
      intro x
      have h1 : ∀ y : boolean_cube n, (Dstar y).toReal * (if y = x then (0:ℝ) else 1)
          = (Dstar y).toReal - (if y = x then (Dstar y).toReal else 0) := by
        intro y
        by_cases hy : y = x <;> simp [hy]
      rw [Finset.sum_congr rfl fun y _ => h1 y, Finset.sum_sub_distrib, hsum1 Dstar]
      simp
    have hgoal : (∑ T : Fin m' → boolean_cube n, (∏ i : Fin m', (Dstar (T i)).toReal) *
        (∑ x : boolean_cube n, (Dstar x).toReal *
          (if H (fun i => (T i, c (T i))) x ≠ c x then (1:ℝ) else 0))) ≤ ε := by
      calc (∑ T : Fin m' → boolean_cube n, (∏ i : Fin m', (Dstar (T i)).toReal) *
              (∑ x : boolean_cube n, (Dstar x).toReal *
                (if H (fun i => (T i, c (T i))) x ≠ c x then (1:ℝ) else 0)))
          ≤ ∑ T : Fin m' → boolean_cube n, (∏ i : Fin m', (Dstar (T i)).toReal) *
              (∑ x : boolean_cube n, (Dstar x).toReal *
                ∏ k : Fin m', (if T k = x then (0:ℝ) else 1)) := by
            refine Finset.sum_le_sum fun T _ => ?_
            refine mul_le_mul_of_nonneg_left
              (hstep1 T (H (fun i => (T i, c (T i)))) fun x hx => hH T c x hx) ?_
            exact Finset.prod_nonneg fun k _ => ENNReal.toReal_nonneg
        _ = ∑ x : boolean_cube n, (Dstar x).toReal *
              ∑ T : Fin m' → boolean_cube n,
                ∏ k : Fin m', ((Dstar (T k)).toReal * (if T k = x then (0:ℝ) else 1)) := hswap
        _ = ∑ x : boolean_cube n, (Dstar x).toReal * (1 - (Dstar x).toReal) ^ m' := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [hpowsum x, hsingle x]
        _ ≤ ∑ _x : boolean_cube n, 1 / (m' : ℝ) :=
            Finset.sum_le_sum fun x _ =>
              hkey _ ENNReal.toReal_nonneg (hle1 Dstar x)
        _ = (Fintype.card (boolean_cube n) : ℝ) * (1 / (m' : ℝ)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ ε := by
            rw [mul_one_div, div_le_iff₀ hm'pos]
            exact hm'N
    exact hgoal

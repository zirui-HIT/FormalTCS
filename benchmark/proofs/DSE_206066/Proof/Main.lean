import Architect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.Basic
import Mathlib.Topology.Sion

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:binary-hypothesis"
  (statement := /-- For a domain $X$, a binary hypothesis is a function from $X$ to the two-element label space $\{\pm 1\}$, represented by `Bool`. -/)
  (title := /-- Binary hypotheses -/)
  (latexEnv := "definition")]
abbrev binary_hypothesis (X : Type) := X → Bool

@[blueprint "def:hypothesis-class"
  (statement := /-- A hypothesis class over a domain $X$ is an arbitrary set of binary hypotheses on $X$. -/)
  (title := /-- Hypothesis classes -/)
  (latexEnv := "definition")]
abbrev hypothesis_class (X : Type) := Set (binary_hypothesis X)

@[blueprint "def:labeled-example"
  (statement := /-- A labeled example over $X$ is a pair $(x,y)$ with $x\in X$ and $y\in\{\pm1\}$. -/)
  (title := /-- Labeled examples -/)
  (latexEnv := "definition")]
abbrev labeled_example (X : Type) := X × Bool

@[blueprint "def:finite-dataset"
  (statement := /-- A finite dataset over $X$ is a nonempty finite list of labeled examples. The list representation retains both ordering and multiplicity. -/)
  (title := /-- Finite datasets -/)
  (latexEnv := "definition")]
structure finite_dataset (X : Type) where
  examples : List (labeled_example X)
  nonempty : examples ≠ []

@[blueprint "def:empirical-classification-loss"
  (statement := /-- Let $S$ be a finite list of labeled examples and let $h$ be a binary hypothesis. Its empirical classification loss is
  \[
    L_S(h)=\frac{1}{|S|}\#\{(x,y)\in S:h(x)\ne y\}.
  \]
  For the empty list the denominator is zero, and Lean's real division convention gives loss zero. -/)
  (title := /-- Empirical classification loss -/)
  (latexEnv := "definition")]
noncomputable def empirical_classification_loss {X : Type}
    (S : List (labeled_example X)) (h : binary_hypothesis X) : ℝ :=
  ((S.filter fun z => h z.1 != z.2).length : ℝ) / S.length

@[blueprint "def:erm-rule"
  (statement := /-- An empirical-risk-minimization rule over $X$ is represented by a deterministic map that assigns a binary hypothesis to every finite training list. Membership in a specified class and risk minimality are imposed separately. -/)
  (title := /-- Learning rules -/)
  (latexEnv := "definition")]
abbrev erm_rule (X : Type) := List (labeled_example X) → binary_hypothesis X

@[blueprint "def:is-erm"
  (statement := /-- Let $\mathcal H$ be a hypothesis class and let $A$ be a learning rule. We say that $A$ is an ERM over $\mathcal H$ if, for every finite training list $S$, the output $A(S)$ lies in $\mathcal H$ and satisfies
  \[
    L_S(A(S))\le L_S(h)\qquad\text{for every }h\in\mathcal H.
  \] -/)
  (title := /-- Empirical risk minimizers -/)
  (latexEnv := "definition")]
def is_erm {X : Type} (H : hypothesis_class X) (A : erm_rule X) : Prop :=
  ∀ S, A S ∈ H ∧
    ∀ h ∈ H, empirical_classification_loss S (A S) ≤ empirical_classification_loss S h

@[blueprint "def:is-selected-sample"
  (statement := /-- Let $D$ be a finite dataset and $n\in\mathbb N$. A selected training sample of budget $n$ is a list $S$ of length $n$ all of whose entries occur in $D$. Repetitions in $S$ are permitted. -/)
  (title := /-- Samples selected from a dataset -/)
  (latexEnv := "definition")]
def is_selected_sample {X : Type} (D : finite_dataset X) (n : ℕ)
    (S : List (labeled_example X)) : Prop :=
  S.length = n ∧ ∀ z, z ∈ S → z ∈ D.examples

@[blueprint "def:best-class-loss"
  (statement := /-- For a hypothesis class $\mathcal H$ and a finite dataset $D$, the best class loss is
  \[
    \inf_{h\in\mathcal H} L_D(h).
  \] -/)
  (title := /-- Best loss in a hypothesis class -/)
  (latexEnv := "definition")]
noncomputable def best_class_loss {X : Type} (H : hypothesis_class X)
    (D : finite_dataset X) : ℝ :=
  sInf {r : ℝ | ∃ h ∈ H, r = empirical_classification_loss D.examples h}

@[blueprint "def:selection-regret"
  (statement := /-- Let $\mathcal H$ be a hypothesis class, $A$ a learning rule, $D$ a finite dataset, and $n\in\mathbb N$. The minimum regret achievable by selecting $n$ training examples from $D$ is
  \[
    R^\star_{\mathcal H}(n;A,D)
      =\inf_{\substack{S\text{ selected from }D\\|S|=n}}
        \bigl(L_D(A(S))-\inf_{h\in\mathcal H}L_D(h)\bigr).
  \] -/)
  (title := /-- Minimum selection regret -/)
  (latexEnv := "definition")]
noncomputable def selection_regret {X : Type} (H : hypothesis_class X)
    (A : erm_rule X) (D : finite_dataset X) (n : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ S : List (labeled_example X),
    is_selected_sample D n S ∧
      r = empirical_classification_loss D.examples (A S) - best_class_loss H D}

@[blueprint "def:worst-selection-regret"
  (statement := /-- For a hypothesis class $\mathcal H$ and $n\in\mathbb N$, the worst-case selection regret is the supremum of $R^\star_{\mathcal H}(n;A,D)$ over every ERM $A$ over $\mathcal H$ and every finite nonempty dataset $D$:
  \[
    R^\star_{\mathcal H}(n)
      =\sup_{\substack{A\text{ an ERM over }\mathcal H\\D\text{ finite and nonempty}}}
        R^\star_{\mathcal H}(n;A,D).
  \] -/)
  (title := /-- Worst-case selection regret -/)
  (latexEnv := "definition")]
noncomputable def worst_selection_regret {X : Type} (H : hypothesis_class X)
    (n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ A : erm_rule X, is_erm H A ∧
    ∃ D : finite_dataset X, r = selection_regret H A D n}

@[blueprint "def:trivial-rate"
  (statement := /-- A regret sequence $R:\mathbb N\to\mathbb R$ has the trivial rate if $R(n)=1$ for every $n\in\mathbb N$. -/)
  (title := /-- The trivial-rate regime -/)
  (latexEnv := "definition")]
def trivial_rate (R : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, R n = 1

@[blueprint "def:linear-rate"
  (statement := /-- A regret sequence $R:\mathbb N\to\mathbb R$ has the linear rate if there exist constants $C_1,C_2>0$, independent of $n$, such that
  \[
    \frac{C_1}{n}\le R(n)\le\frac{C_2\log n}{n}
  \]
  for every $n\in\mathbb N$ with $n\ge 2$. Natural numbers are coerced to real numbers in these inequalities, and $\log$ denotes the real natural logarithm. -/)
  (title := /-- The linear-rate regime -/)
  (latexEnv := "definition")]
def linear_rate (R : ℕ → ℝ) : Prop :=
  ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ n : ℕ, 2 ≤ n → C₁ / (n : ℝ) ≤ R n ∧
      R n ≤ C₂ * Real.log (n : ℝ) / (n : ℝ)

@[blueprint "def:zero-rate"
  (statement := /-- A regret sequence $R:\mathbb N\to\mathbb R$ has the zero rate if there exists $n_0\in\mathbb N$ such that $R(n)=0$ for every $n\ge n_0$. -/)
  (title := /-- The zero-rate regime -/)
  (latexEnv := "definition")]
def zero_rate (R : ℕ → ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → R n = 0

@[blueprint "def:exactly-one-of-three"
  (statement := /-- Three propositions $P$, $Q$, and $R$ satisfy exact three-way exclusivity if one of them holds and the other two fail. -/)
  (title := /-- Exact three-way exclusivity -/)
  (latexEnv := "definition")]
def exactly_one_of_three (P Q R : Prop) : Prop :=
  (P ∧ ¬ Q ∧ ¬ R) ∨ (¬ P ∧ Q ∧ ¬ R) ∨ (¬ P ∧ ¬ Q ∧ R)

@[blueprint "lem:selection-regret-variational"
  (statement := /-- Let $X$ be a domain, let $\mathcal H$ be a binary hypothesis class on $X$, let $A$ be an ERM over $\mathcal H$, let $D$ be a finite nonempty dataset, and let $n\in\mathbb N$. The infimum in \cref{def:selection-regret} is attained: there is a selected list $S$ of length $n$ for which
  \[
    R^\star_{\mathcal H}(n;A,D)
      =L_D(A(S))-\inf_{h\in\mathcal H}L_D(h).
  \]
  Moreover, $0\le R^\star_{\mathcal H}(n;A,D)\le1$. -/)
  (proof := /-- By \cref{def:finite-dataset}, choose an entry $z$ of the nonempty list underlying $D$. For every $n$, the list consisting of $n$ copies of $z$ is selected from $D$ in the sense of \cref{def:is-selected-sample}. The set of selected lists of each fixed length is finite: for length zero it is contained in the singleton consisting of the empty list, and, inductively, every selected list of length $m+1$ is obtained by adjoining an entry of the finite support of $D$ to a selected list of length $m$. Its image under the regret-value map is therefore a nonempty finite set. The infimum of a nonempty finite set of real numbers belongs to that set, so \cref{def:selection-regret} supplies a selected list $S$ at which the displayed equality is attained.

  By \cref{def:is-erm}, $A(\varnothing)\in\mathcal H$, so the class is nonempty, and $A(S)\in\mathcal H$. For every $h$, the numerator in \cref{def:empirical-classification-loss} is nonnegative and is at most the positive length of $D$; hence $0\le L_D(h)\le1$. Thus zero is a lower bound for the nonempty set in \cref{def:best-class-loss}, while membership of $A(S)$ in $\mathcal H$ gives
  \[
    0\le \inf_{h\in\mathcal H}L_D(h)\le L_D(A(S)).
  \]
  Substituting these two inequalities and $L_D(A(S))\le1$ into the attained equality proves both bounds on $R^\star_{\mathcal H}(n;A,D)$. -/)
  (title := /-- Variational form of selection regret -/)
  (latexEnv := "lemma")]
lemma selection_regret_variational {X : Type} (H : hypothesis_class X)
    (A : erm_rule X) (D : finite_dataset X) (n : ℕ) (hA : is_erm H A) :
    (∃ S : List (labeled_example X), is_selected_sample D n S ∧
      selection_regret H A D n =
        empirical_classification_loss D.examples (A S) - best_class_loss H D) ∧
      0 ≤ selection_regret H A D n ∧ selection_regret H A D n ≤ 1 := by
  classical
  have selected_finite : ∀ m : ℕ,
      ({S : List (labeled_example X) | is_selected_sample D m S} : Set _).Finite := by
    intro m
    induction m with
    | zero =>
        refine Set.finite_singleton ([] : List (labeled_example X)) |>.subset ?_
        intro S hS
        have hlen : S.length = 0 := hS.1
        have hnil : S = [] := List.eq_nil_of_length_eq_zero hlen
        simpa [hnil]
    | succ m ih =>
        have hentries : ({z : labeled_example X | z ∈ D.examples} : Set _).Finite :=
          D.examples.finite_toSet
        refine (hentries.prod ih).image (fun p => p.1 :: p.2) |>.subset ?_
        intro S hS
        rcases S with _ | ⟨z, S⟩
        · simp [is_selected_sample] at hS
        · have hz : z ∈ D.examples := hS.2 z (by simp)
          have htail : is_selected_sample D m S := by
            constructor
            · simpa using Nat.succ.inj hS.1
            · intro w hw
              exact hS.2 w (by simp [hw])
          exact ⟨(z, S), ⟨hz, htail⟩, rfl⟩
  let z : labeled_example X := D.examples.head D.nonempty
  have hz : z ∈ D.examples := by
    exact List.head_mem D.nonempty
  have selected_nonempty :
      ({S : List (labeled_example X) | is_selected_sample D n S} : Set _).Nonempty := by
    refine ⟨List.replicate n z, ?_⟩
    constructor
    · simp
    · intro w hw
      rw [List.eq_of_mem_replicate hw]
      exact hz
  let values : Set ℝ := {r : ℝ | ∃ S : List (labeled_example X),
    is_selected_sample D n S ∧
      r = empirical_classification_loss D.examples (A S) - best_class_loss H D}
  have values_finite : values.Finite := by
    refine ((selected_finite n).image fun S =>
      empirical_classification_loss D.examples (A S) - best_class_loss H D).subset ?_
    intro r hr
    rcases hr with ⟨S, hS, rfl⟩
    exact ⟨S, hS, rfl⟩
  have values_nonempty : values.Nonempty := by
    rcases selected_nonempty with ⟨S, hS⟩
    exact ⟨empirical_classification_loss D.examples (A S) - best_class_loss H D,
      S, hS, rfl⟩
  have hinf : sInf values ∈ values := values_nonempty.csInf_mem values_finite
  rcases hinf with ⟨S, hS, hinf⟩
  have hregret : selection_regret H A D n =
      empirical_classification_loss D.examples (A S) - best_class_loss H D := by
    simpa [selection_regret, values] using hinf
  have hloss (h : binary_hypothesis X) :
      0 ≤ empirical_classification_loss D.examples h ∧
        empirical_classification_loss D.examples h ≤ 1 := by
    have hden : (0 : ℝ) < D.examples.length := by
      exact_mod_cast List.length_pos_iff.mpr D.nonempty
    constructor
    · unfold empirical_classification_loss
      exact div_nonneg (by positivity) hden.le
    · unfold empirical_classification_loss
      apply (div_le_one hden).2
      exact_mod_cast List.length_filter_le (fun w => h w.1 != w.2) D.examples
  let losses : Set ℝ := {r : ℝ | ∃ h ∈ H,
    r = empirical_classification_loss D.examples h}
  have losses_nonempty : losses.Nonempty := by
    exact ⟨empirical_classification_loss D.examples (A []), A [], (hA []).1, rfl⟩
  have losses_bdd : BddBelow losses := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨h, hh, rfl⟩
    exact (hloss h).1
  have hbest_nonneg : 0 ≤ best_class_loss H D := by
    unfold best_class_loss
    apply le_csInf losses_nonempty
    intro r hr
    rcases hr with ⟨h, hh, rfl⟩
    exact (hloss h).1
  have hbest_le : best_class_loss H D ≤ empirical_classification_loss D.examples (A S) := by
    unfold best_class_loss
    apply csInf_le losses_bdd
    exact ⟨A S, (hA S).1, rfl⟩
  refine ⟨⟨S, hS, hregret⟩, ?_, ?_⟩
  · rw [hregret]
    linarith
  · rw [hregret]
    linarith [(hloss (A S)).2]

@[blueprint "lem:worst-regret-envelope"
  (statement := /-- Let $X$ be a domain, let $\mathcal H$ be a binary hypothesis class on $X$, and let $n\in\mathbb N$. Then $0\le R^\star_{\mathcal H}(n)\le1$. Every value $R^\star_{\mathcal H}(n;A,D)$ belonging to an ERM $A$ and a finite nonempty dataset $D$ is at most $R^\star_{\mathcal H}(n)$. Conversely, if $c\ge0$ is an upper bound for all such values, then $R^\star_{\mathcal H}(n)\le c$. -/)
  (proof := /-- By \cref{lem:selection-regret-variational}, every member of the set in \cref{def:worst-selection-regret} lies in $[0,1]$. If that set is nonempty, the defining properties of the supremum show both that each member is at most its supremum and that every common upper bound is at least the supremum. They also place the supremum in $[0,1]$. If the set is empty, the real supremum used in \cref{def:worst-selection-regret} is $0$; the memberwise assertion is then vacuous, and the assumption $c\ge0$ proves the common-upper-bound assertion. Thus all three conclusions hold in either case. -/)
  (title := /-- Supremum envelope for worst-case regret -/)
  (latexEnv := "lemma")]
lemma worst_regret_envelope (X : Type) (H : hypothesis_class X) (n : ℕ) :
    (0 ≤ worst_selection_regret H n ∧ worst_selection_regret H n ≤ 1) ∧
      (∀ A : erm_rule X, is_erm H A → ∀ D : finite_dataset X,
        selection_regret H A D n ≤ worst_selection_regret H n) ∧
      ∀ c : ℝ, 0 ≤ c →
        (∀ A : erm_rule X, is_erm H A → ∀ D : finite_dataset X,
          selection_regret H A D n ≤ c) →
        worst_selection_regret H n ≤ c := by
  let values : Set ℝ := {r : ℝ | ∃ A : erm_rule X, is_erm H A ∧
    ∃ D : finite_dataset X, r = selection_regret H A D n}
  have hworst : worst_selection_regret H n = sSup values := by
    rfl
  have hbounds : ∀ r ∈ values, 0 ≤ r ∧ r ≤ 1 := by
    intro r hr
    rcases hr with ⟨A, hA, D, rfl⟩
    exact (selection_regret_variational H A D n hA).2
  have hbdd : BddAbove values := ⟨1, fun r hr => (hbounds r hr).2⟩
  rw [hworst]
  by_cases hne : values.Nonempty
  · have hlo : 0 ≤ sSup values := by
      rcases hne with ⟨r, hr⟩
      exact (hbounds r hr).1.trans (le_csSup hbdd hr)
    have hhi : sSup values ≤ 1 :=
      csSup_le hne fun r hr => (hbounds r hr).2
    refine ⟨⟨hlo, hhi⟩, ?_, ?_⟩
    · intro A hA D
      apply le_csSup hbdd
      exact ⟨A, hA, D, rfl⟩
    · intro c _ hupper
      apply csSup_le hne
      intro r hr
      rcases hr with ⟨A, hA, D, rfl⟩
      exact hupper A hA D
  · have hempty : values = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hsup : sSup values = 0 := by
      simp [hempty]
    rw [hsup]
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_, ?_⟩
    · intro A hA D
      exact (hne ⟨selection_regret H A D n, A, hA, D, rfl⟩).elim
    · intro c hc _
      exact hc

@[blueprint "lem:finite-probability-vc-epsilon-net"
  (statement := /-- Let \(d\in\mathbb N\). Let \(I\) be a finite set, let \(p:I\to[0,\infty)\) have total mass one, and let \(\mathcal R\) be a finite family of subsets of \(I\) whose traces on every finite subset \(J\) number at most
  \[
    \sum_{k=0}^{d}\binom{|J|}{k}.
  \]
  For every integer \(n\ge2\), there is an ordered \(n\)-sample \(f\) such that every \(R\in\mathcal R\) missed by \(f\) has \(p\)-mass at most \(64(d+1)\log(n)/n\). -/)
  (proof := /-- Put \(\varepsilon=64(d+1)\log(n)/n\). If \(\varepsilon\ge1\), any constant sample suffices. Otherwise, apply the double-sampling argument. For an independent sample \(T\), a range of mass greater than \(\varepsilon\) contains at least half its expected number of points with probability bounded below by a fixed positive multiple of \(\varepsilon\). Randomly swap the corresponding coordinates of the original and ghost samples. Conditional on their combined values, a fixed trace occupying \(q\) coordinates is missed by the first sample with probability at most \(2^{-q}\), and the trace hypothesis bounds the number of possible traces by \(\sum_{k=0}^{d}\binom{2n}{k}\). The resulting geometric decay, together with the elementary Sauer--Shelah polynomial estimate and \(n\ge2\), makes the probability of missing a range of mass greater than \(\varepsilon\) strictly less than one. Hence some ordered sample misses no such range. -/)
  (title := /-- Finite probability VC \(\varepsilon\)-net bound -/)
  (latexEnv := "lemma")]
lemma finite_probability_vc_epsilon_net (d m n : ℕ)
    (𝓡 : Set (Finset (Fin m))) (p : Fin m → ℝ)
    (h𝓡 : 𝓡.Finite) (hp : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (htrace : ∀ s : Finset (Fin m),
      (𝓡.image fun r => r ∩ s).ncard
        ≤ ∑ k ∈ Finset.range (d + 1), s.card.choose k)
    (hn : 2 ≤ n) :
    ∃ f : Fin n → Fin m, ∀ r ∈ 𝓡, (∀ j, f j ∉ r) →
      ∑ i ∈ r, p i ≤ 64 * (d + 1) * Real.log n / n := by
  classical
  let ε : ℝ := 64 * (d + 1) * Real.log n / n
  by_cases hlarge : 1 ≤ ε
  · have hi : Nonempty (Fin m) := by
      by_contra h
      haveI : IsEmpty (Fin m) := not_nonempty_iff.mp h
      simp at hp_sum
    let i := Classical.choice hi
    refine ⟨fun _ => i, ?_⟩
    intro r hr hmiss
    apply le_trans ?_ hlarge
    rw [← hp_sum]
    exact Finset.sum_le_univ_sum_of_nonneg hp
  · have hεlt : ε < 1 := lt_of_not_ge hlarge
    have hnreal : (0 : ℝ) < n := by positivity
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hlog : 0 < Real.log n := Real.log_pos hn1
    have hε : 0 < ε := by positivity
    have hsample_sum (k : ℕ) :
        ∑ f : Fin k → Fin m, ∏ j, p (f j) = 1 := by
      simpa [hp_sum] using Finset.sum_prod_piFinset (ι := Fin k)
        (Finset.univ : Finset (Fin m)) (fun _ i => p i)
    have hsample_nonneg (k : ℕ) (f : Fin k → Fin m) :
        0 ≤ ∏ j, p (f j) := Finset.prod_nonneg fun j _ => hp (f j)
    have hcoordinate (j : Fin n) (r : Finset (Fin m)) :
        ∑ f : Fin n → Fin m, (∏ k, p (f k)) *
            (if f j ∈ r then 1 else 0) = ∑ i ∈ r, p i := by
      calc
        ∑ f : Fin n → Fin m, (∏ k, p (f k)) *
            (if f j ∈ r then 1 else 0) =
            ∑ f : Fin n → Fin m, ∏ k,
              p (f k) * (if k = j then (if f k ∈ r then 1 else 0) else 1) := by
                apply Finset.sum_congr rfl
                intro f hf
                rw [Finset.prod_mul_distrib]
                simp
        _ = ∏ k : Fin n, ∑ i : Fin m,
              p i * (if k = j then (if i ∈ r then 1 else 0) else 1) := by
                simpa using Finset.sum_prod_piFinset (ι := Fin n)
                  (Finset.univ : Finset (Fin m))
                  (fun k i => p i *
                    (if k = j then (if i ∈ r then 1 else 0) else 1))
        _ = ∑ i ∈ r, p i := by
                rw [Finset.prod_eq_single j]
                · simp [hp_sum]
                · intro k hk hkj
                  simp [hkj, hp_sum]
                · simp
    have hexpect (r : Finset (Fin m)) :
        ∑ f : Fin n → Fin m, (∏ j, p (f j)) *
            ((Finset.univ.filter fun j => f j ∈ r).card : ℝ) =
          n * ∑ i ∈ r, p i := by
      simp_rw [show ∀ f : Fin n → Fin m,
        ((Finset.univ.filter fun j => f j ∈ r).card : ℝ) =
          ∑ j, if f j ∈ r then (1 : ℝ) else 0 by
            intro f
            simp]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [hcoordinate]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum]
    have hghost (r : Finset (Fin m)) (hr : ε < ∑ i ∈ r, p i) :
        ε / 2 < ∑ f : Fin n → Fin m, (∏ j, p (f j)) *
          (if ε * n / 2 ≤
              ((Finset.univ.filter fun j => f j ∈ r).card : ℝ)
            then 1 else 0) := by
      let q : ℝ := ε * n / 2
      have hq : 0 ≤ q := by positivity
      have hpoint (f : Fin n → Fin m) :
          ((Finset.univ.filter fun j => f j ∈ r).card : ℝ) ≤
            q + n * (if q ≤
                ((Finset.univ.filter fun j => f j ∈ r).card : ℝ)
              then 1 else 0) := by
        by_cases h : q ≤
            ((Finset.univ.filter fun j => f j ∈ r).card : ℝ)
        · rw [if_pos h]
          have hcNat :
              (Finset.univ.filter fun j => f j ∈ r).card ≤ n := by
            simpa using
              Finset.card_le_univ (s := Finset.univ.filter fun j => f j ∈ r)
          have hc :
              ((Finset.univ.filter fun j => f j ∈ r).card : ℝ) ≤ n := by
            exact_mod_cast hcNat
          nlinarith
        · rw [if_neg h, mul_zero, add_zero]
          exact le_of_not_ge h
      have hsum :
          n * (∑ i ∈ r, p i) ≤ q +
            n * ∑ f : Fin n → Fin m, (∏ j, p (f j)) *
              (if q ≤ ((Finset.univ.filter fun j => f j ∈ r).card : ℝ)
                then 1 else 0) := by
        rw [← hexpect r]
        calc
          ∑ f : Fin n → Fin m, (∏ j, p (f j)) *
              ((Finset.univ.filter fun j => f j ∈ r).card : ℝ) ≤
              ∑ f : Fin n → Fin m, (∏ j, p (f j)) *
                (q + n * (if q ≤
                    ((Finset.univ.filter fun j => f j ∈ r).card : ℝ)
                  then 1 else 0)) := by
                    exact Finset.sum_le_sum fun f _ =>
                      mul_le_mul_of_nonneg_left (hpoint f) (hsample_nonneg n f)
          _ = q + n * ∑ f : Fin n → Fin m, (∏ j, p (f j)) *
                (if q ≤
                    ((Finset.univ.filter fun j => f j ∈ r).card : ℝ)
                  then 1 else 0) := by
                    simp_rw [mul_add]
                    rw [Finset.sum_add_distrib]
                    congr 1
                    · rw [← Finset.sum_mul, hsample_sum n, one_mul]
                    · calc
                        ∑ f : Fin n → Fin m, (∏ j, p (f j)) *
                            (n * (if q ≤
                                ((Finset.univ.filter fun j => f j ∈ r).card : ℝ)
                              then 1 else 0)) =
                          ∑ f : Fin n → Fin m, n * ((∏ j, p (f j)) *
                            (if q ≤
                                ((Finset.univ.filter fun j => f j ∈ r).card : ℝ)
                              then 1 else 0)) := by
                                apply Finset.sum_congr rfl
                                intro f hf
                                ring
                        _ = n * ∑ f : Fin n → Fin m, (∏ j, p (f j)) *
                            (if q ≤
                                ((Finset.univ.filter fun j => f j ∈ r).card : ℝ)
                              then 1 else 0) := by rw [Finset.mul_sum]
      dsimp [q] at hsum ⊢
      nlinarith
    by_contra! hnet
    let pairEvent : (Fin n → Fin m) → (Fin n → Fin m) → Prop :=
      fun f g => ∃ r ∈ 𝓡, (∀ j, f j ∉ r) ∧
        ε < ∑ i ∈ r, p i ∧
        ε * n / 2 ≤ ((Finset.univ.filter fun j => g j ∈ r).card : ℝ)
    have hinner (f : Fin n → Fin m) :
        ε / 2 < ∑ g : Fin n → Fin m, (∏ j, p (g j)) *
          (if pairEvent f g then 1 else 0) := by
      obtain ⟨r, hr𝓡, hfr, hrmass⟩ := hnet f
      refine lt_of_lt_of_le (hghost r hrmass) ?_
      apply Finset.sum_le_sum
      intro g hg
      apply mul_le_mul_of_nonneg_left
      · by_cases hgood :
          ε * n / 2 ≤ ((Finset.univ.filter fun j => g j ∈ r).card : ℝ)
        · rw [if_pos hgood, if_pos]
          exact ⟨r, hr𝓡, hfr, hrmass, hgood⟩
        · rw [if_neg hgood]
          positivity
      · exact hsample_nonneg n g
    have hweight_exists : ∃ f : Fin n → Fin m, 0 < ∏ j, p (f j) := by
      by_contra! h
      have hz : ∑ f : Fin n → Fin m, ∏ j, p (f j) ≤ 0 :=
        Finset.sum_nonpos fun f _ => h f
      rw [hsample_sum n] at hz
      norm_num at hz
    have hpair_lower :
        ε / 2 < ∑ f : Fin n → Fin m, (∏ j, p (f j)) *
          (∑ g : Fin n → Fin m, (∏ j, p (g j)) *
            (if pairEvent f g then 1 else 0)) := by
      obtain ⟨f₀, hf₀⟩ := hweight_exists
      calc
        ε / 2 = ∑ f : Fin n → Fin m, (∏ j, p (f j)) * (ε / 2) := by
          rw [← Finset.sum_mul, hsample_sum n, one_mul]
        _ < ∑ f : Fin n → Fin m, (∏ j, p (f j)) *
            (∑ g : Fin n → Fin m, (∏ j, p (g j)) *
              (if pairEvent f g then 1 else 0)) := by
                apply Finset.sum_lt_sum
                · intro f hf
                  exact mul_le_mul_of_nonneg_left (le_of_lt (hinner f))
                    (hsample_nonneg n f)
                · exact ⟨f₀, Finset.mem_univ f₀,
                    mul_lt_mul_of_pos_left (hinner f₀) hf₀⟩
    let left : (Fin n → Fin m) → (Fin n → Fin m) →
        (Fin n → Bool) → (Fin n → Fin m) :=
      fun a b σ j => if σ j then a j else b j
    let right : (Fin n → Fin m) → (Fin n → Fin m) →
        (Fin n → Bool) → (Fin n → Fin m) :=
      fun a b σ j => if σ j then b j else a j
    have hswap_weight (a b : Fin n → Fin m) (σ : Fin n → Bool) :
        (∏ j, p (left a b σ j)) * (∏ j, p (right a b σ j)) =
          (∏ j, p (a j)) * (∏ j, p (b j)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j hj
      by_cases hσ : σ j = true <;> simp [left, right, hσ, mul_comm]
    let swapEquiv (σ : Fin n → Bool) :
        ((Fin n → Fin m) × (Fin n → Fin m)) ≃
          ((Fin n → Fin m) × (Fin n → Fin m)) :=
      { toFun := fun z => (left z.1 z.2 σ, right z.1 z.2 σ)
        invFun := fun z => (left z.1 z.2 σ, right z.1 z.2 σ)
        left_inv := by
          intro z
          rcases z with ⟨a, b⟩
          apply Prod.ext
          · funext j
            by_cases hσ : σ j = true <;> simp [left, right, hσ]
          · funext j
            by_cases hσ : σ j = true <;> simp [left, right, hσ]
        right_inv := by
          intro z
          rcases z with ⟨a, b⟩
          apply Prod.ext
          · funext j
            by_cases hσ : σ j = true <;> simp [left, right, hσ]
          · funext j
            by_cases hσ : σ j = true <;> simp [left, right, hσ] }
    have hswap_sum (σ : Fin n → Bool) :
        ∑ z : (Fin n → Fin m) × (Fin n → Fin m),
            ((∏ j, p (z.1 j)) * (∏ j, p (z.2 j))) *
              (if pairEvent z.1 z.2 then 1 else 0) =
          ∑ z : (Fin n → Fin m) × (Fin n → Fin m),
            ((∏ j, p (z.1 j)) * (∏ j, p (z.2 j))) *
              (if pairEvent (left z.1 z.2 σ) (right z.1 z.2 σ)
                then 1 else 0) := by
      rw [← (swapEquiv σ).sum_comp
        (fun z => ((∏ j, p (z.1 j)) * (∏ j, p (z.2 j))) *
          (if pairEvent z.1 z.2 then 1 else 0))]
      apply Finset.sum_congr rfl
      intro z hz
      change (((∏ j, p (left z.1 z.2 σ j)) *
          (∏ j, p (right z.1 z.2 σ j))) *
            (if pairEvent (left z.1 z.2 σ) (right z.1 z.2 σ)
              then 1 else 0)) =
        (((∏ j, p (z.1 j)) * (∏ j, p (z.2 j))) *
          (if pairEvent (left z.1 z.2 σ) (right z.1 z.2 σ)
            then 1 else 0))
      rw [hswap_weight]
    have hfixed_card_le (A : Finset (Fin n)) (v : Fin n → Bool) :
        Fintype.card {σ : Fin n → Bool // ∀ j ∈ A, σ j = v j} ≤
          2 ^ (n - A.card) := by
      calc
        Fintype.card {σ : Fin n → Bool // ∀ j ∈ A, σ j = v j} ≤
            Fintype.card ({j : Fin n // j ∉ A} → Bool) := by
              apply Fintype.card_le_of_injective
                (fun σ (j : {j : Fin n // j ∉ A}) => σ.1 j.1)
              intro σ τ hστ
              apply Subtype.ext
              funext j
              by_cases hj : j ∈ A
              · rw [σ.2 j hj, τ.2 j hj]
              · exact congrFun hστ ⟨j, hj⟩
        _ = 2 ^ (n - A.card) := by
          rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl,
            Fintype.card_fin]
          congr 1
          simpa using Fintype.card_of_finset' A (fun _ => Iff.rfl)
    let support (a b : Fin n → Fin m) : Finset (Fin m) :=
      Finset.univ.image a ∪ Finset.univ.image b
    let traces (a b : Fin n → Fin m) : Finset (Finset (Fin m)) :=
      (h𝓡.image fun r => r ∩ support a b).toFinset
    let active (a b : Fin n → Fin m) (u : Finset (Fin m)) :
        Finset (Fin n) :=
      Finset.univ.filter fun j => a j ∈ u ∨ b j ∈ u
    have hswap_witness (a b : Fin n → Fin m) (σ : Fin n → Bool)
        (hE : pairEvent (left a b σ) (right a b σ)) :
        ∃ u ∈ traces a b,
          ε * n / 2 ≤ (active a b u).card ∧
          ∀ j ∈ active a b u, σ j = decide (b j ∈ u) := by
      change ∃ r ∈ 𝓡, (∀ j, left a b σ j ∉ r) ∧
        ε < ∑ i ∈ r, p i ∧
        ε * n / 2 ≤
          ((Finset.univ.filter fun j => right a b σ j ∈ r).card : ℝ) at hE
      obtain ⟨r, hr𝓡, hleft, hrmass, hcount⟩ := hE
      let u := r ∩ support a b
      have hu : u ∈ traces a b := by
        simp only [traces, Set.Finite.mem_toFinset, Set.mem_image]
        exact ⟨r, hr𝓡, rfl⟩
      have hcount_eq :
          (Finset.univ.filter fun j => right a b σ j ∈ r) =
            active a b u := by
        ext j
        by_cases hσ : σ j = true
        · have ha : a j ∉ r := by simpa [left, hσ] using hleft j
          simp [active, right, hσ, u, support, ha]
        · have hb : b j ∉ r := by
            have hσf : σ j = false := by simpa using hσ
            simpa [left, hσf] using hleft j
          have hσf : σ j = false := by simpa using hσ
          simp [active, right, hσf, u, support, hb]
      refine ⟨u, hu, ?_, ?_⟩
      · rw [← hcount_eq]
        exact hcount
      · intro j hj
        rcases (Finset.mem_filter.mp hj).2 with ha | hb
        · have hσ : σ j = false := by
            by_contra h
            have hσt : σ j = true := by simpa using h
            exact hleft j (by simpa [left, hσt, u, support] using ha)
          have hbnot : b j ∉ u := by
            intro hbu
            exact hleft j (by simpa [left, hσ, u, support] using hbu)
          simp [hσ, hbnot]
        · have hσ : σ j = true := by
            by_contra h
            have hσf : σ j = false := by simpa using h
            exact hleft j (by simpa [left, hσf, u, support] using hb)
          simp [hσ, hb]
    let L : ℕ := ⌈ε * n / 2⌉₊
    have hswap_card (a b : Fin n → Fin m) :
        (Finset.univ.filter fun σ : Fin n → Bool =>
          pairEvent (left a b σ) (right a b σ)).card ≤
          (∑ k ∈ Finset.range (d + 1), (2 * n).choose k) *
            2 ^ (n - L) := by
      let good : Finset (Finset (Fin m)) :=
        (traces a b).filter fun u => L ≤ (active a b u).card
      let fixed (u : Finset (Fin m)) : Finset (Fin n → Bool) :=
        Finset.univ.filter fun σ => ∀ j ∈ active a b u,
          σ j = decide (b j ∈ u)
      have hevent_subset :
          (Finset.univ.filter fun σ : Fin n → Bool =>
            pairEvent (left a b σ) (right a b σ)) ⊆
            good.biUnion fixed := by
        intro σ hσ
        have hE : pairEvent (left a b σ) (right a b σ) :=
          (Finset.mem_filter.mp hσ).2
        obtain ⟨u, hut, huq, hufix⟩ := hswap_witness a b σ hE
        have huL : L ≤ (active a b u).card := by
          exact Nat.ceil_le.mpr huq
        have hug : u ∈ good := by simp [good, hut, huL]
        rw [Finset.mem_biUnion]
        refine ⟨u, hug, ?_⟩
        simp only [fixed, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hufix
      have hfixed (u : Finset (Fin m)) (hu : u ∈ good) :
          (fixed u).card ≤ 2 ^ (n - L) := by
        have huL : L ≤ (active a b u).card := (Finset.mem_filter.mp hu).2
        calc
          (fixed u).card =
              Fintype.card {σ : Fin n → Bool // ∀ j ∈ active a b u,
                σ j = decide (b j ∈ u)} := by
                  exact (Fintype.card_of_finset'
                    (p := {σ : Fin n → Bool |
                      ∀ j ∈ active a b u, σ j = decide (b j ∈ u)})
                    (fixed u) (by
                      intro σ
                      simp [fixed])).symm
          _ ≤ 2 ^ (n - (active a b u).card) :=
            hfixed_card_le (active a b u) (fun j => decide (b j ∈ u))
          _ ≤ 2 ^ (n - L) := by
            exact Nat.pow_le_pow_right (n := 2)
              (i := n - (active a b u).card) (j := n - L)
              (by omega) (by omega)
      have hsupport : (support a b).card ≤ 2 * n := by
        calc
          (support a b).card ≤ (Finset.univ.image a).card +
              (Finset.univ.image b).card := by
                simpa [support] using
                  Finset.card_union_le (Finset.univ.image a) (Finset.univ.image b)
          _ ≤ n + n := by
            exact Nat.add_le_add
              (by
                calc
                  (Finset.univ.image a).card ≤ Finset.univ.card :=
                    Finset.card_image_le
                  _ = n := by simp)
              (by
                calc
                  (Finset.univ.image b).card ≤ Finset.univ.card :=
                    Finset.card_image_le
                  _ = n := by simp)
          _ = 2 * n := by omega
      have htraces :
          (traces a b).card ≤
            ∑ k ∈ Finset.range (d + 1), (2 * n).choose k := by
        calc
          (traces a b).card ≤
              ∑ k ∈ Finset.range (d + 1), (support a b).card.choose k := by
                change
                  (h𝓡.image fun r => r ∩ support a b).toFinset.card ≤
                    ∑ k ∈ Finset.range (d + 1),
                      (support a b).card.choose k
                rw [← Set.ncard_eq_toFinset_card]
                exact htrace (support a b)
          _ ≤ ∑ k ∈ Finset.range (d + 1), (2 * n).choose k := by
                exact Finset.sum_le_sum fun k _ =>
                  Nat.choose_le_choose k hsupport
      calc
        (Finset.univ.filter fun σ : Fin n → Bool =>
          pairEvent (left a b σ) (right a b σ)).card ≤
            (good.biUnion fixed).card := Finset.card_le_card hevent_subset
        _ ≤ good.card * 2 ^ (n - L) :=
          Finset.card_biUnion_le_card_mul good fixed (2 ^ (n - L)) hfixed
        _ ≤ (traces a b).card * 2 ^ (n - L) := by
          exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
        _ ≤ (∑ k ∈ Finset.range (d + 1), (2 * n).choose k) *
            2 ^ (n - L) := Nat.mul_le_mul_right _ htraces
    let M : ℝ :=
      ∑ z : (Fin n → Fin m) × (Fin n → Fin m),
        ((∏ j, p (z.1 j)) * (∏ j, p (z.2 j))) *
          (if pairEvent z.1 z.2 then 1 else 0)
    have hindicator (z : (Fin n → Fin m) × (Fin n → Fin m)) :
        (∑ σ : Fin n → Bool,
            if pairEvent (left z.1 z.2 σ) (right z.1 z.2 σ)
              then (1 : ℝ) else 0) =
          ((Finset.univ.filter (fun σ : Fin n → Bool =>
            pairEvent (left z.1 z.2 σ) (right z.1 z.2 σ))).card : ℝ) := by
      norm_cast
      simpa using
        (Finset.card_eq_sum_ite
          (s := Finset.univ.filter (fun σ : Fin n → Bool =>
            pairEvent (left z.1 z.2 σ) (right z.1 z.2 σ)))
          (t := Finset.univ) (by simp)).symm
    have havg :
        (2 ^ n : ℝ) * M =
          ∑ z : (Fin n → Fin m) × (Fin n → Fin m),
            ((∏ j, p (z.1 j)) * (∏ j, p (z.2 j))) *
              ((Finset.univ.filter (fun σ : Fin n → Bool =>
                pairEvent (left z.1 z.2 σ)
                  (right z.1 z.2 σ))).card : ℝ) := by
      calc
        (2 ^ n : ℝ) * M = ∑ σ : Fin n → Bool, M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
            Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
          norm_num
        _ = ∑ σ : Fin n → Bool,
            ∑ z : (Fin n → Fin m) × (Fin n → Fin m),
              ((∏ j, p (z.1 j)) * (∏ j, p (z.2 j))) *
                (if pairEvent (left z.1 z.2 σ) (right z.1 z.2 σ)
                  then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro σ hσ
            simpa [M] using hswap_sum σ
        _ = ∑ z : (Fin n → Fin m) × (Fin n → Fin m),
            ((∏ j, p (z.1 j)) * (∏ j, p (z.2 j))) *
              (∑ σ : Fin n → Bool,
                if pairEvent (left z.1 z.2 σ) (right z.1 z.2 σ)
                  then 1 else 0) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro z hz
            rw [Finset.mul_sum]
        _ = ∑ z : (Fin n → Fin m) × (Fin n → Fin m),
            ((∏ j, p (z.1 j)) * (∏ j, p (z.2 j))) *
              ((Finset.univ.filter (fun σ : Fin n → Bool =>
                pairEvent (left z.1 z.2 σ)
                  (right z.1 z.2 σ))).card : ℝ) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [hindicator z]
    have hmain : 64 * ((d : ℝ) + 1) * Real.log n < n := by
      dsimp [ε] at hεlt
      rwa [div_lt_one hnreal] at hεlt
    have hloghalf : (1 / 2 : ℝ) ≤ Real.log n := by
      have hbase := Real.one_sub_inv_le_log_of_pos hnreal
      have hncast : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hinv : (n : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
        (inv_le_inv₀ hnreal (by norm_num)).2 hncast
      norm_num at hinv
      linarith
    have hdlt : d < n := by
      by_contra hdn
      have hnd : n ≤ d := Nat.le_of_not_gt hdn
      have hdn' : (n : ℝ) ≤ d + 1 := by
        exact_mod_cast hnd.trans (Nat.le_add_right d 1)
      have hprod : (n : ℝ) / 2 ≤ ((d : ℝ) + 1) * Real.log n := by
        calc
          (n : ℝ) / 2 = n * (1 / 2) := by ring
          _ ≤ ((d : ℝ) + 1) * (1 / 2) :=
            mul_le_mul_of_nonneg_right hdn' (by norm_num)
          _ ≤ ((d : ℝ) + 1) * Real.log n :=
            mul_le_mul_of_nonneg_left hloghalf (by positivity)
      nlinarith
    have hA_bound :
        (∑ k ∈ Finset.range (d + 1), (2 * n).choose k) ≤
          (d + 1) * (2 * n) ^ d := by
      calc
        (∑ k ∈ Finset.range (d + 1), (2 * n).choose k) ≤
            ∑ k ∈ Finset.range (d + 1), (2 * n) ^ d := by
              exact Finset.sum_le_sum fun k hk =>
                (Nat.choose_le_pow _ _).trans
                  ((Nat.pow_le_pow_right (by omega))
                    (by simp only [Finset.mem_range] at hk; omega))
        _ = (d + 1) * (2 * n) ^ d := by
          rw [Finset.sum_const, Finset.card_range]
          simp [nsmul_eq_mul]
    have hpowL :
        (n : ℝ) ^ (4 * (d + 1)) ≤ (2 : ℝ) ^ L := by
      have hceil : ε * n / 2 ≤ (L : ℝ) := by
        dsimp [L]
        exact Nat.le_ceil (ε * n / 2)
      have heq :
          ε * n / 2 = 32 * ((d : ℝ) + 1) * Real.log n := by
        dsimp [ε]
        field_simp
        ring
      calc
        (n : ℝ) ^ (4 * (d + 1)) =
            (n : ℝ) ^ ((4 * (d + 1) : ℕ) : ℝ) :=
              (Real.rpow_natCast (n : ℝ) (4 * (d + 1))).symm
        _ = Real.exp (Real.log n * ((4 * (d + 1) : ℕ) : ℝ)) :=
          Real.rpow_def_of_pos hnreal _
        _ ≤ Real.exp (Real.log 2 * (L : ℝ)) := by
          rw [Real.exp_le_exp]
          have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
            have h := Real.one_sub_inv_le_log_of_pos
              (show (0 : ℝ) < 2 by norm_num)
            norm_num at h ⊢
            exact h
          push_cast
          rw [heq] at hceil
          have hdnonneg : (0 : ℝ) ≤ d + 1 := by positivity
          nlinarith [mul_nonneg hdnonneg (le_of_lt hlog)]
        _ = (2 : ℝ) ^ (L : ℝ) :=
          (Real.rpow_def_of_pos (by norm_num) _).symm
        _ = (2 : ℝ) ^ L := Real.rpow_natCast _ _
    have hpoly :
        (∑ k ∈ Finset.range (d + 1), (2 * n).choose k) * n ^ 2 ≤
          n ^ (4 * (d + 1)) := by
      calc
        (∑ k ∈ Finset.range (d + 1), (2 * n).choose k) * n ^ 2 ≤
            ((d + 1) * (2 * n) ^ d) * n ^ 2 :=
              Nat.mul_le_mul_right _ hA_bound
        _ ≤ (n * (n ^ 2) ^ d) * n ^ 2 := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul
            (by omega)
            (Nat.pow_le_pow_left (n := 2 * n) (m := n ^ 2)
              (by nlinarith) d))
        _ = n ^ (2 * d + 3) := by ring
        _ ≤ n ^ (4 * (d + 1)) :=
          Nat.pow_le_pow_right (n := n) (i := 2 * d + 3)
            (j := 4 * (d + 1)) (by omega) (by omega)
    have hpowLnat : n ^ (4 * (d + 1)) ≤ 2 ^ L := by
      exact_mod_cast hpowL
    have hAnL :
        (∑ k ∈ Finset.range (d + 1), (2 * n).choose k) * n ^ 2 ≤
          2 ^ L :=
      hpoly.trans hpowLnat
    have hLn : L ≤ n := by
      dsimp [L]
      rw [Nat.ceil_le]
      nlinarith
    have hpair_total :
        (∑ z : (Fin n → Fin m) × (Fin n → Fin m),
          (∏ j, p (z.1 j)) * (∏ j, p (z.2 j))) = 1 := by
      rw [Fintype.sum_prod_type]
      calc
        (∑ x : Fin n → Fin m, ∑ y : Fin n → Fin m,
            (∏ j, p (x j)) * ∏ j, p (y j)) =
            ∑ x : Fin n → Fin m, (∏ j, p (x j)) *
              (∑ y : Fin n → Fin m, ∏ j, p (y j)) := by
                apply Finset.sum_congr rfl
                intro x hx
                rw [Finset.mul_sum]
        _ = 1 := by rw [hsample_sum n]; simp [hsample_sum n]
    have hscaled :
        (2 ^ n : ℝ) * M ≤
          (((∑ k ∈ Finset.range (d + 1), (2 * n).choose k) *
            2 ^ (n - L) : ℕ) : ℝ) := by
      rw [havg]
      calc
        (∑ z : (Fin n → Fin m) × (Fin n → Fin m),
          ((∏ j, p (z.1 j)) * (∏ j, p (z.2 j))) *
            ((Finset.univ.filter (fun σ : Fin n → Bool =>
              pairEvent (left z.1 z.2 σ)
                (right z.1 z.2 σ))).card : ℝ)) ≤
          ∑ z : (Fin n → Fin m) × (Fin n → Fin m),
            ((∏ j, p (z.1 j)) * (∏ j, p (z.2 j))) *
              (((∑ k ∈ Finset.range (d + 1), (2 * n).choose k) *
                2 ^ (n - L) : ℕ) : ℝ) := by
            apply Finset.sum_le_sum
            intro z hz
            apply mul_le_mul_of_nonneg_left
            · exact_mod_cast hswap_card z.1 z.2
            · exact mul_nonneg (hsample_nonneg n z.1)
                (hsample_nonneg n z.2)
        _ = (((∑ k ∈ Finset.range (d + 1), (2 * n).choose k) *
              2 ^ (n - L) : ℕ) : ℝ) := by
          rw [← Finset.sum_mul]
          rw [hpair_total, one_mul]
    have hscaled_nat :
        ((∑ k ∈ Finset.range (d + 1), (2 * n).choose k) *
          2 ^ (n - L)) * n ^ 2 ≤ 2 ^ n := by
      calc
        ((∑ k ∈ Finset.range (d + 1), (2 * n).choose k) *
          2 ^ (n - L)) * n ^ 2 =
            ((∑ k ∈ Finset.range (d + 1), (2 * n).choose k) *
              n ^ 2) * 2 ^ (n - L) := by ring
        _ ≤ 2 ^ L * 2 ^ (n - L) := Nat.mul_le_mul_right _ hAnL
        _ = 2 ^ n := by
          rw [← pow_add]
          congr
          omega
    have hscaled_real :
        (((∑ k ∈ Finset.range (d + 1), (2 * n).choose k) *
          2 ^ (n - L) : ℕ) : ℝ) * (n : ℝ) ^ 2 ≤
            (2 : ℝ) ^ n := by
      exact_mod_cast hscaled_nat
    have hM_upper : M * (n : ℝ) ^ 2 ≤ 1 := by
      refine le_of_mul_le_mul_left ?_ (show (0 : ℝ) < 2 ^ n by positivity)
      calc
        (2 : ℝ) ^ n * (M * (n : ℝ) ^ 2) =
            ((2 : ℝ) ^ n * M) * (n : ℝ) ^ 2 := by ring
        _ ≤ (((∑ k ∈ Finset.range (d + 1), (2 * n).choose k) *
              2 ^ (n - L) : ℕ) : ℝ) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hscaled (sq_nonneg (n : ℝ))
        _ ≤ (2 : ℝ) ^ n := hscaled_real
        _ = (2 : ℝ) ^ n * 1 := by ring
    have hM_lower : ε / 2 < M := by
      dsimp [M]
      apply lt_of_lt_of_le hpair_lower
      simp_rw [Finset.mul_sum]
      rw [Fintype.sum_prod_type]
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro f hf
      apply Finset.sum_congr rfl
      intro g hg
      ring
    have hepsbig : (1 : ℝ) < (ε / 2) * (n : ℝ) ^ 2 := by
      have heq : (ε / 2) * (n : ℝ) ^ 2 =
          32 * ((d : ℝ) + 1) * Real.log n * n := by
        dsimp [ε]
        field_simp
        ring
      rw [heq]
      have hdone : (1 : ℝ) ≤ d + 1 := by norm_num
      have hncast : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [mul_nonneg (sub_nonneg.mpr hloghalf)
        (sub_nonneg.mpr hncast),
        mul_nonneg (sub_nonneg.mpr hdone) (le_of_lt hlog)]
    have hM_lower_scaled :
        (ε / 2) * (n : ℝ) ^ 2 < M * (n : ℝ) ^ 2 :=
      mul_lt_mul_of_pos_right hM_lower (by positivity)
    exact (not_lt_of_ge hM_upper (hepsbig.trans hM_lower_scaled)).elim

@[blueprint "lem:finite-weighted-vc-epsilon-net"
  (statement := /-- Let \(d\in\mathbb N\). There is a constant \(C>0\), depending only on \(d\), with the following property. Let \(I\) be a finite set, let \(w:I\to[0,\infty)\) have positive total mass, and let \(\mathcal R\) be a finite family of subsets of \(I\). Suppose that, for every \(J\subseteq I\), the number of traces \(\{R\cap J:R\in\mathcal R\}\) is at most
  \[
    \sum_{k=0}^{d}\binom{|J|}{k}.
  \]
  Then, for every integer \(n\ge2\), there is a list \(S\) of \(n\) elements of \(I\), with repetitions permitted, such that every \(R\in\mathcal R\) disjoint from \(S\) satisfies
  \[
    \frac{\sum_{i\in R}w(i)}{\sum_{i\in I}w(i)}
      \le C\,\frac{(d+1)\log n}{n}.
  \] -/)
  (proof := /-- Take \(C=64\). For the given weights put
  \(W=\sum_{i\in I}w(i)\) and \(p(i)=w(i)/W\). Positivity of \(W\) and
  nonnegativity of the weights imply that \(p\) is nonnegative, while
  distributivity of finite sums over division gives
  \(\sum_{i\in I}p(i)=1\). Apply
  \cref{lem:finite-probability-vc-epsilon-net} to \(p\), with the given trace
  bound and sample size, and let \(f:\operatorname{Fin}(n)\to I\) be the
  resulting ordered sample. The list obtained from \(f\) has length \(n\).
  If a range \(R\) is disjoint from this list, then \(f(j)\notin R\) for
  every \(j\), so the probability bound from that lemma applies. Finally,
  \[
    \sum_{i\in R}p(i)
      =\sum_{i\in R}\frac{w(i)}{W}
      =\frac{\sum_{i\in R}w(i)}{\sum_{i\in I}w(i)},
  \]
  which is the required inequality. -/)
  (title := /-- Finite weighted VC \(\varepsilon\)-net theorem -/)
  (latexEnv := "lemma")]
lemma finite_weighted_vc_epsilon_net (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m n : ℕ) (𝓡 : Set (Finset (Fin m))) (w : Fin m → ℝ),
        𝓡.Finite →
        (∀ i, 0 ≤ w i) →
        0 < ∑ i, w i →
        (∀ s : Finset (Fin m),
          (𝓡.image fun r => r ∩ s).ncard
            ≤ ∑ k ∈ Finset.range (d + 1), s.card.choose k) →
        2 ≤ n →
        ∃ S : List (Fin m), S.length = n ∧
          ∀ r ∈ 𝓡, (∀ i ∈ S, i ∉ r) →
            (∑ i ∈ r, w i) / (∑ i, w i)
              ≤ C * (d + 1) * Real.log n / n := by
  refine ⟨64, by norm_num, ?_⟩
  intro m n 𝓡 w h𝓡 hw hw_sum htrace hn
  let p : Fin m → ℝ := fun i => w i / ∑ j, w j
  have hp : ∀ i, 0 ≤ p i := by
    intro i
    exact div_nonneg (hw i) (le_of_lt hw_sum)
  have hp_sum : ∑ i, p i = 1 := by
    dsimp [p]
    rw [← Finset.sum_div, div_self (ne_of_gt hw_sum)]
  obtain ⟨f, hf⟩ :=
    finite_probability_vc_epsilon_net d m n 𝓡 p h𝓡 hp hp_sum htrace hn
  let S : List (Fin m) := List.ofFn f
  refine ⟨S, by simp [S], ?_⟩
  intro r hr hmiss
  have hmissf : ∀ j, f j ∉ r := by
    intro j hmem
    exact hmiss (f j) (by simp [S]) hmem
  have hbound := hf r hr hmissf
  simpa [p, Finset.sum_div] using hbound

@[blueprint "lem:epsnet-vc"
  (statement := /-- Let $X$ be a domain, let $\mathcal H$ be a binary hypothesis class on $X$, and let $d$ be a natural number such that no finite subset of $X$ with more than $d$ elements is shattered by $\mathcal H$. Then there is a constant $C>0$, depending only on $d$, such that, for every nonempty finite list $D$ of labeled examples and every integer $n\ge 2$, there is a list $S$ of $n$ labeled examples, with repetitions permitted, every entry of which belongs to $D$, for which every $h\in\mathcal H$ consistent with $S$ has empirical disagreement rate at most $C\,(d+1)\log n/n$ on $D$. -/)
  (proof := /-- Fix a nonempty list \(D=(z_0,\ldots,z_{m-1})\), where \(z_i=(x_i,y_i)\), and let
  \[
    R_h=\{i\in\operatorname{Fin}(m):h(x_i)\ne y_i\}
  \]
  for \(h\in\mathcal H\). These sets form a finite family \(\mathcal R_D\). To verify the trace hypothesis in \cref{lem:finite-weighted-vc-epsilon-net}, fix \(J\subseteq\operatorname{Fin}(m)\), put \(E=\{x_i:i\in J\}\), and consider the finite family
  \[
    \mathcal A_J=\bigl\{\{x\in E:h(x)=1\}:h\in\mathcal H\bigr\}
  \]
  of prediction traces on \(E\). If \(T\subseteq E\) is shattered by \(\mathcal A_J\), then every Boolean labeling of the image of \(T\) in \(X\) is realized by a member of \(\mathcal H\). The inclusion \(E\hookrightarrow X\) is injective, so the VC hypothesis gives \(|T|\le d\). The Sauer--Shelah lemma and \(|E|\le|J|\) therefore imply
  \[
    |\mathcal A_J|\le\sum_{k=0}^{d}\binom{|J|}{k}.
  \]
  On the indices in \(J\), the error bit of \(h\) is determined by its prediction bit and the fixed label \(y_i\). Consequently every trace \(R_h\cap J\) is the image of the corresponding member of \(\mathcal A_J\) under this fixed transformation, and hence
  \[
    |\{R\cap J:R\in\mathcal R_D\}|
      \le |\mathcal A_J|
      \le\sum_{k=0}^{d}\binom{|J|}{k}.
  \]

  Apply \cref{lem:finite-weighted-vc-epsilon-net} to \(\mathcal R_D\) with weight \(1\) on every dataset index. Its positive total weight is \(m\). The lemma gives a list \(I\) of \(n\) indices. Mapping each \(i\in I\) to \(z_i\) gives a list \(S\) of length \(n\), with repetitions permitted, whose entries belong to \(D\). If \(h\in\mathcal H\) is consistent with \(S\), then \(I\) is disjoint from \(R_h\). Finally, enumerating \(\operatorname{Fin}(m)\) identifies \(|R_h|\) with the length of the list obtained by filtering \(D\) for disagreements, including all repeated occurrences. Thus the weighted conclusion is exactly the asserted empirical-disagreement bound. -/)
  (title := /-- $\varepsilon$-net uniform sample bound at VC dimension $d$ -/)
  (latexEnv := "lemma")]
lemma epsnet_vc (X : Type) (H : hypothesis_class X) (d : ℕ)
    (hvc : ∀ s : Finset X, d < s.card → ¬ ∀ g : X → Bool, ∃ h ∈ H, ∀ x ∈ s, h x = g x) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : List (labeled_example X)) (n : ℕ), D ≠ [] → 2 ≤ n →
      ∃ S : List (labeled_example X), S.length = n ∧ (∀ z ∈ S, z ∈ D) ∧ ∀ h ∈ H,
        (∀ z ∈ S, h z.1 = z.2) →
          ((D.filter fun z => h z.1 != z.2).length : ℝ) / D.length
            ≤ C * (d + 1) * Real.log n / n := by
  classical
  obtain ⟨C, hC, hnet⟩ := finite_weighted_vc_epsilon_net d
  refine ⟨C, hC, ?_⟩
  intro D n hD hn
  let 𝓡 : Set (Finset (Fin D.length)) :=
    {r | ∃ h ∈ H, r = Finset.univ.filter fun i => h (D.get i).1 != (D.get i).2}
  have h𝓡 : 𝓡.Finite := Set.toFinite 𝓡
  have htrace : ∀ s : Finset (Fin D.length),
      (𝓡.image fun r => r ∩ s).ncard
        ≤ ∑ k ∈ Finset.range (d + 1), s.card.choose k := by
    intro s
    let E : Finset X := s.image fun i => (D.get i).1
    let pred : (X → Bool) → Finset E :=
      fun h => Finset.univ.filter fun x => h x.1
    let A : Finset (Finset E) :=
      Finset.univ.filter fun p => ∃ h ∈ H, p = pred h
    have hdim : A.vcDim ≤ d := by
      unfold Finset.vcDim
      refine Finset.sup_le ?_
      intro t ht
      rw [Finset.mem_shatterer] at ht
      by_contra htd
      have hdt : d < t.card := Nat.lt_of_not_ge htd
      have hcard_image :
          (t.image fun x : E => x.1).card = t.card :=
        Finset.card_image_of_injective _ Subtype.val_injective
      have hall : ∀ g : X → Bool, ∃ h ∈ H,
          ∀ x ∈ t.image fun y : E => y.1, h x = g x := by
        intro g
        let q : Finset E := t.filter fun x : E => g x.1
        obtain ⟨p, hpA, hinter⟩ := ht (show q ⊆ t by
          intro x hx
          exact (Finset.mem_filter.mp hx).1)
        have hp : ∃ h ∈ H, p = pred h := by
          change p ∈ Finset.univ.filter (fun p => ∃ h ∈ H, p = pred h) at hpA
          exact (Finset.mem_filter.mp hpA).2
        obtain ⟨h, hh, rfl⟩ := hp
        refine ⟨h, hh, ?_⟩
        intro x hx
        obtain ⟨y, hyt, rfl⟩ := Finset.mem_image.mp hx
        have hmem := Finset.ext_iff.mp hinter y
        simp only [Finset.mem_inter, Finset.mem_filter, hyt, true_and,
          q, pred, Finset.mem_univ] at hmem
        cases hhx : h y.1 <;> cases hgx : g y.1 <;> simp_all
      exact (hvc (t.image fun x : E => x.1)
        (by simpa [hcard_image] using hdt) hall).elim
    have hAcard : A.card ≤ ∑ k ∈ Finset.range (d + 1), s.card.choose k := by
      calc
        A.card ≤ A.shatterer.card := Finset.card_le_card_shatterer A
        _ ≤ ∑ k ∈ Finset.Iic A.vcDim, (Fintype.card E).choose k :=
          Finset.card_shatterer_le_sum_vcDim
        _ ≤ ∑ k ∈ Finset.Iic d, (Fintype.card E).choose k := by
          apply Finset.sum_le_sum_of_subset
          intro k hk
          simp only [Finset.mem_Iic] at hk ⊢
          exact hk.trans hdim
        _ ≤ ∑ k ∈ Finset.range (d + 1), s.card.choose k := by
          rw [← Nat.range_succ_eq_Iic]
          simp only [Fintype.card_coe]
          apply Finset.sum_le_sum
          intro k hk
          exact Nat.choose_le_choose k (by
            simpa [E] using Finset.card_image_le (s := s) (f := fun i => (D.get i).1))
    let decode : Finset E → Finset (Fin D.length) := fun p =>
      s.filter fun i =>
        if hi : i ∈ s then
          (decide ((⟨(D.get i).1, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩ : E) ∈ p))
            != (D.get i).2
        else false
    have hsub :
        𝓡.image (fun r => r ∩ s) ⊆ (↑(A.image decode) : Set (Finset (Fin D.length))) := by
      intro u hu
      obtain ⟨r, hr, rfl⟩ := hu
      obtain ⟨h, hh, rfl⟩ := hr
      have hpred : pred h ∈ A := by
        simp [A]
        exact ⟨h, hh, rfl⟩
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨pred h, hpred, ?_⟩)
      ext i
      by_cases hi : i ∈ s
      · simp [decode, pred, hi]
      · simp [decode, hi]
    calc
      (𝓡.image fun r => r ∩ s).ncard
          ≤ (↑(A.image decode) : Set (Finset (Fin D.length))).ncard :=
        Set.ncard_le_ncard hsub
      _ = (A.image decode).card := Set.ncard_coe_finset _
      _ ≤ A.card := Finset.card_image_le
      _ ≤ ∑ k ∈ Finset.range (d + 1), s.card.choose k := hAcard
  have hw_sum : 0 < ∑ _i : Fin D.length, (1 : ℝ) := by
    have hlen_nat : 0 < D.length := Nat.pos_of_ne_zero (by
      intro hlen
      apply hD
      exact List.eq_nil_of_length_eq_zero hlen)
    have hlen : (0 : ℝ) < D.length := by
      exact_mod_cast hlen_nat
    simpa using hlen
  obtain ⟨I, hIlen, hI⟩ :=
    hnet D.length n 𝓡 (fun _ => 1) h𝓡 (by intro i; positivity) hw_sum htrace hn
  refine ⟨I.map D.get, by simp [hIlen], ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
    exact D.get_mem i
  · intro h hh hconsistent
    let r : Finset (Fin D.length) :=
      Finset.univ.filter fun i => h (D.get i).1 != (D.get i).2
    have hr : r ∈ 𝓡 := ⟨h, hh, rfl⟩
    have hmiss : ∀ i ∈ I, i ∉ r := by
      intro i hi hir
      have hgood := hconsistent (D.get i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
      have hbad := (Finset.mem_filter.mp hir).2
      have hne : h (D.get i).1 ≠ (D.get i).2 := by
        simpa using hbad
      exact hne hgood
    have hbound := hI r hr hmiss
    let J : List (Fin D.length) := List.ofFn id
    have hJnodup : J.Nodup := by
      exact List.nodup_ofFn_ofInjective Function.injective_id
    have hDrepr : J.map D.get = D := by
      simp [J, Function.comp_def]
    have hcount :
        (D.filter fun z => h z.1 != z.2).length = r.card := by
      calc
        (D.filter fun z => h z.1 != z.2).length =
            ((J.map D.get).filter fun z => h z.1 != z.2).length := by
              rw [hDrepr]
        _ = ((J.filter fun i => h (D.get i).1 != (D.get i).2).map D.get).length := by
              rw [List.filter_map]
              rfl
        _ = (J.filter fun i => h (D.get i).1 != (D.get i).2).length := by simp
        _ = (J.filter fun i => h (D.get i).1 != (D.get i).2).toFinset.card :=
              (List.toFinset_card_of_nodup (hJnodup.filter _)).symm
        _ = r.card := by
              congr 1
              ext i
              simp [J, r]
    rw [hcount]
    simpa [r] using hbound

@[blueprint "lem:nonempty-class-has-erm"
  (statement := /-- Let $X$ be a domain and let $\mathcal H$ be a nonempty binary hypothesis class on $X$. Then there exists an empirical-risk-minimization rule over $\mathcal H$. -/)
  (proof := /-- For each finite training list, the set of mistake counts achieved by members of $\mathcal H$ is a nonempty set of natural numbers. Choose a hypothesis attaining its least element. Since all empirical losses on the fixed list have the same denominator, minimizing the mistake count minimizes the empirical loss. The resulting pointwise choice is an ERM in the sense of \cref{def:is-erm}. -/)
  (title := /-- Existence of an ERM for a nonempty class -/)
  (latexEnv := "lemma")]
lemma nonempty_class_has_erm (X : Type) (H : hypothesis_class X)
    (hH : H.Nonempty) : ∃ A : erm_rule X, is_erm H A := by
  classical
  have hchoice : ∀ S : List (labeled_example X), ∃ h ∈ H,
      ∀ g ∈ H, empirical_classification_loss S h ≤
        empirical_classification_loss S g := by
    intro S
    have hex : ∃ k : ℕ, ∃ h ∈ H,
        (S.filter fun z => h z.1 != z.2).length = k := by
      rcases hH with ⟨h, hh⟩
      exact ⟨(S.filter fun z => h z.1 != z.2).length, h, hh, rfl⟩
    let k := Nat.find hex
    obtain ⟨h, hh, hk⟩ := Nat.find_spec hex
    refine ⟨h, hh, ?_⟩
    intro g hg
    have hkg : k ≤ (S.filter fun z => g z.1 != z.2).length :=
      Nat.find_min' hex ⟨g, hg, rfl⟩
    unfold empirical_classification_loss
    rw [hk]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hkg) (by positivity)
  choose A hA using hchoice
  exact ⟨A, hA⟩

@[blueprint "lem:nontrivial-regret-finite-vc"
  (statement := /-- Let $X$ be a domain and let $\mathcal H$ be a binary hypothesis class on $X$. If the worst-case selection-regret sequence of $\mathcal H$ is not identically one, then there is $d\in\mathbb N$ such that no finite subset of $X$ of cardinality greater than $d$ is shattered by $\mathcal H$. -/)
  (proof := /-- Choose $q$ for which $R^\star_{\mathcal H}(q)<1$, using \cref{lem:worst-regret-envelope}. If no such VC bound existed, then $\mathcal H$ would shatter finite sets of arbitrarily large cardinality. Choose a shattered set $E$ so large that $q/|E|<1-R^\star_{\mathcal H}(q)$, and label every point of $E$ by zero. The class is nonempty, so \cref{lem:nonempty-class-has-erm} supplies a background ERM. Modify it on the lists of length $q$ selected from this dataset: shattering permits the modified rule to fit every selected point and to misclassify every point of $E$ not represented in the selected list. This is still an ERM, while its full-data loss is at least $1-q/|E|$. The best full-data loss is zero. The attained variational representation in \cref{lem:selection-regret-variational} therefore makes this selection regret strictly larger than $R^\star_{\mathcal H}(q)$, contradicting the memberwise supremum bound in \cref{lem:worst-regret-envelope}. -/)
  (title := /-- Nontrivial regret forces finite VC dimension -/)
  (latexEnv := "lemma")]
lemma nontrivial_regret_finite_vc (X : Type) (H : hypothesis_class X)
    (h : ¬ trivial_rate (worst_selection_regret H)) :
    ∃ d : ℕ, ∀ s : Finset X, d < s.card →
      ¬ ∀ g : X → Bool, ∃ h ∈ H, ∀ x ∈ s, h x = g x := by
  classical
  rw [trivial_rate] at h
  push Not at h
  obtain ⟨q, hq⟩ := h
  have hqb := (worst_regret_envelope X H q).1
  have hqlt : worst_selection_regret H q < 1 :=
    lt_of_le_of_ne hqb.2 hq
  by_contra hfinite
  push Not at hfinite
  let δ : ℝ := 1 - worst_selection_regret H q
  have hδ : 0 < δ := sub_pos.mpr hqlt
  obtain ⟨N, hN⟩ := exists_nat_gt ((q : ℝ) / δ)
  obtain ⟨s, hsN, hshatter⟩ := hfinite N
  have hspos : 0 < s.card := lt_of_le_of_lt (Nat.zero_le N) hsN
  obtain ⟨h₀, hh₀, hh₀s⟩ := hshatter (fun _ => false)
  have hH : H.Nonempty := ⟨h₀, hh₀⟩
  obtain ⟨A₀, hA₀⟩ := nonempty_class_has_erm X H hH
  let D : finite_dataset X :=
    ⟨s.toList.map (fun x => (x, false)), by
      intro hempty
      have hlist : s.toList = [] := List.map_eq_nil_iff.mp hempty
      have : s.card = 0 := by simpa using congrArg List.length hlist
      omega⟩
  have hspecial : ∀ S : List (labeled_example X), is_selected_sample D q S →
      ∃ u ∈ H, empirical_classification_loss S u = 0 ∧
        s.card - q ≤
          (D.examples.filter fun z => u z.1 != z.2).length := by
    intro S hS
    let P : Finset X := (S.map Prod.fst).toFinset
    let g : X → Bool := fun x => decide (x ∉ P)
    obtain ⟨u, huH, hus⟩ := hshatter g
    have hPsub : P ⊆ s := by
      intro x hx
      have hxlist : x ∈ S.map Prod.fst := by
        simpa [P] using hx
      rcases List.mem_map.mp hxlist with ⟨z, hzS, rfl⟩
      have hzD := hS.2 z hzS
      change z ∈ s.toList.map (fun x => (x, false)) at hzD
      rcases List.mem_map.mp hzD with ⟨y, hy, hyz⟩
      have hyzfst : y = z.1 := congrArg Prod.fst hyz
      rw [← hyzfst]
      simpa using hy
    have hPcard : P.card ≤ q := by
      calc
        P.card ≤ (S.map Prod.fst).length := by
          simpa [P] using List.toFinset_card_le (S.map Prod.fst)
        _ = q := by simp [hS.1]
    have htrain : empirical_classification_loss S u = 0 := by
      unfold empirical_classification_loss
      have hnil : (S.filter fun z => u z.1 != z.2) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro z hz
        have hzD := hS.2 z hz
        change z ∈ s.toList.map (fun x => (x, false)) at hzD
        rcases List.mem_map.mp hzD with ⟨x, hxs, rfl⟩
        have hxP : x ∈ P := by
          simp only [P, List.mem_toFinset, List.mem_map]
          exact ⟨(x, false), hz, rfl⟩
        have hux : u x = false := by
          rw [hus x (by simpa using hxs)]
          simp [g, hxP]
        simp [hux]
      rw [hnil]
      simp
    have herr :
        (D.examples.filter fun z => u z.1 != z.2).length =
          (s.filter fun x => x ∉ P).card := by
      change
        ((s.toList.map (fun x => (x, false))).filter
          fun z => u z.1 != z.2).length =
            (s.filter fun x => x ∉ P).card
      rw [List.filter_map]
      simp only [List.length_map]
      change (s.toList.filter (fun x => u x != false)).length =
        (s.filter fun x => x ∉ P).card
      have hfilter :
          s.toList.filter (fun x => u x != false) =
            s.toList.filter (fun x => x ∉ P) := by
        apply List.filter_congr
        intro x hxs
        rw [hus x (by simpa using hxs)]
        simp [g]
      rw [hfilter]
      rw [← List.toFinset_card_of_nodup (s.nodup_toList.filter _)]
      congr 1
      ext x
      simp
    refine ⟨u, huH, htrain, ?_⟩
    rw [herr]
    have hdiff :
        (s.filter fun x => x ∉ P).card = s.card - P.card := by
      rw [show s.filter (fun x => x ∉ P) = s \ P by ext x; simp]
      exact Finset.card_sdiff_of_subset hPsub
    rw [hdiff]
    exact Nat.sub_le_sub_left hPcard s.card
  let A : erm_rule X := fun S =>
    if hS : is_selected_sample D q S then Classical.choose (hspecial S hS)
    else A₀ S
  have hA : is_erm H A := by
    intro S
    dsimp [A]
    split
    next hS =>
      have hspec := Classical.choose_spec (hspecial S hS)
      refine ⟨hspec.1, ?_⟩
      intro u hu
      rw [hspec.2.1]
      unfold empirical_classification_loss
      positivity
    next hS =>
      exact hA₀ S
  have hh₀D : empirical_classification_loss D.examples h₀ = 0 := by
    unfold empirical_classification_loss
    have hnil : (D.examples.filter fun z => h₀ z.1 != z.2) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro z hz
      change z ∈ s.toList.map (fun x => (x, false)) at hz
      rcases List.mem_map.mp hz with ⟨x, hxs, rfl⟩
      have hx := hh₀s x (by simpa using hxs)
      simp [hx]
    rw [hnil]
    simp
  have hbest : best_class_loss H D = 0 := by
    unfold best_class_loss
    apply le_antisymm
    · apply csInf_le
      · refine ⟨0, ?_⟩
        intro r hr
        rcases hr with ⟨u, hu, rfl⟩
        unfold empirical_classification_loss
        positivity
      · exact ⟨h₀, hh₀, hh₀D.symm⟩
    · apply le_csInf
      · exact ⟨0, h₀, hh₀, hh₀D.symm⟩
      · intro r hr
        rcases hr with ⟨u, hu, rfl⟩
        unfold empirical_classification_loss
        positivity
  rcases (selection_regret_variational H A D q hA).1 with ⟨S, hS, hregret⟩
  have hspec := Classical.choose_spec (hspecial S hS)
  have hAS : A S = Classical.choose (hspecial S hS) := by
    simp [A, hS]
  have herrAS :
      s.card - q ≤ (D.examples.filter fun z => A S z.1 != z.2).length := by
    rw [hAS]
    exact hspec.2.2
  have hDlen : D.examples.length = s.card := by
    simp [D]
  have hqcard : q ≤ s.card := by
    have hδle : δ ≤ 1 := by
      dsimp [δ]
      linarith
    have hqδ : (q : ℝ) ≤ (q : ℝ) / δ := by
      apply (le_div_iff₀ hδ).2
      nlinarith [show (0 : ℝ) ≤ q by positivity]
    have hqN : (q : ℝ) < N := lt_of_le_of_lt hqδ hN
    have hqNnat : q < N := by
      exact_mod_cast hqN
    have hqcardlt : q < s.card := by
      exact hqNnat.trans hsN
    exact hqcardlt.le
  have hfrac :
      worst_selection_regret H q <
        ((s.card - q : ℕ) : ℝ) / (s.card : ℝ) := by
    have hscard : (0 : ℝ) < s.card := by exact_mod_cast hspos
    have hratioN : (q : ℝ) / δ < (s.card : ℝ) :=
      hN.trans (by exact_mod_cast hsN)
    have hratio : (q : ℝ) / (s.card : ℝ) < δ := by
      apply (div_lt_iff₀ hscard).2
      simpa [mul_comm] using (div_lt_iff₀ hδ).mp hratioN
    rw [Nat.cast_sub hqcard]
    dsimp [δ] at hratio
    field_simp
    field_simp at hratio
    linarith
  have hloss :
      ((s.card - q : ℕ) : ℝ) / (s.card : ℝ) ≤
        empirical_classification_loss D.examples (A S) := by
    unfold empirical_classification_loss
    rw [hDlen]
    exact div_le_div_of_nonneg_right (by exact_mod_cast herrAS)
      (by positivity)
  have hregret_gt : worst_selection_regret H q < selection_regret H A D q := by
    rw [hregret, hbest, sub_zero]
    exact hfrac.trans_le hloss
  exact (not_lt_of_ge ((worst_regret_envelope X H q).2.1 A hA D)) hregret_gt

@[blueprint "lem:finite-vc-regret-upper"
  (statement := /-- Let $X$ be a domain and let $\mathcal H$ be a binary hypothesis class on $X$. Suppose that some $d\in\mathbb N$ bounds the cardinality of every finite set shattered by $\mathcal H$. Then there is a constant $C_2>0$ such that
  \[
    R^\star_{\mathcal H}(n)\le \frac{C_2\log n}{n}
  \]
  for every natural number $n\ge2$. -/)
  (proof := /-- Apply \cref{lem:epsnet-vc} with the given VC bound. Fix an ERM $A$ and a nonempty dataset $D$, and let $h_0=A(D)$; by the ERM property, $h_0$ attains the best full-data loss. Let $G$ be the sublist of examples correctly classified by $h_0$. If $G$ is empty, the best loss is one and \cref{lem:selection-regret-variational} forces the nonnegative selection regret to be zero. Otherwise, \cref{lem:epsnet-vc} supplies a length-$n$ list $S$ selected from $G$. Since $h_0$ is consistent with $S$, every ERM output $A(S)$ has zero loss on $S$ and is therefore consistent with it. The epsilon-net conclusion bounds the fraction of $G$ misclassified by $A(S)$ by $C(d+1)\log n/n$.

  Every full-data error of $A(S)$ either lies in $G$ or is already an error of $h_0$. Hence the excess full-data loss over $h_0$ is at most the number of errors of $A(S)$ on $G$, divided by $|D|$. Since $|G|\le |D|$, this is bounded by the epsilon-net estimate. The infimum defining selection regret is at most the value at $S$, and the common-upper-bound implication in \cref{lem:worst-regret-envelope} gives the asserted worst-case bound with $C_2=C(d+1)$. -/)
  (title := /-- Regret upper bound for finite-VC classes -/)
  (latexEnv := "lemma")]
lemma finite_vc_regret_upper (X : Type) (H : hypothesis_class X) (d : ℕ)
    (hvc : ∀ s : Finset X, d < s.card →
      ¬ ∀ g : X → Bool, ∃ h ∈ H, ∀ x ∈ s, h x = g x) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ n : ℕ, 2 ≤ n →
      worst_selection_regret H n ≤ C₂ * Real.log (n : ℝ) / (n : ℝ) := by
  classical
  obtain ⟨C, hC, hnet⟩ := epsnet_vc X H d hvc
  let C₂ : ℝ := C * (d + 1)
  refine ⟨C₂, by dsimp [C₂]; positivity, ?_⟩
  intro n hn
  have hlog : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n by omega)
  apply (worst_regret_envelope X H n).2.2
  · dsimp [C₂]
    positivity
  · intro A hA D
    let h₀ : binary_hypothesis X := A D.examples
    have hh₀ : h₀ ∈ H := (hA D.examples).1
    have hmin₀ : ∀ u ∈ H, empirical_classification_loss D.examples h₀ ≤
        empirical_classification_loss D.examples u :=
      (hA D.examples).2
    let G : List (labeled_example X) :=
      D.examples.filter fun z => h₀ z.1 == z.2
    have hloss (L : List (labeled_example X)) (u : binary_hypothesis X) :
        0 ≤ empirical_classification_loss L u ∧
          empirical_classification_loss L u ≤ 1 := by
      constructor
      · unfold empirical_classification_loss
        positivity
      · by_cases hL : L = []
        · simp [hL, empirical_classification_loss]
        · unfold empirical_classification_loss
          apply (div_le_one (by
            exact_mod_cast List.length_pos_iff.mpr hL)).2
          exact_mod_cast List.length_filter_le (fun z => u z.1 != z.2) L
    have hbest : best_class_loss H D =
        empirical_classification_loss D.examples h₀ := by
      unfold best_class_loss
      apply le_antisymm
      · apply csInf_le
        · refine ⟨0, ?_⟩
          intro r hr
          rcases hr with ⟨u, hu, rfl⟩
          exact (hloss D.examples u).1
        · exact ⟨h₀, hh₀, rfl⟩
      · apply le_csInf
        · exact ⟨_, h₀, hh₀, rfl⟩
        · intro r hr
          rcases hr with ⟨u, hu, rfl⟩
          exact hmin₀ u hu
    have hcount (u : binary_hypothesis X) :
        (D.examples.filter fun z => u z.1 != z.2).length ≤
          (G.filter fun z => u z.1 != z.2).length +
            (D.examples.filter fun z => h₀ z.1 != z.2).length := by
      dsimp [G]
      induction D.examples with
      | nil => simp
      | cons z L ih =>
          have ih' :
              (L.filter fun z => u z.1 != z.2).length ≤
                (L.filter fun z =>
                  u z.1 != z.2 && h₀ z.1 == z.2).length +
                  (L.filter fun z => h₀ z.1 != z.2).length := by
            simpa [List.filter_filter, Bool.and_comm] using ih
          by_cases hz₀ : h₀ z.1 = z.2
          · by_cases hzu : u z.1 = z.2
            · simp [hz₀, hzu]
              exact ih'
            · simp [hz₀, hzu]
              omega
          · by_cases hzu : u z.1 = z.2
            · simp [hz₀, hzu]
              omega
            · simp [hz₀, hzu]
              omega
    by_cases hG : G = []
    · rcases (selection_regret_variational H A D n hA).1 with
        ⟨S, hS, hregret⟩
      have herrall :
          D.examples.filter (fun z => h₀ z.1 != z.2) = D.examples := by
        apply List.filter_eq_self.mpr
        intro z hz
        have hne : h₀ z.1 ≠ z.2 := by
          intro hzcorrect
          have hzG : z ∈ G := by
            simp [G, hz, hzcorrect]
          rw [hG] at hzG
          simp at hzG
        simpa [hne]
      have hh₀loss : empirical_classification_loss D.examples h₀ = 1 := by
        unfold empirical_classification_loss
        rw [herrall]
        exact div_self (by
          exact_mod_cast (List.length_pos_iff.mpr D.nonempty).ne')
      have hzero : selection_regret H A D n = 0 := by
        apply le_antisymm
        · rw [hregret, hbest, hh₀loss]
          linarith [(hloss D.examples (A S)).2]
        · exact (selection_regret_variational H A D n hA).2.1
      rw [hzero]
      dsimp [C₂]
      positivity
    · obtain ⟨S, hSlen, hSmem, huniform⟩ := hnet G n hG hn
      have hselected : is_selected_sample D n S := by
        refine ⟨hSlen, ?_⟩
        intro z hz
        exact List.mem_of_mem_filter (hSmem z hz)
      have hSzero : empirical_classification_loss S h₀ = 0 := by
        unfold empirical_classification_loss
        have hnil : (S.filter fun z => h₀ z.1 != z.2) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro z hz
          have hzG := hSmem z hz
          have hzcorrect : h₀ z.1 = z.2 := by
            have hzG' : z ∈ D.examples ∧ h₀ z.1 = z.2 := by
              simpa [G] using hzG
            exact hzG'.2
          simp [hzcorrect]
        rw [hnil]
        simp
      have hASzero : empirical_classification_loss S (A S) = 0 := by
        apply le_antisymm
        · exact (hA S).2 h₀ hh₀ |>.trans_eq hSzero
        · exact (hloss S (A S)).1
      have hconsistent : ∀ z ∈ S, A S z.1 = z.2 := by
        have hfilter :
            (S.filter fun z => A S z.1 != z.2) = [] := by
          have hden : (S.length : ℝ) ≠ 0 := by
            rw [hSlen]
            positivity
          have hnum :
              (((S.filter fun z => A S z.1 != z.2).length : ℕ) : ℝ) = 0 := by
            exact (div_eq_zero_iff.mp hASzero).resolve_right hden
          apply List.length_eq_zero_iff.mp
          exact_mod_cast hnum
        intro z hz
        have hzfalse := List.filter_eq_nil_iff.mp hfilter z hz
        simpa using hzfalse
      have hnetbound := huniform (A S) (hA S).1 hconsistent
      have hDpos : (0 : ℝ) < D.examples.length := by
        exact_mod_cast List.length_pos_iff.mpr D.nonempty
      have hGpos : (0 : ℝ) < G.length := by
        exact_mod_cast List.length_pos_iff.mpr hG
      have hGleD : G.length ≤ D.examples.length := by
        exact List.length_filter_le _ _
      have hbound_nonneg :
          0 ≤ C * (d + 1) * Real.log n / n := by
        positivity
      have hgood :
          (((G.filter fun z => A S z.1 != z.2).length : ℕ) : ℝ) /
              D.examples.length ≤ C * (d + 1) * Real.log n / n := by
        apply (div_le_iff₀ hDpos).2
        have hnum :=
          (div_le_iff₀ hGpos).mp hnetbound
        have hGleDreal : (G.length : ℝ) ≤ D.examples.length := by
          exact_mod_cast hGleD
        nlinarith
      have hexcess :
          empirical_classification_loss D.examples (A S) -
              best_class_loss H D ≤
            (((G.filter fun z => A S z.1 != z.2).length : ℕ) : ℝ) /
              D.examples.length := by
        rw [hbest]
        unfold empirical_classification_loss
        apply (sub_le_iff_le_add).2
        rw [← add_div]
        apply div_le_div_of_nonneg_right
        · exact_mod_cast hcount (A S)
        · exact hDpos.le
      have hbdd : BddBelow
          {r : ℝ | ∃ T : List (labeled_example X),
            is_selected_sample D n T ∧
              r = empirical_classification_loss D.examples (A T) -
                best_class_loss H D} := by
        refine ⟨-1, ?_⟩
        intro r hr
        rcases hr with ⟨T, hT, rfl⟩
        rw [hbest]
        linarith [(hloss D.examples (A T)).1, (hloss D.examples h₀).2]
      rw [selection_regret]
      exact (csInf_le hbdd ⟨S, hselected, rfl⟩).trans
        (hexcess.trans hgood)

@[blueprint "lem:nontrivial-regret-upper"
  (statement := /-- Let $X$ be a domain and let $\mathcal H$ be a binary hypothesis class on $X$. If $R^\star_{\mathcal H}$ does not have the trivial rate, then there is a constant $C_2>0$, depending only on $\mathcal H$, such that
  \[
    R^\star_{\mathcal H}(n)\le \frac{C_2\log n}{n}
  \]
  for every natural number $n\ge2$. -/)
  (proof := /-- By \cref{lem:nontrivial-regret-finite-vc}, failure of the trivial regime yields a natural number $d$ such that no finite subset of $X$ of cardinality greater than $d$ is shattered by $\mathcal H$. Applying \cref{lem:finite-vc-regret-upper} to this $d$ produces a positive constant $C_2$ and the required estimate for every natural number $n\ge2$. -/)
  (title := /-- Logarithmic-over-linear upper bound outside the trivial regime -/)
  (latexEnv := "lemma")]
lemma nontrivial_regret_upper (X : Type) (H : hypothesis_class X)
    (h : ¬ trivial_rate (worst_selection_regret H)) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ n : ℕ, 2 ≤ n →
      worst_selection_regret H n ≤ C₂ * Real.log (n : ℝ) / (n : ℝ) := by
  obtain ⟨d, hvc⟩ := nontrivial_regret_finite_vc X H h
  exact finite_vc_regret_upper X H d hvc

@[blueprint "def:star-set"
  (statement := /-- Let $X$ be a domain and let $\mathcal H$ be a binary hypothesis class on $X$. A star set for $\mathcal H$ is a finite list $T$ of pairwise distinct points for which there are a center $h_0\in\mathcal H$ and, for every $x\in T$, a hypothesis $h_x\in\mathcal H$ such that $h_x(x)\ne h_0(x)$ and $h_x(y)=h_0(y)$ for every $y\in T\setminus\{x\}$. -/)
  (title := /-- Star sets for a binary hypothesis class -/)
  (latexEnv := "definition")]
def star_set {X : Type} (H : hypothesis_class X) (T : List X) : Prop :=
  T.Nodup ∧ ∃ h₀ ∈ H, ∀ x ∈ T, ∃ h ∈ H,
    h x ≠ h₀ x ∧ ∀ y ∈ T, y ≠ x → h y = h₀ y

@[blueprint "lem:nonzero-star-witness"
  (statement := /-- Let $X$ be a domain and let $\mathcal H$ be a binary hypothesis class on $X$. If the worst-case selection-regret sequence of $\mathcal H$ is not eventually zero, then, for every $m\in\mathbb N$, the class $\mathcal H$ has a star set of cardinality $m$. -/)
  (proof := /-- We prove the contrapositive. Suppose that $\mathcal H$ has no star set of cardinality $m$. If $m=0$, then \cref{def:star-set} implies that $\mathcal H$ is empty. There is consequently no ERM over $\mathcal H$, and the empty-supremum case of \cref{lem:worst-regret-envelope} shows that the worst-case regret is identically zero. We may therefore assume that $m\ge1$.

  Fix an ERM $A$ over $\mathcal H$ and a finite nonempty dataset $D$. Choose $h_0\in\mathcal H$ having minimum empirical loss on $D$; such a hypothesis exists because $\mathcal H$ is nonempty and the numerator of the empirical loss takes values in the finite set $\{0,\ldots,|D|\}$. Let $C$ be the finite set of points $x$ for which the labeled example $(x,h_0(x))$ occurs in $D$. Every $h\in\mathcal H$ that agrees with $h_0$ on $C$ is also a full-data minimizer. Indeed, if $h$ had strictly larger loss, then the number of examples on which $h$ is wrong and $h_0$ is correct would exceed the number on which $h$ is correct and $h_0$ is wrong; in particular the former set would be nonempty, contradicting agreement on $C$.

  Starting from $C$, delete one point per round whenever the remaining set still has the property that agreement with $h_0$ forces full-data optimality. Finiteness makes this procedure terminate at an inclusion-minimal subset $T\subseteq C$ with that property. For each $x\in T$, minimality gives $h_x\in\mathcal H$ which agrees with $h_0$ on $T\setminus\{x\}$ but is not a full-data minimizer. The defining property of $T$ then forces $h_x(x)\ne h_0(x)$. Thus, if $|T|\ge m$, any $m$ points of $T$, together with $h_0$ and the corresponding hypotheses $h_x$, form a star set of cardinality $m$ in the sense of \cref{def:star-set}, contrary to the assumption. Hence $|T|<m$.

  Let $n\ge m$. If $T$ is nonempty, form a selected list $S$ of length $n$ by taking once each labeled example $(x,h_0(x))$ with $x\in T$ and filling the remaining positions with repetitions of one of them. If $T$ is empty, take $n$ repetitions of any example of the nonempty dataset $D$. In the first case $h_0$ has zero loss on $S$, so the ERM $A(S)$ also has zero loss on $S$ and therefore agrees with $h_0$ on $T$; it is consequently a full-data minimizer. In the second case every member of $\mathcal H$ is already a full-data minimizer. In both cases the selected sample has zero excess full-data loss. The definition of selection regret and its nonnegativity in \cref{lem:selection-regret-variational} give $R^\star_{\mathcal H}(n;A,D)=0$. Since $A$ and $D$ were arbitrary, the common-upper-bound conclusion of \cref{lem:worst-regret-envelope}, with upper bound zero, gives $R^\star_{\mathcal H}(n)=0$ for every $n\ge m$. This is the zero rate, proving the contrapositive. -/)
  (title := /-- Failure of the zero rate yields arbitrarily large star sets -/)
  (latexEnv := "lemma")]
lemma nonzero_star_witness (X : Type) (H : hypothesis_class X)
    (h : ¬ zero_rate (worst_selection_regret H)) :
    ∀ m : ℕ, ∃ T : List X, T.length = m ∧ star_set H T := by
  classical
  intro m
  by_contra hstar
  apply h
  refine ⟨m, ?_⟩
  intro n hmn
  have hworst := worst_regret_envelope X H n
  apply le_antisymm
  · apply hworst.2.2 0 le_rfl
    intro A hA D
    by_cases hm : m = 0
    · subst m
      exfalso
      apply hstar
      refine ⟨[], rfl, ?_⟩
      refine ⟨List.nodup_nil, A [], (hA []).1, ?_⟩
      simp
    · let h₀ : binary_hypothesis X := A D.examples
      have hh₀ : h₀ ∈ H := (hA D.examples).1
      have hmin₀ : ∀ g ∈ H,
          empirical_classification_loss D.examples h₀ ≤
            empirical_classification_loss D.examples g :=
        (hA D.examples).2
      let C : Finset X :=
        (D.examples.toFinset.image Prod.fst).filter
          (fun x => (x, h₀ x) ∈ D.examples)
      let forces : Finset X → Prop := fun T =>
        ∀ g ∈ H, (∀ x ∈ T, g x = h₀ x) →
          empirical_classification_loss D.examples g =
            empirical_classification_loss D.examples h₀
      have hCforces : forces C := by
        intro g hg hagree
        apply le_antisymm
        · unfold empirical_classification_loss
          apply div_le_div_of_nonneg_right
          · norm_cast
            have hfilter_le : ∀ L : List (labeled_example X), L ⊆ D.examples →
                (L.filter fun z => g z.1 != z.2).length ≤
                  (L.filter fun z => h₀ z.1 != z.2).length := by
              intro L hLD
              induction L with
              | nil => simp
              | cons z L ih =>
                  have hzD : z ∈ D.examples := hLD (by simp)
                  have hLD' : L ⊆ D.examples := by
                    intro w hw
                    exact hLD (by simp [hw])
                  have hle := ih hLD'
                  by_cases hgerr : g z.1 != z.2
                  · have hh₀err : h₀ z.1 != z.2 := by
                      simp only [bne_iff_ne] at hgerr ⊢
                      intro hh₀eq
                      have hzC : z.1 ∈ C := by
                        simp only [C, Finset.mem_filter, Finset.mem_image,
                          List.mem_toFinset]
                        constructor
                        · exact ⟨z, hzD, rfl⟩
                        · simpa [hh₀eq] using hzD
                      exact hgerr ((hagree z.1 hzC).trans hh₀eq)
                    rw [List.filter_cons, List.filter_cons, if_pos hgerr,
                      if_pos hh₀err]
                    simp only [List.length_cons]
                    omega
                  · by_cases hh₀err : h₀ z.1 != z.2
                    · rw [List.filter_cons, List.filter_cons, if_neg hgerr,
                        if_pos hh₀err]
                      simp only [List.length_cons]
                      omega
                    · rw [List.filter_cons, List.filter_cons, if_neg hgerr,
                        if_neg hh₀err]
                      exact hle
            exact hfilter_le D.examples (by intro z hz; exact hz)
          · positivity
        · exact hmin₀ g hg
      let candidates : Finset (Finset X) := C.powerset.filter forces
      have hCmem : C ∈ candidates := by
        simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.Subset.rfl, hCforces⟩
      obtain ⟨T, hTmem, hTmin⟩ :=
        candidates.exists_min_image Finset.card ⟨C, hCmem⟩
      have hTC : T ⊆ C := by
        exact Finset.mem_powerset.mp (Finset.mem_filter.mp hTmem).1
      have hTforces : forces T := by
        exact (Finset.mem_filter.mp hTmem).2
      have hcritical : ∀ x ∈ T, ∃ g ∈ H,
          g x ≠ h₀ x ∧ ∀ y ∈ T, y ≠ x → g y = h₀ y := by
        intro x hx
        have hnotforces : ¬ forces (T.erase x) := by
          intro herase
          have herase_mem : T.erase x ∈ candidates := by
            simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
            exact ⟨(Finset.erase_subset x T).trans hTC, herase⟩
          have hle := hTmin (T.erase x) herase_mem
          have hcard := T.card_erase_add_one hx
          omega
        simp only [forces, not_forall, _root_.not_imp] at hnotforces
        rcases hnotforces with ⟨g, hg, hagree, hne⟩
        refine ⟨g, hg, ?_, ?_⟩
        · intro heq
          apply hne
          apply hTforces g hg
          intro y hy
          by_cases hyx : y = x
          · simpa [hyx] using heq
          · exact hagree y (Finset.mem_erase.mpr ⟨hyx, hy⟩)
        · intro y hy hyx
          exact hagree y (Finset.mem_erase.mpr ⟨hyx, hy⟩)
      have hTcard : T.card < m := by
        apply Nat.lt_of_not_ge
        intro hmT
        obtain ⟨U, hUT, hUcard⟩ := Finset.exists_subset_card_eq hmT
        apply hstar
        refine ⟨U.toList, by simpa using hUcard, ?_⟩
        refine ⟨U.nodup_toList, h₀, hh₀, ?_⟩
        intro x hx
        have hxU : x ∈ U := by simpa using hx
        rcases hcritical x (hUT hxU) with ⟨g, hg, hdiff, hagree⟩
        refine ⟨g, hg, hdiff, ?_⟩
        intro y hy hyx
        have hyU : y ∈ U := by simpa using hy
        exact hagree y (hUT hyU) hyx
      have hbest : best_class_loss H D =
          empirical_classification_loss D.examples h₀ := by
        unfold best_class_loss
        apply le_antisymm
        · apply csInf_le
          · refine ⟨0, ?_⟩
            intro r hr
            rcases hr with ⟨g, hg, rfl⟩
            unfold empirical_classification_loss
            exact div_nonneg (by positivity) (by positivity)
          · exact ⟨h₀, hh₀, rfl⟩
        · apply le_csInf
          · exact ⟨_, h₀, hh₀, rfl⟩
          · intro r hr
            rcases hr with ⟨g, hg, rfl⟩
            exact hmin₀ g hg
      have hsample : ∃ S : List (labeled_example X),
          is_selected_sample D n S ∧
            empirical_classification_loss D.examples (A S) =
              empirical_classification_loss D.examples h₀ := by
        by_cases hTempty : T = ∅
        · obtain ⟨z, hzD⟩ := List.exists_mem_of_ne_nil D.examples D.nonempty
          let S := List.replicate n z
          refine ⟨S, ?_, ?_⟩
          · refine ⟨by simp [S], ?_⟩
            intro w hw
            have hwz : w = z := List.eq_of_mem_replicate hw
            simpa [hwz] using hzD
          · apply hTforces (A S) (hA S).1
            intro x hx
            simp [hTempty] at hx
        · obtain ⟨x₀, hx₀⟩ := T.nonempty_iff_ne_empty.mpr hTempty
          have hTn : T.card ≤ n :=
            (Nat.le_of_lt hTcard).trans hmn
          have hnpos : 0 < n :=
            (Nat.pos_of_ne_zero hm).trans_le hmn
          let S := T.toList.map (fun x => (x, h₀ x)) ++
            List.replicate (n - T.card) (x₀, h₀ x₀)
          have hSlen : S.length = n := by
            simp [S, Nat.add_sub_of_le hTn]
          have hSselected : is_selected_sample D n S := by
            refine ⟨hSlen, ?_⟩
            intro z hz
            rcases List.mem_append.mp hz with hz | hz
            · rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
              have hxT : x ∈ T := by simpa using hx
              have hxC := hTC hxT
              exact (Finset.mem_filter.mp hxC).2
            · have hzeq : z = (x₀, h₀ x₀) := List.eq_of_mem_replicate hz
              subst z
              have hxC := hTC hx₀
              exact (Finset.mem_filter.mp hxC).2
          have hh₀zero : empirical_classification_loss S h₀ = 0 := by
            unfold empirical_classification_loss
            have hfilt : (S.filter fun z => h₀ z.1 != z.2) = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro z hz
              rcases List.mem_append.mp hz with hz | hz
              · rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
                simp
              · have hzeq : z = (x₀, h₀ x₀) := List.eq_of_mem_replicate hz
                subst z
                simp
            rw [hfilt]
            simp
          have hASzero : empirical_classification_loss S (A S) = 0 := by
            have hle := (hA S).2 h₀ hh₀
            rw [hh₀zero] at hle
            have hnonneg : 0 ≤ empirical_classification_loss S (A S) := by
              unfold empirical_classification_loss
              exact div_nonneg (by positivity) (by positivity)
            linarith
          have hASagree : ∀ x ∈ T, A S x = h₀ x := by
            intro x hx
            by_contra hdiff
            have hxS : (x, h₀ x) ∈ S := by
              apply List.mem_append_left
              exact List.mem_map.mpr ⟨x, by simpa using hx, rfl⟩
            have hxerr : (x, h₀ x) ∈
                S.filter (fun z => A S z.1 != z.2) := by
              apply List.mem_filter.mpr
              exact ⟨hxS, by simpa only [bne_iff_ne]⟩
            have hnumpos : 0 <
                (S.filter fun z => A S z.1 != z.2).length :=
              List.length_pos_iff_exists_mem.mpr ⟨_, hxerr⟩
            have hdenpos : 0 < (S.length : ℝ) := by
              rw [hSlen]
              exact_mod_cast hnpos
            have hlosspos : 0 < empirical_classification_loss S (A S) := by
              unfold empirical_classification_loss
              exact div_pos (by exact_mod_cast hnumpos) hdenpos
            linarith
          refine ⟨S, hSselected, ?_⟩
          exact hTforces (A S) (hA S).1 hASagree
      rcases hsample with ⟨S, hSselected, hSoptimal⟩
      have hselection_le : selection_regret H A D n ≤ 0 := by
        unfold selection_regret
        apply csInf_le
        · refine ⟨0, ?_⟩
          intro r hr
          rcases hr with ⟨S', hS', rfl⟩
          rw [hbest]
          exact sub_nonneg.mpr (hmin₀ (A S') (hA S').1)
        · refine ⟨S, hSselected, ?_⟩
          rw [hSoptimal, hbest]
          ring
      have hselection_nonneg : 0 ≤ selection_regret H A D n :=
        (selection_regret_variational H A D n hA).2.1
      exact (le_antisymm hselection_le hselection_nonneg).le
  · exact hworst.1.1

@[blueprint "lem:nonzero-regret-lower"
  (statement := /-- Let $X$ be a domain and let $\mathcal H$ be a binary hypothesis class on $X$. If $R^\star_{\mathcal H}$ is not eventually zero, then there is a constant $C_1>0$, depending only on $\mathcal H$, such that
  \[
    \frac{C_1}{n}\le R^\star_{\mathcal H}(n)
  \]
  for every natural number $n\ge2$. -/)
  (proof := /-- Write $R(n)=R^\star_{\mathcal H}(n)$ and fix $n\ge2$. By \cref{lem:nonzero-star-witness}, there are $n+1$ distinct points $T=\{x_0,\ldots,x_n\}$ forming a star set. Unpack \cref{def:star-set}: there are a center $h_0\in\mathcal H$ and hypotheses $h_i\in\mathcal H$ such that $h_i(x_i)\ne h_0(x_i)$ and $h_i(x_j)=h_0(x_j)$ whenever $j\ne i$. Form the finite nonempty dataset
  \[
    D=((x_0,h_0(x_0)),\ldots,(x_n,h_0(x_n))).
  \]
  The center has zero loss on $D$, whereas every $h_i$ has loss exactly $1/(n+1)$.

  Every list $S$ of length $n$ selected from $D$ omits at least one of the $n+1$ distinct examples, say $(x_i,h_0(x_i))$. The hypothesis $h_i$ agrees with every label occurring in $S$ and hence is an empirical minimizer on $S$. Define a learning rule $A$ on such lists by choosing one omitted index and returning the corresponding $h_i$. On every other finite labeled list, let $A$ return an empirical minimizer in $\mathcal H$. Such a minimizer exists because the star center makes $\mathcal H$ nonempty and empirical losses on a fixed finite list have only finitely many possible numerators. This defines an ERM in the sense of \cref{def:is-erm}.

  For every length-$n$ sample selected from $D$, the output of $A$ has full-data loss $1/(n+1)$, while the best class loss is zero. The variational identity in \cref{lem:selection-regret-variational} therefore gives
  \[
    R^\star_{\mathcal H}(n;A,D)\ge \frac{1}{n+1}\ge\frac{1}{2n}.
  \]
  The memberwise assertion of \cref{lem:worst-regret-envelope} gives the same lower bound for $R(n)$. Since $n\ge2$ was arbitrary, taking $C_1=1/2$ proves the claim. -/)
  (title := /-- Linear lower bound outside the zero regime -/)
  (latexEnv := "lemma")]
lemma nonzero_regret_lower (X : Type) (H : hypothesis_class X)
    (h : ¬ zero_rate (worst_selection_regret H)) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ n : ℕ, 2 ≤ n →
      C₁ / (n : ℝ) ≤ worst_selection_regret H n := by
  classical
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro n hn
  rcases nonzero_star_witness X H h (n + 1) with ⟨T, hTlen, hT⟩
  rcases hT with ⟨hTnodup, h₀, hh₀, hstar⟩
  let E : List (labeled_example X) := T.map (fun x => (x, h₀ x))
  have hinj : Function.Injective (fun x : X => (x, h₀ x)) := by
    intro x y hxy
    exact congrArg Prod.fst hxy
  have hEnodup : E.Nodup := by
    exact hTnodup.map hinj
  have hElen : E.length = n + 1 := by
    simp [E, hTlen]
  have hEne : E ≠ [] := by
    intro hE
    have : E.length = 0 := by simp [hE]
    omega
  let D : finite_dataset X := ⟨E, hEne⟩
  have homit : ∀ S : List (labeled_example X), is_selected_sample D n S →
      ∃ x ∈ T, (x, h₀ x) ∉ S := by
    intro S hS
    by_contra hnone
    push Not at hnone
    have hsub : E.toFinset ⊆ S.toFinset := by
      intro z hz
      simp only [List.mem_toFinset] at hz ⊢
      rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
      exact hnone x hx
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hEnodup] at hcard
    have hScard : S.toFinset.card ≤ S.length := by
      simpa using (List.toFinset_card_le (l := S))
    rw [hElen] at hcard
    rw [hS.1] at hScard
    omega
  have hbad : ∀ S : List (labeled_example X), is_selected_sample D n S →
      ∃ g ∈ H, (∀ z ∈ S, g z.1 = z.2) ∧
        empirical_classification_loss D.examples g =
          1 / ((n + 1 : ℕ) : ℝ) := by
    intro S hS
    rcases homit S hS with ⟨x, hxT, hxS⟩
    rcases hstar x hxT with ⟨g, hg, hgx, hagree⟩
    refine ⟨g, hg, ?_, ?_⟩
    · intro z hzS
      have hzD := hS.2 z hzS
      change z ∈ E at hzD
      rcases List.mem_map.mp hzD with ⟨y, hyT, rfl⟩
      have hyx : y ≠ x := by
        intro hyx
        subst y
        exact hxS hzS
      simpa using hagree y hyT hyx
    · have hDnodup : D.examples.Nodup := by
        exact hEnodup
      have hfilterlen :
          (D.examples.filter fun z => g z.1 != z.2).length = 1 := by
        rw [← List.toFinset_card_of_nodup (hDnodup.filter _)]
        have hfilterset :
            (D.examples.filter fun z => g z.1 != z.2).toFinset =
              {(x, h₀ x)} := by
          ext z
          simp only [List.mem_toFinset, List.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hzD, hzerr⟩
            change z ∈ E at hzD
            rcases List.mem_map.mp hzD with ⟨y, hyT, rfl⟩
            have hyx : y = x := by
              by_contra hyx
              have hgy := hagree y hyT hyx
              simp [hgy] at hzerr
            subst y
            rfl
          · intro hz
            subst z
            refine ⟨?_, ?_⟩
            · change (x, h₀ x) ∈ E
              exact List.mem_map.mpr ⟨x, hxT, rfl⟩
            · simpa only [bne_iff_ne] using hgx
        rw [hfilterset]
        simp
      unfold empirical_classification_loss
      rw [hfilterlen]
      rw [show D.examples.length = n + 1 by exact hElen]
      norm_num
  have hloss_zero : ∀ (S : List (labeled_example X)) (g : binary_hypothesis X),
      (∀ z ∈ S, g z.1 = z.2) → empirical_classification_loss S g = 0 := by
    intro S g hagree
    unfold empirical_classification_loss
    have hfilter : (S.filter fun z => g z.1 != z.2) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro z hz
      simp [hagree z hz]
    rw [hfilter]
    simp
  have hmin : ∀ S : List (labeled_example X),
      ∃ g ∈ H, ∀ f ∈ H,
        empirical_classification_loss S g ≤
          empirical_classification_loss S f := by
    intro S
    let P : ℕ → Prop := fun k =>
      ∃ g ∈ H, (S.filter fun z => g z.1 != z.2).length = k
    have hP : ∃ k, P k := by
      exact ⟨_, h₀, hh₀, rfl⟩
    rcases Nat.find_spec hP with ⟨g, hg, hglen⟩
    refine ⟨g, hg, ?_⟩
    intro f hf
    unfold empirical_classification_loss
    apply div_le_div_of_nonneg_right
    · exact_mod_cast (show
          (S.filter fun z => g z.1 != z.2).length ≤
            (S.filter fun z => f z.1 != z.2).length by
        rw [hglen]
        exact Nat.find_min' hP ⟨f, hf, rfl⟩)
    · positivity
  let A : erm_rule X := fun S =>
    if hS : is_selected_sample D n S then
      Classical.choose (hbad S hS)
    else
      Classical.choose (hmin S)
  have hA : is_erm H A := by
    intro S
    dsimp [A]
    split
    next hS =>
      have hspec := Classical.choose_spec (hbad S hS)
      refine ⟨hspec.1, ?_⟩
      intro f hf
      have hAzero : empirical_classification_loss S
          (Classical.choose (hbad S hS)) = 0 := by
        exact hloss_zero S _ hspec.2.1
      rw [hAzero]
      unfold empirical_classification_loss
      exact div_nonneg (by positivity) (by positivity)
    next hS =>
      exact Classical.choose_spec (hmin S)
  have hAfull : ∀ S : List (labeled_example X), is_selected_sample D n S →
      empirical_classification_loss D.examples (A S) =
        1 / ((n + 1 : ℕ) : ℝ) := by
    intro S hS
    dsimp [A]
    split
    next hS' =>
      exact (Classical.choose_spec (hbad S hS')).2.2
    next hS' =>
      exact (hS' hS).elim
  have hh₀D : empirical_classification_loss D.examples h₀ = 0 := by
    unfold empirical_classification_loss
    have hfilter : (D.examples.filter fun z => h₀ z.1 != z.2) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro z hz
      change z ∈ E at hz
      rcases List.mem_map.mp hz with ⟨x, hx, rfl⟩
      simp
    rw [hfilter]
    simp
  have hbest : best_class_loss H D = 0 := by
    unfold best_class_loss
    apply le_antisymm
    · apply csInf_le
      · refine ⟨0, ?_⟩
        intro r hr
        rcases hr with ⟨g, hg, rfl⟩
        unfold empirical_classification_loss
        exact div_nonneg (by positivity) (by positivity)
      · exact ⟨h₀, hh₀, hh₀D.symm⟩
    · apply le_csInf
      · exact ⟨0, h₀, hh₀, hh₀D.symm⟩
      · intro r hr
        rcases hr with ⟨g, hg, rfl⟩
        unfold empirical_classification_loss
        exact div_nonneg (by positivity) (by positivity)
  rcases (selection_regret_variational H A D n hA).1 with ⟨S, hS, hregret⟩
  rw [hAfull S hS, hbest, sub_zero] at hregret
  have hworst := (worst_regret_envelope X H n).2.1 A hA D
  calc
    (1 / 2 : ℝ) / (n : ℝ) = 1 / (2 * (n : ℝ)) := by ring
    _ ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
      rw [one_div_le_one_div (by positivity) (by positivity)]
      norm_num only [Nat.cast_add, Nat.cast_one]
      exact_mod_cast (show n + 1 ≤ 2 * n by omega)
    _ = selection_regret H A D n := hregret.symm
    _ ≤ worst_selection_regret H n := hworst

@[blueprint "lem:rate-regimes-exclusive"
  (statement := /-- For every sequence $R:\mathbb N\to\mathbb R$, the trivial, linear, and zero rate predicates of \cref{def:trivial-rate,def:linear-rate,def:zero-rate} are pairwise incompatible. -/)
  (proof := /-- Use the three rate predicates from \cref{def:trivial-rate,def:linear-rate,def:zero-rate}. Suppose first that $R$ has both the trivial and zero rates. For any $n$ beyond the zero-rate threshold the two assumptions give respectively $R(n)=1$ and $R(n)=0$, a contradiction.

  Suppose next that $R$ has both the linear and zero rates. Let $C_1>0$ be the lower-bound constant and let $n_0$ be the zero-rate threshold. For $n\ge\max\{2,n_0\}$, the linear lower bound gives $0<C_1/n\le R(n)$, whereas the zero-rate condition gives $R(n)=0$, again a contradiction.

  Finally, suppose that $R$ has both the trivial and linear rates, and let $C_2>0$ be the upper-bound constant. Since $\log x/x\to0$ as $x\to\infty$, there is an integer $n\ge2$ such that $C_2\log n/n<1$. The trivial identity and the linear upper bound then imply $1=R(n)<1$, a contradiction. These three contradictions establish pairwise incompatibility. -/)
  (title := /-- Pairwise incompatibility of the three rates -/)
  (latexEnv := "lemma")]
lemma rate_regimes_exclusive (R : ℕ → ℝ) :
    (trivial_rate R → ¬ linear_rate R ∧ ¬ zero_rate R) ∧
      (linear_rate R → ¬ trivial_rate R ∧ ¬ zero_rate R) ∧
      (zero_rate R → ¬ trivial_rate R ∧ ¬ linear_rate R) := by
  have htl : trivial_rate R → ¬ linear_rate R := by
    intro ht hl
    rcases hl with ⟨C₁, C₂, hC₁, hC₂, hbounds⟩
    have hreal : Filter.Tendsto (fun x : ℝ => C₂ * Real.log x / x)
        Filter.atTop (nhds 0) := by
      simpa [mul_div_assoc] using
        (Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 one_ne_zero).const_mul C₂
    have hnat : Filter.Tendsto
        (fun n : ℕ => C₂ * Real.log (n : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) :=
      hreal.comp tendsto_natCast_atTop_atTop
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        C₂ * Real.log (n : ℝ) / (n : ℝ) < 1 :=
      (tendsto_order.1 hnat).2 1 zero_lt_one
    rcases Filter.eventually_atTop.1 hev with ⟨N, hN⟩
    let n := max 2 N
    have hn2 : 2 ≤ n := le_max_left _ _
    have hnN : N ≤ n := le_max_right _ _
    have hnlt := hN n hnN
    have hup := (hbounds n hn2).2
    rw [ht n] at hup
    linarith
  have htz : trivial_rate R → ¬ zero_rate R := by
    intro ht hz
    rcases hz with ⟨n₀, hz⟩
    have hzero := hz n₀ le_rfl
    rw [ht n₀] at hzero
    norm_num at hzero
  have hlz : linear_rate R → ¬ zero_rate R := by
    intro hl hz
    rcases hl with ⟨C₁, C₂, hC₁, hC₂, hbounds⟩
    rcases hz with ⟨n₀, hz⟩
    let n := max 2 n₀
    have hn2 : 2 ≤ n := le_max_left _ _
    have hn0 : n₀ ≤ n := le_max_right _ _
    have hlower := (hbounds n hn2).1
    rw [hz n hn0] at hlower
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn2)
    have hquot : 0 < C₁ / (n : ℝ) := div_pos hC₁ hnpos
    linarith
  constructor
  · intro ht
    exact ⟨htl ht, htz ht⟩
  constructor
  · intro hl
    exact ⟨fun ht => htl ht hl, hlz hl⟩
  · intro hz
    exact ⟨fun ht => htz ht hz, fun hl => hlz hl hz⟩

@[blueprint "thm:binary-classification-regret-trichotomy"
  (statement := /-- Let $X$ be any domain and let $\mathcal H\subseteq\{\pm1\}^X$ be any binary hypothesis class. For the worst-case selection regret $R^\star_{\mathcal H}$ of \cref{def:worst-selection-regret}, exactly one of the following holds in the sense of \cref{def:exactly-one-of-three}:
  \begin{enumerate}
    \item $R^\star_{\mathcal H}(n)=1$ for every $n\in\mathbb N$ as in \cref{def:trivial-rate};
    \item there exist constants $C_1,C_2>0$, depending on $\mathcal H$ but not on $n$, such that
    \[
      \frac{C_1}{n}\le R^\star_{\mathcal H}(n)
      \le\frac{C_2\log n}{n}
    \]
    for every $n\in\mathbb N$ with $n\ge 2$, as in \cref{def:linear-rate};
    \item there exists $n_0\in\mathbb N$, depending on $\mathcal H$, such that $R^\star_{\mathcal H}(n)=0$ for every $n\ge n_0$, as in \cref{def:zero-rate}.
  \end{enumerate} -/)
  (proof := /-- Put $R=R^\star_{\mathcal H}$. If $R$ has the trivial rate, \cref{lem:rate-regimes-exclusive} shows that it has neither the linear nor the zero rate, which is the first alternative in \cref{def:exactly-one-of-three}.

  Assume henceforth that the trivial rate fails. If the zero rate holds, \cref{lem:rate-regimes-exclusive} also excludes the linear rate, giving the third alternative. It remains to consider the case in which both the trivial and zero rates fail. By \cref{lem:nontrivial-regret-upper}, there is a constant $C_2>0$ giving the upper estimate $R(n)\le C_2\log n/n$ for every $n\ge2$. By \cref{lem:nonzero-regret-lower}, there is a constant $C_1>0$ giving the lower estimate $C_1/n\le R(n)$ for every $n\ge2$. These two estimates are precisely the linear-rate predicate, and \cref{lem:rate-regimes-exclusive} excludes the other two predicates. Thus exactly one of the three alternatives holds in all cases. -/)
  (title := /-- Binary classification regret trichotomy -/)
  (latexEnv := "theorem")]
theorem binary_classification_regret_trichotomy (X : Type)
    (H : hypothesis_class X) :
    exactly_one_of_three
      (trivial_rate (worst_selection_regret H))
      (linear_rate (worst_selection_regret H))
      (zero_rate (worst_selection_regret H)) := by
  have hexclusive := rate_regimes_exclusive (worst_selection_regret H)
  by_cases htrivial : trivial_rate (worst_selection_regret H)
  · exact Or.inl ⟨htrivial, (hexclusive.1 htrivial).1, (hexclusive.1 htrivial).2⟩
  by_cases hzero : zero_rate (worst_selection_regret H)
  · exact Or.inr (Or.inr ⟨htrivial, (hexclusive.2.2 hzero).2, hzero⟩)
  · rcases nontrivial_regret_upper X H htrivial with ⟨C₂, hC₂, hupper⟩
    rcases nonzero_regret_lower X H hzero with ⟨C₁, hC₁, hlower⟩
    have hlinear : linear_rate (worst_selection_regret H) := by
      exact ⟨C₁, C₂, hC₁, hC₂, fun n hn => ⟨hlower n hn, hupper n hn⟩⟩
    exact Or.inr (Or.inl ⟨htrivial, hlinear, hzero⟩)

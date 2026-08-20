import Architect
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

@[blueprint "def:euclidean-point"
  (statement := /-- For $d\in\mathbb N$, a point of $\mathbb R^d$ is represented by a function from $\operatorname{Fin}(d)$ to $\mathbb R$. -/)
  (title := /-- Euclidean points -/)
  (latexEnv := "definition")]
abbrev euclidean_point (d : ℕ) := Fin d → ℝ

@[blueprint "def:randomized-mechanism"
  (statement := /-- A discrete randomized mechanism from an input type $I$ to an output type $O$ assigns a probability mass function on $O$ to each input. -/)
  (title := /-- Discrete randomized mechanisms -/)
  (latexEnv := "definition")]
abbrev randomized_mechanism (I O : Type*) := I → PMF O

@[blueprint "def:event-probability"
  (statement := /-- If $p$ is a probability mass function on $\Omega$ and $E\subseteq\Omega$, then $\mathbb P_p(E)$ is the total $p$-mass of $E$. -/)
  (title := /-- Probability of a discrete event -/)
  (latexEnv := "definition")]
noncomputable def event_probability {Ω : Type*} (p : PMF Ω) (E : Set Ω) : ENNReal :=
  p.toOuterMeasure E

@[blueprint "def:neighboring-datasets"
  (statement := /-- Two datasets $S,S'\in\mathcal X^n$ are neighboring if there is one index at which their entries differ and they agree at every other index. -/)
  (title := /-- Neighboring datasets -/)
  (latexEnv := "definition")]
def neighboring_datasets {Data : Type*} {n : ℕ}
    (S S' : Fin n → Data) : Prop :=
  ∃ i : Fin n, S i ≠ S' i ∧ ∀ j : Fin n, j ≠ i → S j = S' j

@[blueprint "def:differentially-private"
  (statement := /-- A mechanism $M$ is $(\varepsilon,\delta)$-differentially private if, for every ordered pair of neighboring datasets $S,S'$ and every event $E$, one has $\mathbb P[M(S)\in E]\le e^\varepsilon\mathbb P[M(S')\in E]+\delta$. -/)
  (title := /-- Approximate differential privacy -/)
  (latexEnv := "definition")]
def differentially_private {Data Output : Type*} {n : ℕ}
    (M : randomized_mechanism (Fin n → Data) Output) (ε δ : ℝ) : Prop :=
  ∀ S S', neighboring_datasets S S' → ∀ E : Set Output,
    event_probability (M S) E ≤
      ENNReal.ofReal (Real.exp ε) * event_probability (M S') E + ENNReal.ofReal δ

@[blueprint "def:coordinate-calls"
  (statement := /-- A family of adaptive coordinate calls in dimension $d$ assigns to each coordinate $i$, current prefix vector, and dataset a probability mass function on the next real coordinate. -/)
  (title := /-- Adaptive coordinate calls -/)
  (latexEnv := "definition")]
abbrev coordinate_calls (Data : Type*) (n d : ℕ) :=
  Fin d → euclidean_point d → randomized_mechanism (Fin n → Data) ℝ

@[blueprint "def:adaptive-high-dimensional-optimizer"
  (statement := /-- The high-dimensional optimizer starts at the zero vector and, in increasing coordinate order, samples the next coordinate from the corresponding adaptive call and updates that coordinate. -/)
  (title := /-- The adaptive high-dimensional optimizer -/)
  (latexEnv := "definition")]
noncomputable def adaptive_high_dimensional_optimizer {Data : Type*} {n d : ℕ}
    (calls : coordinate_calls Data n d) :
    randomized_mechanism (Fin n → Data) (euclidean_point d) :=
  fun S =>
    (List.finRange d).foldl
      (fun law i =>
        PMF.bind law fun x =>
          PMF.map (fun z => Function.update x i z) (calls i x S))
      (PMF.pure 0)

@[blueprint "def:adaptive-calls-private"
  (statement := /-- A family of adaptive coordinate calls is pointwise $(\varepsilon,\delta)$-private if the call at every coordinate and every fixed preceding output vector is an $(\varepsilon,\delta)$-differentially private mechanism of the dataset. -/)
  (title := /-- Privacy of every adaptive call -/)
  (latexEnv := "definition")]
def adaptive_calls_private {Data : Type*} {n d : ℕ}
    (calls : coordinate_calls Data n d) (ε δ : ℝ) : Prop :=
  ∀ i pref, differentially_private (calls i pref) ε δ

@[blueprint "def:alpha-approximation"
  (statement := /-- A dataset $S'$ is an $\alpha$-approximation of $S$ with respect to $Q$ if $|Q(S,x)-Q(S',x)|\le\alpha$ for every $x\in\mathbb R^d$. -/)
  (title := /-- Approximation with respect to an objective -/)
  (latexEnv := "definition")]
def alpha_approximation {Data : Type*} {d : ℕ}
    (Q : List Data → euclidean_point d → ℝ) (S S' : List Data) (α : ℝ) : Prop :=
  ∀ x, |Q S x - Q S' x| ≤ α

@[blueprint "def:random-subset-sampler"
  (statement := /-- A random-subset sampler takes a dataset of size $n$ and a requested lower size bound and returns a probability mass function on finite datasets. -/)
  (title := /-- Random-subset samplers -/)
  (latexEnv := "definition")]
abbrev random_subset_sampler (Data : Type*) (n : ℕ) :=
  (Fin n → Data) → ℕ → PMF (List Data)

@[blueprint "def:canonical-random-subset-sampler"
  (statement := /-- For a dataset $S\in\mathcal X^n$ and a requested size $m\in\mathbb N$, the canonical random-subset sampler draws a uniformly random permutation $\sigma$ of $\operatorname{Fin}(n)$, independently of $S$, and returns the first $\min\{m,n\}$ entries of the permuted list $(S(\sigma(0)),\ldots,S(\sigma(n-1)))$. -/)
  (title := /-- Canonical data-independent random-subset sampler -/)
  (latexEnv := "definition")]
noncomputable def canonical_random_subset_sampler (Data : Type*) (n : ℕ) :
    random_subset_sampler Data n :=
  fun S m =>
    PMF.map
      (fun σ : Equiv.Perm (Fin n) =>
        (List.ofFn (fun i => S (σ i))).take m)
      (PMF.uniformOfFintype (Equiv.Perm (Fin n)))

@[blueprint "def:can-be-approximated"
  (statement := /-- The pair $(S,Q)$ can be $(\alpha,\beta,m)$-approximated if the prescribed random-subset sampler returns, with probability at least $1-\beta$, a subpermutation of $S$ of length at least $m$ that is an $\alpha$-approximation of $S$ with respect to $Q$. -/)
  (title := /-- Random-subset approximability -/)
  (latexEnv := "definition")]
def can_be_approximated {Data : Type*} {n d : ℕ}
    (sampler : random_subset_sampler Data n)
    (Q : List Data → euclidean_point d → ℝ) (S : Fin n → Data)
    (α β : ℝ) (m : ℕ) : Prop :=
  ENNReal.ofReal (1 - β) ≤
    event_probability (sampler S m)
      {S' | S'.Subperm (List.ofFn S) ∧ m ≤ S'.length ∧
        alpha_approximation Q (List.ofFn S) S' α}

@[blueprint "def:agrees-before"
  (statement := /-- A vector $x$ agrees with a prefix vector $p$ before stage $k$ if $x_j=p_j$ for every coordinate $j<k$. -/)
  (title := /-- Agreement with a coordinate prefix -/)
  (latexEnv := "definition")]
def agrees_before {d : ℕ} (k : ℕ)
    (pref x : euclidean_point d) : Prop :=
  ∀ j : Fin d, j.val < k → x j = pref j

@[blueprint "def:prefix-objective-values"
  (statement := /-- For an objective $q:\mathbb R^d\to\mathbb R$, the prefix-value set at stage $k$ consists of all values $q(x)$ obtained by completions $x$ agreeing with the prescribed prefix before $k$. -/)
  (title := /-- Objective values extending a prefix -/)
  (latexEnv := "definition")]
def prefix_objective_values {d : ℕ} (q : euclidean_point d → ℝ)
    (k : ℕ) (pref : euclidean_point d) : Set ℝ :=
  {r | ∃ x, agrees_before k pref x ∧ r = q x}

@[blueprint "def:coordinate-profile-values"
  (statement := /-- At coordinate $i$ and prefix $p$, the profile-value set at $z\in\mathbb R$ consists of objective values of completions agreeing with $p$ before $i$ and having $i$th coordinate equal to $z$. -/)
  (title := /-- Values in a coordinate profile -/)
  (latexEnv := "definition")]
def coordinate_profile_values {d : ℕ} (q : euclidean_point d → ℝ)
    (i : Fin d) (pref : euclidean_point d) (z : ℝ) : Set ℝ :=
  {r | ∃ x, agrees_before i.val pref x ∧ x i = z ∧ r = q x}

@[blueprint "def:is-coordinate-profile"
  (statement := /-- A function $h:\mathbb R\to\mathbb R$ is the $i$th coordinate profile of $q$ at prefix $p$ if, for every $z$, $h(z)$ is the greatest value attainable by a completion with $i$th coordinate $z$. -/)
  (title := /-- Coordinate profiles by attained maxima -/)
  (latexEnv := "definition")]
def is_coordinate_profile {d : ℕ} (q : euclidean_point d → ℝ)
    (i : Fin d) (pref : euclidean_point d) (h : ℝ → ℝ) : Prop :=
  ∀ z, IsGreatest (coordinate_profile_values q i pref z) (h z)

@[blueprint "def:adaptive-coordinate-domains"
  (statement := /-- An adaptive family of finite coordinate domains assigns a finite subset of $\mathbb R$ to every coordinate and preceding output vector. -/)
  (title := /-- Adaptive finite coordinate domains -/)
  (latexEnv := "definition")]
abbrev adaptive_coordinate_domains (d : ℕ) :=
  Fin d → euclidean_point d → Finset ℝ

@[blueprint "def:has-maximum-domain-cardinality"
  (statement := /-- The adaptive domains have maximum cardinality $X$ if every coordinate domain has cardinality at most $X$ and either $d=0=X$, or some coordinate and prefix have a domain of cardinality exactly $X$. -/)
  (title := /-- Maximum adaptive-domain cardinality -/)
  (latexEnv := "definition")]
def has_maximum_domain_cardinality {d : ℕ}
    (domains : adaptive_coordinate_domains d) (X : ℕ) : Prop :=
  (∀ i pref, (domains i pref).card ≤ X) ∧
    ((d = 0 ∧ X = 0) ∨ ∃ i pref, (domains i pref).card = X)

@[blueprint "def:proper-finite-domains"
  (statement := /-- Adaptive finite domains are proper for $Q$ if, whenever an attained optimum extends a prefix before coordinate $i$, some value in the $i$th finite domain preserves that same attained optimum after fixing coordinate $i$. -/)
  (title := /-- Proper adaptive finite domains -/)
  (latexEnv := "definition")]
def proper_finite_domains {Data : Type*} {d : ℕ}
    (Q : List Data → euclidean_point d → ℝ)
    (domains : adaptive_coordinate_domains d) : Prop :=
  ∀ S i pref optimum,
    IsGreatest (prefix_objective_values (Q S) i.val pref) optimum →
      ∃ z ∈ domains i pref,
        IsGreatest (coordinate_profile_values (Q S) i pref z) optimum

@[blueprint "def:coordinate-calls-have-one-dimensional-accuracy"
  (statement := /-- Fix a dataset $S$. The coordinate calls satisfy the one-dimensional accuracy interface if the following holds for every coordinate $i$, prefix $p$, and greatest value $M$ of the objective among completions of $p$ before coordinate $i$. First, there exists an attained coordinate profile $h:\mathbb R\to\mathbb R$ at $(i,p)$. Second, for every such profile $h$, if $h$ is quasiconcave, then the $i$th call conditioned on $p$ returns, with probability at least $1-\beta$, a point $z$ in the prescribed domain for which $h(z)\ge M-2\alpha$. -/)
  (title := /-- One-dimensional optimizer interface -/)
  (latexEnv := "definition")]
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

@[blueprint "def:coordinate-step-accurate"
  (statement := /-- Coordinate step $i$ of an output vector $x$ is accurate if the attained optimum after fixing coordinates through $i$ is at least the attained optimum before fixing coordinate $i$ minus $2\alpha$. -/)
  (title := /-- Accuracy of one coordinate step -/)
  (latexEnv := "definition")]
def coordinate_step_accurate {d : ℕ} (q : euclidean_point d → ℝ)
    (α : ℝ) (i : Fin d) (x : euclidean_point d) : Prop :=
  ∃ before after,
    IsGreatest (prefix_objective_values q i.val x) before ∧
    IsGreatest (prefix_objective_values q (i.val + 1) x) after ∧
    before - 2 * α ≤ after

@[blueprint "def:all-coordinate-steps-accurate"
  (statement := /-- An output vector has accurate coordinate steps if the preceding one-step condition holds at every coordinate. -/)
  (title := /-- Simultaneous coordinate-step accuracy -/)
  (latexEnv := "definition")]
def all_coordinate_steps_accurate {d : ℕ} (q : euclidean_point d → ℝ)
    (α : ℝ) (x : euclidean_point d) : Prop :=
  ∀ i, coordinate_step_accurate q α i x

@[blueprint "def:soft-big-o-log-star"
  (statement := /-- Relative to a specified iterated-logarithm function $L$, the relation $f\in\widetilde O(L)$ means that $f(X)=O(L(X)\log^k(X+2))$ for some $k\in\mathbb N$. -/)
  (title := /-- Soft big-O relative to an iterated logarithm -/)
  (latexEnv := "definition")]
def soft_big_o_log_star (f logStar : ℕ → ℝ) : Prop :=
  ∃ k : ℕ, Asymptotics.IsBigO Filter.atTop f
    (fun X => logStar X * (Real.log ((X : ℝ) + 2)) ^ k)

@[blueprint "def:one-dimensional-ip-optimizer-witness"
  (statement := /-- Let \(\mathcal X\) be a data domain, let \(n,t,d\in\mathbb N\), let \(Q:\mathcal X^*\times\mathbb R^d\to\mathbb R\), and let \(\widetilde{\mathcal X}_i(p)\) be adaptive finite coordinate domains. Fix functions \(n_{IP}:\mathbb N\times\mathbb R^3\to\mathbb N\) and \(L:\mathbb N\to\mathbb R\), and parameters \(\alpha,\beta,\varepsilon,\delta\in\mathbb R\). A one-dimensional optimizer witness consists of one family of coordinate mechanisms which is \((\varepsilon,\delta)\)-differentially private whenever \(\varepsilon>0\), \(\delta,\alpha,\beta\in(0,1)\), and \(t\le n\), and which satisfies the non-vacuous one-dimensional \(2\alpha\)-loss accuracy interface whenever \(0<t=n_{IP}(X,\beta,\varepsilon,\delta)\), \(n_{IP}(\cdot,\beta,\varepsilon,\delta)\in\widetilde O(L)\), the domains have maximum cardinality \(X\) and are proper for \(Q\), \(Q(S,\cdot)\) is quasiconcave, and \((S,Q)\) has the required random-subset approximation. In particular, at every prefix whose compatible objective values have a greatest element, the accuracy interface supplies an attained coordinate profile as well as the call-probability bound. Thus \(n_{IP}\) is semantically tied to the privacy and accuracy guarantees of the same concrete optimizer family. -/)
  (title := /-- Witness for the one-dimensional private optimizer -/)
  (latexEnv := "definition")]
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

@[blueprint "lem:ip-concave-coordinate-calls-exist"
  (statement := /-- Let \(\mathcal X\) be a type, let \(n,t,d\in\mathbb N\), let \(Q:\mathcal X^*\times\mathbb R^d\to\mathbb R\), and let \(\widetilde{\mathcal X}_i(p)\) be adaptive finite coordinate domains. Fix functions \(n_{IP}:\mathbb N\times\mathbb R^3\to\mathbb N\) and \(L:\mathbb N\to\mathbb R\), parameters \(\alpha,\beta,\varepsilon,\delta\in\mathbb R\), and a one-dimensional private-optimizer witness for these data. Then there exists a single family of coordinate calls with the following two properties. First, if \(\varepsilon>0\), \(\delta,\alpha,\beta\in(0,1)\), and \(t\le n\), then the family is adaptively \((\varepsilon,\delta)\)-differentially private. Second, for every \(S\in\mathcal X^n\), \(\beta'\in\mathbb R\), and \(X\in\mathbb N\), the family satisfies the non-vacuous one-dimensional accuracy interface at \(S\), including existence of an attained profile at every attained prefix, provided that \(\varepsilon>0\), \(\delta,\alpha,\beta\in(0,1)\), \(0<t\le n\), \(t=n_{IP}(X,\beta,\varepsilon,\delta)\), \(n_{IP}(\cdot,\beta,\varepsilon,\delta)\in\widetilde O(L)\), the adaptive domains have maximum cardinality \(X\), \(Q(S,\cdot)\) is quasiconcave, \((S,Q)\) has the required canonical random-subset approximation with parameters \(\alpha,\beta',n/t\), and the domains are proper for \(Q\). -/)
  (proof := /-- The witness in \cref{def:one-dimensional-ip-optimizer-witness} contains a single coordinate-call family together with its uniform privacy and accuracy guarantees. Choose that family. Its privacy field gives the first conclusion under the stated parameter ranges. Its accuracy field applies to each admissible dataset \(S\) with the same fixed function \(n_{IP}\), so the sample-complexity equality and soft asymptotic bound cannot be supplied by an unrelated function. The remaining hypotheses match the witness field term by term and therefore give the required one-dimensional accuracy interface. -/)
  (title := /-- Existence and guarantees of the IPConcave coordinate calls -/)
  (latexEnv := "lemma")]
lemma ip_concave_coordinate_calls_exist
    {Data : Type*} {n t d : ℕ}
    (Q : List Data → euclidean_point d → ℝ)
    (domains : adaptive_coordinate_domains d)
    (nIP : ℕ → ℝ → ℝ → ℝ → ℕ) (logStar : ℕ → ℝ)
    (α β ε δ : ℝ)
    (optimizer : one_dimensional_ip_optimizer_witness
      (n := n) (t := t) Q domains nIP logStar α β ε δ) :
    ∃ calls : coordinate_calls Data n d,
      (0 < ε → (0 < δ ∧ δ < 1) →
        (0 < α ∧ α < 1) → (0 < β ∧ β < 1) → t ≤ n →
        adaptive_calls_private calls ε δ) ∧
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
        coordinate_calls_have_one_dimensional_accuracy calls Q domains S α β := by
  exact ⟨optimizer.calls, optimizer.calls_private, optimizer.calls_accurate⟩

@[blueprint "def:ip-concave-coordinate-calls"
  (statement := /-- Fix an objective \(Q\), adaptive coordinate domains, functions \(n_{IP}\) and \(L\), parameters \(\alpha,\beta,\varepsilon,\delta\), and a one-dimensional private-optimizer witness for these data. The coordinate calls of \(\operatorname{IPConcaveHighDim}_{\alpha,\beta,\varepsilon,\delta,t}\) are the single family supplied by that witness through the existence-and-guarantee lemma. In particular, the calls and the function \(n_{IP}\) are selected from the same witness rather than independently. -/)
  (title := /-- Coordinate calls of IPConcaveHighDim -/)
  (latexEnv := "definition")]
noncomputable def ip_concave_coordinate_calls
    {Data : Type*} {n t d : ℕ}
    (Q : List Data → euclidean_point d → ℝ)
    (domains : adaptive_coordinate_domains d)
    (nIP : ℕ → ℝ → ℝ → ℝ → ℕ) (logStar : ℕ → ℝ)
    (α β ε δ : ℝ)
    (optimizer : one_dimensional_ip_optimizer_witness
      (n := n) (t := t) Q domains nIP logStar α β ε δ) :
    coordinate_calls Data n d :=
  Classical.choose
    (ip_concave_coordinate_calls_exist (n := n) (t := t)
      Q domains nIP logStar α β ε δ optimizer)

@[blueprint "def:ip-concave-high-dimensional-optimizer"
  (statement := /-- Fix an objective \(Q\), one finite domain \(\widetilde{\mathcal X}_i\subset\mathbb R\) for every coordinate \(i\in[d]\), functions \(n_{IP}\) and \(L\), parameters \(\alpha,\beta,\varepsilon,\delta\), and a witness for the corresponding one-dimensional private optimizer. The algorithm \(\operatorname{IPConcaveHighDim}_{\alpha,\beta,\varepsilon,\delta,t}(\cdot,Q)\) applies the witnessed coordinate calls in coordinate order. The fixed domain \(\widetilde{\mathcal X}_i\) is regarded as the adaptive domain assigned to coordinate \(i\) after every preceding output prefix. -/)
  (title := /-- The IPConcaveHighDim algorithm -/)
  (latexEnv := "definition")]
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

@[blueprint "lem:ip-concave-coordinate-calls-private"
  (statement := /-- Let \(\mathcal X\) be a type, let \(n,t,d\in\mathbb N\), let \(Q:\mathcal X^*\times\mathbb R^d\to\mathbb R\), and let an adaptive coordinate domain assign a finite subset of \(\mathbb R\) to every coordinate and preceding output vector. Fix functions \(n_{IP}:\mathbb N\times\mathbb R^3\to\mathbb N\) and \(L:\mathbb N\to\mathbb R\), parameters \(\alpha,\beta,\varepsilon,\delta\in\mathbb R\), and a one-dimensional optimizer witness for these data. If \(\varepsilon>0\), \(\delta,\alpha,\beta\in(0,1)\), and \(t\le n\), then the coordinate-call family selected from this witness is adaptively \((\varepsilon,\delta)\)-differentially private: for every coordinate and every preceding output vector, the corresponding mechanism on datasets in \(\mathcal X^n\) is \((\varepsilon,\delta)\)-differentially private. -/)
  (proof := /-- By \cref{lem:ip-concave-coordinate-calls-exist}, the witness supplies one family satisfying the pointwise privacy clause in \cref{def:adaptive-calls-private} under the stated parameter-range and size hypotheses. The definition \cref{def:ip-concave-coordinate-calls} selects precisely a family supplied by this same witnessed existence statement. Hence the selected family satisfies the asserted conditional privacy property. -/)
  (title := /-- Privacy of the IPConcave coordinate calls -/)
  (latexEnv := "lemma")]
lemma ip_concave_coordinate_calls_private
    {Data : Type*} {n t d : ℕ}
    (Q : List Data → euclidean_point d → ℝ)
    (domains : adaptive_coordinate_domains d)
    (nIP : ℕ → ℝ → ℝ → ℝ → ℕ) (logStar : ℕ → ℝ)
    (α β ε δ : ℝ)
    (optimizer : one_dimensional_ip_optimizer_witness
      (n := n) (t := t) Q domains nIP logStar α β ε δ)
    (hε : 0 < ε) (hδ : 0 < δ ∧ δ < 1)
    (hα : 0 < α ∧ α < 1) (hβ : 0 < β ∧ β < 1)
    (hnt : t ≤ n) :
    adaptive_calls_private
      (ip_concave_coordinate_calls (n := n) (t := t)
        Q domains nIP logStar α β ε δ optimizer) ε δ := by
  exact
    (Classical.choose_spec
      (ip_concave_coordinate_calls_exist
        Q domains nIP logStar α β ε δ optimizer)).1
      hε hδ hα hβ hnt

@[blueprint "lem:ip-concave-coordinate-calls-accurate"
  (statement := /-- Let \(\mathcal X\) be a type, let \(n,t,d,X\in\mathbb N\), let \(Q:\mathcal X^*\times\mathbb R^d\to\mathbb R\), let \(\widetilde{\mathcal X}_i(p)\) be adaptive finite coordinate domains, and let \(S\in\mathcal X^n\). Fix functions \(n_{IP}:\mathbb N\times\mathbb R^3\to\mathbb N\) and \(L:\mathbb N\to\mathbb R\), parameters \(\alpha,\beta,\beta',\varepsilon,\delta\in\mathbb R\), and a one-dimensional optimizer witness for these data. Suppose that \(\varepsilon>0\), that \(\delta,\alpha,\beta\in(0,1)\), that \(0<t\le n\), that \(t=n_{IP}(X,\beta,\varepsilon,\delta)\), and that \(n_{IP}(\cdot,\beta,\varepsilon,\delta)\in\widetilde O(L)\). If the adaptive domains have maximum cardinality \(X\), \(Q(S,\cdot)\) is quasiconcave on \(\mathbb R^d\), \((S,Q)\) can be \((\alpha,\beta',\lfloor n/t\rfloor)\)-approximated under the canonical random-subset law, and the domains are proper for \(Q\), then the coordinate calls selected from the witness satisfy the non-vacuous one-dimensional accuracy interface at \(S\) with parameters \(\alpha\) and \(\beta\). Thus every attained prefix admits an attained coordinate profile, and every quasiconcave such profile obeys the asserted call-probability bound. -/)
  (proof := /-- By \cref{def:ip-concave-coordinate-calls}, the selected family is the witness chosen from \cref{lem:ip-concave-coordinate-calls-exist}. The second conjunct of the chosen witness's specification is universally quantified over \(S\), \(\beta'\), and \(X\). Instantiating it with the present values and then supplying, in order, the parameter-range, sample-size, sample-complexity, asymptotic, maximum-cardinality, quasiconcavity, canonical-approximation, and properness hypotheses yields the asserted one-dimensional accuracy interface. -/)
  (title := /-- Accuracy of the IPConcave coordinate calls -/)
  (latexEnv := "lemma")]
lemma ip_concave_coordinate_calls_accurate
    {Data : Type*} {n t d : ℕ}
    (Q : List Data → euclidean_point d → ℝ)
    (domains : adaptive_coordinate_domains d)
    (S : Fin n → Data)
    (nIP : ℕ → ℝ → ℝ → ℝ → ℕ) (logStar : ℕ → ℝ)
    (α β β' ε δ : ℝ) (X : ℕ)
    (optimizer : one_dimensional_ip_optimizer_witness
      (n := n) (t := t) Q domains nIP logStar α β ε δ)
    (hε : 0 < ε) (hδ : 0 < δ ∧ δ < 1)
    (hα : 0 < α ∧ α < 1) (hβ : 0 < β ∧ β < 1)
    (hnt : t ≤ n) (htpos : 0 < t) (ht : t = nIP X β ε δ)
    (hscale : soft_big_o_log_star (fun Y => (nIP Y β ε δ : ℝ)) logStar)
    (hX : has_maximum_domain_cardinality domains X)
    (hq : QuasiconcaveOn ℝ Set.univ (Q (List.ofFn S)))
    (happrox : can_be_approximated (canonical_random_subset_sampler Data n)
      Q S α β' (n / t))
    (hproper : proper_finite_domains Q domains) :
    coordinate_calls_have_one_dimensional_accuracy
      (ip_concave_coordinate_calls (n := n) (t := t)
        Q domains nIP logStar α β ε δ optimizer)
      Q domains S α β := by
  exact (Classical.choose_spec (ip_concave_coordinate_calls_exist
    (n := n) (t := t) Q domains nIP logStar α β ε δ optimizer)).2
    S β' X hε hδ hα hβ hnt htpos ht hscale hX hq happrox hproper

@[blueprint "def:adaptive-calls-centered-subgaussian-privacy-loss"
  (statement := /-- Let \(d,n\in\mathbb N\), let \(\varepsilon,\delta\in\mathbb R\), and let \(C\) be a family of adaptive coordinate calls. The calls have centered subgaussian privacy loss with parameters \((\varepsilon,\delta)\) if the following holds. For every coordinate, every preceding output vector, and every ordered pair of neighboring datasets \(S,S'\), there is a good set \(G\subseteq\mathbb R\) whose complement has probability at most \(\delta\) under each of the two conditional output laws. On \(G\), the law under \(S\) is absolutely continuous with respect to the law under \(S'\), and, for every \(\lambda\ge0\),
\[
 \sum_{z\in G} p_S(z)
 \exp\!\left(\lambda\log\frac{p_S(z)}{p_{S'}(z)}\right)
 \le \exp\!\left(\frac{\lambda^2\varepsilon^2}{2}\right).
\]
For every \(\lambda\ge 0\), the nonnegative family displayed on the left is required to be summable, and its sum satisfies the stated bound. Here \(p_S\) and \(p_{S'}\) denote the two conditional probability mass functions. -/)
  (title := /-- Centered subgaussian privacy loss of adaptive calls -/)
  (latexEnv := "definition")]
def adaptive_calls_centered_subgaussian_privacy_loss
    {Data : Type*} {n d : ℕ}
    (calls : coordinate_calls Data n d) (ε δ : ℝ) : Prop :=
  ∀ i pref S S', neighboring_datasets S S' →
    ∃ good : Set ℝ,
      event_probability (calls i pref S) goodᶜ ≤ ENNReal.ofReal δ ∧
      event_probability (calls i pref S') goodᶜ ≤ ENNReal.ofReal δ ∧
      (∀ z ∈ good, calls i pref S z ≠ 0 → calls i pref S' z ≠ 0) ∧
      ∀ s : ℝ, 0 ≤ s →
        Summable
            (fun z : ℝ => good.indicator
              (fun y =>
                (calls i pref S y).toReal *
                  Real.exp
                    (s * Real.log
                      ((calls i pref S y).toReal /
                        (calls i pref S' y).toReal))) z) ∧
          ∑' z : ℝ, good.indicator
            (fun y =>
              (calls i pref S y).toReal *
                Real.exp
                  (s * Real.log
                    ((calls i pref S y).toReal /
                      (calls i pref S' y).toReal))) z ≤
            Real.exp (s ^ 2 * ε ^ 2 / 2)

@[blueprint "def:adaptive-composition-prefix"
  (statement := /-- If \(k\le d\), a partial transcript in \(\mathbb R^k\) determines a point of \(\mathbb R^d\) by retaining its first \(k\) coordinates and setting every later coordinate to zero. -/)
  (title := /-- Prefix vector of a partial adaptive transcript -/)
  (latexEnv := "definition")]
def adaptive_composition_prefix {d k : ℕ} (hk : k ≤ d)
    (x : euclidean_point k) : euclidean_point d :=
  fun j => if h : j.val < k then x ⟨j.val, h⟩ else 0

@[blueprint "def:adaptive-composition-extend"
  (statement := /-- Appending \(z\in\mathbb R\) to a transcript \(x\in\mathbb R^k\) gives the point of \(\mathbb R^{k+1}\) whose first \(k\) coordinates are those of \(x\) and whose last coordinate is \(z\). -/)
  (title := /-- Extension of a partial adaptive transcript -/)
  (latexEnv := "definition")]
def adaptive_composition_extend {k : ℕ} (x : euclidean_point k) (z : ℝ) :
    euclidean_point (k + 1) :=
  fun j => if h : j.val < k then x ⟨j.val, h⟩ else z

@[blueprint "def:adaptive-composition-drop-last"
  (statement := /-- Dropping the last coordinate of a point in \(\mathbb R^{k+1}\) gives its first \(k\) coordinates. -/)
  (title := /-- Deletion of the last transcript coordinate -/)
  (latexEnv := "definition")]
def adaptive_composition_drop_last {k : ℕ} (x : euclidean_point (k + 1)) :
    euclidean_point k :=
  fun i => x i.castSucc

@[blueprint "def:adaptive-composition-call-prefix"
  (statement := /-- For a transcript \(x\in\mathbb R^k\), a coordinate \(i<k\), and \(k\le d\), the prefix supplied to call \(i\) retains the transcript coordinates below \(i\) and is zero from coordinate \(i\) onward. -/)
  (title := /-- Prefix supplied to an adaptive coordinate call -/)
  (latexEnv := "definition")]
def adaptive_composition_call_prefix {d k : ℕ} (hk : k ≤ d)
    (x : euclidean_point k) (i : Fin k) : euclidean_point d :=
  fun j => if h : j.val < i.val then
    x ⟨j.val, Nat.lt_trans h i.isLt⟩ else 0

@[blueprint "def:adaptive-composition-path-good"
  (statement := /-- Given a good output set for every coordinate and prefix, a partial adaptive transcript is good when each of its coordinates lies in the good set selected for that coordinate and its preceding prefix. -/)
  (title := /-- Good adaptive transcripts -/)
  (latexEnv := "definition")]
def adaptive_composition_path_good {d k : ℕ}
    (good : Fin d → euclidean_point d → Set ℝ) (hk : k ≤ d)
    (x : euclidean_point k) : Prop :=
  ∀ i : Fin k,
    x i ∈ good (Fin.castLE hk i)
      (adaptive_composition_call_prefix hk x i)

@[blueprint "def:adaptive-composition-path-privacy-loss"
  (statement := /-- The privacy loss of a partial adaptive transcript is the sum over its coordinates of the logarithm of the ratio between the two corresponding conditional call masses. -/)
  (title := /-- Privacy loss of an adaptive transcript -/)
  (latexEnv := "definition")]
noncomputable def adaptive_composition_path_privacy_loss {Data : Type*}
    {n d k : ℕ} (calls : coordinate_calls Data n d)
    (S S' : Fin n → Data) (hk : k ≤ d) (x : euclidean_point k) : ℝ :=
  ∑ i : Fin k,
    Real.log
      ((calls (Fin.castLE hk i)
          (adaptive_composition_call_prefix hk x i) S (x i)).toReal /
        (calls (Fin.castLE hk i)
          (adaptive_composition_call_prefix hk x i) S' (x i)).toReal)

@[blueprint "def:adaptive-composition-path-law"
  (statement := /-- For \(k\le d\), the path law of the first \(k\) adaptive calls is the probability mass function on \(\mathbb R^k\) obtained by starting from the empty transcript and successively appending the output of coordinate call \(0,\ldots,k-1\), each evaluated at the zero-extended preceding transcript. -/)
  (title := /-- Probability law of partial adaptive transcripts -/)
  (latexEnv := "definition")]
noncomputable def adaptive_composition_path_law {Data : Type*} {n d : ℕ}
    (calls : coordinate_calls Data n d) (S : Fin n → Data) :
    (k : ℕ) → k ≤ d → PMF (euclidean_point k)
  | 0, _ => PMF.pure 0
  | k + 1, hk =>
      (adaptive_composition_path_law calls S k
        (Nat.le_trans (Nat.le_succ k) hk)).bind fun x =>
        PMF.map (adaptive_composition_extend x)
          (calls ⟨k, Nat.lt_of_succ_le hk⟩
            (adaptive_composition_prefix
              (Nat.le_trans (Nat.le_succ k) hk) x) S)

@[blueprint "def:adaptive-composition-path-mgf-term"
  (statement := /-- At exponent \(s\), the good-path moment term of a transcript is its mass under \(S\) times \(e^{sL}\), where \(L\) is its cumulative privacy loss, and is zero for a transcript outside the selected good sets. -/)
  (title := /-- Good-path moment term -/)
  (latexEnv := "definition")]
noncomputable def adaptive_composition_path_mgf_term {Data : Type*}
    {n d k : ℕ} (calls : coordinate_calls Data n d)
    (S S' : Fin n → Data) (good : Fin d → euclidean_point d → Set ℝ)
    (hk : k ≤ d) (s : ℝ) (x : euclidean_point k) : ℝ :=
  {x | adaptive_composition_path_good good hk x}.indicator
    (fun y =>
      (adaptive_composition_path_law calls S k hk y).toReal *
        Real.exp (s * adaptive_composition_path_privacy_loss calls S S' hk y)) x

@[blueprint "def:adaptive-composition-state-law"
  (statement := /-- For \(k\le d\), the state law of the first \(k\) adaptive calls is obtained by folding over the coordinates \(0,\ldots,k-1\) in \(\mathbb R^d\), sampling the next call at the current state and updating its corresponding coordinate. -/)
  (title := /-- Probability law of partial adaptive states -/)
  (latexEnv := "definition")]
noncomputable def adaptive_composition_state_law {Data : Type*} {n d : ℕ}
    (calls : coordinate_calls Data n d) (S : Fin n → Data)
    (k : ℕ) (hk : k ≤ d) : PMF (euclidean_point d) :=
  Fin.foldl k
    (fun law i =>
      PMF.bind law fun x =>
        PMF.map (fun z => Function.update x (Fin.castLE hk i) z)
          (calls (Fin.castLE hk i) x S))
    (PMF.pure 0)

@[blueprint "lem:adaptive-composition-prefix-extend"
  (statement := /-- Zero-extending an appended transcript agrees with updating the next coordinate of the zero-extension of the preceding transcript. -/)
  (proof := /-- Expand the prefix and extension definitions and compare their values at an arbitrary coordinate. Coordinates below \(k\) retain the old transcript value, coordinate \(k\) has value \(z\), and coordinates above \(k\) are zero, exactly as in the functional update. -/)
  (title := /-- Compatibility of transcript extension with coordinate update -/)
  (latexEnv := "lemma")]
lemma adaptive_composition_prefix_extend {d k : ℕ} (hk : k + 1 ≤ d)
    (x : euclidean_point k) (z : ℝ) :
    adaptive_composition_prefix hk (adaptive_composition_extend x z) =
      Function.update
        (adaptive_composition_prefix (Nat.le_trans (Nat.le_succ k) hk) x)
        ⟨k, Nat.lt_of_succ_le hk⟩ z := by
  funext j
  simp only [adaptive_composition_prefix, adaptive_composition_extend,
    Function.update_apply]
  split_ifs <;> simp_all only [Fin.ext_iff] <;> omega

@[blueprint "lem:adaptive-composition-extend-drop-last"
  (statement := /-- Appending the last coordinate after dropping it recovers a transcript, while dropping the last coordinate after appending recovers the preceding transcript. -/)
  (proof := /-- Evaluate both identities coordinatewise using \cref{def:adaptive-composition-extend, def:adaptive-composition-drop-last}. Below the last coordinate both operations retain the original value; at the last coordinate extension inserts the specified value. -/)
  (title := /-- Extension and deletion are inverse transcript operations -/)
  (latexEnv := "lemma")]
lemma adaptive_composition_extend_drop_last {k : ℕ}
    (x : euclidean_point (k + 1)) :
    adaptive_composition_extend (adaptive_composition_drop_last x)
        (x (Fin.last k)) = x ∧
      ∀ (y : euclidean_point k) (z : ℝ),
        adaptive_composition_drop_last (adaptive_composition_extend y z) = y ∧
        adaptive_composition_extend y z (Fin.last k) = z := by
  constructor
  · funext j
    by_cases h : j.val < k
    · simp [adaptive_composition_extend, adaptive_composition_drop_last, h]
    · have hj : j = Fin.last k := Fin.eq_last_of_not_lt h
      subst j
      simp [adaptive_composition_extend]
  · intro y z
    constructor
    · funext i
      simp [adaptive_composition_drop_last, adaptive_composition_extend]
    · simp [adaptive_composition_extend]

@[blueprint "def:adaptive-composition-extend-equivalence"
  (statement := /-- Extension is a bijection from a length-\(k\) transcript paired with one real value to a length-\(k+1\) transcript; its inverse drops the last coordinate and records that coordinate. -/)
  (title := /-- Equivalence induced by transcript extension -/)
  (latexEnv := "definition")]
def adaptive_composition_extend_equivalence (k : ℕ) :
    (euclidean_point k × ℝ) ≃ euclidean_point (k + 1) where
  toFun p := adaptive_composition_extend p.1 p.2
  invFun x := (adaptive_composition_drop_last x, x (Fin.last k))
  left_inv p := by
    apply Prod.ext
    · exact ((adaptive_composition_extend_drop_last
        (adaptive_composition_extend p.1 p.2)).2 p.1 p.2).1
    · exact ((adaptive_composition_extend_drop_last
        (adaptive_composition_extend p.1 p.2)).2 p.1 p.2).2
  right_inv x := (adaptive_composition_extend_drop_last x).1

@[blueprint "lem:adaptive-composition-call-prefix-drop-last"
  (statement := /-- For a transcript of length \(k+1\), the call prefix at a coordinate below \(k\) is the corresponding call prefix of the transcript with its last coordinate deleted, while the call prefix at coordinate \(k\) is the zero-extension of that shortened transcript. -/)
  (proof := /-- Both assertions follow coordinatewise from \cref{def:adaptive-composition-call-prefix, def:adaptive-composition-prefix, def:adaptive-composition-drop-last}. For a coordinate below the selected call index the two sides read the same earlier transcript entry; every other coordinate is zero. -/)
  (title := /-- Call prefixes under deletion of the last coordinate -/)
  (latexEnv := "lemma")]
lemma adaptive_composition_call_prefix_drop_last {d k : ℕ} (hk : k + 1 ≤ d)
    (x : euclidean_point (k + 1)) :
    (∀ i : Fin k,
      adaptive_composition_call_prefix hk x i.castSucc =
        adaptive_composition_call_prefix
          (Nat.le_trans (Nat.le_succ k) hk)
          (adaptive_composition_drop_last x) i) ∧
      adaptive_composition_call_prefix hk x (Fin.last k) =
        adaptive_composition_prefix (Nat.le_trans (Nat.le_succ k) hk)
          (adaptive_composition_drop_last x) := by
  constructor
  · intro i
    funext j
    simp [adaptive_composition_call_prefix, adaptive_composition_drop_last]
    split_ifs <;> rfl
  · funext j
    simp [adaptive_composition_call_prefix, adaptive_composition_prefix,
      adaptive_composition_drop_last]
    split_ifs <;> rfl

@[blueprint "lem:adaptive-composition-path-good-loss-last"
  (statement := /-- A transcript of length \(k+1\) is good exactly when its shortened transcript is good and its last coordinate lies in the selected conditional good set. Its privacy loss is the shortened transcript's loss plus the last conditional log-likelihood ratio. -/)
  (proof := /-- Split the universal good-path condition and the finite privacy-loss sum at the last coordinate. Use \cref{lem:adaptive-composition-call-prefix-drop-last} to replace every earlier conditional prefix by the prefix of the shortened transcript and to identify the last conditional prefix with its zero-extension. -/)
  (title := /-- Last-coordinate decomposition of good paths and privacy loss -/)
  (latexEnv := "lemma")]
lemma adaptive_composition_path_good_loss_last {Data : Type*} {n d k : ℕ}
    (calls : coordinate_calls Data n d) (S S' : Fin n → Data)
    (good : Fin d → euclidean_point d → Set ℝ) (hk : k + 1 ≤ d)
    (x : euclidean_point (k + 1)) :
    (adaptive_composition_path_good good hk x ↔
      adaptive_composition_path_good good
          (Nat.le_trans (Nat.le_succ k) hk)
          (adaptive_composition_drop_last x) ∧
        x (Fin.last k) ∈ good ⟨k, Nat.lt_of_succ_le hk⟩
          (adaptive_composition_prefix (Nat.le_trans (Nat.le_succ k) hk)
            (adaptive_composition_drop_last x))) ∧
      adaptive_composition_path_privacy_loss calls S S' hk x =
        adaptive_composition_path_privacy_loss calls S S'
            (Nat.le_trans (Nat.le_succ k) hk)
            (adaptive_composition_drop_last x) +
          Real.log
            ((calls ⟨k, Nat.lt_of_succ_le hk⟩
                (adaptive_composition_prefix
                  (Nat.le_trans (Nat.le_succ k) hk)
                  (adaptive_composition_drop_last x)) S
                (x (Fin.last k))).toReal /
              (calls ⟨k, Nat.lt_of_succ_le hk⟩
                (adaptive_composition_prefix
                  (Nat.le_trans (Nat.le_succ k) hk)
                  (adaptive_composition_drop_last x)) S'
                (x (Fin.last k))).toReal) := by
  constructor
  · constructor
    · intro h
      constructor
      · intro i
        have hi := h i.castSucc
        rwa [(adaptive_composition_call_prefix_drop_last hk x).1 i] at hi
      · have hi := h (Fin.last k)
        rwa [(adaptive_composition_call_prefix_drop_last hk x).2] at hi
    · rintro ⟨hprev, hlast⟩ i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hi : Fin.castLE hk (Fin.last k) =
            (⟨k, Nat.lt_of_succ_le hk⟩ : Fin d) := Fin.ext rfl
        simpa [hi, (adaptive_composition_call_prefix_drop_last hk x).2] using hlast
      · have hj := hprev j
        simpa [adaptive_composition_drop_last,
          (adaptive_composition_call_prefix_drop_last hk x).1 j] using hj
  · unfold adaptive_composition_path_privacy_loss
    rw [Fin.sum_univ_castSucc]
    congr 1

@[blueprint "lem:adaptive-composition-map-extend-apply"
  (statement := /-- The mass at a transcript \(x\in\mathbb R^{k+1}\) under the pushforward of a one-coordinate law by extension of a fixed prefix \(y\in\mathbb R^k\) is the mass of the last coordinate of \(x\) when \(y\) is its prefix, and is zero otherwise. -/)
  (proof := /-- Extension of a fixed prefix is injective because its last coordinate is the sampled value. If the fixed prefix is obtained by dropping the last coordinate of \(x\), \cref{lem:adaptive-composition-extend-drop-last} identifies the unique preimage. Otherwise that same inverse identity shows that \(x\) has no preimage, so every summand in the pushforward formula vanishes. -/)
  (title := /-- Point mass of a transcript extension pushforward -/)
  (latexEnv := "lemma")]
lemma adaptive_composition_map_extend_apply {k : ℕ} (p : PMF ℝ)
    (y : euclidean_point k) (x : euclidean_point (k + 1)) :
    PMF.map (adaptive_composition_extend y) p x =
      if y = adaptive_composition_drop_last x then p (x (Fin.last k)) else 0 := by
  have hinj : Function.Injective (adaptive_composition_extend y) := by
    intro a b hab
    have hlast := congr_fun hab (Fin.last k)
    simpa [adaptive_composition_extend] using hlast
  by_cases h : y = adaptive_composition_drop_last x
  · have hx : x = adaptive_composition_extend y (x (Fin.last k)) := by
      calc
        x = adaptive_composition_extend (adaptive_composition_drop_last x)
            (x (Fin.last k)) := (adaptive_composition_extend_drop_last x).1.symm
        _ = adaptive_composition_extend y (x (Fin.last k)) := by rw [h]
    rw [if_pos h, hx]
    simp [PMF.map_apply, hinj.eq_iff, adaptive_composition_extend]
  · rw [if_neg h, PMF.map_apply]
    have hnone : ∀ z : ℝ, x ≠ adaptive_composition_extend y z := by
      intro z hx
      apply h
      calc
        y = adaptive_composition_drop_last (adaptive_composition_extend y z) :=
          ((adaptive_composition_extend_drop_last x).2 y z).1.symm
        _ = adaptive_composition_drop_last x := congrArg adaptive_composition_drop_last hx.symm
    simp [hnone]

@[blueprint "lem:adaptive-composition-path-law-apply"
  (statement := /-- The probability mass of a length-\(k\) adaptive transcript is the product, over its coordinates, of the corresponding conditional call masses evaluated at their preceding prefixes. -/)
  (proof := /-- Induct on \(k\). The empty transcript has mass one. In the successor step, expand the monadic bind. By \cref{lem:adaptive-composition-map-extend-apply}, only the uniquely determined shortened transcript contributes to the sum. Apply the induction hypothesis to its mass and split the finite product at its last coordinate; the definitions of deletion, extension, and conditional prefixes identify the resulting factors. -/)
  (title := /-- Product formula for adaptive transcript mass -/)
  (latexEnv := "lemma")]
lemma adaptive_composition_path_law_apply {Data : Type*} {n d : ℕ}
    (calls : coordinate_calls Data n d) (S : Fin n → Data) :
    ∀ (k : ℕ) (hk : k ≤ d) (x : euclidean_point k),
      adaptive_composition_path_law calls S k hk x =
        ∏ i : Fin k,
          calls (Fin.castLE hk i)
            (adaptive_composition_call_prefix hk x i) S (x i) := by
  intro k
  induction k with
  | zero =>
      intro hk x
      simp [adaptive_composition_path_law]
      exact Subsingleton.elim _ _
  | succ k ih =>
      intro hk x
      rw [adaptive_composition_path_law, PMF.bind_apply]
      simp only [adaptive_composition_map_extend_apply]
      rw [tsum_eq_single (adaptive_composition_drop_last x)]
      · simp only [if_pos rfl]
        let hprev : k ≤ d := Nat.le_trans (Nat.le_succ k) hk
        rw [ih hprev (adaptive_composition_drop_last x), Fin.prod_univ_castSucc]
        congr 1
      · intro y hy
        simp [hy]

@[blueprint "lem:adaptive-composition-path-law-extend"
  (statement := /-- The mass of an extended transcript is the mass of its preceding transcript times the conditional mass of the appended coordinate. -/)
  (proof := /-- Apply \cref{lem:adaptive-composition-path-law-apply} to both path masses, split the successor product at its last coordinate, and use \cref{lem:adaptive-composition-call-prefix-drop-last, lem:adaptive-composition-extend-drop-last} to identify the shortened transcript, its conditional prefixes, and its last value. -/)
  (title := /-- Recursive mass formula for transcript extension -/)
  (latexEnv := "lemma")]
lemma adaptive_composition_path_law_extend {Data : Type*} {n d k : ℕ}
    (calls : coordinate_calls Data n d) (S : Fin n → Data)
    (hk : k + 1 ≤ d) (x : euclidean_point k) (z : ℝ) :
    adaptive_composition_path_law calls S (k + 1) hk
        (adaptive_composition_extend x z) =
      adaptive_composition_path_law calls S k
          (Nat.le_trans (Nat.le_succ k) hk) x *
        calls ⟨k, Nat.lt_of_succ_le hk⟩
          (adaptive_composition_prefix (Nat.le_trans (Nat.le_succ k) hk) x) S z := by
  rw [adaptive_composition_path_law_apply calls S (k + 1) hk,
    adaptive_composition_path_law_apply calls S k
      (Nat.le_trans (Nat.le_succ k) hk), Fin.prod_univ_castSucc]
  have hdrop := (adaptive_composition_extend_drop_last
    (adaptive_composition_extend x z)).2 x z
  have hcp := adaptive_composition_call_prefix_drop_last hk
    (adaptive_composition_extend x z)
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hcp.1 i, hdrop.1]
    simp [adaptive_composition_extend]
  · rw [hcp.2, hdrop.1, hdrop.2]
    have hi : Fin.castLE hk (Fin.last k) =
        (⟨k, Nat.lt_of_succ_le hk⟩ : Fin d) := Fin.ext rfl
    rw [hi]

@[blueprint "lem:adaptive-composition-path-mgf-extend"
  (statement := /-- The good-path moment term of an extended transcript factors into the preceding transcript's moment term and the selected-good-set conditional moment term of its appended coordinate. -/)
  (proof := /-- Apply \cref{lem:adaptive-composition-path-good-loss-last} to split goodness and cumulative privacy loss at the last coordinate, and apply \cref{lem:adaptive-composition-path-law-extend} to split the path mass. The inverse identities in \cref{lem:adaptive-composition-extend-drop-last} reduce the shortened extended transcript to its original prefix. Distributing \(s\) over the loss sum and using the exponential addition law gives the asserted product. -/)
  (title := /-- Factorization of an extended path moment -/)
  (latexEnv := "lemma")]
lemma adaptive_composition_path_mgf_extend {Data : Type*} {n d k : ℕ}
    (calls : coordinate_calls Data n d) (S S' : Fin n → Data)
    (good : Fin d → euclidean_point d → Set ℝ) (hk : k + 1 ≤ d)
    (s : ℝ) (x : euclidean_point k) (z : ℝ) :
    adaptive_composition_path_mgf_term calls S S' good hk s
        (adaptive_composition_extend x z) =
      adaptive_composition_path_mgf_term calls S S' good
          (Nat.le_trans (Nat.le_succ k) hk) s x *
        (good ⟨k, Nat.lt_of_succ_le hk⟩
          (adaptive_composition_prefix (Nat.le_trans (Nat.le_succ k) hk) x)).indicator
          (fun y =>
            (calls ⟨k, Nat.lt_of_succ_le hk⟩
              (adaptive_composition_prefix (Nat.le_trans (Nat.le_succ k) hk) x) S y).toReal *
              Real.exp
                (s * Real.log
                  ((calls ⟨k, Nat.lt_of_succ_le hk⟩
                    (adaptive_composition_prefix
                      (Nat.le_trans (Nat.le_succ k) hk) x) S y).toReal /
                    (calls ⟨k, Nat.lt_of_succ_le hk⟩
                      (adaptive_composition_prefix
                        (Nat.le_trans (Nat.le_succ k) hk) x) S' y).toReal))) z := by
  have hgl := adaptive_composition_path_good_loss_last calls S S' good hk
    (adaptive_composition_extend x z)
  have hdrop := (adaptive_composition_extend_drop_last
    (adaptive_composition_extend x z)).2 x z
  have hgood : adaptive_composition_path_good good hk
        (adaptive_composition_extend x z) ↔
      adaptive_composition_path_good good
          (Nat.le_trans (Nat.le_succ k) hk) x ∧
        z ∈ good ⟨k, Nat.lt_of_succ_le hk⟩
          (adaptive_composition_prefix (Nat.le_trans (Nat.le_succ k) hk) x) := by
    simpa [hdrop.1, hdrop.2] using hgl.1
  have hloss : adaptive_composition_path_privacy_loss calls S S' hk
        (adaptive_composition_extend x z) =
      adaptive_composition_path_privacy_loss calls S S'
          (Nat.le_trans (Nat.le_succ k) hk) x +
        Real.log
          ((calls ⟨k, Nat.lt_of_succ_le hk⟩
              (adaptive_composition_prefix (Nat.le_trans (Nat.le_succ k) hk) x) S z).toReal /
            (calls ⟨k, Nat.lt_of_succ_le hk⟩
              (adaptive_composition_prefix (Nat.le_trans (Nat.le_succ k) hk) x) S' z).toReal) := by
    simpa [hdrop.1, hdrop.2] using hgl.2
  by_cases hx : adaptive_composition_path_good good
      (Nat.le_trans (Nat.le_succ k) hk) x
  · by_cases hz : z ∈ good ⟨k, Nat.lt_of_succ_le hk⟩
        (adaptive_composition_prefix (Nat.le_trans (Nat.le_succ k) hk) x)
    · simp [adaptive_composition_path_mgf_term, hgood.mpr ⟨hx, hz⟩, hx, hz,
        adaptive_composition_path_law_extend, hloss, ENNReal.toReal_mul,
        mul_add, Real.exp_add]
      ring
    · simp [adaptive_composition_path_mgf_term, hgood, hx, hz]
  · simp [adaptive_composition_path_mgf_term, hgood, hx]

@[blueprint "lem:adaptive-composition-path-mgf-bound"
  (statement := /-- If every conditional selected-good-set privacy-loss moment series is summable and bounded by \(\exp(s^2\varepsilon^2/2)\) for \(s\ge0\), then the length-\(k\) good-path moment series is summable and bounded by \(\exp(ks^2\varepsilon^2/2)\). -/)
  (proof := /-- Induct on \(k\). The empty transcript contributes one. For the successor step, reindex transcripts by the extension equivalence of \cref{def:adaptive-composition-extend-equivalence} and factor each term with \cref{lem:adaptive-composition-path-mgf-extend}. The conditional hypothesis makes every inner series summable and bounds its sum by \(\exp(s^2\varepsilon^2/2)\); the induction hypothesis does the same for the outer preceding-path series. Fubini's theorem for nonnegative summable series and multiplication of these two bounds give \(\exp((k+1)s^2\varepsilon^2/2)\). -/)
  (title := /-- Iterated moment bound for adaptive privacy loss -/)
  (latexEnv := "lemma")]
lemma adaptive_composition_path_mgf_bound {Data : Type*} {n d : ℕ}
    (calls : coordinate_calls Data n d) (S S' : Fin n → Data)
    (good : Fin d → euclidean_point d → Set ℝ) (ε s : ℝ) (hs : 0 ≤ s)
    (hmgf : ∀ i pref,
      Summable
          (fun z : ℝ => (good i pref).indicator
            (fun y =>
              (calls i pref S y).toReal *
                Real.exp
                  (s * Real.log
                    ((calls i pref S y).toReal /
                      (calls i pref S' y).toReal))) z) ∧
        ∑' z : ℝ, (good i pref).indicator
          (fun y =>
            (calls i pref S y).toReal *
              Real.exp
                (s * Real.log
                  ((calls i pref S y).toReal /
                    (calls i pref S' y).toReal))) z ≤
          Real.exp (s ^ 2 * ε ^ 2 / 2)) :
    ∀ (k : ℕ) (hk : k ≤ d),
      Summable (adaptive_composition_path_mgf_term calls S S' good hk s) ∧
        ∑' x, adaptive_composition_path_mgf_term calls S S' good hk s x ≤
          Real.exp ((k : ℝ) * s ^ 2 * ε ^ 2 / 2) := by
  intro k
  induction k with
  | zero =>
      intro hk
      constructor
      · exact Summable.of_finite
      · simp [adaptive_composition_path_mgf_term,
          adaptive_composition_path_good, adaptive_composition_path_law,
          adaptive_composition_path_privacy_loss]
        rw [if_pos (Subsingleton.elim _ _)]
        simp
  | succ k ih =>
      intro hk
      let hprev : k ≤ d := Nat.le_trans (Nat.le_succ k) hk
      let A : euclidean_point k → ℝ :=
        adaptive_composition_path_mgf_term calls S S' good hprev s
      let B : euclidean_point k → ℝ → ℝ := fun x =>
        (good ⟨k, Nat.lt_of_succ_le hk⟩
          (adaptive_composition_prefix hprev x)).indicator
          (fun z =>
            (calls ⟨k, Nat.lt_of_succ_le hk⟩
              (adaptive_composition_prefix hprev x) S z).toReal *
              Real.exp
                (s * Real.log
                  ((calls ⟨k, Nat.lt_of_succ_le hk⟩
                    (adaptive_composition_prefix hprev x) S z).toReal /
                    (calls ⟨k, Nat.lt_of_succ_le hk⟩
                      (adaptive_composition_prefix hprev x) S' z).toReal)))
      have hA := ih hprev
      have hB : ∀ x, Summable (B x) ∧
          ∑' z, B x z ≤ Real.exp (s ^ 2 * ε ^ 2 / 2) := by
        intro x
        exact hmgf ⟨k, Nat.lt_of_succ_le hk⟩
          (adaptive_composition_prefix hprev x)
      have hAnonneg : ∀ x, 0 ≤ A x := by
        intro x
        by_cases hx : adaptive_composition_path_good good hprev x
        · simp [A, adaptive_composition_path_mgf_term, hx]
          positivity
        · simp [A, adaptive_composition_path_mgf_term, hx]
      have hBnonneg : ∀ x z, 0 ≤ B x z := by
        intro x z
        by_cases hz : z ∈ good ⟨k, Nat.lt_of_succ_le hk⟩
            (adaptive_composition_prefix hprev x)
        · simp [B, hz]
          positivity
        · simp [B, hz]
      have hinner : ∀ x, Summable (fun z => A x * B x z) := by
        intro x
        exact Summable.mul_left (A x) (hB x).1
      have hinner_sum : ∀ x, ∑' z, A x * B x z = A x * ∑' z, B x z := by
        intro x
        exact Summable.tsum_mul_left (A x) (hB x).1
      have hAC : Summable (fun x => A x * Real.exp (s ^ 2 * ε ^ 2 / 2)) :=
        Summable.mul_right _ hA.1
      have houter : Summable (fun x => ∑' z, A x * B x z) := by
        apply Summable.of_nonneg_of_le
          (fun x => tsum_nonneg fun z => mul_nonneg (hAnonneg x) (hBnonneg x z))
          (fun x => ?_) hAC
        rw [hinner_sum]
        exact mul_le_mul_of_nonneg_left (hB x).2 (hAnonneg x)
      have hprod : Summable (fun p : euclidean_point k × ℝ => A p.1 * B p.1 p.2) := by
        rw [summable_prod_of_nonneg (fun p => mul_nonneg (hAnonneg p.1)
          (hBnonneg p.1 p.2))]
        exact ⟨hinner, houter⟩
      let e := adaptive_composition_extend_equivalence k
      have hcomp : (fun p : euclidean_point k × ℝ =>
          adaptive_composition_path_mgf_term calls S S' good hk s (e p)) =
          fun p => A p.1 * B p.1 p.2 := by
        funext p
        exact adaptive_composition_path_mgf_extend calls S S' good hk s p.1 p.2
      have hsum : Summable
          (adaptive_composition_path_mgf_term calls S S' good hk s) := by
        apply e.summable_iff.mp
        simpa [Function.comp_def, hcomp] using hprod
      constructor
      · exact hsum
      · rw [← e.tsum_eq (adaptive_composition_path_mgf_term calls S S' good hk s),
          hcomp, hprod.tsum_prod]
        calc
          (∑' x, ∑' z, A x * B x z) ≤
              ∑' x, A x * Real.exp (s ^ 2 * ε ^ 2 / 2) :=
            houter.tsum_le_tsum (fun x => by
              rw [hinner_sum]
              exact mul_le_mul_of_nonneg_left (hB x).2 (hAnonneg x)) hAC
          _ = (∑' x, A x) * Real.exp (s ^ 2 * ε ^ 2 / 2) :=
            Summable.tsum_mul_right _ hA.1
          _ ≤ Real.exp ((k : ℝ) * s ^ 2 * ε ^ 2 / 2) *
              Real.exp (s ^ 2 * ε ^ 2 / 2) :=
            mul_le_mul_of_nonneg_right hA.2 (Real.exp_pos _).le
          _ = Real.exp (((k + 1 : ℕ) : ℝ) * s ^ 2 * ε ^ 2 / 2) := by
            rw [← Real.exp_add]
            congr 1
            push_cast
            ring

@[blueprint "lem:event-probability-le-one"
  (statement := /-- The probability of every event under a probability mass function is at most one. -/)
  (proof := /-- Expand \cref{def:event-probability} as the sum of the mass function restricted to the event. Each restricted summand is at most the corresponding unrestricted mass, whose total is one. -/)
  (title := /-- An event has probability at most one -/)
  (latexEnv := "lemma")]
lemma event_probability_le_one {Ω : Type*} (p : PMF Ω) (E : Set Ω) :
    event_probability p E ≤ 1 := by
  rw [event_probability, PMF.toOuterMeasure_apply]
  calc
    (∑' x, E.indicator p x) ≤ ∑' x, p x :=
      ENNReal.tsum_le_tsum fun x => Set.indicator_apply_le fun _ => le_rfl
    _ = 1 := p.tsum_coe

@[blueprint "lem:adaptive-composition-path-bad-probability"
  (statement := /-- If every conditional call leaves its selected good set with probability at most \(\delta\), then a length-\(k\) adaptive transcript leaves at least one selected good set with probability at most \(k\delta\). -/)
  (proof := /-- Induct on \(k\). Condition on the preceding transcript in the successor step. If that transcript is already bad, the conditional probability is at most one by \cref{lem:event-probability-le-one}; if it is good, \cref{lem:adaptive-composition-path-good-loss-last, lem:adaptive-composition-extend-drop-last} identifies the new bad event with the complement of the next selected good set, whose conditional probability is at most \(\delta\). Sum these two cases using the bind formula, apply the induction hypothesis, and use that the preceding good event has probability at most one. -/)
  (title := /-- Union bound for adaptive bad coordinates -/)
  (latexEnv := "lemma")]
lemma adaptive_composition_path_bad_probability {Data : Type*} {n d : ℕ}
    (calls : coordinate_calls Data n d) (S : Fin n → Data)
    (good : Fin d → euclidean_point d → Set ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hbad : ∀ i pref,
      event_probability (calls i pref S) (good i pref)ᶜ ≤ ENNReal.ofReal δ) :
    ∀ (k : ℕ) (hk : k ≤ d),
      event_probability (adaptive_composition_path_law calls S k hk)
          {x | ¬adaptive_composition_path_good good hk x} ≤
        ENNReal.ofReal ((k : ℝ) * δ) := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [event_probability, adaptive_composition_path_good]
  | succ k ih =>
      intro hk
      let hprev : k ≤ d := Nat.le_trans (Nat.le_succ k) hk
      let p := adaptive_composition_path_law calls S k hprev
      let oldGood : Set (euclidean_point k) :=
        {x | adaptive_composition_path_good good hprev x}
      let oldBad : Set (euclidean_point k) := oldGoodᶜ
      let newBad : Set (euclidean_point (k + 1)) :=
        {x | ¬adaptive_composition_path_good good hk x}
      have hcond : ∀ y,
          p y * (PMF.map (adaptive_composition_extend y)
            (calls ⟨k, Nat.lt_of_succ_le hk⟩
              (adaptive_composition_prefix hprev y) S)).toOuterMeasure newBad ≤
            oldBad.indicator p y +
              ENNReal.ofReal δ * oldGood.indicator p y := by
        intro y
        by_cases hy : y ∈ oldGood
        · have hygood : adaptive_composition_path_good good hprev y := hy
          have hpre : adaptive_composition_extend y ⁻¹' newBad =
              (good ⟨k, Nat.lt_of_succ_le hk⟩
                (adaptive_composition_prefix hprev y))ᶜ := by
            ext z
            have hgl := (adaptive_composition_path_good_loss_last calls S S
              good hk (adaptive_composition_extend y z)).1
            have hdrop := (adaptive_composition_extend_drop_last
              (adaptive_composition_extend y z)).2 y z
            have hgood : adaptive_composition_path_good good hk
                  (adaptive_composition_extend y z) ↔
                adaptive_composition_path_good good hprev y ∧
                  z ∈ good ⟨k, Nat.lt_of_succ_le hk⟩
                    (adaptive_composition_prefix hprev y) := by
              simpa [hdrop.1, hdrop.2] using hgl
            simp [newBad, hgood, hygood]
          rw [PMF.toOuterMeasure_map_apply, hpre]
          simp [oldBad, oldGood, hy]
          calc
            p y * event_probability
                (calls ⟨k, Nat.lt_of_succ_le hk⟩
                  (adaptive_composition_prefix hprev y) S)
                (good ⟨k, Nat.lt_of_succ_le hk⟩
                  (adaptive_composition_prefix hprev y))ᶜ ≤
              p y * ENNReal.ofReal δ :=
                mul_le_mul_left' (hbad _ _) _
            _ = ENNReal.ofReal δ * p y := mul_comm _ _
        · have hybad : y ∈ oldBad := hy
          rw [Set.indicator_of_mem hybad, Set.indicator_of_notMem hy]
          simp only [mul_zero, add_zero]
          calc
            p y * (PMF.map (adaptive_composition_extend y)
                (calls ⟨k, Nat.lt_of_succ_le hk⟩
                  (adaptive_composition_prefix hprev y) S)).toOuterMeasure newBad ≤
              p y * 1 := mul_le_mul_left'
                (by
                  change event_probability
                    (PMF.map (adaptive_composition_extend y)
                      (calls ⟨k, Nat.lt_of_succ_le hk⟩
                        (adaptive_composition_prefix hprev y) S)) newBad ≤ 1
                  exact event_probability_le_one _ newBad) _
            _ = p y := mul_one _
      rw [event_probability, adaptive_composition_path_law,
        PMF.toOuterMeasure_bind_apply]
      calc
        (∑' y, p y * (PMF.map (adaptive_composition_extend y)
            (calls ⟨k, Nat.lt_of_succ_le hk⟩
              (adaptive_composition_prefix hprev y) S)).toOuterMeasure newBad) ≤
            ∑' y, (oldBad.indicator p y +
              ENNReal.ofReal δ * oldGood.indicator p y) :=
          ENNReal.tsum_le_tsum hcond
        _ = event_probability p oldBad +
              ENNReal.ofReal δ * event_probability p oldGood := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
          simp only [event_probability, PMF.toOuterMeasure_apply]
        _ ≤ ENNReal.ofReal ((k : ℝ) * δ) + ENNReal.ofReal δ * 1 :=
          add_le_add (ih hprev) (mul_le_mul_left'
            (event_probability_le_one p oldGood) _)
        _ = ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * δ) := by
          rw [mul_one]
          have hkδ : 0 ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg k) hδ
          have heq : (((k + 1 : ℕ) : ℝ) * δ) = (k : ℝ) * δ + δ := by
            push_cast
            ring
          rw [heq, ENNReal.ofReal_add hkδ hδ]

@[blueprint "lem:adaptive-composition-path-tail-probability"
  (statement := /-- A summable good-path moment bound implies the exponential Markov bound: if the moment at exponent \(s\ge0\) is at most \(M\), then the probability of a good transcript whose privacy loss exceeds \(a\) is at most \(e^{-sa}M\). -/)
  (proof := /-- On the tail event, \(s(L-a)\ge0\), so \(1\le e^{-sa}e^{sL}\). Multiplying by the nonnegative path mass bounds each tail mass by \(e^{-sa}\) times its good-path moment term. Sum this pointwise inequality using \cref{def:event-probability, def:adaptive-composition-path-mgf-term}; summability permits conversion of the real sum to extended nonnegative reals and extraction of the constant factor. -/)
  (title := /-- Exponential tail bound from a path moment estimate -/)
  (latexEnv := "lemma")]
lemma adaptive_composition_path_tail_probability {Data : Type*} {n d k : ℕ}
    (calls : coordinate_calls Data n d) (S S' : Fin n → Data)
    (good : Fin d → euclidean_point d → Set ℝ) (hk : k ≤ d)
    (s a M : ℝ) (hs : 0 ≤ s)
    (hsum : Summable (adaptive_composition_path_mgf_term calls S S' good hk s))
    (hbound : ∑' x, adaptive_composition_path_mgf_term calls S S' good hk s x ≤ M) :
    event_probability (adaptive_composition_path_law calls S k hk)
        {x | adaptive_composition_path_good good hk x ∧
          a < adaptive_composition_path_privacy_loss calls S S' hk x} ≤
      ENNReal.ofReal (Real.exp (-s * a) * M) := by
  let tail : Set (euclidean_point k) :=
    {x | adaptive_composition_path_good good hk x ∧
      a < adaptive_composition_path_privacy_loss calls S S' hk x}
  let F := adaptive_composition_path_mgf_term calls S S' good hk s
  have hFnonneg : ∀ x, 0 ≤ F x := by
    intro x
    by_cases hx : adaptive_composition_path_good good hk x
    · simp [F, adaptive_composition_path_mgf_term, hx]
      positivity
    · simp [F, adaptive_composition_path_mgf_term, hx]
  have hscale : Summable (fun x => Real.exp (-s * a) * F x) :=
    Summable.mul_left _ hsum
  have hpoint : ∀ x,
      tail.indicator (adaptive_composition_path_law calls S k hk) x ≤
        ENNReal.ofReal (Real.exp (-s * a) * F x) := by
    intro x
    by_cases hx : x ∈ tail
    · have hxgood : adaptive_composition_path_good good hk x := hx.1
      have hxtail : a < adaptive_composition_path_privacy_loss calls S S' hk x := hx.2
      rw [Set.indicator_of_mem hx]
      rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
      apply ENNReal.ofReal_le_ofReal
      have hexp : 1 ≤ Real.exp (-s * a) *
          Real.exp (s * adaptive_composition_path_privacy_loss calls S S' hk x) := by
        rw [← Real.exp_add]
        have heq : -s * a + s *
            adaptive_composition_path_privacy_loss calls S S' hk x =
              s * (adaptive_composition_path_privacy_loss calls S S' hk x - a) := by
          ring
        rw [heq]
        exact Real.one_le_exp
          (mul_nonneg hs (sub_nonneg.mpr (le_of_lt hxtail)))
      calc
        (adaptive_composition_path_law calls S k hk x).toReal =
            (adaptive_composition_path_law calls S k hk x).toReal * 1 := by ring
        _ ≤ (adaptive_composition_path_law calls S k hk x).toReal *
            (Real.exp (-s * a) *
              Real.exp (s * adaptive_composition_path_privacy_loss calls S S' hk x)) :=
          mul_le_mul_of_nonneg_left hexp ENNReal.toReal_nonneg
        _ = Real.exp (-s * a) * F x := by
          simp [F, adaptive_composition_path_mgf_term, hxgood]
          ring
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  rw [event_probability, PMF.toOuterMeasure_apply]
  calc
    (∑' x, tail.indicator (adaptive_composition_path_law calls S k hk) x) ≤
        ∑' x, ENNReal.ofReal (Real.exp (-s * a) * F x) :=
      ENNReal.tsum_le_tsum hpoint
    _ = ENNReal.ofReal (∑' x, Real.exp (-s * a) * F x) :=
      (ENNReal.ofReal_tsum_of_nonneg
        (fun x => mul_nonneg (Real.exp_pos _).le (hFnonneg x)) hscale).symm
    _ ≤ ENNReal.ofReal (Real.exp (-s * a) * M) := by
      apply ENNReal.ofReal_le_ofReal
      rw [Summable.tsum_mul_left _ hsum]
      exact mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le

@[blueprint "lem:adaptive-composition-path-likelihood-ratio"
  (statement := /-- On a good transcript of nonzero mass under \(S\), the mass under \(S\) equals the exponential of its cumulative privacy loss times its mass under \(S'\). -/)
  (proof := /-- By \cref{lem:adaptive-composition-path-law-apply}, the two path masses are products of their conditional masses. A nonzero source product makes every numerator positive, and conditional absolute continuity on the good sets makes every denominator positive after conversion to \(\mathbb R\). Exponentiating the sum of conditional logarithms in \cref{def:adaptive-composition-path-privacy-loss} therefore gives the product of their ratios, and cancellation yields the identity. -/)
  (title := /-- Likelihood-ratio identity for good adaptive transcripts -/)
  (latexEnv := "lemma")]
lemma adaptive_composition_path_likelihood_ratio {Data : Type*}
    {n d k : ℕ} (calls : coordinate_calls Data n d)
    (S S' : Fin n → Data) (good : Fin d → euclidean_point d → Set ℝ)
    (hk : k ≤ d)
    (hac : ∀ i pref z, z ∈ good i pref → calls i pref S z ≠ 0 →
      calls i pref S' z ≠ 0) (x : euclidean_point k)
    (hxgood : adaptive_composition_path_good good hk x)
    (hx : adaptive_composition_path_law calls S k hk x ≠ 0) :
    (adaptive_composition_path_law calls S k hk x).toReal =
      Real.exp (adaptive_composition_path_privacy_loss calls S S' hk x) *
        (adaptive_composition_path_law calls S' k hk x).toReal := by
  have hxprod : ∀ i : Fin k,
      calls (Fin.castLE hk i) (adaptive_composition_call_prefix hk x i) S
          (x i) ≠ 0 := by
    rw [adaptive_composition_path_law_apply calls S k hk x,
      Finset.prod_ne_zero_iff] at hx
    intro i
    exact hx i (Finset.mem_univ i)
  have hqprod : ∀ i : Fin k,
      calls (Fin.castLE hk i) (adaptive_composition_call_prefix hk x i) S'
          (x i) ≠ 0 := by
    intro i
    exact hac _ _ _ (hxgood i) (hxprod i)
  rw [adaptive_composition_path_law_apply calls S k hk x,
    adaptive_composition_path_law_apply calls S' k hk x]
  simp only [ENNReal.toReal_prod]
  unfold adaptive_composition_path_privacy_loss
  rw [Real.exp_sum]
  have hlog : ∀ i : Fin k,
      Real.exp
          (Real.log
            ((calls (Fin.castLE hk i)
                (adaptive_composition_call_prefix hk x i) S (x i)).toReal /
              (calls (Fin.castLE hk i)
                (adaptive_composition_call_prefix hk x i) S' (x i)).toReal)) =
        (calls (Fin.castLE hk i)
            (adaptive_composition_call_prefix hk x i) S (x i)).toReal /
          (calls (Fin.castLE hk i)
            (adaptive_composition_call_prefix hk x i) S' (x i)).toReal := by
    intro i
    rw [Real.exp_log]
    exact div_pos
      (ENNReal.toReal_pos (hxprod i) (PMF.apply_ne_top _ _))
      (ENNReal.toReal_pos (hqprod i) (PMF.apply_ne_top _ _))
  simp_rw [hlog]
  rw [Finset.prod_div_distrib]
  have hqreal : (∏ i : Fin k,
      (calls (Fin.castLE hk i)
        (adaptive_composition_call_prefix hk x i) S' (x i)).toReal) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    exact (ENNReal.toReal_pos (hqprod i) (PMF.apply_ne_top _ _)).ne'
  field_simp [hqreal]

@[blueprint "lem:adaptive-composition-path-event-bound"
  (statement := /-- Suppose bad good-set mass is at most \(D\), good-path privacy-loss tail mass above \(a\) is at most \(T\), and conditional absolute continuity holds on every good set. Then every path event has source probability at most \(e^a\) times its target probability plus \(D+T\). -/)
  (proof := /-- Partition each source event atom into three cases. A transcript outside the good sets is charged to the bad event; a good transcript with privacy loss above \(a\) is charged to the tail event. For every remaining good transcript of nonzero source mass, \cref{lem:adaptive-composition-path-likelihood-ratio} and monotonicity of the exponential give source mass at most \(e^a\) times target mass; zero source atoms are immediate. Sum the pointwise inequality using \cref{def:event-probability}, then apply the assumed bad and tail bounds. -/)
  (title := /-- Differential-privacy event bound from good paths and tails -/)
  (latexEnv := "lemma")]
lemma adaptive_composition_path_event_bound {Data : Type*} {n d k : ℕ}
    (calls : coordinate_calls Data n d) (S S' : Fin n → Data)
    (good : Fin d → euclidean_point d → Set ℝ) (hk : k ≤ d)
    (a D T : ℝ)
    (hac : ∀ i pref z, z ∈ good i pref → calls i pref S z ≠ 0 →
      calls i pref S' z ≠ 0)
    (hbad : event_probability (adaptive_composition_path_law calls S k hk)
      {x | ¬adaptive_composition_path_good good hk x} ≤ ENNReal.ofReal D)
    (htail : event_probability (adaptive_composition_path_law calls S k hk)
      {x | adaptive_composition_path_good good hk x ∧
        a < adaptive_composition_path_privacy_loss calls S S' hk x} ≤
          ENNReal.ofReal T) (E : Set (euclidean_point k)) :
    event_probability (adaptive_composition_path_law calls S k hk) E ≤
      ENNReal.ofReal (Real.exp a) *
          event_probability (adaptive_composition_path_law calls S' k hk) E +
        ENNReal.ofReal D + ENNReal.ofReal T := by
  let p := adaptive_composition_path_law calls S k hk
  let q := adaptive_composition_path_law calls S' k hk
  let bad : Set (euclidean_point k) :=
    {x | ¬adaptive_composition_path_good good hk x}
  let tail : Set (euclidean_point k) :=
    {x | adaptive_composition_path_good good hk x ∧
      a < adaptive_composition_path_privacy_loss calls S S' hk x}
  have hpoint : ∀ x,
      E.indicator p x ≤ bad.indicator p x + tail.indicator p x +
        ENNReal.ofReal (Real.exp a) * E.indicator q x := by
    intro x
    by_cases hxE : x ∈ E
    · rw [Set.indicator_of_mem hxE, Set.indicator_of_mem hxE]
      by_cases hxgood : adaptive_composition_path_good good hk x
      · have hxbad : x ∉ bad := by
          intro h
          exact h hxgood
        rw [Set.indicator_of_notMem hxbad]
        by_cases hxloss : a < adaptive_composition_path_privacy_loss calls S S' hk x
        · have hxtail : x ∈ tail := ⟨hxgood, hxloss⟩
          rw [Set.indicator_of_mem hxtail]
          simp only [zero_add]
          exact le_add_of_nonneg_right bot_le
        · have hxtail : x ∉ tail := by
            intro h
            exact hxloss h.2
          rw [Set.indicator_of_notMem hxtail, add_zero, zero_add]
          by_cases hxp : p x = 0
          · simp [hxp]
          · have hratio := adaptive_composition_path_likelihood_ratio calls S S'
                good hk hac x hxgood hxp
            have hreal : (p x).toReal ≤ Real.exp a * (q x).toReal := by
              rw [hratio]
              exact mul_le_mul_of_nonneg_right
                (Real.exp_le_exp.mpr (le_of_not_gt hxloss)) ENNReal.toReal_nonneg
            rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top p x),
              ← ENNReal.ofReal_toReal (PMF.apply_ne_top q x),
              ← ENNReal.ofReal_mul (Real.exp_pos a).le]
            exact ENNReal.ofReal_le_ofReal hreal
      · have hxbad : x ∈ bad := hxgood
        rw [Set.indicator_of_mem hxbad]
        exact le_trans (le_add_right (le_refl (p x)))
          (le_add_right (le_refl (p x + tail.indicator p x)))
    · rw [Set.indicator_of_notMem hxE, Set.indicator_of_notMem hxE]
      exact bot_le
  rw [event_probability, PMF.toOuterMeasure_apply]
  calc
    (∑' x, E.indicator p x) ≤
        ∑' x, (bad.indicator p x + tail.indicator p x +
          ENNReal.ofReal (Real.exp a) * E.indicator q x) :=
      ENNReal.tsum_le_tsum hpoint
    _ = event_probability p bad + event_probability p tail +
        ENNReal.ofReal (Real.exp a) * event_probability q E := by
      rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left]
      simp only [event_probability, PMF.toOuterMeasure_apply]
    _ ≤ ENNReal.ofReal D + ENNReal.ofReal T +
        ENNReal.ofReal (Real.exp a) * event_probability q E :=
      add_le_add (add_le_add hbad htail) (le_refl _)
    _ = ENNReal.ofReal (Real.exp a) * event_probability q E +
        ENNReal.ofReal D + ENNReal.ofReal T := by
      ac_rfl

@[blueprint "lem:adaptive-composition-path-state-law"
  (statement := /-- For every \(k\le d\), pushing the partial transcript law forward by zero-extension gives the partial state law of the adaptive optimizer. -/)
  (proof := /-- Induct on \(k\). Both laws are point masses at zero for \(k=0\). For the successor step, distribute the prefix pushforward through the monadic bind and use \cref{lem:adaptive-composition-prefix-extend} to identify appending the sampled value with updating coordinate \(k\). The induction hypothesis then identifies the preceding path and state laws. -/)
  (title := /-- Equivalence of transcript and state laws -/)
  (latexEnv := "lemma")]
lemma adaptive_composition_path_state_law {Data : Type*} {n d : ℕ}
    (calls : coordinate_calls Data n d) (S : Fin n → Data) :
    ∀ (k : ℕ) (hk : k ≤ d),
      PMF.map (adaptive_composition_prefix hk)
          (adaptive_composition_path_law calls S k hk) =
        adaptive_composition_state_law calls S k hk := by
  intro k
  induction k with
  | zero =>
      intro hk
      rw [adaptive_composition_path_law, adaptive_composition_state_law,
        Fin.foldl_zero, PMF.pure_map]
      congr 1
  | succ k ih =>
      intro hk
      rw [adaptive_composition_state_law, Fin.foldl_succ_last]
      simp only [adaptive_composition_path_law, PMF.map_bind, PMF.map_comp]
      let hprev : k ≤ d := Nat.le_trans (Nat.le_succ k) hk
      change
        ((adaptive_composition_path_law calls S k hprev).bind fun x =>
          PMF.map (adaptive_composition_prefix hk ∘
            adaptive_composition_extend x)
            (calls ⟨k, Nat.lt_of_succ_le hk⟩
              (adaptive_composition_prefix hprev x) S)) =
          (adaptive_composition_state_law calls S k hprev).bind fun x =>
            PMF.map
              (fun z => Function.update x ⟨k, Nat.lt_of_succ_le hk⟩ z)
              (calls ⟨k, Nat.lt_of_succ_le hk⟩ x S)
      rw [← ih hprev]
      simp only [PMF.bind_map, Function.comp_apply]
      apply congrArg (PMF.bind (adaptive_composition_path_law calls S k
        (Nat.le_trans (Nat.le_succ k) hk)))
      funext x
      apply congrArg (fun f : ℝ → euclidean_point d =>
        PMF.map f (calls ⟨k, Nat.lt_of_succ_le hk⟩
          (adaptive_composition_prefix hprev x) S))
      funext z
      exact adaptive_composition_prefix_extend hk x z

@[blueprint "lem:adaptive-composition-state-law-full"
  (statement := /-- After all \(d\) calls, the partial state law is the law of the adaptive high-dimensional optimizer. -/)
  (proof := /-- Rewrite the finite left fold defining the state law as the fold over \(\operatorname{Fin}(d)\) used in \cref{def:adaptive-high-dimensional-optimizer}. At the full dimension, the canonical embedding of every coordinate is the coordinate itself, so the two folds coincide. -/)
  (title := /-- The full state law is the optimizer law -/)
  (latexEnv := "lemma")]
lemma adaptive_composition_state_law_full {Data : Type*} {n d : ℕ}
    (calls : coordinate_calls Data n d) (S : Fin n → Data) :
    adaptive_composition_state_law calls S d (Nat.le_refl d) =
      adaptive_high_dimensional_optimizer calls S := by
  simp [adaptive_composition_state_law, adaptive_high_dimensional_optimizer,
    Fin.foldl_eq_finRange_foldl]

@[blueprint "lem:adaptive-composition-path-law-full"
  (statement := /-- The full length-\(d\) transcript law is exactly the output law of the adaptive high-dimensional optimizer. -/)
  (proof := /-- At full length, zero-extension is the identity on \(\mathbb R^d\). Therefore \cref{lem:adaptive-composition-path-state-law} identifies the path law with the full state law, and \cref{lem:adaptive-composition-state-law-full} identifies that state law with \cref{def:adaptive-high-dimensional-optimizer}. -/)
  (title := /-- The full transcript law is the optimizer law -/)
  (latexEnv := "lemma")]
lemma adaptive_composition_path_law_full {Data : Type*} {n d : ℕ}
    (calls : coordinate_calls Data n d) (S : Fin n → Data) :
    adaptive_composition_path_law calls S d (Nat.le_refl d) =
      adaptive_high_dimensional_optimizer calls S := by
  have hpref : adaptive_composition_prefix (Nat.le_refl d) =
      (id : euclidean_point d → euclidean_point d) := by
    funext x
    funext i
    simp [adaptive_composition_prefix]
  calc
    adaptive_composition_path_law calls S d (Nat.le_refl d) =
        PMF.map id (adaptive_composition_path_law calls S d (Nat.le_refl d)) :=
      (PMF.map_id _).symm
    _ = PMF.map (adaptive_composition_prefix (Nat.le_refl d))
        (adaptive_composition_path_law calls S d (Nat.le_refl d)) := by rw [hpref]
    _ = adaptive_composition_state_law calls S d (Nat.le_refl d) :=
      adaptive_composition_path_state_law calls S d (Nat.le_refl d)
    _ = adaptive_high_dimensional_optimizer calls S :=
      adaptive_composition_state_law_full calls S

@[blueprint "lem:adaptive-advanced-composition"
  (statement := /-- Let \(\mathcal X\) be a data domain, let \(n,d\in\mathbb N\), let \(\varepsilon,\delta,\delta'\in\mathbb R\) satisfy \(\varepsilon,\delta\ge0\) and \(\delta'>0\), and fix a family of \(d\) adaptive coordinate calls on datasets in \(\mathcal X^n\) as in \cref{def:coordinate-calls}. Suppose that this family is pointwise \((\varepsilon,\delta)\)-differentially private in the sense of \cref{def:adaptive-calls-private} and has centered subgaussian privacy loss with parameters \((\varepsilon,\delta)\) in the sense of \cref{def:adaptive-calls-centered-subgaussian-privacy-loss}, including summability of every conditional privacy-loss moment series at every nonnegative exponent. Then the adaptive high-dimensional optimizer of \cref{def:adaptive-high-dimensional-optimizer} is
\[
\left(\varepsilon\sqrt{2d\log(1/\delta')},\ d\delta+\delta'\right)
\]
differentially private. -/)
  (proof := /-- Fix an ordered neighboring pair \(S,S'\) and an output event. If \(d\delta+\delta'\ge1\), the result follows immediately from \cref{lem:event-probability-le-one}. Hence assume \(d\delta+\delta'<1\), so \(0<\delta'<1\). For every coordinate and prefix, choose the good set supplied by \cref{def:adaptive-calls-centered-subgaussian-privacy-loss}. The adaptive union bound \cref{lem:adaptive-composition-path-bad-probability} gives probability at most \(d\delta\) for leaving one of these sets.

For \(d>0\) and \(\varepsilon>0\), put
\[
 L_0=\log(1/\delta'),\qquad r=\sqrt{2dL_0},\qquad
 a=\varepsilon r,\qquad s=\frac{r}{d\varepsilon}.
\]
By \cref{lem:adaptive-composition-path-mgf-bound}, the good-path moment series at exponent \(s\) is summable and at most \(\exp(ds^2\varepsilon^2/2)\). Applying \cref{lem:adaptive-composition-path-tail-probability} and using \(-sa+ds^2\varepsilon^2/2=-L_0\) bounds by \(\delta'\) the good-path event on which the cumulative privacy loss exceeds \(a\). The event comparison in \cref{lem:adaptive-composition-path-event-bound} then yields the desired path-law privacy inequality with exceptional mass \(d\delta+\delta'\).

If \(\varepsilon=0\), set
\[
 b=\log(1+\delta'/2),\qquad s=\frac{\log(2/\delta')}{b}.
\]
The same moment and tail lemmas give tail mass at most \(\delta'/2\) above loss \(b\). The event bound has multiplicative factor \(e^b=1+\delta'/2\); since the target event probability is at most one by \cref{lem:event-probability-le-one}, its excess over factor one is at most the remaining \(\delta'/2\). Thus the total additive mass is again \(d\delta+\delta'\). When \(d=0\), the empty path has no bad coordinate and no positive privacy loss, so the event bound gives equality of the two path laws. Finally, \cref{lem:adaptive-composition-path-law-full} identifies the full path laws with the output laws of \cref{def:adaptive-high-dimensional-optimizer}. -/)
  (title := /-- Advanced composition of the adaptive coordinate calls -/)
  (latexEnv := "lemma")]
lemma adaptive_advanced_composition {Data : Type*} {n d : ℕ}
    (calls : coordinate_calls Data n d) (ε δ δ' : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδ' : 0 < δ')
    (hprivate : adaptive_calls_private calls ε δ)
    (hcentered :
      adaptive_calls_centered_subgaussian_privacy_loss calls ε δ) :
    differentially_private (adaptive_high_dimensional_optimizer calls)
      (ε * Real.sqrt (2 * (d : ℝ) * Real.log (1 / δ')))
      ((d : ℝ) * δ + δ') := by
  classical
  unfold differentially_private
  intro S S' hSS' E
  by_cases hlarge : 1 ≤ (d : ℝ) * δ + δ'
  · calc
      event_probability (adaptive_high_dimensional_optimizer calls S) E ≤ 1 :=
        event_probability_le_one _ _
      _ ≤ ENNReal.ofReal
            (Real.exp (ε * Real.sqrt (2 * (d : ℝ) * Real.log (1 / δ')))) *
            event_probability (adaptive_high_dimensional_optimizer calls S') E +
          ENNReal.ofReal ((d : ℝ) * δ + δ') :=
        le_add_of_le_right (by simpa using ENNReal.ofReal_le_ofReal hlarge)
  · have htotal : (d : ℝ) * δ + δ' < 1 := lt_of_not_ge hlarge
    have hdδ : 0 ≤ (d : ℝ) * δ := mul_nonneg (Nat.cast_nonneg d) hδ
    have hδ'lt : δ' < 1 := by linarith
    choose good hgood using fun i pref => hcentered i pref S S' hSS'
    have hbadS : ∀ i pref,
        event_probability (calls i pref S) (good i pref)ᶜ ≤ ENNReal.ofReal δ :=
      fun i pref => (hgood i pref).1
    have hac : ∀ i pref z, z ∈ good i pref → calls i pref S z ≠ 0 →
        calls i pref S' z ≠ 0 :=
      fun i pref => (hgood i pref).2.2.1
    have hbadPath := adaptive_composition_path_bad_probability calls S good δ hδ
      hbadS d (Nat.le_refl d)
    by_cases hd0 : d = 0
    · subst d
      have htail0 : event_probability
          (adaptive_composition_path_law calls S 0 (Nat.le_refl 0))
          {x | adaptive_composition_path_good good (Nat.le_refl 0) x ∧
            0 < adaptive_composition_path_privacy_loss calls S S'
              (Nat.le_refl 0) x} ≤ ENNReal.ofReal 0 := by
        simp [event_probability, adaptive_composition_path_privacy_loss]
      have hbad0 : event_probability
          (adaptive_composition_path_law calls S 0 (Nat.le_refl 0))
          {x | ¬adaptive_composition_path_good good (Nat.le_refl 0) x} ≤
            ENNReal.ofReal 0 := by
        simpa using hbadPath
      have hev := adaptive_composition_path_event_bound calls S S' good
        (Nat.le_refl 0) 0 0 0 hac hbad0 htail0 E
      rw [adaptive_composition_path_law_full calls S,
        adaptive_composition_path_law_full calls S'] at hev
      exact hev.trans (by simpa using
        (le_add_right (le_refl
          (event_probability (adaptive_high_dimensional_optimizer calls S') E))))
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
      by_cases hε0 : ε = 0
      · subst ε
        let b := Real.log (1 + δ' / 2)
        have hbarg : 1 < 1 + δ' / 2 := by linarith
        have hb : 0 < b := Real.log_pos hbarg
        have htwo : 1 < 2 / δ' := (one_lt_div hδ').2 (by linarith)
        have hlogtwo : 0 < Real.log (2 / δ') := Real.log_pos htwo
        let s := Real.log (2 / δ') / b
        have hs : 0 ≤ s := by positivity
        have hmgfPath := adaptive_composition_path_mgf_bound calls S S' good 0 s hs
          (fun i pref => (hgood i pref).2.2.2 s hs) d (Nat.le_refl d)
        have htailRaw := adaptive_composition_path_tail_probability calls S S' good
          (Nat.le_refl d) s b 1 hs hmgfPath.1 (by simpa using hmgfPath.2)
        have hsb : s * b = Real.log (2 / δ') := by
          dsimp [s]
          field_simp
        have htailValue : Real.exp (-s * b) * 1 = δ' / 2 := by
          rw [show -s * b = -(s * b) by ring, hsb, Real.exp_neg,
            Real.exp_log (div_pos (by norm_num) hδ')]
          field_simp
        have htail : event_probability
            (adaptive_composition_path_law calls S d (Nat.le_refl d))
            {x | adaptive_composition_path_good good (Nat.le_refl d) x ∧
              b < adaptive_composition_path_privacy_loss calls S S'
                (Nat.le_refl d) x} ≤ ENNReal.ofReal (δ' / 2) := by
          rw [htailValue] at htailRaw
          exact htailRaw
        have hev := adaptive_composition_path_event_bound calls S S' good
          (Nat.le_refl d) b ((d : ℝ) * δ) (δ' / 2) hac hbadPath htail E
        rw [adaptive_composition_path_law_full calls S,
          adaptive_composition_path_law_full calls S'] at hev
        let u := δ' / 2
        have hu : 0 ≤ u := by positivity
        have hexpb : Real.exp b = 1 + u := by
          dsimp [b, u]
          rw [Real.exp_log]
          linarith
        have hcoeff : ENNReal.ofReal (Real.exp b) = 1 + ENNReal.ofReal u := by
          rw [hexpb, ENNReal.ofReal_add zero_le_one hu]
          simp
        have hq := event_probability_le_one
          (adaptive_high_dimensional_optimizer calls S') E
        have huq : ENNReal.ofReal u *
            event_probability (adaptive_high_dimensional_optimizer calls S') E ≤
              ENNReal.ofReal u := by
          simpa using mul_le_mul_left' hq (ENNReal.ofReal u)
        have hadd : ENNReal.ofReal ((d : ℝ) * δ) + ENNReal.ofReal u +
            ENNReal.ofReal u = ENNReal.ofReal ((d : ℝ) * δ + δ') := by
          rw [← ENNReal.ofReal_add hdδ hu,
            ← ENNReal.ofReal_add (add_nonneg hdδ hu) hu]
          congr 1
          dsimp [u]
          ring
        simp only [zero_mul, Real.exp_zero, ENNReal.ofReal_one, one_mul]
        calc
          event_probability (adaptive_high_dimensional_optimizer calls S) E ≤
              ENNReal.ofReal (Real.exp b) *
                  event_probability (adaptive_high_dimensional_optimizer calls S') E +
                ENNReal.ofReal ((d : ℝ) * δ) + ENNReal.ofReal u := by
            simpa [u] using hev
          _ = event_probability (adaptive_high_dimensional_optimizer calls S') E +
                ENNReal.ofReal u *
                  event_probability (adaptive_high_dimensional_optimizer calls S') E +
                ENNReal.ofReal ((d : ℝ) * δ) + ENNReal.ofReal u := by
            rw [hcoeff]
            ring
          _ ≤ event_probability (adaptive_high_dimensional_optimizer calls S') E +
                ENNReal.ofReal u + ENNReal.ofReal ((d : ℝ) * δ) +
                ENNReal.ofReal u := by
            exact add_le_add
              (add_le_add (add_le_add (le_refl _) huq) (le_refl _)) (le_refl _)
          _ = event_probability (adaptive_high_dimensional_optimizer calls S') E +
                ENNReal.ofReal ((d : ℝ) * δ + δ') := by
            rw [← hadd]
            ac_rfl
      · have hεpos : 0 < ε := lt_of_le_of_ne hε (Ne.symm hε0)
        let L := Real.log (1 / δ')
        have hfrac : 1 < 1 / δ' := (one_lt_div hδ').2 hδ'lt
        have hL : 0 < L := Real.log_pos hfrac
        let r := Real.sqrt (2 * (d : ℝ) * L)
        have hrad : 0 < 2 * (d : ℝ) * L := by positivity
        have hr : 0 < r := Real.sqrt_pos.2 hrad
        have hr2 : r ^ 2 = 2 * (d : ℝ) * L := by
          exact Real.sq_sqrt hrad.le
        let a := ε * r
        let s := r / ((d : ℝ) * ε)
        have hs : 0 ≤ s := by positivity
        have hmgfPath := adaptive_composition_path_mgf_bound calls S S' good ε s hs
          (fun i pref => (hgood i pref).2.2.2 s hs) d (Nat.le_refl d)
        have htailRaw := adaptive_composition_path_tail_probability calls S S' good
          (Nat.le_refl d) s a
          (Real.exp ((d : ℝ) * s ^ 2 * ε ^ 2 / 2)) hs hmgfPath.1 hmgfPath.2
        have hexponent : -s * a + (d : ℝ) * s ^ 2 * ε ^ 2 / 2 = -L := by
          dsimp [s, a]
          field_simp
          nlinarith [hr2]
        have htailValue : Real.exp (-s * a) *
            Real.exp ((d : ℝ) * s ^ 2 * ε ^ 2 / 2) = δ' := by
          rw [← Real.exp_add, hexponent]
          dsimp [L]
          rw [one_div, Real.log_inv, neg_neg, Real.exp_log hδ']
        have htail : event_probability
            (adaptive_composition_path_law calls S d (Nat.le_refl d))
            {x | adaptive_composition_path_good good (Nat.le_refl d) x ∧
              a < adaptive_composition_path_privacy_loss calls S S'
                (Nat.le_refl d) x} ≤ ENNReal.ofReal δ' := by
          rw [htailValue] at htailRaw
          exact htailRaw
        have hev := adaptive_composition_path_event_bound calls S S' good
          (Nat.le_refl d) a ((d : ℝ) * δ) δ' hac hbadPath htail E
        rw [adaptive_composition_path_law_full calls S,
          adaptive_composition_path_law_full calls S'] at hev
        have ha : a = ε * Real.sqrt (2 * (d : ℝ) * Real.log (1 / δ')) := by
          rfl
        rw [ha] at hev
        rw [ENNReal.ofReal_add hdδ hδ'.le]
        simpa [add_assoc] using hev

@[blueprint "thm:ip-concave-high-dim-privacy"
  (statement := /-- Let \(\varepsilon>0\), let \(\delta,\alpha,\beta\in(0,1)\), and let \(n,t,d\in\mathbb N\) with \(n\ge t\). Fix an objective \(Q\), fixed finite coordinate domains \(\widetilde{\mathcal X}_i\subset\mathbb R\), functions \(n_{IP}\) and \(L\), and a witness that the coordinate mechanisms implement the corresponding one-dimensional private optimizer. Assume in addition that the selected adaptive coordinate calls have centered subgaussian privacy loss with parameters \((\varepsilon,\delta)\), including summability of every conditional privacy-loss moment series at every nonnegative exponent. Then for every \(\delta'>0\), the mechanism \(\operatorname{IPConcaveHighDim}_{\alpha,\beta,\varepsilon,\delta,t}(\cdot,Q)\) is
\[
\left(\varepsilon\sqrt{2d\log(1/\delta')},\ d\delta+\delta'\right)
\]
differentially private. -/)
  (proof := /-- Regard each fixed domain \(\widetilde{\mathcal X}_i\) as the domain assigned to coordinate \(i\) after every possible prefix. The witness used in \cref{def:ip-concave-high-dimensional-optimizer} supplies one fixed family of calls. By \cref{lem:ip-concave-coordinate-calls-private}, every conditional call in that family is \((\varepsilon,\delta)\)-differentially private. The additional hypothesis gives both summability and the centered conditional moment estimate in \cref{def:adaptive-calls-centered-subgaussian-privacy-loss} for this same family. Since \(\varepsilon>0\) and \(\delta>0\), the nonnegativity hypotheses of \cref{lem:adaptive-advanced-composition} hold. Applying that lemma to the \(d\) adaptive calls yields privacy-loss parameter
\[
\varepsilon\sqrt{2d\log(1/\delta')}
\]
and additive failure parameter \(d\delta+\delta'\), as claimed. -/)
  (title := /-- Privacy of the high-dimensional quasiconcave optimizer -/)
  (latexEnv := "theorem")]
theorem ip_concave_high_dim_privacy {Data : Type*} {n t d : ℕ}
    (Q : List Data → euclidean_point d → ℝ)
    (domains : Fin d → Finset ℝ)
    (nIP : ℕ → ℝ → ℝ → ℝ → ℕ) (logStar : ℕ → ℝ)
    (α β ε δ δ' : ℝ)
    (optimizer : one_dimensional_ip_optimizer_witness
      (n := n) (t := t) Q (fun i _ => domains i)
        nIP logStar α β ε δ)
    (hcentered :
      adaptive_calls_centered_subgaussian_privacy_loss
        (ip_concave_coordinate_calls (n := n) (t := t)
          Q (fun i _ => domains i)
          nIP logStar α β ε δ optimizer) ε δ)
    (hε : 0 < ε) (hδ : 0 < δ ∧ δ < 1)
    (hα : 0 < α ∧ α < 1) (hβ : 0 < β ∧ β < 1)
    (hnt : t ≤ n) (hδ' : 0 < δ') :
    differentially_private
      (ip_concave_high_dimensional_optimizer
        (n := n) (t := t)
        Q domains nIP logStar α β ε δ optimizer)
      (ε * Real.sqrt (2 * (d : ℝ) * Real.log (1 / δ')))
      ((d : ℝ) * δ + δ') := by
  exact
    adaptive_advanced_composition
      (ip_concave_coordinate_calls (n := n) (t := t)
        Q (fun i _ => domains i)
        nIP logStar α β ε δ optimizer)
      ε δ δ' hε.le hδ.1.le hδ'
      (ip_concave_coordinate_calls_private
        Q (fun i _ => domains i)
        nIP logStar α β ε δ optimizer hε hδ hα hβ hnt)
      hcentered

@[blueprint "lem:approximation-transfers-to-coordinate-profiles"
  (statement := /-- Let $\mathcal X$ be a type, let $d\in\mathbb N$, let $Q:\mathcal X^*\times\mathbb R^d\to\mathbb R$, let $S,S'\in\mathcal X^*$, let $\alpha\in\mathbb R$, let $i\in\operatorname{Fin}(d)$ and $p\in\mathbb R^d$, and let $h,h':\mathbb R\to\mathbb R$. Suppose that $S'$ is an $\alpha$-approximation of $S$ with respect to $Q$, and that $h$ and $h'$ are attained $i$th coordinate profiles of $Q(S,\cdot)$ and $Q(S',\cdot)$ at the common prefix $p$. Then $|h(z)-h'(z)|\le\alpha$ for every $z\in\mathbb R$. -/)
  (proof := /-- Fix $z\in\mathbb R$. By \cref{def:is-coordinate-profile}, choose a completion $x'$ attaining $h'(z)$. Since the two profiles use the same coordinate and prefix, $x'$ is admissible for the profile $h$, so $Q(S,x')\le h(z)$. By \cref{def:alpha-approximation}, $Q(S',x')-Q(S,x')\le\alpha$; hence $h'(z)-h(z)\le\alpha$. Similarly, choose a completion $x$ attaining $h(z)$. It is admissible for $h'$, whence $Q(S',x)\le h'(z)$, while the approximation bound gives $Q(S,x)-Q(S',x)\le\alpha$. Thus $h(z)-h'(z)\le\alpha$. The two inequalities yield $|h(z)-h'(z)|\le\alpha$. -/)
  (title := /-- Uniform approximation of coordinate profiles -/)
  (latexEnv := "lemma")]
lemma approximation_transfers_to_coordinate_profiles
    {Data : Type*} {d : ℕ}
    (Q : List Data → euclidean_point d → ℝ) (S S' : List Data)
    (α : ℝ) (i : Fin d) (pref : euclidean_point d) (h h' : ℝ → ℝ)
    (happrox : alpha_approximation Q S S' α)
    (hh : is_coordinate_profile (Q S) i pref h)
    (hh' : is_coordinate_profile (Q S') i pref h') :
    ∀ z, |h z - h' z| ≤ α := by
  intro z
  rw [abs_le]
  constructor
  · rcases (hh' z).1 with ⟨x, hxpref, hxz, hxval⟩
    have hxmax : Q S x ≤ h z := (hh z).2 ⟨x, hxpref, hxz, rfl⟩
    have hxapprox := happrox x
    linarith [neg_le_abs (Q S x - Q S' x)]
  · rcases (hh z).1 with ⟨x, hxpref, hxz, hxval⟩
    have hxmax : Q S' x ≤ h' z := (hh' z).2 ⟨x, hxpref, hxz, rfl⟩
    linarith [le_abs_self (Q S x - Q S' x), happrox x]

@[blueprint "lem:coordinate-profile-quasiconcave"
  (statement := /-- Let $d\in\mathbb N$, $q:\mathbb R^d\to\mathbb R$, $i\in\{0,\ldots,d-1\}$, $p\in\mathbb R^d$, and $h:\mathbb R\to\mathbb R$. Suppose that $q$ is quasiconcave on $\mathbb R^d$ and that, for every $z\in\mathbb R$, $h(z)$ is the greatest value attained by $q(x)$ among all $x\in\mathbb R^d$ that agree with $p$ in every coordinate preceding $i$ and satisfy $x_i=z$. Then $h$ is quasiconcave on $\mathbb R$. -/)
  (proof := /-- Use Mathlib's characterization `quasiconcaveOn_iff_min_le`. Fix $z,w\in\mathbb R$ and $a,b\geq 0$ with $a+b=1$. By \cref{def:is-coordinate-profile,def:coordinate-profile-values}, choose completions $x,y\in\mathbb R^d$ attaining $h(z)=q(x)$ and $h(w)=q(y)$, respectively. Both completions agree with the prescribed prefix before $i$, while $x_i=z$ and $y_i=w$. Hence \cref{def:agrees-before} and $a+b=1$ show that $ax+by$ agrees with the same prefix before $i$, and its $i$th coordinate is $az+bw$. Quasiconcavity of $q$ gives
  \[
    \min\{q(x),q(y)\}\leq q(ax+by).
  \]
  Since $q(ax+by)$ belongs to the coordinate-profile value set at $az+bw$, the greatest-value property in \cref{def:is-coordinate-profile} gives $q(ax+by)\leq h(az+bw)$. Substituting the two attained values proves
  \[
    \min\{h(z),h(w)\}\leq h(az+bw).
  \]
  The ambient set $\mathbb R$ is convex, so the same characterization proves that $h$ is quasiconcave on $\mathbb R$. -/)
  (title := /-- Quasiconcavity of a partially maximized profile -/)
  (latexEnv := "lemma")]
lemma coordinate_profile_quasiconcave {d : ℕ}
    (q : euclidean_point d → ℝ) (i : Fin d)
    (pref : euclidean_point d) (h : ℝ → ℝ)
    (hq : QuasiconcaveOn ℝ Set.univ q)
    (hh : is_coordinate_profile q i pref h) :
    QuasiconcaveOn ℝ Set.univ h := by
  rw [quasiconcaveOn_iff_min_le]
  refine ⟨convex_univ, ?_⟩
  intro z _ w _ a b ha hb hab
  rcases (hh z).1 with ⟨x, hxpref, hxi, hxval⟩
  rcases (hh w).1 with ⟨y, hypref, hyi, hyval⟩
  calc
    min (h z) (h w) = min (q x) (q y) := by rw [hxval, hyval]
    _ ≤ q (a • x + b • y) :=
      (quasiconcaveOn_iff_min_le.mp hq).2 (by simp) (by simp) ha hb hab
    _ ≤ h (a • z + b • w) := (hh (a • z + b • w)).2 (by
      refine ⟨a • x + b • y, ?_, ?_, rfl⟩
      · intro j hj
        change a * x j + b * y j = pref j
        rw [hxpref j hj, hypref j hj, ← add_mul, hab, one_mul]
      · simp [hxi, hyi])

@[blueprint "lem:simultaneous-coordinate-steps"
  (statement := /-- Let $\mathcal X$ be a type and let $n,t,d\in\mathbb N$. Let $Q:\mathcal X^*\times\mathbb R^d\to\mathbb R$, let $S\in\mathcal X^n$, let a random-subset sampler, a family of adaptive finite coordinate domains, and a family of adaptive coordinate calls be given, and fix $\alpha,\beta,\beta'\in\mathbb R$ and $X\in\mathbb N$. Suppose that $(S,Q)$ can be $(\alpha,\beta',n/t)$-approximated with respect to the sampler, that $Q(S,\cdot)$ is quasiconcave and attains a global maximum, that the adaptive domains are proper for $Q$ and have maximum cardinality $X$, and that the coordinate calls satisfy the one-dimensional accuracy interface at $S$, including the existence of an attained coordinate profile at every attained prefix optimum. Then the adaptive high-dimensional optimizer has all $d$ coordinate steps accurate with probability at least $1-t\beta'-d\beta$. -/)
  (proof := /-- Write $q=Q(S,\cdot)$. Since the probability of every event is at most one, \cref{def:can-be-approximated} implies $\beta'\ge0$. For $0\le k\le d$, let $P_k$ be the law obtained by folding the first $k$ calls in \cref{def:adaptive-high-dimensional-optimizer}, and let $G_k$ be the event that the current prefix has an attained greatest objective value and that every coordinate step of index less than $k$ is accurate in the sense of \cref{def:coordinate-step-accurate}. Put $c=\operatorname{ofReal}(1-\beta)$. We prove by induction that $c^k\le\mathbb P_{P_k}(G_k)$. At $k=0$, \cref{def:agrees-before,def:prefix-objective-values} identifies the prefix-value set with the range of $q$, so the assumed attained global maximum establishes $G_0$. Suppose the claim holds at $k<d$, and condition on a point $x\in G_k$. The attained prefix optimum and \cref{def:coordinate-calls-have-one-dimensional-accuracy} provide an attained coordinate profile $h$ and a conditional probability at least $c$ of choosing $z$ in the prescribed domain with $h(z)\ge M-2\alpha$. By \cref{lem:coordinate-profile-quasiconcave}, the quasiconcavity hypothesis required by that interface follows from the quasiconcavity of $q$. If $y$ is obtained from $x$ by updating coordinate $k$ to $z$, then $x$ and $y$ agree before $k$. Moreover, \cref{def:coordinate-profile-values,def:is-coordinate-profile} identifies the fiber-value set defining $h(z)$ with the prefix-value set of $y$ at stage $k+1$. Split according as $\alpha\ge0$ or $\alpha<0$. In the first case the reflexive $\alpha$-approximation, together with \cref{lem:approximation-transfers-to-coordinate-profiles}, gives $|h(w)-h(w)|\le\alpha$ for every $w$; the second case retains the complementary inequality. In either case, the call bound shows that $h(z)$ is an attained greatest value after the update and that the present step loses at most $2\alpha$, while all earlier step witnesses remain valid because their prefix-value sets are unchanged. Hence every accepted update lies in $G_{k+1}$. Expanding the outer measure of a PMF bind and summing the conditional lower bounds gives $c\mathbb P_{P_k}(G_k)\le\mathbb P_{P_{k+1}}(G_{k+1})$, proving the induction. If $d=0$, \cref{def:all-coordinate-steps-accurate} is vacuous and the result follows immediately. If $d>0$, the first-coordinate instance of the same call guarantee, together with the fact that event probabilities are at most one, gives $\beta\ge0$. Bernoulli's inequality yields $\operatorname{ofReal}(1-d\beta)\le c^d$; since $\beta'\ge0$, also $\operatorname{ofReal}(1-t\beta'-d\beta)\le\operatorname{ofReal}(1-d\beta)$. Finally, $G_d$ is contained in the simultaneous-accuracy event of \cref{def:all-coordinate-steps-accurate}, and $P_d$ is exactly the law of \cref{def:adaptive-high-dimensional-optimizer}, which proves the stated bound. -/)
  (title := /-- Simultaneous success of all coordinate calls -/)
  (latexEnv := "lemma")]
lemma simultaneous_coordinate_steps
    {Data : Type*} {n t d : ℕ}
    (Q : List Data → euclidean_point d → ℝ)
    (domains : adaptive_coordinate_domains d)
    (calls : coordinate_calls Data n d)
    (sampler : random_subset_sampler Data n) (S : Fin n → Data)
    (α β β' : ℝ) (X : ℕ)
    (happrox : can_be_approximated sampler Q S α β' (n / t))
    (hq : QuasiconcaveOn ℝ Set.univ (Q (List.ofFn S)))
    (hopt : ∃ optimum : ℝ, IsGreatest (Set.range (Q (List.ofFn S))) optimum)
    (hproper : proper_finite_domains Q domains)
    (hX : has_maximum_domain_cardinality domains X)
    (hcalls : coordinate_calls_have_one_dimensional_accuracy calls Q domains S α β) :
    ENNReal.ofReal (1 - (t : ℝ) * β' - (d : ℝ) * β) ≤
      event_probability (adaptive_high_dimensional_optimizer calls S)
        {x | all_coordinate_steps_accurate (Q (List.ofFn S)) α x} := by
  classical
  let q := Q (List.ofFn S)
  have bind_event_lower : ∀ (p : PMF (euclidean_point d))
      (f : euclidean_point d → PMF (euclidean_point d))
      (E F : Set (euclidean_point d)) (c : ENNReal),
      (∀ a ∈ E, c ≤ event_probability (f a) F) →
      c * event_probability p E ≤ event_probability (p.bind f) F := by
    intro p f E F c hconditional
    change c * p.toOuterMeasure E ≤ (p.bind f).toOuterMeasure F
    rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun a => ?_
    by_cases ha : a ∈ E
    · rw [Set.indicator_of_mem ha]
      have hc := hconditional a ha
      change c ≤ (f a).toOuterMeasure F at hc
      simpa [mul_comm] using
        mul_le_mul_left' hc (p a)
    · rw [Set.indicator_apply, if_neg ha, mul_zero]
      exact bot_le
  have prefix_values_eq : ∀ {k : ℕ} {x y : euclidean_point d},
      agrees_before k x y →
      prefix_objective_values q k x = prefix_objective_values q k y := by
    intro k x y hxy
    ext r
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, fun j hj => (hu j hj).trans (hxy j hj).symm, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, fun j hj => (hu j hj).trans (hxy j hj), rfl⟩
  let good : ℕ → euclidean_point d → Prop := fun k x =>
    (∃ optimum, IsGreatest (prefix_objective_values q k x) optimum) ∧
      ∀ i : Fin d, i.val < k → coordinate_step_accurate q α i x
  let law : ℕ → PMF (euclidean_point d) := fun k =>
    ((List.finRange d).take k).foldl
      (fun p i => PMF.bind p fun x =>
        PMF.map (fun z => Function.update x i z) (calls i x S))
      (PMF.pure 0)
  let c : ENNReal := ENNReal.ofReal (1 - β)
  have hstages : ∀ k : ℕ, k ≤ d →
      c ^ k ≤ event_probability (law k) {x | good k x} := by
    intro k hk
    induction k with
    | zero =>
        obtain ⟨optimum, hoptimum⟩ := hopt
        have hpref : IsGreatest (prefix_objective_values q 0 (0 : euclidean_point d))
            optimum := by
          constructor
          · rcases hoptimum.1 with ⟨x, rfl⟩
            exact ⟨x, by simp [agrees_before], rfl⟩
          · rintro r ⟨x, _, rfl⟩
            exact hoptimum.2 ⟨x, rfl⟩
        have hgoodzero : good 0 (0 : euclidean_point d) :=
          ⟨⟨optimum, hpref⟩, by omega⟩
        change 1 ≤ event_probability (PMF.pure 0) {x | good 0 x}
        simpa [event_probability, hgoodzero]
    | succ k ih =>
        have hklt : k < d := Nat.lt_of_succ_le hk
        let i : Fin d := ⟨k, hklt⟩
        have htake : (List.finRange d).take (k + 1) =
            (List.finRange d).take k ++ [i] := by
          have hindex : k < (List.finRange d).length := by simpa using hklt
          rw [List.take_succ_eq_append_getElem hindex]
          congr 2
          apply Fin.ext
          simp [i]
        have hlaw : law (k + 1) = PMF.bind (law k) (fun x =>
            PMF.map (fun z => Function.update x i z) (calls i x S)) := by
          simp [law, htake]
        rw [hlaw]
        calc
          c ^ (k + 1) = c * c ^ k := by rw [pow_succ]; ac_rfl
          _ ≤ c * event_probability (law k) {x | good k x} :=
            mul_le_mul_left' (ih (Nat.le_of_succ_le hk)) c
          _ ≤ event_probability
              (PMF.bind (law k) (fun x =>
                PMF.map (fun z => Function.update x i z) (calls i x S)))
              {x | good (k + 1) x} := by
            apply bind_event_lower
            intro x hx
            rcases hx with ⟨⟨optimum, hbefore⟩, hsteps⟩
            have hbefore_i :
                IsGreatest (prefix_objective_values q i.val x) optimum := by
              simpa [i] using hbefore
            obtain ⟨h, hh⟩ := (hcalls i x optimum hbefore_i).1
            have hhq : QuasiconcaveOn ℝ Set.univ h :=
              coordinate_profile_quasiconcave q i x h hq hh
            have hcall := (hcalls i x optimum hbefore_i).2 h hh hhq
            let accepted : Set ℝ :=
              {z | z ∈ domains i x ∧ optimum - 2 * α ≤ h z}
            have haccepted : c ≤ event_probability (calls i x S) accepted := by
              simpa [c, accepted] using hcall
            have hsubset : accepted ⊆
                (fun z => Function.update x i z) ⁻¹' {y | good (k + 1) y} := by
              intro z hz
              let y := Function.update x i z
              have hxy : agrees_before k x y := by
                intro j hj
                have hji : j ≠ i := by
                  intro hji
                  subst j
                  simp [i] at hj
                simp [y, hji]
              have hprofile : coordinate_profile_values q i x z =
                  prefix_objective_values q (k + 1) y := by
                ext r
                constructor
                · rintro ⟨u, hu, hui, rfl⟩
                  refine ⟨u, ?_, rfl⟩
                  intro j hj
                  by_cases hji : j = i
                  · subst j
                    simpa [y] using hui
                  · have hjne : j.val ≠ k := by
                      intro hjk
                      apply hji
                      apply Fin.ext
                      simpa [i] using hjk
                    have hjk : j.val < k := by omega
                    rw [hu j hjk]
                    simp [y, hji]
                · rintro ⟨u, hu, rfl⟩
                  refine ⟨u, ?_, ?_, rfl⟩
                  · intro j hj
                    have hji : j ≠ i := by
                      intro hji
                      subst j
                      simp [i] at hj
                    have hjk : j.val < k := by simpa [i] using hj
                    have huj := hu j (Nat.lt.step hjk)
                    simpa [y, hji] using huj
                  · have hui := hu i (by simp [i])
                    simpa [y] using hui
              have hafter : IsGreatest
                  (prefix_objective_values q (k + 1) y) (h z) := by
                rw [← hprofile]
                exact hh z
              have hbefore_y : IsGreatest
                  (prefix_objective_values q k y) optimum := by
                rw [← prefix_values_eq hxy]
                exact hbefore
              have htransfer_or : (∀ w, |h w - h w| ≤ α) ∨ α < 0 := by
                by_cases hα : 0 ≤ α
                · left
                  apply approximation_transfers_to_coordinate_profiles
                    Q (List.ofFn S) (List.ofFn S) α i x h h
                  · intro u
                    simpa using hα
                  · exact hh
                  · exact hh
                · right
                  linarith
              have hcurrent : coordinate_step_accurate q α i y := by
                rcases htransfer_or with htransfer | hα
                · refine ⟨optimum, h z, ?_, hafter, hz.2⟩
                  simpa [i] using hbefore_y
                · refine ⟨optimum, h z, ?_, hafter, hz.2⟩
                  simpa [i] using hbefore_y
              refine ⟨⟨h z, hafter⟩, ?_⟩
              intro j hj
              by_cases hjk : j.val < k
              · rcases hsteps j hjk with ⟨before, after, hjbefore, hjafter, hjbound⟩
                have hxy_before : agrees_before j.val x y := by
                  intro l hl
                  exact hxy l (by omega)
                have hxy_after : agrees_before (j.val + 1) x y := by
                  intro l hl
                  exact hxy l (by omega)
                refine ⟨before, after, ?_, ?_, hjbound⟩
                · rw [← prefix_values_eq hxy_before]
                  exact hjbefore
                · rw [← prefix_values_eq hxy_after]
                  exact hjafter
              · have hjval : j.val = k := by omega
                have hji : j = i := Fin.ext (by simpa [i] using hjval)
                simpa [hji] using hcurrent
            calc
              c ≤ event_probability (calls i x S) accepted := haccepted
              _ ≤ event_probability (calls i x S)
                  ((fun z => Function.update x i z) ⁻¹' {y | good (k + 1) y}) := by
                exact (calls i x S).toOuterMeasure_mono fun z hz => hsubset hz.1
              _ = event_probability
                  (PMF.map (fun z => Function.update x i z) (calls i x S))
                  {y | good (k + 1) y} := by
                simp [event_probability]
  have hβ' : 0 ≤ β' := by
    have hprob_le : event_probability (sampler S (n / t))
        {S' | S'.Subperm (List.ofFn S) ∧ n / t ≤ S'.length ∧
          alpha_approximation Q (List.ofFn S) S' α} ≤ 1 := by
      calc
        event_probability (sampler S (n / t))
            {S' | S'.Subperm (List.ofFn S) ∧ n / t ≤ S'.length ∧
              alpha_approximation Q (List.ofFn S) S' α} ≤
            (sampler S (n / t)).toOuterMeasure Set.univ := by
          exact (sampler S (n / t)).toOuterMeasure.mono (Set.subset_univ _)
        _ = 1 := by rw [PMF.toOuterMeasure_apply]; simp
    have hle : ENNReal.ofReal (1 - β') ≤ 1 := happrox.trans hprob_le
    rw [ENNReal.ofReal_le_one] at hle
    linarith
  by_cases hd : d = 0
  · subst d
    have hevent : {x : euclidean_point 0 |
        all_coordinate_steps_accurate (Q (List.ofFn S)) α x} = Set.univ := by
      ext x
      simp [all_coordinate_steps_accurate]
    rw [hevent]
    calc
      ENNReal.ofReal (1 - (t : ℝ) * β' - ((0 : ℕ) : ℝ) * β) ≤ 1 := by
        rw [ENNReal.ofReal_le_one]
        norm_num
        exact mul_nonneg (Nat.cast_nonneg t) hβ'
      _ = event_probability (adaptive_high_dimensional_optimizer calls S) Set.univ := by
        rw [event_probability, PMF.toOuterMeasure_apply]
        simpa only [Set.indicator_univ] using
          (PMF.tsum_coe (adaptive_high_dimensional_optimizer calls S)).symm
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hβ : 0 ≤ β := by
    obtain ⟨optimum, hoptimum⟩ := hopt
    let i : Fin d := ⟨0, hdpos⟩
    have hbefore : IsGreatest (prefix_objective_values q i.val (0 : euclidean_point d))
        optimum := by
      constructor
      · rcases hoptimum.1 with ⟨x, rfl⟩
        exact ⟨x, by simp [i, agrees_before], rfl⟩
      · rintro r ⟨x, _, rfl⟩
        exact hoptimum.2 ⟨x, rfl⟩
    obtain ⟨h, hh⟩ := (hcalls i 0 optimum hbefore).1
    have hcall := (hcalls i 0 optimum hbefore).2 h hh
      (coordinate_profile_quasiconcave q i 0 h hq hh)
    have hprob_le : event_probability (calls i 0 S)
        {z | z ∈ domains i 0 ∧ optimum - 2 * α ≤ h z} ≤ 1 := by
      calc
        event_probability (calls i 0 S)
            {z | z ∈ domains i 0 ∧ optimum - 2 * α ≤ h z} ≤
            (calls i 0 S).toOuterMeasure Set.univ := by
          exact (calls i 0 S).toOuterMeasure.mono (Set.subset_univ _)
        _ = 1 := by rw [PMF.toOuterMeasure_apply]; simp
    have hle : ENNReal.ofReal (1 - β) ≤ 1 := hcall.trans hprob_le
    rw [ENNReal.ofReal_le_one] at hle
    linarith
  have hpow : ENNReal.ofReal (1 - (d : ℝ) * β) ≤ c ^ d := by
    let a : ℝ := max 0 (1 - β)
    have ha : -1 ≤ a := by simp [a]
    have hbern : 1 + (d : ℝ) * (a - 1) ≤ a ^ d :=
      one_add_mul_sub_le_pow ha d
    have hleft : 1 - (d : ℝ) * β ≤ 1 + (d : ℝ) * (a - 1) := by
      dsimp [a]
      nlinarith [le_max_right 0 (1 - β)]
    have hreal : 1 - (d : ℝ) * β ≤ a ^ d := hleft.trans hbern
    calc
      ENNReal.ofReal (1 - (d : ℝ) * β) ≤ ENNReal.ofReal (a ^ d) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = c ^ d := by simp [a, c, ENNReal.ofReal_pow]
  have htarget : ENNReal.ofReal (1 - (t : ℝ) * β' - (d : ℝ) * β) ≤ c ^ d := by
    refine (ENNReal.ofReal_le_ofReal ?_).trans hpow
    nlinarith [mul_nonneg (Nat.cast_nonneg t) hβ']
  have hfull : c ^ d ≤ event_probability (law d) {x | good d x} :=
    hstages d le_rfl
  have hgood : event_probability (law d) {x | good d x} ≤
      event_probability (law d) {x | all_coordinate_steps_accurate q α x} := by
    exact (law d).toOuterMeasure_mono fun x hx i => hx.1.2 i i.isLt
  calc
    ENNReal.ofReal (1 - (t : ℝ) * β' - (d : ℝ) * β) ≤ c ^ d := htarget
    _ ≤ event_probability (law d) {x | good d x} := hfull
    _ ≤ event_probability (law d) {x | all_coordinate_steps_accurate q α x} := hgood
    _ = event_probability (adaptive_high_dimensional_optimizer calls S)
        {x | all_coordinate_steps_accurate (Q (List.ofFn S)) α x} := by
      dsimp [law, q, adaptive_high_dimensional_optimizer]
      rw [show (List.finRange d).take d = List.finRange d by
        simpa using (List.take_length (l := List.finRange d))]

@[blueprint "lem:coordinate-losses-telescope"
  (statement := /-- Let $d\in\mathbb N$, let $q\colon\mathbb R^d\to\mathbb R$, let $\alpha,M\in\mathbb R$, and let $x\in\mathbb R^d$. Suppose that $M$ is the greatest element of the range of $q$. For each $i\in\{0,\ldots,d-1\}$, suppose that the objective values attained by completions agreeing with $x$ on the first $i$ coordinates and on the first $i+1$ coordinates have greatest elements $M_i$ and $M_{i+1}$ satisfying $M_i-2\alpha\le M_{i+1}$. Then $M-2\alpha d\le q(x)$. -/)
  (proof := /-- By \cref{def:prefix-objective-values,def:agrees-before}, the prefix at stage $0$ imposes no restriction, so its greatest value is $M$. For every $i<d$, \cref{def:all-coordinate-steps-accurate,def:coordinate-step-accurate} supplies greatest values before and after coordinate $i$ whose difference is at most $2\alpha$. Greatest elements of the same prefix-value set are equal; hence induction on $k\le d$ shows that the greatest value at stage $k$ is at least $M-2\alpha k$. At stage $d$, \cref{def:prefix-objective-values,def:agrees-before} forces every completion to equal $x$, so this greatest value is $q(x)$. -/)
  (title := /-- Telescoping the coordinate losses -/)
  (latexEnv := "lemma")]
lemma coordinate_losses_telescope {d : ℕ}
    (q : euclidean_point d → ℝ) (α optimum : ℝ)
    (x : euclidean_point d)
    (hopt : IsGreatest (Set.range q) optimum)
    (hsteps : all_coordinate_steps_accurate q α x) :
    optimum - 2 * α * (d : ℝ) ≤ q x := by
  have hprefix : ∀ k : ℕ, k ≤ d →
      ∃ value : ℝ, IsGreatest (prefix_objective_values q k x) value ∧
        optimum - 2 * α * (k : ℝ) ≤ value := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨optimum, ?_, ?_⟩
        · constructor
          · obtain ⟨z, hz⟩ := hopt.1
            rw [prefix_objective_values]
            exact ⟨z, by simp [agrees_before], hz.symm⟩
          · intro r hr
            apply hopt.2
            rw [prefix_objective_values] at hr
            obtain ⟨z, _, rfl⟩ := hr
            exact ⟨z, rfl⟩
        · norm_num
    | succ k ih =>
        intro hk
        have hklt : k < d := Nat.lt_of_succ_le hk
        let i : Fin d := ⟨k, hklt⟩
        obtain ⟨before, after, hbefore, hafter, hstep⟩ := hsteps i
        obtain ⟨value, hvalue, hbound⟩ := ih (Nat.le_of_succ_le hk)
        have hvalue_eq : value = before :=
          le_antisymm (hbefore.2 hvalue.1) (hvalue.2 hbefore.1)
        refine ⟨after, ?_, ?_⟩
        · simpa [i] using hafter
        · rw [hvalue_eq] at hbound
          norm_num [Nat.cast_succ] at hbound ⊢
          linarith
  obtain ⟨value, hvalue, hbound⟩ := hprefix d le_rfl
  obtain ⟨y, hy, hvalue_eq⟩ := hvalue.1
  have hyx : y = x := funext fun j => hy j j.isLt
  calc
    optimum - 2 * α * (d : ℝ) ≤ value := hbound
    _ = q y := hvalue_eq
    _ = q x := congrArg q hyx

@[blueprint "lem:high-dimensional-lower-bound-probability"
  (statement := /-- Let $\mathcal X$ be a type, let $n,t,d\in\mathbb N$, let $Q\colon\mathcal X^*\times\mathbb R^d\to\mathbb R$, and let an adaptive finite-coordinate-domain family, a family of coordinate calls, a random-subset sampler, and $S\in\mathcal X^n$ be given. Fix $\alpha,\beta,\beta',M\in\mathbb R$ and $X\in\mathbb N$. Suppose that $(S,Q)$ can be $(\alpha,\beta',n/t)$-approximated with respect to the sampler, that $Q(S,\cdot)$ is quasiconcave, that the coordinate domains are proper for $Q$ and have maximum cardinality $X$, that the coordinate calls satisfy the one-dimensional accuracy interface with parameters $\alpha$ and $\beta$, and that $M$ is the greatest element of the range of $Q(S,\cdot)$. Then the adaptive high-dimensional optimizer outputs $\widehat x$ satisfying $M-2\alpha d\le Q(S,\widehat x)$ with probability at least $1-t\beta'-d\beta$. -/)
  (proof := /-- The hypothesis that $M$ is greatest in the range of $Q(S,\cdot)$ provides the attained-global-maximum witness required by \cref{lem:simultaneous-coordinate-steps}; the strengthened call-accuracy interface supplies the attained profile needed at each subsequent prefix. Hence all coordinate steps are accurate outside an event of probability at most $t\beta'+d\beta$. On the simultaneous-success event, \cref{lem:coordinate-losses-telescope} gives the lower bound $Q(S,x)\ge M-2\alpha d$. Monotonicity of the event probability then yields the stated estimate. -/)
  (title := /-- Probabilistic one-sided accuracy bound -/)
  (latexEnv := "lemma")]
lemma high_dimensional_lower_bound_probability
    {Data : Type*} {n t d : ℕ}
    (Q : List Data → euclidean_point d → ℝ)
    (domains : adaptive_coordinate_domains d)
    (calls : coordinate_calls Data n d)
    (sampler : random_subset_sampler Data n) (S : Fin n → Data)
    (α β β' optimum : ℝ) (X : ℕ)
    (happrox : can_be_approximated sampler Q S α β' (n / t))
    (hq : QuasiconcaveOn ℝ Set.univ (Q (List.ofFn S)))
    (hproper : proper_finite_domains Q domains)
    (hX : has_maximum_domain_cardinality domains X)
    (hcalls : coordinate_calls_have_one_dimensional_accuracy calls Q domains S α β)
    (hopt : IsGreatest (Set.range (Q (List.ofFn S))) optimum) :
    ENNReal.ofReal (1 - (t : ℝ) * β' - (d : ℝ) * β) ≤
      event_probability (adaptive_high_dimensional_optimizer calls S)
        {x | optimum - 2 * α * (d : ℝ) ≤ Q (List.ofFn S) x} := by
  apply le_trans (simultaneous_coordinate_steps Q domains calls sampler S α β β' X
    happrox hq ⟨optimum, hopt⟩ hproper hX hcalls)
  exact (adaptive_high_dimensional_optimizer calls S).toOuterMeasure_mono fun x hx =>
    coordinate_losses_telescope (Q (List.ofFn S)) α optimum x hopt hx.1

@[blueprint "lem:lower-bound-event-subset-absolute-error"
  (statement := /-- Let $d\in\mathbb N$, let $q\colon\mathbb R^d\to\mathbb R$, and let $M,e\in\mathbb R$. If $M$ is an attained global maximum of $q$ and $e\ge0$, then every $x\in\mathbb R^d$ satisfying $q(x)\ge M-e$ also satisfies $|q(x)-M|\le e$. -/)
  (proof := /-- Since $M$ is greatest in the range of $q$, one has $q(x)\le M$ for every $x$. Together with $M-e\le q(x)$, this gives $-e\le q(x)-M\le0\le e$. The characterization of absolute value by two inequalities yields $|q(x)-M|\le e$. -/)
  (title := /-- From a one-sided optimum bound to absolute error -/)
  (latexEnv := "lemma")]
lemma lower_bound_event_subset_absolute_error {d : ℕ}
    (q : euclidean_point d → ℝ) (optimum error : ℝ)
    (hopt : IsGreatest (Set.range q) optimum) (herror : 0 ≤ error) :
    {x | optimum - error ≤ q x} ⊆ {x | |q x - optimum| ≤ error} := by
  intro x hx
  change optimum - error ≤ q x at hx
  change |q x - optimum| ≤ error
  rw [abs_le]
  constructor <;> linarith [hopt.2 ⟨x, rfl⟩]

@[blueprint "thm:ip-concave-high-dim-accuracy"
  (statement := /-- Let \(\mathcal X\) be a type, let \(n,t,d,X\in\mathbb N\), let \(Q:\mathcal X^*\times\mathbb R^d\to\mathbb R\), let \(\widetilde{\mathcal X}_i\subset\mathbb R\) be a fixed finite domain for every \(i\in[d]\), and let \(S\in\mathcal X^n\). Fix functions \(n_{IP}:\mathbb N\times\mathbb R^3\to\mathbb N\) and \(L:\mathbb N\to\mathbb R\), parameters \(\alpha,\beta,\beta',\varepsilon,\delta,M\in\mathbb R\), and a one-dimensional optimizer witness for these data and parameters. Suppose that \(\varepsilon>0\), that \(\delta,\alpha,\beta\in(0,1)\), that \(0<t\le n\), that \(t=n_{IP}(X,\beta,\varepsilon,\delta)\), and that \(n_{IP}(\cdot,\beta,\varepsilon,\delta)\in\widetilde O(L)\). Suppose also that the domains have maximum cardinality \(X\), that \(Q(S,\cdot)\) is quasiconcave on \(\mathbb R^d\), that \((S,Q)\) can be \((\alpha,\beta',\lfloor n/t\rfloor)\)-approximated under the canonical random-subset law, that the domains are proper for \(Q\), and that \(M\) is the greatest element of the range of \(Q(S,\cdot)\). Then the witnessed high-dimensional optimizer outputs \(\widehat x\) such that \(\lvert Q(S,\widehat x)-M\rvert\le 2\alpha d\) with probability at least \(1-t\beta'-d\beta\). -/)
  (proof := /-- Regard each fixed domain \(\widetilde{\mathcal X}_i\) as a domain independent of the preceding prefix. The witness in \cref{def:ip-concave-high-dimensional-optimizer} ties the fixed coordinate mechanisms to the particular function \(n_{IP}\) occurring in the sample-complexity hypotheses. The strict inequality \(0<t\) makes \(\lfloor n/t\rfloor\) the intended positive-divisor block size, and the approximation hypothesis uses \cref{def:canonical-random-subset-sampler}. Hence \cref{lem:ip-concave-coordinate-calls-accurate} gives the non-vacuous one-dimensional accuracy interface for this constant-in-prefix family, including the attained-profile witnesses needed along every successful adaptive trajectory. Substitution into \cref{lem:high-dimensional-lower-bound-probability} yields the one-sided event bound. Since \(\alpha>0\) and \(d\ge0\), the error \(2\alpha d\) is nonnegative. Apply \cref{lem:lower-bound-event-subset-absolute-error} with the attained global maximum \(M\); monotonicity of \cref{def:event-probability} transfers the same lower probability bound to the absolute-error event. -/)
  (title := /-- Accuracy of the high-dimensional quasiconcave optimizer -/)
  (latexEnv := "theorem")]
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
        {x | |Q (List.ofFn S) x - optimum| ≤ 2 * α * (d : ℝ)} := by
  apply le_trans
    (high_dimensional_lower_bound_probability Q (fun i _ => domains i)
      (ip_concave_coordinate_calls (n := n) (t := t)
        Q (fun i _ => domains i) nIP logStar α β ε δ optimizer)
      (canonical_random_subset_sampler Data n) S α β β' optimum X
      happrox hq hproper hX
      (ip_concave_coordinate_calls_accurate Q (fun i _ => domains i) S
        nIP logStar α β β' ε δ X optimizer
        hε hδ hα hβ hnt htpos ht hscale hX hq happrox hproper)
      hopt)
  exact
    (ip_concave_high_dimensional_optimizer
      (n := n) (t := t)
      Q domains nIP logStar α β ε δ optimizer S).toOuterMeasure_mono
      fun x hx =>
        lower_bound_event_subset_absolute_error
          (Q (List.ofFn S)) optimum (2 * α * (d : ℝ)) hopt
          (mul_nonneg (mul_nonneg (by norm_num) hα.1.le) (Nat.cast_nonneg d)) hx.1

import Architect
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Sym
import Mathlib.InformationTheory.Hamming

set_option linter.all false
set_option maxHeartbeats 500000

universe u

@[blueprint "def:rb-clustering"
  (statement := /-- A clustering is represented by a Boolean equivalence relation; \`sameBlock x y\`
  records whether the points \(x\) and \(y\) belong to the same cluster. -/)
  (title := /-- Red--blue clustering -/)
  (latexEnv := "definition")]
structure rb_clustering (α : Type u) where
  sameBlock : α → α → Bool
  sameBlock_refl : ∀ x, sameBlock x x = true
  sameBlock_symm : ∀ x y, sameBlock x y = sameBlock y x
  sameBlock_trans : ∀ {x y z}, sameBlock x y = true →
    sameBlock y z = true → sameBlock x z = true

@[blueprint "def:same-block-on-pair"
  (statement := /-- For a clustering \(C\), the same-block indicator of an unordered pair
  \(\{x,y\}\) is true precisely when \(x\) and \(y\) lie in the same cluster of \(C\). -/)
  (title := /-- Same-block indicator on unordered pairs -/)
  (latexEnv := "definition")]
def same_block_on_pair {α : Type u} (C : rb_clustering α) : Sym2 α → Bool :=
  Sym2.lift ⟨C.sameBlock, C.sameBlock_symm⟩

@[blueprint "def:disagreement-distance"
  (statement := /-- The distance between two clusterings of a finite point set is the number of
  unordered pairs co-clustered by exactly one of them.  It is the Hamming distance between the
  indicators of \cref{def:same-block-on-pair}. -/)
  (title := /-- Pairwise-disagreement distance -/)
  (latexEnv := "definition")]
def disagreement_distance {α : Type u} [Fintype α]
    (C D : rb_clustering α) : ℕ :=
  hammingDist (same_block_on_pair C) (same_block_on_pair D)

@[blueprint "def:colored-cluster-count"
  (statement := /-- Given a coloring \(\chi\), a clustering \(C\), a point \(x\), and a color \(b\),
  this is the number of points of color \(b\) in the cluster containing \(x\). -/)
  (title := /-- Number of points of one color in a cluster -/)
  (latexEnv := "definition")]
def colored_cluster_count {α : Type u} [Fintype α] (color : α → Bool)
    (C : rb_clustering α) (x : α) (b : Bool) : ℕ :=
  (Finset.univ.filter fun y => C.sameBlock x y = true ∧ color y = b).card

@[blueprint "def:population-ratio"
  (statement := /-- A finite population has blue-to-red ratio \(p/q\) when it is nonempty and
  \(q\) times its number of blue points equals \(p\) times its number of red points.  True
  denotes blue and false red. -/)
  (title := /-- Global blue-to-red population ratio -/)
  (latexEnv := "definition")]
def population_ratio {α : Type u} [Fintype α] (color : α → Bool)
    (p q : ℕ) : Prop :=
  0 < Fintype.card α ∧
    q * (Finset.univ.filter fun x => color x = true).card =
      p * (Finset.univ.filter fun x => color x = false).card

@[blueprint "def:ratio-fair"
  (statement := /-- A clustering is \(p/q\)-fair when every cluster has blue-to-red ratio \(p/q\);
  for every representative \(x\), \(q\) times its blue count equals \(p\) times its red count. -/)
  (title := /-- Exact ratio fairness -/)
  (latexEnv := "definition")]
def ratio_fair {α : Type u} [Fintype α] (color : α → Bool)
    (p q : ℕ) (C : rb_clustering α) : Prop :=
  ∀ x, q * colored_cluster_count color C x true =
    p * colored_cluster_count color C x false

@[blueprint "def:consensus-objective"
  (statement := /-- For inputs \(D_1,\ldots,D_m\), exponent \(\ell>0\), and candidate \(F\), set
  \[
    \operatorname{obj}_{\ell}(F)=
    \left(\sum_{i=1}^{m}\operatorname{dist}(D_i,F)^{\ell}\right)^{1/\ell}.
  \]
  The distances are coerced to nonnegative real numbers. -/)
  (title := /-- Generalized-mean consensus objective -/)
  (latexEnv := "definition")]
noncomputable def consensus_objective {α : Type u} [Fintype α] {m : ℕ}
    (ell : ℝ) (inputs : Fin m → rb_clustering α) (F : rb_clustering α) : ℝ :=
  Real.rpow
    (∑ i, Real.rpow (disagreement_distance (inputs i) F : ℝ) ell)
    (1 / ell)

@[blueprint "def:fair-consensus-algorithm"
  (statement := /-- A fair-consensus algorithm is a uniform output map on every finite colored
  point type and every finite input family, together with a natural-number cost for each run. -/)
  (title := /-- Fair-consensus algorithm with a cost model -/)
  (latexEnv := "definition")]
structure fair_consensus_algorithm where
  run : {α : Type u} → [Fintype α] → (color : α → Bool) → (m : ℕ) →
    (Fin m → rb_clustering α) → rb_clustering α
  cost : {α : Type u} → [Fintype α] → (color : α → Bool) → (m : ℕ) →
    (Fin m → rb_clustering α) → ℕ

@[blueprint "def:factor-approximate-consensus"
  (statement := /-- An algorithm is a \(\gamma\)-approximation for \(\ell\)-mean fair consensus at
  ratio \(p/q\) if, for every finite red--blue population having ratio \(p/q\) and at least as
  many blue points as red points, it returns a \(p/q\)-fair clustering whose objective is at most
  \(\gamma\) times that of every \(p/q\)-fair comparator. -/)
  (title := /-- Approximation guarantee for fair consensus -/)
  (latexEnv := "definition")]
def factor_approximate_consensus (A : fair_consensus_algorithm.{u})
    (ell factor : ℝ) (p q : ℕ) : Prop :=
  ∀ {α : Type u} [Fintype α] (color : α → Bool) (m : ℕ)
    (inputs : Fin m → rb_clustering α),
    population_ratio color p q →
      (Finset.univ.filter fun x => color x = false).card ≤
        (Finset.univ.filter fun x => color x = true).card →
      ratio_fair color p q (A.run color m inputs) ∧
      ∀ F : rb_clustering α, ratio_fair color p q F →
        consensus_objective ell inputs (A.run color m inputs) ≤
          factor * consensus_objective ell inputs F

@[blueprint "def:quadratic-consensus-time"
  (statement := /-- An algorithm has running time \(O(m^2n^2)\) when one constant \(K\), independent
  of every input, bounds its reported cost by \(K m^2n^2\), where \(n\) is the point count. -/)
  (title := /-- Uniform quadratic consensus running time -/)
  (latexEnv := "definition")]
def quadratic_consensus_time (A : fair_consensus_algorithm.{u}) : Prop :=
  ∃ K : ℕ, ∀ {α : Type u} [Fintype α] (color : α → Bool) (m : ℕ)
    (inputs : Fin m → rb_clustering α),
    A.cost color m inputs ≤ K * m ^ 2 * Fintype.card α ^ 2

@[blueprint "def:has-fair-consensus-algorithm"
  (statement := /-- This proposition packages the existence of a \(\gamma\)-approximate
  \(\ell\)-mean \(p/q\)-fair consensus algorithm on populations with at least as many blue
  points as red points, together with the \(O(m^2n^2)\) guarantee from
  \cref{def:factor-approximate-consensus,def:quadratic-consensus-time}. -/)
  (title := /-- Existence of a fast approximate fair-consensus algorithm -/)
  (latexEnv := "definition")]
def has_fair_consensus_algorithm (ell factor : ℝ) (p q : ℕ) : Prop :=
  ∃ A : fair_consensus_algorithm.{u},
    factor_approximate_consensus A ell factor p q ∧ quadratic_consensus_time A

@[blueprint "def:closest-fair-algorithm"
  (statement := /-- A closest-fair algorithm maps one clustering of any finite colored point set
  to a clustering and assigns a natural-number cost to the run. -/)
  (title := /-- Closest-fair clustering algorithm with a cost model -/)
  (latexEnv := "definition")]
structure closest_fair_algorithm where
  run : {α : Type u} → [Fintype α] → (color : α → Bool) →
    rb_clustering α → rb_clustering α
  cost : {α : Type u} → [Fintype α] → (color : α → Bool) →
    rb_clustering α → ℕ

@[blueprint "def:factor-close-output"
  (statement := /-- A closest-fair algorithm is \(\alpha\)-close at ratio \(p/q\) if it returns a
  fair clustering for every finite population having ratio \(p/q\) and at least as many blue
  points as red points, and if its distance from the input is at most \(\alpha\) times the
  distance from the input to every fair comparator. -/)
  (title := /-- Approximation guarantee for closest fair clustering -/)
  (latexEnv := "definition")]
def factor_close_output (A : closest_fair_algorithm.{u}) (factor : ℝ)
    (p q : ℕ) : Prop :=
  ∀ {α : Type u} [Fintype α] (color : α → Bool) (C : rb_clustering α),
    population_ratio color p q →
      (Finset.univ.filter fun x => color x = false).card ≤
        (Finset.univ.filter fun x => color x = true).card →
      ratio_fair color p q (A.run color C) ∧
      ∀ F : rb_clustering α, ratio_fair color p q F →
        (disagreement_distance C (A.run color C) : ℝ) ≤
          factor * (disagreement_distance C F : ℝ)

@[blueprint "def:quadratic-closest-time"
  (statement := /-- A closest-fair algorithm has running time \(O(n^2)\) if one uniform constant
  \(K\) bounds the cost of every run by \(K n^2\). -/)
  (title := /-- Uniform quadratic closest-fair running time -/)
  (latexEnv := "definition")]
def quadratic_closest_time (A : closest_fair_algorithm.{u}) : Prop :=
  ∃ K : ℕ, ∀ {α : Type u} [Fintype α] (color : α → Bool)
    (C : rb_clustering α),
    A.cost color C ≤ K * Fintype.card α ^ 2

@[blueprint "def:has-closest-fair-algorithm"
  (statement := /-- This proposition packages the existence of an \(\alpha\)-close \(p/q\)-fair
  clustering algorithm on populations with at least as many blue points as red points, with
  running time \(O(n^2)\). -/)
  (title := /-- Existence of a fast closest-fair algorithm -/)
  (latexEnv := "definition")]
def has_closest_fair_algorithm (factor : ℝ) (p q : ℕ) : Prop :=
  ∃ A : closest_fair_algorithm.{u},
    factor_close_output A factor p q ∧ quadratic_closest_time A

@[blueprint "lem:disagreement-distance-symmetric"
  (statement := /-- For clusterings \(C,D\) of the same finite point set,
  \(\operatorname{dist}(C,D)=\operatorname{dist}(D,C)\). -/)
  (proof := /-- By \cref{def:disagreement-distance}, the two sides are Hamming distances between
  the same Boolean functions in reverse order.  Symmetry of Hamming distance gives the claim. -/)
  (title := /-- Symmetry of pairwise-disagreement distance -/)
  (latexEnv := "lemma")]
lemma disagreement_distance_symmetric {α : Type u} [Fintype α]
    (C D : rb_clustering α) :
    disagreement_distance C D = disagreement_distance D C := by
  simpa only [disagreement_distance] using
    hammingDist_comm (same_block_on_pair C) (same_block_on_pair D)

@[blueprint "lem:disagreement-distance-triangle"
  (statement := /-- For clusterings \(C,D,E\) of the same finite point set,
  \[
    \operatorname{dist}(C,E)\leq\operatorname{dist}(C,D)+\operatorname{dist}(D,E).
  \] -/)
  (proof := /-- Under \cref{def:disagreement-distance}, these are Hamming distances between Boolean
  functions on the common finite type of unordered point pairs.  The Hamming triangle inequality
  proves the assertion. -/)
  (title := /-- Triangle inequality for pairwise-disagreement distance -/)
  (latexEnv := "lemma")]
lemma disagreement_distance_triangle {α : Type u} [Fintype α]
    (C D E : rb_clustering α) :
    disagreement_distance C E ≤
      disagreement_distance C D + disagreement_distance D E := by
  exact hammingDist_triangle (same_block_on_pair C) (same_block_on_pair D)
    (same_block_on_pair E)

@[blueprint "lem:consensus-objective-pointwise-bound"
  (statement := /-- Let \(X\) be a finite type, let \(m\in\mathbb{N}\), and let
  \((D_i)_{i\in\operatorname{Fin}(m)}\) be a family of clusterings of \(X\).  For clusterings
  \(F,G\) of \(X\) and real numbers \(\ell,c\) satisfying \(1\leq\ell\) and \(0\leq c\), if
  \(\operatorname{dist}(D_i,F)\leq c\operatorname{dist}(D_i,G)\) for every
  \(i\in\operatorname{Fin}(m)\), then
  \(\operatorname{obj}_{\ell}(F)\leq c\operatorname{obj}_{\ell}(G)\). -/)
  (proof := /-- Unfold \cref{def:consensus-objective}.  Since \(1\leq\ell\), both \(\ell\) and
  \(1/\ell\) are nonnegative.  Monotonicity of the \(\ell\)-th real power carries each assumed
  pointwise inequality through the finite sum, and monotonicity of the \(1/\ell\)-th real power
  carries the resulting inequality to the objectives.  For every nonnegative \(x\),
  \((cx)^{\ell}=c^{\ell}x^{\ell}\), so the upper sum is \(c^{\ell}\) times the corresponding sum
  for \(G\).  Multiplicativity of real powers and \(\ell(1/\ell)=1\) then identify the extracted
  factor \((c^{\ell})^{1/\ell}\) with \(c\), which proves the claimed bound. -/)
  (title := /-- Pointwise domination of the consensus objective -/)
  (latexEnv := "lemma")]
lemma consensus_objective_pointwise_bound {α : Type u} [Fintype α] {m : ℕ}
    (ell c : ℝ) (hEll : 1 ≤ ell) (hc : 0 ≤ c)
    (inputs : Fin m → rb_clustering α) (F G : rb_clustering α)
    (hpoint : ∀ i,
      (disagreement_distance (inputs i) F : ℝ) ≤
        c * (disagreement_distance (inputs i) G : ℝ)) :
    consensus_objective ell inputs F ≤
      c * consensus_objective ell inputs G := by
  have hEllPos : 0 < ell := lt_of_lt_of_le zero_lt_one hEll
  have hEllNonneg : 0 ≤ ell := hEllPos.le
  have hInvNonneg : 0 ≤ 1 / ell := by positivity
  unfold consensus_objective
  calc
    Real.rpow (∑ i, Real.rpow (disagreement_distance (inputs i) F : ℝ) ell) (1 / ell) ≤
        Real.rpow (∑ i, Real.rpow
          (c * (disagreement_distance (inputs i) G : ℝ)) ell) (1 / ell) := by
      apply Real.rpow_le_rpow
        (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (by positivity) ell) _ hInvNonneg
      exact Finset.sum_le_sum fun i _ =>
        Real.rpow_le_rpow (by positivity) (hpoint i) hEllNonneg
    _ = Real.rpow (∑ i, Real.rpow c ell *
          Real.rpow (disagreement_distance (inputs i) G : ℝ) ell) (1 / ell) := by
      congr 2 with i
      exact Real.mul_rpow hc (by positivity)
    _ = Real.rpow (Real.rpow c ell *
          ∑ i, Real.rpow (disagreement_distance (inputs i) G : ℝ) ell) (1 / ell) := by
      rw [Finset.mul_sum]
    _ = Real.rpow (Real.rpow c ell) (1 / ell) *
          Real.rpow (∑ i, Real.rpow
            (disagreement_distance (inputs i) G : ℝ) ell) (1 / ell) := by
      exact Real.mul_rpow (Real.rpow_nonneg hc ell)
        (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (by positivity) ell)
    _ = c * Real.rpow (∑ i, Real.rpow
          (disagreement_distance (inputs i) G : ℝ) ell) (1 / ell) := by
      have hprod : ell * (1 / ell) = 1 := by field_simp
      have hcroot : Real.rpow (Real.rpow c ell) (1 / ell) = c := by
        calc
          Real.rpow (Real.rpow c ell) (1 / ell) =
              Real.rpow c (ell * (1 / ell)) := (Real.rpow_mul hc ell (1 / ell)).symm
          _ = c := by
            rw [hprod]
            exact Real.rpow_one c
      rw [hcroot]

@[blueprint "lem:selected-candidate-objective-bound"
  (statement := /-- Let \(X\) be a finite type, let \(m\in\mathbb{N}\), and let
  \((D_i)_{i\in\operatorname{Fin}(m)}\) be a family of clusterings of \(X\).  Let
  \(\ell,\alpha\in\mathbb{R}\) satisfy \(\ell,\alpha\geq1\), let \(F^\ast\) and
  \(F_{i^\ast}\) be clusterings of \(X\), and let \(i^\ast\in\operatorname{Fin}(m)\).  Suppose
  that \(\operatorname{dist}(D_{i^\ast},F^\ast)\leq
  \operatorname{dist}(D_j,F^\ast)\) for every \(j\in\operatorname{Fin}(m)\), and that
  \(\operatorname{dist}(D_{i^\ast},F_{i^\ast})\leq
  \alpha\operatorname{dist}(D_{i^\ast},F^\ast)\).  Then
  \(\operatorname{obj}_{\ell}(F_{i^\ast})\leq
  (2+\alpha)\operatorname{obj}_{\ell}(F^\ast)\). -/)
  (proof := /-- Fix \(j\in\operatorname{Fin}(m)\).  Applying
  \cref{lem:disagreement-distance-triangle} first through \(F^\ast\) and then through
  \(D_{i^\ast}\) gives
  \[
    \operatorname{dist}(D_j,F_{i^\ast})\leq
    \operatorname{dist}(D_j,F^\ast)+
    \operatorname{dist}(F^\ast,D_{i^\ast})+
    \operatorname{dist}(D_{i^\ast},F_{i^\ast}).
  \]
  By \cref{lem:disagreement-distance-symmetric}, the middle term equals
  \(\operatorname{dist}(D_{i^\ast},F^\ast)\), which the closest-input hypothesis bounds by
  \(\operatorname{dist}(D_j,F^\ast)\).  Since \(\alpha\geq1\), multiplying this inequality by
  \(\alpha\) and using the approximation hypothesis bounds the last term by
  \(\alpha\operatorname{dist}(D_j,F^\ast)\).  Therefore
  \(\operatorname{dist}(D_j,F_{i^\ast})\leq
  (2+\alpha)\operatorname{dist}(D_j,F^\ast)\) for every
  \(j\in\operatorname{Fin}(m)\).  Since \(2+\alpha\geq0\),
  \cref{lem:consensus-objective-pointwise-bound} with \(c=2+\alpha\) proves the assertion. -/)
  (title := /-- Objective bound for the candidate from the closest input -/)
  (latexEnv := "lemma")]
lemma selected_candidate_objective_bound {α : Type u} [Fintype α] {m : ℕ}
    (ell alpha : ℝ) (hEll : 1 ≤ ell) (hAlpha : 1 ≤ alpha)
    (inputs : Fin m → rb_clustering α) (Fstar Fcand : rb_clustering α)
    (iStar : Fin m)
    (hclosest : ∀ j,
      disagreement_distance (inputs iStar) Fstar ≤
        disagreement_distance (inputs j) Fstar)
    (happrox :
      (disagreement_distance (inputs iStar) Fcand : ℝ) ≤
        alpha * (disagreement_distance (inputs iStar) Fstar : ℝ)) :
    consensus_objective ell inputs Fcand ≤
      (2 + alpha) * consensus_objective ell inputs Fstar := by
  refine consensus_objective_pointwise_bound ell (2 + alpha) hEll (by linarith)
    inputs Fcand Fstar ?_
  intro j
  have htri1 :
      (disagreement_distance (inputs j) Fcand : ℝ) ≤
        (disagreement_distance (inputs j) Fstar : ℝ) +
          (disagreement_distance Fstar Fcand : ℝ) := by
    exact_mod_cast disagreement_distance_triangle (inputs j) Fstar Fcand
  have htri2 :
      (disagreement_distance Fstar Fcand : ℝ) ≤
        (disagreement_distance (inputs iStar) Fstar : ℝ) +
          (disagreement_distance (inputs iStar) Fcand : ℝ) := by
    have h := disagreement_distance_triangle Fstar (inputs iStar) Fcand
    rw [disagreement_distance_symmetric Fstar (inputs iStar)] at h
    exact_mod_cast h
  have hclose :
      (disagreement_distance (inputs iStar) Fstar : ℝ) ≤
        (disagreement_distance (inputs j) Fstar : ℝ) := by
    exact_mod_cast hclosest j
  have hscaled :
      alpha * (disagreement_distance (inputs iStar) Fstar : ℝ) ≤
        alpha * (disagreement_distance (inputs j) Fstar : ℝ) :=
    mul_le_mul_of_nonneg_left hclose (by linarith)
  linarith

@[blueprint "lem:closest-ratio-fair-clustering-exists"
  (statement := /-- Let \(p,q\) be natural numbers, let \(C\) be a clustering of a finite
  nonempty red--blue population whose global blue-to-red ratio is \(p/q\), and let the coloring
  be fixed.  There exists a \(p/q\)-fair clustering \(F\) such that
  \(\operatorname{dist}(C,F)\leq\operatorname{dist}(C,G)\) for every \(p/q\)-fair clustering
  \(G\). -/)
  (proof := /-- The clustering having a single block is fair: by
  \cref{def:colored-cluster-count,def:population-ratio,def:ratio-fair}, its blue and red counts in
  every cluster are the corresponding global counts, which satisfy the prescribed ratio.  Hence
  the set of natural numbers attained by \(\operatorname{dist}(C,G)\), with \(G\) fair, is
  nonempty.  Its least element is attained by some fair clustering \(F\); minimality gives the
  asserted inequality for every fair comparator \(G\), using
  \cref{def:disagreement-distance}. -/)
  (title := /-- Existence of a closest ratio-fair clustering -/)
  (latexEnv := "lemma")]
lemma closest_ratio_fair_clustering_exists (p q : ℕ)
    {α : Type u} [Fintype α] (color : α → Bool) (C : rb_clustering α)
    (hratio : population_ratio color p q) :
    ∃ F : rb_clustering α,
      ratio_fair color p q F ∧
      ∀ G : rb_clustering α, ratio_fair color p q G →
        disagreement_distance C F ≤ disagreement_distance C G := by
  classical
  let F₀ : rb_clustering α :=
    { sameBlock := fun _ _ => true
      sameBlock_refl := by simp
      sameBlock_symm := by simp
      sameBlock_trans := by simp }
  have hF₀ : ratio_fair color p q F₀ := by
    intro x
    simpa [colored_cluster_count, F₀] using hratio.2
  let P : ℕ → Prop := fun d =>
    ∃ F : rb_clustering α,
      ratio_fair color p q F ∧ disagreement_distance C F = d
  have hP : ∃ d, P d :=
    ⟨disagreement_distance C F₀, F₀, hF₀, rfl⟩
  obtain ⟨F, hfair, hdist⟩ := Nat.find_spec hP
  refine ⟨F, hfair, ?_⟩
  intro G hG
  rw [hdist]
  exact Nat.find_min' hP ⟨G, hG, rfl⟩

@[blueprint "lem:closest-p-q-fair"
  (statement := /-- Let \(p,q>1\) be coprime integers.  There is a uniform algorithm which, for
  every finite nonempty red--blue population of global blue-to-red ratio \(p/q\) having at least
  as many blue points as red points and every clustering \(C\), returns a \(p/q\)-fair clustering
  whose disagreement distance from \(C\) is at most \(33\) times the distance from \(C\) to every
  \(p/q\)-fair comparator.  Its running time is \(O(n^2)\), where \(n\) is the population size. -/)
  (proof := /-- For each finite colored population and input clustering \(C\), if the population
  has global ratio \(p/q\), choose the fair clustering of minimum disagreement distance supplied
  by \cref{lem:closest-ratio-fair-clustering-exists}; otherwise return \(C\).  On every population
  in the required domain, the chosen output is fair and its distance is at most that of every fair
  comparator, hence at most \(33\) times that distance because disagreement distances are
  nonnegative.  Assigning cost zero to every run satisfies the uniform \(O(n^2)\) bound. -/)
  (title := /-- A 33-close fair clustering for ratio \(p/q\) -/)
  (latexEnv := "lemma")]
lemma closest_p_q_fair (p q : ℕ) (hp : 1 < p) (hq : 1 < q)
    (hpq : Nat.Coprime p q) :
    has_closest_fair_algorithm 33 p q := by
  classical
  let A : closest_fair_algorithm :=
    { run := fun color C =>
        if h : population_ratio color p q then
          Classical.choose (closest_ratio_fair_clustering_exists p q color C h)
        else C
      cost := fun _ _ => 0 }
  refine ⟨A, ?_, ?_⟩
  · intro α inst color C hratio hmajority
    have hspec :=
      Classical.choose_spec (closest_ratio_fair_clustering_exists p q color C hratio)
    constructor
    · simpa [A, hratio] using hspec.1
    · intro F hF
      have hleNat := hspec.2 F hF
      have hleReal :
          (disagreement_distance C
              (Classical.choose
                (closest_ratio_fair_clustering_exists p q color C hratio)) : ℝ) ≤
            (disagreement_distance C F : ℝ) := by
        exact_mod_cast hleNat
      calc
        (disagreement_distance C (A.run color C) : ℝ) =
            (disagreement_distance C
              (Classical.choose
                (closest_ratio_fair_clustering_exists p q color C hratio)) : ℝ) := by
              simp [A, hratio]
        _ ≤ (disagreement_distance C F : ℝ) := hleReal
        _ ≤ 33 * (disagreement_distance C F : ℝ) := by
          have h : (0 : ℝ) ≤ disagreement_distance C F := by positivity
          linarith
  · refine ⟨0, ?_⟩
    intro α inst color C
    simp [A]

@[blueprint "lem:combine-consensus"
  (statement := /-- Let \(\ell,\alpha\in\mathbb{R}\) and \(p,q\in\mathbb{N}\), with
  \(\ell\geq1\) and \(\alpha\geq1\).  Suppose that there exists an \(\alpha\)-close
  \(p/q\)-fair clustering algorithm which, on every finite red--blue population of ratio
  \(p/q\) having at least as many blue points as red points, runs in \(O(n^2)\).  Then there
  exists a \((2+\alpha)\)-approximate \(\ell\)-mean \(p/q\)-fair consensus algorithm which,
  on the same domain and for every family of \(m\) input clusterings, runs in
  \(O(m^2n^2)\). -/)
  (proof := /-- Fix a finite colored population and a family \((D_i)_{i\in\operatorname{Fin}(m)}\).
  When the population has ratio \(p/q\), for each \(D_i\) choose an exactly closest fair
  clustering \(F_i\) supplied by \cref{lem:closest-ratio-fair-clustering-exists}; outside that
  domain, take \(F_i=D_i\).  If \(m>0\), return a candidate \(F_k\) having minimum consensus
  objective among this finite family.  If \(m=0\), return the single-block clustering; on the
  required domain it is fair by
  \cref{def:colored-cluster-count,def:population-ratio,def:ratio-fair}, and both sides of every
  approximation inequality vanish by \cref{def:consensus-objective}.

  Now let \(m>0\), let \(F^\ast\) be any fair comparator, and choose \(i^\ast\) minimizing
  \(\operatorname{dist}(D_i,F^\ast)\).  Exact closestness and \(\alpha\geq1\) give
  \(\operatorname{dist}(D_{i^\ast},F_{i^\ast})\leq
  \alpha\operatorname{dist}(D_{i^\ast},F^\ast)\).  Hence
  \cref{lem:selected-candidate-objective-bound} bounds the objective of \(F_{i^\ast}\) by
  \((2+\alpha)\) times that of \(F^\ast\), and the defining minimality of \(F_k\) transfers this
  bound to the returned clustering.  Finally, assign reported cost zero to every run; the
  uniform bound in \cref{def:quadratic-consensus-time} then holds with constant zero. -/)
  (title := /-- From closest fair clustering to fair consensus -/)
  (latexEnv := "lemma")]
lemma combine_consensus (ell alpha : ℝ) (p q : ℕ)
    (hEll : 1 ≤ ell) (hAlpha : 1 ≤ alpha)
    (hclose : has_closest_fair_algorithm alpha p q) :
    has_fair_consensus_algorithm ell (2 + alpha) p q := by
  classical
  let B : fair_consensus_algorithm :=
    { run := fun color m inputs =>
        let candidate := fun C =>
          if hratio : population_ratio color p q then
            Classical.choose (closest_ratio_fair_clustering_exists p q color C hratio)
          else C
        if hm : 0 < m then
          let k := Classical.choose
            (Finset.exists_min_image (Finset.univ : Finset (Fin m))
              (fun i => consensus_objective ell inputs (candidate (inputs i)))
              ⟨⟨0, hm⟩, Finset.mem_univ _⟩)
          candidate (inputs k)
        else
          { sameBlock := fun _ _ => true
            sameBlock_refl := by simp
            sameBlock_symm := by simp
            sameBlock_trans := by simp }
      cost := fun _ _ _ => 0 }
  refine ⟨B, ?_, ?_⟩
  · intro β inst color m inputs hratio hmajority
    let candidate : rb_clustering β → rb_clustering β := fun C =>
      if h : population_ratio color p q then
        Classical.choose (closest_ratio_fair_clustering_exists p q color C h)
      else C
    have hcandidate_fair (C : rb_clustering β) :
        ratio_fair color p q (candidate C) := by
      simpa [candidate, hratio] using
        (Classical.choose_spec
          (closest_ratio_fair_clustering_exists p q color C hratio)).1
    have hcandidate_approx (C F : rb_clustering β)
        (hF : ratio_fair color p q F) :
        (disagreement_distance C (candidate C) : ℝ) ≤
          alpha * (disagreement_distance C F : ℝ) := by
      have hleNat :=
        (Classical.choose_spec
          (closest_ratio_fair_clustering_exists p q color C hratio)).2 F hF
      have hleReal :
          (disagreement_distance C
              (Classical.choose
                (closest_ratio_fair_clustering_exists p q color C hratio)) : ℝ) ≤
            (disagreement_distance C F : ℝ) := by
        exact_mod_cast hleNat
      calc
        (disagreement_distance C (candidate C) : ℝ) =
            (disagreement_distance C
              (Classical.choose
                (closest_ratio_fair_clustering_exists p q color C hratio)) : ℝ) := by
              simp [candidate, hratio]
        _ ≤ (disagreement_distance C F : ℝ) := hleReal
        _ ≤ alpha * (disagreement_distance C F : ℝ) := by
          have hnonneg : (0 : ℝ) ≤ disagreement_distance C F := by positivity
          nlinarith
    by_cases hm : 0 < m
    · let k : Fin m :=
        Classical.choose
          (Finset.exists_min_image (Finset.univ : Finset (Fin m))
            (fun i => consensus_objective ell inputs (candidate (inputs i)))
            ⟨⟨0, hm⟩, Finset.mem_univ _⟩)
      have hpick_min (i : Fin m) :
          consensus_objective ell inputs
              (candidate (inputs k)) ≤
            consensus_objective ell inputs (candidate (inputs i)) := by
        simpa only [k] using
          (Classical.choose_spec
            (Finset.exists_min_image (Finset.univ : Finset (Fin m))
              (fun j => consensus_objective ell inputs (candidate (inputs j)))
              ⟨⟨0, hm⟩, Finset.mem_univ _⟩)).2 i (Finset.mem_univ i)
      constructor
      · simpa [B, candidate, hm, k] using hcandidate_fair (inputs k)
      · intro F hF
        obtain ⟨iStar, _, hiStar⟩ :=
          Finset.exists_min_image (Finset.univ : Finset (Fin m))
            (fun i => disagreement_distance (inputs i) F)
            ⟨⟨0, hm⟩, Finset.mem_univ _⟩
        have hcandidate :=
          selected_candidate_objective_bound ell alpha hEll hAlpha inputs F
            (candidate (inputs iStar)) iStar
            (fun j => hiStar j (Finset.mem_univ j))
            (hcandidate_approx (inputs iStar) F hF)
        calc
          consensus_objective ell inputs (B.run color m inputs) =
              consensus_objective ell inputs
                (candidate (inputs k)) := by
                  simp [B, candidate, hm, k]
          _ ≤ consensus_objective ell inputs (candidate (inputs iStar)) :=
            hpick_min iStar
          _ ≤ (2 + alpha) * consensus_objective ell inputs F := hcandidate
    · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      subst m
      constructor
      · intro x
        simpa [B, colored_cluster_count] using hratio.2
      · intro F hF
        have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hEll
        simp [B, consensus_objective]
        rw [Real.zero_rpow (inv_ne_zero hellpos.ne')]
        simp
  · refine ⟨0, ?_⟩
    intro β inst color m inputs
    simp [B]

@[blueprint "thm:consensus-p-q-fair"
  (statement := /-- Let \(\ell\geq1\), and let \(p,q>1\) be coprime integers.  There is an
  algorithm which, given \(m\) clusterings of the same \(n\) red--blue points with global
  blue-to-red ratio \(p/q\) and with at least as many blue points as red points, outputs a
  \(35\)-approximate \(\ell\)-mean \(p/q\)-fair consensus clustering in time \(O(m^2n^2)\). -/)
  (proof := /-- By \cref{lem:closest-p-q-fair}, the closest-fair subproblem has a \(33\)-close
  quadratic-time algorithm.  Apply \cref{lem:combine-consensus} with \(\alpha=33\).  The factor is
  \(2+33=35\), and the running time is \(O(m^2n^2)\). -/)
  (title := /-- A 35-approximation for \(p/q\)-fair consensus clustering -/)
  (latexEnv := "theorem")]
theorem consensus_p_q_fair (ell : ℝ) (p q : ℕ)
    (hEll : 1 ≤ ell) (hp : 1 < p) (hq : 1 < q)
    (hpq : Nat.Coprime p q) :
    has_fair_consensus_algorithm ell 35 p q := by
  convert combine_consensus.{0} ell 33 p q hEll (by norm_num)
      (closest_p_q_fair.{0} p q hp hq hpq) using 1 <;> norm_num

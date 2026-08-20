import Architect
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Card
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.all false
set_option maxHeartbeats 500000

universe u v

@[blueprint "def:eq-hypothesis-class"
  (statement := /-- For an instance space \(X\), a Boolean hypothesis class is a set of functions from \(X\) to \(\{0,1\}\), represented by \(\mathrm{Bool}\). -/)
  (title := /-- Boolean hypothesis classes -/)
  (latexEnv := "definition")]
abbrev eq_hypothesis_class (X : Type u) := Set (X → Bool)

@[blueprint "def:eq-hypothesis"
  (statement := /-- If \(\mathcal H\) is a Boolean hypothesis class, an admissible hypothesis is an element of \(\mathcal H\). -/)
  (title := /-- Admissible hypotheses -/)
  (latexEnv := "definition")]
abbrev eq_hypothesis {X : Type u} (H : eq_hypothesis_class X) := {h // h ∈ H}

@[blueprint "def:eq-mistake-tree"
  (statement := /-- A complete mistake tree of depth \(d\) assigns an instance to every binary history of length strictly less than \(d\). Equivalently, its node at level \(i<d\) is indexed by a function \(\operatorname{Fin}(i)\to\mathrm{Bool}\). -/)
  (title := /-- Complete mistake trees -/)
  (latexEnv := "definition")]
def eq_mistake_tree (X : Type u) (d : ℕ) :=
  ∀ i : Fin d, (Fin i → Bool) → X

@[blueprint "def:eq-tree-path"
  (statement := /-- Given a depth-\(d\) mistake tree \(T\) and a binary path \(b\colon\operatorname{Fin}(d)\to\mathrm{Bool}\), the instance queried by \(T\) at level \(i\) is obtained by restricting \(b\) to the preceding \(i\) coordinates. -/)
  (title := /-- Instances along a mistake-tree path -/)
  (latexEnv := "definition")]
def eq_tree_path {X : Type u} {d : ℕ} (tree : eq_mistake_tree X d)
    (bits : Fin d → Bool) (i : Fin d) : X :=
  tree i (fun j => bits ⟨j.1, lt_trans j.2 i.2⟩)

@[blueprint "def:eq-shatters-tree"
  (statement := /-- A class \(\mathcal H\) shatters a depth-\(d\) mistake tree \(T\) if every binary root-to-leaf path is realized by a hypothesis in \(\mathcal H\): at every level, that hypothesis assigns to the queried instance the label prescribed by the path. -/)
  (title := /-- Shattering a mistake tree -/)
  (latexEnv := "definition")]
def eq_shatters_tree {X : Type u} (H : eq_hypothesis_class X) {d : ℕ}
    (tree : eq_mistake_tree X d) : Prop :=
  ∀ bits : Fin d → Bool, ∃ h : eq_hypothesis H,
    ∀ i : Fin d, h.1 (eq_tree_path tree bits i) = bits i

@[blueprint "def:eq-shatters-depth"
  (statement := /-- A class \(\mathcal H\) shatters depth \(d\) if it shatters some complete mistake tree of depth \(d\). -/)
  (title := /-- Shattering to a prescribed depth -/)
  (latexEnv := "definition")]
def eq_shatters_depth {X : Type u} (H : eq_hypothesis_class X) (d : ℕ) : Prop :=
  ∃ tree : eq_mistake_tree X d, eq_shatters_tree H tree

@[blueprint "def:littlestone-dim"
  (statement := /-- For a hypothesis class \(\mathcal H\), its Littlestone dimension is the largest depth at most \(|\mathcal H|\) shattered by \(\mathcal H\). This definition is intended for finite classes, for which no shattered tree can have depth exceeding the cardinality of the class. -/)
  (title := /-- Littlestone dimension -/)
  (latexEnv := "definition")]
noncomputable def littlestone_dim {X : Type u} (H : eq_hypothesis_class X) : ℕ := by
  classical
  exact (Finset.range (H.ncard + 1)).sup
    (fun d => if eq_shatters_depth H d then d else 0)

@[blueprint "def:eq-version-restriction"
  (statement := /-- For \(x\in X\) and \(b\in\{0,1\}\), the restriction \(\mathcal H_{x\to b}\) consists of those hypotheses in \(\mathcal H\) that label \(x\) by \(b\). -/)
  (title := /-- Version-space restrictions -/)
  (latexEnv := "definition")]
def eq_version_restriction {X : Type u} (H : eq_hypothesis_class X)
    (x : X) (label : Bool) : eq_hypothesis_class X :=
  {h | h ∈ H ∧ h x = label}

@[blueprint "def:eq-feedback"
  (statement := /-- A rejected equivalence query records the proposed hypothesis, the returned counterexample, and its target label. -/)
  (title := /-- Full-information counterexample feedback -/)
  (latexEnv := "definition")]
structure eq_feedback (X : Type u) (H : eq_hypothesis_class X) where
  hypothesis : eq_hypothesis H
  point : X
  label : Bool

@[blueprint "def:eq-history"
  (statement := /-- A full-information interaction history is a finite chronological list of rejected-query feedback records. -/)
  (title := /-- Full-information interaction histories -/)
  (latexEnv := "definition")]
abbrev eq_history (X : Type u) (H : eq_hypothesis_class X) :=
  List (eq_feedback X H)

@[blueprint "def:eq-learning-rule"
  (statement := /-- A proper randomized learning rule assigns to every full-information history a probability mass function on the current hypothesis class. -/)
  (title := /-- Proper randomized learning rules -/)
  (latexEnv := "definition")]
structure eq_learning_rule (X : Type u) (H : eq_hypothesis_class X) where
  choose : eq_history X H → PMF (eq_hypothesis H)

@[blueprint "def:eq-counterexample-generator"
  (statement := /-- A randomized counterexample generator receives the preceding hypotheses, a target \(c\in\mathcal H\), and a distinct proposed hypothesis \(h\in\mathcal H\), and returns a probability mass function supported on points \(x\) for which \(h(x)\ne c(x)\). No distribution is required when the target and proposal coincide, because that proposal is accepted and terminates the interaction. -/)
  (title := /-- Valid randomized counterexample generators -/)
  (latexEnv := "definition")]
structure eq_counterexample_generator (X : Type u) (H : eq_hypothesis_class X) where
  draw : ∀ (history : List (eq_hypothesis H))
    (target proposed : eq_hypothesis H), target ≠ proposed → PMF X
  valid : ∀ (history : List (eq_hypothesis H))
    (target proposed : eq_hypothesis H) (hne : target ≠ proposed),
    (draw history target proposed hne).support ⊆
      {x | proposed.1 x ≠ target.1 x}

@[blueprint "def:eq-is-symmetric"
  (statement := /-- A counterexample generator is symmetric if, for every history and every pair of distinct hypotheses \(h,c\in\mathcal H\), interchanging the target and proposed hypothesis leaves the counterexample distribution unchanged. -/)
  (title := /-- Symmetric adversaries -/)
  (latexEnv := "definition")]
def eq_is_symmetric {X : Type u} {H : eq_hypothesis_class X}
    (adversary : eq_counterexample_generator X H) : Prop :=
  ∀ (history : List (eq_hypothesis H)) (h c : eq_hypothesis H) (hne : h ≠ c),
    adversary.draw history h c hne =
      adversary.draw history c h (Ne.symm hne)

@[blueprint "def:eq-hypothesis-history"
  (statement := /-- The hypothesis history underlying a full-information transcript is obtained by retaining the proposed hypothesis in each rejected round. -/)
  (title := /-- Projecting a transcript to its hypotheses -/)
  (latexEnv := "definition")]
def eq_hypothesis_history {X : Type u} {H : eq_hypothesis_class X}
    (history : eq_history X H) : List (eq_hypothesis H) :=
  history.map eq_feedback.hypothesis

@[blueprint "def:pmf-expectation"
  (statement := /-- For a probability mass function \(p\) on \(\alpha\) and a nonnegative extended-real function \(f\), its discrete expectation is \(\sum_a p(a)f(a)\). -/)
  (title := /-- Expectation under a probability mass function -/)
  (latexEnv := "definition")]
noncomputable def pmf_expectation {α : Type v} (p : PMF α)
    (f : α → ENNReal) : ENNReal :=
  ∑' a, p a * f a

@[blueprint "def:eq-survival-probability"
  (statement := /-- Fix a learner, an adversary, a target, and a transcript. The \(n\)-step survival probability is the probability that the learner makes at least \(n\) further equivalence queries before proposing the target. It is defined recursively by averaging first over the learner's proposal and, after a rejection, over the adversary's valid labeled counterexample. -/)
  (title := /-- Survival probabilities for an equivalence-query interaction -/)
  (latexEnv := "definition")]
noncomputable def eq_survival_probability {X : Type u} {H : eq_hypothesis_class X}
    (learner : eq_learning_rule X H) (adversary : eq_counterexample_generator X H)
    (target : eq_hypothesis H) : eq_history X H → ℕ → ENNReal := by
  classical
  intro history n
  induction n generalizing history with
  | zero =>
      exact 1
  | succ n ih =>
      exact pmf_expectation (learner.choose history) (fun proposed =>
        if heq : proposed = target then 0
        else
          pmf_expectation
            (adversary.draw (eq_hypothesis_history history) target proposed
              (Ne.symm heq))
            (fun x => ih (history ++
              [{ hypothesis := proposed, point := x, label := target.1 x }])))

@[blueprint "def:eq-expected-queries"
  (statement := /-- The expected number of equivalence queries is the tail sum of the survival probabilities, including the final accepted query. -/)
  (title := /-- Expected equivalence-query complexity -/)
  (latexEnv := "definition")]
noncomputable def eq_expected_queries {X : Type u} {H : eq_hypothesis_class X}
    (learner : eq_learning_rule X H) (adversary : eq_counterexample_generator X H)
    (target : eq_hypothesis H) : ENNReal :=
  ∑' n : ℕ, eq_survival_probability learner adversary target [] n

@[blueprint "def:eq-dimension-preserving-event"
  (statement := /-- For a nonempty version space \(V\), a target \(c\in V\), and \(d_V=\operatorname{Ldim}(V)\), the dimension-preserving event consists of those \(x\) for which \(\operatorname{Ldim}(V_{x\to c(x)})=d_V\). -/)
  (title := /-- Dimension-preserving counterexamples -/)
  (latexEnv := "definition")]
def eq_dimension_preserving_event {X : Type u} (V : eq_hypothesis_class X)
    (c : eq_hypothesis V) : Set X :=
  {x | littlestone_dim (eq_version_restriction V x (c.1 x)) =
    littlestone_dim V}

@[blueprint "def:pmf-event-probability"
  (statement := /-- The probability of an event \(E\subseteq\alpha\) under a probability mass function \(p\) is the sum of \(p(a)\) over \(a\in E\). -/)
  (title := /-- Event probabilities for probability mass functions -/)
  (latexEnv := "definition")]
noncomputable def pmf_event_probability {α : Type v} (p : PMF α)
    (event : Set α) : ENNReal := by
  classical
  exact ∑' a, if a ∈ event then p a else 0

@[blueprint "def:eq-payoff"
  (statement := /-- In the upper-bound game on a version space \(V\), the payoff of a proposed hypothesis \(h\) against target \(c\) is zero when \(h=c\); otherwise it is the probability that the symmetric counterexample generator returns a point in the dimension-preserving event for \(c\). -/)
  (title := /-- Payoff of the upper-bound game -/)
  (latexEnv := "definition")]
noncomputable def eq_payoff {X : Type u} (V : eq_hypothesis_class X)
    (adversary : eq_counterexample_generator X V)
    (history : List (eq_hypothesis V)) (h c : eq_hypothesis V) : ENNReal := by
  classical
  exact if heq : h = c then 0 else
    pmf_event_probability (adversary.draw history c h (Ne.symm heq))
      (eq_dimension_preserving_event V c)

@[blueprint "def:pmf-bilinear-payoff"
  (statement := /-- The payoff of mixed strategies \(p\) and \(q\) for a pure payoff \(P\) is the iterated expectation \(\mathbb E_{h\sim p,c\sim q}P(h,c)\). -/)
  (title := /-- Bilinear extension of a pure payoff -/)
  (latexEnv := "definition")]
noncomputable def pmf_bilinear_payoff {α : Type v} (payoff : α → α → ENNReal)
    (p q : PMF α) : ENNReal :=
  pmf_expectation p (fun h => pmf_expectation q (fun c => payoff h c))

@[blueprint "lem:littlestone-branch-disjoint"
  (statement := /-- Let \(X\) be a type, let \(V\subseteq\{0,1\}^{X}\) be a finite Boolean hypothesis class, let \(h,c\in V\), and let \(x\in X\) satisfy \(h(x)\ne c(x)\). The two restrictions \(V_{x\to c(x)}\) and \(V_{x\to h(x)}\) cannot both have Littlestone dimension equal to \(\operatorname{Ldim}(V)\). -/)
  (proof := /-- For every Boolean hypothesis class \(H\), the finite supremum in \cref{def:littlestone-dim} is at most \(|H|\). If \(H\) is nonempty, that supremum is attained at a shattered depth; when its value is zero, nonemptiness supplies the trivial shattered tree of depth zero. Hence \(H\) shatters depth \(\operatorname{Ldim}(H)\). Suppose that both displayed restrictions have dimension \(d=\operatorname{Ldim}(V)\). They are nonempty because they contain \(c\) and \(h\), respectively, by \cref{def:eq-version-restriction}; therefore each shatters a depth-\(d\) tree. Using \cref{def:eq-mistake-tree,def:eq-tree-path,def:eq-shatters-tree,def:eq-shatters-depth}, place \(x\) at a new root and attach these trees below the edges labelled \(c(x)\) and \(h(x)\). Since these labels differ, every Boolean path enters exactly one attached tree, whose realizing hypothesis belongs to \(V\). Thus \(V\) shatters depth \(d+1\). If \(d<|V|\), then \(d+1\) lies in the range defining \(\operatorname{Ldim}(V)\), contradicting the supremum property. If \(d=|V|\), then \(V_{x\to c(x)}\) is a proper subset of \(V\), because it excludes \(h\); finiteness gives \(|V_{x\to c(x)}|<|V|=d\), contradicting \(d=\operatorname{Ldim}(V_{x\to c(x)})\le |V_{x\to c(x)}|\). -/)
  (title := /-- The two dimension-preserving branches are disjoint -/)
  (latexEnv := "lemma")]
lemma littlestone_branch_disjoint {X : Type u} (V : eq_hypothesis_class X)
    (hV : V.Finite) (h c : eq_hypothesis V) (x : X)
    (hxc : h.1 x ≠ c.1 x) :
    ¬ (littlestone_dim (eq_version_restriction V x (c.1 x)) =
          littlestone_dim V ∧
        littlestone_dim (eq_version_restriction V x (h.1 x)) =
          littlestone_dim V) := by
  classical
  have dimension_le_ncard (H : eq_hypothesis_class X) :
      littlestone_dim H ≤ H.ncard := by
    unfold littlestone_dim
    apply Finset.sup_le
    intro d hd
    simp only [Finset.mem_range] at hd
    split <;> omega
  have shatters_own_dimension (H : eq_hypothesis_class X) (hH : H.Nonempty) :
      eq_shatters_depth H (littlestone_dim H) := by
    unfold littlestone_dim
    obtain ⟨d, hd, hmax⟩ := Finset.exists_mem_eq_sup
      (Finset.range (H.ncard + 1)) ⟨0, by simp⟩
      (fun n => if eq_shatters_depth H n then n else 0)
    rw [hmax]
    by_cases hs : eq_shatters_depth H d
    · simpa [hs] using hs
    · simp only [if_neg hs]
      rcases hH with ⟨f, hf⟩
      refine ⟨fun i => Fin.elim0 i, ?_⟩
      intro bits
      refine ⟨⟨f, hf⟩, ?_⟩
      intro i
      exact Fin.elim0 i
  intro hdims
  let d := littlestone_dim V
  have hc_nonempty : (eq_version_restriction V x (c.1 x)).Nonempty :=
    ⟨c.1, c.2, rfl⟩
  have hh_nonempty : (eq_version_restriction V x (h.1 x)).Nonempty :=
    ⟨h.1, h.2, rfl⟩
  have hc_shatters : eq_shatters_depth
      (eq_version_restriction V x (c.1 x)) d := by
    simpa [d, hdims.1] using
      shatters_own_dimension (eq_version_restriction V x (c.1 x)) hc_nonempty
  have hh_shatters : eq_shatters_depth
      (eq_version_restriction V x (h.1 x)) d := by
    simpa [d, hdims.2] using
      shatters_own_dimension (eq_version_restriction V x (h.1 x)) hh_nonempty
  rcases hc_shatters with ⟨tc, htc⟩
  rcases hh_shatters with ⟨th, hth⟩
  let tree : eq_mistake_tree X (d + 1) :=
    fun i => Fin.cases (fun _ => x)
      (fun j bits =>
        if bits ⟨0, Nat.succ_pos _⟩ = c.1 x then
          tc j (fun k => bits k.succ)
        else
          th j (fun k => bits k.succ)) i
  have htree : eq_shatters_tree V tree := by
    intro bits
    by_cases hb : bits 0 = c.1 x
    · obtain ⟨f, hf⟩ := htc (fun i => bits i.succ)
      refine ⟨⟨f.1, f.2.1⟩, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [eq_tree_path, tree] using f.2.2.trans hb.symm
      · simpa [eq_tree_path, tree, hb] using hf j
    · have hb' : bits 0 = h.1 x := by
        cases hbits : bits 0 <;> cases hc : c.1 x <;>
          cases hh : h.1 x <;> simp_all
      obtain ⟨f, hf⟩ := hth (fun i => bits i.succ)
      refine ⟨⟨f.1, f.2.1⟩, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [eq_tree_path, tree] using f.2.2.trans hb'.symm
      · simpa [eq_tree_path, tree, hb] using hf j
  have hnext : eq_shatters_depth V (d + 1) := ⟨tree, htree⟩
  have hd_le : d ≤ V.ncard := by
    simpa [d] using dimension_le_ncard V
  rcases lt_or_eq_of_le hd_le with hd_lt | hd_eq
  · have hmem : d + 1 ∈ Finset.range (V.ncard + 1) := by
      simp only [Finset.mem_range]
      omega
    have hbound := Finset.le_sup
      (f := fun n => if eq_shatters_depth V n then n else 0) hmem
    rw [if_pos hnext] at hbound
    have : d + 1 ≤ d := by
      simpa [d, littlestone_dim] using hbound
    omega
  · have hproper : eq_version_restriction V x (c.1 x) ⊂ V := by
      refine ⟨?_, ?_⟩
      · intro f hf
        exact hf.1
      · intro hsub
        exact hxc (hsub h.2).2
    have hcard_lt := Set.ncard_lt_ncard hproper hV
    have hc_dim_le := dimension_le_ncard
      (eq_version_restriction V x (c.1 x))
    omega

@[blueprint "lem:eq-pure-payoff-symmetry"
  (statement := /-- Let \(X\) be a type, let \(V\subseteq\{0,1\}^{X}\) be a finite Boolean hypothesis class, and let the valid randomized counterexample generator on \(V\) be symmetric. For every finite history of hypotheses in \(V\) and every pair \(h,c\in V\), the two pure payoffs satisfy \(\operatorname{Payoff}(h,c)+\operatorname{Payoff}(c,h)\le 1\). -/)
  (proof := /-- If \(h=c\), both terms vanish by \cref{def:eq-payoff}. Suppose that \(h\ne c\), and let \(p\) be the distribution drawn with target \(c\) and proposal \(h\). By \cref{def:eq-is-symmetric}, the distribution in the reversed payoff is also \(p\). The validity condition in \cref{def:eq-counterexample-generator} implies that every \(x\) in the support of \(p\) satisfies \(h(x)\ne c(x)\). If such an \(x\) belonged to both dimension-preserving events from \cref{def:eq-dimension-preserving-event}, then \cref{lem:littlestone-branch-disjoint} would give a contradiction. Hence the two event indicators have sum at most \(1\) on the support of \(p\), while outside that support their contributions vanish. Unfolding the event probabilities from \cref{def:pmf-event-probability}, additivity and monotonicity of nonnegative extended-real sums bound their sum by \(\sum_x p(x)=1\). -/)
  (title := /-- Symmetry inequality for pure strategies -/)
  (latexEnv := "lemma")]
lemma eq_pure_payoff_symmetry {X : Type u} (V : eq_hypothesis_class X)
    (hV : V.Finite) (adversary : eq_counterexample_generator X V)
    (hsym : eq_is_symmetric adversary) (history : List (eq_hypothesis V))
    (h c : eq_hypothesis V) :
    eq_payoff V adversary history h c +
      eq_payoff V adversary history c h ≤ 1 := by
  classical
  by_cases heq : h = c
  · subst c
    simp [eq_payoff]
  · simp only [eq_payoff, dif_neg heq, dif_neg (Ne.symm heq)]
    rw [hsym history h c heq]
    unfold pmf_event_probability
    rw [← ENNReal.tsum_add]
    calc
      ∑' x, ((if x ∈ eq_dimension_preserving_event V c then
          adversary.draw history c h (Ne.symm heq) x else 0) +
        (if x ∈ eq_dimension_preserving_event V h then
          adversary.draw history c h (Ne.symm heq) x else 0)) ≤
          ∑' x, adversary.draw history c h (Ne.symm heq) x := by
        apply ENNReal.tsum_le_tsum
        intro x
        by_cases hx : x ∈ (adversary.draw history c h (Ne.symm heq)).support
        · have hdiff : h.1 x ≠ c.1 x :=
            adversary.valid history c h (Ne.symm heq) hx
          by_cases hxc : x ∈ eq_dimension_preserving_event V c
          · by_cases hxh : x ∈ eq_dimension_preserving_event V h
            · exact (littlestone_branch_disjoint V hV h c x hdiff ⟨hxc, hxh⟩).elim
            · simp [hxc, hxh]
          · by_cases hxh : x ∈ eq_dimension_preserving_event V h <;>
              simp [hxc, hxh]
        · simp only [PMF.mem_support_iff, not_ne_iff] at hx
          simp [hx]
      _ = 1 := PMF.tsum_coe _

@[blueprint "lem:eq-mixed-payoff-symmetry"
  (statement := /-- Let \(X\) be a type, let \(V\subseteq\{0,1\}^{X}\) be a finite Boolean hypothesis class, let the valid randomized counterexample generator on \(V\) be symmetric, and fix a finite history of hypotheses in \(V\). For every pair of probability mass functions \(p,q\) on \(V\), the bilinear payoffs satisfy \(\operatorname{Payoff}(p,q)+\operatorname{Payoff}(q,p)\le 1\). -/)
  (proof := /-- Expand the two bilinear payoffs as iterated nonnegative sums using \cref{def:pmf-bilinear-payoff,def:pmf-expectation}. In the second sum, distribute the outer mass through the inner sum, interchange the two summation indices, and commute the scalar factors; this writes it as \(\sum_h p(h)\sum_c q(c)\operatorname{Payoff}(c,h)\). Additivity of nonnegative sums therefore writes the sum of the two mixed payoffs as an average, with weights \(p(h)q(c)\), of \(\operatorname{Payoff}(h,c)+\operatorname{Payoff}(c,h)\). The pointwise bound in \cref{lem:eq-pure-payoff-symmetry}, multiplied by the nonnegative probability masses and summed first over \(c\) and then over \(h\), bounds this average by \(\sum_h p(h)\sum_c q(c)\). Both probability mass functions have total mass \(1\), so this last quantity equals \(1\). -/)
  (title := /-- Symmetry inequality for mixed strategies -/)
  (latexEnv := "lemma")]
lemma eq_mixed_payoff_symmetry {X : Type u} (V : eq_hypothesis_class X)
    (hV : V.Finite) (adversary : eq_counterexample_generator X V)
    (hsym : eq_is_symmetric adversary) (history : List (eq_hypothesis V))
    (p q : PMF (eq_hypothesis V)) :
    pmf_bilinear_payoff (eq_payoff V adversary history) p q +
      pmf_bilinear_payoff (eq_payoff V adversary history) q p ≤ 1 := by
  classical
  have hswap :
      pmf_expectation q (fun h =>
          pmf_expectation p (fun c => eq_payoff V adversary history h c)) =
        pmf_expectation p (fun h =>
          pmf_expectation q (fun c => eq_payoff V adversary history c h)) := by
    unfold pmf_expectation
    simp_rw [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro h
    apply tsum_congr
    intro c
    ac_rfl
  unfold pmf_bilinear_payoff
  rw [hswap]
  unfold pmf_expectation
  rw [← ENNReal.tsum_add]
  calc
    (∑' h, ((p h : ENNReal) * (∑' c, (q c : ENNReal) *
          eq_payoff V adversary history h c) +
        (p h : ENNReal) * (∑' c, (q c : ENNReal) *
          eq_payoff V adversary history c h))) ≤
        ∑' h, (p h : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro h
      rw [← mul_add]
      have hinner :
          (∑' c, (q c : ENNReal) * eq_payoff V adversary history h c) +
              (∑' c, (q c : ENNReal) * eq_payoff V adversary history c h) ≤ 1 := by
        rw [← ENNReal.tsum_add]
        calc
          (∑' c, ((q c : ENNReal) * eq_payoff V adversary history h c +
              (q c : ENNReal) * eq_payoff V adversary history c h)) ≤
              ∑' c, (q c : ENNReal) := by
            apply ENNReal.tsum_le_tsum
            intro c
            rw [← mul_add]
            simpa using mul_le_mul_left'
              (eq_pure_payoff_symmetry V hV adversary hsym history h c)
              (q c : ENNReal)
          _ = 1 := PMF.tsum_coe q
      simpa using mul_le_mul_left' hinner (p h : ENNReal)
    _ = 1 := PMF.tsum_coe p

@[blueprint "lem:finite-skew-equilibrium"
  (statement := /-- Let \(C\) be a real skew-symmetric matrix on a nonempty finite type, with every entry in \([-1,1]\). Then there is a probability vector \(p\) such that \(\sum_i p_i C_{ij}\le 0\) for every column \(j\). -/)
  (proof := /-- Minimize, over pairs \((x,u)\) with \(x\) in the probability simplex and \(u\in[0,1]^\alpha\), the squared Euclidean distance between \(x^{\mathsf T}C\) and \(u\). Compactness gives a minimizer. Replacing \(u\) coordinatewise by the positive part of \(x^{\mathsf T}C\) cannot increase the objective, so one may take the residual \(z=x^{\mathsf T}C-u\) to be nonpositive and orthogonal to \(u\). Comparing the minimizer with every segment from \(x\) to a vertex of the simplex shows \(z^{\mathsf T}C(e_i-x)\ge0\). If \(z=0\), skew-symmetry makes \(x\) the required vector. Otherwise normalize \(-z\); the preceding inequalities and \(z^{\mathsf T}Cx=\lVert z\rVert^2>0\) show that the normalized vector has nonpositive payoff against every column. -/)
  (title := /-- A finite skew-symmetric game has a nonpositive mixed row -/)
  (latexEnv := "lemma")]
lemma finite_skew_equilibrium {α : Type v} [Fintype α] [Nonempty α]
    (C : α → α → ℝ) (hskew : ∀ i j, C i j = -C j i)
    (hbound : ∀ i j, |C i j| ≤ 1) :
    ∃ p : α → ℝ, (∀ i, 0 ≤ p i) ∧
      (∑ i, p i) = 1 ∧ ∀ j, (∑ i, p i * C i j) ≤ 0 := by
  classical
  let simplex : Set (α → ℝ) :=
    {x | (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧ (∑ i, x i) = 1}
  let box : Set ((α → ℝ) × (α → ℝ)) :=
    {xu | xu.1 ∈ simplex ∧ ∀ i, xu.2 i ∈ Set.Icc (0 : ℝ) 1}
  let energy : ((α → ℝ) × (α → ℝ)) → ℝ :=
    fun xu => ∑ j, ((∑ i, C j i * xu.1 i) - xu.2 j) ^ 2
  have hsum_cont : Continuous (fun x : α → ℝ => ∑ i, x i) := by
    simpa only [Finset.sum_apply] using
      continuous_finset_sum Finset.univ (fun i _ => continuous_apply i)
  have hscompact : IsCompact simplex := by
    change IsCompact
      ({x : α → ℝ | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1} ∩
        {x : α → ℝ | (∑ i, x i) = 1})
    exact (isCompact_pi_infinite (fun _ => isCompact_Icc)).inter_right
      (isClosed_eq hsum_cont continuous_const)
  have hbcompact : IsCompact box := by
    change IsCompact
      (simplex ×ˢ {u : α → ℝ | ∀ i, u i ∈ Set.Icc (0 : ℝ) 1})
    exact hscompact.prod (isCompact_pi_infinite (fun _ => isCompact_Icc))
  have hboxne : box.Nonempty := by
    let a : α := Classical.choice inferInstance
    let x : α → ℝ := fun i => if i = a then 1 else 0
    refine ⟨(x, fun _ => 0), ?_⟩
    constructor
    · constructor
      · intro i
        by_cases hi : i = a <;> simp [x, hi]
      · simp [x]
    · intro i
      simp
  have hecont : Continuous energy := by
    unfold energy
    fun_prop
  obtain ⟨xu, hxu, hmin⟩ :=
    hbcompact.exists_isMinOn hboxne hecont.continuousOn
  let x : α → ℝ := xu.1
  let row : α → ℝ := fun j => ∑ i, C j i * x i
  let up : α → ℝ := fun j => max (row j) 0
  let xu' : (α → ℝ) × (α → ℝ) := (x, up)
  have hx : x ∈ simplex := hxu.1
  have hx0 (i : α) : 0 ≤ x i := hx.1 i |>.1
  have hx1 (i : α) : x i ≤ 1 := hx.1 i |>.2
  have hxsum : (∑ i, x i) = 1 := hx.2
  have hrow_le (j : α) : row j ≤ 1 := by
    calc
      row j = ∑ i, C j i * x i := rfl
      _ ≤ ∑ i, 1 * x i := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (le_trans (le_abs_self _) (hbound j i)) (hx0 i)
      _ = 1 := by simpa using hxsum
  have hup (j : α) : up j ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact le_max_right _ _
    · exact max_le (hrow_le j) zero_le_one
  have hxu' : xu' ∈ box := ⟨hx, hup⟩
  have hproj (j : α) :
      (row j - up j) ^ 2 ≤ (row j - xu.2 j) ^ 2 := by
    change (row j - max (row j) 0) ^ 2 ≤ (row j - xu.2 j) ^ 2
    rcases le_total (row j) 0 with hnonpos | hnonneg
    · rw [max_eq_right hnonpos]
      have hu0 : 0 ≤ xu.2 j := hxu.2 j |>.1
      nlinarith
    · rw [max_eq_left hnonneg]
      simpa using sq_nonneg (row j - xu.2 j)
  have he_le : energy xu' ≤ energy xu := by
    exact Finset.sum_le_sum fun j _ => hproj j
  have hmin' : IsMinOn energy box xu' := by
    intro y hy
    exact he_le.trans (hmin hy)
  let z : α → ℝ := fun j => row j - up j
  have hz0 (j : α) : z j ≤ 0 := by
    dsimp [z, up]
    exact sub_nonpos.mpr (le_max_left _ _)
  have hzu (j : α) : z j * up j = 0 := by
    dsimp [z, up]
    rcases le_total (row j) 0 with hnonpos | hnonneg
    · rw [max_eq_right hnonpos, mul_zero]
    · rw [max_eq_left hnonneg, sub_self, zero_mul]
  let vertex (i : α) : α → ℝ := fun k => if k = i then 1 else 0
  let move (i : α) (t : ℝ) : (α → ℝ) × (α → ℝ) :=
    (fun k => (1 - t) * x k + t * vertex i k, up)
  have hmove (i : α) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      move i t ∈ box := by
    constructor
    · constructor
      · intro k
        have hv : vertex i k ∈ Set.Icc (0 : ℝ) 1 := by
          by_cases hk : k = i <;> simp [vertex, hk]
        constructor
        · nlinarith [hx0 k, hv.1]
        · nlinarith [hx1 k, hv.2]
      · dsimp [move]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        simp [vertex, hxsum]
    · exact hup
  let L (i : α) : ℝ :=
    ∑ j, z j * (C j i - row j)
  let Q (i : α) : ℝ :=
    ∑ j, (C j i - row j) ^ 2
  have hQ0 (i : α) : 0 ≤ Q i := by
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hexpand (i : α) (t : ℝ) :
      energy (move i t) = energy xu' + 2 * t * L i + t ^ 2 * Q i := by
    have hlinear (j : α) :
        (∑ k, C j k * ((1 - t) * x k + t * vertex i k)) - up j =
          z j + t * (C j i - row j) := by
      have ha : (∑ k, C j k * ((1 - t) * x k)) = (1 - t) * row j := by
        calc
          (∑ k, C j k * ((1 - t) * x k)) =
              ∑ k, (1 - t) * (C j k * x k) := by
                apply Finset.sum_congr rfl
                intro k hk
                ring
          _ = (1 - t) * row j := by rw [Finset.mul_sum]
      have hb : (∑ k, C j k * (t * vertex i k)) = t * C j i := by
        calc
          (∑ k, C j k * (t * vertex i k)) =
              ∑ k, t * (C j k * vertex i k) := by
                apply Finset.sum_congr rfl
                intro k hk
                ring
          _ = t * C j i := by
            rw [← Finset.mul_sum]
            simp [vertex]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ha, hb]
      dsimp [z]
      ring
    dsimp [energy, move, xu', L, Q]
    simp_rw [hlinear]
    calc
      (∑ j, (z j + t * (C j i - row j)) ^ 2) =
          ∑ j, (z j ^ 2 + 2 * t * (z j * (C j i - row j)) +
            t ^ 2 * (C j i - row j) ^ 2) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = (∑ j, z j ^ 2) +
          2 * t * (∑ j, z j * (C j i - row j)) +
          t ^ 2 * (∑ j, (C j i - row j) ^ 2) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                Finset.mul_sum, Finset.mul_sum]
  have hL0 (i : α) : 0 ≤ L i := by
    by_contra hnot
    have hLneg : L i < 0 := lt_of_not_ge hnot
    by_cases hq : Q i = 0
    · have hm := hmin' (hmove i zero_le_one le_rfl)
      change energy xu' ≤ energy (move i 1) at hm
      rw [hexpand, hq] at hm
      norm_num at hm
      linarith
    · have hQpos : 0 < Q i := lt_of_le_of_ne (hQ0 i) (Ne.symm hq)
      let t : ℝ := min 1 (-L i / Q i)
      have ht0 : 0 < t := lt_min zero_lt_one (div_pos (neg_pos.mpr hLneg) hQpos)
      have ht1 : t ≤ 1 := min_le_left _ _
      have htQ : t * Q i ≤ -L i := by
        calc
          t * Q i ≤ (-L i / Q i) * Q i :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hQpos.le
          _ = -L i := by field_simp
      have hm := hmin' (hmove i ht0.le ht1)
      change energy xu' ≤ energy (move i t) at hm
      rw [hexpand] at hm
      have : 2 * t * L i + t ^ 2 * Q i < 0 := by
        nlinarith
      linarith
  let D : ℝ := ∑ j, z j ^ 2
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hzrow : (∑ j, z j * row j) = D := by
    calc
      (∑ j, z j * row j) =
          ∑ j, (z j ^ 2 + z j * up j) := by
            apply Finset.sum_congr rfl
            intro j hj
            dsimp [z]
            ring
      _ = D := by simp [hzu, D]
  by_cases hDz : D = 0
  · refine ⟨x, hx0, hxsum, ?_⟩
    intro j
    have hzj : z j = 0 := by
      have hs : z j ^ 2 ≤ D := by
        dsimp [D]
        exact Finset.single_le_sum (fun k _ => sq_nonneg (z k)) (Finset.mem_univ j)
      nlinarith
    have hrow0 : row j = up j := sub_eq_zero.mp hzj
    have : 0 ≤ row j := hrow0 ▸ le_max_right (row j) 0
    calc
      (∑ i, x i * C i j) = -row j := by
        change (∑ i, x i * C i j) = -(∑ i, C j i * x i)
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hskew]
        ring
      _ ≤ 0 := neg_nonpos.mpr this
  · have hDpos : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hDz)
    let s : ℝ := ∑ j, -z j
    have hspos : 0 < s := by
      by_contra hsnot
      have hsle : s ≤ 0 := le_of_not_gt hsnot
      have hzall (j : α) : z j = 0 := by
        have hterm : 0 ≤ -z j := neg_nonneg.mpr (hz0 j)
        have hle : -z j ≤ s := by
          dsimp [s]
          exact Finset.single_le_sum (fun k _ => neg_nonneg.mpr (hz0 k))
            (Finset.mem_univ j)
        linarith
      have : D = 0 := by simp [D, hzall]
      exact hDz this
    let p : α → ℝ := fun j => (-z j) / s
    have hp0 (j : α) : 0 ≤ p j :=
      div_nonneg (neg_nonneg.mpr (hz0 j)) hspos.le
    have hpsum : (∑ j, p j) = 1 := by
      dsimp [p, s]
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      exact mul_inv_cancel₀ hspos.ne'
    refine ⟨p, hp0, hpsum, ?_⟩
    intro i
    have hzi : D ≤ ∑ j, z j * C j i := by
      have := hL0 i
      dsimp [L] at this
      simp_rw [mul_sub] at this
      rw [Finset.sum_sub_distrib, hzrow] at this
      linarith
    calc
      (∑ j, p j * C j i) =
          -(∑ j, z j * C j i) / s := by
            dsimp [p]
            rw [div_eq_mul_inv]
            simp_rw [div_eq_mul_inv]
            calc
              (∑ j, -z j * s⁻¹ * C j i) =
                  ∑ j, (-z j * C j i) * s⁻¹ := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
              _ = (∑ j, -z j * C j i) * s⁻¹ := by
                    rw [Finset.sum_mul]
              _ = (-(∑ j, z j * C j i)) * s⁻¹ := by
                    congr 1
                    rw [← Finset.sum_neg_distrib]
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
      _ ≤ 0 := by
            have hnonpos : -(∑ j, z j * C j i) ≤ 0 := by
              linarith
            exact div_nonpos_of_nonpos_of_nonneg hnonpos hspos.le

@[blueprint "lem:finite-minimax-half"
  (statement := /-- Let \(\alpha\) be nonempty and finite, and let \(P\colon\alpha\times\alpha\to[0,\infty]\). If the bilinear extensions satisfy \(P(p,q)+P(q,p)\le1\) for every pair of mixed strategies, then there is a mixed strategy \(p\) such that \(\mathbb E_{h\sim p}P(h,c)\le\tfrac12\) for every pure strategy \(c\). -/)
  (proof := /-- Applying the hypothesis to point masses shows that every payoff is finite and at most \(1\). Form the real skew-symmetric matrix \(C(h,c)=P(h,c)-P(c,h)\). By \cref{lem:finite-skew-equilibrium}, there is a probability vector \(p\) such that the \(p\)-average of \(C(h,c)\) is nonpositive for every \(c\); hence the \(p\)-average of \(P(h,c)\) is at most the \(p\)-average of \(P(c,h)\). Apply the assumed mixed symmetry inequality to \(p\) and the point mass at \(c\). The two averages have sum at most \(1\), while the first is at most the second, so the first is at most \(\tfrac12\). -/)
  (title := /-- A finite minimax consequence of the symmetry inequality -/)
  (latexEnv := "lemma")]
lemma finite_minimax_half {α : Type v} [Fintype α] [Nonempty α]
    (payoff : α → α → ENNReal)
    (hsym : ∀ p q : PMF α,
      pmf_bilinear_payoff payoff p q +
        pmf_bilinear_payoff payoff q p ≤ 1) :
    ∃ p : PMF α, ∀ c : α,
      pmf_expectation p (fun h => payoff h c) ≤ 1 / 2 := by
  classical
  let dirac (i : α) : PMF α :=
    ⟨fun j => if j = i then 1 else 0, hasSum_ite_eq i 1⟩
  have heval (i : α) (f : α → ENNReal) :
      pmf_expectation (dirac i) f = f i := by
    change (∑' b, (if b = i then 1 else 0) * f b) = _
    rw [tsum_eq_single i]
    · simp
    · intro b hb
      simp [hb]
  have hpure (i j : α) : payoff i j + payoff j i ≤ 1 := by
    simpa [pmf_bilinear_payoff, heval] using hsym (dirac i) (dirac j)
  have hle (i j : α) : payoff i j ≤ 1 :=
    (le_add_right (le_refl (payoff i j))).trans (hpure i j)
  have hfinite (i j : α) : payoff i j ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hle i j)
  let C : α → α → ℝ :=
    fun i j => (payoff i j).toReal - (payoff j i).toReal
  have hCskew (i j : α) : C i j = -C j i := by
    dsimp [C]
    ring
  have hreal_le (i j : α) : (payoff i j).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one, ENNReal.toReal_le_toReal (hfinite i j)
      ENNReal.one_ne_top]
    exact hle i j
  have hCbound (i j : α) : |C i j| ≤ 1 := by
    rw [abs_le]
    constructor <;>
      nlinarith [(ENNReal.toReal_nonneg : 0 ≤ (payoff i j).toReal),
        (ENNReal.toReal_nonneg : 0 ≤ (payoff j i).toReal),
        hreal_le i j, hreal_le j i]
  obtain ⟨w, hw0, hwsum, hwC⟩ :=
    finite_skew_equilibrium C hCskew hCbound
  let p : PMF α :=
    ⟨fun i => ENNReal.ofReal (w i), by
      have hsum : (∑ i, ENNReal.ofReal (w i)) = 1 := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · simp [hwsum]
        · intro i hi
          exact hw0 i
      convert (Summable.of_finite :
        Summable (fun i : α => ENNReal.ofReal (w i))).hasSum using 1
      simp [tsum_fintype, hsum]⟩
  have hpexpect (f : α → ENNReal) (hf : ∀ i, f i ≠ ⊤) :
      (pmf_expectation p f).toReal =
        ∑ i, w i * (f i).toReal := by
    rw [pmf_expectation, tsum_fintype, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro i hi
      change (ENNReal.ofReal (w i) * f i).toReal =
        w i * (f i).toReal
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw0 i)]
    · intro i hi
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hf i)
  refine ⟨p, ?_⟩
  intro c
  let left := pmf_expectation p (fun h => payoff h c)
  let right := pmf_expectation p (fun h => payoff c h)
  have hleft_finite : left ≠ ⊤ := by
    dsimp [left, pmf_expectation]
    rw [tsum_fintype]
    exact ENNReal.sum_ne_top.mpr fun i hi =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite i c)
  have hright_finite : right ≠ ⊤ := by
    dsimp [right, pmf_expectation]
    rw [tsum_fintype]
    exact ENNReal.sum_ne_top.mpr fun i hi =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite c i)
  have hlr_real : left.toReal ≤ right.toReal := by
    rw [show left.toReal = ∑ i, w i * (payoff i c).toReal by
      exact hpexpect (fun i => payoff i c) (fun i => hfinite i c)]
    rw [show right.toReal = ∑ i, w i * (payoff c i).toReal by
      exact hpexpect (fun i => payoff c i) (fun i => hfinite c i)]
    have hc := hwC c
    dsimp [C] at hc
    simp_rw [mul_sub] at hc
    rw [Finset.sum_sub_distrib] at hc
    linarith
  have hlr : left ≤ right :=
    (ENNReal.toReal_le_toReal hleft_finite hright_finite).mp hlr_real
  have hsum_lr : left + right ≤ 1 := by
    simpa [left, right, pmf_bilinear_payoff, heval] using hsym p (dirac c)
  have hdouble : left + left ≤ 1 := by
    have hllr := add_le_add_left hlr left
    exact (by simpa [add_comm] using hllr : left + left ≤ left + right) |>.trans hsum_lr
  calc
    pmf_expectation p (fun h => payoff h c) =
        (pmf_expectation p (fun h => payoff h c) +
          pmf_expectation p (fun h => payoff h c)) / 2 := by
            rw [ENNReal.add_div]
            norm_num
    _ ≤ 1 / 2 := ENNReal.div_le_div_right hdouble 2

@[blueprint "lem:eq-game-value-half"
  (statement := /-- Let \(X\) be a type, let \(V\subseteq\{0,1\}^{X}\) be a nonempty finite Boolean hypothesis class, let the counterexample generator on \(V\) be symmetric, and fix a finite history of hypotheses in \(V\). Then there exists a probability mass function \(p\) on \(V\) such that, for every target \(c\in V\), the \(p\)-expected upper-game payoff against \(c\) is at most \(\tfrac12\). -/)
  (proof := /-- By \cref{lem:eq-mixed-payoff-symmetry}, the bilinear payoff on \(V\) obeys the mixed symmetry inequality for all probability mass functions. The nonemptiness of \(V\) makes its subtype of hypotheses nonempty, and the finiteness of \(V\) makes that subtype finite. Thus \cref{lem:finite-minimax-half} supplies a mixed learner strategy \(p_V\) with payoff at most \(\tfrac12\) against every pure target \(c\in V\). -/)
  (title := /-- The upper-bound game has value at most one half -/)
  (latexEnv := "lemma")]
lemma eq_game_value_half {X : Type u} (V : eq_hypothesis_class X)
    (hV : V.Finite) (hne : V.Nonempty)
    (adversary : eq_counterexample_generator X V)
    (hsym : eq_is_symmetric adversary) (history : List (eq_hypothesis V)) :
    ∃ p : PMF (eq_hypothesis V), ∀ c : eq_hypothesis V,
      pmf_expectation p (fun h => eq_payoff V adversary history h c) ≤
        1 / 2 := by
  classical
  letI : Fintype (eq_hypothesis V) := hV.fintype
  letI : Nonempty (eq_hypothesis V) :=
    ⟨⟨hne.choose, hne.choose_spec⟩⟩
  apply finite_minimax_half (payoff := eq_payoff V adversary history)
  intro p q
  exact eq_mixed_payoff_symmetry V hV adversary hsym history p q

@[blueprint "def:full-information-upper-statement"
  (statement := /-- The uniform upper-bound assertion says that there is a finite universal constant \(C\) such that, for every instance space, every nonempty finite hypothesis class \(\mathcal H\), and every symmetric adversary, some proper randomized learner has expected query count at most \(C(\operatorname{Ldim}(\mathcal H)+1)\) for every target in \(\mathcal H\). -/)
  (title := /-- Uniform linear upper bound -/)
  (latexEnv := "definition")]
def full_information_upper_statement : Prop :=
  ∃ C : ENNReal, C ≠ ⊤ ∧
    ∀ (X : Type u) (H : eq_hypothesis_class X), H.Finite → H.Nonempty →
      ∀ adversary : eq_counterexample_generator X H,
        eq_is_symmetric adversary →
        ∃ learner : eq_learning_rule X H, ∀ target : eq_hypothesis H,
          eq_expected_queries learner adversary target ≤
            C * ((littlestone_dim H : ENNReal) + 1)

@[blueprint "def:full-information-lower-statement"
  (statement := /-- The uniform lower-bound assertion says that there is a positive finite universal constant \(c\) such that every nonempty finite hypothesis class \(\mathcal H\) admits a symmetric adversary against which each proper randomized learner has some target requiring expected query count at least \(c\,\operatorname{Ldim}(\mathcal H)\). -/)
  (title := /-- Uniform linear lower bound -/)
  (latexEnv := "definition")]
def full_information_lower_statement : Prop :=
  ∃ c : ENNReal, 0 < c ∧ c ≠ ⊤ ∧
    ∀ (X : Type u) (H : eq_hypothesis_class X), H.Finite → H.Nonempty →
      ∃ adversary : eq_counterexample_generator X H,
        eq_is_symmetric adversary ∧
        ∀ learner : eq_learning_rule X H, ∃ target : eq_hypothesis H,
          c * (littlestone_dim H : ENNReal) ≤
            eq_expected_queries learner adversary target

@[blueprint "lem:full-information-dimension-le-card"
  (statement := /-- For every Boolean hypothesis class \(H\), its Littlestone dimension is at most the cardinality \(|H|\). -/)
  (proof := /-- Unfold \cref{def:littlestone-dim}. Every index in the defining finite supremum is strictly smaller than \(|H|+1\), and the value contributed at that index is either the index itself or zero. Hence every contribution is at most \(|H|\), so the supremum is as well. -/)
  (title := /-- Littlestone dimension is bounded by cardinality -/)
  (latexEnv := "lemma")]
lemma full_information_dimension_le_card {X : Type u} (H : eq_hypothesis_class X) :
    littlestone_dim H ≤ H.ncard := by
  unfold littlestone_dim
  apply Finset.sup_le
  intro d hd
  simp only [Finset.mem_range] at hd
  split <;> omega

@[blueprint "lem:full-information-shatters-own-dimension"
  (statement := /-- Every nonempty Boolean hypothesis class \(H\) shatters a mistake tree of depth \(\operatorname{Ldim}(H)\). -/)
  (proof := /-- The finite supremum in \cref{def:littlestone-dim} is attained. If its maximizing index is shattered, its contribution itself supplies the required shattered depth. Otherwise the contribution is zero; nonemptiness of \(H\) supplies a hypothesis realizing the unique path through the depth-zero tree defined by \cref{def:eq-mistake-tree,def:eq-shatters-tree,def:eq-shatters-depth}. -/)
  (title := /-- A nonempty class shatters at its dimension -/)
  (latexEnv := "lemma")]
lemma full_information_shatters_own_dimension {X : Type u}
    (H : eq_hypothesis_class X) (hH : H.Nonempty) :
    eq_shatters_depth H (littlestone_dim H) := by
  classical
  unfold littlestone_dim
  obtain ⟨d, hd, hmax⟩ := Finset.exists_mem_eq_sup
    (Finset.range (H.ncard + 1)) ⟨0, by simp⟩
    (fun n => if eq_shatters_depth H n then n else 0)
  rw [hmax]
  by_cases hs : eq_shatters_depth H d
  · simpa [hs] using hs
  · simp only [if_neg hs]
    rcases hH with ⟨f, hf⟩
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    intro bits
    refine ⟨⟨f, hf⟩, ?_⟩
    intro i
    exact Fin.elim0 i

@[blueprint "lem:full-information-dimension-mono"
  (statement := /-- Let \(K\subseteq H\) be Boolean hypothesis classes. If \(H\) is finite and \(K\) is nonempty, then \(\operatorname{Ldim}(K)\le \operatorname{Ldim}(H)\). -/)
  (proof := /-- By \cref{lem:full-information-shatters-own-dimension}, the class \(K\) shatters a tree of depth \(\operatorname{Ldim}(K)\); the inclusion \(K\subseteq H\) makes the same tree shattered by \(H\). By \cref{lem:full-information-dimension-le-card} and finite-cardinality monotonicity, this depth belongs to the finite range defining \(\operatorname{Ldim}(H)\). The supremum property in \cref{def:littlestone-dim} then gives the claimed inequality. -/)
  (title := /-- Littlestone dimension is monotone -/)
  (latexEnv := "lemma")]
lemma full_information_dimension_mono {X : Type u}
    (H K : eq_hypothesis_class X) (hH : H.Finite) (hK : K.Nonempty)
    (hsub : K ⊆ H) : littlestone_dim K ≤ littlestone_dim H := by
  classical
  have hshatter : eq_shatters_depth H (littlestone_dim K) := by
    rcases full_information_shatters_own_dimension K hK with ⟨tree, htree⟩
    refine ⟨tree, ?_⟩
    intro bits
    rcases htree bits with ⟨f, hf⟩
    exact ⟨⟨f.1, hsub f.2⟩, hf⟩
  have hcard : littlestone_dim K ≤ H.ncard := by
    exact (full_information_dimension_le_card K).trans
      (Set.ncard_le_ncard hsub hH)
  have hmem : littlestone_dim K ∈ Finset.range (H.ncard + 1) := by
    simp only [Finset.mem_range]
    omega
  have hbound := Finset.le_sup
    (f := fun n => if eq_shatters_depth H n then n else 0) hmem
  rw [if_pos hshatter] at hbound
  simpa [littlestone_dim] using hbound

@[blueprint "def:full-information-pmf-map"
  (statement := /-- The pushforward of a probability mass function \(p\) by a function \(f\) assigns to \(b\) the total \(p\)-mass of the fiber \(f^{-1}(b)\). -/)
  (title := /-- Pushforward of a probability mass function -/)
  (latexEnv := "definition")]
noncomputable def full_information_pmf_map {α : Type u} {β : Type v}
    (f : α → β) (p : PMF α) : PMF β := by
  classical
  refine ⟨fun b => ∑' a, if b = f a then p a else 0, ?_⟩
  apply ENNReal.summable.hasSum_iff.2
  rw [ENNReal.tsum_comm]
  simp [PMF.tsum_coe]

@[blueprint "lem:full-information-expectation-map"
  (statement := /-- If \(p\) is a probability mass function on \(A\), \(f:A\to B\), and \(g:B\to[0,\infty]\), then the expectation of \(g\) under the pushforward of \(p\) by \(f\) equals the expectation of \(g\circ f\) under \(p\). -/)
  (proof := /-- Expand the pushforward probability mass function and the expectation using \cref{def:pmf-expectation}. Distribute multiplication through the nonnegative sums, interchange the two sums by Tonelli's theorem, and evaluate the inner sum, whose only nonzero term is indexed by \(f(a)\). -/)
  (title := /-- Expectation under a pushed-forward probability mass function -/)
  (latexEnv := "lemma")]
lemma full_information_expectation_map {α : Type u} {β : Type v}
    (p : PMF α) (f : α → β) (g : β → ENNReal) :
    pmf_expectation (full_information_pmf_map f p) g =
      pmf_expectation p (fun a => g (f a)) := by
  classical
  change (∑' b, (∑' a, if b = f a then p a else 0) * g b) =
    ∑' a, p a * g (f a)
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  congr with a
  simp

@[blueprint "def:full-information-version-space"
  (statement := /-- Given a Boolean hypothesis class \(H\) and a full-information transcript, the associated version space consists of the hypotheses in \(H\) that agree with every recorded counterexample label. -/)
  (title := /-- Version space of a full-information transcript -/)
  (latexEnv := "definition")]
def full_information_version_space {X : Type u} (H : eq_hypothesis_class X)
    (history : eq_history X H) : eq_hypothesis_class X :=
  {f | f ∈ H ∧ ∀ feedback ∈ history, f feedback.point = feedback.label}

@[blueprint "def:full-information-embed-hypothesis"
  (statement := /-- An inclusion \(V\subseteq H\) sends each admissible hypothesis in \(V\) to the same Boolean function regarded as an admissible hypothesis in \(H\). -/)
  (title := /-- Embedding hypotheses along a class inclusion -/)
  (latexEnv := "definition")]
def full_information_embed_hypothesis {X : Type u}
    {H V : eq_hypothesis_class X} (hsub : V ⊆ H) :
    eq_hypothesis V → eq_hypothesis H :=
  fun h => ⟨h.1, hsub h.2⟩

@[blueprint "def:full-information-restricted-adversary"
  (statement := /-- Fix an original transcript and an inclusion \(V\subseteq H\). The adversary restricted to \(V\) ignores its auxiliary local history, embeds its target and proposal into \(H\), and invokes the original adversary at the fixed transcript. -/)
  (title := /-- Restricting an adversary to a version space -/)
  (latexEnv := "definition")]
def full_information_restricted_adversary {X : Type u}
    {H V : eq_hypothesis_class X} (hsub : V ⊆ H)
    (adversary : eq_counterexample_generator X H) (history : eq_history X H) :
    eq_counterexample_generator X V where
  draw := fun _ target proposed hne =>
    adversary.draw (eq_hypothesis_history history)
      (full_information_embed_hypothesis hsub target)
      (full_information_embed_hypothesis hsub proposed) (by
        intro heq
        apply hne
        apply Subtype.ext
        exact congrArg (fun z : eq_hypothesis H => z.1) heq)
  valid := by
    intro _ target proposed hne x hx
    exact adversary.valid (eq_hypothesis_history history)
      (full_information_embed_hypothesis hsub target)
      (full_information_embed_hypothesis hsub proposed) _ hx

@[blueprint "lem:full-information-restricted-symmetric"
  (statement := /-- Restricting a symmetric adversary to a version space at a fixed transcript preserves symmetry. -/)
  (proof := /-- Unfold symmetry using \cref{def:eq-is-symmetric,def:full-information-restricted-adversary}. The two restricted draws are the corresponding original draws at the fixed projected transcript, so their equality is exactly the original symmetry hypothesis after embedding the two distinct hypotheses. -/)
  (title := /-- Symmetry is preserved by version-space restriction -/)
  (latexEnv := "lemma")]
lemma full_information_restricted_symmetric {X : Type u}
    {H V : eq_hypothesis_class X} (hsub : V ⊆ H)
    (adversary : eq_counterexample_generator X H) (history : eq_history X H)
    (hsym : eq_is_symmetric adversary) :
    eq_is_symmetric (full_information_restricted_adversary hsub adversary history) := by
  intro localHistory h c hne
  simpa [full_information_restricted_adversary] using
    hsym (eq_hypothesis_history history)
      (full_information_embed_hypothesis hsub h)
      (full_information_embed_hypothesis hsub c) (by
        intro heq
        apply hne
        apply Subtype.ext
        exact congrArg (fun z : eq_hypothesis H => z.1) heq)

@[blueprint "def:full-information-pmf-dirac"
  (statement := /-- The Dirac probability mass function at \(a\) assigns mass one to \(a\) and zero to every other point. -/)
  (title := /-- Dirac probability mass function -/)
  (latexEnv := "definition")]
noncomputable def full_information_pmf_dirac {α : Type u} (a : α) : PMF α := by
  classical
  exact ⟨fun a' => if a' = a then 1 else 0, hasSum_ite_eq a (1 : ENNReal)⟩

@[blueprint "lem:full-information-expectation-add"
  (statement := /-- Expectation with respect to a probability mass function is additive for extended nonnegative real-valued functions. -/)
  (proof := /-- Expand expectation using \cref{def:pmf-expectation}, distribute each probability weight over the pointwise sum, and use additivity of nonnegative infinite sums. -/)
  (title := /-- Additivity of probability-mass-function expectation -/)
  (latexEnv := "lemma")]
lemma full_information_expectation_add {α : Type u} (p : PMF α)
    (f g : α → ENNReal) :
    pmf_expectation p (fun a => f a + g a) =
      pmf_expectation p f + pmf_expectation p g := by
  unfold pmf_expectation
  simp_rw [mul_add]
  rw [ENNReal.tsum_add]

@[blueprint "lem:full-information-expectation-mono"
  (statement := /-- Pointwise domination of extended nonnegative real-valued functions implies domination of their expectations under any probability mass function. -/)
  (proof := /-- Expand both expectations using \cref{def:pmf-expectation}. Multiplication by each nonnegative probability preserves the pointwise inequality, and monotonicity of the nonnegative infinite sum preserves it after summation. -/)
  (title := /-- Monotonicity of probability-mass-function expectation -/)
  (latexEnv := "lemma")]
lemma full_information_expectation_mono {α : Type u} (p : PMF α)
    {f g : α → ENNReal} (hfg : ∀ a, f a ≤ g a) :
    pmf_expectation p f ≤ pmf_expectation p g := by
  unfold pmf_expectation
  apply ENNReal.tsum_le_tsum
  intro a
  exact mul_le_mul_left' (hfg a) (p a)

@[blueprint "lem:full-information-expectation-const"
  (statement := /-- The expectation of a constant extended nonnegative real-valued function under a probability mass function equals that constant. -/)
  (proof := /-- By \cref{def:pmf-expectation}, the expectation is the constant times the total probability mass; the latter is one. -/)
  (title := /-- Expectation of a constant -/)
  (latexEnv := "lemma")]
lemma full_information_expectation_const {α : Type u} (p : PMF α) (c : ENNReal) :
    pmf_expectation p (fun _ => c) = c := by
  unfold pmf_expectation
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe]
  simp

@[blueprint "lem:full-information-expectation-scale"
  (statement := /-- Multiplying an extended nonnegative real-valued function by a constant multiplies its expectation by the same constant. -/)
  (proof := /-- Expand expectation using \cref{def:pmf-expectation}, commute the nonnegative factors in each summand, and factor the constant out of the infinite sum. -/)
  (title := /-- Scaling a probability-mass-function expectation -/)
  (latexEnv := "lemma")]
lemma full_information_expectation_scale {α : Type u} (p : PMF α)
    (c : ENNReal) (f : α → ENNReal) :
    pmf_expectation p (fun a => c * f a) = c * pmf_expectation p f := by
  unfold pmf_expectation
  rw [← ENNReal.tsum_mul_left]
  congr with a
  simp only
  ac_rfl

@[blueprint "lem:full-information-expectation-indicator"
  (statement := /-- The expectation of the function equal to \(c\) on an event and zero off it is \(c\) times the probability of that event. -/)
  (proof := /-- Expand expectation and event probability using \cref{def:pmf-expectation,def:pmf-event-probability}. In each summand, distribute through the event indicator and commute the nonnegative factors; then factor \(c\) out of the infinite sum. -/)
  (title := /-- Expectation of a scaled event indicator -/)
  (latexEnv := "lemma")]
lemma full_information_expectation_indicator {α : Type u} (p : PMF α)
    (event : Set α) [DecidablePred (fun a => a ∈ event)] (c : ENNReal) :
    pmf_expectation p (fun a => if a ∈ event then c else 0) =
      c * pmf_event_probability p event := by
  classical
  unfold pmf_expectation pmf_event_probability
  rw [← ENNReal.tsum_mul_left]
  congr with a
  by_cases ha : a ∈ event <;> simp [ha, mul_comm]

@[blueprint "lem:full-information-expectation-finset-sum"
  (statement := /-- Expectation commutes with a finite sum of extended nonnegative real-valued functions. -/)
  (proof := /-- Induct on the finite index set. The empty case is immediate from \cref{def:pmf-expectation}; the insertion step is \cref{lem:full-information-expectation-add} together with the induction hypothesis. -/)
  (title := /-- Expectation commutes with finite sums -/)
  (latexEnv := "lemma")]
lemma full_information_expectation_finset_sum {α : Type u} {ι : Type v}
    (p : PMF α) (s : Finset ι) (f : ι → α → ENNReal) :
    pmf_expectation p (fun a => ∑ i ∈ s, f i a) =
      ∑ i ∈ s, pmf_expectation p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pmf_expectation]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [full_information_expectation_add, ih]

@[blueprint "lem:full-information-truncated-recursion"
  (statement := /-- For a fixed learner, adversary, target, transcript, and horizon \(n\), the sum of the first \(n+1\) survival probabilities is one plus the expected sum of the first \(n\) survival probabilities after the next rejected query. A proposal equal to the target contributes zero. -/)
  (proof := /-- Separate the zero-th survival probability, which is one by \cref{def:eq-survival-probability}. Unfold the successor recursion for every remaining term. Apply \cref{lem:full-information-expectation-finset-sum} first to the learner proposal and then, on each rejected proposal, to the adversary's counterexample draw; this interchanges both expectations with the finite horizon sum. -/)
  (title := /-- Recursion for truncated expected query counts -/)
  (latexEnv := "lemma")]
lemma full_information_truncated_recursion {X : Type u}
    {H : eq_hypothesis_class X} [DecidableEq (eq_hypothesis H)]
    (learner : eq_learning_rule X H)
    (adversary : eq_counterexample_generator X H) (target : eq_hypothesis H)
    (history : eq_history X H) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
        eq_survival_probability learner adversary target history i) =
      1 + pmf_expectation (learner.choose history) (fun proposed =>
        if heq : proposed = target then 0
        else pmf_expectation
          (adversary.draw (eq_hypothesis_history history) target proposed
            (Ne.symm heq))
          (fun x => ∑ i ∈ Finset.range n,
            eq_survival_probability learner adversary target
              (history ++
                [{ hypothesis := proposed, point := x, label := target.1 x }]) i)) := by
  rw [Finset.sum_range_succ']
  simp only [eq_survival_probability]
  rw [add_comm]
  congr 1
  rw [← full_information_expectation_finset_sum]
  apply congrArg (pmf_expectation (learner.choose history))
  funext proposed
  by_cases heq : proposed = target
  · simp [heq]
  · simp only [dif_neg heq]
    rw [full_information_expectation_finset_sum]

@[blueprint "lem:full-information-upper-bound"
  (statement := /-- There exists an extended nonnegative real constant \(C\ne\infty\) such that, for every type \(X\), every finite nonempty Boolean hypothesis class \(\mathcal H\) on \(X\), and every symmetric counterexample generator on \(\mathcal H\), there is a proper randomized learning rule whose expected number of equivalence queries against every target \(c\in\mathcal H\) is at most \(C(\operatorname{Ldim}(\mathcal H)+1)\). Equivalently, the assertion in \cref{def:full-information-upper-statement} holds. -/)
  (proof := /-- Take \(C=2\) in \cref{def:full-information-upper-statement}. For a transcript \(s\), let \(V_s\) be the class from \cref{def:full-information-version-space}. Restrict the original adversary to \(V_s\) at the projected transcript as in \cref{def:full-information-restricted-adversary}; it remains symmetric by \cref{lem:full-information-restricted-symmetric}. Whenever \(V_s\) is nonempty, \cref{lem:eq-game-value-half} gives a probability mass function \(p_s\) on \(V_s\) whose expected dimension-preserving payoff against every target in \(V_s\) is at most \(1/2\). Push \(p_s\) into the original class using \cref{def:full-information-embed-hypothesis,def:full-information-pmf-map}; \cref{lem:full-information-expectation-map} identifies expectations under this pushforward. These choices define the learner. On an inconsistent, hence unreachable, transcript use the Dirac mass from \cref{def:full-information-pmf-dirac}.

Fix a target and a reachable transcript \(s\), write \(k=\operatorname{Ldim}(V_s)\), and let \(T_n(s)\) be the sum of the first \(n\) survival probabilities. We prove \(T_n(s)\le 2(k+1)\) by strong induction on \(k\) and, within it, induction on \(n\). The recursion in \cref{lem:full-information-truncated-recursion} separates the current query from the continuation. After a rejected proposal and counterexample \(x\), the target remains in the new version space, which is exactly \((V_s)_{x\to c(x)}\). Its dimension is at most \(k\) by \cref{lem:full-information-dimension-mono}. On the dimension-preserving event from \cref{def:eq-dimension-preserving-event}, the inner induction bounds the continuation by \(2(k+1)\); off that event the dimension is a natural number strictly below \(k\), so the outer induction bounds it by \(2k\). Thus the continuation is pointwise at most \(2k\) plus twice the event indicator. Applying \cref{lem:full-information-expectation-mono,lem:full-information-expectation-add,lem:full-information-expectation-const,lem:full-information-expectation-indicator} to the adversary draw expresses this bound as \(2k\) plus twice the payoff from \cref{def:eq-payoff}. Applying the same monotonicity to \(p_s\), then \cref{lem:full-information-expectation-add,lem:full-information-expectation-const,lem:full-information-expectation-scale} and the game bound, makes the expected continuation at most \(2k+1\). Adding the current query gives \(2(k+1)\), closing both inductions.

At the empty transcript, \(V_s=\mathcal H\). Every finite partial sum is therefore bounded by \(2(\operatorname{Ldim}(\mathcal H)+1)\). The partial-sum characterization of the nonnegative infinite sum in \cref{def:eq-expected-queries} yields the same bound for the expected number of queries, uniformly over the target. -/)
  (title := /-- From the local game bound to linear expected query complexity -/)
  (latexEnv := "lemma")]
lemma full_information_upper_bound : full_information_upper_statement := by
  classical
  unfold full_information_upper_statement
  refine ⟨2, by norm_num, ?_⟩
  intro X H hH hne adversary hsym
  let V : eq_history X H → eq_hypothesis_class X :=
    fun history => full_information_version_space H history
  have hsub (history : eq_history X H) : V history ⊆ H := by
    intro f hf
    exact hf.1
  have hfinite (history : eq_history X H) : (V history).Finite :=
    hH.subset (hsub history)
  let restricted (history : eq_history X H) :
      eq_counterexample_generator X (V history) :=
    full_information_restricted_adversary (hsub history) adversary history
  have hrestricted_symm (history : eq_history X H) :
      eq_is_symmetric (restricted history) := by
    exact full_information_restricted_symmetric (hsub history) adversary history hsym
  let localP (history : eq_history X H) (hV : (V history).Nonempty) :
      PMF (eq_hypothesis (V history)) :=
    Classical.choose (eq_game_value_half (V history) (hfinite history) hV
      (restricted history) (hrestricted_symm history) [])
  have localP_spec (history : eq_history X H) (hV : (V history).Nonempty) :
      ∀ c : eq_hypothesis (V history),
        pmf_expectation (localP history hV)
          (fun h => eq_payoff (V history) (restricted history) [] h c) ≤ 1 / 2 :=
    Classical.choose_spec (eq_game_value_half (V history) (hfinite history) hV
      (restricted history) (hrestricted_symm history) [])
  let fallback : eq_hypothesis H := ⟨hne.choose, hne.choose_spec⟩
  let learner : eq_learning_rule X H :=
    ⟨fun history =>
      if hV : (V history).Nonempty then
        full_information_pmf_map
          (full_information_embed_hypothesis (hsub history)) (localP history hV)
      else full_information_pmf_dirac fallback⟩
  refine ⟨learner, ?_⟩
  intro target
  have htruncated (k : ℕ) :
      ∀ (history : eq_history X H), target.1 ∈ V history →
        littlestone_dim (V history) = k → ∀ n : ℕ,
          (∑ i ∈ Finset.range n,
            eq_survival_probability learner adversary target history i) ≤
              2 * ((k : ENNReal) + 1) := by
    induction k using Nat.strong_induction_on with
    | h k hk =>
        intro history htarget hdim n
        induction n generalizing history with
        | zero => simp
        | succ n hn =>
            rw [full_information_truncated_recursion]
            have hV : (V history).Nonempty := ⟨target.1, htarget⟩
            let c : eq_hypothesis (V history) := ⟨target.1, htarget⟩
            have hc : full_information_embed_hypothesis (hsub history) c = target := by
              apply Subtype.ext
              rfl
            have hchoose : learner.choose history =
                full_information_pmf_map
                  (full_information_embed_hypothesis (hsub history))
                  (localP history hV) := by
              simp [learner, hV]
            rw [hchoose, full_information_expectation_map]
            have hpoint (h : eq_hypothesis (V history)) :
                (if heq : full_information_embed_hypothesis (hsub history) h = target
                  then 0
                  else pmf_expectation
                    (adversary.draw (eq_hypothesis_history history) target
                      (full_information_embed_hypothesis (hsub history) h)
                      (Ne.symm heq))
                    (fun x => ∑ i ∈ Finset.range n,
                      eq_survival_probability learner adversary target
                        (history ++
                          [{ hypothesis := full_information_embed_hypothesis
                              (hsub history) h, point := x, label := target.1 x }]) i)) ≤
                  2 * (k : ENNReal) +
                    2 * eq_payoff (V history) (restricted history) [] h c := by
              by_cases hh : h = c
              · subst h
                simp [hc, eq_payoff]
              · have hembed :
                    full_information_embed_hypothesis (hsub history) h ≠ target := by
                  intro heq
                  apply hh
                  apply Subtype.ext
                  exact congrArg (fun z : eq_hypothesis H => z.1) (heq.trans hc.symm)
                simp only [dif_neg hembed]
                have hdraw :
                    adversary.draw (eq_hypothesis_history history) target
                        (full_information_embed_hypothesis (hsub history) h)
                        (Ne.symm hembed) =
                      (restricted history).draw [] c h (Ne.symm hh) := by
                  rfl
                rw [hdraw]
                calc
                  pmf_expectation ((restricted history).draw [] c h (Ne.symm hh))
                      (fun x => ∑ i ∈ Finset.range n,
                        eq_survival_probability learner adversary target
                          (history ++ [{ hypothesis := full_information_embed_hypothesis (hsub history) h, point := x, label := target.1 x }]) i) ≤
                    pmf_expectation ((restricted history).draw [] c h (Ne.symm hh))
                      (fun x => 2 * (k : ENNReal) +
                        if x ∈ eq_dimension_preserving_event (V history) c
                        then 2 else 0) := by
                          apply full_information_expectation_mono
                          intro x
                          let nextHistory : eq_history X H :=
                            history ++ [{ hypothesis := full_information_embed_hypothesis (hsub history) h, point := x, label := target.1 x }]
                          have htold := htarget
                          change target.1 ∈ full_information_version_space H history at htold
                          have htarget_next : target.1 ∈ V nextHistory := by
                            change target.1 ∈
                              full_information_version_space H nextHistory
                            refine ⟨target.2, ?_⟩
                            intro feedback hfeedback
                            simp only [nextHistory, List.mem_append,
                              List.mem_singleton] at hfeedback
                            rcases hfeedback with hold | hnew
                            · exact htold.2 feedback hold
                            · subst feedback
                              rfl
                          have hversion :
                              V nextHistory = eq_version_restriction
                                (V history) x (target.1 x) := by
                            apply Set.ext
                            intro f
                            change (f ∈ H ∧ ∀ feedback ∈ nextHistory,
                              f feedback.point = feedback.label) ↔
                                ((f ∈ H ∧ ∀ feedback ∈ history,
                                  f feedback.point = feedback.label) ∧
                                    f x = target.1 x)
                            constructor
                            · rintro ⟨hfH, hall⟩
                              refine ⟨⟨hfH, ?_⟩, ?_⟩
                              · intro feedback hfeedback
                                exact hall feedback (by
                                  simp [nextHistory, hfeedback])
                              · exact hall
                                  { hypothesis :=
                                      full_information_embed_hypothesis
                                        (hsub history) h,
                                    point := x, label := target.1 x } (by
                                      simp [nextHistory])
                            · rintro ⟨⟨hfH, hall⟩, hx⟩
                              refine ⟨hfH, ?_⟩
                              intro feedback hfeedback
                              simp only [nextHistory, List.mem_append,
                                List.mem_singleton] at hfeedback
                              rcases hfeedback with hold | hnew
                              · exact hall feedback hold
                              · subst feedback
                                exact hx
                          have hnext_sub : V nextHistory ⊆ V history := by
                            intro f hf
                            rw [hversion] at hf
                            exact hf.1
                          have hdim_le : littlestone_dim (V nextHistory) ≤ k := by
                            calc
                              littlestone_dim (V nextHistory) ≤
                                  littlestone_dim (V history) :=
                                full_information_dimension_mono (V history)
                                  (V nextHistory) (hfinite history)
                                  ⟨target.1, htarget_next⟩ hnext_sub
                              _ = k := hdim
                          by_cases hpres :
                              x ∈ eq_dimension_preserving_event (V history) c
                          · have hdim_next :
                                littlestone_dim (V nextHistory) = k := by
                              rw [hversion]
                              exact hpres.trans hdim
                            calc
                              (∑ i ∈ Finset.range n,
                                  eq_survival_probability learner adversary target
                                    nextHistory i) ≤ 2 * ((k : ENNReal) + 1) :=
                                hn nextHistory htarget_next hdim_next
                              _ = 2 * (k : ENNReal) +
                                  (if x ∈ eq_dimension_preserving_event
                                    (V history) c then 2 else 0) := by
                                rw [if_pos hpres]
                                ring
                          · have hdim_ne :
                                littlestone_dim (V nextHistory) ≠ k := by
                              intro heq
                              apply hpres
                              change littlestone_dim
                                  (eq_version_restriction (V history) x (c.1 x)) =
                                littlestone_dim (V history)
                              simpa [c, hversion, hdim] using heq
                            have hdim_lt : littlestone_dim (V nextHistory) < k :=
                              lt_of_le_of_ne hdim_le hdim_ne
                            have hcast :
                                ((littlestone_dim (V nextHistory) : ℕ) : ENNReal) + 1 ≤
                                  (k : ENNReal) := by
                              exact_mod_cast (Nat.succ_le_iff.mpr hdim_lt)
                            calc
                              (∑ i ∈ Finset.range n,
                                  eq_survival_probability learner adversary target
                                    nextHistory i) ≤
                                  2 *
                                    ((littlestone_dim (V nextHistory) : ENNReal) + 1) :=
                                hk (littlestone_dim (V nextHistory)) hdim_lt
                                  nextHistory htarget_next rfl n
                              _ ≤ 2 * (k : ENNReal) :=
                                mul_le_mul_left' hcast 2
                              _ = 2 * (k : ENNReal) +
                                  (if x ∈ eq_dimension_preserving_event
                                    (V history) c then 2 else 0) := by
                                rw [if_neg hpres]
                                simp
                  _ = 2 * (k : ENNReal) +
                      2 * pmf_event_probability
                        ((restricted history).draw [] c h (Ne.symm hh))
                        (eq_dimension_preserving_event (V history) c) := by
                    rw [full_information_expectation_add,
                      full_information_expectation_const,
                      full_information_expectation_indicator]
                  _ = 2 * (k : ENNReal) +
                      2 * eq_payoff (V history) (restricted history) [] h c := by
                    simp [eq_payoff, hh]
            calc
              1 + pmf_expectation (localP history hV) (fun h =>
                    if heq : full_information_embed_hypothesis (hsub history) h =
                      target then 0
                    else pmf_expectation
                      (adversary.draw (eq_hypothesis_history history) target
                        (full_information_embed_hypothesis (hsub history) h)
                        (Ne.symm heq))
                      (fun x => ∑ i ∈ Finset.range n,
                        eq_survival_probability learner adversary target
                          (history ++ [{ hypothesis := full_information_embed_hypothesis (hsub history) h, point := x, label := target.1 x }]) i)) ≤
                  1 + pmf_expectation (localP history hV) (fun h =>
                    2 * (k : ENNReal) +
                      2 * eq_payoff (V history) (restricted history) [] h c) := by
                simpa [add_comm] using
                  add_le_add_left
                    (full_information_expectation_mono (localP history hV) hpoint) 1
              _ = 1 + (2 * (k : ENNReal) +
                    2 * pmf_expectation (localP history hV)
                      (fun h => eq_payoff (V history)
                        (restricted history) [] h c)) := by
                rw [full_information_expectation_add,
                  full_information_expectation_const,
                  full_information_expectation_scale]
              _ ≤ 1 + (2 * (k : ENNReal) + 2 * (1 / 2)) := by
                gcongr
                exact localP_spec history hV c
              _ = 2 * ((k : ENNReal) + 1) := by
                norm_num only [div_eq_mul_inv, one_mul]
                rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
                ring
  have hempty : V [] = H := by
    apply Set.ext
    intro f
    simp [V, full_information_version_space]
  have htarget_empty : target.1 ∈ V [] := by
    rw [hempty]
    exact target.2
  have hdim_empty : littlestone_dim (V []) = littlestone_dim H := by
    rw [hempty]
  unfold eq_expected_queries
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  exact htruncated (littlestone_dim H) [] htarget_empty hdim_empty n

@[blueprint "def:eq-lower-expected-from-history"
  (statement := /-- For a learner, an adversary, a target, and an initial full-information transcript, the remaining expected number of equivalence queries is the tail sum of the corresponding survival probabilities. -/)
  (title := /-- Expected remaining queries after a transcript -/)
  (latexEnv := "definition")]
noncomputable def eq_lower_expected_from_history {X : Type u}
    {H : eq_hypothesis_class X} (learner : eq_learning_rule X H)
    (adversary : eq_counterexample_generator X H) (target : eq_hypothesis H)
    (history : eq_history X H) : ENNReal :=
  ∑' n : ℕ, eq_survival_probability learner adversary target history n

@[blueprint "def:eq-lower-disagreement-point"
  (statement := /-- For two distinct hypotheses, choose a point at which their Boolean labels differ. -/)
  (title := /-- A chosen disagreement point -/)
  (latexEnv := "definition")]
noncomputable def eq_lower_disagreement_point {X : Type u}
    {H : eq_hypothesis_class X} (h c : eq_hypothesis H) (hne : h ≠ c) : X :=
  Classical.choose (show ∃ x, h.1 x ≠ c.1 x from by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hne
    apply Subtype.ext
    funext x
    exact hall x)

@[blueprint "lem:eq-lower-disagreement-point-valid"
  (statement := /-- The chosen disagreement point for two distinct hypotheses is a valid counterexample between them. -/)
  (proof := /-- This is the defining property of the choice made in \cref{def:eq-lower-disagreement-point}. -/)
  (title := /-- Validity of the chosen disagreement point -/)
  (latexEnv := "lemma")]
lemma eq_lower_disagreement_point_valid {X : Type u}
    {H : eq_hypothesis_class X} (h c : eq_hypothesis H) (hne : h ≠ c) :
    h.1 (eq_lower_disagreement_point h c hne) ≠
      c.1 (eq_lower_disagreement_point h c hne) := by
  exact Classical.choose_spec (show ∃ x, h.1 x ≠ c.1 x from by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hne
    apply Subtype.ext
    funext x
    exact hall x)

@[blueprint "lem:eq-lower-disagreement-point-symmetric"
  (statement := /-- Interchanging two distinct hypotheses does not change the chosen disagreement point. -/)
  (proof := /-- The disagreement predicates in the two orientations are equal by symmetry of inequality. Rewriting one choice problem to the other and using proof irrelevance in \cref{def:eq-lower-disagreement-point} gives the claim. -/)
  (title := /-- Symmetry of the chosen disagreement point -/)
  (latexEnv := "lemma")]
lemma eq_lower_disagreement_point_symmetric {X : Type u}
    {H : eq_hypothesis_class X} (h c : eq_hypothesis H) (hne : h ≠ c) :
    eq_lower_disagreement_point h c hne =
      eq_lower_disagreement_point c h (Ne.symm hne) := by
  unfold eq_lower_disagreement_point
  congr 1
  funext x
  apply propext
  exact ne_comm

@[blueprint "def:eq-lower-first-list-disagreement"
  (statement := /-- Given an ordered list of instances and two hypotheses, return the first listed instance on which their labels differ, if such an instance exists. -/)
  (title := /-- First disagreement in an instance list -/)
  (latexEnv := "definition")]
def eq_lower_first_list_disagreement {X : Type u}
    {H : eq_hypothesis_class X} (points : List X)
    (h c : eq_hypothesis H) : Option X :=
  match points with
  | [] => none
  | x :: xs =>
      if h.1 x = c.1 x then eq_lower_first_list_disagreement xs h c
      else some x

@[blueprint "lem:eq-lower-first-list-disagreement-valid"
  (statement := /-- Whenever the first-disagreement search returns an instance, the two hypotheses have different labels there. -/)
  (proof := /-- Induct on the ordered list in \cref{def:eq-lower-first-list-disagreement}. If the head labels differ, the returned head is valid. If they agree, apply the induction hypothesis to the tail. -/)
  (title := /-- Validity of first-disagreement search -/)
  (latexEnv := "lemma")]
lemma eq_lower_first_list_disagreement_valid {X : Type u}
    {H : eq_hypothesis_class X} (points : List X)
    (h c : eq_hypothesis H) (x : X)
    (hx : eq_lower_first_list_disagreement points h c = some x) :
    h.1 x ≠ c.1 x := by
  induction points with
  | nil => simp [eq_lower_first_list_disagreement] at hx
  | cons y ys ih =>
      by_cases heq : h.1 y = c.1 y
      · exact ih (by simpa [eq_lower_first_list_disagreement, heq] using hx)
      · have hyx : y = x := by
          simpa [eq_lower_first_list_disagreement, heq] using hx
        subst x
        exact heq

@[blueprint "lem:eq-lower-first-list-disagreement-mem"
  (statement := /-- Every instance returned by the first-disagreement search belongs to the searched list. -/)
  (proof := /-- Induct on the list in \cref{def:eq-lower-first-list-disagreement}. A returned head is a member, while a return from the tail is a member by the induction hypothesis. -/)
  (title := /-- A returned disagreement belongs to the search list -/)
  (latexEnv := "lemma")]
lemma eq_lower_first_list_disagreement_mem {X : Type u}
    {H : eq_hypothesis_class X} (points : List X) (h c : eq_hypothesis H)
    (x : X) (hx : eq_lower_first_list_disagreement points h c = some x) :
    x ∈ points := by
  induction points with
  | nil => simp [eq_lower_first_list_disagreement] at hx
  | cons y ys ih =>
      simp only [eq_lower_first_list_disagreement] at hx
      by_cases heq : h.1 y = c.1 y
      · rw [if_pos heq] at hx
        exact by simp [ih hx]
      · rw [if_neg heq] at hx
        have : y = x := Option.some.inj hx
        subst x
        simp

@[blueprint "lem:eq-lower-first-list-disagreement-symmetric"
  (statement := /-- Interchanging the two hypotheses leaves their first disagreement in an ordered instance list unchanged. -/)
  (proof := /-- Induct on the list in \cref{def:eq-lower-first-list-disagreement}; equality of the two labels is symmetric at the head, and the induction hypothesis handles the tail. -/)
  (title := /-- Symmetry of first-disagreement search -/)
  (latexEnv := "lemma")]
lemma eq_lower_first_list_disagreement_symmetric {X : Type u}
    {H : eq_hypothesis_class X} (points : List X)
    (h c : eq_hypothesis H) :
    eq_lower_first_list_disagreement points h c =
      eq_lower_first_list_disagreement points c h := by
  induction points with
  | nil => rfl
  | cons x xs ih =>
      simp only [eq_lower_first_list_disagreement]
      by_cases heq : h.1 x = c.1 x
      · rw [if_pos heq, if_pos heq.symm, ih]
      · have hne : c.1 x ≠ h.1 x := Ne.symm heq
        rw [if_neg heq, if_neg hne]

@[blueprint "lem:eq-lower-first-list-disagreement-append"
  (statement := /-- Appending one instance to a search list preserves an earlier first disagreement; if none exists, the appended instance is returned exactly when its two labels differ. -/)
  (proof := /-- Induct on the original list using \cref{def:eq-lower-first-list-disagreement}. A disagreement at the head is unchanged; when the head labels agree, apply the induction hypothesis to the tail. -/)
  (title := /-- First disagreement after appending one instance -/)
  (latexEnv := "lemma")]
lemma eq_lower_first_list_disagreement_append {X : Type u}
    {H : eq_hypothesis_class X} (points : List X) (x : X)
    (h c : eq_hypothesis H) :
    eq_lower_first_list_disagreement (points ++ [x]) h c =
      match eq_lower_first_list_disagreement points h c with
      | some y => some y
      | none => if h.1 x = c.1 x then none else some x := by
  induction points with
  | nil => rfl
  | cons y ys ih =>
      simp only [List.cons_append, eq_lower_first_list_disagreement]
      by_cases heq : h.1 y = c.1 y
      · rw [if_pos heq, ih, if_pos heq]
      · rw [if_neg heq, if_neg heq]

@[blueprint "lem:eq-lower-first-list-disagreement-congr-left"
  (statement := /-- Replacing the first hypothesis by one with identical labels on every searched instance does not change the first-disagreement result against a fixed second hypothesis. -/)
  (proof := /-- Induct on the search list in \cref{def:eq-lower-first-list-disagreement}. The agreement hypothesis identifies the two head labels, and the tail follows from the induction hypothesis. -/)
  (title := /-- First-disagreement search depends only on listed labels -/)
  (latexEnv := "lemma")]
lemma eq_lower_first_list_disagreement_congr_left {X : Type u}
    {H : eq_hypothesis_class X} (points : List X)
    (h h' c : eq_hypothesis H)
    (hagrees : ∀ x ∈ points, h.1 x = h'.1 x) :
    eq_lower_first_list_disagreement points h c =
      eq_lower_first_list_disagreement points h' c := by
  induction points with
  | nil => rfl
  | cons x xs ih =>
      simp only [eq_lower_first_list_disagreement]
      have hx := hagrees x (by simp)
      rw [hx]
      split
      · apply ih
        intro y hy
        exact hagrees y (by simp [hy])
      · rfl

@[blueprint "def:eq-lower-mistake-subtree"
  (statement := /-- The depth-\(d\) subtree below a prescribed root label of a depth-\(d+1\) mistake tree is obtained by fixing the first path coordinate to that label. -/)
  (title := /-- A rooted mistake subtree -/)
  (latexEnv := "definition")]
def eq_lower_mistake_subtree {X : Type u} {d : ℕ}
    (tree : eq_mistake_tree X (d + 1)) (label : Bool) :
    eq_mistake_tree X d :=
  fun i bits => tree i.succ (Fin.cases label bits)

@[blueprint "def:eq-lower-tree-disagreement-point"
  (statement := /-- Starting after an ordered prefix of previously exposed tree nodes, recursively choose the first node of a mistake tree on which two distinct hypotheses disagree; if their tree traces coincide, use the fixed symmetric fallback disagreement point. -/)
  (title := /-- First disagreement along a mistake tree -/)
  (latexEnv := "definition")]
noncomputable def eq_lower_tree_disagreement_point {X : Type u}
    {H : eq_hypothesis_class X} :
    (d : ℕ) → List X → eq_mistake_tree X d →
      (h c : eq_hypothesis H) → h ≠ c → X
  | 0, seen, _, h, c, hne =>
      match eq_lower_first_list_disagreement seen h c with
      | some x => x
      | none => eq_lower_disagreement_point h c hne
  | d + 1, seen, tree, h, c, hne =>
      match eq_lower_first_list_disagreement seen h c with
      | some x => x
      | none =>
          let x := tree 0 (fun i => Fin.elim0 i)
          if heq : h.1 x = c.1 x then
            eq_lower_tree_disagreement_point d (seen ++ [x])
              (eq_lower_mistake_subtree tree (h.1 x)) h c hne
          else x

@[blueprint "lem:eq-lower-tree-disagreement-point-of-prefix"
  (statement := /-- If the exposed prefix has a first disagreement, the tree disagreement procedure returns that prefix point, independently of the remaining tree. -/)
  (proof := /-- Split on the remaining depth in \cref{def:eq-lower-tree-disagreement-point} and substitute the successful prefix search. -/)
  (title := /-- A prefix disagreement has priority -/)
  (latexEnv := "lemma")]
lemma eq_lower_tree_disagreement_point_of_prefix {X : Type u}
    {H : eq_hypothesis_class X} (d : ℕ) (seen : List X)
    (tree : eq_mistake_tree X d) (h c : eq_hypothesis H) (hne : h ≠ c)
    (x : X) (hfirst : eq_lower_first_list_disagreement seen h c = some x) :
    eq_lower_tree_disagreement_point d seen tree h c hne = x := by
  cases d <;> simp [eq_lower_tree_disagreement_point, hfirst]

@[blueprint "lem:eq-lower-tree-disagreement-point-shift"
  (statement := /-- If a target labels the root of a positive-depth mistake tree by \(b\), then its first disagreement point computed in the full tree equals the point computed in the \(b\)-subtree after appending the root to the exposed prefix. -/)
  (proof := /-- Expand \cref{def:eq-lower-tree-disagreement-point}. If the old prefix already contains a disagreement, \cref{lem:eq-lower-first-list-disagreement-append} shows that the appended-prefix search returns the same point, and \cref{lem:eq-lower-tree-disagreement-point-of-prefix} reduces both tree procedures to it. Otherwise, unequal root labels make both searches return the root, while equal root labels make both recurse into the same subtree, using the target's prescribed root label. -/)
  (title := /-- Shifting the tree adversary below a realized root -/)
  (latexEnv := "lemma")]
lemma eq_lower_tree_disagreement_point_shift {X : Type u}
    {H : eq_hypothesis_class X} (d : ℕ) (seen : List X)
    (tree : eq_mistake_tree X (d + 1)) (b : Bool)
    (target proposed : eq_hypothesis H) (hne : target ≠ proposed)
    (hroot : target.1 (tree 0 (fun i => Fin.elim0 i)) = b) :
    eq_lower_tree_disagreement_point (d + 1) seen tree target proposed hne =
      eq_lower_tree_disagreement_point d
        (seen ++ [tree 0 (fun i => Fin.elim0 i)])
        (eq_lower_mistake_subtree tree b) target proposed hne := by
  cases hfirst : eq_lower_first_list_disagreement seen target proposed with
  | some x =>
      have happend : eq_lower_first_list_disagreement
          (seen ++ [tree 0 (fun i => Fin.elim0 i)]) target proposed = some x := by
        rw [eq_lower_first_list_disagreement_append, hfirst]
      calc
        _ = x := eq_lower_tree_disagreement_point_of_prefix (d + 1) seen tree
          target proposed hne x hfirst
        _ = _ := (eq_lower_tree_disagreement_point_of_prefix d
          (seen ++ [tree 0 (fun i => Fin.elim0 i)])
          (eq_lower_mistake_subtree tree b) target proposed hne x happend).symm
  | none =>
      by_cases heq :
          target.1 (tree 0 (fun i => Fin.elim0 i)) =
            proposed.1 (tree 0 (fun i => Fin.elim0 i))
      · simp only [eq_lower_tree_disagreement_point, hfirst, dif_pos heq]
        rw [hroot]
      · have happend : eq_lower_first_list_disagreement
            (seen ++ [tree 0 (fun i => Fin.elim0 i)]) target proposed =
            some (tree 0 (fun i => Fin.elim0 i)) := by
          rw [eq_lower_first_list_disagreement_append, hfirst, if_neg heq]
        rw [eq_lower_tree_disagreement_point_of_prefix d
          (seen ++ [tree 0 (fun i => Fin.elim0 i)])
          (eq_lower_mistake_subtree tree b) target proposed hne
          (tree 0 (fun i => Fin.elim0 i)) happend]
        simp only [eq_lower_tree_disagreement_point, hfirst, dif_neg heq]

@[blueprint "lem:eq-lower-tree-disagreement-point-valid"
  (statement := /-- The first tree disagreement point chosen for two distinct hypotheses is always a valid counterexample between them. -/)
  (proof := /-- Induct on the remaining depth. If the prefix search succeeds, use \cref{lem:eq-lower-first-list-disagreement-valid}. At depth zero, a failed prefix search invokes \cref{lem:eq-lower-disagreement-point-valid}. At positive depth, unequal root labels validate the root, while equal root labels reduce to the corresponding subtree and the induction hypothesis. -/)
  (title := /-- Validity of the tree disagreement point -/)
  (latexEnv := "lemma")]
lemma eq_lower_tree_disagreement_point_valid {X : Type u}
    {H : eq_hypothesis_class X} (d : ℕ) (seen : List X)
    (tree : eq_mistake_tree X d) (h c : eq_hypothesis H) (hne : h ≠ c) :
    h.1 (eq_lower_tree_disagreement_point d seen tree h c hne) ≠
      c.1 (eq_lower_tree_disagreement_point d seen tree h c hne) := by
  induction d generalizing seen with
  | zero =>
      simp only [eq_lower_tree_disagreement_point]
      cases hfirst : eq_lower_first_list_disagreement seen h c with
      | none => exact eq_lower_disagreement_point_valid h c hne
      | some x => exact eq_lower_first_list_disagreement_valid seen h c x hfirst
  | succ d ih =>
      simp only [eq_lower_tree_disagreement_point]
      cases hfirst : eq_lower_first_list_disagreement seen h c with
      | some x => exact eq_lower_first_list_disagreement_valid seen h c x hfirst
      | none =>
          simp only [hfirst]
          split
          · exact ih
              (seen ++ [tree 0 (fun i => Fin.elim0 i)])
              (eq_lower_mistake_subtree tree
                (h.1 (tree 0 (fun i => Fin.elim0 i))))
          · assumption

@[blueprint "lem:eq-lower-tree-disagreement-point-symmetric"
  (statement := /-- Interchanging two distinct hypotheses leaves their first mistake-tree disagreement point unchanged. -/)
  (proof := /-- Induct on the remaining tree depth. The prefix case follows from \cref{lem:eq-lower-first-list-disagreement-symmetric}; the depth-zero fallback follows from \cref{lem:eq-lower-disagreement-point-symmetric}. At positive depth, the root equality test is symmetric, and equal root labels select the same subtree before applying the induction hypothesis. -/)
  (title := /-- Symmetry of the tree disagreement point -/)
  (latexEnv := "lemma")]
lemma eq_lower_tree_disagreement_point_symmetric {X : Type u}
    {H : eq_hypothesis_class X} (d : ℕ) (seen : List X)
    (tree : eq_mistake_tree X d) (h c : eq_hypothesis H) (hne : h ≠ c) :
    eq_lower_tree_disagreement_point d seen tree h c hne =
      eq_lower_tree_disagreement_point d seen tree c h (Ne.symm hne) := by
  induction d generalizing seen with
  | zero =>
      simp only [eq_lower_tree_disagreement_point]
      rw [eq_lower_first_list_disagreement_symmetric seen h c]
      cases eq_lower_first_list_disagreement seen c h with
      | none => exact eq_lower_disagreement_point_symmetric h c hne
      | some x => rfl
  | succ d ih =>
      simp only [eq_lower_tree_disagreement_point]
      rw [eq_lower_first_list_disagreement_symmetric seen h c]
      cases hfirst : eq_lower_first_list_disagreement seen c h with
      | some x => rfl
      | none =>
          simp only [hfirst]
          by_cases heq :
              h.1 (tree 0 (fun i => Fin.elim0 i)) =
                c.1 (tree 0 (fun i => Fin.elim0 i))
          · simp only [dif_pos heq, dif_pos heq.symm]
            convert ih
              (seen ++ [tree 0 (fun i => Fin.elim0 i)])
              (eq_lower_mistake_subtree tree
                (h.1 (tree 0 (fun i => Fin.elim0 i)))) using 1
            rw [← heq]
          · simp only [dif_neg heq, dif_neg (Ne.symm heq)]

@[blueprint "def:eq-lower-point-mass"
  (statement := /-- The point mass at an element \(a\) assigns mass \(1\) to \(a\) and mass \(0\) to every other element. -/)
  (title := /-- A point probability mass function -/)
  (latexEnv := "definition")]
noncomputable def eq_lower_point_mass {α : Type v} (a : α) : PMF α := by
  classical
  exact ⟨fun a' => if a' = a then 1 else 0, hasSum_ite_eq _ _⟩

@[blueprint "lem:eq-lower-point-mass-expectation"
  (statement := /-- The expectation of a nonnegative function under a point mass is its value at the atom. -/)
  (proof := /-- Expand \cref{def:pmf-expectation} and \cref{def:eq-lower-point-mass}; every summand except the atom is zero, and the atom has mass one. -/)
  (title := /-- Expectation under a point mass -/)
  (latexEnv := "lemma")]
lemma eq_lower_point_mass_expectation {α : Type v} (a : α) (f : α → ENNReal) :
    pmf_expectation (eq_lower_point_mass a) f = f a := by
  classical
  unfold pmf_expectation
  change (∑' a', (if a' = a then 1 else 0) * f a') = f a
  simp

@[blueprint "lem:eq-lower-pmf-expectation-add"
  (statement := /-- Expectation of a sum of two nonnegative extended-real functions under a probability mass function is the sum of their expectations. -/)
  (proof := /-- Expand \cref{def:pmf-expectation}, distribute each probability mass over the pointwise sum, and apply additivity of nonnegative infinite sums. -/)
  (title := /-- Additivity of discrete expectation -/)
  (latexEnv := "lemma")]
lemma eq_lower_pmf_expectation_add {α : Type v} (p : PMF α)
    (f g : α → ENNReal) :
    pmf_expectation p (fun a => f a + g a) =
      pmf_expectation p f + pmf_expectation p g := by
  unfold pmf_expectation
  simp only [mul_add, ENNReal.tsum_add]

@[blueprint "lem:eq-lower-pmf-expectation-div"
  (statement := /-- Dividing a nonnegative extended-real function by a constant commutes with expectation under a probability mass function. -/)
  (proof := /-- Write division as multiplication by the inverse, reassociate each summand in \cref{def:pmf-expectation}, and move the common right factor outside the nonnegative infinite sum. -/)
  (title := /-- Constant division commutes with discrete expectation -/)
  (latexEnv := "lemma")]
lemma eq_lower_pmf_expectation_div {α : Type v} (p : PMF α)
    (f : α → ENNReal) (c : ENNReal) :
    pmf_expectation p (fun a => f a / c) = pmf_expectation p f / c := by
  unfold pmf_expectation
  simp only [div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right]

@[blueprint "lem:eq-lower-pmf-expectation-const"
  (statement := /-- The expectation of a constant nonnegative extended-real function under a probability mass function is that constant. -/)
  (proof := /-- In \cref{def:pmf-expectation}, factor the constant out of the nonnegative infinite sum and use that the probability masses sum to one. -/)
  (title := /-- Expectation of a constant -/)
  (latexEnv := "lemma")]
lemma eq_lower_pmf_expectation_const {α : Type v} (p : PMF α) (c : ENNReal) :
    pmf_expectation p (fun _ => c) = c := by
  unfold pmf_expectation
  rw [ENNReal.tsum_mul_right]
  have hp : (∑' i : α, (p i : ENNReal)) = 1 := p.property.tsum_eq
  simpa [hp]

@[blueprint "lem:eq-lower-pmf-expectation-mono"
  (statement := /-- Discrete expectation is monotone for pointwise ordered nonnegative extended-real functions. -/)
  (proof := /-- Multiply the pointwise inequality by each nonnegative probability mass and apply monotonicity of nonnegative infinite sums in \cref{def:pmf-expectation}. -/)
  (title := /-- Monotonicity of discrete expectation -/)
  (latexEnv := "lemma")]
lemma eq_lower_pmf_expectation_mono {α : Type v} (p : PMF α)
    (f g : α → ENNReal) (hfg : ∀ a, f a ≤ g a) :
    pmf_expectation p f ≤ pmf_expectation p g := by
  unfold pmf_expectation
  apply ENNReal.tsum_le_tsum
  intro a
  exact mul_le_mul_left' (hfg a) (p a)

@[blueprint "def:eq-lower-forced-learning-rule"
  (statement := /-- Given an initial transcript and a hypothesis, the forced-first learning rule proposes that hypothesis at every transcript of the same length and otherwise follows the original learner. In particular, after the next rejection it follows the original learner. -/)
  (title := /-- A learner with a forced next proposal -/)
  (latexEnv := "definition")]
noncomputable def eq_lower_forced_learning_rule {X : Type u}
    {H : eq_hypothesis_class X} (learner : eq_learning_rule X H)
    (history : eq_history X H) (proposed : eq_hypothesis H) :
    eq_learning_rule X H where
  choose history' :=
    if history'.length = history.length then eq_lower_point_mass proposed
    else learner.choose history'

@[blueprint "lem:eq-lower-forced-learning-rule-after"
  (statement := /-- Once a transcript is longer than the forcing transcript, the survival probabilities of the forced-first learner equal those of the original learner. -/)
  (proof := /-- Induct on the survival horizon using \cref{def:eq-survival-probability}. At the current and every extended transcript, the length is strictly larger than the forcing length, so \cref{def:eq-lower-forced-learning-rule} selects the original learner distribution; apply the induction hypothesis after each rejected feedback. -/)
  (title := /-- A forced-first learner follows the original after rejection -/)
  (latexEnv := "lemma")]
lemma eq_lower_forced_learning_rule_after {X : Type u}
    {H : eq_hypothesis_class X} (learner : eq_learning_rule X H)
    (initial : eq_history X H) (proposed : eq_hypothesis H)
    (adversary : eq_counterexample_generator X H) (target : eq_hypothesis H)
    (history : eq_history X H) (hlength : initial.length < history.length)
    (n : ℕ) :
    eq_survival_probability (eq_lower_forced_learning_rule learner initial proposed)
        adversary target history n =
      eq_survival_probability learner adversary target history n := by
  induction n generalizing history with
  | zero => rfl
  | succ n ih =>
      classical
      have hlenne : history.length ≠ initial.length := Nat.ne_of_gt hlength
      change pmf_expectation
          ((eq_lower_forced_learning_rule learner initial proposed).choose history) _ =
        pmf_expectation (learner.choose history) _
      rw [show (eq_lower_forced_learning_rule learner initial proposed).choose history =
          learner.choose history by
        simp [eq_lower_forced_learning_rule, hlenne]]
      apply congrArg
      funext h
      split
      · rfl
      · apply congrArg
        funext x
        change eq_survival_probability
            (eq_lower_forced_learning_rule learner initial proposed) adversary target
              (history ++ [{ hypothesis := h, point := x, label := target.1 x }]) n =
          eq_survival_probability learner adversary target
            (history ++ [{ hypothesis := h, point := x, label := target.1 x }]) n
        apply ih
        simp only [List.length_append, List.length_singleton]
        omega

@[blueprint "lem:eq-lower-survival-as-forced-average"
  (statement := /-- A learner's survival probability from a transcript is the expectation, over its next proposal, of the survival probability of the learner forced to make that proposal next. -/)
  (proof := /-- For horizon zero, both sides are one because the learner distribution has total mass one. At a positive horizon, expand \cref{def:eq-survival-probability}. The forced learner's first distribution is the point mass from \cref{def:eq-lower-forced-learning-rule}, whose expectation is evaluated by \cref{lem:eq-lower-point-mass-expectation}; after a rejection, \cref{lem:eq-lower-forced-learning-rule-after} identifies its continuation with the original learner. -/)
  (title := /-- Survival as an average of forced proposals -/)
  (latexEnv := "lemma")]
lemma eq_lower_survival_as_forced_average {X : Type u}
    {H : eq_hypothesis_class X} (learner : eq_learning_rule X H)
    (adversary : eq_counterexample_generator X H) (target : eq_hypothesis H)
    (history : eq_history X H) (n : ℕ) :
    eq_survival_probability learner adversary target history n =
      pmf_expectation (learner.choose history) (fun proposed =>
        eq_survival_probability
          (eq_lower_forced_learning_rule learner history proposed)
          adversary target history n) := by
  classical
  cases n with
  | zero =>
      change 1 = pmf_expectation (learner.choose history) (fun _ => 1)
      unfold pmf_expectation
      simp only [mul_one]
      exact (learner.choose history).property.tsum_eq.symm
  | succ n =>
      change pmf_expectation (learner.choose history) _ =
        pmf_expectation (learner.choose history) _
      apply congrArg
      funext proposed
      change (if heq : proposed = target then 0 else
          pmf_expectation
            (adversary.draw (eq_hypothesis_history history) target proposed
              (Ne.symm heq))
            (fun x => eq_survival_probability learner adversary target
              (history ++
                [{ hypothesis := proposed, point := x, label := target.1 x }]) n)) =
        eq_survival_probability
          (eq_lower_forced_learning_rule learner history proposed)
          adversary target history (n + 1)
      change _ = pmf_expectation
        ((eq_lower_forced_learning_rule learner history proposed).choose history) _
      rw [show (eq_lower_forced_learning_rule learner history proposed).choose history =
          eq_lower_point_mass proposed by
        simp [eq_lower_forced_learning_rule]]
      rw [eq_lower_point_mass_expectation]
      split
      · rfl
      · apply congrArg
        funext x
        exact (eq_lower_forced_learning_rule_after learner history proposed
          adversary target
          (history ++ [{ hypothesis := proposed, point := x, label := target.1 x }])
          (by simp only [List.length_append, List.length_singleton]; omega) n).symm

@[blueprint "def:eq-lower-tree-adversary"
  (statement := /-- A mistake tree and an ordered prefix determine a history-independent randomized counterexample generator concentrated at the first tree disagreement point of the target and proposal. -/)
  (title := /-- The first-disagreement tree adversary -/)
  (latexEnv := "definition")]
noncomputable def eq_lower_tree_adversary {X : Type u}
    {H : eq_hypothesis_class X} (d : ℕ) (seen : List X)
    (tree : eq_mistake_tree X d) : eq_counterexample_generator X H := by
  classical
  refine
    { draw := fun _ target proposed hne =>
        eq_lower_point_mass
          (eq_lower_tree_disagreement_point d seen tree target proposed hne)
      valid := ?_ }
  intro history target proposed hne x hx
  change eq_lower_point_mass
    (eq_lower_tree_disagreement_point d seen tree target proposed hne) x ≠ 0 at hx
  have hx' : x = eq_lower_tree_disagreement_point d seen tree target proposed hne := by
    by_contra hxp
    apply hx
    change (if x = eq_lower_tree_disagreement_point d seen tree target proposed hne
      then 1 else 0) = 0
    simp [hxp]
  subst x
  exact Ne.symm
    (eq_lower_tree_disagreement_point_valid d seen tree target proposed hne)

@[blueprint "lem:eq-lower-tree-adversary-draw"
  (statement := /-- The first-disagreement tree adversary's counterexample distribution is the point mass at its selected tree disagreement point. -/)
  (proof := /-- This is the draw field of \cref{def:eq-lower-tree-adversary}. -/)
  (title := /-- Draw distribution of the tree adversary -/)
  (latexEnv := "lemma")]
lemma eq_lower_tree_adversary_draw {X : Type u}
    {H : eq_hypothesis_class X} (d : ℕ) (seen : List X)
    (tree : eq_mistake_tree X d) (history : List (eq_hypothesis H))
    (target proposed : eq_hypothesis H) (hne : target ≠ proposed) :
    (eq_lower_tree_adversary d seen tree).draw history target proposed hne =
      eq_lower_point_mass
        (eq_lower_tree_disagreement_point d seen tree target proposed hne) := by
  rfl

@[blueprint "lem:eq-lower-tree-adversary-symmetric"
  (statement := /-- The first-disagreement tree adversary is symmetric for every mistake tree and every ordered prefix. -/)
  (proof := /-- The generator in \cref{def:eq-lower-tree-adversary} is a point mass. Its two orientations have the same atom by \cref{lem:eq-lower-tree-disagreement-point-symmetric}, and hence the probability mass functions coincide. -/)
  (title := /-- Symmetry of the first-disagreement tree adversary -/)
  (latexEnv := "lemma")]
lemma eq_lower_tree_adversary_symmetric {X : Type u}
    {H : eq_hypothesis_class X} (d : ℕ) (seen : List X)
    (tree : eq_mistake_tree X d) :
    eq_is_symmetric (eq_lower_tree_adversary d seen tree :
      eq_counterexample_generator X H) := by
  intro history h c hne
  simp only [eq_lower_tree_adversary]
  congr 1
  exact eq_lower_tree_disagreement_point_symmetric d seen tree h c hne

@[blueprint "lem:eq-lower-tree-survival-shift"
  (statement := /-- For a target realizing a prescribed root label, survival probabilities under the full-tree adversary equal those under the corresponding subtree adversary with the root appended to the exposed prefix. -/)
  (proof := /-- Induct on the survival horizon in \cref{def:eq-survival-probability}. The learner distribution and acceptance test coincide. For a rejected proposal, \cref{lem:eq-lower-tree-disagreement-point-shift} identifies the atoms of the two point-mass counterexample distributions, and the induction hypothesis identifies the continuation survival probabilities after the common feedback. -/)
  (title := /-- Survival is invariant under a realized-root shift -/)
  (latexEnv := "lemma")]
lemma eq_lower_tree_survival_shift {X : Type u}
    {H : eq_hypothesis_class X} (d : ℕ) (seen : List X)
    (tree : eq_mistake_tree X (d + 1)) (b : Bool)
    (target : eq_hypothesis H)
    (hroot : target.1 (tree 0 (fun i => Fin.elim0 i)) = b)
    (learner : eq_learning_rule X H) (history : eq_history X H) (n : ℕ) :
    eq_survival_probability learner (eq_lower_tree_adversary (d + 1) seen tree)
        target history n =
      eq_survival_probability learner
        (eq_lower_tree_adversary d
          (seen ++ [tree 0 (fun i => Fin.elim0 i)])
          (eq_lower_mistake_subtree tree b)) target history n := by
  induction n generalizing history with
  | zero => rfl
  | succ n ih =>
      classical
      change pmf_expectation (learner.choose history) _ =
        pmf_expectation (learner.choose history) _
      apply congrArg
      funext proposed
      split
      · rfl
      · rename_i hne
        have hpoint := eq_lower_tree_disagreement_point_shift d seen tree b
          target proposed (Ne.symm hne) hroot
        simp only [eq_lower_tree_adversary]
        rw [hpoint]
        apply congrArg
        funext x
        exact ih (history ++
          [{ hypothesis := proposed, point := x, label := target.1 x }])

@[blueprint "def:eq-lower-cube-average"
  (statement := /-- Recursively average a nonnegative extended-real function over the \(2^d\) Boolean paths of length \(d\), assigning equal weight to the two root labels at every level. -/)
  (title := /-- Uniform average over Boolean paths -/)
  (latexEnv := "definition")]
noncomputable def eq_lower_cube_average :
    (d : ℕ) → ((Fin d → Bool) → ENNReal) → ENNReal
  | 0, f => f (fun i => Fin.elim0 i)
  | d + 1, f =>
      (eq_lower_cube_average d (fun bits => f (Fin.cases false bits)) +
        eq_lower_cube_average d (fun bits => f (Fin.cases true bits))) / 2

@[blueprint "lem:eq-lower-cube-average-expectation"
  (statement := /-- Uniform averaging over Boolean paths commutes with expectation under a probability mass function. -/)
  (proof := /-- Induct on the cube dimension in \cref{def:eq-lower-cube-average}. The zero-dimensional case is immediate. At a root, apply the induction hypothesis to both branches, combine them by \cref{lem:eq-lower-pmf-expectation-add}, and move division by two through the expectation using \cref{lem:eq-lower-pmf-expectation-div}. -/)
  (title := /-- Boolean-cube averages commute with expectation -/)
  (latexEnv := "lemma")]
lemma eq_lower_cube_average_expectation {α : Type v} (p : PMF α) (d : ℕ)
    (f : α → (Fin d → Bool) → ENNReal) :
    eq_lower_cube_average d (fun bits => pmf_expectation p (fun a => f a bits)) =
      pmf_expectation p (fun a => eq_lower_cube_average d (fun bits => f a bits)) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [eq_lower_cube_average]
      rw [ih, ih]
      rw [← eq_lower_pmf_expectation_add]
      rw [← eq_lower_pmf_expectation_div]

@[blueprint "lem:eq-lower-cube-average-const"
  (statement := /-- The uniform Boolean-cube average of a constant function is that constant. -/)
  (proof := /-- Induct on the cube dimension in \cref{def:eq-lower-cube-average}; at each root the two branch averages equal the same constant, whose arithmetic mean is itself. -/)
  (title := /-- Average of a constant on the Boolean cube -/)
  (latexEnv := "lemma")]
lemma eq_lower_cube_average_const (d : ℕ) (c : ENNReal) :
    eq_lower_cube_average d (fun _ => c) = c := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [eq_lower_cube_average, ih]
      change (c + c) * 2⁻¹ = c
      rw [add_mul, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]

@[blueprint "lem:eq-lower-cube-average-add"
  (statement := /-- The uniform Boolean-cube average of a pointwise sum is the sum of the two uniform averages. -/)
  (proof := /-- Induct on the dimension in \cref{def:eq-lower-cube-average}. Apply the induction hypothesis in both root branches and rearrange the four nonnegative terms before distributing division by two. -/)
  (title := /-- Additivity of the Boolean-cube average -/)
  (latexEnv := "lemma")]
lemma eq_lower_cube_average_add (d : ℕ)
    (f g : (Fin d → Bool) → ENNReal) :
    eq_lower_cube_average d (fun bits => f bits + g bits) =
      eq_lower_cube_average d f + eq_lower_cube_average d g := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [eq_lower_cube_average, ih]
      change ((eq_lower_cube_average d (fun bits => f (Fin.cases false bits)) +
          eq_lower_cube_average d (fun bits => g (Fin.cases false bits))) +
        (eq_lower_cube_average d (fun bits => f (Fin.cases true bits)) +
          eq_lower_cube_average d (fun bits => g (Fin.cases true bits)))) / 2 = _
      simp only [div_eq_mul_inv, add_mul]
      ac_rfl

@[blueprint "lem:eq-lower-cube-average-attained"
  (statement := /-- A function on the finite Boolean cube has a value at least as large as its uniform recursive average. -/)
  (proof := /-- Induct on the dimension in \cref{def:eq-lower-cube-average}. In dimension zero there is one path. At positive dimension, one of the two branch averages is at least their arithmetic mean; apply the induction hypothesis in that branch and prepend its root label. -/)
  (title := /-- A Boolean-cube average is bounded by a value -/)
  (latexEnv := "lemma")]
lemma eq_lower_cube_average_attained (d : ℕ)
    (f : (Fin d → Bool) → ENNReal) :
    ∃ bits : Fin d → Bool, eq_lower_cube_average d f ≤ f bits := by
  induction d with
  | zero =>
      exact ⟨fun i => Fin.elim0 i, le_rfl⟩
  | succ d ih =>
      let a := eq_lower_cube_average d (fun bits => f (Fin.cases false bits))
      let b := eq_lower_cube_average d (fun bits => f (Fin.cases true bits))
      rcases le_total a b with hab | hba
      · obtain ⟨bits, hbits⟩ := ih (fun bits => f (Fin.cases true bits))
        refine ⟨Fin.cases true bits, ?_⟩
        refine le_trans ?_ hbits
        change (a + b) / 2 ≤ b
        calc
          (a + b) / 2 ≤ (b + b) / 2 := by gcongr
          _ = b := by
            change (b + b) * 2⁻¹ = b
            rw [add_mul, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
      · obtain ⟨bits, hbits⟩ := ih (fun bits => f (Fin.cases false bits))
        refine ⟨Fin.cases false bits, ?_⟩
        refine le_trans ?_ hbits
        change (a + b) / 2 ≤ a
        calc
          (a + b) / 2 ≤ (a + a) / 2 := by gcongr
          _ = a := by
            change (a + a) * 2⁻¹ = a
            rw [add_mul, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]

@[blueprint "def:eq-lower-tree-target"
  (statement := /-- For every Boolean path through a shattered mistake tree, choose one hypothesis in the class that realizes that path. -/)
  (title := /-- A chosen target for each shattered path -/)
  (latexEnv := "definition")]
noncomputable def eq_lower_tree_target {X : Type u}
    {H : eq_hypothesis_class X} {d : ℕ} (tree : eq_mistake_tree X d)
    (hshatter : eq_shatters_tree H tree) (bits : Fin d → Bool) :
    eq_hypothesis H :=
  Classical.choose (hshatter bits)

@[blueprint "lem:eq-lower-tree-target-realizes"
  (statement := /-- The target selected for a path through a shattered mistake tree labels every queried node by the corresponding path bit. -/)
  (proof := /-- This is the defining property of the choice in \cref{def:eq-lower-tree-target}, obtained from the shattering witness \cref{def:eq-shatters-tree}. -/)
  (title := /-- The selected target realizes its path -/)
  (latexEnv := "lemma")]
lemma eq_lower_tree_target_realizes {X : Type u}
    {H : eq_hypothesis_class X} {d : ℕ} (tree : eq_mistake_tree X d)
    (hshatter : eq_shatters_tree H tree) (bits : Fin d → Bool)
    (i : Fin d) :
    (eq_lower_tree_target tree hshatter bits).1 (eq_tree_path tree bits i) =
      bits i := by
  exact (Classical.choose_spec (hshatter bits)) i

@[blueprint "def:eq-lower-truncated-queries"
  (statement := /-- The \(N\)-truncated remaining query count is the sum of the first \(N\) survival probabilities from a prescribed transcript. -/)
  (title := /-- Truncated expected remaining queries -/)
  (latexEnv := "definition")]
noncomputable def eq_lower_truncated_queries {X : Type u}
    {H : eq_hypothesis_class X} (learner : eq_learning_rule X H)
    (adversary : eq_counterexample_generator X H) (target : eq_hypothesis H)
    (history : eq_history X H) (fuel : ℕ) : ENNReal :=
  ∑ n ∈ Finset.range fuel,
    eq_survival_probability learner adversary target history n

@[blueprint "lem:eq-lower-truncated-queries-step"
  (statement := /-- A positive truncation is one plus the finite sum of the shifted positive-index survival probabilities. -/)
  (proof := /-- Apply the successor-range identity to \cref{def:eq-lower-truncated-queries}; the separated zeroth survival probability is \(1\) by \cref{def:eq-survival-probability}. -/)
  (title := /-- First-step decomposition of a truncated query count -/)
  (latexEnv := "lemma")]
lemma eq_lower_truncated_queries_step {X : Type u}
    {H : eq_hypothesis_class X} (learner : eq_learning_rule X H)
    (adversary : eq_counterexample_generator X H) (target : eq_hypothesis H)
    (history : eq_history X H) (fuel : ℕ) :
    eq_lower_truncated_queries learner adversary target history (fuel + 1) =
      1 + ∑ n ∈ Finset.range fuel,
        eq_survival_probability learner adversary target history (n + 1) := by
  unfold eq_lower_truncated_queries
  rw [Finset.sum_range_succ']
  simp [eq_survival_probability, add_comm]

@[blueprint "lem:eq-lower-truncated-queries-le-expected"
  (statement := /-- Every finite truncation of the survival tail sum is bounded above by the full remaining expected query count. -/)
  (proof := /-- Each summand is nonnegative, so the finite partial sum in \cref{def:eq-lower-truncated-queries} is at most the full infinite sum in \cref{def:eq-lower-expected-from-history}. -/)
  (title := /-- Truncated query counts are bounded by expectation -/)
  (latexEnv := "lemma")]
lemma eq_lower_truncated_queries_le_expected {X : Type u}
    {H : eq_hypothesis_class X} (learner : eq_learning_rule X H)
    (adversary : eq_counterexample_generator X H) (target : eq_hypothesis H)
    (history : eq_history X H) (fuel : ℕ) :
    eq_lower_truncated_queries learner adversary target history fuel ≤
      eq_lower_expected_from_history learner adversary target history := by
  unfold eq_lower_truncated_queries eq_lower_expected_from_history
  exact ENNReal.sum_le_tsum (Finset.range fuel)

@[blueprint "lem:eq-lower-truncated-as-forced-average"
  (statement := /-- A learner's truncated query count is the expectation, over its next proposal, of the truncated query count of the corresponding forced-first learner. -/)
  (proof := /-- Expand \cref{def:eq-lower-truncated-queries}, replace each survival probability by \cref{lem:eq-lower-survival-as-forced-average}, and commute the finite time sum with the nonnegative sum defining \cref{def:pmf-expectation}. -/)
  (title := /-- Truncated queries as an average of forced proposals -/)
  (latexEnv := "lemma")]
lemma eq_lower_truncated_as_forced_average {X : Type u}
    {H : eq_hypothesis_class X} (learner : eq_learning_rule X H)
    (adversary : eq_counterexample_generator X H) (target : eq_hypothesis H)
    (history : eq_history X H) (fuel : ℕ) :
    eq_lower_truncated_queries learner adversary target history fuel =
      pmf_expectation (learner.choose history) (fun proposed =>
        eq_lower_truncated_queries
          (eq_lower_forced_learning_rule learner history proposed)
          adversary target history fuel) := by
  unfold eq_lower_truncated_queries
  calc
    (∑ n ∈ Finset.range fuel,
        eq_survival_probability learner adversary target history n) =
        ∑ n ∈ Finset.range fuel,
          pmf_expectation (learner.choose history) (fun proposed =>
            eq_survival_probability
              (eq_lower_forced_learning_rule learner history proposed)
              adversary target history n) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact eq_lower_survival_as_forced_average learner adversary target history n
    _ = pmf_expectation (learner.choose history) (fun proposed =>
          ∑ n ∈ Finset.range fuel,
            eq_survival_probability
              (eq_lower_forced_learning_rule learner history proposed)
              adversary target history n) := by
      unfold pmf_expectation
      generalize Finset.range fuel = s
      induction s using Finset.induction_on with
      | empty => simp
      | insert n s hn ih =>
          simp only [Finset.sum_insert hn, mul_add, ENNReal.tsum_add]
          rw [ih]

@[blueprint "lem:eq-lower-forced-truncated-step"
  (statement := /-- If the forced next proposal is not the target, its positive truncated query count is one plus the adversary-average truncated continuation count of the original learner. -/)
  (proof := /-- Apply \cref{lem:eq-lower-truncated-queries-step}. At each positive survival index, \cref{def:eq-lower-forced-learning-rule} and \cref{lem:eq-lower-point-mass-expectation} fix the first proposal; the inequality hypothesis selects the rejection branch, and \cref{lem:eq-lower-forced-learning-rule-after} replaces the subsequent forced learner by the original learner. Finally commute the finite time sum with the nonnegative counterexample expectation. -/)
  (title := /-- First-step equation for a rejected forced proposal -/)
  (latexEnv := "lemma")]
lemma eq_lower_forced_truncated_step {X : Type u}
    {H : eq_hypothesis_class X} (learner : eq_learning_rule X H)
    (history : eq_history X H) (proposed target : eq_hypothesis H)
    (hne : proposed ≠ target) (adversary : eq_counterexample_generator X H)
    (fuel : ℕ) :
    eq_lower_truncated_queries
        (eq_lower_forced_learning_rule learner history proposed)
        adversary target history (fuel + 1) =
      1 + pmf_expectation
        (adversary.draw (eq_hypothesis_history history) target proposed
          (Ne.symm hne))
        (fun x => eq_lower_truncated_queries learner adversary target
          (history ++
            [{ hypothesis := proposed, point := x, label := target.1 x }]) fuel) := by
  classical
  rw [eq_lower_truncated_queries_step]
  congr 1
  calc
    (∑ n ∈ Finset.range fuel,
        eq_survival_probability
          (eq_lower_forced_learning_rule learner history proposed)
          adversary target history (n + 1)) =
        ∑ n ∈ Finset.range fuel,
          pmf_expectation
            (adversary.draw (eq_hypothesis_history history) target proposed
              (Ne.symm hne))
            (fun x => eq_survival_probability learner adversary target
              (history ++
                [{ hypothesis := proposed, point := x, label := target.1 x }]) n) := by
      apply Finset.sum_congr rfl
      intro n hn
      change pmf_expectation
          ((eq_lower_forced_learning_rule learner history proposed).choose history) _ = _
      rw [show (eq_lower_forced_learning_rule learner history proposed).choose history =
          eq_lower_point_mass proposed by simp [eq_lower_forced_learning_rule]]
      rw [eq_lower_point_mass_expectation]
      simp only [dif_neg hne]
      apply congrArg
      funext x
      exact eq_lower_forced_learning_rule_after learner history proposed
        adversary target
        (history ++ [{ hypothesis := proposed, point := x, label := target.1 x }])
        (by simp only [List.length_append, List.length_singleton]; omega) n
    _ = pmf_expectation
          (adversary.draw (eq_hypothesis_history history) target proposed
            (Ne.symm hne))
          (fun x => ∑ n ∈ Finset.range fuel,
            eq_survival_probability learner adversary target
              (history ++
                [{ hypothesis := proposed, point := x, label := target.1 x }]) n) := by
      unfold pmf_expectation
      generalize Finset.range fuel = s
      induction s using Finset.induction_on with
      | empty => simp
      | insert n s hn ih =>
          simp only [Finset.sum_insert hn, mul_add, ENNReal.tsum_add]
          rw [ih]

@[blueprint "lem:eq-lower-tree-truncated-shift"
  (statement := /-- For a target realizing a prescribed root label, every finite truncated query count under the full-tree adversary equals the corresponding count under the appended-prefix subtree adversary. -/)
  (proof := /-- Expand \cref{def:eq-lower-truncated-queries} and apply \cref{lem:eq-lower-tree-survival-shift} to every survival-probability summand. -/)
  (title := /-- Truncated queries are invariant under a realized-root shift -/)
  (latexEnv := "lemma")]
lemma eq_lower_tree_truncated_shift {X : Type u}
    {H : eq_hypothesis_class X} (d fuel : ℕ) (seen : List X)
    (tree : eq_mistake_tree X (d + 1)) (b : Bool)
    (target : eq_hypothesis H)
    (hroot : target.1 (tree 0 (fun i => Fin.elim0 i)) = b)
    (learner : eq_learning_rule X H) (history : eq_history X H) :
    eq_lower_truncated_queries learner (eq_lower_tree_adversary (d + 1) seen tree)
        target history fuel =
      eq_lower_truncated_queries learner
        (eq_lower_tree_adversary d
          (seen ++ [tree 0 (fun i => Fin.elim0 i)])
          (eq_lower_mistake_subtree tree b)) target history fuel := by
  unfold eq_lower_truncated_queries
  apply Finset.sum_congr rfl
  intro n hn
  exact eq_lower_tree_survival_shift d seen tree b target hroot learner history n

@[blueprint "lem:eq-lower-tree-truncated-average"
  (statement := /-- Suppose that a family of targets realizes all paths of a depth-\(d\) mistake tree and that all targets agree on an ordered exposed prefix. For every learner, transcript, and truncation \(N\), their uniform average truncated query count against the first-disagreement adversary is at least \(\min\{N,d\}/4\). -/)
  (proof := /-- Use strong induction on \(N+d\), with the zero-depth and zero-truncation cases immediate. Express each truncated count as an expectation over a forced first proposal by \cref{lem:eq-lower-truncated-as-forced-average}, commute this expectation with the path average by \cref{lem:eq-lower-cube-average-expectation}, rewrite the desired constant as an expectation by \cref{lem:eq-lower-pmf-expectation-const}, and apply pointwise monotonicity through \cref{lem:eq-lower-pmf-expectation-mono}. If the forced proposal first disagrees on the exposed prefix, \cref{lem:eq-lower-first-list-disagreement-congr-left,lem:eq-lower-first-list-disagreement-mem,lem:eq-lower-first-list-disagreement-valid} make that returned point common to every target and certify rejection. Then \cref{lem:eq-lower-forced-truncated-step,lem:eq-lower-tree-disagreement-point-of-prefix,lem:eq-lower-point-mass-expectation} separate the current query from the recursive truncation; \cref{lem:eq-lower-cube-average-add,lem:eq-lower-cube-average-const} average the resulting sum. If no exposed-prefix disagreement exists, split the paths by their root label. The matching branch is identified with its subtree by \cref{lem:eq-lower-tree-truncated-shift}. In the opposite branch, the selected tree point is valid by \cref{lem:eq-lower-tree-disagreement-point-valid}, its draw distribution is \cref{lem:eq-lower-tree-adversary-draw}, and \cref{lem:eq-lower-forced-truncated-step,lem:eq-lower-point-mass-expectation,lem:eq-lower-tree-truncated-shift} again separate the current query before applying the induction hypothesis. Averaging the matching and opposite bounds yields \(\min\{N,d\}/4\). -/)
  (title := /-- Truncated average lower bound for a realized mistake tree -/)
  (latexEnv := "lemma")]
lemma eq_lower_tree_truncated_average {X : Type u}
    {H : eq_hypothesis_class X} (d fuel : ℕ) (seen : List X)
    (tree : eq_mistake_tree X d) (targets : (Fin d → Bool) → eq_hypothesis H)
    (hrealize : ∀ bits i, (targets bits).1 (eq_tree_path tree bits i) = bits i)
    (hseen : ∀ bits bits' x, x ∈ seen → (targets bits).1 x = (targets bits').1 x)
    (learner : eq_learning_rule X H) (history : eq_history X H) :
    ((min fuel d : ℕ) : ENNReal) / 4 ≤
      eq_lower_cube_average d (fun bits =>
        eq_lower_truncated_queries learner (eq_lower_tree_adversary d seen tree)
          (targets bits) history fuel) := by
  induction hsum : fuel + d using Nat.strong_induction_on generalizing fuel d seen learner history with
  | h n ih =>
      cases fuel with
      | zero => simp [eq_lower_truncated_queries, eq_lower_cube_average]
      | succ fuel =>
          cases d with
          | zero => simp [eq_lower_cube_average]
          | succ d =>
              let root : X := tree 0 (fun i => Fin.elim0 i)
              let parentAdversary : eq_counterexample_generator X H :=
                eq_lower_tree_adversary (d + 1) seen tree
              have hroot (b : Bool) (bits : Fin d → Bool) :
                  (targets (Fin.cases b bits)).1 root = b := by
                have hr := hrealize (Fin.cases b bits) (0 : Fin (d + 1))
                change (targets (Fin.cases b bits)).1 root = b
                rw [show root = eq_tree_path tree (Fin.cases b bits) 0 by
                  unfold root eq_tree_path
                  congr
                  funext j
                  exact Fin.elim0 j]
                exact hr
              have hchild_realize (b : Bool) :
                  ∀ bits i,
                    (targets (Fin.cases b bits)).1
                        (eq_tree_path (eq_lower_mistake_subtree tree b) bits i) = bits i := by
                intro bits i
                have hr := hrealize (Fin.cases b bits) i.succ
                rw [show eq_tree_path (eq_lower_mistake_subtree tree b) bits i =
                    eq_tree_path tree (Fin.cases b bits) i.succ by
                  unfold eq_tree_path eq_lower_mistake_subtree
                  apply congrArg (fun q => tree i.succ q)
                  funext j
                  refine Fin.cases rfl (fun k => ?_) j
                  rfl]
                exact hr
              have hchild_seen (b : Bool) :
                  ∀ bits bits' x, x ∈ seen ++ [root] →
                    (targets (Fin.cases b bits)).1 x =
                      (targets (Fin.cases b bits')).1 x := by
                intro bits bits' x hx
                simp only [List.mem_append, List.mem_singleton] at hx
                rcases hx with hx | rfl
                · exact hseen _ _ x hx
                · exact (hroot b bits).trans (hroot b bits').symm
              have havg :
                  eq_lower_cube_average (d + 1) (fun bits =>
                    eq_lower_truncated_queries learner parentAdversary
                      (targets bits) history (fuel + 1)) =
                    pmf_expectation (learner.choose history) (fun proposed =>
                      eq_lower_cube_average (d + 1) (fun bits =>
                        eq_lower_truncated_queries
                          (eq_lower_forced_learning_rule learner history proposed)
                          parentAdversary (targets bits) history (fuel + 1))) := by
                calc
                  _ = eq_lower_cube_average (d + 1) (fun bits =>
                        pmf_expectation (learner.choose history) (fun proposed =>
                          eq_lower_truncated_queries
                            (eq_lower_forced_learning_rule learner history proposed)
                            parentAdversary (targets bits) history (fuel + 1))) := by
                      apply congrArg
                      funext bits
                      exact eq_lower_truncated_as_forced_average learner parentAdversary
                        (targets bits) history (fuel + 1)
                  _ = _ := eq_lower_cube_average_expectation
                    (learner.choose history) (d + 1)
                    (fun proposed bits =>
                      eq_lower_truncated_queries
                        (eq_lower_forced_learning_rule learner history proposed)
                        parentAdversary (targets bits) history (fuel + 1))
              rw [havg]
              rw [← eq_lower_pmf_expectation_const (learner.choose history)
                (((min (fuel + 1) (d + 1) : ℕ) : ENNReal) / 4)]
              apply eq_lower_pmf_expectation_mono
              intro proposed
              let refBits : Fin (d + 1) → Bool := fun _ => false
              let refTarget : eq_hypothesis H := targets refBits
              cases hfirst : eq_lower_first_list_disagreement seen refTarget proposed with
              | some y =>
                  have hfirst_all (bits : Fin (d + 1) → Bool) :
                      eq_lower_first_list_disagreement seen (targets bits) proposed = some y := by
                    rw [eq_lower_first_list_disagreement_congr_left seen
                      (targets bits) refTarget proposed]
                    · exact hfirst
                    · intro x hx
                      exact hseen bits refBits x hx
                  have hy_mem : y ∈ seen :=
                    eq_lower_first_list_disagreement_mem seen refTarget proposed y hfirst
                  let nextHistory : eq_history X H :=
                    history ++
                      [{ hypothesis := proposed, point := y, label := refTarget.1 y }]
                  have hforced (bits : Fin (d + 1) → Bool) :
                      eq_lower_truncated_queries
                          (eq_lower_forced_learning_rule learner history proposed)
                          parentAdversary (targets bits) history (fuel + 1) =
                        1 + eq_lower_truncated_queries learner parentAdversary
                          (targets bits) nextHistory fuel := by
                    have hvalid := eq_lower_first_list_disagreement_valid seen
                      (targets bits) proposed y (hfirst_all bits)
                    have hne : proposed ≠ targets bits := by
                      intro heq
                      subst proposed
                      exact hvalid rfl
                    rw [eq_lower_forced_truncated_step learner history proposed
                      (targets bits) hne parentAdversary fuel]
                    simp only [parentAdversary, eq_lower_tree_adversary]
                    rw [eq_lower_tree_disagreement_point_of_prefix (d + 1) seen tree
                      (targets bits) proposed (Ne.symm hne) y (hfirst_all bits)]
                    rw [eq_lower_point_mass_expectation]
                    apply congrArg
                    unfold nextHistory
                    rw [hseen bits refBits y hy_mem]
                  have hrec := ih (fuel + (d + 1)) (by omega)
                    (d + 1) fuel seen tree targets hrealize hseen learner nextHistory rfl
                  have hnum : min (fuel + 1) (d + 1) ≤ 4 + min fuel (d + 1) := by
                    omega
                  calc
                    (((min (fuel + 1) (d + 1) : ℕ) : ENNReal) / 4) ≤
                        1 + (((min fuel (d + 1) : ℕ) : ENNReal) / 4) := by
                      have hcast : ((min (fuel + 1) (d + 1) : ℕ) : ENNReal) ≤
                          4 + ((min fuel (d + 1) : ℕ) : ENNReal) := by exact_mod_cast hnum
                      calc
                        _ ≤ (4 + ((min fuel (d + 1) : ℕ) : ENNReal)) / 4 := by
                          gcongr
                        _ = _ := by
                          change (4 + ((min fuel (d + 1) : ℕ) : ENNReal)) * 4⁻¹ =
                            1 + ((min fuel (d + 1) : ℕ) : ENNReal) * 4⁻¹
                          rw [add_mul]
                          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
                    _ ≤ eq_lower_cube_average (d + 1) (fun bits =>
                        eq_lower_truncated_queries
                          (eq_lower_forced_learning_rule learner history proposed)
                          parentAdversary (targets bits) history (fuel + 1)) := by
                      rw [show (fun bits =>
                          eq_lower_truncated_queries
                            (eq_lower_forced_learning_rule learner history proposed)
                            parentAdversary (targets bits) history (fuel + 1)) =
                          (fun bits => 1 + eq_lower_truncated_queries learner
                            parentAdversary (targets bits) nextHistory fuel) by
                        funext bits; exact hforced bits]
                      rw [eq_lower_cube_average_add, eq_lower_cube_average_const]
                      simpa [parentAdversary, add_comm] using add_le_add_left hrec 1
              | none =>
                  have hnone_all (bits : Fin (d + 1) → Bool) :
                      eq_lower_first_list_disagreement seen (targets bits) proposed = none := by
                    rw [eq_lower_first_list_disagreement_congr_left seen
                      (targets bits) refTarget proposed]
                    · exact hfirst
                    · intro x hx
                      exact hseen bits refBits x hx
                  have hmatch (b : Bool)
                      (hp : proposed.1 root = b) :
                      (((min (fuel + 1) d : ℕ) : ENNReal) / 4) ≤
                        eq_lower_cube_average d (fun bits =>
                          eq_lower_truncated_queries
                            (eq_lower_forced_learning_rule learner history proposed)
                            parentAdversary (targets (Fin.cases b bits)) history
                            (fuel + 1)) := by
                    have hrec := ih ((fuel + 1) + d) (by omega)
                      d (fuel + 1) (seen ++ [root])
                      (eq_lower_mistake_subtree tree b)
                      (fun bits => targets (Fin.cases b bits))
                      (hchild_realize b) (hchild_seen b)
                      (eq_lower_forced_learning_rule learner history proposed) history rfl
                    refine le_trans hrec ?_
                    apply le_of_eq
                    apply congrArg
                    funext bits
                    symm
                    exact eq_lower_tree_truncated_shift d (fuel + 1) seen tree b
                      (targets (Fin.cases b bits)) (hroot b bits)
                      (eq_lower_forced_learning_rule learner history proposed) history
                  have hopposite (b : Bool)
                      (hp : proposed.1 root ≠ b) :
                      1 + (((min fuel d : ℕ) : ENNReal) / 4) ≤
                        eq_lower_cube_average d (fun bits =>
                          eq_lower_truncated_queries
                            (eq_lower_forced_learning_rule learner history proposed)
                            parentAdversary (targets (Fin.cases b bits)) history
                            (fuel + 1)) := by
                    let nextHistory : eq_history X H :=
                      history ++ [{ hypothesis := proposed, point := root, label := b }]
                    have hforced (bits : Fin d → Bool) :
                        eq_lower_truncated_queries
                            (eq_lower_forced_learning_rule learner history proposed)
                            parentAdversary (targets (Fin.cases b bits)) history
                            (fuel + 1) =
                          1 + eq_lower_truncated_queries learner
                            (eq_lower_tree_adversary d (seen ++ [root])
                              (eq_lower_mistake_subtree tree b))
                            (targets (Fin.cases b bits)) nextHistory fuel := by
                      have hne : proposed ≠ targets (Fin.cases b bits) := by
                        intro heq
                        have := hroot b bits
                        rw [← heq] at this
                        exact hp this
                      rw [eq_lower_forced_truncated_step learner history proposed
                        (targets (Fin.cases b bits)) hne parentAdversary fuel]
                      have hpoint : eq_lower_tree_disagreement_point (d + 1) seen tree
                          (targets (Fin.cases b bits)) proposed (Ne.symm hne) = root := by
                        have hdiff : (targets (Fin.cases b bits)).1 root ≠
                            proposed.1 root := by
                          rw [hroot b bits]
                          exact Ne.symm hp
                        unfold root at hdiff ⊢
                        simp only [eq_lower_tree_disagreement_point,
                          hnone_all (Fin.cases b bits)]
                        rw [dif_neg hdiff]
                      rw [show parentAdversary.draw (eq_hypothesis_history history)
                          (targets (Fin.cases b bits)) proposed (Ne.symm hne) =
                            eq_lower_point_mass
                              (eq_lower_tree_disagreement_point (d + 1) seen tree
                                (targets (Fin.cases b bits)) proposed (Ne.symm hne)) by
                        exact eq_lower_tree_adversary_draw (d + 1) seen tree
                          (eq_hypothesis_history history) (targets (Fin.cases b bits))
                          proposed (Ne.symm hne)]
                      rw [hpoint, eq_lower_point_mass_expectation]
                      rw [hroot b bits]
                      change 1 + eq_lower_truncated_queries learner parentAdversary
                          (targets (Fin.cases b bits)) nextHistory fuel = _
                      rw [eq_lower_tree_truncated_shift d fuel seen tree b
                        (targets (Fin.cases b bits)) (hroot b bits) learner
                        nextHistory]
                    have hrec := ih (fuel + d) (by omega)
                      d fuel (seen ++ [root]) (eq_lower_mistake_subtree tree b)
                      (fun bits => targets (Fin.cases b bits))
                      (hchild_realize b) (hchild_seen b) learner nextHistory rfl
                    rw [show (fun bits =>
                        eq_lower_truncated_queries
                          (eq_lower_forced_learning_rule learner history proposed)
                          parentAdversary (targets (Fin.cases b bits)) history
                          (fuel + 1)) =
                        (fun bits => 1 + eq_lower_truncated_queries learner
                          (eq_lower_tree_adversary d (seen ++ [root])
                            (eq_lower_mistake_subtree tree b))
                          (targets (Fin.cases b bits)) nextHistory fuel) by
                      funext bits; exact hforced bits]
                    rw [eq_lower_cube_average_add, eq_lower_cube_average_const]
                    simpa [add_comm] using add_le_add_left hrec 1
                  cases hpval : proposed.1 root with
                  | false =>
                      have hm := hmatch false hpval
                      have ho := hopposite true (by simp [hpval])
                      simp only [eq_lower_cube_average]
                      have hnum : 2 * min (fuel + 1) (d + 1) ≤
                          min (fuel + 1) d + 4 + min fuel d := by omega
                      have hcast :
                          2 * (((min (fuel + 1) (d + 1) : ℕ) : ENNReal)) ≤
                            ((min (fuel + 1) d : ℕ) : ENNReal) + 4 +
                              ((min fuel d : ℕ) : ENNReal) := by exact_mod_cast hnum
                      calc
                        (((min (fuel + 1) (d + 1) : ℕ) : ENNReal) / 4) ≤
                            ((((min (fuel + 1) d : ℕ) : ENNReal) / 4) +
                              (1 + (((min fuel d : ℕ) : ENNReal) / 4))) / 2 := by
                          norm_num [div_eq_mul_inv] at hcast ⊢
                          have hlefttop :
                              (↑(min fuel d) + 1) * (4 : ENNReal)⁻¹ ≠ ⊤ := by
                            finiteness
                          have hrighttop :
                              (↑(min (fuel + 1) d) * (4 : ENNReal)⁻¹ +
                                (1 + ↑(min fuel d) * (4 : ENNReal)⁻¹)) *
                                  (2 : ENNReal)⁻¹ ≠ ⊤ := by
                            finiteness
                          rw [← ENNReal.toReal_le_toReal hlefttop hrighttop]
                          simp only [ENNReal.toReal_mul, ENNReal.toReal_inv]
                          repeat' rw [ENNReal.toReal_add
                            (by finiteness) (by finiteness)]
                          simp
                          have hnumReal :
                              ((2 * min (fuel + 1) (d + 1) : ℕ) : ℝ) ≤
                                ((min (fuel + 1) d + 4 + min fuel d : ℕ) : ℝ) := by
                            exact_mod_cast hnum
                          norm_num at hnumReal ⊢
                          linarith
                        _ ≤ _ := by gcongr
                  | true =>
                      have hm := hmatch true hpval
                      have ho := hopposite false (by simp [hpval])
                      simp only [eq_lower_cube_average]
                      have hnum : 2 * min (fuel + 1) (d + 1) ≤
                          min (fuel + 1) d + 4 + min fuel d := by omega
                      have hcast :
                          2 * (((min (fuel + 1) (d + 1) : ℕ) : ENNReal)) ≤
                            ((min (fuel + 1) d : ℕ) : ENNReal) + 4 +
                              ((min fuel d : ℕ) : ENNReal) := by exact_mod_cast hnum
                      calc
                        (((min (fuel + 1) (d + 1) : ℕ) : ENNReal) / 4) ≤
                            ((1 + (((min fuel d : ℕ) : ENNReal) / 4)) +
                              (((min (fuel + 1) d : ℕ) : ENNReal) / 4)) / 2 := by
                          norm_num [div_eq_mul_inv] at hcast ⊢
                          have hlefttop :
                              (↑(min fuel d) + 1) * (4 : ENNReal)⁻¹ ≠ ⊤ := by
                            finiteness
                          have hrighttop :
                              ((1 + ↑(min fuel d) * (4 : ENNReal)⁻¹) +
                                ↑(min (fuel + 1) d) * (4 : ENNReal)⁻¹) *
                                  (2 : ENNReal)⁻¹ ≠ ⊤ := by
                            finiteness
                          rw [← ENNReal.toReal_le_toReal hlefttop hrighttop]
                          simp only [ENNReal.toReal_mul, ENNReal.toReal_inv]
                          repeat' rw [ENNReal.toReal_add
                            (by finiteness) (by finiteness)]
                          simp
                          have hnumReal :
                              ((2 * min (fuel + 1) (d + 1) : ℕ) : ℝ) ≤
                                ((min (fuel + 1) d + 4 + min fuel d : ℕ) : ℝ) := by
                            exact_mod_cast hnum
                          norm_num at hnumReal ⊢
                          linarith
                        _ ≤ _ := by gcongr

@[blueprint "lem:eq-lower-cube-average-mono"
  (statement := /-- If one nonnegative function is pointwise bounded by another on a finite Boolean cube, then its uniform recursive average is bounded by the other average. -/)
  (proof := /-- Induct on the cube dimension in \cref{def:eq-lower-cube-average}. The zero-dimensional claim is the pointwise hypothesis at the unique path. At positive dimension, apply the induction hypothesis separately after fixing the root label to false and to true, then use monotonicity of addition and division by two. -/)
  (title := /-- Monotonicity of the Boolean-cube average -/)
  (latexEnv := "lemma")]
lemma eq_lower_cube_average_mono (d : ℕ)
    (f g : (Fin d → Bool) → ENNReal)
    (h : ∀ bits, f bits ≤ g bits) :
    eq_lower_cube_average d f ≤ eq_lower_cube_average d g := by
  induction d with
  | zero =>
      exact h (fun i => Fin.elim0 i)
  | succ d ih =>
      simp only [eq_lower_cube_average]
      gcongr
      · exact ih (fun bits => f (Fin.cases false bits))
          (fun bits => g (Fin.cases false bits))
          (fun bits => h (Fin.cases false bits))
      · exact ih (fun bits => f (Fin.cases true bits))
          (fun bits => g (Fin.cases true bits))
          (fun bits => h (Fin.cases true bits))

@[blueprint "lem:eq-lower-tree-average-expected"
  (statement := /-- Let a Boolean hypothesis class shatter a mistake tree of depth \(d\). Against the symmetric first-disagreement adversary associated with that tree, every proper randomized learner has uniform average expected query count at least \(d/4\) over the selected targets realizing the \(2^d\) tree paths. -/)
  (proof := /-- Select, for every path, the realizing target certified by \cref{lem:eq-lower-tree-target-realizes}. Apply \cref{lem:eq-lower-tree-truncated-average} with truncation \(N=d\), empty exposed prefix, and empty initial transcript to obtain an average truncated-query lower bound of \(d/4\). For every path, \cref{lem:eq-lower-truncated-queries-le-expected} bounds that truncation by the full survival-tail expectation. Applying the pointwise monotonicity of the finite path average from \cref{lem:eq-lower-cube-average-mono} and unfolding the empty-transcript expectation gives the result. -/)
  (title := /-- Average lower bound on a shattered mistake tree -/)
  (latexEnv := "lemma")]
lemma eq_lower_tree_average_expected {X : Type u}
    {H : eq_hypothesis_class X} {d : ℕ} (tree : eq_mistake_tree X d)
    (hshatter : eq_shatters_tree H tree) (learner : eq_learning_rule X H) :
    (d : ENNReal) / 4 ≤
      eq_lower_cube_average d (fun bits =>
        eq_expected_queries learner (eq_lower_tree_adversary d [] tree)
          (eq_lower_tree_target tree hshatter bits)) := by
  have htrunc := eq_lower_tree_truncated_average d d [] tree
    (fun bits => eq_lower_tree_target tree hshatter bits)
    (by
      intro bits i
      exact eq_lower_tree_target_realizes tree hshatter bits i)
    (by simp) learner []
  have hfull := eq_lower_cube_average_mono d
    (fun bits => eq_lower_truncated_queries learner
      (eq_lower_tree_adversary d [] tree)
      (eq_lower_tree_target tree hshatter bits) [] d)
    (fun bits => eq_lower_expected_from_history learner
      (eq_lower_tree_adversary d [] tree)
      (eq_lower_tree_target tree hshatter bits) [])
    (fun bits => eq_lower_truncated_queries_le_expected learner
      (eq_lower_tree_adversary d [] tree)
      (eq_lower_tree_target tree hshatter bits) [] d)
  exact le_trans (by simpa using htrunc)
    (by
      simpa [eq_expected_queries, eq_lower_expected_from_history] using hfull)

@[blueprint "lem:eq-lower-shatters-own-dimension"
  (statement := /-- Every nonempty Boolean hypothesis class shatters a complete mistake tree whose depth is its Littlestone dimension as defined by the finite supremum in \cref{def:littlestone-dim}. -/)
  (proof := /-- Choose an index attaining the supremum over the nonempty finite range in \cref{def:littlestone-dim}. If the chosen index is shattered, its conditional value equals that index and gives \cref{def:eq-shatters-depth}. Otherwise the conditional value is zero; nonemptiness supplies a hypothesis realizing the unique path through the depth-zero tree, so depth zero is shattered as well. -/)
  (title := /-- A nonempty class shatters its Littlestone dimension -/)
  (latexEnv := "lemma")]
lemma eq_lower_shatters_own_dimension {X : Type u}
    (H : eq_hypothesis_class X) (hH : H.Nonempty) :
    eq_shatters_depth H (littlestone_dim H) := by
  classical
  unfold littlestone_dim
  obtain ⟨d, hd, hmax⟩ := Finset.exists_mem_eq_sup
    (Finset.range (H.ncard + 1)) ⟨0, by simp⟩
    (fun n => if eq_shatters_depth H n then n else 0)
  rw [hmax]
  by_cases hs : eq_shatters_depth H d
  · simpa [hs] using hs
  · simp only [if_neg hs]
    rcases hH with ⟨f, hf⟩
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    intro bits
    refine ⟨⟨f, hf⟩, ?_⟩
    intro i
    exact Fin.elim0 i

@[blueprint "lem:full-information-lower-bound"
  (statement := /-- There exists a positive finite constant \(c\in\mathbb R_{\geq 0}\cup\{\infty\}\) such that, for every type \(X\) and every finite nonempty Boolean hypothesis class \(\mathcal H\subseteq\{0,1\}^{X}\), there is a symmetric counterexample generator \(\mathcal A\) with the following property: for every proper randomized learning rule \(L\), some target \(h^{\star}\in\mathcal H\) satisfies
  \[
    c\,\operatorname{Ldim}(\mathcal H)
      \leq \operatorname{EQueries}(L,\mathcal A,h^{\star}).
  \] -/)
  (proof := /-- Take \(c=1/4\), which is positive and finite. For a nonempty class \(\mathcal H\), \cref{lem:eq-lower-shatters-own-dimension} supplies a shattered mistake tree of depth \(\operatorname{Ldim}(\mathcal H)\). Use its first-disagreement counterexample generator, whose symmetry is \cref{lem:eq-lower-tree-adversary-symmetric}. For an arbitrary proper randomized learner, \cref{lem:eq-lower-tree-average-expected} bounds the uniform average expected query count over the selected path-realizing targets below by \(\operatorname{Ldim}(\mathcal H)/4\). By \cref{lem:eq-lower-cube-average-attained}, one of those targets has expected query count at least that average. Commuting the scalar \(1/4\) with the dimension gives the required inequality. -/)
  (title := /-- A symmetric adversary forcing linear query complexity -/)
  (latexEnv := "lemma")]
lemma full_information_lower_bound : full_information_lower_statement := by
  unfold full_information_lower_statement
  refine ⟨1 / 4, by norm_num, by norm_num, ?_⟩
  intro X H hfinite hnonempty
  obtain ⟨tree, hshatter⟩ := eq_lower_shatters_own_dimension H hnonempty
  refine ⟨eq_lower_tree_adversary (littlestone_dim H) [] tree,
    eq_lower_tree_adversary_symmetric (littlestone_dim H) [] tree, ?_⟩
  intro learner
  have havg := eq_lower_tree_average_expected tree hshatter learner
  obtain ⟨bits, hbits⟩ := eq_lower_cube_average_attained
    (littlestone_dim H)
    (fun bits => eq_expected_queries learner
      (eq_lower_tree_adversary (littlestone_dim H) [] tree)
      (eq_lower_tree_target tree hshatter bits))
  refine ⟨eq_lower_tree_target tree hshatter bits, ?_⟩
  calc
    (1 / 4 : ENNReal) * (littlestone_dim H : ENNReal) =
        (littlestone_dim H : ENNReal) / 4 := by
      simp only [div_eq_mul_inv, one_mul]
      ac_rfl
    _ ≤ eq_lower_cube_average (littlestone_dim H) (fun bits =>
        eq_expected_queries learner
          (eq_lower_tree_adversary (littlestone_dim H) [] tree)
          (eq_lower_tree_target tree hshatter bits)) := havg
    _ ≤ _ := hbits

@[blueprint "thm:full-information"
  (statement := /-- There exist universal constants \(C,c\in\mathbb R_{\geq 0}\cup\{\infty\}\) such that \(C\ne\infty\), \(0<c\), and \(c\ne\infty\), with the following properties. For every type \(X\), every finite nonempty Boolean hypothesis class \(\mathcal H\subseteq\{0,1\}^{X}\), and every symmetric counterexample generator \(\mathcal A\) on \(\mathcal H\), there is a proper randomized learning rule \(L\) such that, for every target \(h^{\star}\in\mathcal H\),
  \[
    \operatorname{EQueries}(L,\mathcal A,h^{\star})
      \leq C\bigl(\operatorname{Ldim}(\mathcal H)+1\bigr).
  \]
  Conversely, for every type \(X\) and every finite nonempty Boolean hypothesis class \(\mathcal H\subseteq\{0,1\}^{X}\), there is a symmetric counterexample generator \(\mathcal A^{\star}\) such that, for every proper randomized learning rule \(L\), some target \(h^{\star}\in\mathcal H\) satisfies
  \[
    c\,\operatorname{Ldim}(\mathcal H)
      \leq \operatorname{EQueries}(L,\mathcal A^{\star},h^{\star}).
  \] -/)
  (proof := /-- The upper assertion is \cref{lem:full-information-upper-bound}, and the lower assertion is \cref{lem:full-information-lower-bound}. Taking these two conclusions together yields the claimed pair of uniform linear bounds. -/)
  (title := /-- Full-information learning from equivalence queries -/)
  (latexEnv := "theorem")]
theorem full_information :
    full_information_upper_statement ∧ full_information_lower_statement := by
  exact ⟨full_information_upper_bound, full_information_lower_bound⟩

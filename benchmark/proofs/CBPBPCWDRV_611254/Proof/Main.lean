import Architect
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Finset.Union
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Partition.Finpartition

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

@[blueprint "def:indexed-union"
  (statement := /-- Let $I=(I_t)_{t\in\kappa}$ be a family of finite subsets of an ambient type.  For a finite set $\Delta\subseteq\kappa$, define $I_\Delta=\bigcup_{t\in\Delta}I_t$. -/)
  (title := /-- Indexed union of the supports -/)
  (latexEnv := "definition")]
def indexed_union {κ ι : Type*} [DecidableEq ι]
    (I : κ → Finset ι) (Δ : Finset κ) : Finset ι :=
  Δ.biUnion I

@[blueprint "def:mixed-moment-x-factor"
  (statement := /-- For $x\in\mathbb R$ and a finite set $S$, define
  \[
    X_x(S)=\prod_{k=1}^{|S|-1}(1-kx)^{-1}.
  \]
  An empty product is understood to be $1$. -/)
  (title := /-- Reciprocal factor in the mixed-moment formula -/)
  (latexEnv := "definition")]
noncomputable def mixed_moment_x_factor {ι : Type*} (x : ℝ) (S : Finset ι) : ℝ :=
  ∏ k ∈ Finset.range (S.card - 1),
    (1 - (((k + 1 : ℕ) : ℝ) * x))⁻¹

@[blueprint "def:mixed-moment-y-factor"
  (statement := /-- For $y\in\mathbb R$ and a finite set $S$, define
  \[
    Y_y(S)=\prod_{k=1}^{|S|-1}(1-ky).
  \]
  An empty product is understood to be $1$. -/)
  (title := /-- Direct factor in the mixed-moment formula -/)
  (latexEnv := "definition")]
def mixed_moment_y_factor {ι : Type*} (y : ℝ) (S : Finset ι) : ℝ :=
  ∏ k ∈ Finset.range (S.card - 1),
    (1 - (((k + 1 : ℕ) : ℝ) * y))

@[blueprint "def:mixed-moment-right-hand-side"
  (statement := /-- Let $I=(I_t)_{t\in[\ell]}$, $A=(A_j)_{j\in[q]}$, and $B=(B_i)_{i\in[r]}$ be finite-set families, and let $\eta,x_0,y_0\in\mathbb R$.  For $\Delta\subseteq[\ell]$, define
  \[
  M(\Delta)=\eta^{|I_\Delta|}
  \prod_{j\in[q]}X_{x_0}(I_\Delta\cap A_j)
  \prod_{i\in[r]}Y_{y_0}(I_\Delta\cap B_i),
  \]
  where $I_\Delta$, $X_{x_0}$, and $Y_{y_0}$ are as in \cref{def:indexed-union,def:mixed-moment-x-factor,def:mixed-moment-y-factor}. -/)
  (title := /-- Right-hand side of the general mixed-moment formula -/)
  (latexEnv := "definition")]
noncomputable def mixed_moment_right_hand_side {ι : Type*} [DecidableEq ι]
    {ℓ q r : ℕ} (I : Fin ℓ → Finset ι) (A : Fin q → Finset ι)
    (B : Fin r → Finset ι) (η x₀ y₀ : ℝ) (Δ : Finset (Fin ℓ)) : ℝ :=
  η ^ (indexed_union I Δ).card *
    (∏ j : Fin q, mixed_moment_x_factor x₀ (indexed_union I Δ ∩ A j)) *
    ∏ i : Fin r, mixed_moment_y_factor y₀ (indexed_union I Δ ∩ B i)

@[blueprint "def:has-general-mixed-moments"
  (statement := /-- Let $(\Omega,\mathcal F,\mu)$ be a measure space, let $Z_t:\Omega\to\mathbb R$ for $t\in[\ell]$, and let $I$, $A$, and $B$ be finite-set families indexed respectively by $[\ell]$, $[q]$, and $[r]$.  The variables have the general mixed moments with parameters $\eta,x_0,y_0$ if the sets within each of the three families are pairwise disjoint and, for every $\Delta\subseteq[\ell]$, the product $\prod_{t\in\Delta}Z_t$ is integrable and its expectation equals the quantity $M(\Delta)$ of \cref{def:mixed-moment-right-hand-side}. -/)
  (title := /-- General mixed-moment hypothesis -/)
  (latexEnv := "definition")]
def has_general_mixed_moments {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {ℓ q r : ℕ} (μ : MeasureTheory.Measure Ω) (Z : Fin ℓ → Ω → ℝ)
    (I : Fin ℓ → Finset ι) (A : Fin q → Finset ι) (B : Fin r → Finset ι)
    (η x₀ y₀ : ℝ) : Prop :=
  Set.univ.PairwiseDisjoint I ∧
    Set.univ.PairwiseDisjoint A ∧
    Set.univ.PairwiseDisjoint B ∧
    ∀ Δ : Finset (Fin ℓ),
      MeasureTheory.Integrable (fun ω ↦ ∏ t ∈ Δ, Z t ω) μ ∧
        (∫ ω, ∏ t ∈ Δ, Z t ω ∂μ) =
          mixed_moment_right_hand_side I A B η x₀ y₀ Δ

@[blueprint "def:total-index-count"
  (statement := /-- For the family $I=(I_t)_{t\in[\ell]}$, define
  \[
    L=\left|\bigcup_{t\in[\ell]}I_t\right|.
  \]
  This is the cardinality of $I_{[\ell]}$ from \cref{def:indexed-union}. -/)
  (title := /-- Cardinality of the total support -/)
  (latexEnv := "definition")]
def total_index_count {ι : Type*} [DecidableEq ι] {ℓ : ℕ}
    (I : Fin ℓ → Finset ι) : ℕ :=
  (indexed_union I Finset.univ).card

@[blueprint "def:joint-cumulant"
  (statement := /-- Let $Z_t:\Omega\to\mathbb R$ be indexed by $[\ell]$ on a measure space $(\Omega,\mathcal F,\mu)$.  Its joint cumulant is
  \[
  \operatorname{cum}(Z_1,\ldots,Z_\ell)
  =\sum_{\pi\in\Pi([\ell])}(-1)^{|\pi|-1}(|\pi|-1)!
    \prod_{C\in\pi}\int_\Omega\prod_{t\in C}Z_t\,d\mu,
  \]
  where $\Pi([\ell])$ denotes the finite set of set partitions of $[\ell]$. -/)
  (title := /-- Joint cumulant -/)
  (latexEnv := "definition")]
noncomputable def joint_cumulant {Ω : Type*} [MeasurableSpace Ω] {ℓ : ℕ}
    (μ : MeasureTheory.Measure Ω) (Z : Fin ℓ → Ω → ℝ) : ℝ :=
  ∑ π : Finpartition (Finset.univ : Finset (Fin ℓ)),
    ((-1 : ℝ) ^ (π.parts.card - 1)) *
      (Nat.factorial (π.parts.card - 1) : ℝ) *
      ∏ C ∈ π.parts, (∫ ω, ∏ t ∈ C, Z t ω ∂μ)

@[blueprint "def:b-intersection-graph"
  (statement := /-- Given $I=(I_t)_{t\in[\ell]}$ and $B=(B_i)_{i\in[r]}$, define the simple graph $\mathcal B$ on $[\ell]$ by declaring two distinct vertices $t,t'$ adjacent precisely when there exists $i\in[r]$ such that $I_t\cap B_i$ and $I_{t'}\cap B_i$ are both nonempty. -/)
  (title := /-- Intersection graph generated by the $B$-family -/)
  (latexEnv := "definition")]
def b_intersection_graph {ι : Type*} [DecidableEq ι] {ℓ r : ℕ}
    (I : Fin ℓ → Finset ι) (B : Fin r → Finset ι) : SimpleGraph (Fin ℓ) :=
  SimpleGraph.fromRel fun t t' ↦
    ∃ i : Fin r, (I t ∩ B i).Nonempty ∧ (I t' ∩ B i).Nonempty

@[blueprint "def:intersection-component-count"
  (statement := /-- Let $cc(\mathcal B)$ be the number of connected components of the graph $\mathcal B$ from \cref{def:b-intersection-graph}. -/)
  (title := /-- Number of components of the intersection graph -/)
  (latexEnv := "definition")]
noncomputable def intersection_component_count {ι : Type*} [DecidableEq ι]
    {ℓ r : ℕ} (I : Fin ℓ → Finset ι) (B : Fin r → Finset ι) : ℕ :=
  Nat.card (b_intersection_graph I B).ConnectedComponent

@[blueprint "lem:joint-cumulant-of-mixed-moments"
  (statement := /-- Let $\Omega$ be a measurable space, let $\iota$ be a type with decidable equality, and let $\ell,q,r\in\mathbb N$.  Fix a measure $\mu$ on $\Omega$, functions $Z_t:\Omega\to\mathbb R$ indexed by $t\in[\ell]$, and families of finite subsets of $\iota$ given by $(I_t)_{t\in[\ell]}$, $(A_j)_{j\in[q]}$, and $(B_i)_{i\in[r]}$.  For $\eta,x_0,y_0\in\mathbb R$, suppose that $Z$ has the general mixed moments of \cref{def:has-general-mixed-moments} with respect to these data.  Writing $M(\Delta)$ for the corresponding expression from \cref{def:mixed-moment-right-hand-side}, one has
  \[
  \operatorname{cum}(Z_1,\ldots,Z_\ell)
  =\sum_{\pi\in\Pi([\ell])}(-1)^{|\pi|-1}(|\pi|-1)!
    \prod_{C\in\pi}M(C).
  \] -/)
  (proof := /-- Expand the joint cumulant using \cref{def:joint-cumulant}.  For every partition $\pi$ of $[\ell]$ and every block $C\in\pi$, the hypothesis \cref{def:has-general-mixed-moments} identifies the integral of $\prod_{t\in C}Z_t$ with $M(C)$ from \cref{def:mixed-moment-right-hand-side}.  Substitution in each factor of each finite product, followed by substitution in the finite sum over $\pi$, gives the displayed identity. -/)
  (title := /-- Cumulant as a partition sum of the prescribed moments -/)
  (latexEnv := "lemma")]
lemma joint_cumulant_of_mixed_moments
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {ℓ q r : ℕ} (μ : MeasureTheory.Measure Ω)
    (Z : Fin ℓ → Ω → ℝ) (I : Fin ℓ → Finset ι)
    (A : Fin q → Finset ι) (B : Fin r → Finset ι) (η x₀ y₀ : ℝ)
    (hmom : has_general_mixed_moments μ Z I A B η x₀ y₀) :
    joint_cumulant μ Z =
      ∑ π : Finpartition (Finset.univ : Finset (Fin ℓ)),
        ((-1 : ℝ) ^ (π.parts.card - 1)) *
          (Nat.factorial (π.parts.card - 1) : ℝ) *
          ∏ C ∈ π.parts, mixed_moment_right_hand_side I A B η x₀ y₀ C := by
  unfold joint_cumulant
  simp_rw [(hmom.2.2.2 _).2]

@[blueprint "def:mixed-moment-occurrence-configuration"
  (statement := /-- Fix an ambient type $\iota$ and integers $q,r\geq0$.  An occurrence-labelled mixed-moment configuration consists of an ordered word $W_{j,u}$ in $\iota$ for every $j\in[q]$ and $u\in\iota$, together with an optional element $b_{i,u}\in\iota$ for every $i\in[r]$ and $u\in\iota$.  The position of an entry in $W_{j,u}$ is part of its label.  Thus repeated choices of the same predecessor at different positions remain distinct occurrences. -/)
  (title := /-- Occurrence-labelled configurations for the mixed-moment expansion -/)
  (latexEnv := "definition")]
structure mixed_moment_occurrence_configuration (ι : Type*) (q r : ℕ) where
  aWords : Fin q → ι → List ι
  bChoice : Fin r → ι → Option ι

@[blueprint "def:mixed-moment-configuration-admissible"
  (statement := /-- Let $U=I_{[\ell]}$ and let $\varrho:U\to\mathbb N$ be the restriction of a function $\varrho:\iota\to\mathbb N$ that is injective on $U$.  An occurrence-labelled configuration $\Gamma$ is admissible if every entry of $W_{j,u}$ lies with $u$ in $U\cap A_j$ and precedes $u$ in the order induced by $\varrho$, and if $b_{i,u}=v$ only when $u,v\in U\cap B_i$ and $\varrho(v)<\varrho(u)$.  Words based outside $U\cap A_j$ are required to be empty. -/)
  (title := /-- Admissibility of an occurrence-labelled configuration -/)
  (latexEnv := "definition")]
def mixed_moment_configuration_admissible {ι : Type*} [DecidableEq ι]
    {ℓ q r : ℕ} (I : Fin ℓ → Finset ι) (A : Fin q → Finset ι)
    (B : Fin r → Finset ι) (rank : ι → ℕ)
    (Γ : mixed_moment_occurrence_configuration ι q r) : Prop :=
  Set.InjOn rank (indexed_union I Finset.univ : Set ι) ∧
    (∀ j u, u ∉ indexed_union I Finset.univ ∩ A j → Γ.aWords j u = []) ∧
    (∀ j u v, v ∈ Γ.aWords j u →
      u ∈ indexed_union I Finset.univ ∩ A j ∧
      v ∈ indexed_union I Finset.univ ∩ A j ∧ rank v < rank u) ∧
    ∀ i u v, Γ.bChoice i u = some v →
      u ∈ indexed_union I Finset.univ ∩ B i ∧
      v ∈ indexed_union I Finset.univ ∩ B i ∧ rank v < rank u

@[blueprint "def:mixed-moment-configuration-weight"
  (statement := /-- Let $\Gamma$ be an occurrence-labelled configuration and put $U=I_{[\ell]}$.  Its weight is
  \[
    w(\Gamma)=\eta^{|U|}x_0^{\sum_{j,u\in U}|W_{j,u}|}
      (-y_0)^{\sum_i|\{u\in U:b_{i,u}\ne\varnothing\}|}.
  \]
  In particular, every word position contributes a separate factor $x_0$, and every nonempty $B$-choice contributes a separate factor $-y_0$. -/)
  (title := /-- Weight of an occurrence-labelled configuration -/)
  (latexEnv := "definition")]
noncomputable def mixed_moment_configuration_weight {ι : Type*} [DecidableEq ι]
    {ℓ q r : ℕ} (I : Fin ℓ → Finset ι) (η x₀ y₀ : ℝ)
    (Γ : mixed_moment_occurrence_configuration ι q r) : ℝ :=
  η ^ total_index_count I *
    x₀ ^ (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ, (Γ.aWords j u).length) *
    (-y₀) ^ (∑ i : Fin r,
      ((indexed_union I Finset.univ).filter fun u ↦ Γ.bChoice i u ≠ none).card)

@[blueprint "def:mixed-moment-configuration-connected"
  (statement := /-- An occurrence-labelled configuration $\Gamma$ is connected relative to $I$ if the following graph on $[\ell]$ is connected.  Join $t$ to $t'$ whenever some $u\in I_t$ and $v\in I_{t'}$ occur together either as an entry $v$ in a word $W_{j,u}$ or as a choice $b_{i,u}=v$.  The simple-graph construction discards loops and forgets orientation, but the configuration itself retains all occurrence labels and word positions. -/)
  (title := /-- Connectivity of an occurrence-labelled configuration -/)
  (latexEnv := "definition")]
def mixed_moment_configuration_connected {ι : Type*} [DecidableEq ι]
    {ℓ q r : ℕ} (I : Fin ℓ → Finset ι)
    (Γ : mixed_moment_occurrence_configuration ι q r) : Prop :=
  (SimpleGraph.fromRel fun t t' ↦
    ∃ u ∈ I t, ∃ v ∈ I t',
      (∃ j : Fin q, v ∈ Γ.aWords j u) ∨
      ∃ i : Fin r, Γ.bChoice i u = some v).Connected

@[blueprint "lem:finpartition-mobius-connected-cancellation"
  (statement := /-- Let $S$ be a nonempty finite set and let $\rho$ be a partition of $S$.  In the refinement order on finite partitions,
  \[
    \sum_{\substack{\pi\in\Pi(S)\\ \rho\leq\pi}}
      (-1)^{|\pi|-1}(|\pi|-1)!
    =
    \begin{cases}
      1,&|\rho|=1,\\
      0,&|\rho|\ne1.
    \end{cases}
  \]
  Thus the cumulant coefficient attached to a configuration is one precisely when its component partition is connected, and is zero otherwise. -/)
  (proof := /-- Every partition $\pi$ satisfying $\rho\leq\pi$ is obtained uniquely by partitioning the finite set of parts of $\rho$ and then taking the unions inside the resulting blocks.  Consequently the displayed sum depends only on $m=|\rho|$ and equals
  \[
    \sum_{k=1}^{m}S(m,k)(-1)^{k-1}(k-1)!,
  \]
  where $S(m,k)$ is the Stirling number of the second kind.  This is $m!$ times the coefficient of $z^m$ in
  \[
    \sum_{k\geq1}\frac{(-1)^{k-1}}{k}(\exp z-1)^k
      =\log(\exp z)=z.
  \]
  The coefficient is therefore $1$ for $m=1$ and $0$ for every other $m$, which proves the formula. -/)
  (title := /-- Möbius cancellation above a component partition -/)
  (latexEnv := "lemma")]
lemma finpartition_mobius_connected_cancellation
    {α : Type*} [DecidableEq α] (S : Finset α) (ρ : Finpartition S) (hS : S.Nonempty) :
    (∑ π : Finpartition S,
      @ite ℝ (ρ ≤ π) (Classical.propDecidable (ρ ≤ π))
        (((-1 : ℝ) ^ (π.parts.card - 1)) *
          (Nat.factorial (π.parts.card - 1) : ℝ))
        0) =
      if ρ.parts.card = 1 then 1 else 0 := by
  classical
  have hSbot : S ≠ ⊥ := by
    simpa [Finset.bot_eq_empty, ← Finset.nonempty_iff_ne_empty] using hS
  by_cases h1 : ρ.parts.card = 1
  · rw [if_pos h1]
    obtain ⟨u, hu⟩ := Finset.card_eq_one.1 h1
    have huS : u = S := by
      have h := ρ.sup_parts
      rw [hu] at h
      simpa using h
    have htop : ∀ π : Finpartition S, π ≤ ρ := by
      intro π c hc
      exact ⟨u, by rw [hu]; exact Finset.mem_singleton_self u, huS ▸ π.le hc⟩
    rw [Finset.sum_eq_single_of_mem ρ (Finset.mem_univ ρ)]
    · rw [if_pos le_rfl, h1]
      norm_num
    · intro π _ hne
      rw [if_neg]
      intro hle
      exact hne (le_antisymm (htop π) hle)
  · rw [if_neg h1]
    have hcard2 : 1 < ρ.parts.card := by
      have h0 : ρ.parts.Nonempty := ρ.parts_nonempty hSbot
      have := Finset.card_pos.2 h0
      omega
    obtain ⟨p, hp, p₂, hp₂, hne⟩ := Finset.one_lt_card.1 hcard2
    obtain ⟨a, ha⟩ := ρ.nonempty_of_mem_parts hp
    have haS : a ∈ S := ρ.subset hp ha
    have hpne : p.Nonempty := ⟨a, ha⟩
    have hpart : ∀ π : Finpartition S, ρ ≤ π → p ⊆ π.part a := by
      intro π hπ
      obtain ⟨c, hc, hpc⟩ := hπ hp
      have hac : π.part a = c := π.part_eq_of_mem hc (hpc ha)
      rw [hac]
      exact hpc
    have hpartmem : ∀ π : Finpartition S, π.part a ∈ π.parts := fun π =>
      (Finpartition.part_mem π).2 haS
    have mkP : ∀ T : Finset (Finset α), (↑T : Set (Finset α)).PairwiseDisjoint id →
        T.sup id = S → (∅ ∉ T) → ∃ σ : Finpartition S, σ.parts = T := by
      intro T hd hsup hbot
      refine ⟨⟨T, Finset.supIndep_iff_pairwiseDisjoint.2 hd, hsup, ?_⟩, rfl⟩
      simpa [Finset.bot_eq_empty] using hbot
    have hsd : ∀ (π : Finpartition S), ρ ≤ π → p ∉ π.parts → (π.part a \ p).Nonempty := by
      intro π h1' h2'
      rw [Finset.sdiff_nonempty]
      intro hsub
      exact h2' (Finset.Subset.antisymm hsub (hpart π h1') ▸ hpartmem π)
    have hnesd : ∀ (π : Finpartition S), ρ ≤ π → p ∉ π.parts → π.part a \ p ≠ p := by
      intro π h1' h2' h
      have hdd : Disjoint p (π.part a \ p) := disjoint_sdiff_self_right
      rw [h] at hdd
      exact hpne.ne_empty (by simpa [Finset.bot_eq_empty] using disjoint_self.1 hdd)
    have hsdnotmem : ∀ (π : Finpartition S), ρ ≤ π → p ∉ π.parts →
        π.part a \ p ∉ π.parts.erase (π.part a) := by
      intro π h1' h2' hmem
      have hd := π.disjoint (hpartmem π) (Finset.mem_of_mem_erase hmem)
        (Ne.symm (Finset.ne_of_mem_erase hmem))
      obtain ⟨e, he⟩ := hsd π h1' h2'
      exact (Finset.disjoint_left.1 hd (Finset.mem_sdiff.1 he).1) he
    have hsplitex : ∀ π : Finpartition S, ρ ≤ π → p ∉ π.parts →
        ∃ σ : Finpartition S, σ.parts =
          insert p (insert (π.part a \ p) (π.parts.erase (π.part a))) := by
      intro π hπ hpπ
      have hD : π.part a ∈ π.parts := hpartmem π
      have hpD : p ⊆ π.part a := hpart π hπ
      have hdisjD : ∀ y ∈ π.parts.erase (π.part a), Disjoint (π.part a) y := by
        intro y hy
        exact π.disjoint hD (Finset.mem_of_mem_erase hy)
          (Ne.symm (Finset.ne_of_mem_erase hy))
      refine mkP _ ?_ ?_ ?_
      · intro x hx y hy hxy
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
          Finset.mem_erase] at hx hy
        simp only [Function.onFun, id_eq]
        rcases hx with rfl | rfl | ⟨hxne, hxmem⟩ <;>
          rcases hy with rfl | rfl | ⟨hyne, hymem⟩
        · exact absurd rfl hxy
        · exact disjoint_sdiff_self_right
        · exact (hdisjD y (Finset.mem_erase.2 ⟨hyne, hymem⟩)).mono_left hpD
        · exact disjoint_sdiff_self_left
        · exact absurd rfl hxy
        · exact (hdisjD y (Finset.mem_erase.2 ⟨hyne, hymem⟩)).mono_left Finset.sdiff_subset
        · exact ((hdisjD x (Finset.mem_erase.2 ⟨hxne, hxmem⟩)).mono_left hpD).symm
        · exact ((hdisjD x (Finset.mem_erase.2 ⟨hxne, hxmem⟩)).mono_left
            Finset.sdiff_subset).symm
        · exact π.disjoint hxmem hymem hxy
      · have h2' : p ⊔ (π.part a \ p) = π.part a := by
          simp only [Finset.sup_eq_union]
          exact Finset.union_sdiff_of_subset hpD
        have h3 : π.part a ⊔ (π.parts.erase (π.part a)).sup id = S := by
          have h := Finset.sup_insert (s := π.parts.erase (π.part a))
            (f := (id : Finset α → Finset α)) (b := π.part a)
          rw [Finset.insert_erase hD, π.sup_parts] at h
          simpa using h.symm
        rw [Finset.sup_insert, Finset.sup_insert, id_eq, id_eq, ← sup_assoc, h2', h3]
      · simp only [Finset.mem_insert, Finset.mem_erase, not_or]
        refine ⟨?_, ?_, ?_⟩
        · exact fun h => hpne.ne_empty h.symm
        · exact fun h => (hsd π hπ hpπ).ne_empty h.symm
        · exact fun h => π.empty_notMem_parts h.2
    have hmergeex : ∀ (π₁ : Finpartition S) (q : Finset α), p ∈ π₁.parts → q ∈ π₁.parts →
        q ≠ p → ∃ σ : Finpartition S,
          σ.parts = insert (p ∪ q) ((π₁.parts.erase p).erase q) := by
      intro π₁ q hpm hqm hqp
      refine mkP _ ?_ ?_ ?_
      · intro x hx y hy hxy
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
          Finset.mem_erase] at hx hy
        simp only [Function.onFun, id_eq]
        have hkey : ∀ z, z ≠ q → z ≠ p → z ∈ π₁.parts → Disjoint (p ∪ q) z := by
          intro z hzq hzp hzm
          rw [Finset.disjoint_union_left]
          exact ⟨π₁.disjoint hpm hzm (Ne.symm hzp), π₁.disjoint hqm hzm (Ne.symm hzq)⟩
        rcases hx with rfl | ⟨hxq, hxne, hxmem⟩ <;>
          rcases hy with rfl | ⟨hyq, hyne, hymem⟩
        · exact absurd rfl hxy
        · exact hkey y hyq hyne hymem
        · exact (hkey x hxq hxne hxmem).symm
        · exact π₁.disjoint hxmem hymem hxy
      · have h4 : q ⊔ ((π₁.parts.erase p).erase q).sup id = (π₁.parts.erase p).sup id := by
          have h := Finset.sup_insert (s := (π₁.parts.erase p).erase q)
            (f := (id : Finset α → Finset α)) (b := q)
          rw [Finset.insert_erase (Finset.mem_erase.2 ⟨hqp, hqm⟩)] at h
          simpa using h.symm
        have h3 : p ⊔ (π₁.parts.erase p).sup id = S := by
          have h := Finset.sup_insert (s := π₁.parts.erase p)
            (f := (id : Finset α → Finset α)) (b := p)
          rw [Finset.insert_erase hpm, π₁.sup_parts] at h
          simpa using h.symm
        rw [Finset.sup_insert, id_eq, ← Finset.sup_eq_union, sup_assoc, h4, h3]
      · simp only [Finset.mem_insert, Finset.mem_erase, not_or]
        refine ⟨?_, ?_⟩
        · exact fun h => hpne.ne_empty (Finset.union_eq_empty.1 h.symm).1
        · exact fun h => π₁.empty_notMem_parts h.2.2
    choose SP hSP using hsplitex
    choose MP hMP using hmergeex
    have hMdisj : ∀ (π₁ : Finpartition S) (q : Finset α), p ∈ π₁.parts → q ∈ π₁.parts → q ≠ p →
        Disjoint p q := fun π₁ q h1' h2' h3' => π₁.disjoint h1' h2' (Ne.symm h3')
    have hpuq : ∀ (π₁ : Finpartition S) (q : Finset α), p ∈ π₁.parts → q ∈ π₁.parts → q ≠ p →
        p ∪ q ≠ p := by
      intro π₁ q h1' h2' h3' h
      obtain ⟨e, he⟩ := π₁.nonempty_of_mem_parts h2'
      have hmem : e ∈ p := h ▸ Finset.mem_union_right _ he
      exact (Finset.disjoint_left.1 (hMdisj π₁ q h1' h2' h3') hmem) he
    have hpuqnotmem : ∀ (π₁ : Finpartition S) (q : Finset α) (h1' : p ∈ π₁.parts)
        (h2' : q ∈ π₁.parts) (h3' : q ≠ p), p ∪ q ∉ (π₁.parts.erase p).erase q := by
      intro π₁ q h1' h2' h3' hmem
      have hmem' := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmem)
      have hd := π₁.disjoint h1' hmem' (Ne.symm (hpuq π₁ q h1' h2' h3'))
      obtain ⟨e, he⟩ := hpne
      exact (Finset.disjoint_left.1 hd he) (Finset.mem_union_left _ he)
    have F1 : ∀ (π : Finpartition S) (h1' : ρ ≤ π) (h2' : p ∉ π.parts), ρ ≤ SP π h1' h2' := by
      intro π h1' h2' d hd
      rw [hSP π h1' h2']
      by_cases hdp : d = p
      · exact ⟨p, Finset.mem_insert_self _ _, hdp.le⟩
      · obtain ⟨c, hc, hdc⟩ := h1' hd
        by_cases hcD : c = π.part a
        · refine ⟨π.part a \ p, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
          rw [Finset.subset_sdiff]
          exact ⟨hcD ▸ hdc, ρ.disjoint hd hp hdp⟩
        · exact ⟨c, Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hcD, hc⟩)), hdc⟩
    have F2 : ∀ (π : Finpartition S) (h1' : ρ ≤ π) (h2' : p ∉ π.parts),
        p ∈ (SP π h1' h2').parts := by
      intro π h1' h2'
      rw [hSP π h1' h2']
      exact Finset.mem_insert_self _ _
    have F3 : ∀ (π : Finpartition S) (h1' : ρ ≤ π) (h2' : p ∉ π.parts),
        (SP π h1' h2').parts.card = π.parts.card + 1 := by
      intro π h1' h2'
      have hcard1 : 1 ≤ π.parts.card := Finset.card_pos.2 ⟨π.part a, hpartmem π⟩
      rw [hSP π h1' h2', Finset.card_insert_of_notMem, Finset.card_insert_of_notMem
        (hsdnotmem π h1' h2'), Finset.card_erase_of_mem (hpartmem π)]
      · omega
      · simp only [Finset.mem_insert, Finset.mem_erase, not_or]
        exact ⟨fun h => hnesd π h1' h2' h.symm, fun h => h2' h.2⟩
    have F4 : ∀ (π : Finpartition S) (h1' : ρ ≤ π) (h2' : p ∉ π.parts),
        π.part a \ p ∈ (SP π h1' h2').parts := by
      intro π h1' h2'
      rw [hSP π h1' h2']
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have F5a : ∀ (π₁ : Finpartition S) (q : Finset α) (hρ : ρ ≤ π₁) (h1' : p ∈ π₁.parts)
        (h2' : q ∈ π₁.parts) (h3' : q ≠ p), ρ ≤ MP π₁ q h1' h2' h3' := by
      intro π₁ q hρ h1' h2' h3' d hd
      rw [hMP]
      obtain ⟨c, hc, hdc⟩ := hρ hd
      by_cases hcp : c = p
      · exact ⟨p ∪ q, Finset.mem_insert_self _ _,
          (hcp ▸ hdc).trans Finset.subset_union_left⟩
      · by_cases hcq : c = q
        · exact ⟨p ∪ q, Finset.mem_insert_self _ _,
            (hcq ▸ hdc).trans Finset.subset_union_right⟩
        · exact ⟨c, Finset.mem_insert_of_mem
            (Finset.mem_erase.2 ⟨hcq, Finset.mem_erase.2 ⟨hcp, hc⟩⟩), hdc⟩
    have F5b : ∀ (π₁ : Finpartition S) (q : Finset α) (h1' : p ∈ π₁.parts) (h2' : q ∈ π₁.parts)
        (h3' : q ≠ p), p ∉ (MP π₁ q h1' h2' h3').parts := by
      intro π₁ q h1' h2' h3'
      rw [hMP]
      simp only [Finset.mem_insert, Finset.mem_erase, not_or]
      exact ⟨fun h => hpuq π₁ q h1' h2' h3' h.symm, fun h => h.2.1 rfl⟩
    have F5c : ∀ (π₁ : Finpartition S) (q : Finset α) (h1' : p ∈ π₁.parts) (h2' : q ∈ π₁.parts)
        (h3' : q ≠ p), (MP π₁ q h1' h2' h3').parts.card = π₁.parts.card - 1 := by
      intro π₁ q h1' h2' h3'
      have h2card : 2 ≤ π₁.parts.card := Finset.one_lt_card.2 ⟨p, h1', q, h2', Ne.symm h3'⟩
      rw [hMP, Finset.card_insert_of_notMem (hpuqnotmem π₁ q h1' h2' h3'),
        Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨h3', h2'⟩), Finset.card_erase_of_mem h1']
      omega
    have F6 : ∀ (π : Finpartition S) (h1' : ρ ≤ π) (h2' : p ∉ π.parts)
        (k1 : p ∈ (SP π h1' h2').parts) (k2 : π.part a \ p ∈ (SP π h1' h2').parts)
        (k3 : π.part a \ p ≠ p), MP (SP π h1' h2') (π.part a \ p) k1 k2 k3 = π := by
      intro π h1' h2' k1 k2 k3
      apply Finpartition.ext
      rw [hMP, hSP π h1' h2', Finset.erase_insert (by
        simp only [Finset.mem_insert, Finset.mem_erase, not_or]
        exact ⟨fun h => hnesd π h1' h2' h.symm, fun h => h2' h.2⟩),
        Finset.erase_insert (hsdnotmem π h1' h2')]
      have hu : p ∪ (π.part a \ p) = π.part a := Finset.union_sdiff_of_subset (hpart π h1')
      rw [hu, Finset.insert_erase (hpartmem π)]
    have F7a : ∀ (π₁ : Finpartition S) (q : Finset α) (h1' : p ∈ π₁.parts) (h2' : q ∈ π₁.parts)
        (h3' : q ≠ p), (MP π₁ q h1' h2' h3').part a = p ∪ q := by
      intro π₁ q h1' h2' h3'
      exact Finpartition.part_eq_of_mem _ (by rw [hMP]; exact Finset.mem_insert_self _ _)
        (Finset.mem_union_left _ ha)
    have F7b : ∀ (π₁ : Finpartition S) (q : Finset α) (h1' : p ∈ π₁.parts) (h2' : q ∈ π₁.parts)
        (h3' : q ≠ p), (p ∪ q) \ p = q := by
      intro π₁ q h1' h2' h3'
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hp'⟩
        · exact absurd h hp'
        · exact h
      · intro h
        exact ⟨Or.inr h, fun hep =>
          (Finset.disjoint_left.1 (hMdisj π₁ q h1' h2' h3') hep) h⟩
    have F7 : ∀ (π₁ : Finpartition S) (q : Finset α) (h1' : p ∈ π₁.parts) (h2' : q ∈ π₁.parts)
        (h3' : q ≠ p) (k1 : ρ ≤ MP π₁ q h1' h2' h3')
        (k2 : p ∉ (MP π₁ q h1' h2' h3').parts),
        SP (MP π₁ q h1' h2' h3') k1 k2 = π₁ := by
      intro π₁ q h1' h2' h3' k1 k2
      apply Finpartition.ext
      rw [hSP, F7a π₁ q h1' h2' h3', F7b π₁ q h1' h2' h3', hMP,
        Finset.erase_insert (hpuqnotmem π₁ q h1' h2' h3'),
        Finset.insert_erase (Finset.mem_erase.2 ⟨h3', h2'⟩), Finset.insert_erase h1']
    have hbig : ∀ π₁ : Finpartition S, ρ ≤ π₁ → p ∈ π₁.parts → 2 ≤ π₁.parts.card := by
      intro π₁ hρ hpm
      obtain ⟨c, hc, h2c⟩ := hρ hp₂
      have hcp : c ≠ p := by
        intro h
        obtain ⟨e, he⟩ := ρ.nonempty_of_mem_parts hp₂
        exact (Finset.disjoint_left.1 (ρ.disjoint hp₂ hp (Ne.symm hne)) he) (h ▸ h2c he)
      exact Finset.one_lt_card.2 ⟨p, hpm, c, hc, Ne.symm hcp⟩
    have step1 : (∑ π : Finpartition S,
        @ite ℝ (ρ ≤ π) (Classical.propDecidable (ρ ≤ π))
          (((-1 : ℝ) ^ (π.parts.card - 1)) * (Nat.factorial (π.parts.card - 1) : ℝ)) 0)
        = ∑ π ∈ Finset.univ.filter (fun π : Finpartition S => ρ ≤ π),
            ((-1 : ℝ) ^ (π.parts.card - 1)) * (Nat.factorial (π.parts.card - 1) : ℝ) := by
      rw [Finset.sum_filter]
    rw [step1, ← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter (fun π : Finpartition S => ρ ≤ π)) (fun π => p ∈ π.parts)]
    have mem1 : ∀ π ∈ (Finset.univ.filter (fun π : Finpartition S => ρ ≤ π)).filter
        (fun π => ¬ p ∈ π.parts), ρ ≤ π := by
      intro π hπ
      exact (Finset.mem_filter.1 (Finset.mem_filter.1 hπ).1).2
    have mem2 : ∀ π ∈ (Finset.univ.filter (fun π : Finpartition S => ρ ≤ π)).filter
        (fun π => ¬ p ∈ π.parts), p ∉ π.parts := by
      intro π hπ
      exact (Finset.mem_filter.1 hπ).2
    have mem3 : ∀ x ∈ ((Finset.univ.filter (fun π : Finpartition S => ρ ≤ π)).filter
        (fun π => p ∈ π.parts)).sigma (fun π₁ => π₁.parts.erase p), ρ ≤ x.1 := by
      intro x hx
      exact (Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_sigma.1 hx).1).1).2
    have mem4 : ∀ x ∈ ((Finset.univ.filter (fun π : Finpartition S => ρ ≤ π)).filter
        (fun π => p ∈ π.parts)).sigma (fun π₁ => π₁.parts.erase p), p ∈ x.1.parts := by
      intro x hx
      exact (Finset.mem_filter.1 (Finset.mem_sigma.1 hx).1).2
    have mem5 : ∀ x ∈ ((Finset.univ.filter (fun π : Finpartition S => ρ ≤ π)).filter
        (fun π => p ∈ π.parts)).sigma (fun π₁ => π₁.parts.erase p), x.2 ∈ x.1.parts := by
      intro x hx
      exact Finset.mem_of_mem_erase (Finset.mem_sigma.1 hx).2
    have mem6 : ∀ x ∈ ((Finset.univ.filter (fun π : Finpartition S => ρ ≤ π)).filter
        (fun π => p ∈ π.parts)).sigma (fun π₁ => π₁.parts.erase p), x.2 ≠ p := by
      intro x hx
      exact Finset.ne_of_mem_erase (Finset.mem_sigma.1 hx).2
    have step2 : (∑ π ∈ (Finset.univ.filter (fun π : Finpartition S => ρ ≤ π)).filter
          (fun π => ¬ p ∈ π.parts),
          ((-1 : ℝ) ^ (π.parts.card - 1)) * (Nat.factorial (π.parts.card - 1) : ℝ))
        = ∑ x ∈ ((Finset.univ.filter (fun π : Finpartition S => ρ ≤ π)).filter
            (fun π => p ∈ π.parts)).sigma (fun π₁ => π₁.parts.erase p),
            ((-1 : ℝ) ^ (x.1.parts.card - 1 - 1)) *
              (Nat.factorial (x.1.parts.card - 1 - 1) : ℝ) := by
      refine Finset.sum_bij'
        (fun π hπ => (⟨SP π (mem1 π hπ) (mem2 π hπ), π.part a \ p⟩ :
          (_ : Finpartition S) × Finset α))
        (fun x hx => MP x.1 x.2 (mem4 x hx) (mem5 x hx) (mem6 x hx)) ?_ ?_ ?_ ?_ ?_
      · intro π hπ
        refine Finset.mem_sigma.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_filter.2
          ⟨Finset.mem_univ _, F1 π (mem1 π hπ) (mem2 π hπ)⟩,
          F2 π (mem1 π hπ) (mem2 π hπ)⟩, ?_⟩
        exact Finset.mem_erase.2 ⟨hnesd π (mem1 π hπ) (mem2 π hπ),
          F4 π (mem1 π hπ) (mem2 π hπ)⟩
      · intro x hx
        exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _,
          F5a x.1 x.2 (mem3 x hx) (mem4 x hx) (mem5 x hx) (mem6 x hx)⟩,
          F5b x.1 x.2 (mem4 x hx) (mem5 x hx) (mem6 x hx)⟩
      · intro π hπ
        exact F6 π (mem1 π hπ) (mem2 π hπ) _ _ _
      · intro x hx
        refine Sigma.ext_iff.2 ⟨?_, heq_of_eq ?_⟩
        · exact F7 x.1 x.2 (mem4 x hx) (mem5 x hx) (mem6 x hx) _ _
        · rw [F7a x.1 x.2 (mem4 x hx) (mem5 x hx) (mem6 x hx)]
          exact F7b x.1 x.2 (mem4 x hx) (mem5 x hx) (mem6 x hx)
      · intro π hπ
        rw [F3 π (mem1 π hπ) (mem2 π hπ)]
        simp
    rw [step2]
    have step3 : (∑ x ∈ ((Finset.univ.filter (fun π : Finpartition S => ρ ≤ π)).filter
          (fun π => p ∈ π.parts)).sigma (fun π₁ => π₁.parts.erase p),
          ((-1 : ℝ) ^ (x.1.parts.card - 1 - 1)) *
            (Nat.factorial (x.1.parts.card - 1 - 1) : ℝ))
        = ∑ π₁ ∈ (Finset.univ.filter (fun π : Finpartition S => ρ ≤ π)).filter
            (fun π => p ∈ π.parts), ∑ _q ∈ π₁.parts.erase p,
            ((-1 : ℝ) ^ (π₁.parts.card - 1 - 1)) *
              (Nat.factorial (π₁.parts.card - 1 - 1) : ℝ) :=
      Finset.sum_sigma _ _ _
    rw [step3]
    have step4 : ∀ π₁ ∈ (Finset.univ.filter (fun π : Finpartition S => ρ ≤ π)).filter
        (fun π => p ∈ π.parts), (∑ _q ∈ π₁.parts.erase p,
          ((-1 : ℝ) ^ (π₁.parts.card - 1 - 1)) *
            (Nat.factorial (π₁.parts.card - 1 - 1) : ℝ))
        = ((π₁.parts.card - 1 : ℕ) : ℝ) * (((-1 : ℝ) ^ (π₁.parts.card - 1 - 1)) *
            (Nat.factorial (π₁.parts.card - 1 - 1) : ℝ)) := by
      intro π₁ hπ₁
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_filter.1 hπ₁).2,
        nsmul_eq_mul]
    rw [Finset.sum_congr rfl step4, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero ?_
    intro π₁ hπ₁
    have h2card : 2 ≤ π₁.parts.card :=
      hbig π₁ (Finset.mem_filter.1 (Finset.mem_filter.1 hπ₁).1).2
        (Finset.mem_filter.1 hπ₁).2
    obtain ⟨m, hm⟩ : ∃ m, π₁.parts.card = m + 2 := ⟨π₁.parts.card - 2, by omega⟩
    rw [hm]
    have e2 : m + 2 - 1 - 1 = m := by omega
    have e1 : m + 2 - 1 = m + 1 := by omega
    rw [e2, e1, pow_succ, Nat.factorial_succ]
    push_cast
    ring

@[blueprint "lem:mixed-moment-configuration-expansion"
  (statement := /-- Let $\ell\geq1$, let the finite sets within each of the families $I$, $A$, and $B$ be pairwise disjoint, put $U=I_{[\ell]}$, and suppose that $\eta,x_0,y_0\geq0$ and $|U|x_0<1$.  There exists a rank function $\varrho:\iota\to\mathbb N$ that is injective on $U$ such that the absolute sum of the weights of all admissible occurrence-labelled configurations is finite and
  \[
  \sum_{\pi\in\Pi([\ell])}(-1)^{|\pi|-1}(|\pi|-1)!
    \prod_{C\in\pi}M(C)
  =
  \sum_{\substack{\Gamma\ {\rm admissible}\\\Gamma\ {\rm connected}}}w(\Gamma).
  \]
  Admissibility, connectivity, and weight are those of \cref{def:mixed-moment-configuration-admissible,def:mixed-moment-configuration-connected,def:mixed-moment-configuration-weight}. -/)
  (proof := /-- Choose a total ordering of the finite set $U$ and extend its rank function to $\iota$.  For $u\in U\cap A_j$, let $k$ be the number of elements of $U\cap A_j$ preceding $u$.  Since $kx_0<1$, expand
  \[
    (1-kx_0)^{-1}=\sum_{n\geq0}x_0^n
      \sum_{(v_1,\ldots,v_n)\in[k]^n}1.
  \]
  The list $(v_1,\ldots,v_n)$ is exactly the word $W_{j,u}$ in \cref{def:mixed-moment-occurrence-configuration}; its list indices retain all occurrence positions.  For $u\in U\cap B_i$, expand $1-ky_0$ as the choice between no predecessor and one of the $k$ preceding elements with weight $-y_0$.  Multiplying these expansions gives precisely the admissible configurations and their weights.  The reciprocal series are absolutely summable because $kx_0<1$, and only finitely many $B$-choices occur.  Pairwise disjointness of the $I_t$ gives the common factor $\eta^{|U|}$.

  Fix an admissible configuration.  It occurs in the product indexed by a partition $\pi$ exactly when every edge of its induced graph lies in one block of $\pi$, equivalently when its component partition refines $\pi$.  Apply \cref{lem:finpartition-mobius-connected-cancellation} to that component partition.  Its multiplier is one when the induced graph is connected and zero otherwise.  Absolute summability permits the finite partition sum to be interchanged with the configuration sum, leaving exactly the asserted sum over connected admissible configurations. -/)
  (title := /-- Absolutely convergent connected-configuration expansion -/)
  (latexEnv := "lemma")]
lemma mixed_moment_configuration_expansion
    {ι : Type*} [DecidableEq ι] {ℓ q r : ℕ}
    (I : Fin ℓ → Finset ι) (A : Fin q → Finset ι)
    (B : Fin r → Finset ι) (η x₀ y₀ : ℝ)
    (hI : Set.univ.PairwiseDisjoint I)
    (hA : Set.univ.PairwiseDisjoint A)
    (hB : Set.univ.PairwiseDisjoint B)
    (hℓ : 0 < ℓ) (hη : 0 ≤ η) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀)
    (hconv : (total_index_count I : ℝ) * x₀ < 1) :
    ∃ rank : ι → ℕ,
      Set.InjOn rank (indexed_union I Finset.univ : Set ι) ∧
      Summable (fun Γ :
        {Γ : mixed_moment_occurrence_configuration ι q r //
          mixed_moment_configuration_admissible I A B rank Γ} ↦
        |mixed_moment_configuration_weight I η x₀ y₀ Γ.1|) ∧
      (∑ π : Finpartition (Finset.univ : Finset (Fin ℓ)),
        ((-1 : ℝ) ^ (π.parts.card - 1)) *
          (Nat.factorial (π.parts.card - 1) : ℝ) *
          ∏ C ∈ π.parts, mixed_moment_right_hand_side I A B η x₀ y₀ C) =
        ∑' Γ :
          {Γ : mixed_moment_occurrence_configuration ι q r //
            mixed_moment_configuration_admissible I A B rank Γ ∧
            mixed_moment_configuration_connected I Γ},
          mixed_moment_configuration_weight I η x₀ y₀ Γ.1 := by
  classical
  obtain ⟨U, hU⟩ : ∃ s : Finset ι, s = indexed_union I Finset.univ := ⟨_, rfl⟩
  have hLcard : U.card = total_index_count I := by simp [hU, total_index_count]
  obtain ⟨rank, hrankdef⟩ : ∃ f : ι → ℕ,
      f = fun u => if h : u ∈ U then ((U.equivFin ⟨u, h⟩ : Fin U.card) : ℕ) else 0 := ⟨_, rfl⟩
  have hUmem : ∀ u : ι, (u ∈ indexed_union I Finset.univ ↔ u ∈ U) := fun u => by rw [hU]
  have hrank : Set.InjOn rank (U : Set ι) := by
    intro u hu v hv huv
    have hu' : u ∈ U := Finset.mem_coe.1 hu
    have hv' : v ∈ U := Finset.mem_coe.1 hv
    rw [hrankdef] at huv
    simp only [dif_pos hu', dif_pos hv'] at huv
    have hfe : (U.equivFin ⟨u, hu'⟩ : Fin U.card) = (U.equivFin ⟨v, hv'⟩ : Fin U.card) :=
      Fin.val_injective huv
    exact congrArg Subtype.val (U.equivFin.injective hfe)
  have htall : ∀ u : ι, ∃ t : Fin ℓ, u ∈ U → u ∈ I t := by
    intro u
    by_cases hu : u ∈ U
    · obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.1 ((hUmem u).2 hu)
      exact ⟨t, fun _ => ht⟩
    · exact ⟨⟨0, hℓ⟩, fun h => absurd h hu⟩
  choose tt htt using htall
  have hmemU : ∀ (u : ι) (t : Fin ℓ), u ∈ I t → u ∈ U := by
    intro u t ht
    rw [hU]
    exact Finset.mem_biUnion.2 ⟨t, Finset.mem_univ t, ht⟩
  have htuniq : ∀ (u : ι) (t : Fin ℓ), u ∈ I t → tt u = t := by
    intro u t hut
    by_contra hne
    exact Finset.disjoint_left.1 (hI (Set.mem_univ (tt u)) (Set.mem_univ t) hne)
      (htt u (hmemU u t hut)) hut
  have htUD : ∀ (Δ : Finset (Fin ℓ)) (u : ι), u ∈ U →
      (u ∈ indexed_union I Δ ↔ tt u ∈ Δ) := by
    intro Δ u huU
    constructor
    · intro h
      obtain ⟨t, htΔ, hut⟩ := Finset.mem_biUnion.1 h
      rw [← htuniq u t hut] at htΔ
      exact htΔ
    · intro hΔ
      exact Finset.mem_biUnion.2 ⟨tt u, hΔ, htt u huU⟩
  have hUDmono : ∀ (Δ₁ Δ₂ : Finset (Fin ℓ)), Δ₁ ⊆ Δ₂ →
      indexed_union I Δ₁ ⊆ indexed_union I Δ₂ := by
    intro Δ₁ Δ₂ h
    refine Finset.subset_iff.2 fun u hu => ?_
    obtain ⟨t, ht, hut⟩ := Finset.mem_biUnion.1 hu
    exact Finset.mem_biUnion.2 ⟨t, h ht, hut⟩
  have hUDdisj : ∀ (Δ₁ Δ₂ : Finset (Fin ℓ)), Disjoint Δ₁ Δ₂ →
      Disjoint (indexed_union I Δ₁) (indexed_union I Δ₂) := by
    intro Δ₁ Δ₂ hdisj
    rw [Finset.disjoint_left]
    intro u hu₁ hu₂
    obtain ⟨t₁, ht₁, hut₁⟩ := Finset.mem_biUnion.1 hu₁
    obtain ⟨t₂, ht₂, hut₂⟩ := Finset.mem_biUnion.1 hu₂
    exact Finset.disjoint_left.1 (hI (Set.mem_univ t₁) (Set.mem_univ t₂)
      (Finset.disjoint_iff_ne.1 hdisj t₁ ht₁ t₂ ht₂)) hut₁ hut₂
  have hpartsdisj : ∀ (π : Finpartition (Finset.univ : Finset (Fin ℓ))),
      (↑π.parts : Set (Finset (Fin ℓ))).PairwiseDisjoint (fun C => indexed_union I C) := by
    intro π C₁ hC₁ C₂ hC₂ hne
    exact hUDdisj C₁ C₂ (π.disjoint hC₁ hC₂ hne)
  have hUDcover : ∀ (π : Finpartition (Finset.univ : Finset (Fin ℓ))),
      π.parts.biUnion (fun C => indexed_union I C) = U := by
    intro π
    refine Finset.ext fun u => ?_
    constructor
    · intro hu
      obtain ⟨C, hC, huC⟩ := Finset.mem_biUnion.1 hu
      rw [hU]
      exact hUDmono C Finset.univ (π.subset hC) huC
    · intro hu
      rw [hU] at hu
      obtain ⟨t, ht, hut⟩ := Finset.mem_biUnion.1 hu
      have htt' : tt u ∈ Finset.univ := Finset.mem_univ _
      rw [← π.sup_parts] at htt'
      obtain ⟨C, hC, hCt⟩ := Finset.mem_sup.1 htt'
      exact Finset.mem_biUnion.2 ⟨C, hC, Finset.mem_biUnion.2 ⟨tt u, hCt, htt u (hmemU u t hut)⟩⟩
  have hUDsumsplit : ∀ (π : Finpartition (Finset.univ : Finset (Fin ℓ))) (g : ι → ℕ),
      (∑ u ∈ U, g u) = ∑ C ∈ π.parts, ∑ u ∈ indexed_union I C, g u := by
    intro π g
    rw [← hUDcover π, Finset.sum_biUnion (hpartsdisj π)]
  have hUDcard : ∀ (π : Finpartition (Finset.univ : Finset (Fin ℓ))),
      U.card = ∑ C ∈ π.parts, (indexed_union I C).card := by
    intro π
    rw [← hUDcover π, Finset.card_biUnion (hpartsdisj π)]
  obtain ⟨admW, hadmW⟩ : ∃ f : Finset (Fin ℓ) → (Fin q → ι → List ι) → Prop,
      f = fun Δ W => ∀ j u v, v ∈ W j u →
        u ∈ indexed_union I Δ ∩ A j ∧ v ∈ indexed_union I Δ ∩ A j ∧ rank v < rank u := ⟨_, rfl⟩
  obtain ⟨admB, hadmB⟩ : ∃ f : Finset (Fin ℓ) → (Fin r → ι → Option ι) → Prop,
      f = fun Δ b => ∀ i u v, b i u = some v →
        u ∈ indexed_union I Δ ∩ B i ∧ v ∈ indexed_union I Δ ∩ B i ∧ rank v < rank u := ⟨_, rfl⟩
  have hrankU : Set.InjOn rank (indexed_union I Finset.univ : Set ι) := by
    rw [← hU]
    exact hrank
  have hadmsplit : ∀ Γ : mixed_moment_occurrence_configuration ι q r,
      mixed_moment_configuration_admissible I A B rank Γ ↔
      admW Finset.univ Γ.aWords ∧ admB Finset.univ Γ.bChoice := by
    intro Γ
    constructor
    · intro h
      constructor
      · rw [hadmW]; exact h.2.2.1
      · rw [hadmB]; exact h.2.2.2
    · rintro ⟨hw, hb⟩
      simp only [hadmW] at hw
      simp only [hadmB] at hb
      show Set.InjOn rank (indexed_union I Finset.univ : Set ι) ∧
        (∀ j u, u ∉ indexed_union I Finset.univ ∩ A j → Γ.aWords j u = []) ∧
        (∀ j u v, v ∈ Γ.aWords j u →
          u ∈ indexed_union I Finset.univ ∩ A j ∧
          v ∈ indexed_union I Finset.univ ∩ A j ∧ rank v < rank u) ∧
        ∀ i u v, Γ.bChoice i u = some v →
          u ∈ indexed_union I Finset.univ ∩ B i ∧
          v ∈ indexed_union I Finset.univ ∩ B i ∧ rank v < rank u
      refine ⟨hrankU, ?_, hw, hb⟩
      intro j u hu
      by_contra hne
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil (Γ.aWords j u) hne
      exact hu ((hw j u v hv).1)
  obtain ⟨NA, hNA⟩ : ∃ f : Finset (Fin ℓ) → mixed_moment_occurrence_configuration ι q r → ℕ,
      f = fun Δ Γ => ∑ j : Fin q, ∑ u ∈ indexed_union I Δ, (Γ.aWords j u).length := ⟨_, rfl⟩
  obtain ⟨NB, hNB⟩ : ∃ f : Finset (Fin ℓ) → mixed_moment_occurrence_configuration ι q r → ℕ,
      f = fun Δ Γ => ∑ i : Fin r,
        ((indexed_union I Δ).filter fun u => Γ.bChoice i u ≠ none).card := ⟨_, rfl⟩
  have hweight : ∀ Γ : mixed_moment_occurrence_configuration ι q r,
      mixed_moment_configuration_weight I η x₀ y₀ Γ =
        η ^ U.card * x₀ ^ (NA Finset.univ Γ) * (-y₀) ^ (NB Finset.univ Γ) := by
    intro Γ
    simp only [mixed_moment_configuration_weight, hNA, hNB, ← hLcard, ← hU]
  obtain ⟨kS, hkS⟩ : ∃ f : Finset ι → ι → ℕ,
      f = fun S u => (S.filter fun v => rank v < rank u).card := ⟨_, rfl⟩
  have hRANKPROD : ∀ (S : Finset ι) (F : ℕ → ℝ), (∀ u ∈ S, u ∈ U) → F 0 = 1 →
      ∏ k ∈ Finset.range (S.card - 1), F (k + 1) = ∏ u ∈ S, F (kS S u) := by
    intro S F hS hF0
    have hkcard : ∀ u ∈ S, (S.filter fun v => rank v < rank u).card < S.card := by
      intro u hu
      refine Finset.card_lt_card ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      exact lt_irrefl _ (Finset.mem_filter.1 (heq hu)).2
    have hinj : ∀ u ∈ S, ∀ v ∈ S, kS S u = kS S v → u = v := by
      intro u hu v hv h
      simp only [hkS] at h
      by_contra hne
      rcases lt_trichotomy (rank u) (rank v) with hlt | heq | hlt
      · have hsub : (S.filter fun w => rank w < rank u) ⊆
            (S.filter fun w => rank w < rank v) := by
          intro w hw
          have h1 := (Finset.mem_filter.1 hw).2
          exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hw).1, by omega⟩
        have hmem : u ∈ S.filter fun w => rank w < rank v :=
          Finset.mem_filter.2 ⟨hu, hlt⟩
        have hclt : (S.filter fun w => rank w < rank u).card <
            (S.filter fun w => rank w < rank v).card := by
          refine Finset.card_lt_card ⟨hsub, ?_⟩
          intro heq
          exact lt_irrefl _ (Finset.mem_filter.1 (heq hmem)).2
        omega
      · exact hne (hrank (hS u hu) (hS v hv) heq)
      · have hsub : (S.filter fun w => rank w < rank v) ⊆
            (S.filter fun w => rank w < rank u) := by
          intro w hw
          have h1 := (Finset.mem_filter.1 hw).2
          exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hw).1, by omega⟩
        have hmem : v ∈ S.filter fun w => rank w < rank u :=
          Finset.mem_filter.2 ⟨hv, hlt⟩
        have hclt : (S.filter fun w => rank w < rank v).card <
            (S.filter fun w => rank w < rank u).card := by
          refine Finset.card_lt_card ⟨hsub, ?_⟩
          intro heq
          exact lt_irrefl _ (Finset.mem_filter.1 (heq hmem)).2
        omega
    have himg : Finset.image (kS S) S = Finset.range S.card := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro k hk
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hk
        exact Finset.mem_range.2 (by simp only [hkS]; exact hkcard u hu)
      · rw [Finset.card_image_of_injOn hinj]
        simp
    have hshift : ∏ k ∈ Finset.range (S.card - 1), F (k + 1) =
        ∏ k ∈ Finset.range S.card, F k := by
      rcases Nat.eq_zero_or_pos S.card with h0 | h0
      · rw [h0]
        simp
      · obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 := ⟨S.card - 1, by omega⟩
        rw [hm]
        simp only [Nat.add_sub_cancel]
        rw [Finset.prod_range_succ', hF0, mul_one]
    calc ∏ k ∈ Finset.range (S.card - 1), F (k + 1) = ∏ k ∈ Finset.range S.card, F k := hshift
      _ = ∏ k ∈ Finset.image (kS S) S, F k := by rw [himg]
      _ = ∏ u ∈ S, F (kS S u) := Finset.prod_image hinj
  have hXeq : ∀ (S : Finset ι) (a : ℝ), (∀ u ∈ S, u ∈ U) →
      mixed_moment_x_factor a S = ∏ u ∈ S, (1 - (kS S u : ℝ) * a)⁻¹ := by
    intro S a hS
    rw [mixed_moment_x_factor]
    refine hRANKPROD S (fun k => (1 - (k : ℝ) * a)⁻¹) hS ?_
    simp
  have hYeq : ∀ (S : Finset ι) (b : ℝ), (∀ u ∈ S, u ∈ U) →
      mixed_moment_y_factor b S = ∏ u ∈ S, (1 - (kS S u : ℝ) * b) := by
    intro S b hS
    rw [mixed_moment_y_factor]
    refine hRANKPROD S (fun k => 1 - (k : ℝ) * b) hS ?_
    simp
  have hC1 : ∀ (P : Finset ι) (a : ℝ), 0 ≤ a → a * (P.card : ℝ) < 1 →
      HasSum (fun w : List ι => if (∀ v ∈ w, v ∈ P) then a ^ w.length else 0)
        ((1 - (P.card : ℝ) * a)⁻¹) := by
    intro P a ha hlt
    have hc : (0 : ℝ) ≤ (P.card : ℝ) := by positivity
    have hr1 : (P.card : ℝ) * a < 1 := by rwa [mul_comm] at hlt
    have hcardpow : ∀ n : ℕ, ∑ _g : Fin n → ↥P, a ^ n = ((P.card : ℝ) ^ n) * a ^ n := by
      intro n
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_pi, Fintype.card_coe,
        Fin.prod_const, Nat.cast_pow]
    have hHScongr : ∀ {β : Type} {f g : β → ℝ} {s : ℝ}, HasSum f s → (∀ b, f b = g b) →
        HasSum g s := by
      intro β f g s h hfg
      have hs : Summable g := h.summable.congr hfg
      have hs2 : ∑' b, g b = s := by
        rw [← h.tsum_eq, tsum_congr hfg]
      rw [← hs2]
      exact hs.hasSum
    have hfib : ∀ n : ℕ, HasSum (fun _g : Fin n → ↥P => a ^ n) (((P.card : ℝ) ^ n) * a ^ n) := by
      intro n
      rw [← hcardpow n]
      exact hasSum_fintype _
    have hsigsum : Summable (fun p : (Σ n : ℕ, Fin n → ↥P) => a ^ p.1) := by
      rw [summable_sigma_of_nonneg (fun p => pow_nonneg ha p.1)]
      refine ⟨fun n => (hfib n).summable, ?_⟩
      have hconv : Summable (fun n : ℕ => ((P.card : ℝ) * a) ^ n) :=
        summable_geometric_of_abs_lt_one (by
          rw [abs_of_nonneg (mul_nonneg hc ha)]; exact hr1)
      refine hconv.congr ?_
      intro n
      rw [tsum_fintype, hcardpow, mul_pow]
    have hgeom : HasSum (fun n : ℕ => ((P.card : ℝ) ^ n) * a ^ n)
        ((1 - (P.card : ℝ) * a)⁻¹) :=
      hHScongr (hasSum_geometric_of_abs_lt_one (r := (P.card : ℝ) * a) (by
        rw [abs_of_nonneg (mul_nonneg hc ha)]; exact hr1)) (fun n => mul_pow _ _ n)
    have hmain : HasSum (fun p : (Σ n : ℕ, Fin n → ↥P) => a ^ p.1)
        ((1 - (P.card : ℝ) * a)⁻¹) :=
      HasSum.sigma_of_hasSum hgeom hfib hsigsum
    obtain ⟨hE, hEapp⟩ : ∃ E : ((Σ n : ℕ, Fin n → ↥P) ≃ {w : List ι // ∀ v ∈ w, v ∈ P}),
        ∀ p : Σ n : ℕ, Fin n → ↥P, (E p : List ι) = List.ofFn fun i => (p.2 i : ι) := by
      refine ⟨{ toFun := fun p => ⟨List.ofFn fun i => (p.2 i : ι), by
                  intro v hv
                  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
                  exact (p.2 i).2⟩
                invFun := fun w => ⟨w.1.length,
                  fun i => ⟨w.1.get i, w.2 _ (List.get_mem _ i)⟩⟩
                left_inv := ?_
                right_inv := ?_ }, fun p => rfl⟩
      · rintro ⟨n, f⟩
        refine Fin.sigma_eq_of_eq_comp_cast (List.length_ofFn) ?_
        funext i
        simp only [List.get_ofFn, Subtype.coe_mk]
        rfl
      · rintro ⟨w, hw⟩
        apply Subtype.ext
        simp only [Subtype.coe_mk]
        exact List.ofFn_get w
    have hsub : HasSum (fun w : {w : List ι // ∀ v ∈ w, v ∈ P} => a ^ w.1.length)
        ((1 - (P.card : ℝ) * a)⁻¹) := by
      refine (Equiv.hasSum_iff hE).mp (HasSum.congr_fun hmain ?_)
      intro p
      show a ^ ((hE p : {w : List ι // ∀ v ∈ w, v ∈ P}).val.length) = a ^ p.fst
      rw [hEapp p]
      simp [List.length_ofFn]
    refine HasSum.congr_fun
      ((hasSum_subtype_iff_indicator
        (f := fun w : List ι => a ^ w.length)
        (s := {w : List ι | ∀ v ∈ w, v ∈ P})).mp hsub) ?_
    intro w
    by_cases hw : ∀ v ∈ w, v ∈ P
    · rw [if_pos hw, Set.indicator_of_mem (by simpa only [Set.mem_setOf_eq] using hw)]
    · rw [if_neg hw, Set.indicator_of_notMem (by
        intro hmem
        exact hw hmem)]
  have IP : ∀ (s : Finset ↥U) (p : ↥U → Prop) (f : ↥U → ℝ),
      (if (∀ x ∈ s, p x) then ∏ x ∈ s, f x else (0 : ℝ)) =
        ∏ x ∈ s, (if p x then f x else 0) := by
    intro s p f
    by_cases h : ∀ x ∈ s, p x
    · rw [if_pos h]
      exact Finset.prod_congr rfl fun x hx => (if_pos (h x hx)).symm
    · rw [if_neg h]
      have hex : ∃ x ∈ s, ¬ p x := by
        by_contra hcon
        exact h (fun x hx => by_contra fun hpx => hcon ⟨x, hx, hpx⟩)
      obtain ⟨x, hx, hpx⟩ := hex
      exact (Finset.prod_eq_zero hx (if_neg hpx)).symm
  have NORM : ∀ {β : Type _} (f : β → ℝ), Summable f → Summable fun x => ‖f x‖ := by
    intro β f h
    simpa [Real.norm_eq_abs] using Summable.abs h
  have CORE : ∀ (n : ℕ) (τ : Type _) (a : Fin n → ℝ) (g : Fin n → τ → ℝ),
      (∀ i, HasSum (g i) (a i)) →
      HasSum (fun F : Fin n → τ => ∏ i, g i (F i)) (∏ i, a i) := by
    intro n
    induction n with
    | zero =>
      intro τ a g _
      have h1 : (fun F : Fin 0 → τ => ∏ i, g i (F i)) = fun _ => (1 : ℝ) := by
        funext F; simp
      rw [h1]
      simpa using hasSum_unique (f := fun _ : Fin 0 → τ => (1 : ℝ))
    | succ n ih =>
      intro τ a g hga
      obtain ⟨heq, heqapp⟩ : ∃ f : τ × (Fin n → τ) ≃ (Fin (n + 1) → τ),
          ∀ p : τ × (Fin n → τ), ⇑f p = Fin.cons p.1 p.2 :=
        ⟨Fin.consEquiv (fun _ : Fin (n + 1) => τ), fun p => rfl⟩
      obtain ⟨Z, hZ⟩ : ∃ f : (Fin n → τ) → ℝ, ∀ x, f x = ∏ i, g i.succ (x i) :=
        ⟨_, fun _ => rfl⟩
      have hIH : HasSum Z (∏ i : Fin n, a i.succ) :=
        HasSum.congr_fun
          (ih τ (fun i : Fin n => a i.succ) (fun i : Fin n => g i.succ)
            (fun i : Fin n => hga i.succ)) hZ
      have hprod : Summable (fun p : τ × (Fin n → τ) => g 0 p.1 * Z p.2) :=
        summable_mul_of_summable_norm (f := g 0) (g := Z)
          (NORM _ (hga 0).summable) (NORM _ hIH.summable)
      have hmul : HasSum (fun p : τ × (Fin n → τ) => g 0 p.1 * Z p.2)
          (a 0 * ∏ i : Fin n, a i.succ) := HasSum.mul (hga 0) hIH hprod
      refine (Equiv.hasSum_iff
        (f := fun F : Fin (n + 1) → τ => ∏ i, g i (F i)) heq).mp ?_
      have hf : ((fun F : Fin (n + 1) → τ => ∏ i, g i (F i)) ∘ ⇑heq) =
          fun p : τ × (Fin n → τ) => g 0 p.1 * ∏ i, g i.succ (p.2 i) := by
        funext p
        show ∏ i, g i (⇑heq p i) = g 0 p.1 * ∏ i, g i.succ (p.2 i)
        rw [heqapp p]
        simp [Fin.prod_univ_succ]
      rw [hf, Fin.prod_univ_succ]
      refine HasSum.congr_fun hmul ?_
      intro p
      rw [hZ p.2]
  have COREFT : ∀ (σ : Type _) [Fintype σ] (τ : Type _) (a : σ → ℝ) (g : σ → τ → ℝ),
      (∀ s, HasSum (g s) (a s)) →
      HasSum (fun F : σ → τ => ∏ s, g s (F s)) (∏ s, a s) := by
    intro σ _ τ a g hga
    obtain ⟨n, e, -⟩ : ∃ n : ℕ, ∃ e : σ ≃ Fin n, True :=
      ⟨Fintype.card σ, Fintype.equivFin σ, trivial⟩
    obtain ⟨hf, hfapp⟩ : ∃ f : (Fin n → τ) ≃ (σ → τ),
        ∀ F' : Fin n → τ, f F' = fun s => F' (e s) :=
      ⟨{ toFun := fun F' s => F' (e s)
         invFun := fun F i => F (e.symm i)
         left_inv := by
           intro F'
           funext i
           show F' (e (e.symm i)) = F' i
           rw [e.apply_symm_apply]
         right_inv := by
           intro F
           funext s
           show F (e.symm (e s)) = F s
           rw [e.symm_apply_apply] },
        fun F' => rfl⟩
    refine (Equiv.hasSum_iff (f := fun F : σ → τ => ∏ s, g s (F s)) hf).mp ?_
    have hfun : ((fun F : σ → τ => ∏ s, g s (F s)) ∘ ⇑hf) =
        fun F' : Fin n → τ => ∏ i, g (e.symm i) (F' i) := by
      funext F'
      show ∏ s, g s (⇑hf F' s) = ∏ i, g (e.symm i) (F' i)
      rw [hfapp F']
      refine Fintype.prod_equiv e (fun s => g s (F' (e s)))
        (fun i => g (e.symm i) (F' i))
        (fun s => by rw [e.symm_apply_apply])
    have hval : ∏ s, a s = ∏ i : Fin n, a (e.symm i) :=
      Fintype.prod_equiv e a (fun i => a (e.symm i))
        (fun s => by rw [e.symm_apply_apply])
    rw [hfun, hval]
    exact CORE n τ (fun i => a (e.symm i)) (fun i => g (e.symm i))
      (fun i => hga (e.symm i))
  have RESTR : ∀ (τ : Type _) (junk : ι → τ) (G : (ι → τ) → ℝ) (S : ℝ),
      (∀ F : ι → τ, (∃ u : ι, u ∉ U ∧ F u ≠ junk u) → G F = 0) →
      HasSum (fun F₀ : ↥U → τ =>
        G (fun u => if h : u ∈ U then F₀ ⟨u, h⟩ else junk u)) S →
      HasSum G S := by
    intro τ junk G S hG hsub
    obtain ⟨extf, hextf⟩ : ∃ f : (↥U → τ) → (ι → τ),
        f = fun F₀ u => if h : u ∈ U then F₀ ⟨u, h⟩ else junk u := ⟨_, rfl⟩
    have hinj : Function.Injective extf := by
      intro F₁ F₂ h
      funext p
      have h1 : extf F₁ (p : ι) = extf F₂ (p : ι) := by rw [h]
      rw [hextf] at h1
      simp only at h1
      have h1' : (if h : (p : ι) ∈ U then F₁ ⟨(p : ι), h⟩ else junk (p : ι))
          = (if h : (p : ι) ∈ U then F₂ ⟨(p : ι), h⟩ else junk (p : ι)) := h1
      simpa only [dif_pos p.2] using h1'
    have hvanish : ∀ F : ι → τ, F ∉ Set.range extf → G F = 0 := by
      intro F hF
      refine hG F ?_
      by_contra hcon
      rw [not_exists] at hcon
      refine hF ⟨fun p => F (p : ι), ?_⟩
      rw [hextf]
      funext u
      by_cases hu : u ∈ U
      · simp only [dif_pos hu]
      · have hfu : F u = junk u := by
          by_contra hne
          exact hcon u ⟨hu, hne⟩
        simp only [dif_neg hu, hfu]
    have hcoepress : HasSum (fun F₀ : ↥U → τ => G (extf F₀)) S := by
      have h1 : (fun F₀ : ↥U → τ => G (extf F₀))
          = fun F₀ : ↥U → τ =>
            G (fun u => if h : u ∈ U then F₀ ⟨u, h⟩ else junk u) := by
        funext F₀
        rw [hextf]
      rw [h1]
      exact hsub
    have hstep1 : HasSum (G ∘ Subtype.val : ↥(Set.range extf) → ℝ) S :=
      (Equiv.hasSum_iff (Equiv.ofInjective extf hinj)).mp hcoepress
    have hstep2 : HasSum ((Set.range extf).indicator G) S :=
      hasSum_subtype_iff_indicator.mp hstep1
    refine HasSum.congr_fun hstep2 ?_
    intro F
    by_cases hF : F ∈ Set.range extf
    · rw [Set.indicator_of_mem hF]
    · rw [hvanish F hF, Set.indicator_of_notMem hF]
  have OPT : ∀ (P : Finset ι) (c : ℝ),
      HasSum (fun o : Option ι =>
        if (∀ v, o = some v → v ∈ P) then (if o = none then 1 else c) else 0)
        (1 + (P.card : ℝ) * c) := by
    intro P c
    have hnone : (none : Option ι) ∉ P.image some := by simp
    have hS : ∀ o : Option ι,
        o ∉ insert none (P.image some) →
        (if (∀ v, o = some v → v ∈ P) then (if o = none then (1 : ℝ) else c) else 0) = 0 := by
      intro o ho
      have hone : o ≠ none := fun h => ho (by rw [h]; simp)
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hone
      have hvp : v ∉ P := by
        intro hvp
        exact ho (by rw [hv]; exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hvp))
      have hpred : ¬ ∀ w, o = some w → w ∈ P := fun h => hvp (h v hv)
      rw [if_neg hpred]
    have hsum : (∑ o ∈ insert none (P.image some),
        (if (∀ v, o = some v → v ∈ P) then (if o = none then (1 : ℝ) else c) else 0))
        = 1 + (P.card : ℝ) * c := by
      rw [Finset.sum_insert hnone, Finset.sum_image]
      have hgn : (if (∀ v, (none : Option ι) = some v → v ∈ P) then
          (if (none : Option ι) = none then (1 : ℝ) else c) else 0) = 1 := by
        rw [if_pos (by intro v hv; simp at hv), if_pos rfl]
      rw [hgn]
      have hgs : ∀ v ∈ P,
          (if (∀ w, (some v : Option ι) = some w → w ∈ P) then
            (if (some v : Option ι) = none then (1 : ℝ) else c) else 0) = c := by
        intro v hv
        rw [if_pos (by
            intro w hw
            have hvw : v = w := Option.some.inj hw
            rw [← hvw]
            exact hv),
          if_neg (Option.some_ne_none v)]
      rw [Finset.sum_congr rfl hgs, Finset.sum_const, nsmul_eq_mul]
      norm_num
    have hsub : HasSum ((↑(insert none (P.image some)) : Set (Option ι)).indicator
        (fun o : Option ι =>
          if (∀ v, o = some v → v ∈ P) then (if o = none then (1 : ℝ) else c) else 0))
        (∑ o ∈ insert none (P.image some),
          (if (∀ v, o = some v → v ∈ P) then (if o = none then (1 : ℝ) else c) else 0)) :=
      hasSum_subtype_iff_indicator.mp (Finset.hasSum _ _)
    have hfin2 : HasSum (fun o : Option ι =>
        if (∀ v, o = some v → v ∈ P) then (if o = none then (1 : ℝ) else c) else 0)
        (1 + (P.card : ℝ) * c) := by
      rw [← hsum]
      refine HasSum.congr_fun hsub ?_
      intro o
      by_cases ho : o ∈ insert none (P.image some)
      · rw [Set.indicator_of_mem ho]
      · rw [hS o ho, Set.indicator_of_notMem ho]
    exact hfin2
  have POWPROD : ∀ (s : Finset ι) (F : ι → ℕ),
      x₀ ^ (∑ u ∈ s, F u) = ∏ u ∈ s, x₀ ^ (F u) := by
    intro s F
    exact (Finset.prod_pow_eq_pow_sum s F x₀).symm
  have MASTER_A : ∀ (Φ : Fin q → ι → Finset ι),
      (∀ j u, u ∉ U ∩ A j → Φ j u = ∅) →
      (∀ j u, x₀ * ((Φ j u).card : ℝ) < 1) →
      HasSum (fun W : Fin q → ι → List ι =>
        (if (∀ j u v, v ∈ W j u → v ∈ Φ j u) then
          x₀ ^ (∑ j, ∑ u ∈ U, (W j u).length) else 0))
        (∏ j, ∏ u ∈ U, (1 - ((Φ j u).card : ℝ) * x₀)⁻¹) := by
    intro Φ hΦ1 hΦ2
    obtain ⟨gA, hgA⟩ : ∃ f : Fin q → ι → (List ι → ℝ),
        f = fun j u w => if (∀ v ∈ w, v ∈ Φ j u) then x₀ ^ w.length else 0 := ⟨_, rfl⟩
    obtain ⟨Gj, hGj⟩ : ∃ f : Fin q → ((ι → List ι) → ℝ),
        f = fun j W => (if (∀ u v, v ∈ W u → v ∈ Φ j u) then
          x₀ ^ (∑ u ∈ U, (W u).length) else 0) := ⟨_, rfl⟩
    have hslot : ∀ (j : Fin q) (p : ↥U),
        HasSum (gA j (p : ι)) ((1 - ((Φ j (p : ι)).card : ℝ) * x₀)⁻¹) := by
      intro j p
      have h1 := hC1 (Φ j (p : ι)) x₀ hx₀ (hΦ2 j (p : ι))
      simpa only [hgA] using h1
    have hGjHas : ∀ j : Fin q, HasSum (Gj j)
        (∏ u ∈ U, (1 - ((Φ j u).card : ℝ) * x₀)⁻¹) := by
      intro j
      rw [← Finset.prod_coe_sort U
        (fun u => (1 - ((Φ j u).card : ℝ) * x₀)⁻¹)]
      have hvan : ∀ W : ι → List ι, (∃ u : ι, u ∉ U ∧ W u ≠ []) → Gj j W = 0 := by
        intro W hW
        obtain ⟨u, huU, hne⟩ := hW
        have hbad : ¬ ∀ v v' : ι, v' ∈ W v → v' ∈ Φ j v := by
          intro hall
          obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil (W u) hne
          have hmem : v ∈ Φ j u := hall u v hv
          rw [hΦ1 j u (fun hc => huU (Finset.mem_inter.1 hc).1)] at hmem
          exact Finset.notMem_empty v hmem
        simp only [hGj]
        rw [if_neg hbad]
      refine RESTR (List ι) (fun _ => []) (Gj j) _ hvan ?_
      have hext : ∀ (F₀ : ↥U → List ι) (p : ↥U),
          (fun u => if h : u ∈ U then F₀ ⟨u, h⟩ else []) (p : ι) = F₀ p := by
        intro F₀ p
        show (if h : (p : ι) ∈ U then F₀ ⟨(p : ι), h⟩ else []) = F₀ p
        rw [dif_pos p.2]
      have hpw : ∀ F₀ : ↥U → List ι,
          Gj j (fun u => if h : u ∈ U then F₀ ⟨u, h⟩ else [])
            = ∏ p : ↥U, gA j (p : ι) (F₀ p) := by
        intro F₀
        simp only [hGj]
        by_cases hall : ∀ u v : ι,
            v ∈ (fun u => if h : u ∈ U then F₀ ⟨u, h⟩ else []) u → v ∈ Φ j u
        · rw [if_pos hall]
          have hall' : ∀ p : ↥U, ∀ v ∈ F₀ p, v ∈ Φ j (p : ι) := by
            intro p v hv
            refine hall (p : ι) v ?_
            rw [hext F₀ p]
            exact hv
          have hsum : (∑ u ∈ U,
              ((fun u => if h : u ∈ U then F₀ ⟨u, h⟩ else []) u).length)
              = ∑ p : ↥U, (F₀ p).length := by
            rw [← Finset.sum_coe_sort U
              (fun u => ((fun u => if h : u ∈ U then F₀ ⟨u, h⟩ else []) u).length)]
            refine Finset.sum_congr rfl fun p _ => ?_
            show ((fun u => if h : u ∈ U then F₀ ⟨u, h⟩ else []) (p : ι)).length
              = (F₀ p).length
            rw [hext F₀ p]
          rw [hsum, ← Finset.prod_pow_eq_pow_sum
            (Finset.univ : Finset ↥U) (fun p => (F₀ p).length) x₀]
          exact Finset.prod_congr rfl fun p _ => by
            simp only [hgA, if_pos (hall' p)]
        · rw [if_neg hall]
          rw [not_forall] at hall
          obtain ⟨u, hu⟩ := hall
          rw [not_forall] at hu
          obtain ⟨v, hv⟩ := hu
          push Not at hv
          obtain ⟨hvmem, hnv⟩ := hv
          have huU : u ∈ U := by
            by_contra hcon
            rw [dif_neg hcon] at hvmem
            exact absurd hvmem (by simp)
          rw [dif_pos huU] at hvmem
          rw [Finset.prod_eq_zero (Finset.mem_univ (⟨u, huU⟩ : ↥U))]
          simp only [hgA]
          rw [if_neg (fun h => hnv (h v hvmem))]
      exact (COREFT ↥U (List ι)
        (fun p => (1 - ((Φ j (p : ι)).card : ℝ) * x₀)⁻¹)
        (fun p => gA j (p : ι)) (hslot j)).congr_fun hpw
    refine (CORE q (ι → List ι)
      (fun j => ∏ u ∈ U, (1 - ((Φ j u).card : ℝ) * x₀)⁻¹) (fun j => Gj j)
      hGjHas).congr_fun ?_
    intro W
    by_cases hW : ∀ (j : Fin q) (u v : ι), v ∈ W j u → v ∈ Φ j u
    · rw [if_pos hW, ← Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin q))
        (fun j => ∑ u ∈ U, (W j u).length)]
      exact Finset.prod_congr rfl fun j _ => by
        simp only [hGj, if_pos (fun u v hv => hW j u v hv)]
    · rw [if_neg hW]
      push Not at hW
      obtain ⟨j, u, v, hvmem, hnv⟩ := hW
      rw [Finset.prod_eq_zero (Finset.mem_univ j)]
      simp only [hGj]
      rw [if_neg (fun h => hnv (h u v hvmem))]
  have MASTER_B : ∀ (c : ℝ) (Ψ : Fin r → ι → Finset ι),
      (∀ i u, u ∉ U ∩ B i → Ψ i u = ∅) →
      HasSum (fun b : Fin r → ι → Option ι =>
        (if (∀ i u v, b i u = some v → v ∈ Ψ i u) then
          c ^ (∑ i, ((U.filter fun u => b i u ≠ none).card)) else 0))
        (∏ i, ∏ u ∈ U, (1 + ((Ψ i u).card : ℝ) * c)) := by
    intro c Ψ hΨ1
    obtain ⟨gB, hgB⟩ : ∃ f : Fin r → ι → (Option ι → ℝ),
        f = fun i u o => if (∀ v, o = some v → v ∈ Ψ i u) then
          (if o = none then 1 else c) else 0 := ⟨_, rfl⟩
    obtain ⟨GBi, hGBi⟩ : ∃ f : Fin r → ((ι → Option ι) → ℝ),
        f = fun i b => (if (∀ u v, b u = some v → v ∈ Ψ i u) then
          c ^ ((U.filter fun u => b u ≠ none).card) else 0) := ⟨_, rfl⟩
    have hslot : ∀ (i : Fin r) (p : ↥U),
        HasSum (gB i (p : ι)) (1 + ((Ψ i (p : ι)).card : ℝ) * c) := by
      intro i p
      have h1 := OPT (Ψ i (p : ι)) c
      simpa only [hgB] using h1
    have hGBiHas : ∀ i : Fin r, HasSum (GBi i)
        (∏ u ∈ U, (1 + ((Ψ i u).card : ℝ) * c)) := by
      intro i
      rw [← Finset.prod_coe_sort U (fun u => (1 + ((Ψ i u).card : ℝ) * c))]
      have hvan : ∀ b : ι → Option ι, (∃ u : ι, u ∉ U ∧ b u ≠ none) → GBi i b = 0 := by
        intro b hb
        obtain ⟨u, huU, hne⟩ := hb
        have hbad : ¬ ∀ v w : ι, b v = some w → w ∈ Ψ i v := by
          intro hall
          obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hne
          have hmem : w ∈ Ψ i u := hall u w hw
          rw [hΨ1 i u (fun hc => huU (Finset.mem_inter.1 hc).1)] at hmem
          exact Finset.notMem_empty w hmem
        simp only [hGBi]
        rw [if_neg hbad]
      refine RESTR (Option ι) (fun _ => none) (GBi i) _ hvan ?_
      have hext : ∀ (F₀ : ↥U → Option ι) (p : ↥U),
          (fun u => if h : u ∈ U then F₀ ⟨u, h⟩ else none) (p : ι) = F₀ p := by
        intro F₀ p
        show (if h : (p : ι) ∈ U then F₀ ⟨(p : ι), h⟩ else none) = F₀ p
        rw [dif_pos p.2]
      have hpw : ∀ F₀ : ↥U → Option ι,
          GBi i (fun u => if h : u ∈ U then F₀ ⟨u, h⟩ else none)
            = ∏ p : ↥U, gB i (p : ι) (F₀ p) := by
        intro F₀
        simp only [hGBi]
        by_cases hall : ∀ u v : ι,
            (fun u => if h : u ∈ U then F₀ ⟨u, h⟩ else none) u = some v → v ∈ Ψ i u
        · rw [if_pos hall]
          have hall' : ∀ p : ↥U, ∀ v, F₀ p = some v → v ∈ Ψ i (p : ι) := by
            intro p v hv
            refine hall (p : ι) v ?_
            rw [hext F₀ p]
            exact hv
          have hcard : (U.filter
              (fun u => (fun u => if h : u ∈ U then F₀ ⟨u, h⟩ else none) u ≠ none)).card
              = (Finset.univ.filter (fun p : ↥U => F₀ p ≠ none)).card := by
            rw [Finset.card_filter, Finset.card_filter]
            rw [← Finset.sum_coe_sort U
              (fun u => if (fun u => if h : u ∈ U then F₀ ⟨u, h⟩ else none) u ≠ none
                then 1 else 0)]
            refine Finset.sum_congr rfl fun p _ => ?_
            show (if (fun u => if h : u ∈ U then F₀ ⟨u, h⟩ else none) (p : ι) ≠ none
                then 1 else 0) = (if F₀ p ≠ none then 1 else 0)
            rw [hext F₀ p]
          have hRHS : (∏ p : ↥U, gB i (p : ι) (F₀ p))
              = ∏ p ∈ (Finset.univ : Finset ↥U), (if F₀ p ≠ none then c else 1) := by
            refine Finset.prod_congr rfl fun p _ => ?_
            simp only [hgB, if_pos (hall' p)]
            by_cases h : F₀ p = none <;> simp [h]
          rw [hRHS, hcard, Finset.card_filter, ← Finset.prod_pow_eq_pow_sum
            (Finset.univ : Finset ↥U) (fun p => (if F₀ p ≠ none then 1 else 0)) c]
          exact Finset.prod_congr rfl fun p _ => by
            by_cases h : F₀ p ≠ none <;> simp [h]
        · rw [if_neg hall]
          rw [not_forall] at hall
          obtain ⟨u, hu⟩ := hall
          rw [not_forall] at hu
          obtain ⟨v, hv⟩ := hu
          push Not at hv
          obtain ⟨hvmem, hnv⟩ := hv
          have huU : u ∈ U := by
            by_contra hcon
            rw [dif_neg hcon] at hvmem
            simp at hvmem
          rw [dif_pos huU] at hvmem
          rw [Finset.prod_eq_zero (Finset.mem_univ (⟨u, huU⟩ : ↥U))]
          simp only [hgB]
          rw [if_neg (fun h => hnv (h v hvmem))]
      exact (COREFT ↥U (Option ι)
        (fun p => (1 + ((Ψ i (p : ι)).card : ℝ) * c))
        (fun p => gB i (p : ι)) (hslot i)).congr_fun hpw
    refine (CORE r (ι → Option ι)
      (fun i => ∏ u ∈ U, (1 + ((Ψ i u).card : ℝ) * c)) (fun i => GBi i)
      hGBiHas).congr_fun ?_
    intro b
    by_cases hb : ∀ (i : Fin r) (u v : ι), b i u = some v → v ∈ Ψ i u
    · rw [if_pos hb, ← Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin r))
        (fun i => ((U.filter fun u => b i u ≠ none).card)) c]
      exact Finset.prod_congr rfl fun i _ => by
        simp only [hGBi, if_pos (fun u v hv => hb i u v hv)]
    · rw [if_neg hb]
      push Not at hb
      obtain ⟨i, u, v, hvmem, hnv⟩ := hb
      rw [Finset.prod_eq_zero (Finset.mem_univ i)]
      simp only [hGBi]
      rw [if_neg (fun h => hnv (h u v hvmem))]
  obtain ⟨CE, hCE⟩ : ∃ e : mixed_moment_occurrence_configuration ι q r ≃
      ((Fin q → ι → List ι) × (Fin r → ι → Option ι)),
      ∀ Γ, e Γ = (Γ.aWords, Γ.bChoice) :=
    ⟨{ toFun := fun Γ => (Γ.aWords, Γ.bChoice)
       invFun := fun p => ⟨p.1, p.2⟩
       left_inv := fun Γ => rfl
       right_inv := fun p => rfl }, fun Γ => rfl⟩
  have COMBINE : ∀ (c : ℝ) (Φ : Fin q → ι → Finset ι) (Ψ : Fin r → ι → Finset ι),
      (∀ j u, u ∉ U ∩ A j → Φ j u = ∅) → (∀ j u, x₀ * ((Φ j u).card : ℝ) < 1) →
      (∀ i u, u ∉ U ∩ B i → Ψ i u = ∅) →
      HasSum (fun Γ : mixed_moment_occurrence_configuration ι q r =>
        (if (∀ j u v, v ∈ Γ.aWords j u → v ∈ Φ j u) ∧
            (∀ i u v, Γ.bChoice i u = some v → v ∈ Ψ i u) then
          η ^ U.card * (x₀ ^ (NA Finset.univ Γ) * c ^ (NB Finset.univ Γ)) else 0))
        (η ^ U.card *
          ((∏ j, ∏ u ∈ U, (1 - ((Φ j u).card : ℝ) * x₀)⁻¹) *
          ∏ i, ∏ u ∈ U, (1 + ((Ψ i u).card : ℝ) * c))) := by
    intro c Φ Ψ hΦ1 hΦ2 hΨ1
    obtain ⟨WA, hWAdef⟩ : ∃ f : (Fin q → ι → List ι) → ℝ,
        f = fun W => (if (∀ j u v, v ∈ W j u → v ∈ Φ j u) then
          x₀ ^ (∑ j, ∑ u ∈ U, (W j u).length) else 0) := ⟨_, rfl⟩
    obtain ⟨BB, hBBdef⟩ : ∃ f : (Fin r → ι → Option ι) → ℝ,
        f = fun b => (if (∀ i u v, b i u = some v → v ∈ Ψ i u) then
          c ^ (∑ i, ((U.filter fun u => b i u ≠ none).card)) else 0) := ⟨_, rfl⟩
    have hW : HasSum WA (∏ j, ∏ u ∈ U, (1 - ((Φ j u).card : ℝ) * x₀)⁻¹) := by
      rw [hWAdef]
      exact MASTER_A Φ hΦ1 hΦ2
    have hb : HasSum BB (∏ i, ∏ u ∈ U, (1 + ((Ψ i u).card : ℝ) * c)) := by
      rw [hBBdef]
      exact MASTER_B c Ψ hΨ1
    have hWAabs : ∀ W : Fin q → ι → List ι, ‖WA W‖ = WA W := by
      intro W
      simp only [hWAdef]
      by_cases h : ∀ (j : Fin q) (u v : ι), v ∈ W j u → v ∈ Φ j u
      · rw [if_pos h, Real.norm_eq_abs, _root_.abs_of_nonneg (pow_nonneg hx₀ _)]
      · rw [if_neg h, Real.norm_eq_abs, _root_.abs_zero]
    have hBBabs : ∀ b : Fin r → ι → Option ι,
        ‖BB b‖ = (if (∀ i u v, b i u = some v → v ∈ Ψ i u) then
          |c| ^ (∑ i, ((U.filter fun u => b i u ≠ none).card)) else 0) := by
      intro b
      simp only [hBBdef]
      by_cases h : ∀ (i : Fin r) (u v : ι), b i u = some v → v ∈ Ψ i u
      · rw [if_pos h, if_pos h, Real.norm_eq_abs, _root_.abs_pow]
      · rw [if_neg h, if_neg h, Real.norm_eq_abs, _root_.abs_zero]
    have hsA : Summable (fun W : Fin q → ι → List ι => ‖WA W‖) :=
      hW.summable.congr fun W => (hWAabs W).symm
    have hsB : Summable (fun b : Fin r → ι → Option ι => ‖BB b‖) := by
      refine (MASTER_B |c| Ψ hΨ1).summable.congr fun b => (hBBabs b).symm
    have hsAB : Summable (fun p : (Fin q → ι → List ι) × (Fin r → ι → Option ι) =>
        WA p.1 * BB p.2) := summable_mul_of_summable_norm hsA hsB
    have hpair : HasSum (fun p : (Fin q → ι → List ι) × (Fin r → ι → Option ι) =>
        WA p.1 * BB p.2)
        ((∏ j, ∏ u ∈ U, (1 - ((Φ j u).card : ℝ) * x₀)⁻¹) *
          ∏ i, ∏ u ∈ U, (1 + ((Ψ i u).card : ℝ) * c)) := HasSum.mul hW hb hsAB
    have hcfg : HasSum (fun Γ : mixed_moment_occurrence_configuration ι q r =>
        WA Γ.aWords * BB Γ.bChoice)
        ((∏ j, ∏ u ∈ U, (1 - ((Φ j u).card : ℝ) * x₀)⁻¹) *
          ∏ i, ∏ u ∈ U, (1 + ((Ψ i u).card : ℝ) * c)) := by
      refine HasSum.congr_fun ((Equiv.hasSum_iff
        (f := fun p : (Fin q → ι → List ι) × (Fin r → ι → Option ι) => WA p.1 * BB p.2)
        CE).mpr hpair) ?_
      intro Γ
      show WA Γ.aWords * BB Γ.bChoice = (fun p => WA p.1 * BB p.2) (CE Γ)
      rw [hCE Γ]
    refine HasSum.congr_fun (HasSum.mul_left (η ^ U.card) hcfg) ?_
    intro Γ
    simp only [hWAdef, hBBdef, hNA, hNB, ← hU]
    by_cases hA : ∀ (j : Fin q) (u v : ι), v ∈ Γ.aWords j u → v ∈ Φ j u
    · by_cases hB : ∀ (i : Fin r) (u v : ι), Γ.bChoice i u = some v → v ∈ Ψ i u
      · rw [if_pos ⟨hA, hB⟩, if_pos hA, if_pos hB]
      · rw [if_neg (fun h => hB h.2), if_pos hA, if_neg hB]
        ring
    · rw [if_neg (fun h => hA h.1), if_neg hA]
      ring
  obtain ⟨Φf, hΦf⟩ : ∃ f : Fin q → ι → Finset ι,
      ∀ j u, f j u = (U ∩ A j).filter
        (fun v => rank v < rank u ∧ u ∈ U ∩ A j) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Ψf, hΨf⟩ : ∃ f : Fin r → ι → Finset ι,
      ∀ i u, f i u = (U ∩ B i).filter
        (fun v => rank v < rank u ∧ u ∈ U ∩ B i) := ⟨_, fun _ _ => rfl⟩
  have hmemΦ : ∀ (j : Fin q) (u v : ι), v ∈ Φf j u ↔
      (v ∈ U ∩ A j ∧ rank v < rank u ∧ u ∈ U ∩ A j) := by
    intro j u v
    rw [hΦf j u, Finset.mem_filter]
  have hmemΨ : ∀ (i : Fin r) (u v : ι), v ∈ Ψf i u ↔
      (v ∈ U ∩ B i ∧ rank v < rank u ∧ u ∈ U ∩ B i) := by
    intro i u v
    rw [hΨf i u, Finset.mem_filter]
  have hΦf1 : ∀ j u, u ∉ U ∩ A j → Φf j u = ∅ := by
    intro j u hu
    rw [hΦf j u, Finset.filter_eq_empty_iff]
    intro v hv hconj
    exact hu hconj.2
  have hΨf1 : ∀ i u, u ∉ U ∩ B i → Ψf i u = ∅ := by
    intro i u hu
    rw [hΨf i u, Finset.filter_eq_empty_iff]
    intro v hv hconj
    exact hu hconj.2
  have hΦf2 : ∀ j u, x₀ * ((Φf j u).card : ℝ) < 1 := by
    intro j u
    have h1 : (Φf j u).card ≤ U.card := by
      rw [hΦf j u]
      refine Nat.le_trans (Finset.card_filter_le _ _) ?_
      exact Finset.card_le_card (Finset.filter_subset _ _)
    have h2 : ((Φf j u).card : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast h1
    have h3 : x₀ * ((Φf j u).card : ℝ) ≤ x₀ * (U.card : ℝ) :=
      mul_le_mul_of_nonneg_left h2 hx₀
    rw [hLcard] at h3
    have hcomm : x₀ * ((total_index_count I : ℕ) : ℝ)
        = ((total_index_count I : ℕ) : ℝ) * x₀ := mul_comm _ _
    linarith
  have hadmiff : ∀ Γ : mixed_moment_occurrence_configuration ι q r,
      mixed_moment_configuration_admissible I A B rank Γ ↔
      (∀ j u v, v ∈ Γ.aWords j u → v ∈ Φf j u) ∧
      (∀ i u v, Γ.bChoice i u = some v → v ∈ Ψf i u) := by
    intro Γ
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro j u v hv
        obtain ⟨hu, hv2, hr⟩ := h.2.2.1 j u v hv
        rw [hmemΦ j u v]
        rw [← hU] at hu hv2
        exact ⟨hv2, hr, hu⟩
      · intro i u v hv
        obtain ⟨hu, hv2, hr⟩ := h.2.2.2 i u v hv
        rw [hmemΨ i u v]
        rw [← hU] at hu hv2
        exact ⟨hv2, hr, hu⟩
    · rintro ⟨hw, hb⟩
      refine ⟨hrankU, ?_, ?_, ?_⟩
      · intro j u hu
        by_contra hne
        obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil (Γ.aWords j u) hne
        have h1 := hw j u v hv
        rw [hmemΦ j u v] at h1
        rw [← hU] at hu
        exact hu h1.2.2
      · intro j u v hv
        have h1 := hw j u v hv
        rw [hmemΦ j u v] at h1
        rw [← hU]
        exact ⟨h1.2.2, h1.1, h1.2.1⟩
      · intro i u v hv
        have h1 := hb i u v hv
        rw [hmemΨ i u v] at h1
        rw [← hU]
        exact ⟨h1.2.2, h1.1, h1.2.1⟩
  have hwabs : ∀ Γ : mixed_moment_occurrence_configuration ι q r,
      |mixed_moment_configuration_weight I η x₀ y₀ Γ| =
        η ^ U.card * (x₀ ^ (NA Finset.univ Γ) * y₀ ^ (NB Finset.univ Γ)) := by
    intro Γ
    rw [hweight Γ, _root_.abs_mul, _root_.abs_mul, _root_.abs_pow, _root_.abs_pow,
      _root_.abs_pow, _root_.abs_of_nonneg hη, _root_.abs_of_nonneg hx₀,
      _root_.abs_neg, _root_.abs_of_nonneg hy₀]
    ring
  have hsumabs : HasSum (fun Γ : mixed_moment_occurrence_configuration ι q r =>
      if mixed_moment_configuration_admissible I A B rank Γ then
        |mixed_moment_configuration_weight I η x₀ y₀ Γ| else 0)
      (η ^ U.card *
        ((∏ j, ∏ u ∈ U, (1 - ((Φf j u).card : ℝ) * x₀)⁻¹) *
        ∏ i, ∏ u ∈ U, (1 + ((Ψf i u).card : ℝ) * y₀))) := by
    refine HasSum.congr_fun (COMBINE y₀ Φf Ψf hΦf1 hΦf2 hΨf1) ?_
    intro Γ
    by_cases hadm : mixed_moment_configuration_admissible I A B rank Γ
    · rw [if_pos hadm, if_pos ((hadmiff Γ).mp hadm), hwabs Γ]
    · rw [if_neg hadm, if_neg (fun h => hadm ((hadmiff Γ).mpr h))]
  have hsumm : Summable (fun Γ :
      {Γ : mixed_moment_occurrence_configuration ι q r //
        mixed_moment_configuration_admissible I A B rank Γ} ↦
      |mixed_moment_configuration_weight I η x₀ y₀ Γ.1|) := by
    have hsub : HasSum (fun Γ :
        {Γ : mixed_moment_occurrence_configuration ι q r //
          mixed_moment_configuration_admissible I A B rank Γ} =>
        |mixed_moment_configuration_weight I η x₀ y₀ Γ.1|)
        (η ^ U.card *
          ((∏ j, ∏ u ∈ U, (1 - ((Φf j u).card : ℝ) * x₀)⁻¹) *
          ∏ i, ∏ u ∈ U, (1 + ((Ψf i u).card : ℝ) * y₀))) := by
      refine (hasSum_subtype_iff_indicator
        (f := fun Γ : mixed_moment_occurrence_configuration ι q r =>
          |mixed_moment_configuration_weight I η x₀ y₀ Γ|)
        (s := {Γ : mixed_moment_occurrence_configuration ι q r |
          mixed_moment_configuration_admissible I A B rank Γ})).mpr ?_
      refine HasSum.congr_fun hsumabs ?_
      intro Γ
      by_cases hadm : mixed_moment_configuration_admissible I A B rank Γ
      · rw [if_pos hadm]
        exact Set.indicator_of_mem
          (f := fun Γ : mixed_moment_occurrence_configuration ι q r =>
            |mixed_moment_configuration_weight I η x₀ y₀ Γ|)
          (s := {Γ : mixed_moment_occurrence_configuration ι q r |
            mixed_moment_configuration_admissible I A B rank Γ}) hadm
      · rw [if_neg hadm]
        exact Set.indicator_of_notMem
          (f := fun Γ : mixed_moment_occurrence_configuration ι q r =>
            |mixed_moment_configuration_weight I η x₀ y₀ Γ|)
          (s := {Γ : mixed_moment_occurrence_configuration ι q r |
            mixed_moment_configuration_admissible I A B rank Γ}) hadm
    exact hsub.summable
  have hcardlt : ∀ S : Finset ι, S ⊆ U → x₀ * ((S.card : ℝ)) < 1 := by
    intro S hS
    have h1 : S.card ≤ U.card := Finset.card_le_card hS
    have h2 : (S.card : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast h1
    have h3 : x₀ * (S.card : ℝ) ≤ x₀ * (U.card : ℝ) := mul_le_mul_of_nonneg_left h2 hx₀
    rw [hLcard] at h3
    have hcomm : x₀ * ((total_index_count I : ℕ) : ℝ)
        = ((total_index_count I : ℕ) : ℝ) * x₀ := mul_comm _ _
    linarith
  obtain ⟨Φp, hΦp⟩ : ∃ f : Finpartition (Finset.univ : Finset (Fin ℓ)) → Fin q → ι → Finset ι,
      ∀ π j u, f π j u = (U ∩ A j).filter
        (fun v => rank v < rank u ∧ u ∈ U ∩ A j ∧ π.part (tt u) = π.part (tt v)) :=
    ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨Ψp, hΨp⟩ : ∃ f : Finpartition (Finset.univ : Finset (Fin ℓ)) → Fin r → ι → Finset ι,
      ∀ π i u, f π i u = (U ∩ B i).filter
        (fun v => rank v < rank u ∧ u ∈ U ∩ B i ∧ π.part (tt u) = π.part (tt v)) :=
    ⟨_, fun _ _ _ => rfl⟩
  have hΦp1 : ∀ π j u, u ∉ U ∩ A j → Φp π j u = ∅ := by
    intro π j u hu
    rw [hΦp π j u, Finset.filter_eq_empty_iff]
    intro v hv hconj
    exact hu hconj.2.1
  have hΨp1 : ∀ π i u, u ∉ U ∩ B i → Ψp π i u = ∅ := by
    intro π i u hu
    rw [hΨp π i u, Finset.filter_eq_empty_iff]
    intro v hv hconj
    exact hu hconj.2.1
  have hΦp2 : ∀ π j u, x₀ * ((Φp π j u).card : ℝ) < 1 := by
    intro π j u
    refine hcardlt (Φp π j u) ?_
    rw [hΦp π j u]
    exact (Finset.filter_subset _ _).trans Finset.inter_subset_left
  have hICsubU : ∀ C : Finset (Fin ℓ), indexed_union I C ⊆ U := by
    intro C
    rw [hU]
    exact hUDmono C Finset.univ (Finset.subset_univ C)
  have httC : ∀ (C : Finset (Fin ℓ)) (u : ι), u ∈ indexed_union I C → tt u ∈ C := by
    intro C u hu
    obtain ⟨t, htC, hut⟩ := Finset.mem_biUnion.1 hu
    rw [htuniq u t hut]
    exact htC
  have hUIC : ∀ (C : Finset (Fin ℓ)) (u : ι), u ∈ U → tt u ∈ C → u ∈ indexed_union I C := by
    intro C u hu htC
    exact Finset.mem_biUnion.2 ⟨tt u, htC, htt u hu⟩
  have hkSeq : ∀ (S : Finset ι) (u : ι),
      kS S u = (S.filter (fun v => rank v < rank u)).card := fun S u => by rw [hkS]
  have hΦeq : ∀ (π : Finpartition (Finset.univ : Finset (Fin ℓ))) {C : Finset (Fin ℓ)}
      (hC : C ∈ π.parts) (j : Fin q) {u : ι} (hu : u ∈ indexed_union I C ∩ A j),
      Φp π j u = (indexed_union I C ∩ A j).filter (fun v => rank v < rank u) := by
    intro π C hC j u hu
    rw [hΦp π j u]
    apply Finset.ext
    intro v
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hvUA, hr, -, hparts⟩
      refine ⟨?_, hr⟩
      have httu : tt u ∈ C := httC C u (Finset.mem_inter.1 hu).1
      have hpu : π.part (tt u) = C := π.part_eq_of_mem hC httu
      have httv : tt v ∈ C := by
        have h1 : tt v ∈ π.part (tt v) := π.mem_part (Finset.mem_univ _)
        rw [← hparts] at h1
        rw [hpu] at h1
        exact h1
      exact Finset.mem_inter.2 ⟨hUIC C v (Finset.mem_inter.1 hvUA).1 httv,
        (Finset.mem_inter.1 hvUA).2⟩
    · rintro ⟨hv, hr⟩
      have httu : tt u ∈ C := httC C u (Finset.mem_inter.1 hu).1
      have httv : tt v ∈ C := httC C v (Finset.mem_inter.1 hv).1
      exact ⟨Finset.mem_inter.2 ⟨hICsubU C (Finset.mem_inter.1 hv).1,
        (Finset.mem_inter.1 hv).2⟩, hr,
        Finset.mem_inter.2 ⟨hICsubU C (Finset.mem_inter.1 hu).1,
          (Finset.mem_inter.1 hu).2⟩,
        by rw [π.part_eq_of_mem hC httu, π.part_eq_of_mem hC httv]⟩
  have hΨeq : ∀ (π : Finpartition (Finset.univ : Finset (Fin ℓ))) {C : Finset (Fin ℓ)}
      (hC : C ∈ π.parts) (i : Fin r) {u : ι} (hu : u ∈ indexed_union I C ∩ B i),
      Ψp π i u = (indexed_union I C ∩ B i).filter (fun v => rank v < rank u) := by
    intro π C hC i u hu
    rw [hΨp π i u]
    apply Finset.ext
    intro v
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hvUB, hr, -, hparts⟩
      refine ⟨?_, hr⟩
      have httu : tt u ∈ C := httC C u (Finset.mem_inter.1 hu).1
      have hpu : π.part (tt u) = C := π.part_eq_of_mem hC httu
      have httv : tt v ∈ C := by
        have h1 : tt v ∈ π.part (tt v) := π.mem_part (Finset.mem_univ _)
        rw [← hparts] at h1
        rw [hpu] at h1
        exact h1
      exact Finset.mem_inter.2 ⟨hUIC C v (Finset.mem_inter.1 hvUB).1 httv,
        (Finset.mem_inter.1 hvUB).2⟩
    · rintro ⟨hv, hr⟩
      have httu : tt u ∈ C := httC C u (Finset.mem_inter.1 hu).1
      have httv : tt v ∈ C := httC C v (Finset.mem_inter.1 hv).1
      exact ⟨Finset.mem_inter.2 ⟨hICsubU C (Finset.mem_inter.1 hv).1,
        (Finset.mem_inter.1 hv).2⟩, hr,
        Finset.mem_inter.2 ⟨hICsubU C (Finset.mem_inter.1 hu).1,
          (Finset.mem_inter.1 hu).2⟩,
        by rw [π.part_eq_of_mem hC httu, π.part_eq_of_mem hC httv]⟩
  have hICj : ∀ (π : Finpartition (Finset.univ : Finset (Fin ℓ))) {C : Finset (Fin ℓ)}
      (hC : C ∈ π.parts) (j : Fin q),
      (∏ u ∈ indexed_union I C ∩ A j, (1 - ((Φp π j u).card : ℝ) * x₀)⁻¹)
      = mixed_moment_x_factor x₀ (indexed_union I C ∩ A j) := by
    intro π C hC j
    rw [hXeq _ x₀ (fun u hu => hICsubU C (Finset.mem_inter.1 hu).1)]
    refine Finset.prod_congr rfl fun u hu => ?_
    rw [hΦeq π hC j hu, hkSeq]
  have hICi : ∀ (π : Finpartition (Finset.univ : Finset (Fin ℓ))) {C : Finset (Fin ℓ)}
      (hC : C ∈ π.parts) (i : Fin r),
      (∏ u ∈ indexed_union I C ∩ B i, (1 + ((Ψp π i u).card : ℝ) * (-y₀)))
      = mixed_moment_y_factor y₀ (indexed_union I C ∩ B i) := by
    intro π C hC i
    rw [hYeq _ y₀ (fun u hu => hICsubU C (Finset.mem_inter.1 hu).1)]
    refine Finset.prod_congr rfl fun u hu => ?_
    rw [hΨeq π hC i hu, hkSeq]
    ring
  have hICprod : ∀ (π : Finpartition (Finset.univ : Finset (Fin ℓ))) {C : Finset (Fin ℓ)}
      (hC : C ∈ π.parts) (j : Fin q),
      (∏ u ∈ indexed_union I C, (1 - ((Φp π j u).card : ℝ) * x₀)⁻¹)
      = mixed_moment_x_factor x₀ (indexed_union I C ∩ A j) := by
    intro π C hC j
    rw [← Finset.prod_subset
      (Finset.inter_subset_left : indexed_union I C ∩ A j ⊆ indexed_union I C)]
    · exact hICj π hC j
    · intro u hu hu'
      rw [hΦp1 π j u (fun hc => hu' (Finset.mem_inter.2 ⟨hu, (Finset.mem_inter.1 hc).2⟩))]
      simp
  have hICprodbi : ∀ (π : Finpartition (Finset.univ : Finset (Fin ℓ))) {C : Finset (Fin ℓ)}
      (hC : C ∈ π.parts) (i : Fin r),
      (∏ u ∈ indexed_union I C, (1 + ((Ψp π i u).card : ℝ) * (-y₀)))
      = mixed_moment_y_factor y₀ (indexed_union I C ∩ B i) := by
    intro π C hC i
    rw [← Finset.prod_subset
      (Finset.inter_subset_left : indexed_union I C ∩ B i ⊆ indexed_union I C)]
    · exact hICi π hC i
    · intro u hu hu'
      rw [hΨp1 π i u (fun hc => hu' (Finset.mem_inter.2 ⟨hu, (Finset.mem_inter.1 hc).2⟩))]
      simp
  have hAj : ∀ (π : Finpartition (Finset.univ : Finset (Fin ℓ))) (j : Fin q),
      (∏ u ∈ U, (1 - ((Φp π j u).card : ℝ) * x₀)⁻¹)
      = ∏ C ∈ π.parts, mixed_moment_x_factor x₀ (indexed_union I C ∩ A j) := by
    intro π j
    rw [← hUDcover π, Finset.prod_biUnion (hpartsdisj π)]
    exact Finset.prod_congr rfl fun C hC => hICprod π hC j
  have hBi : ∀ (π : Finpartition (Finset.univ : Finset (Fin ℓ))) (i : Fin r),
      (∏ u ∈ U, (1 + ((Ψp π i u).card : ℝ) * (-y₀)))
      = ∏ C ∈ π.parts, mixed_moment_y_factor y₀ (indexed_union I C ∩ B i) := by
    intro π i
    rw [← hUDcover π, Finset.prod_biUnion (hpartsdisj π)]
    exact Finset.prod_congr rfl fun C hC => hICprodbi π hC i
  have hval : ∀ π : Finpartition (Finset.univ : Finset (Fin ℓ)),
      (η ^ U.card *
        ((∏ j, ∏ u ∈ U, (1 - ((Φp π j u).card : ℝ) * x₀)⁻¹) *
        ∏ i, ∏ u ∈ U, (1 + ((Ψp π i u).card : ℝ) * (-y₀))))
      = ∏ C ∈ π.parts, mixed_moment_right_hand_side I A B η x₀ y₀ C := by
    intro π
    have hSA : (∏ j, ∏ u ∈ U, (1 - ((Φp π j u).card : ℝ) * x₀)⁻¹)
        = ∏ j, ∏ C ∈ π.parts, mixed_moment_x_factor x₀ (indexed_union I C ∩ A j) :=
      Finset.prod_congr rfl fun j _ => hAj π j
    have hSB : (∏ i, ∏ u ∈ U, (1 + ((Ψp π i u).card : ℝ) * (-y₀)))
        = ∏ i, ∏ C ∈ π.parts, mixed_moment_y_factor y₀ (indexed_union I C ∩ B i) :=
      Finset.prod_congr rfl fun i _ => hBi π i
    have hswapA : (∏ j, ∏ C ∈ π.parts, mixed_moment_x_factor x₀ (indexed_union I C ∩ A j))
        = ∏ C ∈ π.parts, ∏ j, mixed_moment_x_factor x₀ (indexed_union I C ∩ A j) :=
      Finset.prod_comm
    have hswapB : (∏ i, ∏ C ∈ π.parts, mixed_moment_y_factor y₀ (indexed_union I C ∩ B i))
        = ∏ C ∈ π.parts, ∏ i, mixed_moment_y_factor y₀ (indexed_union I C ∩ B i) :=
      Finset.prod_comm
    have hpowU : (∏ C ∈ π.parts, η ^ (indexed_union I C).card) = η ^ U.card := by
      rw [Finset.prod_pow_eq_pow_sum π.parts (fun C => (indexed_union I C).card) η,
        ← hUDcard π]
    rw [hSA, hSB, hswapA, hswapB, ← hpowU, ← mul_assoc, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun C _ => rfl
  have hcombπ : ∀ π : Finpartition (Finset.univ : Finset (Fin ℓ)),
      HasSum (fun Γ : mixed_moment_occurrence_configuration ι q r =>
        (if (∀ j u v, v ∈ Γ.aWords j u → v ∈ Φp π j u) ∧
            (∀ i u v, Γ.bChoice i u = some v → v ∈ Ψp π i u) then
          mixed_moment_configuration_weight I η x₀ y₀ Γ else 0))
        (∏ C ∈ π.parts, mixed_moment_right_hand_side I A B η x₀ y₀ C) := by
    intro π
    rw [← hval π]
    refine HasSum.congr_fun (COMBINE (-y₀) (Φp π) (Ψp π) (hΦp1 π) (hΦp2 π) (hΨp1 π)) ?_
    intro Γ
    by_cases hp : (∀ (j : Fin q) (u v : ι), v ∈ Γ.aWords j u → v ∈ Φp π j u) ∧
        (∀ (i : Fin r) (u v : ι), Γ.bChoice i u = some v → v ∈ Ψp π i u)
    · rw [if_pos hp, if_pos hp, hweight Γ]
      ring
    · rw [if_neg hp, if_neg hp]
  have hmemΦp : ∀ (π : Finpartition (Finset.univ : Finset (Fin ℓ))) (j : Fin q) (u v : ι),
      v ∈ Φp π j u ↔
      (v ∈ U ∩ A j ∧ rank v < rank u ∧ u ∈ U ∩ A j ∧ π.part (tt u) = π.part (tt v)) := by
    intro π j u v
    rw [hΦp π j u, Finset.mem_filter]
  have hmemΨp : ∀ (π : Finpartition (Finset.univ : Finset (Fin ℓ))) (i : Fin r) (u v : ι),
      v ∈ Ψp π i u ↔
      (v ∈ U ∩ B i ∧ rank v < rank u ∧ u ∈ U ∩ B i ∧ π.part (tt u) = π.part (tt v)) := by
    intro π i u v
    rw [hΨp π i u, Finset.mem_filter]
  have hΦsub : ∀ (π : Finpartition (Finset.univ : Finset (Fin ℓ))) (j : Fin q) (u v : ι),
      v ∈ Φp π j u → v ∈ Φf j u := by
    intro π j u v hv
    obtain ⟨h1, h2, h3, -⟩ := (hmemΦp π j u v).mp hv
    exact (hmemΦ j u v).mpr ⟨h1, h2, h3⟩
  have hΨsub : ∀ (π : Finpartition (Finset.univ : Finset (Fin ℓ))) (i : Fin r) (u v : ι),
      v ∈ Ψp π i u → v ∈ Ψf i u := by
    intro π i u v hv
    obtain ⟨h1, h2, h3, -⟩ := (hmemΨp π i u v).mp hv
    exact (hmemΨ i u v).mpr ⟨h1, h2, h3⟩
  obtain ⟨HF, hHF⟩ : ∃ f : mixed_moment_occurrence_configuration ι q r → ℝ,
      f = fun Γ => ∑ π : Finpartition (Finset.univ : Finset (Fin ℓ)),
        ((-1 : ℝ) ^ (π.parts.card - 1)) * (Nat.factorial (π.parts.card - 1) : ℝ) *
        (if (∀ j u v, v ∈ Γ.aWords j u → v ∈ Φp π j u) ∧
            (∀ i u v, Γ.bChoice i u = some v → v ∈ Ψp π i u) then
          mixed_moment_configuration_weight I η x₀ y₀ Γ else 0) := ⟨_, rfl⟩
  have hHsum : HasSum HF
      (∑ π : Finpartition (Finset.univ : Finset (Fin ℓ)),
        ((-1 : ℝ) ^ (π.parts.card - 1)) * (Nat.factorial (π.parts.card - 1) : ℝ) *
        ∏ C ∈ π.parts, mixed_moment_right_hand_side I A B η x₀ y₀ C) := by
    rw [hHF]
    refine hasSum_sum fun π _ => HasSum.mul_left
      (((-1 : ℝ) ^ (π.parts.card - 1)) * (Nat.factorial (π.parts.card - 1) : ℝ))
      (hcombπ π)
  have hHpt : ∀ Γ : mixed_moment_occurrence_configuration ι q r,
      HF Γ = if mixed_moment_configuration_admissible I A B rank Γ ∧
          mixed_moment_configuration_connected I Γ then
        mixed_moment_configuration_weight I η x₀ y₀ Γ else 0 := by
    intro Γ
    simp only [hHF]
    by_cases hadm : mixed_moment_configuration_admissible I A B rank Γ
    · obtain ⟨G, hG⟩ : ∃ g : SimpleGraph (Fin ℓ), g = SimpleGraph.fromRel
          fun t t' ↦ ∃ u ∈ I t, ∃ v ∈ I t',
            (∃ j : Fin q, v ∈ Γ.aWords j u) ∨ ∃ i : Fin r, Γ.bChoice i u = some v :=
        ⟨_, rfl⟩
      have hconnG : mixed_moment_configuration_connected I Γ ↔ G.Connected := by
        rw [hG]
        exact Iff.rfl
      obtain ⟨s, hs⟩ : ∃ z : Setoid (Fin ℓ), ∀ t t' : Fin ℓ, z.r t t' = G.Reachable t t' :=
        ⟨⟨fun t t' => G.Reachable t t',
          fun t => SimpleGraph.Reachable.refl t,
          fun {t t'} h => SimpleGraph.Reachable.symm h,
          fun {t t' t''} h1 h2 => SimpleGraph.Reachable.trans h1 h2⟩, fun _ _ => rfl⟩
      obtain ⟨ρ, hρ⟩ : ∃ z : Finpartition (Finset.univ : Finset (Fin ℓ)),
          ∀ t t' : Fin ℓ, t' ∈ z.part t ↔ G.Reachable t t' := by
        refine ⟨Finpartition.ofSetoid s, fun t t' => ?_⟩
        exact Finpartition.mem_part_ofSetoid_iff_rel.trans (Iff.of_eq (hs t t'))
      have hreach1 : ∀ (t t' : Fin ℓ),
          (∃ u ∈ I t, ∃ v ∈ I t',
            (∃ j : Fin q, v ∈ Γ.aWords j u) ∨ ∃ i : Fin r, Γ.bChoice i u = some v) →
          G.Reachable t t' := by
        intro t t' h
        by_cases hne : t = t'
        · subst hne
          exact SimpleGraph.Reachable.refl _
        · refine SimpleGraph.Adj.reachable ?_
          rw [hG]
          exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inl h⟩
      have hsame : ∀ (π : Finpartition (Finset.univ : Finset (Fin ℓ))) (t t' : Fin ℓ),
          ((∀ j u v, v ∈ Γ.aWords j u → v ∈ Φp π j u) ∧
            (∀ i u v, Γ.bChoice i u = some v → v ∈ Ψp π i u)) →
          (∃ u ∈ I t, ∃ v ∈ I t',
            (∃ j : Fin q, v ∈ Γ.aWords j u) ∨ ∃ i : Fin r, Γ.bChoice i u = some v) →
          π.part t = π.part t' := by
        intro π t t' hok ⟨u, hut, v, hvt, hoccur⟩
        have httu : tt u = t := htuniq u t hut
        have httv : tt v = t' := htuniq v t' hvt
        rcases hoccur with ⟨j, hj⟩ | ⟨i, hi⟩
        · have h2 : π.part (tt u) = π.part (tt v) :=
            ((hmemΦp π j u v).mp (hok.1 j u v hj)).2.2.2
          rw [httu, httv] at h2
          exact h2
        · have h2 : π.part (tt u) = π.part (tt v) :=
            ((hmemΨp π i u v).mp (hok.2 i u v hi)).2.2.2
          rw [httu, httv] at h2
          exact h2
      have hprop : ∀ (π : Finpartition (Finset.univ : Finset (Fin ℓ))) (t t' : Fin ℓ),
          ((∀ j u v, v ∈ Γ.aWords j u → v ∈ Φp π j u) ∧
            (∀ i u v, Γ.bChoice i u = some v → v ∈ Ψp π i u)) →
          G.Reachable t t' → π.part t = π.part t' := by
        intro π t t' hok hreach
        have h' : Relation.ReflTransGen G.Adj t t' := by
          rw [← SimpleGraph.reachable_eq_reflTransGen]
          exact hreach
        clear hreach
        induction h' using Relation.ReflTransGen.trans_induction_on with
        | refl a => rfl
        | single hab =>
            rw [hG] at hab
            obtain ⟨-, hor⟩ := (SimpleGraph.fromRel_adj _ _ _).mp hab
            rcases hor with h | h
            · exact hsame π _ _ hok h
            · exact (hsame π _ _ hok h).symm
        | trans h₁ h₂ ih₁ ih₂ => rw [ih₁, ih₂]
      have hokle : ∀ π : Finpartition (Finset.univ : Finset (Fin ℓ)),
          ((∀ j u v, v ∈ Γ.aWords j u → v ∈ Φp π j u) ∧
            (∀ i u v, Γ.bChoice i u = some v → v ∈ Ψp π i u)) ↔ ρ ≤ π := by
        intro π
        constructor
        · intro hok b hb
          obtain ⟨t, ht⟩ := ρ.nonempty_of_mem_parts hb
          have hbt : ρ.part t = b := ρ.part_eq_of_mem hb ht
          refine ⟨π.part t, π.part_mem.2 (Finset.mem_univ _), ?_⟩
          rw [← hbt]
          intro t' ht'
          have hparts : π.part t = π.part t' :=
            hprop π t t' hok ((hρ t t').mp ht')
          have hmem : t' ∈ π.part t := by
            rw [hparts]
            exact π.mem_part (Finset.mem_univ _)
          exact hmem
        · intro hle
          constructor
          · intro j u v hv
            obtain ⟨hvU, hr, huU⟩ :=
              (hmemΦ j u v).mp (((hadmiff Γ).mp hadm).1 j u v hv)
            rw [hmemΦp π j u]
            refine ⟨hvU, hr, huU, ?_⟩
            have huU' : u ∈ U := (Finset.mem_inter.1 huU).1
            have hvU' : v ∈ U := (Finset.mem_inter.1 hvU).1
            have hreach : G.Reachable (tt u) (tt v) := hreach1 (tt u) (tt v)
              ⟨u, htt u huU', v, htt v hvU', Or.inl ⟨j, hv⟩⟩
            obtain ⟨C, hCπ, hCsub⟩ := hle (ρ.part_mem.2 (Finset.mem_univ _))
            have httu2 : tt u ∈ C := hCsub (ρ.mem_part (Finset.mem_univ _))
            have httv2 : tt v ∈ C :=
              hCsub ((hρ (tt u) (tt v)).mpr hreach)
            rw [π.part_eq_of_mem hCπ httu2, π.part_eq_of_mem hCπ httv2]
          · intro i u v hv
            obtain ⟨hvU, hr, huU⟩ :=
              (hmemΨ i u v).mp (((hadmiff Γ).mp hadm).2 i u v hv)
            rw [hmemΨp π i u]
            refine ⟨hvU, hr, huU, ?_⟩
            have huU' : u ∈ U := (Finset.mem_inter.1 huU).1
            have hvU' : v ∈ U := (Finset.mem_inter.1 hvU).1
            have hreach : G.Reachable (tt u) (tt v) := hreach1 (tt u) (tt v)
              ⟨u, htt u huU', v, htt v hvU', Or.inr ⟨i, hv⟩⟩
            obtain ⟨C, hCπ, hCsub⟩ := hle (ρ.part_mem.2 (Finset.mem_univ _))
            have httu2 : tt u ∈ C := hCsub (ρ.mem_part (Finset.mem_univ _))
            have httv2 : tt v ∈ C :=
              hCsub ((hρ (tt u) (tt v)).mpr hreach)
            rw [π.part_eq_of_mem hCπ httu2, π.part_eq_of_mem hCπ httv2]
      have hcardconn : ρ.parts.card = 1 ↔ mixed_moment_configuration_connected I Γ := by
        rw [hconnG]
        constructor
        · intro hcard
          obtain ⟨C₀, hC₀⟩ := Finset.card_eq_one.1 hcard
          have hcls : ∀ t : Fin ℓ, ρ.part t = C₀ := by
            intro t
            have h1 : ρ.part t ∈ ρ.parts := ρ.part_mem.2 (Finset.mem_univ _)
            rw [hC₀] at h1
            exact Finset.mem_singleton.1 h1
          refine (SimpleGraph.connected_iff G).2 ⟨?_, ⟨⟨0, hℓ⟩⟩⟩
          intro t t'
          have h1 : t' ∈ ρ.part t' := ρ.mem_part (Finset.mem_univ _)
          rw [hcls t'] at h1
          rw [← hcls t] at h1
          exact (hρ t t').mp h1
        · intro hconn
          have hpre : ∀ t t' : Fin ℓ, G.Reachable t t' :=
            ((SimpleGraph.connected_iff G).1 hconn).1
          have hcls : ∀ t : Fin ℓ, ρ.part t = ρ.part ⟨0, hℓ⟩ := by
            intro t
            have h1 : t ∈ ρ.part ⟨0, hℓ⟩ :=
              (hρ ⟨0, hℓ⟩ t).mpr (hpre ⟨0, hℓ⟩ t)
            exact ρ.part_eq_of_mem (ρ.part_mem.2 (Finset.mem_univ _)) h1
          have hsub : ∀ b ∈ ρ.parts, b = ρ.part ⟨0, hℓ⟩ := by
            intro b hb
            obtain ⟨t, ht⟩ := ρ.nonempty_of_mem_parts hb
            rw [← ρ.part_eq_of_mem hb ht, hcls t]
          have hparts : ρ.parts = {ρ.part ⟨0, hℓ⟩} :=
            Finset.eq_singleton_iff_unique_mem.2
              ⟨ρ.part_mem.2 (Finset.mem_univ _), hsub⟩
          rw [hparts, Finset.card_singleton]
      have hmob := finpartition_mobius_connected_cancellation
        (Finset.univ : Finset (Fin ℓ)) ρ ⟨⟨0, hℓ⟩, Finset.mem_univ _⟩
      have hconj : ∀ π : Finpartition (Finset.univ : Finset (Fin ℓ)),
          ((-1 : ℝ) ^ (π.parts.card - 1)) * (Nat.factorial (π.parts.card - 1) : ℝ) *
          (if (∀ j u v, v ∈ Γ.aWords j u → v ∈ Φp π j u) ∧
              (∀ i u v, Γ.bChoice i u = some v → v ∈ Ψp π i u) then
            mixed_moment_configuration_weight I η x₀ y₀ Γ else 0)
          = mixed_moment_configuration_weight I η x₀ y₀ Γ *
            @ite ℝ (ρ ≤ π) (Classical.propDecidable (ρ ≤ π))
              (((-1 : ℝ) ^ (π.parts.card - 1)) *
                (Nat.factorial (π.parts.card - 1) : ℝ)) 0 := by
        intro π
        by_cases hok : (∀ j u v, v ∈ Γ.aWords j u → v ∈ Φp π j u) ∧
            (∀ i u v, Γ.bChoice i u = some v → v ∈ Ψp π i u)
        · rw [if_pos hok, if_pos ((hokle π).mp hok)]
          ring
        · rw [if_neg hok, if_neg (fun h => hok ((hokle π).mpr h))]
          ring
      rw [Finset.sum_congr rfl (fun π _ => hconj π), ← Finset.mul_sum, hmob]
      by_cases hconn : mixed_moment_configuration_connected I Γ
      · rw [if_pos ((hcardconn).mpr hconn), if_pos ⟨hadm, hconn⟩, mul_one]
      · rw [if_neg (show ¬(ρ.parts.card = 1) from
            fun hcard => hconn (hcardconn.mp hcard)),
          if_neg (show ¬(mixed_moment_configuration_admissible I A B rank Γ ∧
            mixed_moment_configuration_connected I Γ) from fun h => hconn h.2), mul_zero]
    · have hzero : ∀ π : Finpartition (Finset.univ : Finset (Fin ℓ)),
          ¬ ((∀ j u v, v ∈ Γ.aWords j u → v ∈ Φp π j u) ∧
             (∀ i u v, Γ.bChoice i u = some v → v ∈ Ψp π i u)) :=
        fun π h => hadm ((hadmiff Γ).mpr
          ⟨fun j u v hv => hΦsub π j u v (h.1 j u v hv),
            fun i u v hv => hΨsub π i u v (h.2 i u v hv)⟩)
      rw [Finset.sum_eq_zero fun π _ => by rw [if_neg (hzero π), mul_zero],
        if_neg (show ¬(mixed_moment_configuration_admissible I A B rank Γ ∧
          mixed_moment_configuration_connected I Γ) from fun h => hadm h.1)]
  refine ⟨rank, hrankU, hsumm, ?_⟩
  have hfinal : HasSum (fun Γ :
      {Γ : mixed_moment_occurrence_configuration ι q r //
        mixed_moment_configuration_admissible I A B rank Γ ∧
        mixed_moment_configuration_connected I Γ} =>
      mixed_moment_configuration_weight I η x₀ y₀ Γ.1)
      (∑ π : Finpartition (Finset.univ : Finset (Fin ℓ)),
        ((-1 : ℝ) ^ (π.parts.card - 1)) * (Nat.factorial (π.parts.card - 1) : ℝ) *
        ∏ C ∈ π.parts, mixed_moment_right_hand_side I A B η x₀ y₀ C) := by
    refine (hasSum_subtype_iff_indicator
      (f := fun Γ : mixed_moment_occurrence_configuration ι q r =>
        mixed_moment_configuration_weight I η x₀ y₀ Γ)
      (s := {Γ : mixed_moment_occurrence_configuration ι q r |
        mixed_moment_configuration_admissible I A B rank Γ ∧
        mixed_moment_configuration_connected I Γ})).mpr ?_
    refine HasSum.congr_fun hHsum ?_
    intro Γ
    rw [hHpt Γ]
    by_cases hc : mixed_moment_configuration_admissible I A B rank Γ ∧
        mixed_moment_configuration_connected I Γ
    · rw [if_pos hc]
      exact Set.indicator_of_mem
        (f := fun Γ : mixed_moment_occurrence_configuration ι q r =>
          mixed_moment_configuration_weight I η x₀ y₀ Γ)
        (s := {Γ : mixed_moment_occurrence_configuration ι q r |
          mixed_moment_configuration_admissible I A B rank Γ ∧
          mixed_moment_configuration_connected I Γ}) hc
    · rw [if_neg hc]
      exact Set.indicator_of_notMem
        (f := fun Γ : mixed_moment_occurrence_configuration ι q r =>
          mixed_moment_configuration_weight I η x₀ y₀ Γ)
        (s := {Γ : mixed_moment_occurrence_configuration ι q r |
          mixed_moment_configuration_admissible I A B rank Γ ∧
          mixed_moment_configuration_connected I Γ}) hc
  exact hfinal.tsum_eq.symm

@[blueprint "lem:mixed-moment-positive-b-tree-majorant"
  (statement := /-- Under the hypotheses of the positive-$B$ case, fix a rank function $\varrho$ that is injective on $U=I_{[\ell]}$.  The sum of the weights of connected admissible configurations factors as
  \[
    \eta^L(L^2y_0)^{\ell-1}
      \left(\frac{x_0}{y_0}\right)^{cc(\mathcal B)-1}R,
    \qquad |R|\leq4\ell^{2\ell}.
  \]
  Here configurations, admissibility, connectivity, and weights are defined in \cref{def:mixed-moment-occurrence-configuration,def:mixed-moment-configuration-admissible,def:mixed-moment-configuration-connected,def:mixed-moment-configuration-weight}. -/)
  (proof := /-- The assertion is immediate for $\ell=1$.  Suppose $\ell\geq2$.  A connected induced graph has a spanning tree.  Order its edges and, for each edge, mark the least occurrence witnessing it; this is done in the occurrence-labelled configuration, so an $A$-mark includes its list position.  Cayley's bound gives at most $\ell^{\ell-2}$ underlying trees, each marked edge has at most $L^2$ ordered witnesses, and it has one of the two colours $A$ or $B$.  Thus the marked tree contributes at most $2^{\ell-1}\ell^{\ell-2}(L^2y_0)^{\ell-1}$ after replacing each $A$-weight by $x_0\leq y_0/2$.

  Every $B$-occurrence stays within one component of $\mathcal B$.  Contracting these components shows that at least $cc(\mathcal B)-1$ marked or unmarked occurrences have colour $A$, so their weights supply the factor $(x_0/y_0)^{cc(\mathcal B)-1}$.  To sum the residual configurations, retain a marked $A$-position as a gap in its word rather than deleting and closing the gap.  If a word with $k$ available letters contains $m$ specified marked positions, summing the remaining letters and all gap locations gives
  \[
    \sum_{n\geq m}\binom{n}{m}k^{n-m}x_0^n
      =\frac{x_0^m}{(1-kx_0)^{m+1}}.
  \]
  Hence no insertion-position multiplicity is discarded.  Summing this formula over the marked words, and the two choices in every unmarked $B$-slot, bounds the residual absolute mass by the corresponding product of reciprocal and direct absolute factors with one additional reciprocal factor per marked $A$-position.

  Pairwise disjointness gives at most $L$ nontrivial $A$-slots and at most $L$ nontrivial $B$-slots, with $k\leq L$.  The assumptions yield $Lx_0\leq1/(4L)$ and $Ly_0\leq1/(2L)$.  Applying the preceding product bound and $(1-a)^{-1}\leq\exp(2a)$ for $0\leq a\leq1/2$ shows that the residual mass, including all retained gaps, is at most $4$.  Combining it with the tree count, and using $2^{\ell-1}\ell^{\ell-2}\leq\ell^{2\ell}$, yields the claimed factorization and bound on $R$. -/)
  (title := /-- Position-preserving tree majorant in the positive-$B$ case -/)
  (latexEnv := "lemma")]
lemma mixed_moment_positive_b_tree_majorant
    {ι : Type*} [DecidableEq ι] {ℓ q r : ℕ}
    (I : Fin ℓ → Finset ι) (A : Fin q → Finset ι)
    (B : Fin r → Finset ι) (η x₀ y₀ : ℝ) (rank : ι → ℕ)
    (hI : Set.univ.PairwiseDisjoint I)
    (hA : Set.univ.PairwiseDisjoint A)
    (hB : Set.univ.PairwiseDisjoint B)
    (hℓ : 0 < ℓ) (hη : 0 ≤ η) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀)
    (hr : 1 ≤ r)
    (hsmall : 2 * (total_index_count I : ℝ) ^ 2 * y₀ ≤ 1)
    (hxy : 2 * x₀ ≤ y₀)
    (hrank : Set.InjOn rank (indexed_union I Finset.univ : Set ι)) :
    ∃ R : ℝ,
      (∑' Γ :
        {Γ : mixed_moment_occurrence_configuration ι q r //
          mixed_moment_configuration_admissible I A B rank Γ ∧
          mixed_moment_configuration_connected I Γ},
        mixed_moment_configuration_weight I η x₀ y₀ Γ.1) =
        η ^ total_index_count I *
          ((total_index_count I : ℝ) ^ 2 * y₀) ^ (ℓ - 1) *
          (x₀ / y₀) ^ (intersection_component_count I B - 1) * R ∧
      |R| ≤ 4 * (ℓ : ℝ) ^ (2 * ℓ) := by
  classical
  obtain ⟨L, hL⟩ : ∃ n : ℕ, n = total_index_count I := ⟨_, rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ n : ℕ, n = intersection_component_count I B := ⟨_, rfl⟩
  obtain ⟨NA, hNA⟩ : ∃ f : mixed_moment_occurrence_configuration ι q r → ℕ,
      ∀ Γ, f Γ = ∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
        (Γ.aWords j u).length := ⟨_, fun _ => rfl⟩
  obtain ⟨NB, hNB⟩ : ∃ f : mixed_moment_occurrence_configuration ι q r → ℕ,
      ∀ Γ, f Γ = ∑ i : Fin r,
        ((indexed_union I Finset.univ).filter fun u ↦ Γ.bChoice i u ≠ none).card :=
    ⟨_, fun _ => rfl⟩
  rw [← hL, ← hcc]
  have hwabs : ∀ Γ : mixed_moment_occurrence_configuration ι q r,
      |mixed_moment_configuration_weight I η x₀ y₀ Γ| =
        η ^ L * x₀ ^ NA Γ * y₀ ^ NB Γ := by
    intro Γ
    rw [mixed_moment_configuration_weight, hNA, hNB, ← hL, abs_mul, abs_mul, abs_pow,
      abs_pow, abs_pow, abs_of_nonneg hη, abs_of_nonneg hx₀, abs_neg, abs_of_nonneg hy₀]
  have hXY : (0:ℝ) ≤ (L : ℝ) ^ 2 * x₀ ∧ (L : ℝ) ^ 2 * x₀ ≤ ((L : ℝ) ^ 2 * y₀) / 2 ∧
      (0:ℝ) ≤ (L : ℝ) ^ 2 * y₀ ∧ (L : ℝ) ^ 2 * y₀ ≤ 1 / 2 := by
    refine ⟨by positivity, ?_, by positivity, ?_⟩
    · nlinarith [sq_nonneg ((L : ℝ))]
    · rw [hL]
      linarith
  have hcc1 : 1 ≤ cc := by
    rw [hcc, intersection_component_count]
    have : Nonempty (b_intersection_graph I B).ConnectedComponent :=
      ⟨(b_intersection_graph I B).connectedComponentMk ⟨0, hℓ⟩⟩
    exact Nat.one_le_iff_ne_zero.2 (Nat.card_ne_zero.2 ⟨this, Finite.of_fintype _⟩)
  have hccℓ : cc ≤ ℓ := by
    rw [hcc, intersection_component_count]
    calc Nat.card (b_intersection_graph I B).ConnectedComponent
        ≤ Nat.card (Fin ℓ) :=
          Nat.card_le_card_of_surjective _ (Quot.mk_surjective)
      _ = ℓ := by simp
  have hccineq : ∀ Γ : mixed_moment_occurrence_configuration ι q r,
      mixed_moment_configuration_admissible I A B rank Γ →
      mixed_moment_configuration_connected I Γ → cc - 1 ≤ NA Γ := by
    intro Γ hadm hconn
    have htall : ∀ u : ι, ∃ t : Fin ℓ,
        u ∈ indexed_union I Finset.univ → u ∈ I t := by
      intro u
      by_cases hu : u ∈ indexed_union I Finset.univ
      · obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.1 hu
        exact ⟨t, fun _ => ht⟩
      · exact ⟨⟨0, hℓ⟩, fun h => absurd h hu⟩
    choose tt htt using htall
    have hmemU : ∀ (u : ι) (t : Fin ℓ), u ∈ I t → u ∈ indexed_union I Finset.univ := by
      intro u t ht
      exact Finset.mem_biUnion.2 ⟨t, Finset.mem_univ t, ht⟩
    have htuniq : ∀ (u : ι) (t : Fin ℓ), u ∈ I t → tt u = t := by
      intro u t hut
      by_contra hne
      exact Finset.disjoint_left.1 (hI (Set.mem_univ (tt u)) (Set.mem_univ t) hne)
        (htt u (hmemU u t hut)) hut
    obtain ⟨U, hU⟩ : ∃ s : Finset ι, s = indexed_union I Finset.univ := ⟨_, rfl⟩
    obtain ⟨SA, hSA⟩ : ∃ s : Finset (ι × ι),
        s = (U ×ˢ U).filter (fun p => ∃ j : Fin q, p.2 ∈ Γ.aWords j p.1) := ⟨_, rfl⟩
    obtain ⟨φ, hφ⟩ : ∃ f : Fin ℓ → (b_intersection_graph I B).ConnectedComponent,
        ∀ t, f t = (b_intersection_graph I B).connectedComponentMk t := ⟨_, fun _ => rfl⟩
    obtain ⟨H, hH⟩ : ∃ G : SimpleGraph ((b_intersection_graph I B).ConnectedComponent),
        G = SimpleGraph.fromRel fun c c' =>
          ∃ u v : ι, (∃ j : Fin q, v ∈ Γ.aWords j u) ∧
            (∃ t : Fin ℓ, u ∈ I t ∧ φ t = c) ∧
            (∃ t' : Fin ℓ, v ∈ I t' ∧ φ t' = c') := ⟨_, rfl⟩
    obtain ⟨GG, hGG⟩ : ∃ G : SimpleGraph (Fin ℓ), G = SimpleGraph.fromRel
        fun t t' ↦ ∃ u ∈ I t, ∃ v ∈ I t',
          (∃ j : Fin q, v ∈ Γ.aWords j u) ∨
          ∃ i : Fin r, Γ.bChoice i u = some v := ⟨_, rfl⟩
    have hGGconn : GG.Connected := by
      rw [hGG]
      exact hconn
    have hrel : ∀ a b : Fin ℓ, (∃ u ∈ I a, ∃ v ∈ I b,
        (∃ j : Fin q, v ∈ Γ.aWords j u) ∨
        ∃ i : Fin r, Γ.bChoice i u = some v) → H.Reachable (φ a) (φ b) := by
      intro a b hab
      obtain ⟨u, hu, v, hv, halt⟩ := hab
      rcases halt with ⟨j, hj⟩ | ⟨i, hi⟩
      · by_cases hne : φ a = φ b
        · rw [hne]
        · refine SimpleGraph.Adj.reachable ?_
          rw [hH, SimpleGraph.fromRel_adj]
          exact ⟨hne, Or.inl ⟨u, v, ⟨j, hj⟩, ⟨a, hu, rfl⟩, ⟨b, hv, rfl⟩⟩⟩
      · have hbu := hadm.2.2.2 i u v hi
        have heq : φ a = φ b := by
          rw [hφ, hφ]
          by_cases hab2 : a = b
          · rw [hab2]
          · refine SimpleGraph.ConnectedComponent.eq.2 (SimpleGraph.Adj.reachable ?_)
            rw [b_intersection_graph, SimpleGraph.fromRel_adj]
            refine ⟨hab2, Or.inl ⟨i, ⟨u, Finset.mem_inter.2 ⟨hu, (Finset.mem_inter.1 hbu.1).2⟩⟩,
              ⟨v, Finset.mem_inter.2 ⟨hv, (Finset.mem_inter.1 hbu.2.1).2⟩⟩⟩⟩
        rw [heq]
    have hedgeAdj : ∀ a b : Fin ℓ, GG.Adj a b → H.Reachable (φ a) (φ b) := by
      intro a b h
      rw [hGG, SimpleGraph.fromRel_adj] at h
      rcases h.2 with hr | hr
      · exact hrel a b hr
      · exact (hrel b a hr).symm
    have hwalk : ∀ (a b : Fin ℓ), GG.Reachable a b → H.Reachable (φ a) (φ b) := by
      intro a b hab
      obtain ⟨w⟩ := hab
      induction w with
      | nil => exact SimpleGraph.Reachable.refl _
      | cons hadj p ih => exact SimpleGraph.Reachable.trans (hedgeAdj _ _ hadj) ih
    haveI hHne : Nonempty ((b_intersection_graph I B).ConnectedComponent) :=
      ⟨φ ⟨0, hℓ⟩⟩
    have hHconn : H.Connected := by
      refine ⟨?_⟩
      intro c c'
      obtain ⟨a, ha⟩ := Quot.exists_rep c
      obtain ⟨b, hb⟩ := Quot.exists_rep c'
      have ha' : φ a = c := by
        rw [hφ]
        exact ha
      have hb' : φ b = c' := by
        rw [hφ]
        exact hb
      rw [← ha', ← hb']
      exact hwalk a b (hGGconn a b)
    have hcard := hHconn.card_vert_le_card_edgeSet_add_one
    have hsub : H.edgeSet ⊆
        ↑(SA.image fun p : ι × ι => s(φ (tt p.1), φ (tt p.2))) := by
      intro e he
      induction e using Sym2.ind with
      | _ c c' =>
        rw [hH, SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at he
        have hgen : ∀ d d' : (b_intersection_graph I B).ConnectedComponent,
            (∃ u v : ι, (∃ j : Fin q, v ∈ Γ.aWords j u) ∧
              (∃ t : Fin ℓ, u ∈ I t ∧ φ t = d) ∧
              (∃ t' : Fin ℓ, v ∈ I t' ∧ φ t' = d')) →
            s(d, d') ∈ SA.image fun p : ι × ι => s(φ (tt p.1), φ (tt p.2)) := by
          intro d d' hdd
          obtain ⟨u, v, ⟨j, hj⟩, ⟨t, hut, htd⟩, ⟨t', hvt', ht'd⟩⟩ := hdd
          refine Finset.mem_image.2 ⟨(u, v), ?_, ?_⟩
          · rw [hSA]
            exact Finset.mem_filter.2 ⟨Finset.mk_mem_product
              (by rw [hU]; exact hmemU u t hut) (by rw [hU]; exact hmemU v t' hvt'),
              ⟨j, hj⟩⟩
          · rw [htuniq u t hut, htuniq v t' hvt', htd, ht'd]
        rcases he.2 with h | h
        · exact hgen c c' h
        · have h2 := hgen c' c h
          rwa [Sym2.eq_swap] at h2
    have hEcard : Nat.card H.edgeSet ≤
        (SA.image fun p : ι × ι => s(φ (tt p.1), φ (tt p.2))).card := by
      rw [Nat.card_coe_set_eq]
      calc H.edgeSet.ncard
          ≤ (((SA.image fun p : ι × ι => s(φ (tt p.1), φ (tt p.2))) :
              Finset (Sym2 ((b_intersection_graph I B).ConnectedComponent))) :
              Set (Sym2 ((b_intersection_graph I B).ConnectedComponent))).ncard :=
            Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = _ := Set.ncard_coe_finset _
    have hSAcard : SA.card ≤ NA Γ := by
      rw [hNA]
      have hPsub : SA ⊆ U.biUnion (fun u =>
          (Finset.univ : Finset (Fin q)).biUnion (fun j =>
            (Γ.aWords j u).toFinset.image (fun v => (u, v)))) := by
        intro p hp
        rw [hSA] at hp
        obtain ⟨hmem, j, hj⟩ := Finset.mem_filter.1 hp
        refine Finset.mem_biUnion.2 ⟨p.1, (Finset.mem_product.1 hmem).1, ?_⟩
        exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j,
          Finset.mem_image.2 ⟨p.2, List.mem_toFinset.2 hj, rfl⟩⟩
      calc SA.card
          ≤ (U.biUnion (fun u =>
              (Finset.univ : Finset (Fin q)).biUnion (fun j =>
                (Γ.aWords j u).toFinset.image (fun v => (u, v))))).card :=
            Finset.card_le_card hPsub
        _ ≤ ∑ u ∈ U, ((Finset.univ : Finset (Fin q)).biUnion (fun j =>
              (Γ.aWords j u).toFinset.image (fun v => (u, v)))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ u ∈ U, ∑ j : Fin q, (Γ.aWords j u).length := by
            refine Finset.sum_le_sum fun u _ => ?_
            refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun j _ => ?_)
            exact le_trans Finset.card_image_le (List.toFinset_card_le _)
        _ = ∑ j : Fin q, ∑ u ∈ U, (Γ.aWords j u).length := Finset.sum_comm
        _ = ∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
              (Γ.aWords j u).length := by rw [hU]
    have hIm : (SA.image fun p : ι × ι => s(φ (tt p.1), φ (tt p.2))).card ≤ SA.card :=
      Finset.card_image_le
    rw [hcc, intersection_component_count]
    omega
  have habineq : ∀ Γ : mixed_moment_occurrence_configuration ι q r,
      mixed_moment_configuration_admissible I A B rank Γ →
      mixed_moment_configuration_connected I Γ → ℓ - 1 ≤ NA Γ + NB Γ := by
    intro Γ hadm hconn
    have htall : ∀ u : ι, ∃ t : Fin ℓ,
        u ∈ indexed_union I Finset.univ → u ∈ I t := by
      intro u
      by_cases hu : u ∈ indexed_union I Finset.univ
      · obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.1 hu
        exact ⟨t, fun _ => ht⟩
      · exact ⟨⟨0, hℓ⟩, fun h => absurd h hu⟩
    choose tt htt using htall
    have hmemU : ∀ (u : ι) (t : Fin ℓ), u ∈ I t → u ∈ indexed_union I Finset.univ := by
      intro u t ht
      exact Finset.mem_biUnion.2 ⟨t, Finset.mem_univ t, ht⟩
    have htuniq : ∀ (u : ι) (t : Fin ℓ), u ∈ I t → tt u = t := by
      intro u t hut
      by_contra hne
      exact Finset.disjoint_left.1 (hI (Set.mem_univ (tt u)) (Set.mem_univ t) hne)
        (htt u (hmemU u t hut)) hut
    obtain ⟨U, hU⟩ : ∃ s : Finset ι, s = indexed_union I Finset.univ := ⟨_, rfl⟩
    obtain ⟨SA, hSA⟩ : ∃ s : Finset (ι × ι),
        s = (U ×ˢ U).filter (fun p => ∃ j : Fin q, p.2 ∈ Γ.aWords j p.1) := ⟨_, rfl⟩
    obtain ⟨SB, hSB⟩ : ∃ s : Finset (ι × ι),
        s = (U ×ˢ U).filter (fun p => ∃ i : Fin r, Γ.bChoice i p.1 = some p.2) :=
      ⟨_, rfl⟩
    obtain ⟨GG, hGG⟩ : ∃ G : SimpleGraph (Fin ℓ), G = SimpleGraph.fromRel
        fun t t' ↦ ∃ u ∈ I t, ∃ v ∈ I t',
          (∃ j : Fin q, v ∈ Γ.aWords j u) ∨
          ∃ i : Fin r, Γ.bChoice i u = some v := ⟨_, rfl⟩
    have hGGconn : GG.Connected := by
      rw [hGG]
      exact hconn
    have hcard := hGGconn.card_vert_le_card_edgeSet_add_one
    have hsub : GG.edgeSet ⊆
        ↑((SA ∪ SB).image fun p : ι × ι => s(tt p.1, tt p.2)) := by
      intro e he
      induction e using Sym2.ind with
      | _ t t' =>
        rw [hGG, SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at he
        have hgen : ∀ a b : Fin ℓ, (∃ u ∈ I a, ∃ v ∈ I b,
            (∃ j : Fin q, v ∈ Γ.aWords j u) ∨
            ∃ i : Fin r, Γ.bChoice i u = some v) →
            s(a, b) ∈ (SA ∪ SB).image fun p : ι × ι => s(tt p.1, tt p.2) := by
          intro a b hab
          obtain ⟨u, hu, v, hv, hjw⟩ := hab
          have hpm : (u, v) ∈ U ×ˢ U := Finset.mk_mem_product
            (by rw [hU]; exact hmemU u a hu) (by rw [hU]; exact hmemU v b hv)
          refine Finset.mem_image.2 ⟨(u, v), ?_, ?_⟩
          · rw [Finset.mem_union, hSA, hSB]
            rcases hjw with h | h
            · exact Or.inl (Finset.mem_filter.2 ⟨hpm, h⟩)
            · exact Or.inr (Finset.mem_filter.2 ⟨hpm, h⟩)
          · rw [htuniq u a hu, htuniq v b hv]
        rcases he.2 with h | h
        · exact hgen t t' h
        · have h2 := hgen t' t h
          rwa [Sym2.eq_swap] at h2
    have hEcard : Nat.card GG.edgeSet ≤
        ((SA ∪ SB).image fun p : ι × ι => s(tt p.1, tt p.2)).card := by
      rw [Nat.card_coe_set_eq]
      calc GG.edgeSet.ncard
          ≤ ((((SA ∪ SB).image fun p : ι × ι => s(tt p.1, tt p.2)) :
              Finset (Sym2 (Fin ℓ))) : Set (Sym2 (Fin ℓ))).ncard :=
            Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = _ := Set.ncard_coe_finset _
    have hSAcard : SA.card ≤ NA Γ := by
      rw [hNA]
      have hPsub : SA ⊆ U.biUnion (fun u =>
          (Finset.univ : Finset (Fin q)).biUnion (fun j =>
            (Γ.aWords j u).toFinset.image (fun v => (u, v)))) := by
        intro p hp
        rw [hSA] at hp
        obtain ⟨hmem, j, hj⟩ := Finset.mem_filter.1 hp
        refine Finset.mem_biUnion.2 ⟨p.1, (Finset.mem_product.1 hmem).1, ?_⟩
        exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j,
          Finset.mem_image.2 ⟨p.2, List.mem_toFinset.2 hj, rfl⟩⟩
      calc SA.card
          ≤ (U.biUnion (fun u =>
              (Finset.univ : Finset (Fin q)).biUnion (fun j =>
                (Γ.aWords j u).toFinset.image (fun v => (u, v))))).card :=
            Finset.card_le_card hPsub
        _ ≤ ∑ u ∈ U, ((Finset.univ : Finset (Fin q)).biUnion (fun j =>
              (Γ.aWords j u).toFinset.image (fun v => (u, v)))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ u ∈ U, ∑ j : Fin q, (Γ.aWords j u).length := by
            refine Finset.sum_le_sum fun u _ => ?_
            refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun j _ => ?_)
            exact le_trans Finset.card_image_le (List.toFinset_card_le _)
        _ = ∑ j : Fin q, ∑ u ∈ U, (Γ.aWords j u).length := Finset.sum_comm
        _ = ∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
              (Γ.aWords j u).length := by rw [hU]
    have hSBcard : SB.card ≤ NB Γ := by
      rw [hNB]
      have hch : ∀ p : ι × ι, ∃ i : Fin r,
          (∃ i' : Fin r, Γ.bChoice i' p.1 = some p.2) →
          Γ.bChoice i p.1 = some p.2 := by
        intro p
        by_cases h : ∃ i' : Fin r, Γ.bChoice i' p.1 = some p.2
        · obtain ⟨i, hi⟩ := h
          exact ⟨i, fun _ => hi⟩
        · exact ⟨⟨0, hr⟩, fun hh => absurd hh h⟩
      choose ii hii using hch
      have htgt : SB.card ≤ ((Finset.univ : Finset (Fin r)).biUnion (fun i =>
          (U.filter fun u => Γ.bChoice i u ≠ none).image (fun u => (i, u)))).card := by
        refine Finset.card_le_card_of_injOn (fun p => (ii p, p.1)) ?_ ?_
        · intro p hp
          rw [hSB] at hp
          obtain ⟨hmem, hex⟩ := Finset.mem_filter.1 hp
          refine Finset.mem_biUnion.2 ⟨ii p, Finset.mem_univ _,
            Finset.mem_image.2 ⟨p.1, Finset.mem_filter.2
              ⟨(Finset.mem_product.1 hmem).1, ?_⟩, rfl⟩⟩
          rw [hii p hex]
          exact Option.some_ne_none _
        · intro p hp p' hp' heq
          rw [hSB, Finset.mem_coe, Finset.mem_filter] at hp hp'
          have e1 : ii p = ii p' := congrArg Prod.fst heq
          have e2 : p.1 = p'.1 := congrArg Prod.snd heq
          have b1 := hii p hp.2
          have b2 := hii p' hp'.2
          rw [← e1, ← e2] at b2
          have e3 : some p.2 = some p'.2 := by rw [← b1, b2]
          exact Prod.ext e2 (Option.some_injective _ e3)
      refine le_trans htgt (le_trans Finset.card_biUnion_le ?_)
      refine Finset.sum_le_sum fun i _ => ?_
      refine le_trans Finset.card_image_le ?_
      rw [hU]
    have hIm : ((SA ∪ SB).image fun p : ι × ι => s(tt p.1, tt p.2)).card ≤
        SA.card + SB.card := le_trans Finset.card_image_le (Finset.card_union_le _ _)
    have hℓcard : Nat.card (Fin ℓ) = ℓ := by simp
    rw [hℓcard] at hcard
    omega
  have hUcard : (indexed_union I Finset.univ).card = L := by
    rw [hL]
    rfl
  have hext : ∀ Γ₁ Γ₂ : mixed_moment_occurrence_configuration ι q r,
      Γ₁.aWords = Γ₂.aWords → Γ₁.bChoice = Γ₂.bChoice → Γ₁ = Γ₂ := by
    intro Γ₁ Γ₂ h1 h2
    obtain ⟨a1, b1⟩ := Γ₁
    obtain ⟨a2, b2⟩ := Γ₂
    have e1 : a1 = a2 := h1
    have e2 : b1 = b2 := h2
    rw [e1, e2]
  have hcountA : ∀ (n : ℕ) (G : Finset (mixed_moment_occurrence_configuration ι q r)),
      (∀ Γ ∈ G, mixed_moment_configuration_admissible I A B rank Γ ∧
        (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
          (Γ.aWords j u).length) = n ∧
        Γ.bChoice = fun _ _ => none) →
      G.card ≤ (L ^ 2) ^ n := by
    intro n
    induction n with
    | zero =>
      intro G hG
      rw [pow_zero]
      refine Finset.card_le_one.2 ?_
      intro Γ₁ h1 Γ₂ h2
      have key : ∀ Γ, Γ ∈ G → ∀ j u, Γ.aWords j u = [] := by
        intro Γ hΓ j u
        by_cases huU : u ∈ indexed_union I Finset.univ
        · have hsum := (hG Γ hΓ).2.1
          have hj : ∑ u ∈ indexed_union I Finset.univ, (Γ.aWords j u).length = 0 :=
            Finset.sum_eq_zero_iff.1 hsum j (Finset.mem_univ j)
          exact List.length_eq_zero_iff.1 (Finset.sum_eq_zero_iff.1 hj u huU)
        · exact (hG Γ hΓ).1.2.1 j u (fun hmem => huU (Finset.mem_inter.1 hmem).1)
      refine hext Γ₁ Γ₂ (funext fun j => funext fun u => ?_) ?_
      · rw [key Γ₁ h1 j u, key Γ₂ h2 j u]
      · rw [(hG Γ₁ h1).2.2, (hG Γ₂ h2).2.2]
    | succ n ih =>
      intro G hG
      rcases Finset.eq_empty_or_nonempty (indexed_union I Finset.univ) with hUe | hUne
      · have hGe : G = ∅ := by
          refine Finset.eq_empty_of_forall_notMem ?_
          intro Γ hΓ
          have h2 := (hG Γ hΓ).2.1
          rw [hUe] at h2
          simp at h2
        rw [hGe]
        simp
      obtain ⟨ustar, hustar⟩ := hUne
      have hex : ∀ Γ : mixed_moment_occurrence_configuration ι q r,
          ∃ (u₀ v₀ : ι) (Γ' : mixed_moment_occurrence_configuration ι q r),
            mixed_moment_configuration_admissible I A B rank Γ →
            (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
              (Γ.aWords j u).length) = n + 1 →
              u₀ ∈ indexed_union I Finset.univ ∧
              v₀ ∈ indexed_union I Finset.univ ∧
              mixed_moment_configuration_admissible I A B rank Γ' ∧
              (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
                (Γ'.aWords j u).length) = n ∧
              Γ'.bChoice = Γ.bChoice ∧
              ∃ j₀ : Fin q, ∀ j u, Γ.aWords j u =
                if j = j₀ ∧ u = u₀ then v₀ :: Γ'.aWords j u else Γ'.aWords j u := by
        intro Γ
        by_cases hgood : mixed_moment_configuration_admissible I A B rank Γ ∧
            (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
              (Γ.aWords j u).length) = n + 1
        · obtain ⟨hadm, hN⟩ := hgood
          have hne : (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
              (Γ.aWords j u).length) ≠ 0 := by
            rw [hN]
            omega
          obtain ⟨j₀, -, hj₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
          obtain ⟨u₀, hu₀U, hu₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj₀
          have hwne : Γ.aWords j₀ u₀ ≠ [] := by
            intro h
            rw [h] at hu₀
            exact hu₀ rfl
          obtain ⟨v₀, w, hword⟩ := List.exists_cons_of_ne_nil hwne
          have hmemv : v₀ ∈ Γ.aWords j₀ u₀ := by
            rw [hword]
            exact List.mem_cons_self
          have hadm3 := hadm.2.2.1 j₀ u₀ v₀ hmemv
          obtain ⟨Γ', hΓ'w, hΓ'b⟩ :
              ∃ Γ' : mixed_moment_occurrence_configuration ι q r,
                (∀ j u, Γ'.aWords j u =
                  if j = j₀ ∧ u = u₀ then w else Γ.aWords j u) ∧
                Γ'.bChoice = Γ.bChoice :=
            ⟨⟨fun j u => if j = j₀ ∧ u = u₀ then w else Γ.aWords j u, Γ.bChoice⟩,
              fun j u => rfl, rfl⟩
          have hkey1 : (∑ u ∈ indexed_union I Finset.univ,
              (Γ'.aWords j₀ u).length) + 1 =
              ∑ u ∈ indexed_union I Finset.univ, (Γ.aWords j₀ u).length := by
            rw [← Finset.add_sum_erase (indexed_union I Finset.univ)
                (fun u => (Γ'.aWords j₀ u).length) hu₀U,
              ← Finset.add_sum_erase (indexed_union I Finset.univ)
                (fun u => (Γ.aWords j₀ u).length) hu₀U]
            have e0 : (Γ'.aWords j₀ u₀).length + 1 = (Γ.aWords j₀ u₀).length := by
              rw [hΓ'w, if_pos ⟨rfl, rfl⟩, hword]
              simp
            have e1 : (∑ u ∈ (indexed_union I Finset.univ).erase u₀,
                (Γ'.aWords j₀ u).length) =
                ∑ u ∈ (indexed_union I Finset.univ).erase u₀,
                  (Γ.aWords j₀ u).length := by
              refine Finset.sum_congr rfl fun u hu => ?_
              rw [hΓ'w, if_neg (fun hc => (Finset.mem_erase.1 hu).1 hc.2)]
            omega
          have hkey2 : ∀ j ∈ (Finset.univ : Finset (Fin q)).erase j₀,
              (∑ u ∈ indexed_union I Finset.univ, (Γ'.aWords j u).length) =
              ∑ u ∈ indexed_union I Finset.univ, (Γ.aWords j u).length := by
            intro j hj
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [hΓ'w, if_neg (fun hc => (Finset.mem_erase.1 hj).1 hc.1)]
          have hkey3 : (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
              (Γ'.aWords j u).length) + 1 =
              ∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
                (Γ.aWords j u).length := by
            rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin q))
                (fun j => ∑ u ∈ indexed_union I Finset.univ,
                  (Γ'.aWords j u).length) (Finset.mem_univ j₀),
              ← Finset.add_sum_erase (Finset.univ : Finset (Fin q))
                (fun j => ∑ u ∈ indexed_union I Finset.univ,
                  (Γ.aWords j u).length) (Finset.mem_univ j₀),
              Finset.sum_congr rfl hkey2]
            omega
          refine ⟨u₀, v₀, Γ', fun _ _ =>
            ⟨hu₀U, (Finset.mem_inter.1 hadm3.2.1).1, ?_, by omega, hΓ'b, ⟨j₀, ?_⟩⟩⟩
          · refine ⟨hadm.1, ?_, ?_, ?_⟩
            · intro j u hu
              by_cases hc : j = j₀ ∧ u = u₀
              · exact absurd (by rw [hc.1, hc.2]; exact hadm3.1) hu
              · rw [hΓ'w, if_neg hc]
                exact hadm.2.1 j u hu
            · intro j u v hv
              rw [hΓ'w] at hv
              by_cases hc : j = j₀ ∧ u = u₀
              · rw [if_pos hc] at hv
                rw [hc.1, hc.2]
                refine hadm.2.2.1 j₀ u₀ v ?_
                rw [hword]
                exact List.mem_cons_of_mem _ hv
              · rw [if_neg hc] at hv
                exact hadm.2.2.1 j u v hv
            · intro i u v hiv
              rw [hΓ'b] at hiv
              exact hadm.2.2.2 i u v hiv
          · intro j u
            by_cases hc : j = j₀ ∧ u = u₀
            · rw [if_pos hc, hΓ'w, if_pos hc, hc.1, hc.2, hword]
            · rw [if_neg hc, hΓ'w, if_neg hc]
        · exact ⟨ustar, ustar, Γ, fun h1 h2 => absurd ⟨h1, h2⟩ hgood⟩
      choose uu vv PP hPP using hex
      have hmaps : ∀ Γ ∈ G, ((uu Γ, vv Γ), PP Γ) ∈
          ((indexed_union I Finset.univ) ×ˢ (indexed_union I Finset.univ)) ×ˢ
            G.image PP := by
        intro Γ hΓ
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hPP Γ (hG Γ hΓ).1 (hG Γ hΓ).2.1
        exact Finset.mk_mem_product (Finset.mk_mem_product h1 h2)
          (Finset.mem_image_of_mem _ hΓ)
      have hinj : Set.InjOn (fun Γ => ((uu Γ, vv Γ), PP Γ)) G := by
        intro Γ₁ h1 Γ₂ h2 heq
        obtain ⟨p1, p2, p3, p4, p4b, j₁, p5⟩ :=
          hPP Γ₁ (hG Γ₁ h1).1 (hG Γ₁ h1).2.1
        obtain ⟨s1, s2, s3, s4, s4b, j₂, s5⟩ :=
          hPP Γ₂ (hG Γ₂ h2).1 (hG Γ₂ h2).2.1
        have hu : uu Γ₁ = uu Γ₂ := congrArg (fun x => x.1.1) heq
        have hv : vv Γ₁ = vv Γ₂ := congrArg (fun x => x.1.2) heq
        have hP : PP Γ₁ = PP Γ₂ := congrArg (fun x => x.2) heq
        have hj : j₁ = j₂ := by
          have m1 : vv Γ₁ ∈ Γ₁.aWords j₁ (uu Γ₁) := by
            rw [p5 j₁ (uu Γ₁), if_pos ⟨rfl, rfl⟩]
            exact List.mem_cons_self
          have m2 : vv Γ₂ ∈ Γ₂.aWords j₂ (uu Γ₂) := by
            rw [s5 j₂ (uu Γ₂), if_pos ⟨rfl, rfl⟩]
            exact List.mem_cons_self
          have a1 := ((hG Γ₁ h1).1.2.2.1 j₁ (uu Γ₁) (vv Γ₁) m1).1
          have a2 := ((hG Γ₂ h2).1.2.2.1 j₂ (uu Γ₂) (vv Γ₂) m2).1
          by_contra hne
          have hd : Disjoint (A j₁) (A j₂) := hA (Set.mem_univ j₁) (Set.mem_univ j₂) hne
          have m1' : uu Γ₁ ∈ A j₁ := (Finset.mem_inter.1 a1).2
          have m2' : uu Γ₁ ∈ A j₂ := by
            rw [hu]
            exact (Finset.mem_inter.1 a2).2
          exact Finset.disjoint_left.1 hd m1' m2'
        refine hext Γ₁ Γ₂ (funext fun j => funext fun u => ?_) ?_
        · rw [p5 j u, s5 j u, hu, hv, hP, hj]
        · rw [← p4b, ← s4b, hP]
      calc G.card ≤ (((indexed_union I Finset.univ) ×ˢ
            (indexed_union I Finset.univ)) ×ˢ G.image PP).card :=
            Finset.card_le_card_of_injOn _ hmaps hinj
        _ = (L * L) * (G.image PP).card := by
            rw [Finset.card_product, Finset.card_product, hUcard]
        _ ≤ (L * L) * (L ^ 2) ^ n := by
            refine Nat.mul_le_mul_left _ (ih _ ?_)
            intro Γ hΓ
            obtain ⟨Γ₀, hΓ₀, rfl⟩ := Finset.mem_image.1 hΓ
            obtain ⟨p1, p2, p3, p4, p4b, -⟩ :=
              hPP Γ₀ (hG Γ₀ hΓ₀).1 (hG Γ₀ hΓ₀).2.1
            exact ⟨p3, p4, by rw [p4b]; exact (hG Γ₀ hΓ₀).2.2⟩
        _ = (L ^ 2) ^ (n + 1) := by ring
  have hcountB : ∀ (n : ℕ) (G : Finset (mixed_moment_occurrence_configuration ι q r)),
      (∀ Γ ∈ G, mixed_moment_configuration_admissible I A B rank Γ ∧
        (∑ i : Fin r, ((indexed_union I Finset.univ).filter
          fun u => Γ.bChoice i u ≠ none).card) = n ∧
        Γ.aWords = fun _ _ => []) →
      G.card ≤ (L ^ 2) ^ n := by
    intro n
    induction n with
    | zero =>
      intro G hG
      rw [pow_zero]
      refine Finset.card_le_one.2 ?_
      intro Γ₁ h1 Γ₂ h2
      have key : ∀ Γ, Γ ∈ G → Γ.bChoice = fun _ _ => none := by
        intro Γ hΓ
        refine funext fun i => funext fun u => ?_
        by_cases huU : u ∈ indexed_union I Finset.univ
        · have hsum := (hG Γ hΓ).2.1
          have hi : ((indexed_union I Finset.univ).filter
              fun u => Γ.bChoice i u ≠ none).card = 0 :=
            Finset.sum_eq_zero_iff.1 hsum i (Finset.mem_univ i)
          have hnm : u ∉ (indexed_union I Finset.univ).filter
              fun u => Γ.bChoice i u ≠ none := by
            rw [Finset.card_eq_zero] at hi
            rw [hi]
            exact Finset.notMem_empty u
          by_contra hc
          exact hnm (Finset.mem_filter.2 ⟨huU, hc⟩)
        · by_contra hc
          obtain ⟨v, hv⟩ : ∃ v, Γ.bChoice i u = some v := Option.ne_none_iff_exists'.1 hc
          exact huU (Finset.mem_inter.1 ((hG Γ hΓ).1.2.2.2 i u v hv).1).1
      refine hext Γ₁ Γ₂ ?_ ?_
      · rw [(hG Γ₁ h1).2.2, (hG Γ₂ h2).2.2]
      · rw [key Γ₁ h1, key Γ₂ h2]
    | succ n ih =>
      intro G hG
      rcases Finset.eq_empty_or_nonempty (indexed_union I Finset.univ) with hUe | hUne
      · have hGe : G = ∅ := by
          refine Finset.eq_empty_of_forall_notMem ?_
          intro Γ hΓ
          have h2 := (hG Γ hΓ).2.1
          rw [hUe] at h2
          simp at h2
        rw [hGe]
        simp
      obtain ⟨ustar, hustar⟩ := hUne
      have hex : ∀ Γ : mixed_moment_occurrence_configuration ι q r,
          ∃ (u₀ v₀ : ι) (Γ' : mixed_moment_occurrence_configuration ι q r),
            mixed_moment_configuration_admissible I A B rank Γ →
            (∑ i : Fin r, ((indexed_union I Finset.univ).filter
              fun u => Γ.bChoice i u ≠ none).card) = n + 1 →
              u₀ ∈ indexed_union I Finset.univ ∧
              v₀ ∈ indexed_union I Finset.univ ∧
              mixed_moment_configuration_admissible I A B rank Γ' ∧
              (∑ i : Fin r, ((indexed_union I Finset.univ).filter
                fun u => Γ'.bChoice i u ≠ none).card) = n ∧
              Γ'.aWords = Γ.aWords ∧
              ∃ i₀ : Fin r, ∀ i u, Γ.bChoice i u =
                if i = i₀ ∧ u = u₀ then some v₀ else Γ'.bChoice i u := by
        intro Γ
        by_cases hgood : mixed_moment_configuration_admissible I A B rank Γ ∧
            (∑ i : Fin r, ((indexed_union I Finset.univ).filter
              fun u => Γ.bChoice i u ≠ none).card) = n + 1
        · obtain ⟨hadm, hN⟩ := hgood
          have hne : (∑ i : Fin r, ((indexed_union I Finset.univ).filter
              fun u => Γ.bChoice i u ≠ none).card) ≠ 0 := by
            rw [hN]
            omega
          obtain ⟨i₀, -, hi₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
          obtain ⟨u₀, hu₀mem⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hi₀)
          obtain ⟨hu₀U, hu₀ne⟩ := Finset.mem_filter.1 hu₀mem
          obtain ⟨v₀, hv₀⟩ : ∃ v, Γ.bChoice i₀ u₀ = some v :=
            Option.ne_none_iff_exists'.1 hu₀ne
          have hadm4 := hadm.2.2.2 i₀ u₀ v₀ hv₀
          obtain ⟨Γ', hΓ'w, hΓ'b⟩ :
              ∃ Γ' : mixed_moment_occurrence_configuration ι q r,
                Γ'.aWords = Γ.aWords ∧
                (∀ i u, Γ'.bChoice i u =
                  if i = i₀ ∧ u = u₀ then none else Γ.bChoice i u) :=
            ⟨⟨Γ.aWords, fun i u => if i = i₀ ∧ u = u₀ then none else Γ.bChoice i u⟩,
              rfl, fun i u => rfl⟩
          have hset : ((indexed_union I Finset.univ).filter
              fun u => Γ'.bChoice i₀ u ≠ none) =
              (((indexed_union I Finset.univ).filter
                fun u => Γ.bChoice i₀ u ≠ none).erase u₀) := by
            ext u
            constructor
            · intro hu
              obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
              rw [hΓ'b i₀ u] at hu2
              by_cases hc : u = u₀
              · rw [if_pos ⟨rfl, hc⟩] at hu2
                exact absurd rfl hu2
              · rw [if_neg (fun hh => hc hh.2)] at hu2
                exact Finset.mem_erase.2 ⟨hc, Finset.mem_filter.2 ⟨hu1, hu2⟩⟩
            · intro hu
              obtain ⟨hune, hmem⟩ := Finset.mem_erase.1 hu
              obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hmem
              refine Finset.mem_filter.2 ⟨hu1, ?_⟩
              rw [hΓ'b i₀ u, if_neg (fun hh => hune hh.2)]
              exact hu2
          have hkey1 : ((indexed_union I Finset.univ).filter
              fun u => Γ'.bChoice i₀ u ≠ none).card + 1 =
              ((indexed_union I Finset.univ).filter
                fun u => Γ.bChoice i₀ u ≠ none).card := by
            have hpos : 0 < ((indexed_union I Finset.univ).filter
                fun u => Γ.bChoice i₀ u ≠ none).card :=
              Finset.card_pos.2 ⟨u₀, hu₀mem⟩
            rw [hset, Finset.card_erase_of_mem hu₀mem]
            omega
          have hkey2 : ∀ i ∈ (Finset.univ : Finset (Fin r)).erase i₀,
              ((indexed_union I Finset.univ).filter
                fun u => Γ'.bChoice i u ≠ none).card =
              ((indexed_union I Finset.univ).filter
                fun u => Γ.bChoice i u ≠ none).card := by
            intro i hi
            refine congrArg Finset.card (Finset.filter_congr fun u _ => ?_)
            rw [hΓ'b, if_neg (fun hh => (Finset.mem_erase.1 hi).1 hh.1)]
          have hkey3 : (∑ i : Fin r, ((indexed_union I Finset.univ).filter
              fun u => Γ'.bChoice i u ≠ none).card) + 1 =
              ∑ i : Fin r, ((indexed_union I Finset.univ).filter
                fun u => Γ.bChoice i u ≠ none).card := by
            rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin r))
                (fun i => ((indexed_union I Finset.univ).filter
                  fun u => Γ'.bChoice i u ≠ none).card) (Finset.mem_univ i₀),
              ← Finset.add_sum_erase (Finset.univ : Finset (Fin r))
                (fun i => ((indexed_union I Finset.univ).filter
                  fun u => Γ.bChoice i u ≠ none).card) (Finset.mem_univ i₀),
              Finset.sum_congr rfl hkey2]
            omega
          refine ⟨u₀, v₀, Γ', fun _ _ =>
            ⟨hu₀U, (Finset.mem_inter.1 hadm4.2.1).1, ?_, by omega, hΓ'w, ⟨i₀, ?_⟩⟩⟩
          · refine ⟨hadm.1, ?_, ?_, ?_⟩
            · intro j u hu
              rw [hΓ'w]
              exact hadm.2.1 j u hu
            · intro j u v hv
              rw [hΓ'w] at hv
              exact hadm.2.2.1 j u v hv
            · intro i u v hiv
              rw [hΓ'b] at hiv
              by_cases hc : i = i₀ ∧ u = u₀
              · rw [if_pos hc] at hiv
                exact (Option.some_ne_none v (hiv.symm)).elim
              · rw [if_neg hc] at hiv
                exact hadm.2.2.2 i u v hiv
          · intro i u
            by_cases hc : i = i₀ ∧ u = u₀
            · rw [if_pos hc, hc.1, hc.2]
              exact hv₀
            · rw [if_neg hc, hΓ'b, if_neg hc]
        · exact ⟨ustar, ustar, Γ, fun h1 h2 => absurd ⟨h1, h2⟩ hgood⟩
      choose uu vv PP hPP using hex
      have hmaps : ∀ Γ ∈ G, ((uu Γ, vv Γ), PP Γ) ∈
          ((indexed_union I Finset.univ) ×ˢ (indexed_union I Finset.univ)) ×ˢ
            G.image PP := by
        intro Γ hΓ
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hPP Γ (hG Γ hΓ).1 (hG Γ hΓ).2.1
        exact Finset.mk_mem_product (Finset.mk_mem_product h1 h2)
          (Finset.mem_image_of_mem _ hΓ)
      have hinj : Set.InjOn (fun Γ => ((uu Γ, vv Γ), PP Γ)) G := by
        intro Γ₁ h1 Γ₂ h2 heq
        obtain ⟨p1, p2, p3, p4, p4b, i₁, p5⟩ :=
          hPP Γ₁ (hG Γ₁ h1).1 (hG Γ₁ h1).2.1
        obtain ⟨s1, s2, s3, s4, s4b, i₂, s5⟩ :=
          hPP Γ₂ (hG Γ₂ h2).1 (hG Γ₂ h2).2.1
        have hu : uu Γ₁ = uu Γ₂ := congrArg (fun x => x.1.1) heq
        have hv : vv Γ₁ = vv Γ₂ := congrArg (fun x => x.1.2) heq
        have hP : PP Γ₁ = PP Γ₂ := congrArg (fun x => x.2) heq
        have hi : i₁ = i₂ := by
          have m1 : Γ₁.bChoice i₁ (uu Γ₁) = some (vv Γ₁) := by
            rw [p5 i₁ (uu Γ₁), if_pos ⟨rfl, rfl⟩]
          have m2 : Γ₂.bChoice i₂ (uu Γ₂) = some (vv Γ₂) := by
            rw [s5 i₂ (uu Γ₂), if_pos ⟨rfl, rfl⟩]
          have a1 := ((hG Γ₁ h1).1.2.2.2 i₁ (uu Γ₁) (vv Γ₁) m1).1
          have a2 := ((hG Γ₂ h2).1.2.2.2 i₂ (uu Γ₂) (vv Γ₂) m2).1
          by_contra hne
          have hd : Disjoint (B i₁) (B i₂) := hB (Set.mem_univ i₁) (Set.mem_univ i₂) hne
          have m1' : uu Γ₁ ∈ B i₁ := (Finset.mem_inter.1 a1).2
          have m2' : uu Γ₁ ∈ B i₂ := by
            rw [hu]
            exact (Finset.mem_inter.1 a2).2
          exact Finset.disjoint_left.1 hd m1' m2'
        refine hext Γ₁ Γ₂ ?_ (funext fun i => funext fun u => ?_)
        · rw [← p4b, ← s4b, hP]
        · rw [p5 i u, s5 i u, hu, hv, hP, hi]
      calc G.card ≤ (((indexed_union I Finset.univ) ×ˢ
            (indexed_union I Finset.univ)) ×ˢ G.image PP).card :=
            Finset.card_le_card_of_injOn _ hmaps hinj
        _ = (L * L) * (G.image PP).card := by
            rw [Finset.card_product, Finset.card_product, hUcard]
        _ ≤ (L * L) * (L ^ 2) ^ n := by
            refine Nat.mul_le_mul_left _ (ih _ ?_)
            intro Γ hΓ
            obtain ⟨Γ₀, hΓ₀, rfl⟩ := Finset.mem_image.1 hΓ
            obtain ⟨p1, p2, p3, p4, p4b, -⟩ :=
              hPP Γ₀ (hG Γ₀ hΓ₀).1 (hG Γ₀ hΓ₀).2.1
            exact ⟨p3, p4, by rw [p4b]; exact (hG Γ₀ hΓ₀).2.2⟩
        _ = (L ^ 2) ^ (n + 1) := by ring
  have hcount : ∀ (a b : ℕ) (G : Finset (mixed_moment_occurrence_configuration ι q r)),
      (∀ Γ ∈ G, mixed_moment_configuration_admissible I A B rank Γ ∧
        NA Γ = a ∧ NB Γ = b) → G.card ≤ (L ^ 2) ^ a * (L ^ 2) ^ b := by
    intro a b G hG
    obtain ⟨f1, hf1w, hf1b⟩ :
        ∃ f : mixed_moment_occurrence_configuration ι q r →
          mixed_moment_occurrence_configuration ι q r,
          (∀ Γ, (f Γ).aWords = Γ.aWords) ∧ (∀ Γ, (f Γ).bChoice = fun _ _ => none) :=
      ⟨fun Γ => ⟨Γ.aWords, fun _ _ => none⟩, fun Γ => rfl, fun Γ => rfl⟩
    obtain ⟨f2, hf2w, hf2b⟩ :
        ∃ f : mixed_moment_occurrence_configuration ι q r →
          mixed_moment_occurrence_configuration ι q r,
          (∀ Γ, (f Γ).aWords = fun _ _ => []) ∧ (∀ Γ, (f Γ).bChoice = Γ.bChoice) :=
      ⟨fun Γ => ⟨fun _ _ => [], Γ.bChoice⟩, fun Γ => rfl, fun Γ => rfl⟩
    have hmaps : ∀ Γ ∈ G, (f1 Γ, f2 Γ) ∈ (G.image f1) ×ˢ (G.image f2) := fun Γ hΓ =>
      Finset.mk_mem_product (Finset.mem_image_of_mem _ hΓ)
        (Finset.mem_image_of_mem _ hΓ)
    have hinj : Set.InjOn (fun Γ => (f1 Γ, f2 Γ)) G := by
      intro Γ₁ _ Γ₂ _ heq
      have e1 : f1 Γ₁ = f1 Γ₂ := congrArg Prod.fst heq
      have e2 : f2 Γ₁ = f2 Γ₂ := congrArg Prod.snd heq
      refine hext Γ₁ Γ₂ ?_ ?_
      · rw [← hf1w Γ₁, ← hf1w Γ₂, e1]
      · rw [← hf2b Γ₁, ← hf2b Γ₂, e2]
    have hA1 : (G.image f1).card ≤ (L ^ 2) ^ a := by
      refine hcountA a _ ?_
      intro Γ hΓ
      obtain ⟨Γ₀, hΓ₀, rfl⟩ := Finset.mem_image.1 hΓ
      have hadm := (hG Γ₀ hΓ₀).1
      refine ⟨⟨hadm.1, ?_, ?_, ?_⟩, ?_, hf1b Γ₀⟩
      · intro j u hu
        rw [hf1w Γ₀]
        exact hadm.2.1 j u hu
      · intro j u v hv
        rw [hf1w Γ₀] at hv
        exact hadm.2.2.1 j u v hv
      · intro i u v hiv
        rw [hf1b Γ₀] at hiv
        exact (Option.some_ne_none v hiv.symm).elim
      · rw [hf1w Γ₀, ← hNA]
        exact (hG Γ₀ hΓ₀).2.1
    have hB1 : (G.image f2).card ≤ (L ^ 2) ^ b := by
      refine hcountB b _ ?_
      intro Γ hΓ
      obtain ⟨Γ₀, hΓ₀, rfl⟩ := Finset.mem_image.1 hΓ
      have hadm := (hG Γ₀ hΓ₀).1
      refine ⟨⟨hadm.1, ?_, ?_, ?_⟩, ?_, hf2w Γ₀⟩
      · intro j u hu
        rw [hf2w Γ₀]
      · intro j u v hv
        rw [hf2w Γ₀] at hv
        exact absurd hv (List.not_mem_nil)
      · intro i u v hiv
        rw [hf2b Γ₀] at hiv
        exact hadm.2.2.2 i u v hiv
      · rw [hf2b Γ₀, ← hNB]
        exact (hG Γ₀ hΓ₀).2.2
    calc G.card ≤ ((G.image f1) ×ˢ (G.image f2)).card :=
          Finset.card_le_card_of_injOn _ hmaps hinj
      _ = (G.image f1).card * (G.image f2).card := Finset.card_product _ _
      _ ≤ (L ^ 2) ^ a * (L ^ 2) ^ b := Nat.mul_le_mul hA1 hB1
  have hYnn : (0:ℝ) ≤ (L : ℝ) ^ 2 * y₀ := mul_nonneg (by positivity) hy₀
  have hXnn : (0:ℝ) ≤ (L : ℝ) ^ 2 * x₀ := mul_nonneg (by positivity) hx₀
  have hDnn : (0:ℝ) ≤ x₀ / y₀ := div_nonneg hx₀ hy₀
  have hCnn : (0:ℝ) ≤ η ^ L * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - 1) * (x₀ / y₀) ^ (cc - 1) :=
    mul_nonneg (mul_nonneg (pow_nonneg hη _) (pow_nonneg hYnn _)) (pow_nonneg hDnn _)
  have hgeom : ∀ k : ℕ, ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ i ≤ 2 := by
    intro k
    have h := geom_sum_mul ((1:ℝ)/2) k
    have hs : (0:ℝ) ≤ ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ i :=
      Finset.sum_nonneg fun i _ => by positivity
    have hk : (0:ℝ) ≤ ((1:ℝ)/2) ^ k := by positivity
    nlinarith [h, hs, hk]
  have hbound : ∀ F : Finset {Γ : mixed_moment_occurrence_configuration ι q r //
      mixed_moment_configuration_admissible I A B rank Γ ∧
      mixed_moment_configuration_connected I Γ},
      ∑ Γ ∈ F, |mixed_moment_configuration_weight I η x₀ y₀ Γ.1| ≤
        4 * (η ^ L * ((L : ℝ) ^ 2 * x₀) ^ (cc - 1) * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - cc)) := by
    intro F
    obtain ⟨P, hP⟩ : ∃ P : Finset (ℕ × ℕ),
        P = F.image (fun Γ => (NA Γ.1, NB Γ.1)) := ⟨_, rfl⟩
    have hPmem : ∀ p ∈ P, cc - 1 ≤ p.1 ∧ ℓ - 1 ≤ p.1 + p.2 := by
      intro p hp
      rw [hP] at hp
      obtain ⟨Γ, hΓ, rfl⟩ := Finset.mem_image.1 hp
      exact ⟨hccineq Γ.1 Γ.2.1 Γ.2.2, habineq Γ.1 Γ.2.1 Γ.2.2⟩
    have e1 : ∑ Γ ∈ F, |mixed_moment_configuration_weight I η x₀ y₀ Γ.1| =
        η ^ L * ∑ Γ ∈ F, (x₀ ^ NA Γ.1 * y₀ ^ NB Γ.1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun Γ _ => by rw [hwabs Γ.1, mul_assoc]
    have hmain : ∑ Γ ∈ F, (x₀ ^ NA Γ.1 * y₀ ^ NB Γ.1) ≤
        4 * (((L : ℝ) ^ 2 * x₀) ^ (cc - 1) * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - cc)) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun Γ => (NA Γ.1, NB Γ.1)) (t := P)
        (fun Γ hΓ => by rw [hP]; exact Finset.mem_image_of_mem _ hΓ)]
      have hinner : ∀ p ∈ P,
          (∑ Γ ∈ F.filter (fun Γ => (NA Γ.1, NB Γ.1) = p), (x₀ ^ NA Γ.1 * y₀ ^ NB Γ.1)) ≤
            ((L : ℝ) ^ 2 * x₀) ^ p.1 * ((L : ℝ) ^ 2 * y₀) ^ p.2 := by
        intro p _
        have h1 : ∀ Γ ∈ F.filter (fun Γ => (NA Γ.1, NB Γ.1) = p),
            x₀ ^ NA Γ.1 * y₀ ^ NB Γ.1 = x₀ ^ p.1 * y₀ ^ p.2 := by
          intro Γ hΓ
          have h2 := (Finset.mem_filter.1 hΓ).2
          rw [show NA Γ.1 = p.1 from congrArg Prod.fst h2,
            show NB Γ.1 = p.2 from congrArg Prod.snd h2]
        rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
        have hcard : (F.filter (fun Γ => (NA Γ.1, NB Γ.1) = p)).card ≤
            (L ^ 2) ^ p.1 * (L ^ 2) ^ p.2 := by
          have hh := hcount p.1 p.2
            ((F.filter (fun Γ => (NA Γ.1, NB Γ.1) = p)).image (fun Γ => Γ.1)) ?_
          · rwa [Finset.card_image_of_injective _ Subtype.val_injective] at hh
          · intro Γ hΓ
            obtain ⟨Γ', hΓ', rfl⟩ := Finset.mem_image.1 hΓ
            have h2 := (Finset.mem_filter.1 hΓ').2
            exact ⟨Γ'.2.1, congrArg Prod.fst h2, congrArg Prod.snd h2⟩
        have hcast : ((F.filter (fun Γ => (NA Γ.1, NB Γ.1) = p)).card : ℝ) ≤
            ((L : ℝ) ^ 2) ^ p.1 * ((L : ℝ) ^ 2) ^ p.2 := by
          have he : (((L ^ 2) ^ p.1 * (L ^ 2) ^ p.2 : ℕ) : ℝ) =
              ((L : ℝ) ^ 2) ^ p.1 * ((L : ℝ) ^ 2) ^ p.2 := by
            push_cast
            ring
          rw [← he]
          exact_mod_cast hcard
        calc ((F.filter (fun Γ => (NA Γ.1, NB Γ.1) = p)).card : ℝ) * (x₀ ^ p.1 * y₀ ^ p.2)
            ≤ (((L : ℝ) ^ 2) ^ p.1 * ((L : ℝ) ^ 2) ^ p.2) * (x₀ ^ p.1 * y₀ ^ p.2) :=
              mul_le_mul_of_nonneg_right hcast
                (mul_nonneg (pow_nonneg hx₀ _) (pow_nonneg hy₀ _))
          _ = ((L : ℝ) ^ 2 * x₀) ^ p.1 * ((L : ℝ) ^ 2 * y₀) ^ p.2 := by
              rw [mul_pow, mul_pow]
              ring
      refine le_trans (Finset.sum_le_sum hinner) ?_
      have hper : ∀ p ∈ P,
          ((L : ℝ) ^ 2 * x₀) ^ p.1 * ((L : ℝ) ^ 2 * y₀) ^ p.2 ≤
            ((L : ℝ) ^ 2 * x₀) ^ (cc - 1) * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - cc) *
              (((1:ℝ)/2) ^ (p.1 - (cc - 1)) * ((1:ℝ)/2) ^ (p.1 + p.2 - (ℓ - 1))) := by
        intro p hp
        obtain ⟨h1, h2⟩ := hPmem p hp
        have ea : p.1 = (cc - 1) + (p.1 - (cc - 1)) := by omega
        have eb : (p.1 - (cc - 1)) + p.2 = (ℓ - cc) + (p.1 + p.2 - (ℓ - 1)) := by omega
        have hstep1 : ((L : ℝ) ^ 2 * x₀) ^ (p.1 - (cc - 1)) ≤
            ((1:ℝ)/2) ^ (p.1 - (cc - 1)) * ((L : ℝ) ^ 2 * y₀) ^ (p.1 - (cc - 1)) := by
          have h3 : ((L : ℝ) ^ 2 * x₀) ^ (p.1 - (cc - 1)) ≤
              (((L : ℝ) ^ 2 * y₀) / 2) ^ (p.1 - (cc - 1)) :=
            pow_le_pow_left₀ hXnn hXY.2.1 _
          refine le_trans h3 (le_of_eq ?_)
          rw [div_pow, div_pow, one_pow]
          ring
        have hstep2 : ((L : ℝ) ^ 2 * y₀) ^ (p.1 + p.2 - (ℓ - 1)) ≤
            ((1:ℝ)/2) ^ (p.1 + p.2 - (ℓ - 1)) :=
          pow_le_pow_left₀ hYnn hXY.2.2.2 _
        calc ((L : ℝ) ^ 2 * x₀) ^ p.1 * ((L : ℝ) ^ 2 * y₀) ^ p.2
            = ((L : ℝ) ^ 2 * x₀) ^ (cc - 1) *
                (((L : ℝ) ^ 2 * x₀) ^ (p.1 - (cc - 1)) * ((L : ℝ) ^ 2 * y₀) ^ p.2) := by
              rw [← mul_assoc, ← pow_add, ← ea]
          _ ≤ ((L : ℝ) ^ 2 * x₀) ^ (cc - 1) *
                ((((1:ℝ)/2) ^ (p.1 - (cc - 1)) * ((L : ℝ) ^ 2 * y₀) ^ (p.1 - (cc - 1))) *
                  ((L : ℝ) ^ 2 * y₀) ^ p.2) := by
              refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hXnn _)
              exact mul_le_mul_of_nonneg_right hstep1 (pow_nonneg hYnn _)
          _ = ((L : ℝ) ^ 2 * x₀) ^ (cc - 1) *
                (((1:ℝ)/2) ^ (p.1 - (cc - 1)) *
                  (((L : ℝ) ^ 2 * y₀) ^ (ℓ - cc) *
                    ((L : ℝ) ^ 2 * y₀) ^ (p.1 + p.2 - (ℓ - 1)))) := by
              have hYc : ((L : ℝ) ^ 2 * y₀) ^ (p.1 - (cc - 1)) *
                  ((L : ℝ) ^ 2 * y₀) ^ p.2 =
                  ((L : ℝ) ^ 2 * y₀) ^ (ℓ - cc) *
                    ((L : ℝ) ^ 2 * y₀) ^ (p.1 + p.2 - (ℓ - 1)) := by
                rw [← pow_add, ← pow_add, eb]
              calc ((L : ℝ) ^ 2 * x₀) ^ (cc - 1) *
                    ((((1:ℝ)/2) ^ (p.1 - (cc - 1)) *
                      ((L : ℝ) ^ 2 * y₀) ^ (p.1 - (cc - 1))) *
                      ((L : ℝ) ^ 2 * y₀) ^ p.2)
                  = ((L : ℝ) ^ 2 * x₀) ^ (cc - 1) *
                    (((1:ℝ)/2) ^ (p.1 - (cc - 1)) *
                      (((L : ℝ) ^ 2 * y₀) ^ (p.1 - (cc - 1)) *
                        ((L : ℝ) ^ 2 * y₀) ^ p.2)) := by ring
                _ = _ := by rw [hYc]
          _ ≤ ((L : ℝ) ^ 2 * x₀) ^ (cc - 1) *
                (((1:ℝ)/2) ^ (p.1 - (cc - 1)) *
                  (((L : ℝ) ^ 2 * y₀) ^ (ℓ - cc) *
                    ((1:ℝ)/2) ^ (p.1 + p.2 - (ℓ - 1)))) := by
              refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hXnn _)
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_left hstep2 (pow_nonneg hYnn _)
          _ = ((L : ℝ) ^ 2 * x₀) ^ (cc - 1) * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - cc) *
                (((1:ℝ)/2) ^ (p.1 - (cc - 1)) * ((1:ℝ)/2) ^ (p.1 + p.2 - (ℓ - 1))) := by
              ring
      refine le_trans (Finset.sum_le_sum hper) ?_
      rw [← Finset.mul_sum]
      have hsum4 : (∑ p ∈ P, (((1:ℝ)/2) ^ (p.1 - (cc - 1)) *
          ((1:ℝ)/2) ^ (p.1 + p.2 - (ℓ - 1)))) ≤ 4 := by
        have hinjmap : ∀ p ∈ P, ∀ p' ∈ P,
            (p.1 - (cc - 1), p.1 + p.2 - (ℓ - 1)) =
              (p'.1 - (cc - 1), p'.1 + p'.2 - (ℓ - 1)) → p = p' := by
          intro p hp p' hp' heq
          obtain ⟨k1, k2⟩ := hPmem p hp
          obtain ⟨k3, k4⟩ := hPmem p' hp'
          have m1 := congrArg Prod.fst heq
          have m2 := congrArg Prod.snd heq
          simp only at m1 m2
          refine Prod.ext ?_ ?_ <;> omega
        have himg : (∑ qq ∈ P.image (fun p => (p.1 - (cc - 1), p.1 + p.2 - (ℓ - 1))),
            (((1:ℝ)/2) ^ qq.1 * ((1:ℝ)/2) ^ qq.2)) =
            ∑ p ∈ P, (((1:ℝ)/2) ^ (p.1 - (cc - 1)) *
              ((1:ℝ)/2) ^ (p.1 + p.2 - (ℓ - 1))) :=
          Finset.sum_image hinjmap
        rw [← himg]
        obtain ⟨Q, hQ⟩ : ∃ Q : Finset (ℕ × ℕ),
            Q = P.image (fun p => (p.1 - (cc - 1), p.1 + p.2 - (ℓ - 1))) := ⟨_, rfl⟩
        rw [← hQ]
        obtain ⟨M, hM⟩ : ∃ M : ℕ, M = (Q.sup fun q => max q.1 q.2) + 1 := ⟨_, rfl⟩
        have hQsub : Q ⊆ Finset.range M ×ˢ Finset.range M := by
          intro qq hqq
          have hle : max qq.1 qq.2 ≤ Q.sup fun q => max q.1 q.2 :=
            Finset.le_sup (f := fun q => max q.1 q.2) hqq
          refine Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, Finset.mem_range.2 ?_⟩
          · omega
          · omega
        have hstep := Finset.sum_le_sum_of_subset_of_nonneg hQsub
          (f := fun q : ℕ × ℕ => ((1:ℝ)/2) ^ q.1 * ((1:ℝ)/2) ^ q.2)
          (fun q _ _ => by positivity)
        refine le_trans hstep ?_
        have hprod : (∑ q ∈ Finset.range M ×ˢ Finset.range M,
            (((1:ℝ)/2) ^ q.1 * ((1:ℝ)/2) ^ q.2)) =
            (∑ i ∈ Finset.range M, ((1:ℝ)/2) ^ i) *
              (∑ j ∈ Finset.range M, ((1:ℝ)/2) ^ j) := by
          rw [Finset.sum_product, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
        rw [hprod]
        have hpos : (0:ℝ) ≤ ∑ i ∈ Finset.range M, ((1:ℝ)/2) ^ i :=
          Finset.sum_nonneg fun i _ => by positivity
        nlinarith [hgeom M, hpos]
      calc ((L : ℝ) ^ 2 * x₀) ^ (cc - 1) * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - cc) *
            (∑ p ∈ P, (((1:ℝ)/2) ^ (p.1 - (cc - 1)) *
              ((1:ℝ)/2) ^ (p.1 + p.2 - (ℓ - 1))))
          ≤ ((L : ℝ) ^ 2 * x₀) ^ (cc - 1) * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - cc) * 4 :=
            mul_le_mul_of_nonneg_left hsum4
              (mul_nonneg (pow_nonneg hXnn _) (pow_nonneg hYnn _))
        _ = 4 * (((L : ℝ) ^ 2 * x₀) ^ (cc - 1) * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - cc)) := by ring
    rw [e1]
    calc η ^ L * ∑ Γ ∈ F, (x₀ ^ NA Γ.1 * y₀ ^ NB Γ.1)
        ≤ η ^ L * (4 * (((L : ℝ) ^ 2 * x₀) ^ (cc - 1) * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - cc))) :=
          mul_le_mul_of_nonneg_left hmain (pow_nonneg hη _)
      _ = 4 * (η ^ L * ((L : ℝ) ^ 2 * x₀) ^ (cc - 1) * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - cc)) := by
          ring
  have hpow1 : (1:ℝ) ≤ (ℓ : ℝ) ^ (2 * ℓ) := by
    apply one_le_pow₀
    exact_mod_cast hℓ
  have harith : 4 * (η ^ L * ((L : ℝ) ^ 2 * x₀) ^ (cc - 1) *
      ((L : ℝ) ^ 2 * y₀) ^ (ℓ - cc)) ≤
      4 * (ℓ : ℝ) ^ (2 * ℓ) *
        (η ^ L * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - 1) * (x₀ / y₀) ^ (cc - 1)) := by
    rcases eq_or_lt_of_le hy₀ with hy0 | hy0
    · have hx0 : x₀ = 0 := by linarith
      rcases Nat.lt_or_ge cc 2 with hc | hc
      · have hcc1' : cc - 1 = 0 := by omega
        have hccl : ℓ - cc = ℓ - 1 := by omega
        rw [hcc1', hccl, pow_zero, pow_zero, mul_one, mul_one]
        have hnn : (0:ℝ) ≤ η ^ L * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - 1) :=
          mul_nonneg (pow_nonneg hη _) (pow_nonneg hYnn _)
        nlinarith [hnn, hpow1]
      · have hz : ((L : ℝ) ^ 2 * x₀) ^ (cc - 1) = 0 := by
          rw [hx0, mul_zero]
          exact zero_pow (by omega)
        rw [hz]
        have : (0:ℝ) ≤ 4 * (ℓ : ℝ) ^ (2 * ℓ) *
            (η ^ L * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - 1) * (x₀ / y₀) ^ (cc - 1)) := by
          have h4 : (0:ℝ) ≤ 4 * (ℓ : ℝ) ^ (2 * ℓ) := by positivity
          exact mul_nonneg h4 hCnn
        nlinarith [this]
    · have hkey : ((L : ℝ) ^ 2 * x₀) ^ (cc - 1) * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - cc) =
          ((L : ℝ) ^ 2 * y₀) ^ (ℓ - 1) * (x₀ / y₀) ^ (cc - 1) := by
        rw [div_pow, mul_pow, mul_pow, mul_pow]
        have e3 : (ℓ - 1) = (cc - 1) + (ℓ - cc) := by omega
        rw [e3, pow_add, pow_add]
        field_simp
      rw [mul_assoc, hkey]
      have hnn : (0:ℝ) ≤ η ^ L *
          (((L : ℝ) ^ 2 * y₀) ^ (ℓ - 1) * (x₀ / y₀) ^ (cc - 1)) :=
        mul_nonneg (pow_nonneg hη _) (mul_nonneg (pow_nonneg hYnn _) (pow_nonneg hDnn _))
      nlinarith [hnn, hpow1]
  have hfin : ∀ F : Finset {Γ : mixed_moment_occurrence_configuration ι q r //
      mixed_moment_configuration_admissible I A B rank Γ ∧
      mixed_moment_configuration_connected I Γ},
      ∑ Γ ∈ F, |mixed_moment_configuration_weight I η x₀ y₀ Γ.1| ≤
        4 * (ℓ : ℝ) ^ (2 * ℓ) *
          (η ^ L * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - 1) * (x₀ / y₀) ^ (cc - 1)) :=
    fun F => le_trans (hbound F) harith
  have hkey : |∑' Γ : {Γ : mixed_moment_occurrence_configuration ι q r //
      mixed_moment_configuration_admissible I A B rank Γ ∧
      mixed_moment_configuration_connected I Γ},
      mixed_moment_configuration_weight I η x₀ y₀ Γ.1| ≤
      4 * (ℓ : ℝ) ^ (2 * ℓ) *
        (η ^ L * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - 1) * (x₀ / y₀) ^ (cc - 1)) := by
    by_cases hsum : Summable (fun Γ : {Γ : mixed_moment_occurrence_configuration ι q r //
        mixed_moment_configuration_admissible I A B rank Γ ∧
        mixed_moment_configuration_connected I Γ} =>
        mixed_moment_configuration_weight I η x₀ y₀ Γ.1)
    · have habs := hsum.abs
      have h1 := norm_tsum_le_tsum_norm (f := fun Γ : {Γ :
          mixed_moment_occurrence_configuration ι q r //
          mixed_moment_configuration_admissible I A B rank Γ ∧
          mixed_moment_configuration_connected I Γ} =>
          mixed_moment_configuration_weight I η x₀ y₀ Γ.1)
          (by simpa [Real.norm_eq_abs] using habs)
      rw [Real.norm_eq_abs] at h1
      refine le_trans h1 ?_
      have h2 : (∑' Γ : {Γ : mixed_moment_occurrence_configuration ι q r //
          mixed_moment_configuration_admissible I A B rank Γ ∧
          mixed_moment_configuration_connected I Γ},
          ‖mixed_moment_configuration_weight I η x₀ y₀ Γ.1‖) =
          ∑' Γ : {Γ : mixed_moment_occurrence_configuration ι q r //
          mixed_moment_configuration_admissible I A B rank Γ ∧
          mixed_moment_configuration_connected I Γ},
          |mixed_moment_configuration_weight I η x₀ y₀ Γ.1| := by
        simp [Real.norm_eq_abs]
      rw [h2]
      exact habs.tsum_le_of_sum_le hfin
    · rw [tsum_eq_zero_of_not_summable hsum, abs_zero]
      have h4 : (0:ℝ) ≤ 4 * (ℓ : ℝ) ^ (2 * ℓ) := by positivity
      exact mul_nonneg h4 hCnn
  by_cases hz : (∑' Γ : {Γ : mixed_moment_occurrence_configuration ι q r //
      mixed_moment_configuration_admissible I A B rank Γ ∧
      mixed_moment_configuration_connected I Γ},
      mixed_moment_configuration_weight I η x₀ y₀ Γ.1) = 0
  · refine ⟨0, by rw [hz, mul_zero], ?_⟩
    rw [abs_zero]
    positivity
  · have hCne : (η ^ L * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - 1) * (x₀ / y₀) ^ (cc - 1)) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hkey
      exact hz (abs_eq_zero.1 (le_antisymm hkey (abs_nonneg _)))
    refine ⟨(∑' Γ : {Γ : mixed_moment_occurrence_configuration ι q r //
        mixed_moment_configuration_admissible I A B rank Γ ∧
        mixed_moment_configuration_connected I Γ},
        mixed_moment_configuration_weight I η x₀ y₀ Γ.1) /
        (η ^ L * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - 1) * (x₀ / y₀) ^ (cc - 1)), ?_, ?_⟩
    · exact (mul_div_cancel₀ _ hCne).symm
    · rw [abs_div, div_le_iff₀ (abs_pos.2 hCne)]
      calc |∑' Γ : {Γ : mixed_moment_occurrence_configuration ι q r //
            mixed_moment_configuration_admissible I A B rank Γ ∧
            mixed_moment_configuration_connected I Γ},
            mixed_moment_configuration_weight I η x₀ y₀ Γ.1|
          ≤ 4 * (ℓ : ℝ) ^ (2 * ℓ) *
            (η ^ L * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - 1) * (x₀ / y₀) ^ (cc - 1)) := hkey
        _ = 4 * (ℓ : ℝ) ^ (2 * ℓ) *
            |η ^ L * ((L : ℝ) ^ 2 * y₀) ^ (ℓ - 1) * (x₀ / y₀) ^ (cc - 1)| := by
            rw [abs_of_nonneg hCnn]

@[blueprint "lem:mixed-moment-empty-b-tree-majorant"
  (statement := /-- Under the hypotheses of the empty-$B$ case, fix a rank function $\varrho$ that is injective on $U=I_{[\ell]}$.  The connected admissible configuration sum satisfies
  \[
    \left|\sum_{\Gamma\ {\rm connected}}w(\Gamma)\right|
      \leq2\ell^{2\ell}\eta^L(L^2x_0)^{\ell-1}.
  \]
  The summation retains every word position from \cref{def:mixed-moment-occurrence-configuration}. -/)
  (proof := /-- If $\ell=1$, there is no tree edge and the assertion follows by summing the unmarked words.  Suppose $\ell\geq2$.  Every connected configuration has a spanning tree.  For an upper bound, sum over all labelled trees and mark, for each tree edge, an occurrence witnessing that edge.  There are $\ell^{\ell-2}$ trees and at most $L^2$ ordered witness pairs for each edge.

  Marks are positions in lists, not merely predecessor values.  If $m$ positions are marked in a word with $k$ possible predecessors, then the sum over every residual word and every placement of those marks is
  \[
    \sum_{n\geq m}\binom{n}{m}k^{n-m}x_0^n
      =\frac{x_0^m}{(1-kx_0)^{m+1}}.
  \]
  This identity follows by differentiating the geometric series $m$ times and dividing by $m!$; it explicitly accounts for the insertion positions omitted by the naive deletion map.  Multiplication over all words shows that, after extracting $x_0^{\ell-1}$ for the tree marks, the residual mass is at most
  \[
    (1-Lx_0)^{-(L+\ell-1)}.
  \]
  If a connected configuration exists, every vertex has nonempty $I_t$, whence $L\geq\ell$.  The smallness assumption gives $Lx_0\leq1/(2L)$, and therefore
  \[
    (1-Lx_0)^{-(L+\ell-1)}
      \leq\left(1-\frac1{2L}\right)^{-(2L-1)}<4.
  \]
  Consequently the total is bounded by
  $4\ell^{\ell-2}\eta^L(L^2x_0)^{\ell-1}$.  For every $\ell\geq2$,
  $4\ell^{\ell-2}\leq2\ell^{2\ell}$, which proves the asserted constant.  Configurations cannot be connected when some $I_t$ is empty and $\ell\geq2$, so that remaining case contributes zero. -/)
  (title := /-- Position-preserving tree majorant in the empty-$B$ case -/)
  (latexEnv := "lemma")]
lemma mixed_moment_empty_b_tree_majorant
    {ι : Type*} [DecidableEq ι] {ℓ q r : ℕ}
    (I : Fin ℓ → Finset ι) (A : Fin q → Finset ι)
    (B : Fin r → Finset ι) (η x₀ y₀ : ℝ) (rank : ι → ℕ)
    (hI : Set.univ.PairwiseDisjoint I)
    (hA : Set.univ.PairwiseDisjoint A)
    (hB : Set.univ.PairwiseDisjoint B)
    (hℓ : 0 < ℓ) (hη : 0 ≤ η) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀)
    (hr : r = 0)
    (hsmall : 2 * (total_index_count I : ℝ) ^ 2 * x₀ ≤ 1)
    (hrank : Set.InjOn rank (indexed_union I Finset.univ : Set ι)) :
    |∑' Γ :
      {Γ : mixed_moment_occurrence_configuration ι q r //
        mixed_moment_configuration_admissible I A B rank Γ ∧
        mixed_moment_configuration_connected I Γ},
      mixed_moment_configuration_weight I η x₀ y₀ Γ.1| ≤
      2 * (ℓ : ℝ) ^ (2 * ℓ) * η ^ total_index_count I *
        ((total_index_count I : ℝ) ^ 2 * x₀) ^ (ℓ - 1) := by
  classical
  subst hr
  have hw : ∀ Γ : mixed_moment_occurrence_configuration ι q 0,
      mixed_moment_configuration_weight I η x₀ y₀ Γ =
        η ^ total_index_count I *
          x₀ ^ (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
            (Γ.aWords j u).length) := by
    intro Γ
    simp [mixed_moment_configuration_weight]
  have hterm : ∀ Γ : {Γ : mixed_moment_occurrence_configuration ι q 0 //
      mixed_moment_configuration_admissible I A B rank Γ ∧
      mixed_moment_configuration_connected I Γ},
      0 ≤ mixed_moment_configuration_weight I η x₀ y₀ Γ.1 := by
    intro Γ
    rw [hw]
    exact mul_nonneg (pow_nonneg hη _) (pow_nonneg hx₀ _)
  have hRHS : (0:ℝ) ≤ 2 * (ℓ : ℝ) ^ (2 * ℓ) * η ^ total_index_count I *
      ((total_index_count I : ℝ) ^ 2 * x₀) ^ (ℓ - 1) := by
    have : (0:ℝ) ≤ (total_index_count I : ℝ) ^ 2 * x₀ := by positivity
    positivity
  rw [abs_of_nonneg (tsum_nonneg hterm)]
  refine tsum_le_of_sum_le' hRHS ?_
  intro F
  have hmain : ∑ Γ ∈ F, x₀ ^ (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
      ((Γ : mixed_moment_occurrence_configuration ι q 0).aWords j u).length) ≤
      2 * ((total_index_count I : ℝ) ^ 2 * x₀) ^ (ℓ - 1) := by
    have hA0 : (0:ℝ) ≤ (total_index_count I : ℝ) ^ 2 * x₀ := by positivity
    have hAhalf : (total_index_count I : ℝ) ^ 2 * x₀ ≤ 1/2 := by linarith
    have hNge : ∀ Γ ∈ F, ℓ - 1 ≤ ∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
        ((Γ : mixed_moment_occurrence_configuration ι q 0).aWords j u).length := by
      intro Γ hΓF
      have htall : ∀ u : ι, ∃ t : Fin ℓ, u ∈ indexed_union I Finset.univ → u ∈ I t := by
        intro u
        by_cases hu : u ∈ indexed_union I Finset.univ
        · obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.1 hu
          exact ⟨t, fun _ => ht⟩
        · exact ⟨⟨0, hℓ⟩, fun h => absurd h hu⟩
      choose tt htt using htall
      have hmemU : ∀ (u : ι) (t : Fin ℓ), u ∈ I t → u ∈ indexed_union I Finset.univ := by
        intro u t ht
        exact Finset.mem_biUnion.2 ⟨t, Finset.mem_univ t, ht⟩
      have htuniq : ∀ (u : ι) (t : Fin ℓ), u ∈ I t → tt u = t := by
        intro u t hut
        by_contra hne
        exact Finset.disjoint_left.1 (hI (Set.mem_univ (tt u)) (Set.mem_univ t) hne)
          (htt u (hmemU u t hut)) hut
      have hconn : (SimpleGraph.fromRel fun t t' : Fin ℓ =>
          ∃ u ∈ I t, ∃ v ∈ I t',
            (∃ j : Fin q,
              v ∈ (Γ : mixed_moment_occurrence_configuration ι q 0).aWords j u) ∨
            ∃ i : Fin 0,
              (Γ : mixed_moment_occurrence_configuration ι q 0).bChoice i u
                = some v).Connected := Γ.2.2
      have hcard := hconn.card_vert_le_card_edgeSet_add_one
      have hsub : (SimpleGraph.fromRel fun t t' : Fin ℓ =>
          ∃ u ∈ I t, ∃ v ∈ I t',
            (∃ j : Fin q,
              v ∈ (Γ : mixed_moment_occurrence_configuration ι q 0).aWords j u) ∨
            ∃ i : Fin 0,
              (Γ : mixed_moment_occurrence_configuration ι q 0).bChoice i u
                = some v).edgeSet ⊆
          ↑((((indexed_union I Finset.univ) ×ˢ (indexed_union I Finset.univ)).filter
            (fun p => ∃ j : Fin q,
              p.2 ∈ (Γ : mixed_moment_occurrence_configuration ι q 0).aWords j p.1)).image
              (fun p : ι × ι => s(tt p.1, tt p.2))) := by
        intro e he
        induction e using Sym2.ind with
        | _ t t' =>
          rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at he
          have hgen : ∀ a b : Fin ℓ, (∃ u ∈ I a, ∃ v ∈ I b,
              (∃ j : Fin q,
                v ∈ (Γ : mixed_moment_occurrence_configuration ι q 0).aWords j u) ∨
              ∃ i : Fin 0,
                (Γ : mixed_moment_occurrence_configuration ι q 0).bChoice i u = some v) →
              s(a, b) ∈ ((((indexed_union I Finset.univ) ×ˢ
                (indexed_union I Finset.univ)).filter
                (fun p => ∃ j : Fin q,
                  p.2 ∈ (Γ : mixed_moment_occurrence_configuration ι q 0).aWords j p.1)).image
                  (fun p : ι × ι => s(tt p.1, tt p.2))) := by
            intro a b hab
            obtain ⟨u, hu, v, hv, hjw⟩ := hab
            have hjw' : ∃ j : Fin q,
                v ∈ (Γ : mixed_moment_occurrence_configuration ι q 0).aWords j u := by
              rcases hjw with h | ⟨i, -⟩
              · exact h
              · exact i.elim0
            refine Finset.mem_image.2 ⟨(u, v), Finset.mem_filter.2
              ⟨Finset.mk_mem_product (hmemU u a hu) (hmemU v b hv), hjw'⟩, ?_⟩
            rw [htuniq u a hu, htuniq v b hv]
          rcases he.2 with h | h
          · exact hgen t t' h
          · have := hgen t' t h
            rwa [Sym2.eq_swap] at this
      have hEcard : Nat.card (SimpleGraph.fromRel fun t t' : Fin ℓ =>
          ∃ u ∈ I t, ∃ v ∈ I t',
            (∃ j : Fin q,
              v ∈ (Γ : mixed_moment_occurrence_configuration ι q 0).aWords j u) ∨
            ∃ i : Fin 0,
              (Γ : mixed_moment_occurrence_configuration ι q 0).bChoice i u
                = some v).edgeSet ≤
          ((((indexed_union I Finset.univ) ×ˢ (indexed_union I Finset.univ)).filter
            (fun p => ∃ j : Fin q,
              p.2 ∈ (Γ : mixed_moment_occurrence_configuration ι q 0).aWords j p.1)).image
              (fun p : ι × ι => s(tt p.1, tt p.2))).card := by
        rw [Nat.card_coe_set_eq]
        calc (SimpleGraph.fromRel fun t t' : Fin ℓ =>
              ∃ u ∈ I t, ∃ v ∈ I t',
                (∃ j : Fin q,
                  v ∈ (Γ : mixed_moment_occurrence_configuration ι q 0).aWords j u) ∨
                ∃ i : Fin 0,
                  (Γ : mixed_moment_occurrence_configuration ι q 0).bChoice i u
                    = some v).edgeSet.ncard
              ≤ ((((((indexed_union I Finset.univ) ×ˢ (indexed_union I Finset.univ)).filter
                (fun p => ∃ j : Fin q,
                  p.2 ∈
                    (Γ : mixed_moment_occurrence_configuration ι q 0).aWords j p.1)).image
                  (fun p : ι × ι => s(tt p.1, tt p.2)))) : Set (Sym2 (Fin ℓ))).ncard :=
              Set.ncard_le_ncard hsub (Finset.finite_toSet _)
          _ = _ := Set.ncard_coe_finset _
      have hPcard : ((((indexed_union I Finset.univ) ×ˢ (indexed_union I Finset.univ)).filter
          (fun p => ∃ j : Fin q,
            p.2 ∈ (Γ : mixed_moment_occurrence_configuration ι q 0).aWords j p.1))).card ≤
          ∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
            ((Γ : mixed_moment_occurrence_configuration ι q 0).aWords j u).length := by
        have hPsub : ((((indexed_union I Finset.univ) ×ˢ
            (indexed_union I Finset.univ)).filter
            (fun p => ∃ j : Fin q,
              p.2 ∈ (Γ : mixed_moment_occurrence_configuration ι q 0).aWords j p.1))) ⊆
            (indexed_union I Finset.univ).biUnion (fun u =>
              (Finset.univ : Finset (Fin q)).biUnion (fun j =>
                ((Γ : mixed_moment_occurrence_configuration ι q 0).aWords j u).toFinset.image
                  (fun v => (u, v)))) := by
          intro p hp
          obtain ⟨hmem, j, hj⟩ := Finset.mem_filter.1 hp
          refine Finset.mem_biUnion.2 ⟨p.1, (Finset.mem_product.1 hmem).1, ?_⟩
          refine Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, ?_⟩
          exact Finset.mem_image.2 ⟨p.2, List.mem_toFinset.2 hj, rfl⟩
        calc ((((indexed_union I Finset.univ) ×ˢ (indexed_union I Finset.univ)).filter
              (fun p => ∃ j : Fin q,
                p.2 ∈
                  (Γ : mixed_moment_occurrence_configuration ι q 0).aWords j p.1))).card
            ≤ ((indexed_union I Finset.univ).biUnion (fun u =>
                (Finset.univ : Finset (Fin q)).biUnion (fun j =>
                  ((Γ : mixed_moment_occurrence_configuration ι q 0).aWords j u).toFinset.image
                    (fun v => (u, v))))).card := Finset.card_le_card hPsub
          _ ≤ ∑ u ∈ indexed_union I Finset.univ,
              ((Finset.univ : Finset (Fin q)).biUnion (fun j =>
                ((Γ : mixed_moment_occurrence_configuration ι q 0).aWords j u).toFinset.image
                  (fun v => (u, v)))).card := Finset.card_biUnion_le
          _ ≤ ∑ u ∈ indexed_union I Finset.univ, ∑ j : Fin q,
              ((Γ : mixed_moment_occurrence_configuration ι q 0).aWords j u).length := by
              refine Finset.sum_le_sum fun u _ => ?_
              refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun j _ => ?_)
              exact le_trans Finset.card_image_le (List.toFinset_card_le _)
          _ = ∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
              ((Γ : mixed_moment_occurrence_configuration ι q 0).aWords j u).length :=
              Finset.sum_comm
      have hℓcard : Nat.card (Fin ℓ) = ℓ := by simp
      have hIm : ((((indexed_union I Finset.univ) ×ˢ (indexed_union I Finset.univ)).filter
          (fun p => ∃ j : Fin q,
            p.2 ∈ (Γ : mixed_moment_occurrence_configuration ι q 0).aWords j p.1)).image
            (fun p : ι × ι => s(tt p.1, tt p.2))).card ≤
          ((((indexed_union I Finset.univ) ×ˢ (indexed_union I Finset.univ)).filter
            (fun p => ∃ j : Fin q,
              p.2 ∈
                (Γ : mixed_moment_occurrence_configuration ι q 0).aWords j p.1))).card :=
        Finset.card_image_le
      rw [hℓcard] at hcard
      omega
    have hext : ∀ Γ₁ Γ₂ : mixed_moment_occurrence_configuration ι q 0,
        (∀ j u, Γ₁.aWords j u = Γ₂.aWords j u) → Γ₁ = Γ₂ := by
      intro Γ₁ Γ₂ h
      obtain ⟨a1, b1⟩ := Γ₁
      obtain ⟨a2, b2⟩ := Γ₂
      have ha : a1 = a2 := funext fun j => funext fun u => h j u
      have hb : b1 = b2 := funext fun i => i.elim0
      rw [ha, hb]
    have hcount : ∀ (n : ℕ) (G : Finset (mixed_moment_occurrence_configuration ι q 0)),
        (∀ Γ ∈ G, mixed_moment_configuration_admissible I A B rank Γ ∧
          (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
            (Γ.aWords j u).length) = n) →
        G.card ≤ (total_index_count I ^ 2) ^ n := by
      intro n
      induction n with
      | zero =>
        intro G hG
        rw [pow_zero]
        refine Finset.card_le_one.2 ?_
        intro Γ₁ h1 Γ₂ h2
        have key : ∀ Γ, Γ ∈ G → ∀ j u, Γ.aWords j u = [] := by
          intro Γ hΓ j u
          by_cases huU : u ∈ indexed_union I Finset.univ
          · have hsum := (hG Γ hΓ).2
            have hj : ∑ u ∈ indexed_union I Finset.univ, (Γ.aWords j u).length = 0 :=
              Finset.sum_eq_zero_iff.1 hsum j (Finset.mem_univ j)
            exact List.length_eq_zero_iff.1 (Finset.sum_eq_zero_iff.1 hj u huU)
          · exact (hG Γ hΓ).1.2.1 j u (fun hmem => huU (Finset.mem_inter.1 hmem).1)
        exact hext Γ₁ Γ₂ (fun j u => by rw [key Γ₁ h1 j u, key Γ₂ h2 j u])
      | succ n ih =>
        intro G hG
        rcases Finset.eq_empty_or_nonempty (indexed_union I Finset.univ) with hUe | hUne
        · have hGe : G = ∅ := by
            refine Finset.eq_empty_of_forall_notMem ?_
            intro Γ hΓ
            have h2 := (hG Γ hΓ).2
            rw [hUe] at h2
            simp at h2
          rw [hGe]
          simp
        obtain ⟨ustar, hustar⟩ := hUne
        have hex : ∀ Γ : mixed_moment_occurrence_configuration ι q 0,
            ∃ (u₀ v₀ : ι) (Γ' : mixed_moment_occurrence_configuration ι q 0),
              mixed_moment_configuration_admissible I A B rank Γ →
              (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
                (Γ.aWords j u).length) = n + 1 →
                u₀ ∈ indexed_union I Finset.univ ∧
                v₀ ∈ indexed_union I Finset.univ ∧
                mixed_moment_configuration_admissible I A B rank Γ' ∧
                (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
                  (Γ'.aWords j u).length) = n ∧
                ∃ j₀ : Fin q, ∀ j u, Γ.aWords j u =
                  if j = j₀ ∧ u = u₀ then v₀ :: Γ'.aWords j u else Γ'.aWords j u := by
          intro Γ
          by_cases hgood : mixed_moment_configuration_admissible I A B rank Γ ∧
              (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
                (Γ.aWords j u).length) = n + 1
          · obtain ⟨hadm, hN⟩ := hgood
            have hne : (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
                (Γ.aWords j u).length) ≠ 0 := by
              rw [hN]
              omega
            obtain ⟨j₀, -, hj₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
            obtain ⟨u₀, hu₀U, hu₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj₀
            have hwne : Γ.aWords j₀ u₀ ≠ [] := by
              intro h
              rw [h] at hu₀
              exact hu₀ rfl
            obtain ⟨v₀, w, hword⟩ := List.exists_cons_of_ne_nil hwne
            have hmemv : v₀ ∈ Γ.aWords j₀ u₀ := by
              rw [hword]
              exact List.mem_cons_self
            have hadm3 := hadm.2.2.1 j₀ u₀ v₀ hmemv
            obtain ⟨Γ', hΓ'w, hΓ'b⟩ :
                ∃ Γ' : mixed_moment_occurrence_configuration ι q 0,
                  (∀ j u, Γ'.aWords j u =
                    if j = j₀ ∧ u = u₀ then w else Γ.aWords j u) ∧
                  Γ'.bChoice = Γ.bChoice :=
              ⟨⟨fun j u => if j = j₀ ∧ u = u₀ then w else Γ.aWords j u, Γ.bChoice⟩,
                fun j u => rfl, rfl⟩
            have hkey1 : (∑ u ∈ indexed_union I Finset.univ,
                (Γ'.aWords j₀ u).length) + 1 =
                ∑ u ∈ indexed_union I Finset.univ, (Γ.aWords j₀ u).length := by
              rw [← Finset.add_sum_erase (indexed_union I Finset.univ)
                  (fun u => (Γ'.aWords j₀ u).length) hu₀U,
                ← Finset.add_sum_erase (indexed_union I Finset.univ)
                  (fun u => (Γ.aWords j₀ u).length) hu₀U]
              have e0 : (Γ'.aWords j₀ u₀).length + 1 = (Γ.aWords j₀ u₀).length := by
                rw [hΓ'w, if_pos ⟨rfl, rfl⟩, hword]
                simp
              have e1 : (∑ u ∈ (indexed_union I Finset.univ).erase u₀,
                  (Γ'.aWords j₀ u).length) =
                  ∑ u ∈ (indexed_union I Finset.univ).erase u₀,
                    (Γ.aWords j₀ u).length := by
                refine Finset.sum_congr rfl fun u hu => ?_
                rw [hΓ'w, if_neg (fun hc => (Finset.mem_erase.1 hu).1 hc.2)]
              omega
            have hkey2 : ∀ j ∈ (Finset.univ : Finset (Fin q)).erase j₀,
                (∑ u ∈ indexed_union I Finset.univ, (Γ'.aWords j u).length) =
                ∑ u ∈ indexed_union I Finset.univ, (Γ.aWords j u).length := by
              intro j hj
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [hΓ'w, if_neg (fun hc => (Finset.mem_erase.1 hj).1 hc.1)]
            have hkey3 : (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
                (Γ'.aWords j u).length) + 1 =
                ∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
                  (Γ.aWords j u).length := by
              rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin q))
                  (fun j => ∑ u ∈ indexed_union I Finset.univ,
                    (Γ'.aWords j u).length) (Finset.mem_univ j₀),
                ← Finset.add_sum_erase (Finset.univ : Finset (Fin q))
                  (fun j => ∑ u ∈ indexed_union I Finset.univ,
                    (Γ.aWords j u).length) (Finset.mem_univ j₀),
                Finset.sum_congr rfl hkey2]
              omega
            refine ⟨u₀, v₀, Γ', fun _ _ =>
              ⟨hu₀U, (Finset.mem_inter.1 hadm3.2.1).1, ?_, by omega, ⟨j₀, ?_⟩⟩⟩
            · refine ⟨hadm.1, ?_, ?_, ?_⟩
              · intro j u hu
                by_cases hc : j = j₀ ∧ u = u₀
                · exact absurd (by rw [hc.1, hc.2]; exact hadm3.1) hu
                · rw [hΓ'w, if_neg hc]
                  exact hadm.2.1 j u hu
              · intro j u v hv
                rw [hΓ'w] at hv
                by_cases hc : j = j₀ ∧ u = u₀
                · rw [if_pos hc] at hv
                  rw [hc.1, hc.2]
                  refine hadm.2.2.1 j₀ u₀ v ?_
                  rw [hword]
                  exact List.mem_cons_of_mem _ hv
                · rw [if_neg hc] at hv
                  exact hadm.2.2.1 j u v hv
              · intro i u v hiv
                rw [hΓ'b] at hiv
                exact hadm.2.2.2 i u v hiv
            · intro j u
              by_cases hc : j = j₀ ∧ u = u₀
              · rw [if_pos hc, hΓ'w, if_pos hc, hc.1, hc.2, hword]
              · rw [if_neg hc, hΓ'w, if_neg hc]
          · exact ⟨ustar, ustar, Γ, fun h1 h2 => absurd ⟨h1, h2⟩ hgood⟩
        choose uu vv PP hPP using hex
        have hmaps : ∀ Γ ∈ G, ((uu Γ, vv Γ), PP Γ) ∈
            ((indexed_union I Finset.univ) ×ˢ (indexed_union I Finset.univ)) ×ˢ G.image PP := by
          intro Γ hΓ
          obtain ⟨h1, h2, h3, h4, h5⟩ := hPP Γ (hG Γ hΓ).1 (hG Γ hΓ).2
          exact Finset.mk_mem_product (Finset.mk_mem_product h1 h2)
            (Finset.mem_image_of_mem _ hΓ)
        have hinj : Set.InjOn (fun Γ => ((uu Γ, vv Γ), PP Γ)) G := by
          intro Γ₁ h1 Γ₂ h2 heq
          obtain ⟨p1, p2, p3, p4, j₁, p5⟩ := hPP Γ₁ (hG Γ₁ h1).1 (hG Γ₁ h1).2
          obtain ⟨r1, r2, r3, r4, j₂, r5⟩ := hPP Γ₂ (hG Γ₂ h2).1 (hG Γ₂ h2).2
          have hu : uu Γ₁ = uu Γ₂ := congrArg (fun x => x.1.1) heq
          have hv : vv Γ₁ = vv Γ₂ := congrArg (fun x => x.1.2) heq
          have hP : PP Γ₁ = PP Γ₂ := congrArg (fun x => x.2) heq
          have hj : j₁ = j₂ := by
            have m1 : vv Γ₁ ∈ Γ₁.aWords j₁ (uu Γ₁) := by
              rw [p5 j₁ (uu Γ₁), if_pos ⟨rfl, rfl⟩]
              exact List.mem_cons_self
            have m2 : vv Γ₂ ∈ Γ₂.aWords j₂ (uu Γ₂) := by
              rw [r5 j₂ (uu Γ₂), if_pos ⟨rfl, rfl⟩]
              exact List.mem_cons_self
            have a1 := ((hG Γ₁ h1).1.2.2.1 j₁ (uu Γ₁) (vv Γ₁) m1).1
            have a2 := ((hG Γ₂ h2).1.2.2.1 j₂ (uu Γ₂) (vv Γ₂) m2).1
            by_contra hne
            have hd : Disjoint (A j₁) (A j₂) := hA (Set.mem_univ j₁) (Set.mem_univ j₂) hne
            have m1' : uu Γ₁ ∈ A j₁ := (Finset.mem_inter.1 a1).2
            have m2' : uu Γ₁ ∈ A j₂ := by
              rw [hu]
              exact (Finset.mem_inter.1 a2).2
            exact Finset.disjoint_left.1 hd m1' m2'
          refine hext Γ₁ Γ₂ ?_
          intro j u
          rw [p5 j u, r5 j u, hu, hv, hP, hj]
        calc G.card ≤ (((indexed_union I Finset.univ) ×ˢ
              (indexed_union I Finset.univ)) ×ˢ G.image PP).card :=
              Finset.card_le_card_of_injOn _ hmaps hinj
          _ = (total_index_count I * total_index_count I) * (G.image PP).card := by
              rw [Finset.card_product, Finset.card_product]
              rfl
          _ ≤ (total_index_count I * total_index_count I) *
              (total_index_count I ^ 2) ^ n := by
              refine Nat.mul_le_mul_left _ (ih _ ?_)
              intro Γ hΓ
              obtain ⟨Γ₀, hΓ₀, rfl⟩ := Finset.mem_image.1 hΓ
              obtain ⟨p1, p2, p3, p4, -⟩ := hPP Γ₀ (hG Γ₀ hΓ₀).1 (hG Γ₀ hΓ₀).2
              exact ⟨p3, p4⟩
          _ = (total_index_count I ^ 2) ^ (n + 1) := by ring
    have hgeom : ∀ k : ℕ, ∑ i ∈ Finset.range k,
        ((total_index_count I : ℝ) ^ 2 * x₀) ^ i ≤ 2 := by
      intro k
      have h := geom_sum_mul ((total_index_count I : ℝ) ^ 2 * x₀) k
      have hs : (0:ℝ) ≤ ∑ i ∈ Finset.range k,
          ((total_index_count I : ℝ) ^ 2 * x₀) ^ i :=
        Finset.sum_nonneg fun i _ => pow_nonneg hA0 i
      have hAk : (0:ℝ) ≤ ((total_index_count I : ℝ) ^ 2 * x₀) ^ k := pow_nonneg hA0 k
      nlinarith [h, hs, hAk, hAhalf]
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun Γ : {Γ : mixed_moment_occurrence_configuration ι q 0 //
          mixed_moment_configuration_admissible I A B rank Γ ∧
          mixed_moment_configuration_connected I Γ} =>
        ∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ, (Γ.1.aWords j u).length)
      (t := F.image (fun Γ => ∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
        (Γ.1.aWords j u).length))
      (fun Γ hΓ => Finset.mem_image_of_mem _ hΓ)]
    have hinner : ∀ n ∈ F.image (fun Γ => ∑ j : Fin q,
        ∑ u ∈ indexed_union I Finset.univ, (Γ.1.aWords j u).length),
        (∑ Γ ∈ F.filter (fun Γ => (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
          (Γ.1.aWords j u).length) = n),
          x₀ ^ (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
            (Γ.1.aWords j u).length)) ≤
          ((total_index_count I : ℝ) ^ 2 * x₀) ^ n := by
      intro n _
      have h1 : ∀ Γ ∈ F.filter (fun Γ => (∑ j : Fin q,
          ∑ u ∈ indexed_union I Finset.univ, (Γ.1.aWords j u).length) = n),
          x₀ ^ (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
            (Γ.1.aWords j u).length) = x₀ ^ n := by
        intro Γ hΓ
        rw [(Finset.mem_filter.1 hΓ).2]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
      have hcard : (F.filter (fun Γ => (∑ j : Fin q,
          ∑ u ∈ indexed_union I Finset.univ, (Γ.1.aWords j u).length) = n)).card ≤
          (total_index_count I ^ 2) ^ n := by
        have himg := hcount n ((F.filter (fun Γ => (∑ j : Fin q,
          ∑ u ∈ indexed_union I Finset.univ, (Γ.1.aWords j u).length) = n)).image
            (fun Γ => Γ.1)) ?_
        · rwa [Finset.card_image_of_injective _ Subtype.val_injective] at himg
        · intro Γ hΓ
          obtain ⟨Γ', hΓ', rfl⟩ := Finset.mem_image.1 hΓ
          exact ⟨Γ'.2.1, (Finset.mem_filter.1 hΓ').2⟩
      have hcast : ((F.filter (fun Γ => (∑ j : Fin q,
          ∑ u ∈ indexed_union I Finset.univ, (Γ.1.aWords j u).length) = n)).card : ℝ) ≤
          ((total_index_count I : ℝ) ^ 2) ^ n := by
        have : ((total_index_count I ^ 2 : ℕ) ^ n : ℝ) = ((total_index_count I : ℝ) ^ 2) ^ n := by
          push_cast
          ring
        rw [← this]
        exact_mod_cast hcard
      calc ((F.filter (fun Γ => (∑ j : Fin q,
              ∑ u ∈ indexed_union I Finset.univ, (Γ.1.aWords j u).length) = n)).card : ℝ)
            * x₀ ^ n
          ≤ ((total_index_count I : ℝ) ^ 2) ^ n * x₀ ^ n :=
            mul_le_mul_of_nonneg_right hcast (pow_nonneg hx₀ n)
        _ = ((total_index_count I : ℝ) ^ 2 * x₀) ^ n := by rw [mul_pow]
    refine le_trans (Finset.sum_le_sum hinner) ?_
    have hsub : F.image (fun Γ => ∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
        (Γ.1.aWords j u).length) ⊆
        Finset.Ico (ℓ - 1) ((F.image (fun Γ => ∑ j : Fin q,
          ∑ u ∈ indexed_union I Finset.univ, (Γ.1.aWords j u).length)).sup id + 1) := by
      intro n hn
      obtain ⟨Γ, hΓ, hΓn⟩ := Finset.mem_image.1 hn
      refine Finset.mem_Ico.2 ⟨hΓn ▸ hNge Γ hΓ, Nat.lt_succ_of_le ?_⟩
      exact Finset.le_sup (f := id) hn
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => pow_nonneg hA0 i)) ?_
    rw [Finset.sum_Ico_eq_sum_range]
    have hsplit : ∀ i ∈ Finset.range ((F.image (fun Γ => ∑ j : Fin q,
        ∑ u ∈ indexed_union I Finset.univ, (Γ.1.aWords j u).length)).sup id + 1 - (ℓ - 1)),
        ((total_index_count I : ℝ) ^ 2 * x₀) ^ (ℓ - 1 + i) =
          ((total_index_count I : ℝ) ^ 2 * x₀) ^ (ℓ - 1) *
            ((total_index_count I : ℝ) ^ 2 * x₀) ^ i := by
      intro i _
      rw [pow_add]
    rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum, mul_comm]
    exact mul_le_mul_of_nonneg_right (hgeom _) (pow_nonneg hA0 _)
  have hstep : ∑ Γ ∈ F, mixed_moment_configuration_weight I η x₀ y₀ Γ.1 =
      η ^ total_index_count I *
        ∑ Γ ∈ F, x₀ ^ (∑ j : Fin q, ∑ u ∈ indexed_union I Finset.univ,
          ((Γ : mixed_moment_occurrence_configuration ι q 0).aWords j u).length) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun Γ _ => hw Γ.1
  rw [hstep]
  have hpow : (1:ℝ) ≤ (ℓ : ℝ) ^ (2 * ℓ) := by
    apply one_le_pow₀
    exact_mod_cast hℓ
  have hA0 : (0:ℝ) ≤ ((total_index_count I : ℝ) ^ 2 * x₀) ^ (ℓ - 1) := by positivity
  calc η ^ total_index_count I * ∑ Γ ∈ F, x₀ ^ (∑ j : Fin q,
        ∑ u ∈ indexed_union I Finset.univ,
        ((Γ : mixed_moment_occurrence_configuration ι q 0).aWords j u).length)
      ≤ η ^ total_index_count I *
        (2 * ((total_index_count I : ℝ) ^ 2 * x₀) ^ (ℓ - 1)) := by
        exact mul_le_mul_of_nonneg_left hmain (pow_nonneg hη _)
    _ ≤ 2 * (ℓ : ℝ) ^ (2 * ℓ) * η ^ total_index_count I *
        ((total_index_count I : ℝ) ^ 2 * x₀) ^ (ℓ - 1) := by
        have := pow_nonneg hη (total_index_count I)
        nlinarith [mul_nonneg (pow_nonneg hη (total_index_count I)) hA0]

@[blueprint "lem:mixed-moment-connected-cluster-cancellation"
  (statement := /-- Let $\ell,q,r\in\mathbb N$ with $\ell\geq1$ and $r\geq1$, let $I$, $A$, and $B$ be finite-set families indexed by $[\ell]$, $[q]$, and $[r]$, respectively, and suppose that the sets within each family are pairwise disjoint.  Let $\eta,x_0,y_0\geq0$.  Put $L=|I_{[\ell]}|$, let $M$ be the function of \cref{def:mixed-moment-right-hand-side}, and let $c$ be the number of components of the graph in \cref{def:intersection-component-count}.  If $2L^2y_0\leq1$ and $2x_0\leq y_0$, then there is a real number $R$ such that
  \[
  \sum_{\pi\in\Pi([\ell])}(-1)^{|\pi|-1}(|\pi|-1)!
    \prod_{C\in\pi}M(C)
  =\eta^L(L^2y_0)^{\ell-1}
    \left(\frac{x_0}{y_0}\right)^{c-1}R
  \]
  and $|R|\leq4\ell^{2\ell}$. -/)
  (proof := /-- The smallness and comparison hypotheses imply $Lx_0<1$, including the degenerate case $L=0$.  Apply \cref{lem:mixed-moment-configuration-expansion} to obtain a rank function and to identify the partition sum with the absolutely convergent sum of connected admissible configurations.  For this rank function, \cref{lem:mixed-moment-positive-b-tree-majorant} factors that connected sum as
  \[
    \eta^L(L^2y_0)^{\ell-1}
      (x_0/y_0)^{cc(\mathcal B)-1}R
  \]
  with $|R|\leq4\ell^{2\ell}$.  Substitution of the connected-configuration expansion gives the asserted equality and bound. -/)
  (title := /-- Connected-cluster cancellation for the mixed-moment partition sum -/)
  (latexEnv := "lemma")]
lemma mixed_moment_connected_cluster_cancellation
    {ι : Type*} [DecidableEq ι] {ℓ q r : ℕ}
    (I : Fin ℓ → Finset ι) (A : Fin q → Finset ι)
    (B : Fin r → Finset ι) (η x₀ y₀ : ℝ)
    (hI : Set.univ.PairwiseDisjoint I)
    (hA : Set.univ.PairwiseDisjoint A)
    (hB : Set.univ.PairwiseDisjoint B)
    (hℓ : 0 < ℓ) (hη : 0 ≤ η) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀)
    (hr : 1 ≤ r)
    (hsmall : 2 * (total_index_count I : ℝ) ^ 2 * y₀ ≤ 1)
    (hxy : 2 * x₀ ≤ y₀) :
    ∃ R : ℝ,
      (∑ π : Finpartition (Finset.univ : Finset (Fin ℓ)),
        ((-1 : ℝ) ^ (π.parts.card - 1)) *
          (Nat.factorial (π.parts.card - 1) : ℝ) *
          ∏ C ∈ π.parts, mixed_moment_right_hand_side I A B η x₀ y₀ C) =
        η ^ total_index_count I *
          ((total_index_count I : ℝ) ^ 2 * y₀) ^ (ℓ - 1) *
          (x₀ / y₀) ^ (intersection_component_count I B - 1) * R ∧
      |R| ≤ 4 * (ℓ : ℝ) ^ (2 * ℓ) := by
  have hL : (0 : ℝ) ≤ (total_index_count I : ℝ) := Nat.cast_nonneg _
  have hconv : (total_index_count I : ℝ) * x₀ < 1 := by
    rcases Nat.eq_zero_or_pos (total_index_count I) with h | h
    · rw [h]
      norm_num
    · have h1 : (1 : ℝ) ≤ (total_index_count I : ℝ) := by
        exact_mod_cast h
      nlinarith [mul_nonneg hL (sub_nonneg.2 hxy),
        mul_nonneg (mul_nonneg hL (sub_nonneg.2 h1)) hy₀]
  obtain ⟨rank, hrank, hsummable, hexp⟩ :=
    mixed_moment_configuration_expansion I A B η x₀ y₀ hI hA hB hℓ hη hx₀ hy₀ hconv
  obtain ⟨R, hR, hRbound⟩ :=
    mixed_moment_positive_b_tree_majorant I A B η x₀ y₀ rank hI hA hB hℓ hη hx₀ hy₀
      hr hsmall hxy hrank
  exact ⟨R, by rw [hexp, hR], hRbound⟩

@[blueprint "lem:mixed-moment-cluster-majorant"
  (statement := /-- Under the hypotheses of \cref{lem:mixed-moment-connected-cluster-cancellation}, including pairwise disjointness within each of the families $I$, $A$, and $B$, the mixed-moment partition sum satisfies
  \[
  \left|\sum_{\pi\in\Pi([\ell])}(-1)^{|\pi|-1}(|\pi|-1)!
    \prod_{C\in\pi}M(C)\right|
  \leq4\ell^{2\ell}\eta^L(L^2y_0)^{\ell-1}
    \left(\frac{x_0}{y_0}\right)^{cc(\mathcal B)-1}.
  \] -/)
  (proof := /-- By \cref{lem:mixed-moment-connected-cluster-cancellation}, the partition sum is the product of
  $\eta^L(L^2y_0)^{\ell-1}(x_0/y_0)^{cc(\mathcal B)-1}$ and a remainder $R$ with $|R|\leq4\ell^{2\ell}$.  All factors preceding $R$ are nonnegative under the stated hypotheses.  Taking absolute values, using multiplicativity of the absolute value, and applying the bound on $R$ yields the displayed inequality. -/)
  (title := /-- Majorant for the mixed-moment cluster expansion -/)
  (latexEnv := "lemma")]
lemma mixed_moment_cluster_majorant
    {ι : Type*} [DecidableEq ι] {ℓ q r : ℕ}
    (I : Fin ℓ → Finset ι) (A : Fin q → Finset ι)
    (B : Fin r → Finset ι) (η x₀ y₀ : ℝ)
    (hI : Set.univ.PairwiseDisjoint I)
    (hA : Set.univ.PairwiseDisjoint A)
    (hB : Set.univ.PairwiseDisjoint B)
    (hℓ : 0 < ℓ) (hη : 0 ≤ η) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀)
    (hr : 1 ≤ r)
    (hsmall : 2 * (total_index_count I : ℝ) ^ 2 * y₀ ≤ 1)
    (hxy : 2 * x₀ ≤ y₀) :
    |∑ π : Finpartition (Finset.univ : Finset (Fin ℓ)),
        ((-1 : ℝ) ^ (π.parts.card - 1)) *
          (Nat.factorial (π.parts.card - 1) : ℝ) *
          ∏ C ∈ π.parts, mixed_moment_right_hand_side I A B η x₀ y₀ C| ≤
      4 * (ℓ : ℝ) ^ (2 * ℓ) * η ^ total_index_count I *
        ((total_index_count I : ℝ) ^ 2 * y₀) ^ (ℓ - 1) *
        (x₀ / y₀) ^ (intersection_component_count I B - 1) := by
  obtain ⟨R, hR, hRbound⟩ :=
    mixed_moment_connected_cluster_cancellation I A B η x₀ y₀ hI hA hB hℓ hη hx₀ hy₀
      hr hsmall hxy
  have hK : (0 : ℝ) ≤ η ^ total_index_count I *
      ((total_index_count I : ℝ) ^ 2 * y₀) ^ (ℓ - 1) *
      (x₀ / y₀) ^ (intersection_component_count I B - 1) :=
    mul_nonneg (mul_nonneg (pow_nonneg hη _)
      (pow_nonneg (mul_nonneg (sq_nonneg _) hy₀) _))
      (pow_nonneg (div_nonneg hx₀ hy₀) _)
  rw [hR, abs_mul, abs_of_nonneg hK]
  calc (η ^ total_index_count I *
        ((total_index_count I : ℝ) ^ 2 * y₀) ^ (ℓ - 1) *
        (x₀ / y₀) ^ (intersection_component_count I B - 1)) * |R|
      ≤ (η ^ total_index_count I *
        ((total_index_count I : ℝ) ^ 2 * y₀) ^ (ℓ - 1) *
        (x₀ / y₀) ^ (intersection_component_count I B - 1)) *
          (4 * (ℓ : ℝ) ^ (2 * ℓ)) := mul_le_mul_of_nonneg_left hRbound hK
    _ = 4 * (ℓ : ℝ) ^ (2 * ℓ) * η ^ total_index_count I *
        ((total_index_count I : ℝ) ^ 2 * y₀) ^ (ℓ - 1) *
        (x₀ / y₀) ^ (intersection_component_count I B - 1) := by ring

@[blueprint "lem:cumulant-bound-positive-b-family"
  (statement := /-- Let $\ell,q,r\in\mathbb N$ with $\ell\geq1$ and $r\geq1$.  Let $(\Omega,\mathcal F,\mu)$ be a probability space; let $Z_t:\Omega\to\mathbb R$ for $t\in[\ell]$; and let $I$, $A$, and $B$ be finite-set families indexed by $[\ell]$, $[q]$, and $[r]$, respectively.  Suppose that $\eta,x_0,y_0\geq0$, that the general mixed-moment hypothesis of \cref{def:has-general-mixed-moments} holds (so, in particular, the sets within each of $I$, $A$, and $B$ are pairwise disjoint), that $2L^2y_0\leq1$, and that $2x_0\leq y_0$.  Then
  \[
  |\operatorname{cum}(Z_1,\ldots,Z_\ell)|
  \leq4\ell^{2\ell}\eta^L(L^2y_0)^{\ell-1}
  \left(\frac{x_0}{y_0}\right)^{cc(\mathcal B)-1},
  \]
  where $L$ is defined by \cref{def:total-index-count}, the cumulant by \cref{def:joint-cumulant}, and $cc(\mathcal B)$ by \cref{def:intersection-component-count}. -/)
  (proof := /-- By \cref{lem:joint-cumulant-of-mixed-moments}, the joint cumulant is the partition sum formed from the prescribed mixed moments.  Apply \cref{lem:mixed-moment-cluster-majorant} to this sum with the stated nonnegativity, nonemptiness, and smallness hypotheses.  Substituting its bound in the partition-sum identity gives the asserted inequality. -/)
  (title := /-- Cumulant bound when the $B$-family is nonempty -/)
  (latexEnv := "lemma")]
lemma cumulant_bound_positive_b_family
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {ℓ q r : ℕ} (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (Z : Fin ℓ → Ω → ℝ) (I : Fin ℓ → Finset ι)
    (A : Fin q → Finset ι) (B : Fin r → Finset ι) (η x₀ y₀ : ℝ)
    (hℓ : 0 < ℓ) (hη : 0 ≤ η) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀)
    (hmom : has_general_mixed_moments μ Z I A B η x₀ y₀)
    (hr : 1 ≤ r)
    (hsmall : 2 * (total_index_count I : ℝ) ^ 2 * y₀ ≤ 1)
    (hxy : 2 * x₀ ≤ y₀) :
    |joint_cumulant μ Z| ≤
      4 * (ℓ : ℝ) ^ (2 * ℓ) * η ^ total_index_count I *
        ((total_index_count I : ℝ) ^ 2 * y₀) ^ (ℓ - 1) *
        (x₀ / y₀) ^ (intersection_component_count I B - 1) := by
  rw [joint_cumulant_of_mixed_moments μ Z I A B η x₀ y₀ hmom]
  exact mixed_moment_cluster_majorant I A B η x₀ y₀ hmom.1 hmom.2.1 hmom.2.2.1 hℓ hη hx₀ hy₀
    hr hsmall hxy

@[blueprint "lem:mixed-moment-empty-b-cluster-majorant"
  (statement := /-- Let $\ell,q,r\in\mathbb N$ with $\ell\geq1$ and $r=0$.  Let $I$, $A$, and $B$ be finite-set families indexed by $[\ell]$, $[q]$, and $[r]$, respectively, and suppose that the sets within each family are pairwise disjoint.  Let $\eta,x_0,y_0\geq0$, put $L=|I_{[\ell]}|$, and let $M$ be the function of \cref{def:mixed-moment-right-hand-side}.  If $2L^2x_0\leq1$, then
  \[
  \left|\sum_{\pi\in\Pi([\ell])}(-1)^{|\pi|-1}(|\pi|-1)!
    \prod_{C\in\pi}M(C)\right|
  \leq2\ell^{2\ell}\eta^L(L^2x_0)^{\ell-1}.
  \] -/)
  (proof := /-- The smallness hypothesis implies $Lx_0<1$.  Apply \cref{lem:mixed-moment-configuration-expansion} to express the partition sum as the absolutely convergent sum of the weights of connected admissible configurations for a rank function on $U$.  The position-preserving estimate \cref{lem:mixed-moment-empty-b-tree-majorant} applies to this rank function.  It sums the differentiated geometric masses created by marking tree occurrences, including every possible marked word position, and gives exactly
  \[
    2\ell^{2\ell}\eta^L(L^2x_0)^{\ell-1}.
  \]
  Substituting the connected-configuration expansion proves the desired inequality. -/)
  (title := /-- Sharp cluster majorant for an empty $B$-family -/)
  (latexEnv := "lemma")]
lemma mixed_moment_empty_b_cluster_majorant
    {ι : Type*} [DecidableEq ι] {ℓ q r : ℕ}
    (I : Fin ℓ → Finset ι) (A : Fin q → Finset ι)
    (B : Fin r → Finset ι) (η x₀ y₀ : ℝ)
    (hI : Set.univ.PairwiseDisjoint I)
    (hA : Set.univ.PairwiseDisjoint A)
    (hB : Set.univ.PairwiseDisjoint B)
    (hℓ : 0 < ℓ) (hη : 0 ≤ η) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀)
    (hr : r = 0)
    (hsmall : 2 * (total_index_count I : ℝ) ^ 2 * x₀ ≤ 1) :
    |∑ π : Finpartition (Finset.univ : Finset (Fin ℓ)),
        ((-1 : ℝ) ^ (π.parts.card - 1)) *
          (Nat.factorial (π.parts.card - 1) : ℝ) *
          ∏ C ∈ π.parts, mixed_moment_right_hand_side I A B η x₀ y₀ C| ≤
      2 * (ℓ : ℝ) ^ (2 * ℓ) * η ^ total_index_count I *
        ((total_index_count I : ℝ) ^ 2 * x₀) ^ (ℓ - 1) := by
  have hL : (0 : ℝ) ≤ (total_index_count I : ℝ) := Nat.cast_nonneg _
  have hconv : (total_index_count I : ℝ) * x₀ < 1 := by
    rcases Nat.eq_zero_or_pos (total_index_count I) with h | h
    · rw [h]
      norm_num
    · have h1 : (1 : ℝ) ≤ (total_index_count I : ℝ) := by
        exact_mod_cast h
      nlinarith [mul_nonneg (mul_nonneg hL (sub_nonneg.2 h1)) hx₀]
  obtain ⟨rank, hrank, hsummable, hexp⟩ :=
    mixed_moment_configuration_expansion I A B η x₀ y₀ hI hA hB hℓ hη hx₀ hy₀ hconv
  rw [hexp]
  exact mixed_moment_empty_b_tree_majorant I A B η x₀ y₀ rank hI hA hB hℓ hη hx₀ hy₀
    hr hsmall hrank

@[blueprint "lem:cumulant-bound-empty-b-family"
  (statement := /-- Let $\ell,q,r\in\mathbb N$ with $\ell\geq1$ and $r=0$.  Let $(\Omega,\mathcal F,\mu)$ be a probability space; let $Z_t:\Omega\to\mathbb R$ for $t\in[\ell]$; and let $I$, $A$, and $B$ be finite-set families indexed by $[\ell]$, $[q]$, and $[r]$, respectively.  Suppose that $\eta,x_0,y_0\geq0$, that the general mixed-moment hypothesis of \cref{def:has-general-mixed-moments} holds (so, in particular, the sets within each of $I$, $A$, and $B$ are pairwise disjoint), and that $2L^2x_0\leq1$.  Then
  \[
  |\operatorname{cum}(Z_1,\ldots,Z_\ell)|
  \leq2\ell^{2\ell}\eta^L(L^2x_0)^{\ell-1},
  \]
  where $L$ and the cumulant are defined by \cref{def:total-index-count,def:joint-cumulant}. -/)
  (proof := /-- By \cref{lem:joint-cumulant-of-mixed-moments}, the joint cumulant is the partition sum of the prescribed mixed moments.  The hypothesis \cref{def:has-general-mixed-moments} supplies pairwise disjointness within the families $I$, $A$, and $B$.  Apply \cref{lem:mixed-moment-empty-b-cluster-majorant} with these disjointness hypotheses, $r=0$, the nonnegativity assumptions, and $2L^2x_0\leq1$.  Substitution in the partition-sum identity gives the required bound. -/)
  (title := /-- Cumulant bound when the $B$-family is empty -/)
  (latexEnv := "lemma")]
lemma cumulant_bound_empty_b_family
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {ℓ q r : ℕ} (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (Z : Fin ℓ → Ω → ℝ) (I : Fin ℓ → Finset ι)
    (A : Fin q → Finset ι) (B : Fin r → Finset ι) (η x₀ y₀ : ℝ)
    (hℓ : 0 < ℓ) (hη : 0 ≤ η) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀)
    (hmom : has_general_mixed_moments μ Z I A B η x₀ y₀)
    (hr : r = 0)
    (hsmall : 2 * (total_index_count I : ℝ) ^ 2 * x₀ ≤ 1) :
    |joint_cumulant μ Z| ≤
      2 * (ℓ : ℝ) ^ (2 * ℓ) * η ^ total_index_count I *
        ((total_index_count I : ℝ) ^ 2 * x₀) ^ (ℓ - 1) := by
  rw [joint_cumulant_of_mixed_moments μ Z I A B η x₀ y₀ hmom]
  exact mixed_moment_empty_b_cluster_majorant I A B η x₀ y₀ hmom.1 hmom.2.1 hmom.2.2.1
    hℓ hη hx₀ hy₀ hr hsmall

@[blueprint "thm:upper-bound-general-cumulant"
  (statement := /-- Let $\ell,q,r\in\mathbb N$ with $\ell\geq1$.  Let $(\Omega,\mathcal F,\mu)$ be a probability space; let $Z_t:\Omega\to\mathbb R$ for $t\in[\ell]$; and let $I$, $A$, and $B$ be finite-set families indexed by $[\ell]$, $[q]$, and $[r]$, respectively.  Assume that $\eta,x_0,y_0\geq0$ and that the variables satisfy the general mixed-moment hypothesis of \cref{def:has-general-mixed-moments}; in particular, the sets within each of $I$, $A$, and $B$ are pairwise disjoint.  Writing $L=|I_{[\ell]}|$ and letting $\mathcal B$ be the graph of \cref{def:b-intersection-graph}, the following assertions hold:
  \begin{enumerate}
  \item If $r\geq1$, $2L^2y_0\leq1$, and $2x_0\leq y_0$, then
  \[
  |\operatorname{cum}(Z_1,\ldots,Z_\ell)|
  \leq4\ell^{2\ell}\eta^L(L^2y_0)^{\ell-1}
  \left(\frac{x_0}{y_0}\right)^{cc(\mathcal B)-1}.
  \]
  \item If $r=0$ and $2L^2x_0\leq1$, then
  \[
  |\operatorname{cum}(Z_1,\ldots,Z_\ell)|
  \leq2\ell^{2\ell}\eta^L(L^2x_0)^{\ell-1}.
  \]
  \end{enumerate} -/)
  (proof := /-- Under the hypotheses of the first implication, \cref{lem:cumulant-bound-positive-b-family} gives the first displayed inequality.  Under the hypotheses of the second implication, \cref{lem:cumulant-bound-empty-b-family} gives the second displayed inequality.  These two implications form the asserted conjunction. -/)
  (title := /-- General upper bounds for the joint cumulant -/)
  (latexEnv := "theorem")]
theorem upper_bound_general_cumulant
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {ℓ q r : ℕ} (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (Z : Fin ℓ → Ω → ℝ) (I : Fin ℓ → Finset ι)
    (A : Fin q → Finset ι) (B : Fin r → Finset ι) (η x₀ y₀ : ℝ)
    (hℓ : 0 < ℓ) (hη : 0 ≤ η) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀)
    (hmom : has_general_mixed_moments μ Z I A B η x₀ y₀) :
    (1 ≤ r →
      2 * (total_index_count I : ℝ) ^ 2 * y₀ ≤ 1 →
      2 * x₀ ≤ y₀ →
      |joint_cumulant μ Z| ≤
        4 * (ℓ : ℝ) ^ (2 * ℓ) * η ^ total_index_count I *
          ((total_index_count I : ℝ) ^ 2 * y₀) ^ (ℓ - 1) *
          (x₀ / y₀) ^ (intersection_component_count I B - 1)) ∧
    (r = 0 →
      2 * (total_index_count I : ℝ) ^ 2 * x₀ ≤ 1 →
      |joint_cumulant μ Z| ≤
        2 * (ℓ : ℝ) ^ (2 * ℓ) * η ^ total_index_count I *
          ((total_index_count I : ℝ) ^ 2 * x₀) ^ (ℓ - 1)) := by
  refine ⟨fun hr hsmall hxy =>
      cumulant_bound_positive_b_family μ Z I A B η x₀ y₀ hℓ hη hx₀ hy₀ hmom hr hsmall hxy,
    fun hr hsmall =>
      cumulant_bound_empty_b_family μ Z I A B η x₀ y₀ hℓ hη hx₀ hy₀ hmom hr hsmall⟩

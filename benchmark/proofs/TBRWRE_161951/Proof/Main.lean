import Architect
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Kernel.Invariance

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

@[blueprint "def:graph-edge-weights"
  (statement := /-- Let $G=(V,E)$ be a simple graph.  A positive edge-weighting of $G$ is a
  symmetric function $w:V\times V\to\mathbb{R}$ which is strictly positive on adjacent
  pairs and vanishes on nonadjacent pairs. -/)
  (title := /-- Positive edge-weightings -/)
  (latexEnv := "definition")]
structure graph_edge_weights {V : Type*} (G : SimpleGraph V) where
  weight : V → V → ℝ
  symmetric : ∀ x y, weight x y = weight y x
  positive_of_adj : ∀ {x y}, G.Adj x y → 0 < weight x y
  zero_of_not_adj : ∀ {x y}, ¬ G.Adj x y → weight x y = 0

@[blueprint "def:weight-lipschitz"
  (statement := /-- Let $G=(V,E)$ be a simple graph, let $w$ be a positive edge-weighting,
  and let $\beta\in\mathbb{R}$.  The weighting $w$ is $\beta$-Lipschitz if, for every
  $x,y,z\in V$ with $y\sim x\sim z$,
  \[
    \beta^{-1}\leq \frac{w(x,y)}{w(x,z)}\leq\beta .
  \] -/)
  (title := /-- The local Lipschitz condition -/)
  (latexEnv := "definition")]
def weight_lipschitz {V : Type*} (G : SimpleGraph V) (β : ℝ)
    (w : graph_edge_weights G) : Prop :=
  ∀ ⦃x y z : V⦄, G.Adj x y → G.Adj x z →
    β⁻¹ ≤ w.weight x y / w.weight x z ∧ w.weight x y / w.weight x z ≤ β

@[blueprint "def:weighted-degree"
  (statement := /-- For a positive edge-weighting $w$ on a finite graph, define the
  weighted degree of $x$ by $w(x)=\sum_{y\in V}w(x,y)$. -/)
  (title := /-- Weighted vertex degree -/)
  (latexEnv := "definition")]
noncomputable def weighted_degree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (w : graph_edge_weights G) (x : V) : ℝ := by
  classical
  exact ∑ y, w.weight x y

@[blueprint "def:weighted-transition"
  (statement := /-- For a positive edge-weighting $w$ on a finite graph, define its
  weighted random-walk matrix by
  \[
    P_w(x,y)=
    \begin{cases}
      w(x,y)/w(x),&x\neq y,\\
      0,&x=y.
    \end{cases}
  \] -/)
  (title := /-- The weighted random walk -/)
  (latexEnv := "definition")]
noncomputable def weighted_transition {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (w : graph_edge_weights G) : Matrix V V ℝ := by
  classical
  exact fun x y => if x = y then 0 else w.weight x y / weighted_degree G w x

@[blueprint "def:parity-averaged-power"
  (statement := /-- Let $P$ be a real matrix indexed by a finite set and let
  $m\in\mathbb N$.  Its parity-averaged $m$-step kernel is
  \[
    \mathcal A_m(P)=\frac12\bigl(P^m+P^{m-1}\bigr),
  \]
  where subtraction in the exponent is truncated at zero. -/)
  (title := /-- Average of two consecutive matrix powers -/)
  (latexEnv := "definition")]
noncomputable def parity_averaged_power {V : Type*} [Fintype V]
    [DecidableEq V] (P : Matrix V V ℝ) (m : ℕ) : Matrix V V ℝ := by
  exact fun x y => ((P ^ m) x y + (P ^ (m - 1)) x y) / 2

@[blueprint "def:lazy-weighted-transition"
  (statement := /-- For a positive edge-weighting $w$ on a finite graph, define the
  half-lazy weighted transition matrix by
  \[
    P_w^{\mathrm{L}}(x,y)=
    \begin{cases}
      \tfrac12,&x=y,\\
      \tfrac12\,w(x,y)/w(x),&x\neq y.
    \end{cases}
  \]
  Thus $P_w^{\mathrm{L}}=(I+P_w)/2$ whenever every weighted degree is positive. -/)
  (title := /-- The half-lazy weighted random walk -/)
  (latexEnv := "definition")]
noncomputable def lazy_weighted_transition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : graph_edge_weights G) : Matrix V V ℝ := by
  classical
  exact fun x y =>
    if x = y then 1 / 2 else w.weight x y / (2 * weighted_degree G w x)

@[blueprint "def:stationary-distribution"
  (statement := /-- For a positive edge-weighting $w$, define
  \[
    W=\sum_{x\in V}w(x),\qquad \pi_w(x)=\frac{w(x)}{W}.
  \]
  This is the stationary distribution of the weighted random walk whenever the total
  weight is positive. -/)
  (title := /-- Stationary distribution of the weighted walk -/)
  (latexEnv := "definition")]
noncomputable def stationary_distribution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (w : graph_edge_weights G) : V → ℝ := by
  classical
  exact fun x => weighted_degree G w x / ∑ z, weighted_degree G w z

@[blueprint "def:external-vertex-boundary"
  (statement := /-- If $S$ is a finite set of vertices of $G$, its external vertex
  boundary is
  \[
    \partial_V S=\{v\in V\setminus S:\text{ there is }u\in S\text{ with }u\sim v\}.
  \] -/)
  (title := /-- External vertex boundary -/)
  (latexEnv := "definition")]
noncomputable def external_vertex_boundary {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (S : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => v ∉ S ∧ ∃ u ∈ S, G.Adj u v

@[blueprint "def:vertex-expansion"
  (statement := /-- For a finite simple graph $G=(V,E)$, define its vertex expansion by
  \[
    \Psi_G=\inf_{\substack{\varnothing\neq S\subseteq V\\2|S|\leq |V|}}
      \frac{|\partial_VS|}{|S|}.
  \] -/)
  (title := /-- Vertex expansion -/)
  (latexEnv := "definition")]
noncomputable def vertex_expansion {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ :=
  sInf {r : ℝ | ∃ S : Finset V, S.Nonempty ∧ 2 * S.card ≤ Fintype.card V ∧
    r = (external_vertex_boundary G S).card / (S.card : ℝ)}

@[blueprint "def:closed-metric-neighborhood"
  (statement := /-- For $S\subseteq V$ and $k\in\mathbb{N}$, define the closed
  $k$-neighborhood
  \[
    B_k(S)=\{v\in V:\text{ there is }u\in S\text{ with }\operatorname{dist}_G(u,v)\leq k\}.
  \] -/)
  (title := /-- Closed graph neighborhoods -/)
  (latexEnv := "definition")]
noncomputable def closed_metric_neighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (k : ℕ) (S : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ∃ u ∈ S, G.dist u v ≤ k

@[blueprint "def:robust-radius"
  (statement := /-- For $\psi\in\mathbb{R}$, set
  \[
    K(\psi)=\left\lceil\frac{2}{\log(1+\psi)}\right\rceil_{\mathbb{N}}.
  \] -/)
  (title := /-- The robustness radius -/)
  (latexEnv := "definition")]
noncomputable def robust_radius (ψ : ℝ) : ℕ :=
  ⌈2 / Real.log (1 + ψ)⌉₊

@[blueprint "def:robust-lipschitz-bound"
  (statement := /-- For the radius $K(\psi)$, set
  \[
    \sigma(\psi)=\exp\left(\frac{1}{2K(\psi)}\right).
  \] -/)
  (title := /-- The robustness Lipschitz constant -/)
  (latexEnv := "definition")]
noncomputable def robust_lipschitz_bound (ψ : ℝ) : ℝ :=
  Real.exp (1 / (2 * (robust_radius ψ : ℝ)))

@[blueprint "def:stationary-mass"
  (statement := /-- If $\pi:V\to\mathbb{R}$ and $S\subseteq V$ is finite, define
  $\pi(S)=\sum_{x\in S}\pi(x)$. -/)
  (title := /-- Mass of a vertex set -/)
  (latexEnv := "definition")]
noncomputable def stationary_mass {V : Type*} (π : V → ℝ) (S : Finset V) : ℝ := by
  classical
  exact ∑ x ∈ S, π x

@[blueprint "def:stationary-cut-flow"
  (statement := /-- For a transition matrix $P$, a weight $\pi$, and finite vertex sets
  $S,T$, define
  \[
    Q_P(S,T)=\sum_{x\in S}\sum_{y\in T}\pi(x)P(x,y).
  \] -/)
  (title := /-- Stationary flow across a cut -/)
  (latexEnv := "definition")]
noncomputable def stationary_cut_flow {V : Type*} (π : V → ℝ) (P : Matrix V V ℝ)
    (S T : Finset V) : ℝ := by
  classical
  exact ∑ x ∈ S, ∑ y ∈ T, π x * P x y

@[blueprint "def:markov-conductance"
  (statement := /-- Let $P$ be a finite transition matrix with stationary weight $\pi$.
  Its conductance is
  \[
    \Phi_P=\inf_{\substack{\varnothing\neq S\subseteq V\\0<\pi(S)\leq 1/2}}
      \frac{Q_P(S,V\setminus S)}{\pi(S)}.
  \] -/)
  (title := /-- Conductance of a finite chain -/)
  (latexEnv := "definition")]
noncomputable def markov_conductance {V : Type*} [Fintype V] [DecidableEq V] (π : V → ℝ)
    (P : Matrix V V ℝ) : ℝ :=
  sInf {r : ℝ | ∃ S : Finset V, S.Nonempty ∧ 0 < stationary_mass π S ∧
    stationary_mass π S ≤ 1 / 2 ∧
    r = stationary_cut_flow π P S (Finset.univ \ S) / stationary_mass π S}

@[blueprint "def:weighted-mean"
  (statement := /-- For a weight $\pi:V\to\mathbb{R}$ and $f:V\to\mathbb{R}$, define
  $\mathbb{E}_{\pi}f=\sum_{x\in V}\pi(x)f(x)$. -/)
  (title := /-- Weighted mean -/)
  (latexEnv := "definition")]
noncomputable def weighted_mean {V : Type*} [Fintype V] [DecidableEq V]
    (π f : V → ℝ) : ℝ := by
  classical
  exact ∑ x, π x * f x

@[blueprint "def:weighted-variance"
  (statement := /-- Define the variance of $f:V\to\mathbb{R}$ with respect to $\pi$ by
  \[
    \operatorname{Var}_{\pi}(f)=
      \sum_{x\in V}\pi(x)\bigl(f(x)-\mathbb{E}_{\pi}f\bigr)^2.
  \] -/)
  (title := /-- Weighted variance -/)
  (latexEnv := "definition")]
noncomputable def weighted_variance {V : Type*} [Fintype V] [DecidableEq V]
    (π f : V → ℝ) : ℝ := by
  classical
  exact ∑ x, π x * (f x - weighted_mean π f) ^ 2

@[blueprint "def:dirichlet-form"
  (statement := /-- For a transition matrix $P$ and stationary weight $\pi$, define
  \[
    \mathcal{E}_P(f,f)=\frac12\sum_{x,y\in V}
      \pi(x)P(x,y)\bigl(f(x)-f(y)\bigr)^2.
  \] -/)
  (title := /-- Dirichlet form of a finite chain -/)
  (latexEnv := "definition")]
noncomputable def dirichlet_form {V : Type*} [Fintype V] [DecidableEq V] (π : V → ℝ)
    (P : Matrix V V ℝ) (f : V → ℝ) : ℝ := by
  classical
  exact (1 / 2) * ∑ x, ∑ y, π x * P x y * (f x - f y) ^ 2

@[blueprint "def:spectral-gap"
  (statement := /-- For a finite reversible transition matrix $P$ with stationary
  distribution $\pi$, define its spectral gap by the Poincaré variational formula
  \[
    \gamma_P=\inf_{\operatorname{Var}_{\pi}(f)>0}
      \frac{\mathcal{E}_P(f,f)}{\operatorname{Var}_{\pi}(f)}.
  \]
  For a reversible chain this equals $1-\lambda_2$, where $\lambda_2$ is the
  second-largest eigenvalue. -/)
  (title := /-- Spectral gap -/)
  (latexEnv := "definition")]
noncomputable def spectral_gap {V : Type*} [Fintype V] [DecidableEq V] (π : V → ℝ)
    (P : Matrix V V ℝ) : ℝ :=
  sInf {r : ℝ | ∃ f : V → ℝ, 0 < weighted_variance π f ∧
    r = dirichlet_form π P f / weighted_variance π f}

@[blueprint "lem:two-sided-vertex-boundary-bound"
  (statement := /-- Let $G=(V,E)$ be a finite simple graph, let $\psi\in\mathbb R$,
  and suppose that $\psi\leq\Psi_G$. Then every $S\subseteq V$ satisfies
  \[
    |\partial_VS|\geq \frac{\psi}{3}\min\{|S|,|V\setminus S|\}.
  \] -/)
  (proof := /-- By \cref{def:vertex-expansion}, for every nonempty
  $A\subseteq V$ with $2|A|\leq |V|$ one has
  $\psi|A|\leq |\partial_VA|$. By \cref{def:external-vertex-boundary},
  $\partial_VA\subseteq V\setminus A$. If $|V|<2$, the family defining
  $\Psi_G$ is empty and hence $\psi\leq0$; the conclusion is then immediate.
  It is likewise immediate whenever $\psi\leq0$. Thus suppose that $|V|\geq2$
  and $\psi>0$. Choose $A\subseteq V$ with $|A|=\lfloor |V|/2\rfloor$.
  Then $A$ is admissible and
  $|\partial_VA|\leq |V\setminus A|\leq2|A|$, whence
  $\psi\leq\Psi_G\leq2$.

  If $2|S|\leq |V|$, the asserted inequality follows from
  $\psi|S|\leq|\partial_VS|$; the case $S=\varnothing$ is immediate. Otherwise
  put $C=V\setminus S$, $T=\partial_VS$, and $R=C\setminus T$. Then
  $|C|\leq|S|$, $2|R|\leq|V|$, and $C$ is the disjoint union of $R$ and $T$.
  Moreover, $\partial_VR\subseteq T$: if an external neighbor of $R$ were not
  in $T$, it would lie in $S$, and its adjacent vertex in $R$ would then belong
  to $T$, a contradiction. If $R$ is nonempty, expansion gives
  $\psi|R|\leq|\partial_VR|\leq|T|$; if $R$ is empty, then $C\subseteq T$.
  Using $\psi\leq2$ and $|C|=|R|+|T|$ in either case gives
  $\psi|C|\leq3|T|$. Since $|C|\leq|S|$, this is precisely the required
  estimate. -/)
  (title := /-- A two-sided vertex-boundary estimate -/)
  (latexEnv := "lemma")]
lemma two_sided_vertex_boundary_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (ψ : ℝ) (hExpansion : ψ ≤ vertex_expansion G) (S : Finset V) :
    (ψ / 3) * min (S.card : ℝ) ((Finset.univ \ S).card : ℝ) ≤
      (external_vertex_boundary G S).card := by
  classical
  have hBdd : BddBelow {r : ℝ | ∃ A : Finset V, A.Nonempty ∧
      2 * A.card ≤ Fintype.card V ∧
      r = (external_vertex_boundary G A).card / (A.card : ℝ)} := by
    refine ⟨0, ?_⟩
    rintro r ⟨A, -, -, rfl⟩
    positivity
  have expansion_le_ratio (A : Finset V) (hAne : A.Nonempty)
      (hAhalf : 2 * A.card ≤ Fintype.card V) :
      vertex_expansion G ≤
        (external_vertex_boundary G A).card / (A.card : ℝ) := by
    unfold vertex_expansion
    apply csInf_le hBdd
    exact ⟨A, hAne, hAhalf, rfl⟩
  have boundary_subset_compl (A : Finset V) :
      external_vertex_boundary G A ⊆ Finset.univ \ A := by
    intro v hv
    have hv' : v ∉ A ∧ ∃ u ∈ A, G.Adj u v := by
      simpa only [external_vertex_boundary, Finset.mem_filter,
        Finset.mem_univ, true_and] using hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv'.1⟩
  by_cases hVsmall : Fintype.card V < 2
  · have hEmpty : {r : ℝ | ∃ A : Finset V, A.Nonempty ∧
        2 * A.card ≤ Fintype.card V ∧
        r = (external_vertex_boundary G A).card / (A.card : ℝ)} = ∅ := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨A, hAne, hAhalf, -⟩
      have hApos : 0 < A.card := Finset.card_pos.mpr hAne
      have hAle : A.card ≤ Fintype.card V := Finset.card_le_univ A
      omega
    have hExpansionZero : vertex_expansion G = 0 := by
      simp [vertex_expansion, hEmpty]
    have hψnonpos : ψ ≤ 0 := by
      linarith
    have hminnonneg : 0 ≤ min (S.card : ℝ) ((Finset.univ \ S).card : ℝ) := by
      positivity
    exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) hminnonneg).trans (by positivity)
  · have hVlarge : 2 ≤ Fintype.card V := by omega
    by_cases hψnonpos : ψ ≤ 0
    · have hminnonneg : 0 ≤ min (S.card : ℝ) ((Finset.univ \ S).card : ℝ) := by
        positivity
      exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) hminnonneg).trans (by positivity)
    · have hψpos : 0 < ψ := lt_of_not_ge hψnonpos
      have hψtwo : ψ ≤ 2 := by
        have hHalfLe : Fintype.card V / 2 ≤ (Finset.univ : Finset V).card := by
          simpa using Nat.div_le_self (Fintype.card V) 2
        obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq
          (s := (Finset.univ : Finset V)) (n := Fintype.card V / 2) hHalfLe
        have hHalfPos : 0 < Fintype.card V / 2 := Nat.div_pos hVlarge (by norm_num)
        have hAposNat : 0 < A.card := by omega
        have hAne : A.Nonempty := Finset.card_pos.mp hAposNat
        have hAhalf : 2 * A.card ≤ Fintype.card V := by omega
        have hExpA := expansion_le_ratio A hAne hAhalf
        have hBoundaryCard : (external_vertex_boundary G A).card ≤
            (Finset.univ \ A).card :=
          Finset.card_le_card (boundary_subset_compl A)
        have hComplCard : (Finset.univ \ A).card = Fintype.card V - A.card :=
          Finset.card_univ_sdiff A
        have hComplBound : (Finset.univ \ A).card ≤ 2 * A.card := by
          rw [hComplCard, hAcard]
          omega
        have hCardBound : (external_vertex_boundary G A).card ≤ 2 * A.card :=
          hBoundaryCard.trans hComplBound
        have hApos : 0 < (A.card : ℝ) := by exact_mod_cast hAposNat
        have hRatioTwo :
            (external_vertex_boundary G A).card / (A.card : ℝ) ≤ 2 := by
          apply (div_le_iff₀ hApos).2
          exact_mod_cast hCardBound
        exact hExpansion.trans (hExpA.trans hRatioTwo)
      by_cases hShalf : 2 * S.card ≤ Fintype.card V
      · by_cases hSne : S.Nonempty
        · have hExpS := expansion_le_ratio S hSne hShalf
          have hSposNat : 0 < S.card := Finset.card_pos.mpr hSne
          have hSpos : 0 < (S.card : ℝ) := by exact_mod_cast hSposNat
          have hStrong : ψ * (S.card : ℝ) ≤
              (external_vertex_boundary G S).card :=
            (le_div_iff₀ hSpos).mp (hExpansion.trans hExpS)
          have hMinLe : min (S.card : ℝ) ((Finset.univ \ S).card : ℝ) ≤
              (S.card : ℝ) := min_le_left _ _
          nlinarith
        · simp only [Finset.not_nonempty_iff_eq_empty] at hSne
          subst S
          simp
      · let C : Finset V := Finset.univ \ S
        let T : Finset V := external_vertex_boundary G S
        let R : Finset V := C \ T
        have hTsubC : T ⊆ C := boundary_subset_compl S
        have hScardLe : S.card ≤ Fintype.card V := Finset.card_le_univ S
        have hCcard : C.card = Fintype.card V - S.card := by
          exact Finset.card_univ_sdiff S
        have hCleS : C.card ≤ S.card := by
          rw [hCcard]
          omega
        have hCleSreal : (C.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hCleS
        rw [min_eq_right hCleSreal]
        change ψ / 3 * (C.card : ℝ) ≤ (T.card : ℝ)
        have hRsubC : R ⊆ C := Finset.sdiff_subset
        have hCsplit : R.card + T.card = C.card := by
          exact Finset.card_sdiff_add_card_eq_card hTsubC
        have hBoundaryRsubT : external_vertex_boundary G R ⊆ T := by
          intro v hv
          have hv' : v ∉ R ∧ ∃ u ∈ R, G.Adj u v := by
            simpa only [external_vertex_boundary, Finset.mem_filter,
              Finset.mem_univ, true_and] using hv
          rcases hv' with ⟨hvnotR, u, huR, huv⟩
          by_contra hvnotT
          have hvnotC : v ∉ C := by
            intro hvC
            exact hvnotR (Finset.mem_sdiff.mpr ⟨hvC, hvnotT⟩)
          have hvS : v ∈ S := by
            by_contra hvnotS
            apply hvnotC
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvnotS⟩
          have huC : u ∈ C := hRsubC huR
          have hunotS : u ∉ S := (Finset.mem_sdiff.mp huC).2
          have huT : u ∈ T := by
            have : u ∈ external_vertex_boundary G S := by
              simp only [external_vertex_boundary, Finset.mem_filter,
                Finset.mem_univ, true_and]
              exact ⟨hunotS, v, hvS, huv.symm⟩
            exact this
          exact (Finset.mem_sdiff.mp huR).2 huT
        by_cases hRne : R.Nonempty
        · have hChalf : 2 * C.card ≤ Fintype.card V := by
            rw [hCcard]
            omega
          have hRcardLe : R.card ≤ C.card := Finset.card_le_card hRsubC
          have hRhalf : 2 * R.card ≤ Fintype.card V := by omega
          have hExpR := expansion_le_ratio R hRne hRhalf
          have hRposNat : 0 < R.card := Finset.card_pos.mpr hRne
          have hRpos : 0 < (R.card : ℝ) := by exact_mod_cast hRposNat
          have hExpansionR : ψ * (R.card : ℝ) ≤
              (external_vertex_boundary G R).card :=
            (le_div_iff₀ hRpos).mp (hExpansion.trans hExpR)
          have hBoundaryRCard : (external_vertex_boundary G R).card ≤ T.card :=
            Finset.card_le_card hBoundaryRsubT
          have hExpansionRT : ψ * (R.card : ℝ) ≤ (T.card : ℝ) := by
            apply hExpansionR.trans
            exact_mod_cast hBoundaryRCard
          have hSplitReal : (C.card : ℝ) = (R.card : ℝ) + (T.card : ℝ) := by
            exact_mod_cast hCsplit.symm
          nlinarith
        · simp only [Finset.not_nonempty_iff_eq_empty] at hRne
          have hCsubT : C ⊆ T := by
            intro v hvC
            by_contra hvnotT
            have : v ∈ R := Finset.mem_sdiff.mpr ⟨hvC, hvnotT⟩
            simpa [hRne] using this
          have hCcardLe : C.card ≤ T.card := Finset.card_le_card hCsubT
          have hCcardLeReal : (C.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hCcardLe
          nlinarith

@[blueprint "lem:vertex-expansion-ball-growth"
  (statement := /-- Let $G=(V,E)$ be a finite graph and let $\psi>0$ satisfy
  $\Psi_G\geq\psi$.  For every $S\subseteq V$ and $k\in\mathbb{N}$,
  \[
    |B_k(S)|\geq
    \min\left\{(1+\psi)^k|S|,\frac{|V|}{2}\right\}.
  \] -/)
  (proof := /-- Write $B_i=B_i(S)$ as in
  \cref{def:closed-metric-neighborhood}.  The definition
  \cref{lem:two-sided-vertex-boundary-bound} first gives a nonnegative coarse
  lower bound for $|\partial_VA|$, and hence verifies the sign of its boundary
  ratio.  The definition \cref{def:vertex-expansion} then implies that every
  nonempty $A\subseteq V$ with $2|A|\leq |V|$ satisfies
  $\psi|A|\leq |\partial_VA|$: the defining infimum is at most the boundary
  ratio of $A$, while it is at least $\psi$ by hypothesis.

  For every $i$, one has $S\subseteq B_i\subseteq B_{i+1}$.  Moreover,
  \cref{def:external-vertex-boundary,def:closed-metric-neighborhood} give
  $B_i\cap\partial_VB_i=\varnothing$ and
  $B_i\cup\partial_VB_i\subseteq B_{i+1}$.  For the latter inclusion, a vertex
  of the boundary is adjacent to some $u\in B_i$; appending that edge to a path
  of length at most $i$ from $S$ to $u$ places the boundary vertex in
  $B_{i+1}$.  Consequently,
  $|B_{i+1}|\geq |B_i|+|\partial_VB_i|$.

  We prove by induction on $i$ that either
  $|B_i|\geq(1+\psi)^i|S|$ or $|B_i|\geq |V|/2$.  The assertion at $i=0$
  follows from $S\subseteq B_0$.  If the half-volume alternative already holds,
  monotonicity propagates it.  Otherwise, if $S$ is nonempty, then $B_i$ is
  nonempty and $2|B_i|\leq |V|$, so the preceding expansion and union estimates
  yield $|B_{i+1}|\geq(1+\psi)|B_i|$ and hence the first alternative at
  $i+1$.  If $S$ is empty, that alternative is immediate.  Applying the
  resulting disjunction at $i=k$ proves the asserted minimum bound. -/)
  (title := /-- Growth of metric neighborhoods -/)
  (latexEnv := "lemma")]
lemma vertex_expansion_ball_growth {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (ψ : ℝ) (hψ : 0 < ψ) (hExpansion : ψ ≤ vertex_expansion G)
    (S : Finset V) (k : ℕ) :
    min ((1 + ψ) ^ k * (S.card : ℝ)) ((Fintype.card V : ℝ) / 2) ≤
      (closed_metric_neighborhood G k S).card := by
  classical
  have hBdd : BddBelow {r : ℝ | ∃ A : Finset V, A.Nonempty ∧
      2 * A.card ≤ Fintype.card V ∧
      r = (external_vertex_boundary G A).card / (A.card : ℝ)} := by
    refine ⟨0, ?_⟩
    rintro r ⟨A, -, -, rfl⟩
    positivity
  have expansion_le_ratio (A : Finset V) (hAne : A.Nonempty)
      (hAhalf : 2 * A.card ≤ Fintype.card V) :
      vertex_expansion G ≤
        (external_vertex_boundary G A).card / (A.card : ℝ) := by
    unfold vertex_expansion
    apply csInf_le hBdd
    exact ⟨A, hAne, hAhalf, rfl⟩
  have seed_subset (i : ℕ) :
      S ⊆ closed_metric_neighborhood G i S := by
    intro v hv
    simp only [closed_metric_neighborhood, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨v, hv, by simp⟩
  have neighborhood_mono (i : ℕ) :
      closed_metric_neighborhood G i S ⊆
        closed_metric_neighborhood G (i + 1) S := by
    intro v hv
    have hv' : ∃ u ∈ S, G.dist u v ≤ i := by
      simpa only [closed_metric_neighborhood, Finset.mem_filter,
        Finset.mem_univ, true_and] using hv
    rcases hv' with ⟨u, hu, huv⟩
    simp only [closed_metric_neighborhood, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨u, hu, by omega⟩
  have neighborhood_union_subset (i : ℕ) :
      closed_metric_neighborhood G i S ∪
          external_vertex_boundary G (closed_metric_neighborhood G i S) ⊆
        closed_metric_neighborhood G (i + 1) S := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact neighborhood_mono i hv
    · have hv' : v ∉ closed_metric_neighborhood G i S ∧
          ∃ u ∈ closed_metric_neighborhood G i S, G.Adj u v := by
        simpa only [external_vertex_boundary, Finset.mem_filter,
          Finset.mem_univ, true_and] using hv
      rcases hv'.2 with ⟨u, hu, huv⟩
      have hu' : ∃ s ∈ S, G.dist s u ≤ i := by
        simpa only [closed_metric_neighborhood, Finset.mem_filter,
          Finset.mem_univ, true_and] using hu
      rcases hu' with ⟨s, hs, hsu⟩
      simp only [closed_metric_neighborhood, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨s, hs, ?_⟩
      calc
        G.dist s v ≤ G.dist s u + G.dist u v :=
          huv.reachable.dist_triangle_right s
        _ = G.dist s u + 1 := by
          rw [G.dist_eq_one_iff_adj.mpr huv]
        _ ≤ i + 1 := by omega
  have neighborhood_boundary_disjoint (i : ℕ) :
      Disjoint (closed_metric_neighborhood G i S)
        (external_vertex_boundary G (closed_metric_neighborhood G i S)) := by
    refine Finset.disjoint_left.mpr ?_
    intro v hvNeighborhood hvBoundary
    have hvBoundary' : v ∉ closed_metric_neighborhood G i S ∧
        ∃ u ∈ closed_metric_neighborhood G i S, G.Adj u v := by
      simpa only [external_vertex_boundary, Finset.mem_filter,
        Finset.mem_univ, true_and] using hvBoundary
    exact hvBoundary'.1 hvNeighborhood
  have neighborhood_card_growth (i : ℕ) :
      (closed_metric_neighborhood G i S).card +
          (external_vertex_boundary G (closed_metric_neighborhood G i S)).card ≤
        (closed_metric_neighborhood G (i + 1) S).card := by
    calc
      (closed_metric_neighborhood G i S).card +
          (external_vertex_boundary G (closed_metric_neighborhood G i S)).card =
        (closed_metric_neighborhood G i S ∪
          external_vertex_boundary G (closed_metric_neighborhood G i S)).card :=
            (Finset.card_union_of_disjoint
              (neighborhood_boundary_disjoint i)).symm
      _ ≤ (closed_metric_neighborhood G (i + 1) S).card :=
        Finset.card_le_card (neighborhood_union_subset i)
  have growth_or_half : ∀ i : ℕ,
      (1 + ψ) ^ i * (S.card : ℝ) ≤
          (closed_metric_neighborhood G i S).card ∨
        (Fintype.card V : ℝ) / 2 ≤
          (closed_metric_neighborhood G i S).card := by
    intro i
    induction i with
    | zero =>
        left
        have hcard := Finset.card_le_card (seed_subset 0)
        have hcardReal : (S.card : ℝ) ≤
            ((closed_metric_neighborhood G 0 S).card : ℝ) := by
          exact_mod_cast hcard
        simpa using hcardReal
    | succ i ih =>
        have hmonoNat := Finset.card_le_card (neighborhood_mono i)
        have hmonoReal : ((closed_metric_neighborhood G i S).card : ℝ) ≤
            ((closed_metric_neighborhood G (i + 1) S).card : ℝ) := by
          exact_mod_cast hmonoNat
        rcases ih with hGrowth | hHalf
        · by_cases hAlready : (Fintype.card V : ℝ) / 2 ≤
              (closed_metric_neighborhood G i S).card
          · right
            simpa [Nat.succ_eq_add_one] using hAlready.trans hmonoReal
          · by_cases hSne : S.Nonempty
            · have hNeighborhoodNe :
                  (closed_metric_neighborhood G i S).Nonempty :=
                hSne.mono (seed_subset i)
              have hBelow : ((closed_metric_neighborhood G i S).card : ℝ) <
                  (Fintype.card V : ℝ) / 2 := lt_of_not_ge hAlready
              have hTwiceReal :
                  2 * ((closed_metric_neighborhood G i S).card : ℝ) <
                    (Fintype.card V : ℝ) := by
                nlinarith
              have hTwiceNat :
                  2 * (closed_metric_neighborhood G i S).card <
                    Fintype.card V := by
                exact_mod_cast hTwiceReal
              have hNeighborhoodHalf :
                  2 * (closed_metric_neighborhood G i S).card ≤
                    Fintype.card V := by omega
              have hExp := expansion_le_ratio
                (closed_metric_neighborhood G i S) hNeighborhoodNe
                hNeighborhoodHalf
              have hCardPosNat :
                  0 < (closed_metric_neighborhood G i S).card :=
                Finset.card_pos.mpr hNeighborhoodNe
              have hCardPos :
                  0 < ((closed_metric_neighborhood G i S).card : ℝ) := by
                exact_mod_cast hCardPosNat
              have hTwoSided := two_sided_vertex_boundary_bound G ψ hExpansion
                (closed_metric_neighborhood G i S)
              have hCoarseNonneg : 0 ≤
                  (ψ / 3) * min
                    ((closed_metric_neighborhood G i S).card : ℝ)
                    (((Finset.univ \ closed_metric_neighborhood G i S).card : ℝ)) := by
                positivity
              have hBoundaryNonneg : 0 ≤
                  ((external_vertex_boundary G
                    (closed_metric_neighborhood G i S)).card : ℝ) :=
                hCoarseNonneg.trans hTwoSided
              have hRatioNonneg : 0 ≤
                  (external_vertex_boundary G
                    (closed_metric_neighborhood G i S)).card /
                    ((closed_metric_neighborhood G i S).card : ℝ) :=
                div_nonneg hBoundaryNonneg hCardPos.le
              have hRatio := hExpansion.trans hExp
              have hBoundary :
                  ψ * ((closed_metric_neighborhood G i S).card : ℝ) ≤
                    (external_vertex_boundary G
                      (closed_metric_neighborhood G i S)).card := by
                have hMul := mul_le_mul hRatio
                  (le_refl ((closed_metric_neighborhood G i S).card : ℝ))
                  hCardPos.le hRatioNonneg
                calc
                  ψ * ((closed_metric_neighborhood G i S).card : ℝ) ≤
                      ((external_vertex_boundary G
                        (closed_metric_neighborhood G i S)).card : ℝ) /
                        ((closed_metric_neighborhood G i S).card : ℝ) *
                          ((closed_metric_neighborhood G i S).card : ℝ) := hMul
                  _ = (external_vertex_boundary G
                        (closed_metric_neighborhood G i S)).card := by
                    field_simp
              have hCardGrowthNat := neighborhood_card_growth i
              have hCardGrowthReal :
                  ((closed_metric_neighborhood G i S).card : ℝ) +
                      ((external_vertex_boundary G
                        (closed_metric_neighborhood G i S)).card : ℝ) ≤
                    ((closed_metric_neighborhood G (i + 1) S).card : ℝ) := by
                exact_mod_cast hCardGrowthNat
              have hOneNonneg : 0 ≤ 1 + ψ := by linarith
              have hScaled := mul_le_mul_of_nonneg_left hGrowth hOneNonneg
              have hGrowNeighborhood :
                  (1 + ψ) * ((closed_metric_neighborhood G i S).card : ℝ) ≤
                    (closed_metric_neighborhood G (i + 1) S).card := by
                nlinarith
              left
              calc
                (1 + ψ) ^ (Nat.succ i) * (S.card : ℝ) =
                    (1 + ψ) * ((1 + ψ) ^ i * (S.card : ℝ)) := by
                  rw [pow_succ]
                  ring
                _ ≤ (1 + ψ) *
                    ((closed_metric_neighborhood G i S).card : ℝ) := hScaled
                _ ≤ (closed_metric_neighborhood G (Nat.succ i) S).card := by
                  simpa [Nat.succ_eq_add_one] using hGrowNeighborhood
            · left
              rw [Finset.not_nonempty_iff_eq_empty] at hSne
              subst S
              simp [closed_metric_neighborhood]
        · right
          simpa [Nat.succ_eq_add_one] using hHalf.trans hmonoReal
  rcases growth_or_half k with hGrowth | hHalf
  · exact (min_le_left _ _).trans hGrowth
  · exact (min_le_right _ _).trans hHalf

@[blueprint "lem:stationary-ratio-on-short-paths"
  (statement := /-- Let $G$ be a finite $d$-regular graph with $d>0$, and let
  $w$ be a $\sigma(\psi)$-Lipschitz positive edge-weighting.  For all
  $x,y\in V$ such that $y$ is reachable from $x$ and
  $\operatorname{dist}_G(x,y)\leq K(\psi)$, one has
  \[
    \sigma(\psi)^{-2K(\psi)}
    \leq\frac{\pi_w(x)}{\pi_w(y)}
    \leq\sigma(\psi)^{2K(\psi)}.
  \] -/)
  (proof := /-- By \cref{def:robust-radius,def:robust-lipschitz-bound},
  $\sigma(\psi)$ is positive and at least one.  Reachability supplies a shortest
  walk from $x$ to $y$; its length is $\operatorname{dist}_G(x,y)$ and is
  therefore at most $K(\psi)$.  At two adjacent vertices, regularity supplies
  exactly $d$ incident edges at each endpoint.  By
  \cref{def:graph-edge-weights,def:weight-lipschitz,def:weighted-degree}, the
  weighted degrees are positive, and comparing every incident weight with the
  common edge bounds the ratio of the two weighted degrees between
  $\sigma(\psi)^{-2}$ and $\sigma(\psi)^2$.  Induction along the shortest
  walk, followed by monotonicity of powers because $\sigma(\psi)\geq1$, gives
  the same bounds with exponent $2K(\psi)$.  The total weighted degree is
  positive, so the common normalizing factor in
  \cref{def:stationary-distribution} cancels and yields the displayed
  inequalities. -/)
  (title := /-- Stationary masses vary slowly on short paths -/)
  (latexEnv := "lemma")]
lemma stationary_ratio_on_short_paths {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite]
    (d : ℕ) (ψ : ℝ) (w : graph_edge_weights G)
    (hRegular : G.IsRegularOfDegree d)
    (hd : 0 < d)
    (hLipschitz : weight_lipschitz G (robust_lipschitz_bound ψ) w)
    {x y : V} (hReachable : G.Reachable x y)
    (hxy : G.dist x y ≤ robust_radius ψ) :
    ((robust_lipschitz_bound ψ) ^ (2 * robust_radius ψ))⁻¹ ≤
        stationary_distribution G w x / stationary_distribution G w y ∧
      stationary_distribution G w x / stationary_distribution G w y ≤
        (robust_lipschitz_bound ψ) ^ (2 * robust_radius ψ) := by
  classical
  let σ := robust_lipschitz_bound ψ
  have hσpos : 0 < σ := by
    exact Real.exp_pos _
  have hσone : 1 ≤ σ := by
    simp [σ, robust_lipschitz_bound]
  have hdegree_eq (a : V) :
      weighted_degree G w a = ∑ z ∈ G.neighborFinset a, w.weight a z := by
    rw [weighted_degree]
    symm
    apply Finset.sum_subset (by simp)
    intro z _ hz
    apply w.zero_of_not_adj
    simpa using hz
  have hdegree_upper {a b : V} (hab : G.Adj a b) :
      weighted_degree G w a ≤ (d : ℝ) * σ * w.weight a b := by
    rw [hdegree_eq]
    calc
      (∑ z ∈ G.neighborFinset a, w.weight a z) ≤
          ∑ _z ∈ G.neighborFinset a, σ * w.weight a b := by
        apply Finset.sum_le_sum
        intro z hz
        exact (div_le_iff₀ (w.positive_of_adj hab)).mp
          ((hLipschitz (by simpa using hz) hab).2)
      _ = (d : ℝ) * σ * w.weight a b := by
        simp [hRegular.degree_eq]
        ring
  have hdegree_lower {a b : V} (hab : G.Adj a b) :
      (d : ℝ) * σ⁻¹ * w.weight a b ≤ weighted_degree G w a := by
    rw [hdegree_eq]
    calc
      (d : ℝ) * σ⁻¹ * w.weight a b =
          ∑ _z ∈ G.neighborFinset a, σ⁻¹ * w.weight a b := by
        simp [hRegular.degree_eq]
        ring
      _ ≤ ∑ z ∈ G.neighborFinset a, w.weight a z := by
        apply Finset.sum_le_sum
        intro z hz
        exact (le_div_iff₀ (w.positive_of_adj hab)).mp
          ((hLipschitz (by simpa using hz) hab).1)
  have hdegree_pos (a : V) : 0 < weighted_degree G w a := by
    have hdegree_nat : 0 < G.degree a := by
      simpa [hRegular.degree_eq] using hd
    obtain ⟨b, hab⟩ := (G.degree_pos_iff_exists_adj (v := a)).mp hdegree_nat
    have hlower := hdegree_lower hab
    have hpositive : 0 < (d : ℝ) * σ⁻¹ * w.weight a b := by
      exact mul_pos (mul_pos (by exact_mod_cast hd) (inv_pos.mpr hσpos))
        (w.positive_of_adj hab)
    exact hpositive.trans_le hlower
  have hadjacent {a b : V} (hab : G.Adj a b) :
      weighted_degree G w a ≤ σ ^ 2 * weighted_degree G w b := by
    calc
      weighted_degree G w a ≤ (d : ℝ) * σ * w.weight a b :=
        hdegree_upper hab
      _ = σ ^ 2 * ((d : ℝ) * σ⁻¹ * w.weight b a) := by
        rw [w.symmetric b a]
        field_simp [ne_of_gt hσpos]
        <;> ring
      _ ≤ σ ^ 2 * weighted_degree G w b :=
        mul_le_mul_of_nonneg_left (hdegree_lower hab.symm) (sq_nonneg σ)
  have hwalk {a b : V} (q : G.Walk a b) :
      weighted_degree G w a ≤ σ ^ (2 * q.length) * weighted_degree G w b := by
    induction q with
    | nil =>
        simp
    | cons hab q ih =>
        simp only [SimpleGraph.Walk.length]
        calc
          weighted_degree G w _ ≤ σ ^ 2 * weighted_degree G w _ :=
            hadjacent hab
          _ ≤ σ ^ 2 * (σ ^ (2 * q.length) * weighted_degree G w _) :=
            mul_le_mul_of_nonneg_left ih (sq_nonneg σ)
          _ = σ ^ (2 * Nat.succ q.length) * weighted_degree G w _ := by
            rw [show 2 * Nat.succ q.length = 2 + 2 * q.length by omega, pow_add]
            ring
  obtain ⟨p, hp⟩ := hReachable.exists_walk_length_eq_dist
  have hexponent : 2 * G.dist x y ≤ 2 * robust_radius ψ := by
    omega
  have hforward :
      weighted_degree G w x ≤
        σ ^ (2 * robust_radius ψ) * weighted_degree G w y := by
    calc
      weighted_degree G w x ≤ σ ^ (2 * p.length) * weighted_degree G w y :=
        hwalk p
      _ ≤ σ ^ (2 * robust_radius ψ) * weighted_degree G w y := by
        apply mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hσone (by simpa [hp] using hexponent))
          (le_of_lt (hdegree_pos y))
  have hreverse :
      weighted_degree G w y ≤
        σ ^ (2 * robust_radius ψ) * weighted_degree G w x := by
    calc
      weighted_degree G w y ≤
          σ ^ (2 * p.reverse.length) * weighted_degree G w x :=
        hwalk p.reverse
      _ ≤ σ ^ (2 * robust_radius ψ) * weighted_degree G w x := by
        apply mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hσone (by simpa [hp] using hexponent))
          (le_of_lt (hdegree_pos x))
  have htotal_pos : 0 < ∑ z, weighted_degree G w z := by
    apply Finset.sum_pos
    · intro z _
      exact hdegree_pos z
    · exact ⟨x, by simp⟩
  have hratio :
      stationary_distribution G w x / stationary_distribution G w y =
        weighted_degree G w x / weighted_degree G w y := by
    simp only [stationary_distribution]
    field_simp [ne_of_gt htotal_pos, ne_of_gt (hdegree_pos y)]
  rw [hratio]
  constructor
  · apply (le_div_iff₀ (hdegree_pos y)).2
    calc
      (σ ^ (2 * robust_radius ψ))⁻¹ * weighted_degree G w y ≤
          (σ ^ (2 * robust_radius ψ))⁻¹ *
            (σ ^ (2 * robust_radius ψ) * weighted_degree G w x) :=
        mul_le_mul_of_nonneg_left hreverse (by positivity)
      _ = weighted_degree G w x := by
        field_simp [ne_of_gt hσpos]
  · exact (div_le_iff₀ (hdegree_pos y)).2 hforward

@[blueprint "lem:weighted-transition-power-entry-nonnegative"
  (statement := /-- Let $V$ be finite, let $G$ be a locally finite simple
  graph on $V$, and let $w$ be a positive edge-weighting of $G$.  For every
  $n\in\mathbb N$ and every $x,y\in V$,
  \[
    0\leq P_w^n(x,y).
  \] -/)
  (proof := /-- By \cref{def:graph-edge-weights}, every weight is
  nonnegative: it is positive on an edge and zero off the edge set.  Hence
  every weighted degree from \cref{def:weighted-degree} is nonnegative, and
  every entry of the matrix in \cref{def:weighted-transition} is
  nonnegative.  Induction on $n$ now proves the claim.  The case $n=0$
  follows from the entries of the identity matrix.  At the induction step,
  the matrix-product formula expresses each entry as a finite sum of
  products of nonnegative entries. -/)
  (title := /-- Nonnegativity of weighted transition powers -/)
  (latexEnv := "lemma")]
lemma weighted_transition_power_entry_nonnegative {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
    (w : graph_edge_weights G) (n : ℕ) (x y : V) :
    0 ≤ (weighted_transition G w ^ n) x y := by
  classical
  have hweight_nonneg (a b : V) : 0 ≤ w.weight a b := by
    by_cases hab : G.Adj a b
    · exact le_of_lt (w.positive_of_adj hab)
    · rw [w.zero_of_not_adj hab]
  have hdegree_nonneg (a : V) : 0 ≤ weighted_degree G w a := by
    rw [weighted_degree]
    exact Finset.sum_nonneg fun z _ => hweight_nonneg a z
  have htransition_nonneg (a b : V) :
      0 ≤ weighted_transition G w a b := by
    rw [weighted_transition]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (hweight_nonneg a b) (hdegree_nonneg a)
  induction n generalizing x y with
  | zero =>
      simp only [pow_zero, Matrix.one_apply]
      split <;> norm_num
  | succ n ih =>
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun z _ =>
        mul_nonneg (ih x z) (htransition_nonneg z y)

@[blueprint "lem:bounded-walk-transition-lower-bound"
  (statement := /-- Let $V$ be finite, let $G$ be a locally finite
  $d$-regular simple graph on $V$ with $d>0$, let $\psi\in\mathbb R$, and
  let $w$ be a $\sigma(\psi)$-Lipschitz positive edge-weighting.  If $p$ is
  a walk from $x$ to $y$ of length at most $2K(\psi)$, then
  \[
    \bigl(d\,\sigma(\psi)\bigr)^{-2K(\psi)}
      \leq P_w^{\operatorname{length}(p)}(x,y).
  \] -/)
  (proof := /-- The definitions
  \cref{def:robust-lipschitz-bound,def:weight-lipschitz} give
  $\sigma(\psi)\geq1$.  By regularity and
  \cref{def:graph-edge-weights,def:weighted-degree}, each weighted degree is
  positive, and comparison of every incident weight with the weight of a
  fixed edge gives $w(a)\leq d\sigma(\psi)w(a,b)$ whenever $a\sim b$.
  Thus \cref{def:weighted-transition} gives
  $P_w(a,b)\geq(d\sigma(\psi))^{-1}$ on every edge.

  Induction along $p$ retains the summand corresponding to the next vertex
  in each matrix product.  All discarded summands are nonnegative by
  \cref{lem:weighted-transition-power-entry-nonnegative}, so this yields
  $P_w^{\operatorname{length}(p)}(x,y)\geq
  (d\sigma(\psi))^{-\operatorname{length}(p)}$.  Finally,
  $d\sigma(\psi)\geq1$ and
  $\operatorname{length}(p)\leq2K(\psi)$, so monotonicity of powers and
  order reversal under inversion give the displayed bound. -/)
  (title := /-- Transition lower bound along a bounded-length walk -/)
  (latexEnv := "lemma")]
lemma bounded_walk_transition_lower_bound {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
    (d : ℕ) (ψ : ℝ) (w : graph_edge_weights G)
    (hRegular : G.IsRegularOfDegree d) (hd : 0 < d)
    (hLipschitz : weight_lipschitz G (robust_lipschitz_bound ψ) w)
    {x y : V} (p : G.Walk x y)
    (hp : p.length ≤ 2 * robust_radius ψ) :
    ((((d : ℝ) * robust_lipschitz_bound ψ) ^
      (2 * robust_radius ψ))⁻¹) ≤
      (weighted_transition G w ^ p.length) x y := by
  classical
  let σ := robust_lipschitz_bound ψ
  have hσpos : 0 < σ := by
    exact Real.exp_pos _
  have hσone : 1 ≤ σ := by
    simp [σ, robust_lipschitz_bound]
  have hdreal : (1 : ℝ) ≤ d := by
    exact_mod_cast (show 1 ≤ d by omega)
  have hbasepos : 0 < (d : ℝ) * σ := by
    exact mul_pos (by exact_mod_cast hd) hσpos
  have hbaseone : 1 ≤ (d : ℝ) * σ := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (d : ℝ) * σ :=
        mul_le_mul hdreal hσone (by norm_num) (by positivity)
  have hdegree_eq (a : V) :
      weighted_degree G w a = ∑ z ∈ G.neighborFinset a, w.weight a z := by
    rw [weighted_degree]
    symm
    apply Finset.sum_subset (by simp)
    intro z _ hz
    apply w.zero_of_not_adj
    simpa using hz
  have hdegree_upper {a b : V} (hab : G.Adj a b) :
      weighted_degree G w a ≤ (d : ℝ) * σ * w.weight a b := by
    rw [hdegree_eq]
    calc
      (∑ z ∈ G.neighborFinset a, w.weight a z) ≤
          ∑ _z ∈ G.neighborFinset a, σ * w.weight a b := by
        apply Finset.sum_le_sum
        intro z hz
        exact (div_le_iff₀ (w.positive_of_adj hab)).mp
          ((hLipschitz (by simpa using hz) hab).2)
      _ = (d : ℝ) * σ * w.weight a b := by
        simp [hRegular.degree_eq]
        ring
  have hdegree_pos (a : V) : 0 < weighted_degree G w a := by
    have hdegree_nat : 0 < G.degree a := by
      simpa [hRegular.degree_eq] using hd
    obtain ⟨b, hab⟩ := (G.degree_pos_iff_exists_adj (v := a)).mp hdegree_nat
    rw [hdegree_eq]
    apply Finset.sum_pos
    · intro z hz
      exact w.positive_of_adj (by simpa using hz)
    · exact ⟨b, by simpa⟩
  have htransition_lower {a b : V} (hab : G.Adj a b) :
      ((d : ℝ) * σ)⁻¹ ≤ weighted_transition G w a b := by
    rw [weighted_transition, if_neg hab.ne]
    apply (le_div_iff₀ (hdegree_pos a)).2
    calc
      ((d : ℝ) * σ)⁻¹ * weighted_degree G w a ≤
          ((d : ℝ) * σ)⁻¹ * ((d : ℝ) * σ * w.weight a b) :=
        mul_le_mul_of_nonneg_left (hdegree_upper hab) (by positivity)
      _ = w.weight a b := by
        field_simp [ne_of_gt hbasepos]
  have hwalk {a b : V} (q : G.Walk a b) :
      (((d : ℝ) * σ) ^ q.length)⁻¹ ≤
        (weighted_transition G w ^ q.length) a b := by
    induction q with
    | nil =>
        simp
    | @cons u v t hab q ih =>
        simp only [SimpleGraph.Walk.length]
        calc
          (((d : ℝ) * σ) ^ Nat.succ q.length)⁻¹ =
              ((d : ℝ) * σ)⁻¹ *
                (((d : ℝ) * σ) ^ q.length)⁻¹ := by
            rw [pow_succ, mul_inv]
            ring
          _ ≤ weighted_transition G w u v *
                (weighted_transition G w ^ q.length) v t := by
            exact mul_le_mul (htransition_lower hab) ih (by positivity)
              (by simpa using
                weighted_transition_power_entry_nonnegative G w 1 u v)
          _ ≤ (weighted_transition G w *
                (weighted_transition G w ^ q.length)) u t := by
            rw [Matrix.mul_apply]
            exact Finset.single_le_sum (s := Finset.univ) (a := v)
              (fun z _ => mul_nonneg
                (by simpa using
                  weighted_transition_power_entry_nonnegative G w 1 u z)
                (weighted_transition_power_entry_nonnegative G w q.length z t))
              (Finset.mem_univ v)
          _ = (weighted_transition G w ^ Nat.succ q.length) u t := by
            rw [show Nat.succ q.length = q.length + 1 by omega, pow_succ']
  calc
    ((((d : ℝ) * robust_lipschitz_bound ψ) ^
        (2 * robust_radius ψ))⁻¹) =
        (((d : ℝ) * σ) ^ (2 * robust_radius ψ))⁻¹ := by rfl
    _ ≤ (((d : ℝ) * σ) ^ p.length)⁻¹ := by
      exact (inv_le_inv₀ (pow_pos hbasepos _) (pow_pos hbasepos _)).2
        (pow_le_pow_right₀ hbaseone hp)
    _ ≤ (weighted_transition G w ^ p.length) x y := hwalk p

@[blueprint "lem:parity-averaged-transition-lower-bound"
  (statement := /-- Let $V$ be finite, let $G$ be a connected, locally finite,
  $d$-regular simple graph with $d>0$, let $\psi>0$, and let $w$ be a
  $\sigma(\psi)$-Lipschitz positive edge-weighting.  If $x,y\in V$ satisfy
  $\operatorname{dist}_G(x,y)\leq 2K(\psi)$, then
  \[
    \frac{1}{20}d^{-2K(\psi)}
      \leq \mathcal A_{2K(\psi)}(P_w)(x,y).
  \] -/)
  (proof := /-- By positivity of $\psi$ and
  \cref{def:robust-radius}, $K=K(\psi)$ is positive.  Choose a shortest walk
  from $x$ to $y$, of length $r\leq2K$.  If $r$ is even, insert two-edge
  backtracks to obtain a walk of length $2K$; if $r$ is odd, then
  $r\leq2K-1$, and the same operation gives a walk of length $2K-1$.
  Connected $d$-regularity and $d>0$ provide an edge on which to perform every
  backtrack.  In the applicable parity, the estimate
  \cref{lem:bounded-walk-transition-lower-bound} gives
  \[
    P_w^j(x,y)\geq(d\sigma)^{-2K},
    \qquad j\in\{2K-1,2K\}.
  \]
  By \cref{def:robust-lipschitz-bound}, $\sigma^{2K}=e$.  The elementary
  first-order exponential remainder estimate gives $e\leq3<10$, and hence
  $(d\sigma)^{-2K}\geq\frac1{10}d^{-2K}$.
  The other entry is nonnegative by
  \cref{lem:weighted-transition-power-entry-nonnegative}.  Averaging the two
  entries according to \cref{def:parity-averaged-power} therefore gives the
  asserted factor $1/20$. -/)
  (title := /-- Transition bound for the parity-averaged kernel -/)
  (latexEnv := "lemma")]
lemma parity_averaged_transition_lower_bound {V : Type*} [Fintype V]
    [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite]
    (d : ℕ) (ψ : ℝ) (w : graph_edge_weights G)
    (hConnected : G.Connected) (hRegular : G.IsRegularOfDegree d)
    (hd : 0 < d) (hψ : 0 < ψ)
    (hLipschitz : weight_lipschitz G (robust_lipschitz_bound ψ) w)
    {x y : V} (hxy : G.dist x y ≤ 2 * robust_radius ψ) :
    (1 / 20) * (((d : ℝ) ^ (2 * robust_radius ψ))⁻¹) ≤
      parity_averaged_power (weighted_transition G w)
        (2 * robust_radius ψ) x y := by
  classical
  let K := robust_radius ψ
  change (1 / 20) * (((d : ℝ) ^ (2 * K))⁻¹) ≤
    parity_averaged_power (weighted_transition G w) (2 * K) x y
  have hKpos : 0 < K := by
    have hlog : 0 < Real.log (1 + ψ) := Real.log_pos (by linarith)
    change 0 < robust_radius ψ
    rw [robust_radius, Nat.ceil_pos]
    exact div_pos (by norm_num) hlog
  have hdreal : 0 < (d : ℝ) := by
    exact_mod_cast hd
  have hσpow : robust_lipschitz_bound ψ ^ (2 * K) = Real.exp 1 := by
    change (Real.exp (1 / (2 * (K : ℝ)))) ^ (2 * K) = Real.exp 1
    rw [← Real.exp_nat_mul]
    congr 1
    have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hKpos)
    field_simp
    norm_num
  have hexp_le : Real.exp 1 ≤ (10 : ℝ) := by
    have h := Real.exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num)
      (n := 1) (by norm_num)
    norm_num at h ⊢
    linarith
  have hinv : (1 / 10 : ℝ) ≤ (Real.exp 1)⁻¹ := by
    rw [one_div]
    exact (inv_le_inv₀ (by norm_num) (Real.exp_pos 1)).2 hexp_le
  have hscale :
      (1 / 10 : ℝ) * (((d : ℝ) ^ (2 * K))⁻¹) ≤
        ((((d : ℝ) * robust_lipschitz_bound ψ) ^ (2 * K))⁻¹) := by
    calc
      (1 / 10 : ℝ) * (((d : ℝ) ^ (2 * K))⁻¹) ≤
          (Real.exp 1)⁻¹ * (((d : ℝ) ^ (2 * K))⁻¹) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = ((((d : ℝ) * robust_lipschitz_bound ψ) ^ (2 * K))⁻¹) := by
        simp only [mul_pow, hσpow, mul_inv]
        ring
  obtain ⟨p, hp⟩ := hConnected.exists_walk_length_eq_dist x y
  have hplen : p.length ≤ 2 * K := by
    calc
      p.length = G.dist x y := hp
      _ ≤ 2 * K := by simpa [K] using hxy
  have hydegree : 0 < G.degree y := by
    simpa [hRegular.degree_eq] using hd
  obtain ⟨z, hyz⟩ := (G.degree_pos_iff_exists_adj (v := y)).mp hydegree
  have extend_walk (q : G.Walk x y) (t : ℕ) :
      ∃ r : G.Walk x y, r.length = q.length + 2 * t := by
    induction t with
    | zero =>
        exact ⟨q, by simp⟩
    | succ t ih =>
        obtain ⟨r, hr⟩ := ih
        refine ⟨(r.concat hyz).concat hyz.symm, ?_⟩
        simp [hr]
        omega
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' p.length
  · have hkK : k ≤ K := by omega
    obtain ⟨q, hq⟩ := extend_walk p (K - k)
    have hqlen : q.length = 2 * K := by omega
    have hqle : q.length ≤ 2 * K := by omega
    have hgood :
        ((((d : ℝ) * robust_lipschitz_bound ψ) ^ (2 * K))⁻¹) ≤
          (weighted_transition G w ^ (2 * K)) x y := by
      simpa [K, hqlen] using
        bounded_walk_transition_lower_bound G d ψ w hRegular hd hLipschitz q
          (by simpa [K] using hqle)
    have hother :
        0 ≤ (weighted_transition G w ^ (2 * K - 1)) x y :=
      weighted_transition_power_entry_nonnegative G w (2 * K - 1) x y
    rw [parity_averaged_power]
    nlinarith
  · have hkK : k + 1 ≤ K := by omega
    obtain ⟨q, hq⟩ := extend_walk p (K - (k + 1))
    have hqlen : q.length = 2 * K - 1 := by omega
    have hqle : q.length ≤ 2 * K := by omega
    have hgood :
        ((((d : ℝ) * robust_lipschitz_bound ψ) ^ (2 * K))⁻¹) ≤
          (weighted_transition G w ^ (2 * K - 1)) x y := by
      simpa [K, hqlen] using
        bounded_walk_transition_lower_bound G d ψ w hRegular hd hLipschitz q
          (by simpa [K] using hqle)
    have hother : 0 ≤ (weighted_transition G w ^ (2 * K)) x y :=
      weighted_transition_power_entry_nonnegative G w (2 * K) x y
    rw [parity_averaged_power]
    nlinarith

@[blueprint "lem:small-cardinality-cut-flow-bound-neighborhood-growth"
  (statement := /-- Let (G=(V,E)) be a finite simple graph with vertex
  expansion at least (psi>0).  If the closed (k)-neighborhood of
  (A\subseteq V) is contained in a set (T\subseteq V) satisfying
  (2|T|\leq |V|), then
  [
    (1+\psi)^k|A|\leq |B_k(A)|.
  ] -/)
  (proof := /-- By \cref{lem:vertex-expansion-ball-growth},
  (|B_k(A)|) is at least the minimum of ((1+\psi)^k|A|) and (|V|/2).
  Thus the claim is immediate when ((1+\psi)^k|A|\leq |V|/2).
  In the remaining case, write (B_i=B_i(A)).  The definitions
  \cref{def:closed-metric-neighborhood,def:external-vertex-boundary} give
  (B_i\cup\partial_VB_i\subseteq B_{i+1}), and the union is disjoint.
  For every (i\leq k), one has (B_i\subseteq B_k\subseteq T); hence
  (2|B_i|\leq |V|).  If (A) is nonempty, the definition
  \cref{def:vertex-expansion} therefore yields
  (|\partial_VB_i|\geq\psi|B_i|), so
  (|B_{i+1}|\geq(1+\psi)|B_i|).  Induction from (A\subseteq B_0)
  proves the claim.  If (A) is empty, both sides vanish. -/)
  (title := /-- Neighborhood growth below half cardinality -/)
  (latexEnv := "lemma")]
lemma small_cardinality_cut_flow_bound_neighborhood_growth
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ψ : ℝ) (hψ : 0 < ψ)
    (hExpansion : ψ ≤ vertex_expansion G)
    (A T : Finset V) (k : ℕ)
    (hContain : closed_metric_neighborhood G k A ⊆ T)
    (hTcard : 2 * T.card ≤ Fintype.card V) :
    (1 + ψ) ^ k * (A.card : ℝ) ≤
      (closed_metric_neighborhood G k A).card := by
  classical
  have hBdd : BddBelow {r : ℝ | ∃ C : Finset V, C.Nonempty ∧
      2 * C.card ≤ Fintype.card V ∧
      r = (external_vertex_boundary G C).card / (C.card : ℝ)} := by
    refine ⟨0, ?_⟩
    rintro r ⟨C, -, -, rfl⟩
    positivity
  have expansion_le_ratio (C : Finset V) (hCne : C.Nonempty)
      (hChalf : 2 * C.card ≤ Fintype.card V) :
      vertex_expansion G ≤
        (external_vertex_boundary G C).card / (C.card : ℝ) := by
    unfold vertex_expansion
    apply csInf_le hBdd
    exact ⟨C, hCne, hChalf, rfl⟩
  have seed_subset (i : ℕ) :
      A ⊆ closed_metric_neighborhood G i A := by
    intro v hv
    simp only [closed_metric_neighborhood, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨v, hv, by simp⟩
  have neighborhood_mono_to {i j : ℕ} (hij : i ≤ j) :
      closed_metric_neighborhood G i A ⊆
        closed_metric_neighborhood G j A := by
    intro v hv
    have hv' : ∃ u ∈ A, G.dist u v ≤ i := by
      simpa only [closed_metric_neighborhood, Finset.mem_filter,
        Finset.mem_univ, true_and] using hv
    rcases hv' with ⟨u, hu, huv⟩
    simp only [closed_metric_neighborhood, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨u, hu, huv.trans hij⟩
  have neighborhood_union_subset (i : ℕ) :
      closed_metric_neighborhood G i A ∪
          external_vertex_boundary G (closed_metric_neighborhood G i A) ⊆
        closed_metric_neighborhood G (i + 1) A := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact neighborhood_mono_to (by omega) hv
    · have hv' : v ∉ closed_metric_neighborhood G i A ∧
          ∃ u ∈ closed_metric_neighborhood G i A, G.Adj u v := by
        simpa only [external_vertex_boundary, Finset.mem_filter,
          Finset.mem_univ, true_and] using hv
      rcases hv'.2 with ⟨u, hu, huv⟩
      have hu' : ∃ a ∈ A, G.dist a u ≤ i := by
        simpa only [closed_metric_neighborhood, Finset.mem_filter,
          Finset.mem_univ, true_and] using hu
      rcases hu' with ⟨a, ha, hau⟩
      simp only [closed_metric_neighborhood, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨a, ha, ?_⟩
      calc
        G.dist a v ≤ G.dist a u + G.dist u v :=
          huv.reachable.dist_triangle_right a
        _ = G.dist a u + 1 := by
          rw [G.dist_eq_one_iff_adj.mpr huv]
        _ ≤ i + 1 := by omega
  have neighborhood_boundary_disjoint (i : ℕ) :
      Disjoint (closed_metric_neighborhood G i A)
        (external_vertex_boundary G (closed_metric_neighborhood G i A)) := by
    refine Finset.disjoint_left.mpr ?_
    intro v hvNeighborhood hvBoundary
    have hvBoundary' : v ∉ closed_metric_neighborhood G i A ∧
        ∃ u ∈ closed_metric_neighborhood G i A, G.Adj u v := by
      simpa only [external_vertex_boundary, Finset.mem_filter,
        Finset.mem_univ, true_and] using hvBoundary
    exact hvBoundary'.1 hvNeighborhood
  have neighborhood_card_growth (i : ℕ) :
      (closed_metric_neighborhood G i A).card +
          (external_vertex_boundary G
            (closed_metric_neighborhood G i A)).card ≤
        (closed_metric_neighborhood G (i + 1) A).card := by
    calc
      (closed_metric_neighborhood G i A).card +
          (external_vertex_boundary G
            (closed_metric_neighborhood G i A)).card =
        (closed_metric_neighborhood G i A ∪
          external_vertex_boundary G
            (closed_metric_neighborhood G i A)).card :=
          (Finset.card_union_of_disjoint
            (neighborhood_boundary_disjoint i)).symm
      _ ≤ (closed_metric_neighborhood G (i + 1) A).card :=
        Finset.card_le_card (neighborhood_union_subset i)
  have growth : ∀ i : ℕ, i ≤ k →
      (1 + ψ) ^ i * (A.card : ℝ) ≤
        (closed_metric_neighborhood G i A).card := by
    intro i hi
    induction i with
    | zero =>
        have hcard := Finset.card_le_card (seed_subset 0)
        have hcardReal : (A.card : ℝ) ≤
            ((closed_metric_neighborhood G 0 A).card : ℝ) := by
          exact_mod_cast hcard
        simpa using hcardReal
    | succ i ih =>
        by_cases hAne : A.Nonempty
        · have hi' : i ≤ k := by omega
          have hGrowth := ih hi'
          have hNeighborhoodNe :
              (closed_metric_neighborhood G i A).Nonempty :=
            hAne.mono (seed_subset i)
          have hSubsetT :
              closed_metric_neighborhood G i A ⊆ T :=
            (neighborhood_mono_to (by omega)).trans hContain
          have hNeighborhoodCard :
              (closed_metric_neighborhood G i A).card ≤ T.card :=
            Finset.card_le_card hSubsetT
          have hNeighborhoodHalf :
              2 * (closed_metric_neighborhood G i A).card ≤
                Fintype.card V := by omega
          have hExp := expansion_le_ratio
            (closed_metric_neighborhood G i A) hNeighborhoodNe
            hNeighborhoodHalf
          have hCardPosNat :
              0 < (closed_metric_neighborhood G i A).card :=
            Finset.card_pos.mpr hNeighborhoodNe
          have hCardPos :
              0 < ((closed_metric_neighborhood G i A).card : ℝ) := by
            exact_mod_cast hCardPosNat
          have hBoundary :
              ψ * ((closed_metric_neighborhood G i A).card : ℝ) ≤
                (external_vertex_boundary G
                  (closed_metric_neighborhood G i A)).card :=
            (le_div_iff₀ hCardPos).mp (hExpansion.trans hExp)
          have hCardGrowthReal :
              ((closed_metric_neighborhood G i A).card : ℝ) +
                  ((external_vertex_boundary G
                    (closed_metric_neighborhood G i A)).card : ℝ) ≤
                ((closed_metric_neighborhood G (i + 1) A).card : ℝ) := by
            exact_mod_cast neighborhood_card_growth i
          have hOneNonneg : 0 ≤ 1 + ψ := by linarith
          have hScaled :
              (1 + ψ) * ((1 + ψ) ^ i * (A.card : ℝ)) ≤
                (1 + ψ) *
                  ((closed_metric_neighborhood G i A).card : ℝ) :=
            mul_le_mul_of_nonneg_left hGrowth hOneNonneg
          calc
            (1 + ψ) ^ (Nat.succ i) * (A.card : ℝ) =
                (1 + ψ) * ((1 + ψ) ^ i * (A.card : ℝ)) := by
              rw [pow_succ]
              ring
            _ ≤ (1 + ψ) *
                ((closed_metric_neighborhood G i A).card : ℝ) := hScaled
            _ ≤ (closed_metric_neighborhood G (Nat.succ i) A).card := by
              norm_num [Nat.succ_eq_add_one] at hCardGrowthReal ⊢
              nlinarith
        · rw [Finset.not_nonempty_iff_eq_empty] at hAne
          subst A
          simp [closed_metric_neighborhood]
  have hCoarse :=
    vertex_expansion_ball_growth G ψ hψ hExpansion A k
  by_cases hBelow :
      (1 + ψ) ^ k * (A.card : ℝ) ≤ (Fintype.card V : ℝ) / 2
  · simpa [min_eq_left hBelow] using hCoarse
  · exact growth k le_rfl

@[blueprint "lem:small-cardinality-cut-flow-bound-hall-restrict"
  (statement := /-- Let (t_i\subseteq\alpha) be a finite family satisfying
  Hall's cardinality condition.  For every finite set (s) of indices, the
  family restricted to (s) also satisfies Hall's condition. -/)
  (proof := /-- Map a finite set of elements of the subtype (s) injectively
  into the original index type.  Its union of allowed sets is unchanged under
  this coercion, so the original Hall inequality gives the result. -/)
  (title := /-- Hall's condition under restriction -/)
  (latexEnv := "lemma")]
lemma small_cardinality_cut_flow_bound_hall_restrict
    {ι α : Type*} [Fintype ι] [DecidableEq α]
    (t : ι → Finset α)
    (ht : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card)
    (s : Finset ι) (s' : Finset (s : Set ι)) :
    s'.card ≤ (s'.biUnion fun a' => t a').card := by
  classical
  rw [← Finset.card_image_of_injective s' Subtype.coe_injective]
  convert ht (s'.image fun z => z.1) using 1
  apply congr_arg
  ext y
  simp

@[blueprint "lem:small-cardinality-cut-flow-bound-hall-erase"
  (statement := /-- Suppose a finite family (t_i\subseteq\alpha) satisfies
  the strict Hall inequality on every nonempty proper set of indices.  After
  deleting one index (x) and one value (a), the family
  $t_i\setminus\{a\}$ satisfies Hall's weak inequality. -/)
  (proof := /-- Coerce a set of indices different from (x) into the original
  type.  It is proper, so its union has strictly larger cardinality.  Erasing
  (a) lowers that cardinality by at most one, leaving at least as many values
  as indices.  The empty set is immediate. -/)
  (title := /-- Hall's condition after deleting an index and value -/)
  (latexEnv := "lemma")]
lemma small_cardinality_cut_flow_bound_hall_erase
    {ι α : Type*} [Fintype ι] [DecidableEq α]
    (t : ι → Finset α) {x : ι} (a : α)
    (ha : ∀ s : Finset ι, s.Nonempty → s ≠ Finset.univ →
      s.card < (s.biUnion t).card)
    (s' : Finset {x' : ι | x' ≠ x}) :
    s'.card ≤ (s'.biUnion fun x' => (t x').erase a).card := by
  classical
  specialize ha (s'.image fun z => z.1)
  rw [Finset.image_nonempty,
    Finset.card_image_of_injective s' Subtype.coe_injective] at ha
  by_cases hne : s'.Nonempty
  · have ha' : s'.card < (s'.biUnion fun z => t z).card := by
      convert ha hne (fun h => by
        simpa [← h] using Finset.mem_univ x) using 2
      ext z
      simp only [Finset.mem_image, Finset.mem_biUnion, SetCoe.exists,
        exists_and_right, exists_eq_right]
    rw [← Finset.erase_biUnion]
    by_cases hmem : a ∈ s'.biUnion fun z => t z
    · rw [Finset.card_erase_of_mem hmem]
      exact Nat.le_sub_one_of_lt ha'
    · rw [Finset.erase_eq_of_notMem hmem]
      exact Nat.le_of_lt ha'
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst s'
    simp

@[blueprint "lem:small-cardinality-cut-flow-bound-hall-complement"
  (statement := /-- Let (t_i\subseteq\alpha) satisfy Hall's condition, and
  suppose equality holds for an index set (s).  On the complementary
  indices, deleting the union belonging to (s) preserves Hall's condition. -/)
  (proof := /-- For a complementary set (s'), apply Hall's inequality to the
  disjoint union (s\cup s') and subtract the equality for (s).  The values
  left after removing the union of the (s)-family contain the corresponding
  set difference, so cardinality monotonicity proves the claim. -/)
  (title := /-- Hall's condition on the complementary family -/)
  (latexEnv := "lemma")]
lemma small_cardinality_cut_flow_bound_hall_complement
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (t : ι → Finset α) (s : Finset ι)
    (hus : s.card = (s.biUnion t).card)
    (ht : ∀ u : Finset ι, u.card ≤ (u.biUnion t).card)
    (s' : Finset ↥(sᶜ : Finset ι)) :
    s'.card ≤
      (s'.biUnion fun x' => t x' \ s.biUnion t).card := by
  classical
  have hDisjoint : Disjoint s (s'.image fun z => z.1) := by
    simp only [Finset.disjoint_left, not_exists, Finset.mem_image,
      SetCoe.exists, exists_and_right, exists_eq_right]
    intro x hx hxc hx'
    rcases hx' with ⟨hxMem, hEq⟩
    subst x
    exact (Finset.mem_compl.mp hxc.2) hx
  have hCard :
      s'.card = (s ∪ s'.image fun z => z.1).card - s.card := by
    simp [hDisjoint,
      Finset.card_image_of_injective _ Subtype.coe_injective,
      Nat.add_sub_cancel_left]
  rw [hCard, hus]
  refine (Nat.sub_le_sub_right (ht _) _).trans ?_
  rw [← Finset.card_sdiff_of_subset]
  · apply Finset.card_le_card
    intro y
    simp only [Finset.mem_biUnion, Finset.mem_sdiff, not_exists,
      Finset.mem_image, and_imp, Finset.mem_union, exists_imp]
    rintro x (hx | ⟨x', hx', rfl⟩) hyt hys
    · exact False.elim ((hys x) ⟨hx, hyt⟩)
    · exact ⟨x', hx', hyt, hys⟩
  · apply Finset.biUnion_subset_biUnion_of_subset_left
    exact Finset.subset_union_left

@[blueprint "lem:small-cardinality-cut-flow-bound-hall-matching"
  (statement := /-- Let (I) be finite and let (t_i\subseteq\alpha) be
  finite.  If every finite (s\subseteq I) satisfies
  [
    |s|\leq\left|\bigcup_{i\in s}t_i\right|,
  ]
  then there is an injective function (f:I\to\alpha) with
  (f(i)\in t_i) for every (i). -/)
  (proof := /-- Proceed by strong induction on (|I|).  If every nonempty
  proper family satisfies strict Hall inequality, choose one index and one
  allowed value, delete both, and apply the induction hypothesis using
  \cref{lem:small-cardinality-cut-flow-bound-hall-erase}.  Otherwise choose a
  nonempty proper tight family.  Apply induction to it using
  \cref{lem:small-cardinality-cut-flow-bound-hall-restrict}, and separately to
  the complementary indices after deleting its value union using
  \cref{lem:small-cardinality-cut-flow-bound-hall-complement}.  The two images
  are disjoint, so the resulting functions combine to an injective system of
  representatives. -/)
  (title := /-- A finite form of Hall's marriage theorem -/)
  (latexEnv := "lemma")]
lemma small_cardinality_cut_flow_bound_hall_matching
    {ι : Type u} {α : Type v} [Finite ι] [DecidableEq α]
    (t : ι → Finset α)
    (ht : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  cases nonempty_fintype ι
  generalize hn : Fintype.card ι = m
  induction m using Nat.strongRecOn generalizing ι with
  | ind n ih =>
      rcases n with (_ | n)
      · rw [Fintype.card_eq_zero_iff] at hn
        exact ⟨isEmptyElim, isEmptyElim, isEmptyElim⟩
      · have ih' :
            ∀ {ι' : Type u} [Fintype ι'] (t' : ι' → Finset α),
              Fintype.card ι' ≤ n →
              (∀ s' : Finset ι',
                s'.card ≤ (s'.biUnion t').card) →
              ∃ f : ι' → α, Function.Injective f ∧
                ∀ x, f x ∈ t' x := by
          intro ι' _ t' hι' ht'
          exact ih _ (Nat.lt_succ_of_le hι') t' ht' _ rfl
        by_cases hStrict :
            ∀ s : Finset ι, s.Nonempty → s ≠ Finset.univ →
              s.card < (s.biUnion t).card
        · haveI : Nonempty ι :=
            Fintype.card_pos_iff.mp (hn.symm ▸ Nat.succ_pos n)
          letI := Classical.decEq ι
          let x := Classical.arbitrary ι
          have htx : (t x).Nonempty := by
            rw [← Finset.card_pos]
            calc
              0 < 1 := Nat.one_pos
              _ ≤ (Finset.biUnion {x} t).card := ht {x}
              _ = (t x).card := by rw [Finset.singleton_biUnion]
          obtain ⟨y, hy⟩ := htx
          let ι' := {x' : ι | x' ≠ x}
          let t' : ι' → Finset α := fun x' => (t x').erase y
          have hCardι' : Fintype.card ι' = n := by
            calc
              Fintype.card ι' = Fintype.card ι - 1 :=
                Set.card_ne_eq x
              _ = n := by
                rw [hn, Nat.add_succ_sub_one, add_zero]
          rcases ih' t' hCardι'.le
              (small_cardinality_cut_flow_bound_hall_erase
                t y hStrict) with ⟨f', hfInjective, hfMem⟩
          refine ⟨fun z => if h : z = x then y else f' ⟨z, h⟩, ?_, ?_⟩
          · intro z₁ z₂ hz
            have hKey : ∀ {z}, y ≠ f' z := by
              intro z hEq
              have hzMem := hfMem z
              simpa [t', ← hEq] using hzMem
            by_cases h₁ : z₁ = x <;> by_cases h₂ : z₂ = x
            · exact h₁.trans h₂.symm
            · simp only [h₁, h₂, ↓reduceDIte] at hz
              exact False.elim (hKey hz)
            · simp only [h₁, h₂, ↓reduceDIte] at hz
              exact False.elim (hKey hz.symm)
            · simp only [h₁, h₂, ↓reduceDIte] at hz
              exact congrArg Subtype.val (hfInjective hz)
          · intro z
            by_cases hz : z = x
            · simp [hz, hy]
            · simp only [hz, ↓reduceDIte]
              exact Finset.mem_of_mem_erase (hfMem ⟨z, hz⟩)
        · push Not at hStrict
          rcases hStrict with ⟨s, hs, hns, hle⟩
          have hTight : s.card = (s.biUnion t).card :=
            Nat.le_antisymm (ht s) hle
          letI := Classical.decEq ι
          have hCardS : Fintype.card s ≤ n := by
            apply Nat.le_of_lt_succ
            calc
              Fintype.card s = s.card := Fintype.card_coe s
              _ < Fintype.card ι :=
                (Finset.card_lt_iff_ne_univ s).mpr hns
              _ = n.succ := hn
          let t' : s → Finset α := fun x' => t x'
          rcases ih' t' hCardS
              (small_cardinality_cut_flow_bound_hall_restrict t ht s) with
            ⟨f', hf'Injective, hf'Mem⟩
          let ι'' := ↥(sᶜ : Finset ι)
          let t'' : ι'' → Finset α :=
            fun x'' => t x'' \ s.biUnion t
          have hCardCompl : Fintype.card ι'' ≤ n := by
            have hlt : (sᶜ).card < Fintype.card ι :=
              (Finset.card_compl_lt_iff_nonempty s).2 hs
            have hEq : Fintype.card ι'' = (sᶜ).card := by
              simpa [ι''] using Fintype.card_coe (sᶜ)
            rw [hEq]
            exact Nat.le_of_lt_succ (by simpa [hn] using hlt)
          rcases ih' t'' hCardCompl
              (small_cardinality_cut_flow_bound_hall_complement
                t s hTight ht) with
            ⟨f'', hf''Injective, hf''Mem⟩
          have hf''Outside :
              ∀ (x : ι) (hx : x ∉ s),
                f'' ⟨x, Finset.mem_compl.mpr hx⟩ ∉ s.biUnion t := by
            intro x hx
            exact (Finset.mem_sdiff.mp
              (hf''Mem ⟨x, Finset.mem_compl.mpr hx⟩)).2
          refine
            ⟨fun x => if h : x ∈ s then f' ⟨x, h⟩
              else f'' ⟨x, Finset.mem_compl.mpr h⟩, ?_, ?_⟩
          · intro x y hxy
            by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
            · simp only [hx, hy, ↓reduceDIte] at hxy
              exact congrArg Subtype.val (hf'Injective hxy)
            · simp only [hx, hy, ↓reduceDIte] at hxy
              have hfx : f' ⟨x, hx⟩ ∈ s.biUnion t := by
                exact Finset.mem_biUnion.mpr
                  ⟨x, hx, hf'Mem ⟨x, hx⟩⟩
              exact False.elim
                ((hf''Outside y hy) (hxy ▸ hfx))
            · simp only [hx, hy, ↓reduceDIte] at hxy
              have hfy : f' ⟨y, hy⟩ ∈ s.biUnion t := by
                exact Finset.mem_biUnion.mpr
                  ⟨y, hy, hf'Mem ⟨y, hy⟩⟩
              exact False.elim
                ((hf''Outside x hx) (hxy.symm ▸ hfy))
            · simp only [hx, hy, ↓reduceDIte] at hxy
              exact congrArg Subtype.val (hf''Injective hxy)
          · intro x
            by_cases hx : x ∈ s
            · simp only [hx, ↓reduceDIte]
              exact hf'Mem ⟨x, hx⟩
            · simp only [hx, ↓reduceDIte]
              exact Finset.sdiff_subset
                (hf''Mem ⟨x, Finset.mem_compl.mpr hx⟩)

@[blueprint "lem:parity-averaged-small-cardinality-cut-flow-bound"
  (statement := /-- Let $G=(V,E)$ be a finite, connected, $d$-regular simple
  graph, and let $\psi>0$ satisfy $\Psi_G\geq\psi$.  Let $w$ be a
  $\sigma(\psi)$-Lipschitz positive edge-weighting.  Set
  $\mathcal A_{2K}(P_w)=\tfrac12(P_w^{2K}+P_w^{2K-1})$.  If
  $\varnothing\neq S\subseteq V$ and $2|S|\leq|V|$, then
  \[
    \frac{Q_{\mathcal A_{2K(\psi)}(P_w)}(S,V\setminus S)}{\pi_w(S)}
      \geq \frac{1}{4000}\,d^{-2K(\psi)}.
  \] -/)
  (proof := /-- Since $S$ is nonempty and $2|S|\leq|V|$, the graph has at
  least two vertices; connected regularity therefore gives $d>0$.  Put
  $K=K(\psi)$.  The inequalities
  $\log(1+\psi)\leq\psi$ and
  $K\geq2/\log(1+\psi)$, followed by Bernoulli's inequality, give
  $(1+\psi)^K\geq3$.

  Let $B\subseteq S$ consist of the vertices whose closed $K$-neighborhood is
  contained in $S$.  For a finite set
  $U\subseteq B\times\{0,1,2\}$, let $C\subseteq B$ be its set of first
  coordinates.  Then $|U|\leq3|C|$, while
  \cref{lem:small-cardinality-cut-flow-bound-neighborhood-growth} gives
  $|B_K(C)|\geq3|C|$.  Thus the family of $K$-neighborhoods indexed by the
  three copies of $B$ satisfies Hall's condition.
  By \cref{lem:small-cardinality-cut-flow-bound-hall-matching}, there is an
  injective choice of a vertex of $S$ from each of these neighborhoods.

  Every stationary mass is positive.  For each matched pair $(x,y)$,
  \cref{lem:stationary-ratio-on-short-paths} and
  $\sigma(\psi)^{2K}=e\leq11/4$ imply
  $4\pi_w(x)\leq11\pi_w(y)$.  Summing over the three copies of $B$, using
  injectivity and positivity, yields
  $12\pi_w(B)\leq11\pi_w(S)$.  Hence the complementary set
  $H=S\setminus B$ has mass at least $\pi_w(S)/12$.

  For every $x\in H$, choose $y\notin S$ with
  $\operatorname{dist}_G(x,y)\leq K\leq2K$.  The estimate
  \cref{lem:parity-averaged-transition-lower-bound} gives
  $\mathcal A_{2K}(P_w)(x,y)\geq(1/20)d^{-2K}$.
  All other summands are nonnegative by
  \cref{lem:weighted-transition-power-entry-nonnegative} and
  \cref{def:parity-averaged-power}.  Therefore
  [
    Q_{\mathcal A_{2K}(P_w)}(S,V\setminus S)
      \geq \frac1{20}d^{-2K}\pi_w(H)
      \geq \frac1{240}d^{-2K}\pi_w(S).
  ]
  The stationary mass of $S$ is positive, so division by it and
  $1/4000\leq1/240$ prove the claim. -/)
  (title := /-- Parity-averaged flow out of a cardinality-small set -/)
  (latexEnv := "lemma")]
lemma parity_averaged_small_cardinality_cut_flow_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite]
    (d : ℕ) (ψ : ℝ) (w : graph_edge_weights G)
    (hConnected : G.Connected) (hRegular : G.IsRegularOfDegree d)
    (hExpansion : ψ ≤ vertex_expansion G) (hψ : 0 < ψ)
    (hLipschitz : weight_lipschitz G (robust_lipschitz_bound ψ) w)
    (S : Finset V) (hSnonempty : S.Nonempty)
    (hScard : 2 * S.card ≤ Fintype.card V) :
    (1 / 4000) * (((d : ℝ) ^ (2 * robust_radius ψ))⁻¹) ≤
      stationary_cut_flow (stationary_distribution G w)
          (parity_averaged_power (weighted_transition G w)
            (2 * robust_radius ψ))
          S (Finset.univ \ S) /
        stationary_mass (stationary_distribution G w) S := by
  classical
  let K := robust_radius ψ
  let π := stationary_distribution G w
  let P := parity_averaged_power (weighted_transition G w) (2 * K)
  have hScardPos : 0 < S.card := Finset.card_pos.mpr hSnonempty
  have hVcard : 2 ≤ Fintype.card V := by omega
  letI : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hd : 0 < d := by
    obtain ⟨x, hx⟩ := hSnonempty
    have hxNotIsolated : ¬G.IsIsolated x :=
      hConnected.preconnected.not_isIsolated x
    have hxNeighbors : (G.neighborFinset x).Nonempty :=
      (SimpleGraph.neighborFinset_nonempty G x).2 hxNotIsolated
    have hxDegree : 0 < G.degree x := by
      exact Finset.card_pos.mpr hxNeighbors
    simpa [hRegular.degree_eq] using hxDegree
  have hlogPos : 0 < Real.log (1 + ψ) :=
    Real.log_pos (by linarith)
  have hKpos : 0 < K := by
    change 0 < robust_radius ψ
    rw [robust_radius, Nat.ceil_pos]
    exact div_pos (by norm_num) hlogPos
  have hlogLe : Real.log (1 + ψ) ≤ ψ := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + ψ by linarith)
    norm_num at h ⊢
    linarith
  have hceil : 2 / Real.log (1 + ψ) ≤ (K : ℝ) := by
    simpa [K, robust_radius] using
      (Nat.le_ceil (2 / Real.log (1 + ψ)))
  have hKlog : 2 ≤ (K : ℝ) * Real.log (1 + ψ) := by
    exact (div_le_iff₀ hlogPos).mp hceil
  have hKψ : 2 ≤ (K : ℝ) * ψ := by
    have hKnonneg : 0 ≤ (K : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hlogLe hKnonneg
    linarith
  have hThree : (3 : ℝ) ≤ (1 + ψ) ^ K := by
    have hBernoulli := one_add_mul_le_pow (show (-2 : ℝ) ≤ ψ by linarith) K
    norm_num at hBernoulli ⊢
    push_cast at hBernoulli
    nlinarith
  let Bad : Finset V :=
    S.filter fun x => closed_metric_neighborhood G K {x} ⊆ S
  have hBadSub : Bad ⊆ S := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  let N : (↥Bad × Fin 3) → Finset V := fun q =>
    closed_metric_neighborhood G K {q.1.1}
  have hNSub (q : ↥Bad × Fin 3) : N q ⊆ S := by
    have hq := (Finset.mem_filter.mp q.1.2).2
    simpa [N] using hq
  have hHall (U : Finset (↥Bad × Fin 3)) :
      U.card ≤ (U.biUnion N).card := by
    let centers : Finset V := U.image fun q => q.1.1
    have hCentersBad : centers ⊆ Bad := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨q, hqU, rfl⟩
      exact q.1.2
    have hCentersBall :
        closed_metric_neighborhood G K centers ⊆ S := by
      intro y hy
      have hy' : ∃ x ∈ centers, G.dist x y ≤ K := by
        simpa only [closed_metric_neighborhood, Finset.mem_filter,
          Finset.mem_univ, true_and] using hy
      rcases hy' with ⟨x, hxCenters, hxy⟩
      have hxBad : x ∈ Bad := hCentersBad hxCenters
      have hxProperty := (Finset.mem_filter.mp hxBad).2
      apply hxProperty
      simp only [closed_metric_neighborhood, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨x, rfl, hxy⟩
    have hGrowth :=
      small_cardinality_cut_flow_bound_neighborhood_growth G ψ hψ
        hExpansion centers S K hCentersBall hScard
    have hThreeCenters :
        (3 : ℝ) * (centers.card : ℝ) ≤
          (closed_metric_neighborhood G K centers).card := by
      calc
        (3 : ℝ) * (centers.card : ℝ) ≤
            (1 + ψ) ^ K * (centers.card : ℝ) :=
          mul_le_mul_of_nonneg_right hThree (by positivity)
        _ ≤ (closed_metric_neighborhood G K centers).card :=
          hGrowth
    have hUCenters : U.card ≤ 3 * centers.card := by
      rw [Finset.card_eq_sum_card_image (fun q => q.1.1) U]
      change (∑ x ∈ centers, (U.filter fun q => q.1.1 = x).card) ≤
        3 * centers.card
      calc
        (∑ x ∈ centers, (U.filter fun q => q.1.1 = x).card) ≤
            ∑ _x ∈ centers, 3 := by
          apply Finset.sum_le_sum
          intro x hx
          have hMaps :
              Set.MapsTo (fun q : ↥Bad × Fin 3 => q.2)
                (U.filter fun q => q.1.1 = x)
                (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) := by
            intro q hq
            simp
          have hInj :
              Set.InjOn (fun q : ↥Bad × Fin 3 => q.2)
                (U.filter fun q => q.1.1 = x) := by
            intro q hq r hr hqr
            have hqFirst := (Finset.mem_filter.mp hq).2
            have hrFirst := (Finset.mem_filter.mp hr).2
            apply Prod.ext
            · apply Subtype.ext
              exact hqFirst.trans hrFirst.symm
            · exact hqr
          have := Finset.card_le_card_of_injOn
            (fun q : ↥Bad × Fin 3 => q.2) hMaps hInj
          simpa using this
        _ = 3 * centers.card := by
          simp
          omega
    have hUnion :
        U.biUnion N = closed_metric_neighborhood G K centers := by
      ext y
      simp only [Finset.mem_biUnion, N, closed_metric_neighborhood,
        Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        centers, Finset.mem_image]
      constructor
      · rintro ⟨q, hqU, x, hx, hxy⟩
        subst x
        exact ⟨q.1.1, ⟨q, hqU, rfl⟩, hxy⟩
      · rintro ⟨x, ⟨q, hqU, hqx⟩, hxy⟩
        subst x
        exact ⟨q, hqU, q.1.1, rfl, hxy⟩
    rw [hUnion]
    have hUReal : (U.card : ℝ) ≤ 3 * (centers.card : ℝ) := by
      exact_mod_cast hUCenters
    have hCardReal :
        (U.card : ℝ) ≤
          ((closed_metric_neighborhood G K centers).card : ℝ) :=
      hUReal.trans hThreeCenters
    exact_mod_cast hCardReal
  obtain ⟨f, hfInjective, hfN⟩ :=
    small_cardinality_cut_flow_bound_hall_matching N hHall
  have hfS (q : ↥Bad × Fin 3) : f q ∈ S :=
    hNSub q (hfN q)
  have hWeightNonneg (x y : V) : 0 ≤ w.weight x y := by
    by_cases hxy : G.Adj x y
    · exact (w.positive_of_adj hxy).le
    · rw [w.zero_of_not_adj hxy]
  have hDegreePos (x : V) : 0 < weighted_degree G w x := by
    have hxDegree : 0 < G.degree x := by
      simpa [hRegular.degree_eq] using hd
    obtain ⟨y, hxy⟩ := (G.degree_pos_iff_exists_adj (v := x)).mp hxDegree
    unfold weighted_degree
    apply Finset.sum_pos'
    · intro z hz
      exact hWeightNonneg x z
    · exact ⟨y, Finset.mem_univ y, w.positive_of_adj hxy⟩
  have hTotalPos : 0 < ∑ z, weighted_degree G w z := by
    obtain ⟨x, hx⟩ := hSnonempty
    apply Finset.sum_pos'
    · intro z hz
      exact (hDegreePos z).le
    · exact ⟨x, Finset.mem_univ x, hDegreePos x⟩
  have hπPos (x : V) : 0 < π x := by
    simp only [π, stationary_distribution]
    exact div_pos (hDegreePos x) hTotalPos
  have hσpow :
      robust_lipschitz_bound ψ ^ (2 * K) = Real.exp 1 := by
    change (Real.exp (1 / (2 * (K : ℝ)))) ^ (2 * K) = Real.exp 1
    rw [← Real.exp_nat_mul]
    congr 1
    have hKne : (K : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hKpos)
    field_simp
    norm_num
  have hexpLe : Real.exp 1 ≤ (11 / 4 : ℝ) := by
    have h := Real.exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num)
      (n := 2) (by norm_num)
    norm_num at h ⊢
    linarith
  have hCompare (q : ↥Bad × Fin 3) :
      4 * π q.1.1 ≤ 11 * π (f q) := by
    have hdist : G.dist q.1.1 (f q) ≤ K := by
      have hmem : f q ∈
          closed_metric_neighborhood G K {q.1.1} := by
        simpa [N] using hfN q
      rcases (show ∃ u ∈ ({q.1.1} : Finset V),
          G.dist u (f q) ≤ K by
        simpa only [closed_metric_neighborhood, Finset.mem_filter,
          Finset.mem_univ, true_and] using hmem) with ⟨u, hu, huf⟩
      have huEq : u = q.1.1 := Finset.mem_singleton.mp hu
      subst u
      exact huf
    have hRatio := stationary_ratio_on_short_paths G d ψ w hRegular hd
      hLipschitz (hConnected _ _) hdist
    have hMul :
        π q.1.1 ≤
          robust_lipschitz_bound ψ ^ (2 * K) * π (f q) := by
      apply (div_le_iff₀ (hπPos (f q))).mp
      simpa [π, K] using hRatio.2
    have hExpMul :
        Real.exp 1 * π (f q) ≤ (11 / 4 : ℝ) * π (f q) :=
      mul_le_mul_of_nonneg_right hexpLe (hπPos (f q)).le
    rw [hσpow] at hMul
    nlinarith
  have hMatchingSum :
      4 * (∑ q : ↥Bad × Fin 3, π q.1.1) ≤
        11 * ∑ q : ↥Bad × Fin 3, π (f q) := by
    calc
      4 * (∑ q : ↥Bad × Fin 3, π q.1.1) =
          ∑ q : ↥Bad × Fin 3, 4 * π q.1.1 := by
        rw [Finset.mul_sum]
      _ ≤ ∑ q : ↥Bad × Fin 3, 11 * π (f q) :=
        Finset.sum_le_sum fun q hq => hCompare q
      _ = 11 * ∑ q : ↥Bad × Fin 3, π (f q) := by
        rw [Finset.mul_sum]
  let F : Finset V := Finset.univ.image f
  have hFSub : F ⊆ S := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
    exact hfS q
  have hImageSum :
      (∑ q : ↥Bad × Fin 3, π (f q)) = ∑ y ∈ F, π y := by
    rw [show (∑ q : ↥Bad × Fin 3, π (f q)) =
      ∑ q ∈ (Finset.univ : Finset (↥Bad × Fin 3)), π (f q) by simp]
    symm
    apply Finset.sum_image
    intro q hq r hr h
    exact hfInjective h
  have hFMass : (∑ y ∈ F, π y) ≤ stationary_mass π S := by
    simp only [stationary_mass]
    apply Finset.sum_le_sum_of_subset_of_nonneg hFSub
    intro y hyS hyF
    exact (hπPos y).le
  have hLeftSum :
      (∑ q : ↥Bad × Fin 3, π q.1.1) =
        3 * stationary_mass π Bad := by
    calc
      (∑ q : ↥Bad × Fin 3, π q.1.1) =
          ∑ x : ↥Bad, ∑ _i : Fin 3, π x.1 := by
        rw [Fintype.sum_prod_type]
      _ = ∑ x : ↥Bad, 3 * π x.1 := by
        apply Finset.sum_congr rfl
        intro x hx
        simp
      _ = ∑ x ∈ Bad, 3 * π x :=
        (Finset.sum_subtype Bad (fun x => Iff.rfl)
          (fun x => 3 * π x)).symm
      _ = 3 * stationary_mass π Bad := by
        simp only [stationary_mass, Finset.mul_sum]
  have hBadMass :
      12 * stationary_mass π Bad ≤ 11 * stationary_mass π S := by
    have hMatch :
        4 * (3 * stationary_mass π Bad) ≤
          11 * ∑ q : ↥Bad × Fin 3, π (f q) := by
      rw [← hLeftSum]
      exact hMatchingSum
    calc
      12 * stationary_mass π Bad =
          4 * (3 * stationary_mass π Bad) := by ring
      _ ≤ 11 * ∑ q : ↥Bad × Fin 3, π (f q) := hMatch
      _ = 11 * ∑ y ∈ F, π y := by rw [hImageSum]
      _ ≤ 11 * stationary_mass π S :=
        mul_le_mul_of_nonneg_left hFMass (by norm_num)
  let Good : Finset V := S \ Bad
  have hMassSplit :
      stationary_mass π Bad + stationary_mass π Good =
        stationary_mass π S := by
    simp only [stationary_mass, Good]
    rw [← Finset.sum_sdiff hBadSub]
    ring
  have hGoodMass :
      stationary_mass π S / 12 ≤ stationary_mass π Good := by
    nlinarith [hBadMass, hMassSplit]
  have hGoodWitness (x : ↥Good) :
      ∃ y ∈ Finset.univ \ S, G.dist x.1 y ≤ K := by
    have hxGood := x.2
    have hxS : x.1 ∈ S := (Finset.mem_sdiff.mp hxGood).1
    have hxNotBad : x.1 ∉ Bad := (Finset.mem_sdiff.mp hxGood).2
    have hNotSubset :
        ¬closed_metric_neighborhood G K {x.1} ⊆ S := by
      intro h
      apply hxNotBad
      exact Finset.mem_filter.mpr ⟨hxS, h⟩
    rcases Finset.not_subset.mp hNotSubset with ⟨y, hyBall, hyNotS⟩
    refine ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyNotS⟩, ?_⟩
    rcases (show ∃ u ∈ ({x.1} : Finset V), G.dist u y ≤ K by
      simpa only [closed_metric_neighborhood, Finset.mem_filter,
        Finset.mem_univ, true_and] using hyBall) with ⟨u, hu, huy⟩
    have huEq : u = x.1 := Finset.mem_singleton.mp hu
    subst u
    exact huy
  let out : ↥Good → V := fun x => (hGoodWitness x).choose
  have houtMem (x : ↥Good) : out x ∈ Finset.univ \ S :=
    (hGoodWitness x).choose_spec.1
  have houtDist (x : ↥Good) : G.dist x.1 (out x) ≤ K :=
    (hGoodWitness x).choose_spec.2
  have hPNonneg (x y : V) : 0 ≤ P x y := by
    have hEven := weighted_transition_power_entry_nonnegative G w (2 * K) x y
    have hOdd :=
      weighted_transition_power_entry_nonnegative G w (2 * K - 1) x y
    simp only [P, parity_averaged_power]
    positivity
  have hEntry (x : ↥Good) :
      (1 / 20) * (((d : ℝ) ^ (2 * K))⁻¹) ≤ P x.1 (out x) := by
    simpa [P, K] using
      parity_averaged_transition_lower_bound G d ψ w hConnected hRegular
        hd hψ hLipschitz ((houtDist x).trans (by omega))
  have hChosenFlow :
      (1 / 20) * (((d : ℝ) ^ (2 * K))⁻¹) *
          stationary_mass π Good ≤
        ∑ x : ↥Good, π x.1 * P x.1 (out x) := by
    simp only [stationary_mass]
    rw [← Finset.sum_attach Good π]
    rw [Finset.sum_coe_sort_eq_attach]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left (hEntry x) (hπPos x.1).le
  have hChosenLeCut :
      (∑ x : ↥Good, π x.1 * P x.1 (out x)) ≤
        stationary_cut_flow π P S (Finset.univ \ S) := by
    simp only [stationary_cut_flow]
    calc
      (∑ x : ↥Good, π x.1 * P x.1 (out x)) ≤
          ∑ x : ↥Good, ∑ y ∈ Finset.univ \ S,
            π x.1 * P x.1 y := by
        apply Finset.sum_le_sum
        intro x hx
        exact Finset.single_le_sum
          (fun y hy => mul_nonneg (hπPos x.1).le (hPNonneg x.1 y))
          (houtMem x)
      _ = ∑ x ∈ Good, ∑ y ∈ Finset.univ \ S, π x * P x y := by
        exact (Finset.sum_subtype Good (fun x => Iff.rfl)
          (fun x => ∑ y ∈ Finset.univ \ S, π x * P x y)).symm
      _ ≤ ∑ x ∈ S, ∑ y ∈ Finset.univ \ S, π x * P x y := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.sdiff_subset
        · intro x hxS hxGood
          apply Finset.sum_nonneg
          intro y hy
          exact mul_nonneg (hπPos x).le (hPNonneg x y)
  have hFlow :
      (1 / 240) * (((d : ℝ) ^ (2 * K))⁻¹) *
          stationary_mass π S ≤
        stationary_cut_flow π P S (Finset.univ \ S) := by
    have hD : 0 ≤ (((d : ℝ) ^ (2 * K))⁻¹) := by positivity
    have hScale :
        (1 / 20) * (((d : ℝ) ^ (2 * K))⁻¹) *
            (stationary_mass π S / 12) ≤
          (1 / 20) * (((d : ℝ) ^ (2 * K))⁻¹) *
            stationary_mass π Good :=
      mul_le_mul_of_nonneg_left hGoodMass (mul_nonneg (by norm_num) hD)
    calc
      (1 / 240) * (((d : ℝ) ^ (2 * K))⁻¹) *
          stationary_mass π S =
        (1 / 20) * (((d : ℝ) ^ (2 * K))⁻¹) *
          (stationary_mass π S / 12) := by ring
      _ ≤ (1 / 20) * (((d : ℝ) ^ (2 * K))⁻¹) *
          stationary_mass π Good := hScale
      _ ≤ ∑ x : ↥Good, π x.1 * P x.1 (out x) := hChosenFlow
      _ ≤ stationary_cut_flow π P S (Finset.univ \ S) := hChosenLeCut
  have hMassPos : 0 < stationary_mass π S := by
    simp only [stationary_mass]
    apply Finset.sum_pos'
    · intro x hx
      exact (hπPos x).le
    · obtain ⟨x, hx⟩ := hSnonempty
      exact ⟨x, hx, hπPos x⟩
  change (1 / 4000) * (((d : ℝ) ^ (2 * K))⁻¹) ≤
    stationary_cut_flow π P S (Finset.univ \ S) /
      stationary_mass π S
  apply (le_div_iff₀ hMassPos).2
  have hD : 0 ≤ (((d : ℝ) ^ (2 * K))⁻¹) := by positivity
  calc
    (1 / 4000) * (((d : ℝ) ^ (2 * K))⁻¹) *
        stationary_mass π S ≤
      (1 / 240) * (((d : ℝ) ^ (2 * K))⁻¹) *
        stationary_mass π S := by
      have hMassNonneg := hMassPos.le
      nlinarith
    _ ≤ stationary_cut_flow π P S (Finset.univ \ S) := hFlow

@[blueprint "lem:small-cardinality-power-cut-flow-bound"
  (statement := /-- Let $G=(V,E)$ be a finite, connected, $d$-regular simple
  graph, let $\psi>0$ satisfy $\Psi_G\geq\psi$, and let $w$ be a
  $\sigma(\psi)$-Lipschitz positive edge-weighting.  Assume that, whenever
  $x,y\in V$ satisfy $\operatorname{dist}_G(x,y)\leq2K(\psi)$,
  \[
    P_w^{2K(\psi)}(x,y)\geq
      \frac1{20}d^{-2K(\psi)}.
  \]
  If $\varnothing\neq S\subseteq V$ and $2|S|\leq|V|$, then
  \[
    \frac{Q_{P_w^{2K(\psi)}}(S,V\setminus S)}{\pi_w(S)}
      \geq \frac1{4000}d^{-2K(\psi)}.
  \] -/)
  (proof := /-- Put $K=K(\psi)$.  Since $S$ is nonempty and has at most half
  the vertices, connected regularity gives $d>0$.  The definition
  \cref{def:robust-radius}, the inequality $\log(1+\psi)\leq\psi$, and
  Bernoulli's inequality imply $(1+\psi)^K\geq3$.

  Let $B\subseteq S$ consist of those vertices whose closed $K$-neighborhood
  is contained in $S$.  For each finite subset $U$ of
  $B\times\{0,1,2\}$, let $C\subseteq B$ be its projection onto the first
  coordinate.  Then $|U|\leq3|C|$, whereas
  \cref{lem:small-cardinality-cut-flow-bound-neighborhood-growth} gives
  $|B_K(C)|\geq3|C|$.  Hence the $K$-neighborhoods indexed by the three
  copies of $B$ satisfy Hall's condition.  By
  \cref{lem:small-cardinality-cut-flow-bound-hall-matching}, they admit an
  injective system of representatives in $S$.

  For every matched pair $(x,y)$,
  \cref{lem:stationary-ratio-on-short-paths} and
  $\sigma(\psi)^{2K}=e\leq11/4$ give
  $4\pi_w(x)\leq11\pi_w(y)$.  Summing over the three copies of $B$ and using
  injectivity gives $12\pi_w(B)\leq11\pi_w(S)$.  Thus
  $H=S\setminus B$ satisfies $\pi_w(H)\geq\pi_w(S)/12$.

  For every $x\in H$, choose $y\notin S$ with
  $\operatorname{dist}_G(x,y)\leq K\leq2K$.  The assumed even-time
  accessibility estimate gives
  $P_w^{2K}(x,y)\geq(1/20)d^{-2K}$, while all remaining summands are
  nonnegative by
  \cref{lem:weighted-transition-power-entry-nonnegative}.  Therefore
  \[
    Q_{P_w^{2K}}(S,V\setminus S)
      \geq\frac1{20}d^{-2K}\pi_w(H)
      \geq\frac1{240}d^{-2K}\pi_w(S).
  \]
  Positivity of $\pi_w(S)$ permits division, and
  $1/4000\leq1/240$ proves the assertion. -/)
  (title := /-- Pure-power flow out of a cardinality-small set -/)
  (latexEnv := "lemma")]
lemma small_cardinality_power_cut_flow_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite]
    (d : ℕ) (ψ : ℝ) (w : graph_edge_weights G)
    (hConnected : G.Connected) (hRegular : G.IsRegularOfDegree d)
    (hExpansion : ψ ≤ vertex_expansion G) (hψ : 0 < ψ)
    (hLipschitz : weight_lipschitz G (robust_lipschitz_bound ψ) w)
    (hEvenPowerLower : ∀ x y : V,
      G.dist x y ≤ 2 * robust_radius ψ →
        (1 / 20) * (((d : ℝ) ^ (2 * robust_radius ψ))⁻¹) ≤
          (weighted_transition G w ^ (2 * robust_radius ψ)) x y)
    (S : Finset V) (hSnonempty : S.Nonempty)
    (hScard : 2 * S.card ≤ Fintype.card V) :
    (1 / 4000) * (((d : ℝ) ^ (2 * robust_radius ψ))⁻¹) ≤
      stationary_cut_flow (stationary_distribution G w)
          (weighted_transition G w ^ (2 * robust_radius ψ))
          S (Finset.univ \ S) /
        stationary_mass (stationary_distribution G w) S := by
  classical
  let K := robust_radius ψ
  let π := stationary_distribution G w
  let P := weighted_transition G w ^ (2 * K)
  have hScardPos : 0 < S.card := Finset.card_pos.mpr hSnonempty
  have hVcard : 2 ≤ Fintype.card V := by omega
  letI : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hd : 0 < d := by
    obtain ⟨x, hx⟩ := hSnonempty
    have hxNotIsolated : ¬G.IsIsolated x :=
      hConnected.preconnected.not_isIsolated x
    have hxNeighbors : (G.neighborFinset x).Nonempty :=
      (SimpleGraph.neighborFinset_nonempty G x).2 hxNotIsolated
    have hxDegree : 0 < G.degree x := by
      exact Finset.card_pos.mpr hxNeighbors
    simpa [hRegular.degree_eq] using hxDegree
  have hlogPos : 0 < Real.log (1 + ψ) :=
    Real.log_pos (by linarith)
  have hKpos : 0 < K := by
    change 0 < robust_radius ψ
    rw [robust_radius, Nat.ceil_pos]
    exact div_pos (by norm_num) hlogPos
  have hlogLe : Real.log (1 + ψ) ≤ ψ := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + ψ by linarith)
    norm_num at h ⊢
    linarith
  have hceil : 2 / Real.log (1 + ψ) ≤ (K : ℝ) := by
    simpa [K, robust_radius] using
      (Nat.le_ceil (2 / Real.log (1 + ψ)))
  have hKlog : 2 ≤ (K : ℝ) * Real.log (1 + ψ) := by
    exact (div_le_iff₀ hlogPos).mp hceil
  have hKψ : 2 ≤ (K : ℝ) * ψ := by
    have hKnonneg : 0 ≤ (K : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hlogLe hKnonneg
    linarith
  have hThree : (3 : ℝ) ≤ (1 + ψ) ^ K := by
    have hBernoulli := one_add_mul_le_pow (show (-2 : ℝ) ≤ ψ by linarith) K
    norm_num at hBernoulli ⊢
    push_cast at hBernoulli
    nlinarith
  let Bad : Finset V :=
    S.filter fun x => closed_metric_neighborhood G K {x} ⊆ S
  have hBadSub : Bad ⊆ S := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  let N : (↥Bad × Fin 3) → Finset V := fun q =>
    closed_metric_neighborhood G K {q.1.1}
  have hNSub (q : ↥Bad × Fin 3) : N q ⊆ S := by
    have hq := (Finset.mem_filter.mp q.1.2).2
    simpa [N] using hq
  have hHall (U : Finset (↥Bad × Fin 3)) :
      U.card ≤ (U.biUnion N).card := by
    let centers : Finset V := U.image fun q => q.1.1
    have hCentersBad : centers ⊆ Bad := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨q, hqU, rfl⟩
      exact q.1.2
    have hCentersBall :
        closed_metric_neighborhood G K centers ⊆ S := by
      intro y hy
      have hy' : ∃ x ∈ centers, G.dist x y ≤ K := by
        simpa only [closed_metric_neighborhood, Finset.mem_filter,
          Finset.mem_univ, true_and] using hy
      rcases hy' with ⟨x, hxCenters, hxy⟩
      have hxBad : x ∈ Bad := hCentersBad hxCenters
      have hxProperty := (Finset.mem_filter.mp hxBad).2
      apply hxProperty
      simp only [closed_metric_neighborhood, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨x, rfl, hxy⟩
    have hGrowth :=
      small_cardinality_cut_flow_bound_neighborhood_growth G ψ hψ
        hExpansion centers S K hCentersBall hScard
    have hThreeCenters :
        (3 : ℝ) * (centers.card : ℝ) ≤
          (closed_metric_neighborhood G K centers).card := by
      calc
        (3 : ℝ) * (centers.card : ℝ) ≤
            (1 + ψ) ^ K * (centers.card : ℝ) :=
          mul_le_mul_of_nonneg_right hThree (by positivity)
        _ ≤ (closed_metric_neighborhood G K centers).card :=
          hGrowth
    have hUCenters : U.card ≤ 3 * centers.card := by
      rw [Finset.card_eq_sum_card_image (fun q => q.1.1) U]
      change (∑ x ∈ centers, (U.filter fun q => q.1.1 = x).card) ≤
        3 * centers.card
      calc
        (∑ x ∈ centers, (U.filter fun q => q.1.1 = x).card) ≤
            ∑ _x ∈ centers, 3 := by
          apply Finset.sum_le_sum
          intro x hx
          have hMaps :
              Set.MapsTo (fun q : ↥Bad × Fin 3 => q.2)
                (U.filter fun q => q.1.1 = x)
                (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)) := by
            intro q hq
            simp
          have hInj :
              Set.InjOn (fun q : ↥Bad × Fin 3 => q.2)
                (U.filter fun q => q.1.1 = x) := by
            intro q hq r hr hqr
            have hqFirst := (Finset.mem_filter.mp hq).2
            have hrFirst := (Finset.mem_filter.mp hr).2
            apply Prod.ext
            · apply Subtype.ext
              exact hqFirst.trans hrFirst.symm
            · exact hqr
          have := Finset.card_le_card_of_injOn
            (fun q : ↥Bad × Fin 3 => q.2) hMaps hInj
          simpa using this
        _ = 3 * centers.card := by
          simp
          omega
    have hUnion :
        U.biUnion N = closed_metric_neighborhood G K centers := by
      ext y
      simp only [Finset.mem_biUnion, N, closed_metric_neighborhood,
        Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        centers, Finset.mem_image]
      constructor
      · rintro ⟨q, hqU, x, hx, hxy⟩
        subst x
        exact ⟨q.1.1, ⟨q, hqU, rfl⟩, hxy⟩
      · rintro ⟨x, ⟨q, hqU, hqx⟩, hxy⟩
        subst x
        exact ⟨q, hqU, q.1.1, rfl, hxy⟩
    rw [hUnion]
    have hUReal : (U.card : ℝ) ≤ 3 * (centers.card : ℝ) := by
      exact_mod_cast hUCenters
    have hCardReal :
        (U.card : ℝ) ≤
          ((closed_metric_neighborhood G K centers).card : ℝ) :=
      hUReal.trans hThreeCenters
    exact_mod_cast hCardReal
  obtain ⟨f, hfInjective, hfN⟩ :=
    small_cardinality_cut_flow_bound_hall_matching N hHall
  have hfS (q : ↥Bad × Fin 3) : f q ∈ S :=
    hNSub q (hfN q)
  have hWeightNonneg (x y : V) : 0 ≤ w.weight x y := by
    by_cases hxy : G.Adj x y
    · exact (w.positive_of_adj hxy).le
    · rw [w.zero_of_not_adj hxy]
  have hDegreePos (x : V) : 0 < weighted_degree G w x := by
    have hxDegree : 0 < G.degree x := by
      simpa [hRegular.degree_eq] using hd
    obtain ⟨y, hxy⟩ := (G.degree_pos_iff_exists_adj (v := x)).mp hxDegree
    unfold weighted_degree
    apply Finset.sum_pos'
    · intro z hz
      exact hWeightNonneg x z
    · exact ⟨y, Finset.mem_univ y, w.positive_of_adj hxy⟩
  have hTotalPos : 0 < ∑ z, weighted_degree G w z := by
    obtain ⟨x, hx⟩ := hSnonempty
    apply Finset.sum_pos'
    · intro z hz
      exact (hDegreePos z).le
    · exact ⟨x, Finset.mem_univ x, hDegreePos x⟩
  have hπPos (x : V) : 0 < π x := by
    simp only [π, stationary_distribution]
    exact div_pos (hDegreePos x) hTotalPos
  have hσpow :
      robust_lipschitz_bound ψ ^ (2 * K) = Real.exp 1 := by
    change (Real.exp (1 / (2 * (K : ℝ)))) ^ (2 * K) = Real.exp 1
    rw [← Real.exp_nat_mul]
    congr 1
    have hKne : (K : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hKpos)
    field_simp
    norm_num
  have hexpLe : Real.exp 1 ≤ (11 / 4 : ℝ) := by
    have h := Real.exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num)
      (n := 2) (by norm_num)
    norm_num at h ⊢
    linarith
  have hCompare (q : ↥Bad × Fin 3) :
      4 * π q.1.1 ≤ 11 * π (f q) := by
    have hdist : G.dist q.1.1 (f q) ≤ K := by
      have hmem : f q ∈
          closed_metric_neighborhood G K {q.1.1} := by
        simpa [N] using hfN q
      rcases (show ∃ u ∈ ({q.1.1} : Finset V),
          G.dist u (f q) ≤ K by
        simpa only [closed_metric_neighborhood, Finset.mem_filter,
          Finset.mem_univ, true_and] using hmem) with ⟨u, hu, huf⟩
      have huEq : u = q.1.1 := Finset.mem_singleton.mp hu
      subst u
      exact huf
    have hRatio := stationary_ratio_on_short_paths G d ψ w hRegular hd
      hLipschitz (hConnected _ _) hdist
    have hMul :
        π q.1.1 ≤
          robust_lipschitz_bound ψ ^ (2 * K) * π (f q) := by
      apply (div_le_iff₀ (hπPos (f q))).mp
      simpa [π, K] using hRatio.2
    have hExpMul :
        Real.exp 1 * π (f q) ≤ (11 / 4 : ℝ) * π (f q) :=
      mul_le_mul_of_nonneg_right hexpLe (hπPos (f q)).le
    rw [hσpow] at hMul
    nlinarith
  have hMatchingSum :
      4 * (∑ q : ↥Bad × Fin 3, π q.1.1) ≤
        11 * ∑ q : ↥Bad × Fin 3, π (f q) := by
    calc
      4 * (∑ q : ↥Bad × Fin 3, π q.1.1) =
          ∑ q : ↥Bad × Fin 3, 4 * π q.1.1 := by
        rw [Finset.mul_sum]
      _ ≤ ∑ q : ↥Bad × Fin 3, 11 * π (f q) :=
        Finset.sum_le_sum fun q hq => hCompare q
      _ = 11 * ∑ q : ↥Bad × Fin 3, π (f q) := by
        rw [Finset.mul_sum]
  let F : Finset V := Finset.univ.image f
  have hFSub : F ⊆ S := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
    exact hfS q
  have hImageSum :
      (∑ q : ↥Bad × Fin 3, π (f q)) = ∑ y ∈ F, π y := by
    rw [show (∑ q : ↥Bad × Fin 3, π (f q)) =
      ∑ q ∈ (Finset.univ : Finset (↥Bad × Fin 3)), π (f q) by simp]
    symm
    apply Finset.sum_image
    intro q hq r hr h
    exact hfInjective h
  have hFMass : (∑ y ∈ F, π y) ≤ stationary_mass π S := by
    simp only [stationary_mass]
    apply Finset.sum_le_sum_of_subset_of_nonneg hFSub
    intro y hyS hyF
    exact (hπPos y).le
  have hLeftSum :
      (∑ q : ↥Bad × Fin 3, π q.1.1) =
        3 * stationary_mass π Bad := by
    calc
      (∑ q : ↥Bad × Fin 3, π q.1.1) =
          ∑ x : ↥Bad, ∑ _i : Fin 3, π x.1 := by
        rw [Fintype.sum_prod_type]
      _ = ∑ x : ↥Bad, 3 * π x.1 := by
        apply Finset.sum_congr rfl
        intro x hx
        simp
      _ = ∑ x ∈ Bad, 3 * π x :=
        (Finset.sum_subtype Bad (fun x => Iff.rfl)
          (fun x => 3 * π x)).symm
      _ = 3 * stationary_mass π Bad := by
        simp only [stationary_mass, Finset.mul_sum]
  have hBadMass :
      12 * stationary_mass π Bad ≤ 11 * stationary_mass π S := by
    have hMatch :
        4 * (3 * stationary_mass π Bad) ≤
          11 * ∑ q : ↥Bad × Fin 3, π (f q) := by
      rw [← hLeftSum]
      exact hMatchingSum
    calc
      12 * stationary_mass π Bad =
          4 * (3 * stationary_mass π Bad) := by ring
      _ ≤ 11 * ∑ q : ↥Bad × Fin 3, π (f q) := hMatch
      _ = 11 * ∑ y ∈ F, π y := by rw [hImageSum]
      _ ≤ 11 * stationary_mass π S :=
        mul_le_mul_of_nonneg_left hFMass (by norm_num)
  let Good : Finset V := S \ Bad
  have hMassSplit :
      stationary_mass π Bad + stationary_mass π Good =
        stationary_mass π S := by
    simp only [stationary_mass, Good]
    rw [← Finset.sum_sdiff hBadSub]
    ring
  have hGoodMass :
      stationary_mass π S / 12 ≤ stationary_mass π Good := by
    nlinarith [hBadMass, hMassSplit]
  have hGoodWitness (x : ↥Good) :
      ∃ y ∈ Finset.univ \ S, G.dist x.1 y ≤ K := by
    have hxGood := x.2
    have hxS : x.1 ∈ S := (Finset.mem_sdiff.mp hxGood).1
    have hxNotBad : x.1 ∉ Bad := (Finset.mem_sdiff.mp hxGood).2
    have hNotSubset :
        ¬closed_metric_neighborhood G K {x.1} ⊆ S := by
      intro h
      apply hxNotBad
      exact Finset.mem_filter.mpr ⟨hxS, h⟩
    rcases Finset.not_subset.mp hNotSubset with ⟨y, hyBall, hyNotS⟩
    refine ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyNotS⟩, ?_⟩
    rcases (show ∃ u ∈ ({x.1} : Finset V), G.dist u y ≤ K by
      simpa only [closed_metric_neighborhood, Finset.mem_filter,
        Finset.mem_univ, true_and] using hyBall) with ⟨u, hu, huy⟩
    have huEq : u = x.1 := Finset.mem_singleton.mp hu
    subst u
    exact huy
  let out : ↥Good → V := fun x => (hGoodWitness x).choose
  have houtMem (x : ↥Good) : out x ∈ Finset.univ \ S :=
    (hGoodWitness x).choose_spec.1
  have houtDist (x : ↥Good) : G.dist x.1 (out x) ≤ K :=
    (hGoodWitness x).choose_spec.2
  have hPNonneg (x y : V) : 0 ≤ P x y := by
    simpa [P] using
      weighted_transition_power_entry_nonnegative G w (2 * K) x y
  have hEntry (x : ↥Good) :
      (1 / 20) * (((d : ℝ) ^ (2 * K))⁻¹) ≤ P x.1 (out x) := by
    simpa [P, K] using
      hEvenPowerLower x.1 (out x) ((houtDist x).trans (by omega))
  have hChosenFlow :
      (1 / 20) * (((d : ℝ) ^ (2 * K))⁻¹) *
          stationary_mass π Good ≤
        ∑ x : ↥Good, π x.1 * P x.1 (out x) := by
    simp only [stationary_mass]
    rw [← Finset.sum_attach Good π]
    rw [Finset.sum_coe_sort_eq_attach]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left (hEntry x) (hπPos x.1).le
  have hChosenLeCut :
      (∑ x : ↥Good, π x.1 * P x.1 (out x)) ≤
        stationary_cut_flow π P S (Finset.univ \ S) := by
    simp only [stationary_cut_flow]
    calc
      (∑ x : ↥Good, π x.1 * P x.1 (out x)) ≤
          ∑ x : ↥Good, ∑ y ∈ Finset.univ \ S,
            π x.1 * P x.1 y := by
        apply Finset.sum_le_sum
        intro x hx
        exact Finset.single_le_sum
          (fun y hy => mul_nonneg (hπPos x.1).le (hPNonneg x.1 y))
          (houtMem x)
      _ = ∑ x ∈ Good, ∑ y ∈ Finset.univ \ S, π x * P x y := by
        exact (Finset.sum_subtype Good (fun x => Iff.rfl)
          (fun x => ∑ y ∈ Finset.univ \ S, π x * P x y)).symm
      _ ≤ ∑ x ∈ S, ∑ y ∈ Finset.univ \ S, π x * P x y := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.sdiff_subset
        · intro x hxS hxGood
          apply Finset.sum_nonneg
          intro y hy
          exact mul_nonneg (hπPos x).le (hPNonneg x y)
  have hFlow :
      (1 / 240) * (((d : ℝ) ^ (2 * K))⁻¹) *
          stationary_mass π S ≤
        stationary_cut_flow π P S (Finset.univ \ S) := by
    have hD : 0 ≤ (((d : ℝ) ^ (2 * K))⁻¹) := by positivity
    have hScale :
        (1 / 20) * (((d : ℝ) ^ (2 * K))⁻¹) *
            (stationary_mass π S / 12) ≤
          (1 / 20) * (((d : ℝ) ^ (2 * K))⁻¹) *
            stationary_mass π Good :=
      mul_le_mul_of_nonneg_left hGoodMass (mul_nonneg (by norm_num) hD)
    calc
      (1 / 240) * (((d : ℝ) ^ (2 * K))⁻¹) *
          stationary_mass π S =
        (1 / 20) * (((d : ℝ) ^ (2 * K))⁻¹) *
          (stationary_mass π S / 12) := by ring
      _ ≤ (1 / 20) * (((d : ℝ) ^ (2 * K))⁻¹) *
          stationary_mass π Good := hScale
      _ ≤ ∑ x : ↥Good, π x.1 * P x.1 (out x) := hChosenFlow
      _ ≤ stationary_cut_flow π P S (Finset.univ \ S) := hChosenLeCut
  have hMassPos : 0 < stationary_mass π S := by
    simp only [stationary_mass]
    apply Finset.sum_pos'
    · intro x hx
      exact (hπPos x).le
    · obtain ⟨x, hx⟩ := hSnonempty
      exact ⟨x, hx, hπPos x⟩
  change (1 / 4000) * (((d : ℝ) ^ (2 * K))⁻¹) ≤
    stationary_cut_flow π P S (Finset.univ \ S) /
      stationary_mass π S
  apply (le_div_iff₀ hMassPos).2
  have hD : 0 ≤ (((d : ℝ) ^ (2 * K))⁻¹) := by positivity
  calc
    (1 / 4000) * (((d : ℝ) ^ (2 * K))⁻¹) *
        stationary_mass π S ≤
      (1 / 240) * (((d : ℝ) ^ (2 * K))⁻¹) *
        stationary_mass π S := by
      have hMassNonneg := hMassPos.le
      nlinarith
    _ ≤ stationary_cut_flow π P S (Finset.univ \ S) := hFlow

@[blueprint "lem:weighted-cut-flow-symmetry"
  (statement := /-- Let $G$ be a simple graph on a finite vertex set $V$, and let
  $w:V\times V\to\mathbb{R}$ be symmetric, strictly positive on adjacent pairs, and
  zero on nonadjacent pairs.  For every $m\in\mathbb{N}$ and every $S\subseteq V$,
  \[
    Q_{P_w^m}(S,V\setminus S)
      =Q_{P_w^m}(V\setminus S,S).
  \] -/)
  (proof := /-- By \cref{def:graph-edge-weights}, every edge weight is
  nonnegative.  Hence each weighted degree in \cref{def:weighted-degree} is
  nonnegative, and an endpoint of an edge has positive weighted degree; in that
  case the total weighted degree is positive as well.  If $x=y$, the two sides
  of the one-step detailed-balance identity coincide.  If $x\neq y$ and $x$ is
  adjacent to $y$, expanding \cref{def:weighted-transition,
  def:stationary-distribution}, cancelling the positive degrees and total
  degree, and using symmetry of $w$ gives
  $\pi_w(x)P_w(x,y)=\pi_w(y)P_w(y,x)$.  If the vertices are not adjacent, both
  sides instead vanish.  Induction on $n$, using the formula for matrix
  multiplication together with the one-step identity at the induction step,
  therefore gives
  $\pi_w(x)P_w^n(x,y)=\pi_w(y)P_w^n(y,x)$ for all $n\in\mathbb N$.
  Finally, expand \cref{def:stationary-cut-flow}, apply this powered identity
  to every pair $(x,y)\in S\times(V\setminus S)$, and exchange the two finite
  sums. -/)
  (title := /-- Symmetry of stationary cut flow -/)
  (latexEnv := "lemma")]
lemma weighted_cut_flow_symmetry {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (w : graph_edge_weights G) (m : ℕ) (S : Finset V) :
    stationary_cut_flow (stationary_distribution G w)
        (weighted_transition G w ^ m) S (Finset.univ \ S) =
      stationary_cut_flow (stationary_distribution G w)
        (weighted_transition G w ^ m) (Finset.univ \ S) S := by
  classical
  have hweight_nonneg (x y : V) : 0 ≤ w.weight x y := by
    by_cases hxy : G.Adj x y
    · exact (w.positive_of_adj hxy).le
    · rw [w.zero_of_not_adj hxy]
  have hdegree_nonneg (x : V) : 0 ≤ weighted_degree G w x := by
    unfold weighted_degree
    exact Finset.sum_nonneg fun y _ ↦ hweight_nonneg x y
  have hdegree_pos {x y : V} (hxy : G.Adj x y) : 0 < weighted_degree G w x := by
    unfold weighted_degree
    exact Finset.sum_pos' (fun z _ ↦ hweight_nonneg x z)
      ⟨y, Finset.mem_univ y, w.positive_of_adj hxy⟩
  have hbalance (x y : V) :
      stationary_distribution G w x * weighted_transition G w x y =
        stationary_distribution G w y * weighted_transition G w y x := by
    by_cases hxy : x = y
    · subst y
      rfl
    · by_cases hadj : G.Adj x y
      · have hdx : weighted_degree G w x ≠ 0 := (hdegree_pos hadj).ne'
        have hdy : weighted_degree G w y ≠ 0 := (hdegree_pos hadj.symm).ne'
        have htotal : 0 < ∑ z, weighted_degree G w z :=
          Finset.sum_pos' (fun z _ ↦ hdegree_nonneg z)
            ⟨x, Finset.mem_univ x, hdegree_pos hadj⟩
        simp only [stationary_distribution, weighted_transition, hxy, Ne.symm hxy, if_false]
        rw [w.symmetric x y]
        field_simp [hdx, hdy, htotal.ne'] <;> ring
      · have hnotadj : ¬G.Adj y x := fun hyx ↦ hadj hyx.symm
        simp [weighted_transition, hxy, Ne.symm hxy, hnotadj, w.zero_of_not_adj hadj,
          w.zero_of_not_adj hnotadj]
  have hpower : ∀ (n : ℕ) (x y : V),
      stationary_distribution G w x * (weighted_transition G w ^ n) x y =
        stationary_distribution G w y * (weighted_transition G w ^ n) y x := by
    intro n
    induction n with
    | zero =>
        intro x y
        by_cases hxy : x = y
        · subst y
          rfl
        · simp [hxy, Ne.symm hxy]
    | succ n ih =>
        intro x y
        conv_lhs => rw [pow_succ]
        conv_rhs => rw [pow_succ']
        rw [Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        calc
          stationary_distribution G w x *
                ((weighted_transition G w ^ n) x z * weighted_transition G w z y) =
              (stationary_distribution G w x *
                (weighted_transition G w ^ n) x z) * weighted_transition G w z y := by
            ring
          _ = (stationary_distribution G w z *
                (weighted_transition G w ^ n) z x) * weighted_transition G w z y := by
            rw [ih]
          _ = (stationary_distribution G w z * weighted_transition G w z y) *
                (weighted_transition G w ^ n) z x := by
            ring
          _ = (stationary_distribution G w y * weighted_transition G w y z) *
                (weighted_transition G w ^ n) z x := by
            rw [hbalance]
          _ = stationary_distribution G w y *
                (weighted_transition G w y z * (weighted_transition G w ^ n) z x) := by
            ring
  unfold stationary_cut_flow
  calc
    (∑ x ∈ S, ∑ y ∈ Finset.univ \ S,
        stationary_distribution G w x * (weighted_transition G w ^ m) x y) =
      ∑ x ∈ S, ∑ y ∈ Finset.univ \ S,
        stationary_distribution G w y * (weighted_transition G w ^ m) y x := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          exact hpower m x y
    _ = ∑ y ∈ Finset.univ \ S, ∑ x ∈ S,
        stationary_distribution G w y * (weighted_transition G w ^ m) y x := by
          rw [Finset.sum_comm]

@[blueprint "lem:parity-averaged-cut-flow-symmetry"
  (statement := /-- Let $G$ be a simple graph on a finite vertex set $V$, let
  $w$ be a positive edge-weighting, let $m\in\mathbb N$, and let
  $S\subseteq V$.  Then
  \[
    Q_{\mathcal A_m(P_w)}(S,V\setminus S)
      =Q_{\mathcal A_m(P_w)}(V\setminus S,S).
  \] -/)
  (proof := /-- Expand \cref{def:parity-averaged-power} and
  \cref{def:stationary-cut-flow}.  The flow for the averaged kernel is the
  arithmetic mean of the flows for $P_w^m$ and $P_w^{m-1}$.  Apply
  \cref{lem:weighted-cut-flow-symmetry} separately to these two powers and
  average the resulting equalities. -/)
  (title := /-- Symmetry of parity-averaged stationary cut flow -/)
  (latexEnv := "lemma")]
lemma parity_averaged_cut_flow_symmetry {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (w : graph_edge_weights G)
    (m : ℕ) (S : Finset V) :
    stationary_cut_flow (stationary_distribution G w)
        (parity_averaged_power (weighted_transition G w) m)
        S (Finset.univ \ S) =
      stationary_cut_flow (stationary_distribution G w)
        (parity_averaged_power (weighted_transition G w) m)
        (Finset.univ \ S) S := by
  classical
  have h₁ := weighted_cut_flow_symmetry G w m S
  have h₂ := weighted_cut_flow_symmetry G w (m - 1) S
  simp only [stationary_cut_flow, parity_averaged_power] at *
  simp_rw [show ∀ a b c : ℝ, a * ((b + c) / 2) =
    (a * b) / 2 + (a * c) / 2 by intros; ring, Finset.sum_add_distrib]
  simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
  rw [h₁, h₂]

@[blueprint "lem:parity-averaged-conductance-bound-aux"
  (statement := /-- Let $G=(V,E)$ be a finite, connected, $d$-regular simple
  graph, let $\psi>0$ satisfy $\Psi_G\geq\psi$, and let $w$ be a
  $\sigma(\psi)$-Lipschitz positive edge-weighting.  Then
  \[
    \Phi_{\mathcal A_{2K(\psi)}(P_w)}\geq
      \frac{1}{4000}\,d^{-2K(\psi)}.
  \] -/)
  (proof := /-- Put $K=K(\psi)$ and $A=\mathcal A_{2K}(P_w)$.  Since
  $\psi>0$ and $\psi\leq\Psi_G$, \cref{def:vertex-expansion} implies
  $|V|\geq2$: if $|V|<2$, the family defining $\Psi_G$ is empty and
  $\Psi_G=0$.  Connected $d$-regularity then gives $d>0$, so every vertex has
  positive weighted degree.  By \cref{def:stationary-distribution} and
  \cref{def:stationary-mass}, every vertex has positive stationary mass,
  $\pi_w(V)=1$, and
  \[
    \pi_w(V\setminus S)=1-\pi_w(S)
  \]
  for every $S\subseteq V$.  The family in
  \cref{def:markov-conductance} is nonempty: for any $x\in V$, either
  $\pi_w(\{x\})\leq1/2$, or its nonempty complement has stationary mass at
  most $1/2$.

  Now fix a nonempty $S\subseteq V$ satisfying
  $0<\pi_w(S)\leq1/2$.  If $2|S|\leq|V|$, then
  \cref{lem:parity-averaged-small-cardinality-cut-flow-bound} gives
  \[
    \frac{Q_A(S,V\setminus S)}{\pi_w(S)}
      \geq\frac{1}{4000}d^{-2K}.
  \]
  Otherwise set $T=V\setminus S$.  Then $T$ is nonempty,
  $2|T|\leq|V|$, and
  $\pi_w(T)=1-\pi_w(S)\geq\pi_w(S)>0$.  Applying the same lemma to $T$
  yields
  \[
    \frac{Q_A(T,S)}{\pi_w(T)}
      \geq\frac{1}{4000}d^{-2K}.
  \]
  The lower bound on the right is nonnegative, so this inequality and
  $\pi_w(T)>0$ show that $Q_A(T,S)\geq0$.  By
  \cref{lem:parity-averaged-cut-flow-symmetry},
  $Q_A(T,S)=Q_A(S,T)$.  Since $\pi_w(S)\leq\pi_w(T)$, division by the
  smaller positive denominator gives
  \[
    \frac{Q_A(S,T)}{\pi_w(S)}
      \geq\frac{Q_A(T,S)}{\pi_w(T)}
      \geq\frac{1}{4000}d^{-2K}.
  \]
  Thus every member of the nonempty family defining the infimum in
  \cref{def:markov-conductance} is bounded below by the asserted constant,
  which proves the claim. -/)
  (title := /-- Conductance of the parity-averaged weighted walk -/)
  (latexEnv := "lemma")]
lemma parity_averaged_conductance_bound_aux {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite]
    (d : ℕ) (ψ : ℝ) (w : graph_edge_weights G)
    (hConnected : G.Connected) (hRegular : G.IsRegularOfDegree d)
    (hExpansion : ψ ≤ vertex_expansion G) (hψ : 0 < ψ)
    (hLipschitz : weight_lipschitz G (robust_lipschitz_bound ψ) w) :
    (1 / 4000) * (((d : ℝ) ^ (2 * robust_radius ψ))⁻¹) ≤
      markov_conductance (stationary_distribution G w)
        (parity_averaged_power (weighted_transition G w)
          (2 * robust_radius ψ)) := by
  classical
  let π := stationary_distribution G w
  let A := parity_averaged_power (weighted_transition G w)
    (2 * robust_radius ψ)
  let c : ℝ := (1 / 4000) * (((d : ℝ) ^ (2 * robust_radius ψ))⁻¹)
  have hVcard : 2 ≤ Fintype.card V := by
    by_contra h
    have hVsmall : Fintype.card V < 2 := by omega
    have hEmpty : {r : ℝ | ∃ S : Finset V, S.Nonempty ∧
        2 * S.card ≤ Fintype.card V ∧
        r = (external_vertex_boundary G S).card / (S.card : ℝ)} = ∅ := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨S, hSnonempty, hScard, -⟩
      have hSpos : 0 < S.card := Finset.card_pos.mpr hSnonempty
      have hSle : S.card ≤ Fintype.card V := Finset.card_le_univ S
      omega
    have hExpansionZero : vertex_expansion G = 0 := by
      simp [vertex_expansion, hEmpty]
    rw [hExpansionZero] at hExpansion
    linarith
  letI : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Nonempty V := hConnected.nonempty
  let x : V := Classical.choice (inferInstance : Nonempty V)
  have hd : 0 < d := by
    have hxNotIsolated : ¬G.IsIsolated x :=
      hConnected.preconnected.not_isIsolated x
    have hxNeighbors : (G.neighborFinset x).Nonempty :=
      (SimpleGraph.neighborFinset_nonempty G x).2 hxNotIsolated
    have hxDegree : 0 < G.degree x :=
      Finset.card_pos.mpr hxNeighbors
    simpa [hRegular.degree_eq] using hxDegree
  have hWeightNonneg (u v : V) : 0 ≤ w.weight u v := by
    by_cases huv : G.Adj u v
    · exact (w.positive_of_adj huv).le
    · rw [w.zero_of_not_adj huv]
  have hDegreePos (u : V) : 0 < weighted_degree G w u := by
    have huDegree : 0 < G.degree u := by
      simpa [hRegular.degree_eq] using hd
    obtain ⟨v, huv⟩ := (G.degree_pos_iff_exists_adj (v := u)).mp huDegree
    unfold weighted_degree
    apply Finset.sum_pos'
    · intro z hz
      exact hWeightNonneg u z
    · exact ⟨v, Finset.mem_univ v, w.positive_of_adj huv⟩
  have hTotalPos : 0 < ∑ z, weighted_degree G w z := by
    apply Finset.sum_pos
    · intro z hz
      exact hDegreePos z
    · exact ⟨x, Finset.mem_univ x⟩
  have hπPos (u : V) : 0 < π u := by
    simp only [π, stationary_distribution]
    exact div_pos (hDegreePos u) hTotalPos
  have hMassPos (S : Finset V) (hS : S.Nonempty) :
      0 < stationary_mass π S := by
    simp only [stationary_mass]
    apply Finset.sum_pos'
    · intro u hu
      exact (hπPos u).le
    · obtain ⟨u, hu⟩ := hS
      exact ⟨u, hu, hπPos u⟩
  have hMassUniv : stationary_mass π Finset.univ = 1 := by
    simp only [π, stationary_mass, stationary_distribution, Finset.sum_filter,
      Finset.mem_univ, ↓reduceIte, div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ hTotalPos.ne'
  have hMassCompl (S : Finset V) :
      stationary_mass π (Finset.univ \ S) = 1 - stationary_mass π S := by
    rw [← hMassUniv]
    simp only [stationary_mass]
    have hSplit := Finset.sum_sdiff (f := π) (Finset.subset_univ S)
    linarith
  have hConductanceSetNonempty :
      {r : ℝ | ∃ S : Finset V, S.Nonempty ∧ 0 < stationary_mass π S ∧
        stationary_mass π S ≤ 1 / 2 ∧
        r = stationary_cut_flow π A S (Finset.univ \ S) /
          stationary_mass π S}.Nonempty := by
    by_cases hxHalf : stationary_mass π {x} ≤ 1 / 2
    · refine ⟨stationary_cut_flow π A {x} (Finset.univ \ {x}) /
          stationary_mass π {x}, {x}, by simp, hMassPos {x} (by simp),
          hxHalf, rfl⟩
    · let T := Finset.univ \ {x}
      have hTnonempty : T.Nonempty := by
        obtain ⟨y, hy⟩ := exists_ne x
        exact ⟨y, by simp [T, hy]⟩
      have hxMass : stationary_mass π {x} = π x := by
        simp [stationary_mass]
      have hTHalf : stationary_mass π T ≤ 1 / 2 := by
        change stationary_mass π (Finset.univ \ {x}) ≤ 1 / 2
        rw [hMassCompl, hxMass]
        rw [hxMass] at hxHalf
        linarith
      refine ⟨stationary_cut_flow π A T (Finset.univ \ T) /
          stationary_mass π T, T, hTnonempty, hMassPos T hTnonempty,
          hTHalf, rfl⟩
  unfold markov_conductance
  change c ≤ sInf {r : ℝ | ∃ S : Finset V, S.Nonempty ∧
    0 < stationary_mass π S ∧ stationary_mass π S ≤ 1 / 2 ∧
    r = stationary_cut_flow π A S (Finset.univ \ S) /
      stationary_mass π S}
  refine le_csInf hConductanceSetNonempty ?_
  rintro r ⟨S, hSnonempty, hSMassPos, hSHalf, rfl⟩
  by_cases hScard : 2 * S.card ≤ Fintype.card V
  · simpa [c, π, A] using
      parity_averaged_small_cardinality_cut_flow_bound G d ψ w hConnected
        hRegular hExpansion hψ hLipschitz S hSnonempty hScard
  · let T := Finset.univ \ S
    have hTcard : 2 * T.card ≤ Fintype.card V := by
      have hSle : S.card ≤ Fintype.card V := Finset.card_le_univ S
      simp only [T]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
      simp only [Finset.card_univ]
      omega
    have hTnonempty : T.Nonempty := by
      by_contra hT
      have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
      have hTmassZero : stationary_mass π T = 0 := by
        simp [hTempty, stationary_mass]
      have hTmassEq : stationary_mass π T = 1 - stationary_mass π S := by
        simpa [T] using hMassCompl S
      linarith
    have hTMassPos : 0 < stationary_mass π T := hMassPos T hTnonempty
    have hTMassEq : stationary_mass π T = 1 - stationary_mass π S := by
      simpa [T] using hMassCompl S
    have hMassOrder : stationary_mass π S ≤ stationary_mass π T := by
      linarith
    have hSmall :=
      parity_averaged_small_cardinality_cut_flow_bound G d ψ w hConnected
        hRegular hExpansion hψ hLipschitz T hTnonempty hTcard
    change c ≤ stationary_cut_flow π A T (Finset.univ \ T) /
      stationary_mass π T at hSmall
    simp only [T, Finset.sdiff_sdiff_eq_self (Finset.subset_univ S)] at hSmall
    have hSymmetry := parity_averaged_cut_flow_symmetry G w
      (2 * robust_radius ψ) S
    change stationary_cut_flow π A S (Finset.univ \ S) =
      stationary_cut_flow π A (Finset.univ \ S) S at hSymmetry
    rw [← hSymmetry] at hSmall
    have hc : 0 ≤ c := by
      simp only [c]
      positivity
    have hRatioNonneg :
        0 ≤ stationary_cut_flow π A S (Finset.univ \ S) /
          stationary_mass π T := hc.trans hSmall
    have hFlowNonneg :
        0 ≤ stationary_cut_flow π A S (Finset.univ \ S) := by
      rw [← div_mul_cancel₀
        (stationary_cut_flow π A S (Finset.univ \ S)) hTMassPos.ne']
      exact mul_nonneg hRatioNonneg hTMassPos.le
    exact hSmall.trans
      (div_le_div_of_nonneg_left hFlowNonneg hSMassPos hMassOrder)

@[blueprint "lem:power-conductance-bound"
  (statement := /-- Let $G=(V,E)$ be a finite, connected, $d$-regular simple
  graph, let $\psi>0$ satisfy $\Psi_G\geq\psi$, and let $w$ be a
  $\sigma(\psi)$-Lipschitz positive edge-weighting.  Assume that, for all
  $x,y\in V$ with $\operatorname{dist}_G(x,y)\leq2K(\psi)$,
  \[
    P_w^{2K(\psi)}(x,y)\geq
      \frac1{20}d^{-2K(\psi)}.
  \]
  Then
  \[
    \Phi_{P_w^{2K(\psi)}}\geq
      \frac1{4000}d^{-2K(\psi)}.
  \] -/)
  (proof := /-- Put $K=K(\psi)$ and $P=P_w^{2K}$.  Since $\psi>0$ and
  $\psi\leq\Psi_G$, \cref{def:vertex-expansion} implies $|V|\geq2$: if
  $|V|<2$, the family defining $\Psi_G$ is empty and $\Psi_G=0$.
  Connected $d$-regularity then gives $d>0$, so every vertex has positive
  weighted degree.  By \cref{def:stationary-distribution} and
  \cref{def:stationary-mass}, every vertex has positive stationary mass,
  $\pi_w(V)=1$, and
  \[
    \pi_w(V\setminus S)=1-\pi_w(S)
  \]
  for every $S\subseteq V$.  The family in
  \cref{def:markov-conductance} is nonempty: for any $x\in V$, either
  $\pi_w(\{x\})\leq1/2$, or its nonempty complement has stationary mass at
  most $1/2$.

  Now fix a nonempty $S\subseteq V$ satisfying
  $0<\pi_w(S)\leq1/2$.  If $2|S|\leq|V|$, then
  \cref{lem:small-cardinality-power-cut-flow-bound} gives
  \[
    \frac{Q_P(S,V\setminus S)}{\pi_w(S)}
      \geq\frac1{4000}d^{-2K}.
  \]
  Otherwise set $T=V\setminus S$.  Then $T$ is nonempty,
  $2|T|\leq|V|$, and
  $\pi_w(T)=1-\pi_w(S)\geq\pi_w(S)>0$.  Applying the same lemma to $T$
  yields
  \[
    \frac{Q_P(T,S)}{\pi_w(T)}
      \geq\frac1{4000}d^{-2K}.
  \]
  The lower bound on the right is nonnegative, so this inequality and
  $\pi_w(T)>0$ show that $Q_P(T,S)\geq0$.  By
  \cref{lem:weighted-cut-flow-symmetry}, $Q_P(T,S)=Q_P(S,T)$.
  Since $\pi_w(S)\leq\pi_w(T)$, division by the smaller positive
  denominator gives
  \[
    \frac{Q_P(S,T)}{\pi_w(S)}
      \geq\frac{Q_P(T,S)}{\pi_w(T)}
      \geq\frac1{4000}d^{-2K}.
  \]
  Thus every member of the nonempty family defining the infimum in
  \cref{def:markov-conductance} is bounded below by the asserted constant,
  which proves the claim. -/)
  (title := /-- Conductance of an even power under even-time accessibility -/)
  (latexEnv := "lemma")]
lemma power_conductance_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite]
    (d : ℕ) (ψ : ℝ) (w : graph_edge_weights G)
    (hConnected : G.Connected) (hRegular : G.IsRegularOfDegree d)
    (hExpansion : ψ ≤ vertex_expansion G) (hψ : 0 < ψ)
    (hLipschitz : weight_lipschitz G (robust_lipschitz_bound ψ) w)
    (hEvenPowerLower : ∀ x y : V,
      G.dist x y ≤ 2 * robust_radius ψ →
        (1 / 20) * (((d : ℝ) ^ (2 * robust_radius ψ))⁻¹) ≤
          (weighted_transition G w ^ (2 * robust_radius ψ)) x y) :
    (1 / 4000) * (((d : ℝ) ^ (2 * robust_radius ψ))⁻¹) ≤
      markov_conductance (stationary_distribution G w)
        (weighted_transition G w ^ (2 * robust_radius ψ)) := by
  classical
  let π := stationary_distribution G w
  let P := weighted_transition G w ^ (2 * robust_radius ψ)
  let c : ℝ := (1 / 4000) * (((d : ℝ) ^ (2 * robust_radius ψ))⁻¹)
  have hVcard : 2 ≤ Fintype.card V := by
    by_contra h
    have hVsmall : Fintype.card V < 2 := by omega
    have hEmpty : {r : ℝ | ∃ S : Finset V, S.Nonempty ∧
        2 * S.card ≤ Fintype.card V ∧
        r = (external_vertex_boundary G S).card / (S.card : ℝ)} = ∅ := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨S, hSnonempty, hScard, -⟩
      have hSpos : 0 < S.card := Finset.card_pos.mpr hSnonempty
      have hSle : S.card ≤ Fintype.card V := Finset.card_le_univ S
      omega
    have hExpansionZero : vertex_expansion G = 0 := by
      simp [vertex_expansion, hEmpty]
    rw [hExpansionZero] at hExpansion
    linarith
  letI : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Nonempty V := hConnected.nonempty
  let x : V := Classical.choice (inferInstance : Nonempty V)
  have hd : 0 < d := by
    have hxNotIsolated : ¬G.IsIsolated x :=
      hConnected.preconnected.not_isIsolated x
    have hxNeighbors : (G.neighborFinset x).Nonempty :=
      (SimpleGraph.neighborFinset_nonempty G x).2 hxNotIsolated
    have hxDegree : 0 < G.degree x :=
      Finset.card_pos.mpr hxNeighbors
    simpa [hRegular.degree_eq] using hxDegree
  have hWeightNonneg (u v : V) : 0 ≤ w.weight u v := by
    by_cases huv : G.Adj u v
    · exact (w.positive_of_adj huv).le
    · rw [w.zero_of_not_adj huv]
  have hDegreePos (u : V) : 0 < weighted_degree G w u := by
    have huDegree : 0 < G.degree u := by
      simpa [hRegular.degree_eq] using hd
    obtain ⟨v, huv⟩ := (G.degree_pos_iff_exists_adj (v := u)).mp huDegree
    unfold weighted_degree
    apply Finset.sum_pos'
    · intro z hz
      exact hWeightNonneg u z
    · exact ⟨v, Finset.mem_univ v, w.positive_of_adj huv⟩
  have hTotalPos : 0 < ∑ z, weighted_degree G w z := by
    apply Finset.sum_pos
    · intro z hz
      exact hDegreePos z
    · exact ⟨x, Finset.mem_univ x⟩
  have hπPos (u : V) : 0 < π u := by
    simp only [π, stationary_distribution]
    exact div_pos (hDegreePos u) hTotalPos
  have hMassPos (S : Finset V) (hS : S.Nonempty) :
      0 < stationary_mass π S := by
    simp only [stationary_mass]
    apply Finset.sum_pos'
    · intro u hu
      exact (hπPos u).le
    · obtain ⟨u, hu⟩ := hS
      exact ⟨u, hu, hπPos u⟩
  have hMassUniv : stationary_mass π Finset.univ = 1 := by
    simp only [π, stationary_mass, stationary_distribution, Finset.sum_filter,
      Finset.mem_univ, ↓reduceIte, div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ hTotalPos.ne'
  have hMassCompl (S : Finset V) :
      stationary_mass π (Finset.univ \ S) = 1 - stationary_mass π S := by
    rw [← hMassUniv]
    simp only [stationary_mass]
    have hSplit := Finset.sum_sdiff (f := π) (Finset.subset_univ S)
    linarith
  have hConductanceSetNonempty :
      {r : ℝ | ∃ S : Finset V, S.Nonempty ∧ 0 < stationary_mass π S ∧
        stationary_mass π S ≤ 1 / 2 ∧
        r = stationary_cut_flow π P S (Finset.univ \ S) /
          stationary_mass π S}.Nonempty := by
    by_cases hxHalf : stationary_mass π {x} ≤ 1 / 2
    · refine ⟨stationary_cut_flow π P {x} (Finset.univ \ {x}) /
          stationary_mass π {x}, {x}, by simp, hMassPos {x} (by simp),
          hxHalf, rfl⟩
    · let T := Finset.univ \ {x}
      have hTnonempty : T.Nonempty := by
        obtain ⟨y, hy⟩ := exists_ne x
        exact ⟨y, by simp [T, hy]⟩
      have hxMass : stationary_mass π {x} = π x := by
        simp [stationary_mass]
      have hTHalf : stationary_mass π T ≤ 1 / 2 := by
        change stationary_mass π (Finset.univ \ {x}) ≤ 1 / 2
        rw [hMassCompl, hxMass]
        rw [hxMass] at hxHalf
        linarith
      refine ⟨stationary_cut_flow π P T (Finset.univ \ T) /
          stationary_mass π T, T, hTnonempty, hMassPos T hTnonempty,
          hTHalf, rfl⟩
  unfold markov_conductance
  change c ≤ sInf {r : ℝ | ∃ S : Finset V, S.Nonempty ∧
    0 < stationary_mass π S ∧ stationary_mass π S ≤ 1 / 2 ∧
    r = stationary_cut_flow π P S (Finset.univ \ S) /
      stationary_mass π S}
  refine le_csInf hConductanceSetNonempty ?_
  rintro r ⟨S, hSnonempty, hSMassPos, hSHalf, rfl⟩
  by_cases hScard : 2 * S.card ≤ Fintype.card V
  · simpa [c, π, P] using
      small_cardinality_power_cut_flow_bound G d ψ w hConnected
        hRegular hExpansion hψ hLipschitz hEvenPowerLower S hSnonempty hScard
  · let T := Finset.univ \ S
    have hTcard : 2 * T.card ≤ Fintype.card V := by
      have hSle : S.card ≤ Fintype.card V := Finset.card_le_univ S
      simp only [T]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
      simp only [Finset.card_univ]
      omega
    have hTnonempty : T.Nonempty := by
      by_contra hT
      have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
      have hTmassZero : stationary_mass π T = 0 := by
        simp [hTempty, stationary_mass]
      have hTmassEq : stationary_mass π T = 1 - stationary_mass π S := by
        simpa [T] using hMassCompl S
      linarith
    have hTMassPos : 0 < stationary_mass π T := hMassPos T hTnonempty
    have hTMassEq : stationary_mass π T = 1 - stationary_mass π S := by
      simpa [T] using hMassCompl S
    have hMassOrder : stationary_mass π S ≤ stationary_mass π T := by
      linarith
    have hSmall :=
      small_cardinality_power_cut_flow_bound G d ψ w hConnected
        hRegular hExpansion hψ hLipschitz hEvenPowerLower T hTnonempty hTcard
    change c ≤ stationary_cut_flow π P T (Finset.univ \ T) /
      stationary_mass π T at hSmall
    simp only [T, Finset.sdiff_sdiff_eq_self (Finset.subset_univ S)] at hSmall
    have hSymmetry := weighted_cut_flow_symmetry G w
      (2 * robust_radius ψ) S
    change stationary_cut_flow π P S (Finset.univ \ S) =
      stationary_cut_flow π P (Finset.univ \ S) S at hSymmetry
    rw [← hSymmetry] at hSmall
    have hc : 0 ≤ c := by
      simp only [c]
      positivity
    have hRatioNonneg :
        0 ≤ stationary_cut_flow π P S (Finset.univ \ S) /
          stationary_mass π T := hc.trans hSmall
    have hFlowNonneg :
        0 ≤ stationary_cut_flow π P S (Finset.univ \ S) := by
      rw [← div_mul_cancel₀
        (stationary_cut_flow π P S (Finset.univ \ S)) hTMassPos.ne']
      exact mul_nonneg hRatioNonneg hTMassPos.le
    exact hSmall.trans
      (div_le_div_of_nonneg_left hFlowNonneg hSMassPos hMassOrder)

set_option maxHeartbeats 4000000 in
@[blueprint "lem:parity-averaged-spectral-gap-transfer"
  (statement := /-- Let $G=(V,E)$ be a finite, connected, $d$-regular simple
  graph, let $\psi>0$ satisfy $\Psi_G\geq\psi$, and let $w$ be a
  $\sigma(\psi)$-Lipschitz positive edge-weighting.  Then
  \[
    \gamma_{P_w}\geq
      10^{-8}d^{-4K(\psi)}.
  \] -/)
  (proof := /-- Put $K=K(\psi)$, $\beta=\sigma(\psi)$,
  $q(x)=w(x)=\sum_yw(x,y)$, and $q(U)=\sum_{x\in U}q(x)$.  We use the
  following finite-state form of Cheeger's inequality.  If $R$ is reversible
  with stationary probability $\pi$ and conductance $\Phi_R$, then
  \[
    \gamma_R\geq\tfrac12\Phi_R^2.                                      \tag{C}
  \]
  Indeed, for a nonnegative $g$ whose support has $\pi$-mass at most
  $1/2$, layer-cake integration and \cref{def:markov-conductance} give
  \[
    \Phi_R\sum_x\pi(x)g(x)^2
      \leq\frac12\sum_{x,y}\pi(x)R(x,y)|g(x)^2-g(y)^2|.
  \]
  Detailed balance, the Cauchy--Schwarz inequality, and
  $(g(x)+g(y))^2\leq2g(x)^2+2g(y)^2$ bound the right-hand side by
  \[
    \left(2\mathcal E_R(g,g)\sum_x\pi(x)g(x)^2\right)^{1/2}.
  \]
  Given an arbitrary nonconstant $f$, choose a median $m$ and apply this
  estimate to $(f-m)_+$ and $(m-f)_+$.  Both supports have mass at most
  $1/2$, their Dirichlet energies sum to at most $\mathcal E_R(f,f)$, and
  $\operatorname{Var}_\pi(f)\leq\sum_x\pi(x)(f(x)-m)^2$.  Taking the
  infimum in \cref{def:spectral-gap} proves (C).

  Positivity of $\psi$ and \cref{def:robust-radius} give $K\geq1$.  We first
  record the case $K=1$.
  By \cref{lem:parity-averaged-conductance-bound-aux},
  \[
    \Phi_{\mathcal A_2(P_w)}\geq\frac1{4000}d^{-2}.
  \]
  The symmetry of the edge weights gives detailed balance for $P_w$ and for
  $A=\mathcal A_2(P_w)$.  Applying (C) therefore yields
  \[
    \gamma_A\geq\frac12\Phi_A^2
      \geq\frac1{32\,000\,000}d^{-4}.
  \]
  If the second eigenvalue $\lambda_2$ of $P_w$ is negative, then
  $\gamma_{P_w}>1$.  Otherwise
  $(\lambda_2^2+\lambda_2)/2$ is a nonconstant eigenvalue of $A$, whence
  $\gamma_A\leq2\gamma_{P_w}$.  In either event,
  $\gamma_{P_w}\geq(64\,000\,000)^{-1}d^{-4}$, which is stronger than the
  required estimate.

  It remains to treat $K\geq2$.  We give a direct conductance estimate for
  $P_w$, thereby avoiding the factor $K$ inherent in comparison with a
  $2K$-step kernel.  By \cref{def:weight-lipschitz,def:weighted-degree}, if
  $x\sim y$, comparison of every edge incident to $x$ or $y$ with the common
  edge $\{x,y\}$ gives
  \[
    \rho^{-1}\leq\frac{q(x)}{q(y)}\leq\rho,
    \qquad \rho:=\beta^2=e^{1/K}.
  \]
  Since $K=\lceil2/\log(1+\psi)\rceil$, one has
  \[
    \rho\leq\sqrt{1+\psi},\qquad
    \sqrt{1+\psi}-1\geq\tfrac12\log(1+\psi)\geq K^{-1}.
  \]

  We claim that every $U\subseteq V$ with $2|U|\leq|V|$ satisfies
  \[
    q(\partial_VU)\geq K^{-1}q(U).                                      \tag{1}
  \]
  For $t>0$, put $U_t=\{x\in U:q(x)\geq t\}$.  Every vertex in
  $\partial_VU_t$ either belongs to $\partial_VU$ and has weight at least
  $t/\rho$, or belongs to $U$ and has weight in $[t/\rho,t)$.  Hence
  \cref{def:external-vertex-boundary,def:vertex-expansion} gives
  \[
    \psi|U_t|
      \leq|\{y\in\partial_VU:q(y)\geq t/\rho\}|
        +|\{y\in U:t/\rho\leq q(y)<t\}|.
  \]
  Integrating this finite layer-cake inequality over $t>0$ gives
  \[
    \psi q(U)\leq\rho q(\partial_VU)+(\rho-1)q(U).
  \]
  Consequently
  \[
    q(\partial_VU)\geq\frac{1+\psi-\rho}{\rho}q(U)
      \geq(\sqrt{1+\psi}-1)q(U)\geq K^{-1}q(U),
  \]
  proving (1).

  Let $S$ be nonempty with $0<\pi_w(S)\leq1/2$.  If
  $2|S|\leq|V|$, apply (1) to $U=S$.  Otherwise apply it to
  $U=V\setminus S$; by \cref{def:stationary-distribution},
  $q(V\setminus S)\geq q(S)$.  In both cases one side of the cut has a
  vertex boundary $B$ contained in the other side and satisfying
  $q(B)\geq K^{-1}q(S)$.  For each $y\in B$, choose one edge $e_y$ crossing
  the cut.  The chosen edges are distinct, and the Lipschitz condition at
  $y$ gives $w(e_y)\geq q(y)/(d\beta)$.  Expanding
  \cref{def:weighted-transition,def:stationary-cut-flow} and cancelling the
  weighted degree at the initial vertex therefore gives
  \[
    Q_{P_w}(S,V\setminus S)
      \geq\frac{\pi_w(S)}{d\beta K}.
  \]
  Since $\beta=e^{1/(2K)}<2$, \cref{def:markov-conductance} yields
  $\Phi_{P_w}\geq(2dK)^{-1}$.  Applying (C) now gives
  \[
    \gamma_{P_w}\geq\tfrac12\Phi_{P_w}^2
      \geq\frac1{8d^2K^2}.
  \]
  Positive vertex expansion forces $|V|\geq2$, and connected regularity
  forces $d\geq1$.  If $d=1$, then $G$ consists of two adjacent vertices;
  $P_w$ interchanges them, so its variational spectral gap is $2$.
  If $d\geq2$, the elementary inequality
  $K^2\leq2^{4K-2}\leq d^{4K-2}$ implies
  \[
    \frac1{8d^2K^2}\geq10^{-8}d^{-4K}.
  \]
  This proves the assertion in every case. -/)
  (title := /-- Spectral gap of a Lipschitz-weighted expander -/)
  (latexEnv := "lemma")]
lemma parity_averaged_spectral_gap_transfer {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite]
    (d : ℕ) (ψ : ℝ) (w : graph_edge_weights G)
    (hConnected : G.Connected) (hRegular : G.IsRegularOfDegree d)
    (hExpansion : ψ ≤ vertex_expansion G) (hψ : 0 < ψ)
    (hLipschitz : weight_lipschitz G (robust_lipschitz_bound ψ) w) :
    (1 / 100000000) * (((d : ℝ) ^ (4 * robust_radius ψ))⁻¹) ≤
      spectral_gap (stationary_distribution G w) (weighted_transition G w) := by
  classical
  have hlogPos : 0 < Real.log (1 + ψ) := Real.log_pos (by linarith)
  have hKpos : 0 < robust_radius ψ := by
    rw [robust_radius, Nat.ceil_pos]
    exact div_pos (by norm_num) hlogPos
  have hKceil : 2 / Real.log (1 + ψ) ≤ (robust_radius ψ : ℝ) := by
    simpa [robust_radius] using (Nat.le_ceil (2 / Real.log (1 + ψ)))
  have hKR : (0:ℝ) < (robust_radius ψ : ℝ) := by positivity
  have hσpos : 0 < robust_lipschitz_bound ψ := Real.exp_pos _
  have hσone : 1 ≤ robust_lipschitz_bound ψ := by
    simp [robust_lipschitz_bound]
  have hσsq : (robust_lipschitz_bound ψ) ^ 2 = Real.exp (1 / (robust_radius ψ : ℝ)) := by
    rw [robust_lipschitz_bound, sq, ← Real.exp_add]
    congr 1
    field_simp
    norm_num
  have hKone : (1:ℝ) ≤ (robust_radius ψ : ℝ) := Nat.one_le_cast.mpr hKpos
  have hσle2 : robust_lipschitz_bound ψ ≤ 2 := by
    have hx : (1:ℝ) / (2 * (robust_radius ψ : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hxnn : (0:ℝ) ≤ 1 / (2 * (robust_radius ψ : ℝ)) := by positivity
    have h2 := Real.add_one_le_exp (-(1 / (2 * (robust_radius ψ : ℝ))))
    have h3 : Real.exp (-(1 / (2 * (robust_radius ψ : ℝ)))) *
        Real.exp (1 / (2 * (robust_radius ψ : ℝ))) = 1 := by
      rw [← Real.exp_add]
      simp
    have h4 : 0 < Real.exp (1 / (2 * (robust_radius ψ : ℝ))) := Real.exp_pos _
    have h5 : robust_lipschitz_bound ψ = Real.exp (1 / (2 * (robust_radius ψ : ℝ))) := rfl
    rw [h5]
    nlinarith [h2, h3, h4, hx]
  have hρ4 : ((robust_lipschitz_bound ψ) ^ 2) ^ 2 ≤ 1 + ψ := by
    have h2K : 2 / (robust_radius ψ : ℝ) ≤ Real.log (1 + ψ) := by
      rw [div_le_iff₀ hKR]
      rw [div_le_iff₀ hlogPos] at hKceil
      linarith [hKceil]
    calc ((robust_lipschitz_bound ψ) ^ 2) ^ 2
        = Real.exp (2 / (robust_radius ψ : ℝ)) := by
          rw [hσsq, sq, ← Real.exp_add]
          congr 1
          field_simp
          ring
      _ ≤ Real.exp (Real.log (1 + ψ)) := Real.exp_le_exp.mpr h2K
      _ = 1 + ψ := Real.exp_log (by linarith)
  have hρK : 1 + 1 / (robust_radius ψ : ℝ) ≤ (robust_lipschitz_bound ψ) ^ 2 := by
    rw [hσsq]
    have := Real.add_one_le_exp (1 / (robust_radius ψ : ℝ))
    linarith
  have hVcard : 2 ≤ Fintype.card V := by
    by_contra hcon
    have hEmpty : {r : ℝ | ∃ S : Finset V, S.Nonempty ∧
        2 * S.card ≤ Fintype.card V ∧
        r = (external_vertex_boundary G S).card / (S.card : ℝ)} = ∅ := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨S, hSnonempty, hScard, -⟩
      have hSpos : 0 < S.card := Finset.card_pos.mpr hSnonempty
      have hSle : S.card ≤ Fintype.card V := Finset.card_le_univ S
      omega
    have hExpansionZero : vertex_expansion G = 0 := by
      simp [vertex_expansion, hEmpty]
    rw [hExpansionZero] at hExpansion
    linarith
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Nonempty V := hConnected.nonempty
  have hd : 0 < d := by
    obtain ⟨x⟩ := (inferInstance : Nonempty V)
    have hxNotIsolated : ¬G.IsIsolated x := hConnected.preconnected.not_isIsolated x
    have hxNeighbors : (G.neighborFinset x).Nonempty :=
      (SimpleGraph.neighborFinset_nonempty G x).2 hxNotIsolated
    have hxDegree : 0 < G.degree x := Finset.card_pos.mpr hxNeighbors
    simpa [hRegular.degree_eq] using hxDegree
  have hdR : (0:ℝ) < (d:ℝ) := by positivity
  have hwnn : ∀ u v : V, 0 ≤ w.weight u v := by
    intro u v
    by_cases huv : G.Adj u v
    · exact (w.positive_of_adj huv).le
    · rw [w.zero_of_not_adj huv]
  have hqpos : ∀ u : V, 0 < weighted_degree G w u := by
    intro u
    have huDegree : 0 < G.degree u := by simpa [hRegular.degree_eq] using hd
    obtain ⟨v, huv⟩ := (G.degree_pos_iff_exists_adj (v := u)).mp huDegree
    unfold weighted_degree
    exact Finset.sum_pos' (fun z _ => hwnn u z)
      ⟨v, Finset.mem_univ v, w.positive_of_adj huv⟩
  have hWpos : 0 < ∑ z, weighted_degree G w z := by
    obtain ⟨x⟩ := (inferInstance : Nonempty V)
    exact Finset.sum_pos (fun z _ => hqpos z) ⟨x, Finset.mem_univ x⟩
  have hπeq : ∀ x : V, stationary_distribution G w x =
      weighted_degree G w x / ∑ z, weighted_degree G w z := fun x => rfl
  have hπpos : ∀ x : V, 0 < stationary_distribution G w x := by
    intro x
    rw [hπeq]
    exact div_pos (hqpos x) hWpos
  have hπsum : ∑ x, stationary_distribution G w x = 1 := by
    simp only [hπeq, div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ hWpos.ne'
  have hPi : ∀ x y : V, stationary_distribution G w x * weighted_transition G w x y =
      w.weight x y / ∑ z, weighted_degree G w z := by
    intro x y
    by_cases hxy : x = y
    · subst y
      have hself : w.weight x x = 0 := w.zero_of_not_adj (by simp)
      simp [weighted_transition, hself]
    · rw [hπeq, weighted_transition]
      simp only [hxy, if_false]
      field_simp
      rw [mul_comm, mul_div_assoc, div_self (hqpos x).ne', mul_one]
  have hexp : ∀ S : Finset V, S.Nonempty → 2 * S.card ≤ Fintype.card V →
      ψ * (S.card : ℝ) ≤ ((external_vertex_boundary G S).card : ℝ) := by
    have hBdd : BddBelow {r : ℝ | ∃ C : Finset V, C.Nonempty ∧
        2 * C.card ≤ Fintype.card V ∧
        r = (external_vertex_boundary G C).card / (C.card : ℝ)} := by
      refine ⟨0, ?_⟩
      rintro r ⟨C, -, -, rfl⟩
      positivity
    intro S hSne hScard
    have hle : vertex_expansion G ≤
        ((external_vertex_boundary G S).card : ℝ) / (S.card : ℝ) := by
      unfold vertex_expansion
      exact csInf_le hBdd ⟨S, hSne, hScard, rfl⟩
    have hcardpos : (0:ℝ) < (S.card : ℝ) := by
      have := Finset.card_pos.mpr hSne
      exact_mod_cast this
    rw [le_div_iff₀ hcardpos] at hle
    calc ψ * (S.card : ℝ) ≤ vertex_expansion G * (S.card : ℝ) := by
          exact mul_le_mul_of_nonneg_right hExpansion hcardpos.le
      _ ≤ _ := hle
  have hdegree_eq : ∀ a : V, weighted_degree G w a =
      ∑ z ∈ G.neighborFinset a, w.weight a z := by
    intro a
    rw [weighted_degree]
    symm
    apply Finset.sum_subset (by simp)
    intro z _ hz
    exact w.zero_of_not_adj (by simpa using hz)
  have hdegree_upper : ∀ {a b : V}, G.Adj a b →
      weighted_degree G w a ≤ (d : ℝ) * robust_lipschitz_bound ψ * w.weight a b := by
    intro a b hab
    rw [hdegree_eq]
    calc (∑ z ∈ G.neighborFinset a, w.weight a z)
        ≤ ∑ _z ∈ G.neighborFinset a, robust_lipschitz_bound ψ * w.weight a b := by
          refine Finset.sum_le_sum ?_
          intro z hz
          exact (div_le_iff₀ (w.positive_of_adj hab)).mp
            ((hLipschitz (by simpa using hz) hab).2)
      _ = (d : ℝ) * robust_lipschitz_bound ψ * w.weight a b := by
          simp [hRegular.degree_eq, mul_assoc]
  have hdegree_lower : ∀ {a b : V}, G.Adj a b →
      (d : ℝ) * (robust_lipschitz_bound ψ)⁻¹ * w.weight a b ≤ weighted_degree G w a := by
    intro a b hab
    rw [hdegree_eq]
    calc (d : ℝ) * (robust_lipschitz_bound ψ)⁻¹ * w.weight a b
        = ∑ _z ∈ G.neighborFinset a, (robust_lipschitz_bound ψ)⁻¹ * w.weight a b := by
          simp [hRegular.degree_eq, mul_assoc]
      _ ≤ ∑ z ∈ G.neighborFinset a, w.weight a z := by
          refine Finset.sum_le_sum ?_
          intro z hz
          exact (le_div_iff₀ (w.positive_of_adj hab)).mp
            ((hLipschitz (by simpa using hz) hab).1)
  have hρ : ∀ x y : V, G.Adj x y →
      weighted_degree G w x ≤ (robust_lipschitz_bound ψ) ^ 2 * weighted_degree G w y := by
    intro x y hxy
    have h1 := hdegree_upper hxy
    have h2 := hdegree_lower hxy.symm
    rw [w.symmetric y x] at h2
    have hσ' : 0 < robust_lipschitz_bound ψ := hσpos
    have h3 : w.weight x y ≤ weighted_degree G w y * robust_lipschitz_bound ψ / (d:ℝ) := by
      rw [le_div_iff₀ hdR]
      have := mul_le_mul_of_nonneg_left h2 hσ'.le
      calc w.weight x y * (d:ℝ)
          = robust_lipschitz_bound ψ * ((d:ℝ) * (robust_lipschitz_bound ψ)⁻¹ * w.weight x y) := by
            field_simp
        _ ≤ robust_lipschitz_bound ψ * weighted_degree G w y := this
        _ = weighted_degree G w y * robust_lipschitz_bound ψ := by ring
    calc weighted_degree G w x ≤ (d : ℝ) * robust_lipschitz_bound ψ * w.weight x y := h1
      _ ≤ (d : ℝ) * robust_lipschitz_bound ψ *
            (weighted_degree G w y * robust_lipschitz_bound ψ / (d:ℝ)) := by
          apply mul_le_mul_of_nonneg_left h3
          positivity
      _ = (robust_lipschitz_bound ψ) ^ 2 * weighted_degree G w y := by
          field_simp
          try ring
  have coarea : ∀ (D : (V → ℝ) → ℝ) (b : V → ℝ) (lam : ℝ) (Pr : Finset V → Prop),
      (∀ S T : Finset V, T ⊆ S → Pr S → Pr T) →
      (∀ (m : ℝ) (S : Finset V) (g : V → ℝ), 0 < m → S.Nonempty → Pr S →
         (∀ x, 0 ≤ g x) → (∀ x, x ∉ S → g x = 0) →
         lam * (m * ∑ x ∈ S, b x) + D g ≤ D (fun x => (if x ∈ S then m else 0) + g x)) →
      (0 ≤ D (fun _ => 0)) →
      ∀ (n : ℕ) (h : V → ℝ), (∀ x, 0 ≤ h x) →
        (Finset.univ.filter (fun x => h x ≠ 0)).card ≤ n →
        Pr (Finset.univ.filter (fun x => h x ≠ 0)) →
        lam * (∑ x, b x * h x) ≤ D h := by
    intro D b lam Pr hsub hdec hzero n
    induction n with
    | zero =>
        intro h hhnn hcard _
        have hsupp : Finset.univ.filter (fun x => h x ≠ 0) = ∅ :=
          Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
        have hh0 : h = fun _ => 0 := by
          funext x
          by_contra hx
          have : x ∈ Finset.univ.filter (fun x => h x ≠ 0) := by
            simp [hx]
          simp [hsupp] at this
        rw [hh0]
        simpa using hzero
    | succ n ih =>
        intro h hhnn hcard hPr
        set S := Finset.univ.filter (fun x => h x ≠ 0) with hS
        by_cases hSne : S.Nonempty
        · obtain ⟨x₀, hx₀S, hx₀min⟩ := S.exists_min_image h hSne
          have hx₀pos : 0 < h x₀ := by
            have : h x₀ ≠ 0 := by
              have := hx₀S
              simp [hS] at this
              exact this
            exact lt_of_le_of_ne (hhnn x₀) (Ne.symm this)
          set m := h x₀ with hm
          set g : V → ℝ := fun x => if x ∈ S then h x - m else 0 with hg
          have hgnn : ∀ x, 0 ≤ g x := by
            intro x
            simp only [hg]
            split_ifs with hx
            · have := hx₀min x hx
              linarith
            · exact le_rfl
          have hgzero : ∀ x, x ∉ S → g x = 0 := by
            intro x hx
            simp [hg, hx]
          have hheqx : ∀ x, h x = (if x ∈ S then m else 0) + g x := by
            intro x
            simp only [hg]
            by_cases hx : x ∈ S
            · simp [hx]
            · have hh : h x = 0 := by
                simp [hS] at hx
                exact hx
              simp [hx, hh]
          have hheq : h = fun x => (if x ∈ S then m else 0) + g x := funext hheqx
          have hsuppg : Finset.univ.filter (fun x => g x ≠ 0) ⊆ S.erase x₀ := by
            intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
            have hxS : x ∈ S := by
              by_contra hcx
              exact hx (hgzero x hcx)
            refine Finset.mem_erase.mpr ⟨?_, hxS⟩
            intro hxx
            rw [hxx] at hx
            simp [hg, hx₀S, hm] at hx
          have hcardg : (Finset.univ.filter (fun x => g x ≠ 0)).card ≤ n := by
            have h1 := Finset.card_le_card hsuppg
            have h2 : (S.erase x₀).card = S.card - 1 := Finset.card_erase_of_mem hx₀S
            have h3 : 0 < S.card := Finset.card_pos.mpr hSne
            omega
          have hPrg : Pr (Finset.univ.filter (fun x => g x ≠ 0)) :=
            hsub S _ (hsuppg.trans (Finset.erase_subset _ _)) hPr
          have hIH := ih g hgnn hcardg hPrg
          have hdecS := hdec m S g hx₀pos hSne hPr hgnn hgzero
          have hsplit : ∑ x, b x * h x = m * (∑ x ∈ S, b x) + ∑ x, b x * g x := by
            calc ∑ x, b x * h x
                = ∑ x, ((if x ∈ S then m * b x else 0) + b x * g x) := by
                  refine Finset.sum_congr rfl ?_
                  intro x _
                  rw [hheqx x]
                  by_cases hx : x ∈ S <;> simp [hx] <;> ring
              _ = (∑ x, (if x ∈ S then m * b x else 0)) + ∑ x, b x * g x :=
                  Finset.sum_add_distrib
              _ = m * (∑ x ∈ S, b x) + ∑ x, b x * g x := by
                  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
          rw [hsplit, hheq]
          have hexpand : lam * (m * (∑ x ∈ S, b x) + ∑ x, b x * g x)
              = lam * (m * ∑ x ∈ S, b x) + lam * ∑ x, b x * g x := by ring
          rw [hexpand]
          calc lam * (m * ∑ x ∈ S, b x) + lam * ∑ x, b x * g x
              ≤ lam * (m * ∑ x ∈ S, b x) + D g := by linarith
            _ ≤ _ := hdecS
        · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
          have hh0 : h = fun _ => 0 := by
            funext x
            by_contra hx
            have : x ∈ S := by simp [hS, hx]
            simp [hSempty] at this
          rw [hh0]
          simpa using hzero
  have hune : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
  have appl : ∀ (q : V → ℝ) (ρ : ℝ), (∀ x, 0 < q x) → 1 ≤ ρ →
      (∀ x y : V, G.Adj x y → q x ≤ ρ * q y) → ρ ^ 2 ≤ 1 + ψ →
      ∀ U : Finset V, U.Nonempty → 2 * U.card ≤ Fintype.card V →
        (ρ - 1) * (∑ x ∈ U, q x) ≤ ∑ y ∈ external_vertex_boundary G U, q y := by
    intro q ρ hqpos hρ1 hρ hρψ
    intro U hUne hUcard
    have main : ψ * (∑ x, (1:ℝ) * (if x ∈ U then q x else 0)) ≤
        ∑ y, Finset.univ.sup' hune (fun x => if G.Adj x y then
          max ((if x ∈ U then q x else 0) - (if y ∈ U then q y else 0)) 0 else 0) := by
      refine coarea (fun h => ∑ y, Finset.univ.sup' hune
        (fun x => if G.Adj x y then max (h x - h y) 0 else 0)) (fun _ => 1) ψ
        (fun S => 2 * S.card ≤ Fintype.card V) ?_ ?_ ?_ (Fintype.card V) _ ?_ ?_ ?_
      · intro S T hTS hS
        have := Finset.card_le_card hTS
        omega
      · intro m S g hm hSne hPr hgnn hgz
        have hpt : ∀ y : V, (if y ∈ external_vertex_boundary G S then m else 0) +
            Finset.univ.sup' hune (fun x => if G.Adj x y then max (g x - g y) 0 else 0) ≤
            Finset.univ.sup' hune (fun x => if G.Adj x y then
              max (((if x ∈ S then m else 0) + g x) - ((if y ∈ S then m else 0) + g y)) 0
              else 0) := by
          intro y
          by_cases hyS : y ∈ S
          · have hyB : y ∉ external_vertex_boundary G S := by
              simp only [external_vertex_boundary, Finset.mem_filter, Finset.mem_univ,
                true_and, not_and, not_not]
              intro hc
              exact absurd hyS hc
            rw [if_neg hyB, zero_add]
            refine Finset.sup'_le hune _ (fun x _ => ?_)
            refine le_trans ?_ (Finset.le_sup'
              (f := fun x => if G.Adj x y then
                max (((if x ∈ S then m else 0) + g x) - ((if y ∈ S then m else 0) + g y)) 0
                else 0) (Finset.mem_univ x))
            by_cases hadj : G.Adj x y
            · simp only [hadj, if_true, if_pos hyS]
              by_cases hxS : x ∈ S
              · simp only [if_pos hxS]
                have : m + g x - (m + g y) = g x - g y := by ring
                rw [this]
              · simp only [if_neg hxS]
                have hgx : g x = 0 := hgz x hxS
                have hgy : 0 ≤ g y := hgnn y
                rw [hgx]
                rw [max_eq_right (by linarith), max_eq_right (by linarith)]
            · simp only [hadj, if_false]
              exact le_rfl
          · have hgy : g y = 0 := hgz y hyS
            by_cases hyB : y ∈ external_vertex_boundary G S
            · obtain ⟨u, huS, huadj⟩ : ∃ u ∈ S, G.Adj u y := by
                have h2 := hyB
                simp only [external_vertex_boundary, Finset.mem_filter, Finset.mem_univ,
                  true_and] at h2
                exact h2.2
              rw [if_pos hyB]
              obtain ⟨x', -, hx'eq⟩ := Finset.exists_mem_eq_sup' hune
                (fun x => if G.Adj x y then max (g x - g y) 0 else 0)
              rw [hx'eq]
              by_cases hcase : x' ∈ S ∧ G.Adj x' y
              · obtain ⟨hx'S, hx'adj⟩ := hcase
                refine le_trans ?_ (Finset.le_sup'
                  (f := fun x => if G.Adj x y then
                    max (((if x ∈ S then m else 0) + g x) -
                      ((if y ∈ S then m else 0) + g y)) 0 else 0) (Finset.mem_univ x'))
                simp only [hx'adj, if_true, if_pos hx'S, if_neg hyS]
                rw [hgy]
                have hgx' : 0 ≤ g x' := hgnn x'
                rw [max_eq_left (by linarith : (0:ℝ) ≤ g x' - 0),
                  max_eq_left (by linarith : (0:ℝ) ≤ m + g x' - (0 + 0))]
                linarith
              · have hz : (if G.Adj x' y then max (g x' - g y) 0 else 0) = 0 := by
                  by_cases hadj : G.Adj x' y
                  · simp only [hadj, if_true]
                    have hx'S : x' ∉ S := by
                      intro hc
                      exact hcase ⟨hc, hadj⟩
                    rw [hgz x' hx'S, hgy]
                    simp
                  · simp [hadj]
                rw [hz]
                refine le_trans ?_ (Finset.le_sup'
                  (f := fun x => if G.Adj x y then
                    max (((if x ∈ S then m else 0) + g x) -
                      ((if y ∈ S then m else 0) + g y)) 0 else 0) (Finset.mem_univ u))
                simp only [huadj, if_true, if_pos huS, if_neg hyS]
                rw [hgy]
                have hgu : 0 ≤ g u := hgnn u
                rw [max_eq_left (by linarith : (0:ℝ) ≤ m + g u - (0 + 0))]
                linarith
            · rw [if_neg hyB, zero_add]
              have hno : ∀ x : V, G.Adj x y → x ∉ S := by
                intro x hadj hxS
                exact hyB (by
                  simp only [external_vertex_boundary, Finset.mem_filter, Finset.mem_univ,
                    true_and]
                  exact ⟨hyS, ⟨x, hxS, hadj⟩⟩)
              refine Finset.sup'_le hune _ (fun x _ => ?_)
              refine le_trans ?_ (Finset.le_sup'
                (f := fun x => if G.Adj x y then
                  max (((if x ∈ S then m else 0) + g x) -
                    ((if y ∈ S then m else 0) + g y)) 0 else 0) (Finset.mem_univ x))
              by_cases hadj : G.Adj x y
              · have hxS : x ∉ S := hno x hadj
                simp only [hadj, if_true, if_neg hxS, if_neg hyS]
                rw [hgz x hxS, hgy]
                norm_num
              · simp only [hadj, if_false]
                exact le_rfl
        have hcardS : ∑ _x ∈ S, (1:ℝ) = (S.card : ℝ) := by simp
        have hexpS := hexp S hSne hPr
        have hBsum : m * ((external_vertex_boundary G S).card : ℝ) =
            ∑ _y : V, (if _y ∈ external_vertex_boundary G S then m else 0) := by
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
          ring
        calc ψ * (m * ∑ _x ∈ S, (1:ℝ)) +
              ∑ y, Finset.univ.sup' hune (fun x => if G.Adj x y then max (g x - g y) 0 else 0)
            ≤ m * ((external_vertex_boundary G S).card : ℝ) +
              ∑ y, Finset.univ.sup' hune
                (fun x => if G.Adj x y then max (g x - g y) 0 else 0) := by
              rw [hcardS]
              nlinarith [hm.le, hexpS]
          _ = ∑ y, ((if y ∈ external_vertex_boundary G S then m else 0) +
                Finset.univ.sup' hune
                  (fun x => if G.Adj x y then max (g x - g y) 0 else 0)) := by
              rw [Finset.sum_add_distrib, ← hBsum]
          _ ≤ _ := Finset.sum_le_sum (fun y _ => hpt y)
      · refine Finset.sum_nonneg (fun y _ => ?_)
        obtain ⟨x0⟩ := (inferInstance : Nonempty V)
        refine le_trans ?_ (Finset.le_sup'
          (f := fun x : V => if G.Adj x y then max ((0:ℝ) - 0) 0 else 0) (Finset.mem_univ x0))
        by_cases hx : G.Adj x0 y <;> simp [hx]
      · intro x
        by_cases hx : x ∈ U <;> simp [hx, (hqpos x).le]
      · exact le_trans (Finset.card_le_univ _) (by simp)
      · have hsupp : (Finset.univ.filter
            (fun x => (if x ∈ U then q x else 0) ≠ 0)) = U := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx, (hqpos x).ne']
        rw [hsupp]
        exact hUcard
    have hUB : ∀ y : V, Finset.univ.sup' hune (fun x => if G.Adj x y then
        max ((if x ∈ U then q x else 0) - (if y ∈ U then q y else 0)) 0 else 0) ≤
        (if y ∈ U then (ρ - 1) * q y else 0) +
        (if y ∈ external_vertex_boundary G U then ρ * q y else 0) := by
      intro y
      have hqy := hqpos y
      by_cases hyU : y ∈ U
      · have hyB : y ∉ external_vertex_boundary G U := by
          simp only [external_vertex_boundary, Finset.mem_filter, Finset.mem_univ,
            true_and, not_and, not_not]
          intro hc
          exact absurd hyU hc
        simp only [hyU, hyB, if_true, if_false, add_zero]
        refine Finset.sup'_le hune _ (fun x _ => ?_)
        by_cases hadj : G.Adj x y
        · simp only [hadj, if_true]
          refine max_le ?_ (by nlinarith)
          by_cases hxU : x ∈ U
          · simp only [hxU, if_true]
            have := hρ x y hadj
            nlinarith
          · simp only [hxU, if_false]
            nlinarith
        · simp only [hadj, if_false]
          nlinarith
      · simp only [hyU, if_false, zero_add]
        by_cases hyB : y ∈ external_vertex_boundary G U
        · simp only [hyB, if_true]
          refine Finset.sup'_le hune _ (fun x _ => ?_)
          by_cases hadj : G.Adj x y
          · simp only [hadj, if_true]
            refine max_le ?_ (by nlinarith)
            by_cases hxU : x ∈ U
            · simp only [hxU, if_true]
              have := hρ x y hadj
              nlinarith
            · simp only [hxU, if_false]
              nlinarith
          · simp only [hadj, if_false]
            nlinarith
        · simp only [hyB, if_false]
          refine Finset.sup'_le hune _ (fun x _ => ?_)
          have hno : ∀ z : V, G.Adj z y → z ∉ U := by
            intro z hadj hzU
            exact hyB (by
              simp only [external_vertex_boundary, Finset.mem_filter, Finset.mem_univ,
                true_and]
              exact ⟨hyU, ⟨z, hzU, hadj⟩⟩)
          by_cases hadj : G.Adj x y
          · simp only [hadj, if_true, hno x hadj, if_false]
            simp
          · simp only [hadj, if_false]
            exact le_rfl
    have hsum1 : ∑ x, (1:ℝ) * (if x ∈ U then q x else 0) = ∑ x ∈ U, q x := by
      simp only [one_mul]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have hsum2 : ∑ y : V, ((if y ∈ U then (ρ - 1) * q y else 0) +
        (if y ∈ external_vertex_boundary G U then ρ * q y else 0)) =
        (ρ - 1) * (∑ x ∈ U, q x) + ρ * ∑ y ∈ external_vertex_boundary G U, q y := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum, ← Finset.mul_sum]
    have hQUnn : 0 ≤ ∑ x ∈ U, q x := Finset.sum_nonneg (fun x _ => (hqpos x).le)
    have hfin : ψ * (∑ x ∈ U, q x) ≤
        (ρ - 1) * (∑ x ∈ U, q x) + ρ * ∑ y ∈ external_vertex_boundary G U, q y := by
      have h1 := le_trans main (Finset.sum_le_sum (fun y _ => hUB y))
      rw [hsum1, hsum2] at h1
      exact h1
    nlinarith [hfin, hQUnn, hρ1, hρψ, mul_nonneg (sub_nonneg.mpr hρ1) hQUnn]
  have hcheeger : ∀ (π : V → ℝ) (P : Matrix V V ℝ), (∀ x, 0 < π x) → (∑ x, π x = 1) →
      (∀ x y : V, π x * P x y = π y * P y x) → (∀ x y : V, 0 ≤ P x y) →
      (∀ x : V, ∑ y, P x y = 1) →
      ∀ c : ℝ, 0 < c →
        (∀ S : Finset V, S.Nonempty → 2 * S.card ≤ Fintype.card V →
          c * stationary_mass π S ≤ stationary_cut_flow π P S (Finset.univ \ S)) →
        c ^ 2 / 8 ≤ spectral_gap π P := by
    intro π P hπpos hπsum hTsym hPnn hrow c hc hcond
    have hTnn : ∀ x y : V, 0 ≤ π x * P x y := fun x y => mul_nonneg (hπpos x).le (hPnn x y)
    have hcolsum : ∀ y : V, ∑ x, π x * P x y = π y := by
      intro y
      calc ∑ x, π x * P x y = ∑ x, π y * P y x := Finset.sum_congr rfl (fun x _ => hTsym x y)
        _ = π y * ∑ x, P y x := by rw [← Finset.mul_sum]
        _ = π y := by rw [hrow y, mul_one]
    have hsubm : ∀ S T : Finset V, T ⊆ S → 2 * S.card ≤ Fintype.card V →
        2 * T.card ≤ Fintype.card V := by
      intro S T hTS hS
      have := Finset.card_le_card hTS
      omega
    have hdecm : ∀ (m : ℝ) (S : Finset V) (g : V → ℝ), 0 < m → S.Nonempty →
        2 * S.card ≤ Fintype.card V → (∀ x, 0 ≤ g x) → (∀ x, x ∉ S → g x = 0) →
        c * (m * ∑ x ∈ S, π x) +
            (∑ x, ∑ y, (π x * P x y) * max (g x - g y) 0) ≤
          ∑ x, ∑ y, (π x * P x y) *
            max (((if x ∈ S then m else 0) + g x) - ((if y ∈ S then m else 0) + g y)) 0 := by
      intro m S g hm hSne hPr hgnn hgz
      have hQ : c * (m * ∑ x ∈ S, π x) ≤
          m * stationary_cut_flow π P S (Finset.univ \ S) := by
        have h1 := hcond S hSne hPr
        have h2 : stationary_mass π S = ∑ x ∈ S, π x := rfl
        rw [h2] at h1
        nlinarith [hm.le]
      have hblock : ∑ x : V, ∑ y : V, (π x * P x y) * (if x ∈ S ∧ y ∉ S then m else 0)
          = m * stationary_cut_flow π P S (Finset.univ \ S) := by
        have hinner : ∀ x : V, ∑ y : V, (π x * P x y) * (if x ∈ S ∧ y ∉ S then m else 0)
            = (if x ∈ S then m * ∑ y ∈ Finset.univ \ S, π x * P x y else 0) := by
          intro x
          by_cases hx : x ∈ S
          · rw [if_pos hx, Finset.sdiff_eq_filter, Finset.mul_sum, Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro y _
            by_cases hy : y ∈ S
            · rw [if_neg (by tauto : ¬ (x ∈ S ∧ y ∉ S)),
                if_neg (by simpa using hy : ¬ y ∉ S)]
              ring
            · rw [if_pos (⟨hx, hy⟩ : x ∈ S ∧ y ∉ S), if_pos (hy : y ∉ S)]
              ring
          · rw [if_neg hx]
            refine Finset.sum_eq_zero ?_
            intro y _
            rw [if_neg (by tauto : ¬ (x ∈ S ∧ y ∉ S))]
            ring
        rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hinner x),
          Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
        rfl
      have hpt : ∀ x y : V,
          max (((if x ∈ S then m else 0) + g x) - ((if y ∈ S then m else 0) + g y)) 0
          = (if x ∈ S ∧ y ∉ S then m else 0) + max (g x - g y) 0 := by
        intro x y
        by_cases hx : x ∈ S
        · by_cases hy : y ∈ S
          · rw [if_pos hx, if_pos hy, if_neg (by tauto : ¬ (x ∈ S ∧ y ∉ S)), zero_add]
            congr 1
            ring
          · have hgy := hgz y hy
            have hgx := hgnn x
            rw [if_pos hx, if_neg hy, if_pos (⟨hx, hy⟩ : x ∈ S ∧ y ∉ S), hgy,
              max_eq_left (by linarith : (0:ℝ) ≤ m + g x - (0 + 0)),
              max_eq_left (by linarith : (0:ℝ) ≤ g x - 0)]
            ring
        · by_cases hy : y ∈ S
          · have hgx := hgz x hx
            have hgy := hgnn y
            rw [if_neg hx, if_pos hy, if_neg (by tauto : ¬ (x ∈ S ∧ y ∉ S)), hgx,
              max_eq_right (by linarith : (0:ℝ) + 0 - (m + g y) ≤ 0),
              max_eq_right (by linarith : (0:ℝ) - g y ≤ 0), zero_add]
          · have hgx := hgz x hx
            have hgy := hgz y hy
            rw [if_neg hx, if_neg hy, if_neg (by tauto : ¬ (x ∈ S ∧ y ∉ S)), hgx, hgy, zero_add]
            norm_num
      have hDh' : ∑ x : V, ∑ y : V, (π x * P x y) *
            max (((if x ∈ S then m else 0) + g x) - ((if y ∈ S then m else 0) + g y)) 0
          = m * stationary_cut_flow π P S (Finset.univ \ S)
            + ∑ x : V, ∑ y : V, (π x * P x y) * max (g x - g y) 0 := by
        rw [← hblock, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro x _
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro y _
        rw [hpt x y]
        ring
      rw [hDh']
      linarith [hQ]
    have hzerom : (0:ℝ) ≤ ∑ _x : V, ∑ _y : V, (π _x * P _x _y) * max ((0:ℝ) - 0) 0 := by
      simp
    have hkey : ∀ g : V → ℝ, (∀ x, 0 ≤ g x) →
        2 * (Finset.univ.filter (fun x => g x ≠ 0)).card ≤ Fintype.card V →
        c ^ 2 * (∑ x, π x * g x ^ 2) ≤
          4 * ∑ x, ∑ y, π x * P x y * (g x - g y) ^ 2 := by
      intro g hgnn hgsupp
      have hlayer : c * (∑ x, π x * g x ^ 2) ≤
          ∑ x, ∑ y, (π x * P x y) * max (g x ^ 2 - g y ^ 2) 0 := by
        refine coarea (fun h => ∑ x, ∑ y, (π x * P x y) * max (h x - h y) 0) π c
          (fun S => 2 * S.card ≤ Fintype.card V) hsubm hdecm hzerom (Fintype.card V)
          (fun x => g x ^ 2) (fun x => sq_nonneg _) ?_ ?_
        · exact le_trans (Finset.card_le_univ _) (by simp)
        · have heqs : (Finset.univ.filter (fun x => g x ^ 2 ≠ 0))
              = Finset.univ.filter (fun x => g x ≠ 0) := by
            ext x
            simp [pow_eq_zero_iff]
          rw [heqs]
          exact hgsupp
      have hterm : ∀ x y : V, c * max (g x ^ 2 - g y ^ 2) 0 ≤
          2 * (g x - g y) ^ 2 + (c ^ 2 / 4) * (g x ^ 2 + g y ^ 2) := by
        intro x y
        rcases le_or_gt (g x ^ 2 - g y ^ 2) 0 with hle | hgt
        · rw [max_eq_right hle, mul_zero]
          positivity
        · rw [max_eq_left hgt.le]
          nlinarith [sq_nonneg (4 * (g x - g y) - c * (g x + g y)),
            mul_nonneg (mul_nonneg hc.le hc.le) (sq_nonneg (g x - g y))]
      have hstep : c * (∑ x, ∑ y, (π x * P x y) * max (g x ^ 2 - g y ^ 2) 0) ≤
          ∑ x, ∑ y, (π x * P x y) *
            (2 * (g x - g y) ^ 2 + (c ^ 2 / 4) * (g x ^ 2 + g y ^ 2)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum ?_
        intro x _
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum ?_
        intro y _
        calc c * ((π x * P x y) * max (g x ^ 2 - g y ^ 2) 0)
            = (π x * P x y) * (c * max (g x ^ 2 - g y ^ 2) 0) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hterm x y) (hTnn x y)
      have hAA : ∑ x : V, ∑ y : V, (π x * P x y) * (g x ^ 2 + g y ^ 2)
          = 2 * ∑ x, π x * g x ^ 2 := by
        have h1 : ∑ x : V, ∑ y : V, (π x * P x y) * g x ^ 2 = ∑ x, π x * g x ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [← Finset.sum_mul, ← Finset.mul_sum, hrow x, mul_one]
        have h2 : ∑ x : V, ∑ y : V, (π x * P x y) * g y ^ 2 = ∑ x, π x * g x ^ 2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro y _
          rw [← Finset.sum_mul, hcolsum y]
        calc ∑ x : V, ∑ y : V, (π x * P x y) * (g x ^ 2 + g y ^ 2)
            = ∑ x : V, ((∑ y : V, (π x * P x y) * g x ^ 2)
                + ∑ y : V, (π x * P x y) * g y ^ 2) := by
              refine Finset.sum_congr rfl ?_
              intro x _
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro y _
              ring
          _ = (∑ x : V, ∑ y : V, (π x * P x y) * g x ^ 2)
                + ∑ x : V, ∑ y : V, (π x * P x y) * g y ^ 2 := Finset.sum_add_distrib
          _ = 2 * ∑ x, π x * g x ^ 2 := by rw [h1, h2]; ring
      have hsplit : ∑ x : V, ∑ y : V, (π x * P x y) *
            (2 * (g x - g y) ^ 2 + (c ^ 2 / 4) * (g x ^ 2 + g y ^ 2))
          = 2 * (∑ x, ∑ y, π x * P x y * (g x - g y) ^ 2)
            + (c ^ 2 / 4) * (∑ x : V, ∑ y : V, (π x * P x y) * (g x ^ 2 + g y ^ 2)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro x _
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro y _
        ring
      rw [hsplit, hAA] at hstep
      nlinarith [mul_le_mul_of_nonneg_left hlayer hc.le, hstep]
    have hmain : ∀ f : V → ℝ, 0 < weighted_variance π f →
        c ^ 2 / 8 ≤ dirichlet_form π P f / weighted_variance π f := by
      intro f hVar
      have hVne : (Finset.univ : Finset V).Nonempty := by
        rw [Finset.univ_nonempty_iff]
        exact Fintype.card_pos_iff.mp (by omega)
      have hGoodNe : (Finset.univ.image f).filter
          (fun t => Fintype.card V ≤
            2 * (Finset.univ.filter (fun x => f x ≤ t)).card) |>.Nonempty := by
        obtain ⟨t, -, htMax⟩ := Finset.exists_max_image Finset.univ f hVne
        refine ⟨f t, Finset.mem_filter.mpr
          ⟨Finset.mem_image_of_mem f (Finset.mem_univ t), ?_⟩⟩
        have hall : Finset.univ.filter (fun x => f x ≤ f t) = Finset.univ := by
          ext x
          simp [htMax x (Finset.mem_univ x)]
        rw [hall, Finset.card_univ]
        omega
      obtain ⟨m, hmGood, hmMin⟩ := Finset.exists_min_image _ id hGoodNe
      have hmMass : Fintype.card V ≤
          2 * (Finset.univ.filter (fun x => f x ≤ m)).card := (Finset.mem_filter.mp hmGood).2
      have hcards : (Finset.univ.filter (fun x => f x ≤ m)).card
          + (Finset.univ.filter (fun x => m < f x)).card = Fintype.card V := by
        have heq : Finset.univ.filter (fun x => ¬ f x ≤ m)
            = Finset.univ.filter (fun x => m < f x) := by
          ext x
          simp [not_le]
        rw [← heq, ← Finset.card_univ]
        exact Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset V))
          (p := fun x => f x ≤ m)
      have hgt : 2 * (Finset.univ.filter (fun x => m < f x)).card ≤ Fintype.card V := by
        omega
      have hlt : 2 * (Finset.univ.filter (fun x => f x < m)).card ≤ Fintype.card V := by
        by_contra hcon0
        have hcon : Fintype.card V < 2 * (Finset.univ.filter (fun x => f x < m)).card :=
          Nat.lt_of_not_le hcon0
        have hAne : (Finset.univ.filter (fun x => f x < m)).Nonempty := by
          rw [← Finset.card_pos]
          omega
        obtain ⟨x₀, hx₀A, hx₀max⟩ := Finset.exists_max_image _ f hAne
        have hx₀lt : f x₀ < m := by
          have := hx₀A
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact this
        have hAeq : Finset.univ.filter (fun x => f x ≤ f x₀)
            = Finset.univ.filter (fun x => f x < m) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hx
            linarith
          · intro hx
            exact hx₀max x (by simp [hx])
        have hgood : f x₀ ∈ (Finset.univ.image f).filter
            (fun t => Fintype.card V ≤
              2 * (Finset.univ.filter (fun x => f x ≤ t)).card) :=
          Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem f (Finset.mem_univ x₀), by
            rw [hAeq]; omega⟩
        have := hmMin _ hgood
        simp only [id] at this
        linarith
      have hsupp1 : Finset.univ.filter (fun x => max (f x - m) 0 ≠ 0)
          = Finset.univ.filter (fun x => m < f x) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hx
          by_contra hcx0
          have hcx := not_lt.mp hcx0
          exact hx (max_eq_right (by linarith))
        · intro hx hcx
          rw [max_eq_left (by linarith : (0:ℝ) ≤ f x - m)] at hcx
          linarith
      have hsupp2 : Finset.univ.filter (fun x => max (m - f x) 0 ≠ 0)
          = Finset.univ.filter (fun x => f x < m) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hx
          by_contra hcx0
          have hcx := not_lt.mp hcx0
          exact hx (max_eq_right (by linarith))
        · intro hx hcx
          rw [max_eq_left (by linarith : (0:ℝ) ≤ m - f x)] at hcx
          linarith
      have hk1 := hkey (fun x => max (f x - m) 0) (fun x => le_max_right _ _)
        (by rw [hsupp1]; exact hgt)
      have hk2 := hkey (fun x => max (m - f x) 0) (fun x => le_max_right _ _)
        (by rw [hsupp2]; exact hlt)
      have hpair : ∀ x y : V,
          (max (f x - m) 0 - max (f y - m) 0) ^ 2 + (max (m - f x) 0 - max (m - f y) 0) ^ 2
            ≤ (f x - f y) ^ 2 := by
        intro x y
        rcases le_or_gt (f x) m with hx | hx <;> rcases le_or_gt (f y) m with hy | hy
        · rw [max_eq_right (by linarith : f x - m ≤ 0), max_eq_right (by linarith : f y - m ≤ 0),
            max_eq_left (by linarith : (0:ℝ) ≤ m - f x),
            max_eq_left (by linarith : (0:ℝ) ≤ m - f y)]
          nlinarith []
        · rw [max_eq_right (by linarith : f x - m ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ f y - m),
            max_eq_left (by linarith : (0:ℝ) ≤ m - f x),
            max_eq_right (by linarith : m - f y ≤ 0)]
          nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ m - f x) (by linarith : (0:ℝ) ≤ f y - m)]
        · rw [max_eq_left (by linarith : (0:ℝ) ≤ f x - m), max_eq_right (by linarith : f y - m ≤ 0),
            max_eq_right (by linarith : m - f x ≤ 0),
            max_eq_left (by linarith : (0:ℝ) ≤ m - f y)]
          nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ f x - m) (by linarith : (0:ℝ) ≤ m - f y)]
        · rw [max_eq_left (by linarith : (0:ℝ) ≤ f x - m), max_eq_left (by linarith : (0:ℝ) ≤ f y - m),
            max_eq_right (by linarith : m - f x ≤ 0),
            max_eq_right (by linarith : m - f y ≤ 0)]
          nlinarith []
      have hEsum : (∑ x, ∑ y, π x * P x y * (max (f x - m) 0 - max (f y - m) 0) ^ 2)
          + (∑ x, ∑ y, π x * P x y * (max (m - f x) 0 - max (m - f y) 0) ^ 2)
          ≤ ∑ x, ∑ y, π x * P x y * (f x - f y) ^ 2 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum ?_
        intro x _
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum ?_
        intro y _
        calc π x * P x y * (max (f x - m) 0 - max (f y - m) 0) ^ 2
              + π x * P x y * (max (m - f x) 0 - max (m - f y) 0) ^ 2
            = π x * P x y * ((max (f x - m) 0 - max (f y - m) 0) ^ 2
                + (max (m - f x) 0 - max (m - f y) 0) ^ 2) := by ring
          _ ≤ π x * P x y * (f x - f y) ^ 2 :=
              mul_le_mul_of_nonneg_left (hpair x y) (hTnn x y)
      have hB : (∑ x, π x * max (f x - m) 0 ^ 2) + (∑ x, π x * max (m - f x) 0 ^ 2)
          = ∑ x, π x * (f x - m) ^ 2 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro x _
        rcases le_or_gt (f x) m with hx | hx
        · rw [max_eq_right (by linarith : f x - m ≤ 0),
            max_eq_left (by linarith : (0:ℝ) ≤ m - f x)]
          ring
        · rw [max_eq_left (by linarith : (0:ℝ) ≤ f x - m),
            max_eq_right (by linarith : m - f x ≤ 0)]
          ring
      have hzeromean : ∑ x, π x * (f x - weighted_mean π f) = 0 := by
        have hm1 : ∑ x, π x * (f x - weighted_mean π f)
            = (∑ x, π x * f x) - (∑ x, π x) * weighted_mean π f := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro x _
          ring
        rw [hm1, hπsum, one_mul]
        have : weighted_mean π f = ∑ x, π x * f x := rfl
        rw [this]
        ring
      have hVarLe : weighted_variance π f ≤ ∑ x, π x * (f x - m) ^ 2 := by
        have hexpand : ∑ x, π x * (f x - m) ^ 2
            = weighted_variance π f + (weighted_mean π f - m) ^ 2 := by
          have h1 : ∑ x, π x * (f x - m) ^ 2
              = (∑ x, π x * (f x - weighted_mean π f) ^ 2)
                + (2 * (weighted_mean π f - m)) * (∑ x, π x * (f x - weighted_mean π f))
                + (weighted_mean π f - m) ^ 2 * (∑ x, π x) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
              ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro x _
            ring
          rw [h1, hzeromean, hπsum]
          have h2 : weighted_variance π f = ∑ x, π x * (f x - weighted_mean π f) ^ 2 := rfl
          rw [h2]
          ring
        nlinarith [sq_nonneg (weighted_mean π f - m)]
      have hDf : dirichlet_form π P f
          = (1 / 2) * ∑ x, ∑ y, π x * P x y * (f x - f y) ^ 2 := rfl
      rw [le_div_iff₀ hVar, hDf]
      have hc2 : c ^ 2 * weighted_variance π f ≤ c ^ 2 * ∑ x, π x * (f x - m) ^ 2 :=
        mul_le_mul_of_nonneg_left hVarLe (sq_nonneg c)
      rw [← hB] at hc2
      nlinarith [hk1, hk2, hEsum, hc2]
    unfold spectral_gap
    refine le_csInf ?_ ?_
    · obtain ⟨x0, y0, hxy⟩ : ∃ x y : V, x ≠ y :=
        Fintype.exists_pair_of_one_lt_card (by omega)
      refine ⟨dirichlet_form π P (fun x => if x = x0 then 1 else 0) /
        weighted_variance π (fun x => if x = x0 then 1 else 0),
        ⟨fun x => if x = x0 then 1 else 0, ?_, rfl⟩⟩
      have hmean : weighted_mean π (fun x => if x = x0 then 1 else 0) = π x0 := by
        have : weighted_mean π (fun x => if x = x0 then (1:ℝ) else 0)
            = ∑ x, π x * (if x = x0 then (1:ℝ) else 0) := rfl
        rw [this]
        simp
      have hvar : weighted_variance π (fun x => if x = x0 then (1:ℝ) else 0)
          = ∑ x, π x * ((if x = x0 then (1:ℝ) else 0) - π x0) ^ 2 := by
        have : weighted_variance π (fun x => if x = x0 then (1:ℝ) else 0)
            = ∑ x, π x * ((if x = x0 then (1:ℝ) else 0)
              - weighted_mean π (fun x => if x = x0 then (1:ℝ) else 0)) ^ 2 := rfl
        rw [this, hmean]
      rw [hvar]
      have hterm : 0 < π y0 * ((if y0 = x0 then (1:ℝ) else 0) - π x0) ^ 2 := by
        rw [if_neg hxy.symm]
        have : 0 < π x0 := hπpos x0
        have h2 : (0 - π x0) ^ 2 > 0 := by nlinarith
        exact mul_pos (hπpos y0) h2
      refine lt_of_lt_of_le hterm ?_
      refine Finset.single_le_sum
        (f := fun x => π x * ((if x = x0 then (1:ℝ) else 0) - π x0) ^ 2) ?_ (Finset.mem_univ y0)
      intro x _
      exact mul_nonneg (hπpos x).le (sq_nonneg _)
    · rintro r ⟨f, hVar, rfl⟩
      exact hmain f hVar
  have hTsym : ∀ x y : V, stationary_distribution G w x * weighted_transition G w x y
      = stationary_distribution G w y * weighted_transition G w y x := by
    intro x y
    rw [hPi x y, hPi y x, w.symmetric x y]
  have hPnn : ∀ x y : V, 0 ≤ weighted_transition G w x y := by
    intro x y
    by_cases hxy : x = y
    · simp [weighted_transition, hxy]
    · simp only [weighted_transition]
      rw [if_neg hxy]
      exact div_nonneg (hwnn x y) (hqpos x).le
  have hrow : ∀ x : V, ∑ y, weighted_transition G w x y = 1 := by
    intro x
    have hself : w.weight x x = 0 := w.zero_of_not_adj (by simp)
    have hpt : ∀ y : V, weighted_transition G w x y
        = w.weight x y / weighted_degree G w x := by
      intro y
      by_cases hxy : x = y
      · subst hxy
        simp [weighted_transition, hself]
      · simp [weighted_transition, hxy]
    rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hpt y), ← Finset.sum_div]
    exact div_self (hqpos x).ne'
  rcases Nat.lt_or_ge d 2 with hdlt | hd2
  · have hdeq : d = 1 := by omega
    obtain ⟨x0⟩ := (inferInstance : Nonempty V)
    have hdegx : (G.neighborFinset x0).card = 1 := by
      have hrx := hRegular x0
      rw [hdeq] at hrx
      exact hrx
    obtain ⟨y0, hy0⟩ := Finset.card_eq_one.mp hdegx
    have hadj : G.Adj x0 y0 := by
      rw [← SimpleGraph.mem_neighborFinset, hy0]
      exact Finset.mem_singleton_self y0
    have hnbrx : ∀ v : V, G.Adj x0 v → v = y0 := by
      intro v hv
      rw [← SimpleGraph.mem_neighborFinset, hy0, Finset.mem_singleton] at hv
      exact hv
    have hdegy : (G.neighborFinset y0).card = 1 := by
      have hry := hRegular y0
      rw [hdeq] at hry
      exact hry
    have hnbry : ∀ v : V, G.Adj y0 v → v = x0 := by
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hdegy
      have hx0z : x0 = z := by
        have hmem : x0 ∈ G.neighborFinset y0 := by
          rw [SimpleGraph.mem_neighborFinset]
          exact hadj.symm
        rw [hz, Finset.mem_singleton] at hmem
        exact hmem
      intro v hv
      rw [← SimpleGraph.mem_neighborFinset, hz, Finset.mem_singleton, ← hx0z] at hv
      exact hv
    have hxy0 : x0 ≠ y0 := hadj.ne
    have hpair : ({x0, y0} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy0]), Finset.card_singleton]
    have hcard3 : Fintype.card V ≤ 3 := by
      by_contra hc4
      have hSne : ({x0, y0} : Finset V).Nonempty := ⟨x0, by simp⟩
      have hScard : 2 * ({x0, y0} : Finset V).card ≤ Fintype.card V := by omega
      have hB : external_vertex_boundary G ({x0, y0} : Finset V) = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.mpr ?_
        intro v hv
        simp only [external_vertex_boundary, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        obtain ⟨hvS, u, huS, huv⟩ := hv
        have hvor : v = x0 ∨ v = y0 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at huS
          rcases huS with rfl | rfl
          · exact Or.inr (hnbrx v huv)
          · exact Or.inl (hnbry v huv)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hvS
        tauto
      have hexpS := hexp {x0, y0} hSne hScard
      rw [hB, hpair, Finset.card_empty] at hexpS
      push_cast at hexpS
      linarith
    have hallV : ∀ v : V, v = x0 ∨ v = y0 := by
      intro v
      by_contra hcon
      have hvx : v ≠ x0 := fun h => hcon (Or.inl h)
      have hvy : v ≠ y0 := fun h => hcon (Or.inr h)
      have hdegv : (G.neighborFinset v).card = 1 := by
        have hrv := hRegular v
        rw [hdeq] at hrv
        exact hrv
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hdegv
      have huadj : G.Adj v u := by
        rw [← SimpleGraph.mem_neighborFinset, hu]
        exact Finset.mem_singleton_self u
      have hux : u ≠ x0 := by
        intro h
        rw [h] at huadj
        exact hvy (hnbrx v huadj.symm)
      have huy : u ≠ y0 := by
        intro h
        rw [h] at huadj
        exact hvx (hnbry v huadj.symm)
      have huv : u ≠ v := (huadj.ne).symm
      have hc4 : ({x0, y0, v, u} : Finset V).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy0, Ne.symm hvx, Ne.symm hux]),
          Finset.card_insert_of_notMem (by simp [Ne.symm hvy, Ne.symm huy]),
          Finset.card_insert_of_notMem (by simp [Ne.symm huv]), Finset.card_singleton]
      have hle := Finset.card_le_univ ({x0, y0, v, u} : Finset V)
      rw [hc4] at hle
      omega
    have huniv : (Finset.univ : Finset V) = {x0, y0} := by
      ext v
      simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
      exact hallV v
    have hcardV : Fintype.card V = 2 := by
      rw [← Finset.card_univ, huniv, hpair]
    have hcond1 : ∀ S : Finset V, S.Nonempty → 2 * S.card ≤ Fintype.card V →
        (1:ℝ) * stationary_mass (stationary_distribution G w) S ≤
          stationary_cut_flow (stationary_distribution G w) (weighted_transition G w) S
            (Finset.univ \ S) := by
      intro S hSne hScard
      have hS1 : S.card = 1 := by
        have hSpos := Finset.card_pos.mpr hSne
        omega
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hS1
      have hmass : stationary_mass (stationary_distribution G w) ({v} : Finset V)
          = stationary_distribution G w v := by
        have h0 : stationary_mass (stationary_distribution G w) ({v} : Finset V)
            = ∑ x ∈ ({v} : Finset V), stationary_distribution G w x := rfl
        rw [h0, Finset.sum_singleton]
      have hcut : stationary_cut_flow (stationary_distribution G w) (weighted_transition G w)
            ({v} : Finset V) (Finset.univ \ ({v} : Finset V))
          = ∑ y ∈ Finset.univ \ ({v} : Finset V),
              stationary_distribution G w v * weighted_transition G w v y := by
        have h0 : stationary_cut_flow (stationary_distribution G w) (weighted_transition G w)
              ({v} : Finset V) (Finset.univ \ ({v} : Finset V))
            = ∑ x ∈ ({v} : Finset V), ∑ y ∈ Finset.univ \ ({v} : Finset V),
                stationary_distribution G w x * weighted_transition G w x y := rfl
        rw [h0, Finset.sum_singleton]
      have hPvv : weighted_transition G w v v = 0 := by simp [weighted_transition]
      have hsub : ∑ y ∈ Finset.univ \ ({v} : Finset V), weighted_transition G w v y = 1 := by
        have h1 : ∑ y ∈ Finset.univ \ ({v} : Finset V), weighted_transition G w v y
            = (∑ y, weighted_transition G w v y)
              - ∑ y ∈ ({v} : Finset V), weighted_transition G w v y :=
          Finset.sum_sdiff_eq_sub (Finset.subset_univ _)
        rw [h1, hrow v, Finset.sum_singleton, hPvv, sub_zero]
      rw [hmass, hcut, ← Finset.mul_sum, hsub]
      norm_num
    have hgap := hcheeger (stationary_distribution G w) (weighted_transition G w)
      hπpos hπsum hTsym hPnn hrow 1 one_pos hcond1
    refine le_trans ?_ hgap
    rw [hdeq]
    norm_num
  · have hdRpos : (0:ℝ) < (d:ℝ) := by positivity
    have hcpos : (0:ℝ) < 1 / (2 * (d:ℝ) * (robust_radius ψ : ℝ)) := by positivity
    have hσsqone : (1:ℝ) ≤ (robust_lipschitz_bound ψ) ^ 2 := by nlinarith [hσone]
    have hcond2 : ∀ S : Finset V, S.Nonempty → 2 * S.card ≤ Fintype.card V →
        (1 / (2 * (d:ℝ) * (robust_radius ψ : ℝ)))
            * stationary_mass (stationary_distribution G w) S ≤
          stationary_cut_flow (stationary_distribution G w) (weighted_transition G w) S
            (Finset.univ \ S) := by
      intro S hSne hScard
      have hA1 := appl (weighted_degree G w) ((robust_lipschitz_bound ψ) ^ 2) hqpos hσsqone
        hρ hρ4 S hSne hScard
      have hmass : stationary_mass (stationary_distribution G w) S
          = (∑ x ∈ S, weighted_degree G w x) / (∑ z, weighted_degree G w z) := by
        have h1 : stationary_mass (stationary_distribution G w) S
            = ∑ x ∈ S, stationary_distribution G w x := rfl
        rw [h1, Finset.sum_div]
        exact Finset.sum_congr rfl (fun x _ => hπeq x)
      have hcut : stationary_cut_flow (stationary_distribution G w) (weighted_transition G w) S
            (Finset.univ \ S)
          = (∑ x ∈ S, ∑ y ∈ Finset.univ \ S, w.weight x y)
              / (∑ z, weighted_degree G w z) := by
        have h1 : stationary_cut_flow (stationary_distribution G w)
              (weighted_transition G w) S (Finset.univ \ S)
            = ∑ x ∈ S, ∑ y ∈ Finset.univ \ S,
                stationary_distribution G w x * weighted_transition G w x y := rfl
        rw [h1, Finset.sum_div]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun y _ => hPi x y)
      have hsubset : external_vertex_boundary G S ⊆ Finset.univ \ S := by
        intro y hy
        simp only [external_vertex_boundary, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy.1⟩
      have hcharge : ∑ y ∈ external_vertex_boundary G S, weighted_degree G w y
          ≤ (d:ℝ) * robust_lipschitz_bound ψ
              * ∑ x ∈ S, ∑ y ∈ Finset.univ \ S, w.weight x y := by
        have hchoice : ∀ y ∈ external_vertex_boundary G S, weighted_degree G w y
            ≤ (d:ℝ) * robust_lipschitz_bound ψ * (∑ x ∈ S, w.weight x y) := by
          intro y hy
          simp only [external_vertex_boundary, Finset.mem_filter, Finset.mem_univ,
            true_and] at hy
          obtain ⟨u, huS, huv⟩ := hy.2
          have h1 := hdegree_upper huv.symm
          have h2 : w.weight y u = w.weight u y := w.symmetric y u
          have h3 : w.weight u y ≤ ∑ x ∈ S, w.weight x y :=
            Finset.single_le_sum (f := fun x => w.weight x y) (fun x _ => hwnn x y) huS
          rw [h2] at h1
          refine le_trans h1 ?_
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
        calc ∑ y ∈ external_vertex_boundary G S, weighted_degree G w y
            ≤ ∑ y ∈ external_vertex_boundary G S,
                (d:ℝ) * robust_lipschitz_bound ψ * (∑ x ∈ S, w.weight x y) :=
              Finset.sum_le_sum hchoice
          _ = (d:ℝ) * robust_lipschitz_bound ψ
                * ∑ y ∈ external_vertex_boundary G S, ∑ x ∈ S, w.weight x y := by
              rw [Finset.mul_sum]
          _ ≤ (d:ℝ) * robust_lipschitz_bound ψ
                * ∑ y ∈ Finset.univ \ S, ∑ x ∈ S, w.weight x y := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
              intro y _ _
              exact Finset.sum_nonneg (fun x _ => hwnn x y)
          _ = (d:ℝ) * robust_lipschitz_bound ψ
                * ∑ x ∈ S, ∑ y ∈ Finset.univ \ S, w.weight x y := by
              rw [Finset.sum_comm]
      have hQSnn : 0 ≤ ∑ x ∈ S, weighted_degree G w x :=
        Finset.sum_nonneg (fun x _ => (hqpos x).le)
      have hcds : (1 / (2 * (d:ℝ) * (robust_radius ψ : ℝ)))
            * ((d:ℝ) * robust_lipschitz_bound ψ)
          ≤ (robust_lipschitz_bound ψ) ^ 2 - 1 := by
        have h1 : (1 / (2 * (d:ℝ) * (robust_radius ψ : ℝ)))
              * ((d:ℝ) * robust_lipschitz_bound ψ)
            = robust_lipschitz_bound ψ / (2 * (robust_radius ψ : ℝ)) := by
          field_simp
        have h2 : robust_lipschitz_bound ψ / (2 * (robust_radius ψ : ℝ))
            ≤ 1 / (robust_radius ψ : ℝ) := by
          have e2 : (1:ℝ) / (robust_radius ψ : ℝ)
              - robust_lipschitz_bound ψ / (2 * (robust_radius ψ : ℝ))
              = (2 - robust_lipschitz_bound ψ) / (2 * (robust_radius ψ : ℝ)) := by
            field_simp
          have hnn2 : (0:ℝ)
              ≤ (2 - robust_lipschitz_bound ψ) / (2 * (robust_radius ψ : ℝ)) :=
            div_nonneg (by linarith [hσle2]) (by positivity)
          rw [← e2] at hnn2
          linarith
        rw [h1]
        linarith [hρK, h2]
      have hkeyineq : (1 / (2 * (d:ℝ) * (robust_radius ψ : ℝ)))
            * (∑ x ∈ S, weighted_degree G w x)
          ≤ ∑ x ∈ S, ∑ y ∈ Finset.univ \ S, w.weight x y := by
        have hdσ : (0:ℝ) < (d:ℝ) * robust_lipschitz_bound ψ := by positivity
        refine le_of_mul_le_mul_right ?_ hdσ
        have h5 := mul_le_mul_of_nonneg_right hcds hQSnn
        have h6 := le_trans hA1 hcharge
        nlinarith [h5, h6]
      rw [hmass, hcut]
      have h7 : 0 ≤ ((∑ x ∈ S, ∑ y ∈ Finset.univ \ S, w.weight x y)
          - (1 / (2 * (d:ℝ) * (robust_radius ψ : ℝ))) * (∑ x ∈ S, weighted_degree G w x))
          / (∑ z, weighted_degree G w z) := div_nonneg (by linarith) hWpos.le
      have h8 : ((∑ x ∈ S, ∑ y ∈ Finset.univ \ S, w.weight x y)
          - (1 / (2 * (d:ℝ) * (robust_radius ψ : ℝ))) * (∑ x ∈ S, weighted_degree G w x))
          / (∑ z, weighted_degree G w z)
          = (∑ x ∈ S, ∑ y ∈ Finset.univ \ S, w.weight x y) / (∑ z, weighted_degree G w z)
            - (1 / (2 * (d:ℝ) * (robust_radius ψ : ℝ)))
              * ((∑ x ∈ S, weighted_degree G w x) / (∑ z, weighted_degree G w z)) := by
        ring
      rw [h8] at h7
      linarith
    have hgap := hcheeger (stationary_distribution G w) (weighted_transition G w)
      hπpos hπsum hTsym hPnn hrow (1 / (2 * (d:ℝ) * (robust_radius ψ : ℝ))) hcpos hcond2
    refine le_trans ?_ hgap
    have hKnat : 1 ≤ robust_radius ψ := hKpos
    have hnat : 32 * d ^ 2 * (robust_radius ψ) ^ 2
        ≤ 100000000 * d ^ (4 * robust_radius ψ) := by
      have h1 : robust_radius ψ < 2 ^ (robust_radius ψ) := Nat.lt_two_pow_self
      have h2 : (robust_radius ψ) ^ 2 ≤ (2 ^ (robust_radius ψ)) ^ 2 :=
        Nat.pow_le_pow_left h1.le 2
      have h3 : (2 ^ (robust_radius ψ)) ^ 2 = 4 ^ (robust_radius ψ) := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
        norm_num
      have h4 : 4 ^ (robust_radius ψ) ≤ d ^ (2 * robust_radius ψ) := by
        have he : (4:ℕ) = 2 ^ 2 := by norm_num
        rw [he, ← pow_mul]
        exact Nat.pow_le_pow_left hd2 _
      have h5 : d ^ 2 ≤ d ^ (2 * robust_radius ψ) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h6 : d ^ (2 * robust_radius ψ) * d ^ (2 * robust_radius ψ)
          = d ^ (4 * robust_radius ψ) := by
        rw [← pow_add]
        congr 1
        omega
      calc 32 * d ^ 2 * (robust_radius ψ) ^ 2
          ≤ 32 * d ^ (2 * robust_radius ψ) * d ^ (2 * robust_radius ψ) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 32 h5) (le_trans h2 (le_of_eq h3) |>.trans h4)
        _ = 32 * d ^ (4 * robust_radius ψ) := by rw [mul_assoc, h6]
        _ ≤ 100000000 * d ^ (4 * robust_radius ψ) :=
            Nat.mul_le_mul_right _ (by norm_num)
    have hApos : (0:ℝ) < (d:ℝ) ^ (4 * robust_radius ψ) := by positivity
    have hcast : 32 * (d:ℝ) ^ 2 * ((robust_radius ψ : ℝ)) ^ 2
        ≤ 100000000 * (d:ℝ) ^ (4 * robust_radius ψ) := by exact_mod_cast hnat
    have hden : (0:ℝ) < 32 * (d:ℝ) ^ 2 * ((robust_radius ψ : ℝ)) ^ 2 := by positivity
    have he : (1 / (2 * (d:ℝ) * (robust_radius ψ : ℝ))) ^ 2 / 8
        - (1 / 100000000) * (((d:ℝ) ^ (4 * robust_radius ψ))⁻¹)
        = (100000000 * (d:ℝ) ^ (4 * robust_radius ψ)
            - 32 * (d:ℝ) ^ 2 * ((robust_radius ψ : ℝ)) ^ 2)
          / ((32 * (d:ℝ) ^ 2 * ((robust_radius ψ : ℝ)) ^ 2)
            * (100000000 * (d:ℝ) ^ (4 * robust_radius ψ))) := by
      field_simp
      ring
    have hnn : (0:ℝ) ≤ (100000000 * (d:ℝ) ^ (4 * robust_radius ψ)
        - 32 * (d:ℝ) ^ 2 * ((robust_radius ψ : ℝ)) ^ 2)
        / ((32 * (d:ℝ) ^ 2 * ((robust_radius ψ : ℝ)) ^ 2)
          * (100000000 * (d:ℝ) ^ (4 * robust_radius ψ))) :=
      div_nonneg (by linarith) (by positivity)
    rw [← he] at hnn
    linarith

@[blueprint "thm:robustness-of-expanders"
  (statement := /-- Let $G=(V,E)$ be a finite, connected, $d$-regular simple
  graph, and let $\psi>0$ satisfy $\Psi_G\geq\psi$, where $\Psi_G$ is the
  vertex expansion of $G$.  Set
  \[
    K=\left\lceil\frac{2}{\log(1+\psi)}\right\rceil_{\mathbb{N}},
    \qquad \sigma=e^{1/(2K)}.
  \]
  Let $w$ be a $\sigma$-Lipschitz positive edge-weighting.  Assume in
  addition that every pair $x,y\in V$ with
  $\operatorname{dist}_G(x,y)\leq2K$ satisfies the quantitative even-time
  accessibility bound
  \[
    P_w^{2K}(x,y)\geq\frac1{20}d^{-2K}.
  \]
  Then
  \[
    \Phi_{P_w^{2K}}
      \geq\frac1{4000}d^{-2K},
    \qquad
    \gamma_{P_w}\geq10^{-8}d^{-4K}.
  \] -/)
  (proof := /-- Apply \cref{lem:power-conductance-bound} with the assumed
  even-time accessibility estimate to obtain the first inequality for
  $P_w^{2K}$.  Then apply
  \cref{lem:parity-averaged-spectral-gap-transfer} to the same graph and
  weighting; its spectral comparison with the parity-averaged power gives
  the second inequality. -/)
  (title := /-- Robustness of expanders -/)
  (latexEnv := "theorem")]
theorem robustness_of_expanders {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite]
    (d : ℕ) (ψ : ℝ) (w : graph_edge_weights G)
    (hConnected : G.Connected) (hRegular : G.IsRegularOfDegree d)
    (hExpansion : ψ ≤ vertex_expansion G) (hψ : 0 < ψ)
    (hLipschitz : weight_lipschitz G (robust_lipschitz_bound ψ) w)
    (hEvenPowerLower : ∀ x y : V,
      G.dist x y ≤ 2 * robust_radius ψ →
        (1 / 20) * (((d : ℝ) ^ (2 * robust_radius ψ))⁻¹) ≤
          (weighted_transition G w ^ (2 * robust_radius ψ)) x y) :
    ((1 / 4000) * (((d : ℝ) ^ (2 * robust_radius ψ))⁻¹) ≤
        markov_conductance (stationary_distribution G w)
          (weighted_transition G w ^ (2 * robust_radius ψ))) ∧
      ((1 / 100000000) * (((d : ℝ) ^ (4 * robust_radius ψ))⁻¹) ≤
        spectral_gap (stationary_distribution G w) (weighted_transition G w)) := by
  refine ⟨?_, ?_⟩
  · exact power_conductance_bound G d ψ w hConnected hRegular hExpansion hψ
      hLipschitz hEvenPowerLower
  · exact parity_averaged_spectral_gap_transfer G d ψ w hConnected hRegular
      hExpansion hψ hLipschitz

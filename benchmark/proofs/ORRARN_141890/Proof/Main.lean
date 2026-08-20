import Architect
import Mathlib

set_option linter.all false
set_option maxHeartbeats 500000

variable {X Y : Type*}

@[blueprint "def:approx-pseudometric"
  (statement := /-- Let $c \ge 1$ and let $\ell : \mathcal{Y} \times \mathcal{Y} \to \mathbb{R}_{\ge 0}$ be a loss function.
We say $\ell$ is a \emph{$c$-approximate pseudo-metric} if: (i) $\ell(y,y) = 0$ for all $y \in \mathcal{Y}$;
(ii) $\ell(y_1,y_2) = \ell(y_2,y_1)$ for all $y_1,y_2 \in \mathcal{Y}$; and (iii) for all $y_1,y_2,y_3 \in \mathcal{Y}$,
$\ell(y_1,y_2) \le c\,\bigl(\ell(y_1,y_3) + \ell(y_2,y_3)\bigr)$. -/)
  (title := /-- $c$-approximate pseudo-metric -/)
  (latexEnv := "definition")]
def approx_pseudometric (c : ℝ) (ℓ : Y → Y → ℝ) : Prop :=
  1 ≤ c ∧ (∀ y, ℓ y y = 0) ∧ (∀ y₁ y₂, ℓ y₁ y₂ = ℓ y₂ y₁) ∧
    ∀ y₁ y₂ y₃, ℓ y₁ y₂ ≤ c * (ℓ y₁ y₃ + ℓ y₂ y₃)

@[blueprint "def:induced-metric"
  (statement := /-- For a loss $\ell$ and hypotheses $f, g \in \mathcal{Y}^{\mathcal{X}}$, the \emph{induced pseudo-metric}
is $d_\ell(f,g) := \sup_{x \in \mathcal{X}} \ell\bigl(f(x), g(x)\bigr)$. This supremum is intended over classes of finite
diameter (\cref{def:finite-diameter}), on which the pointwise family $\{\ell(f(x),g(x))\}_{x \in \mathcal{X}}$ is bounded
above; there it is a genuine supremum and the pointwise domination $\ell(f(x),g(x)) \le d_\ell(f,g)$ holds for every
$x \in \mathcal{X}$. -/)
  (title := /-- Induced sup pseudo-metric -/)
  (latexEnv := "definition")]
noncomputable def induced_metric (ℓ : Y → Y → ℝ) (f g : X → Y) : ℝ :=
  ⨆ x, ℓ (f x) (g x)

@[blueprint "def:diameter"
  (statement := /-- For a hypothesis class $\mathcal{H} \subseteq \mathcal{Y}^{\mathcal{X}}$, its \emph{diameter}
under the induced pseudo-metric $d_\ell$ (\cref{def:induced-metric}) is
$\operatorname{diam}(\mathcal{H}) := \sup_{f,g \in \mathcal{H}} d_\ell(f,g)$. -/)
  (title := /-- Diameter of a hypothesis class -/)
  (latexEnv := "definition")]
noncomputable def diameter (ℓ : Y → Y → ℝ) (H : Set (X → Y)) : ℝ :=
  ⨆ (f : H) (g : H), induced_metric ℓ f.1 g.1

@[blueprint "def:finite-diameter"
  (statement := /-- The class $\mathcal{H}$ has \emph{finite diameter} if its pointwise losses are uniformly bounded:
there exists $M \in \mathbb{R}$ such that $\ell\bigl(f(x), g(x)\bigr) \le M$ for all $f, g \in \mathcal{H}$ and all
$x \in \mathcal{X}$. Equivalently, the induced sup pseudo-metric $d_\ell$ (\cref{def:induced-metric}) is a genuine
(finite) supremum on $\mathcal{H} \times \mathcal{H}$ and $\operatorname{diam}(\mathcal{H}) < \infty$
(\cref{def:diameter}). -/)
  (title := /-- Finite diameter hypothesis class -/)
  (latexEnv := "definition")]
def finite_diameter (ℓ : Y → Y → ℝ) (H : Set (X → Y)) : Prop :=
  ∃ M : ℝ, ∀ f ∈ H, ∀ g ∈ H, ∀ x, ℓ (f x) (g x) ≤ M

@[blueprint "def:covering-number"
  (statement := /-- For $\varepsilon \in \mathbb{R}$ and $U \subseteq \mathcal{H}$, the \emph{covering number}
$N(U,\varepsilon)$ is the least cardinality of a finite set $S \subseteq \mathcal{H}$ such that every $u \in U$
admits some $s \in S$ with $d_\ell(u,s) \le \varepsilon$ (\cref{def:induced-metric}). It takes values in
$\mathbb{N} \cup \{\infty\}$, with the convention that the infimum over an empty family of covers is $\infty$. -/)
  (title := /-- Covering number -/)
  (latexEnv := "definition")]
noncomputable def covering_number (ℓ : Y → Y → ℝ) (H : Set (X → Y)) (U : Set (X → Y))
    (ε : ℝ) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ S : Finset (X → Y), (↑S : Set (X → Y)) ⊆ H ∧ (S.card : ℕ∞) = n ∧
    ∀ u ∈ U, ∃ s ∈ S, induced_metric ℓ u s ≤ ε}

@[blueprint "def:entropy-potential"
  (statement := /-- For $U \subseteq \mathcal{H}$, the \emph{entropy potential} is the extended-nonnegative-real value
$\Phi(U) := \int_0^{\operatorname{diam}(\mathcal{H})} \log_2 N(U,\varepsilon)\, d\varepsilon \in [0,+\infty]$,
the base-$2$ logarithm of the covering number $N(U,\varepsilon)$ of \cref{def:covering-number} integrated over
$\varepsilon$ from $0$ to the diameter of \cref{def:diameter}. The integrand is read in $[0,+\infty]$ under the
conventions $\log_2 1 = 0$ and $\log_2(+\infty) = +\infty$: at any $\varepsilon$ where $U$ admits no finite
$\varepsilon$-cover, so $N(U,\varepsilon) = +\infty$ (\cref{def:covering-number}), the integrand equals $+\infty$;
at any $\varepsilon$ with $N(U,\varepsilon) \in \mathbb{N}$ it equals the ordinary nonnegative real $\log_2 N(U,\varepsilon)$
(with the degenerate value $0$ when $N(U,\varepsilon) \in \{0,1\}$). The integral is the lower Lebesgue integral with
respect to Lebesgue measure on $\bigl(0, \operatorname{diam}(\mathcal{H})\bigr]$. In particular $\Phi(U) = +\infty$
whenever $U$ fails to be totally bounded on a subinterval of $\bigl(0,\operatorname{diam}(\mathcal{H})\bigr)$ of positive
length, faithfully encoding $\log_2 N$ with $N = \infty$. -/)
  (title := /-- Entropy potential -/)
  (latexEnv := "definition")]
noncomputable def entropy_potential (ℓ : Y → Y → ℝ) (H : Set (X → Y)) (U : Set (X → Y)) : ENNReal :=
  MeasureTheory.lintegral
    (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) (diameter ℓ H)))
    (fun ε => if covering_number ℓ H U ε = ⊤ then (⊤ : ENNReal)
      else ENNReal.ofReal (Real.logb 2 (covering_number ℓ H U ε).toENNReal.toReal))

@[blueprint "def:scaled-tree"
  (statement := /-- A \emph{scaled Littlestone tree} of depth $\infty$ for $\mathcal{X}, \mathcal{Y}$ is a complete
binary tree in which each internal node $u \in \{0,1\}^{<\infty}$ is labeled by an instance $x_u \in \mathcal{X}$
and its two outgoing edges are labeled by $s_{u,0}, s_{u,1} \in \mathcal{Y}$. Nodes are indexed by finite binary
strings. -/)
  (title := /-- Scaled Littlestone tree -/)
  (latexEnv := "definition")]
structure scaled_tree (X Y : Type*) where
  inst : List Bool → X
  edge : List Bool → Bool → Y

@[blueprint "def:branch-prefix"
  (statement := /-- For a branch $b : \mathbb{N} \to \{0,1\}$ and $t \in \mathbb{N}$, the \emph{length-$t$ prefix}
$b_{\le t}$ is the node $\bigl(b(0), b(1), \dots, b(t-1)\bigr) \in \{0,1\}^{t}$. -/)
  (title := /-- Branch prefix -/)
  (latexEnv := "definition")]
def branch_prefix (b : ℕ → Bool) (t : ℕ) : List Bool :=
  (List.range t).map b

@[blueprint "def:node-gap"
  (statement := /-- For a scaled Littlestone tree (\cref{def:scaled-tree}) and an internal node $u$, the \emph{gap}
at $u$ is $\gamma_u := \ell(s_{u,0}, s_{u,1})$, the loss between the two edge labels leaving $u$. -/)
  (title := /-- Node gap -/)
  (latexEnv := "definition")]
def node_gap (ℓ : Y → Y → ℝ) (T : scaled_tree X Y) (u : List Bool) : ℝ :=
  ℓ (T.edge u false) (T.edge u true)

@[blueprint "def:realizable-tree"
  (statement := /-- A scaled Littlestone tree (\cref{def:scaled-tree}) is \emph{realizable by $\mathcal{H}$} if for
every branch $b : \mathbb{N} \to \{0,1\}$ and every $n \in \mathbb{N}$ there exists $h \in \mathcal{H}$ such that
$h\bigl(x_{b_{\le t}}\bigr) = s_{b_{\le t},\, b(t)}$ for all $t < n$, where $b_{\le t}$ is the prefix of
\cref{def:branch-prefix}. -/)
  (title := /-- Realizable scaled Littlestone tree -/)
  (latexEnv := "definition")]
def realizable_tree (H : Set (X → Y)) (T : scaled_tree X Y) : Prop :=
  ∀ b : ℕ → Bool, ∀ n : ℕ, ∃ h ∈ H, ∀ t < n,
    h (T.inst (branch_prefix b t)) = T.edge (branch_prefix b t) (b t)

@[blueprint "def:version-space"
  (statement := /-- For a scaled Littlestone tree (\cref{def:scaled-tree}) and a node $u \in \{0,1\}^{<\infty}$, the
\emph{version space} $U_u$ is the set of $h \in \mathcal{H}$ consistent with the path from the root to $u$: for every
$t < |u|$ one has $h\bigl(x_{u_{\le t}}\bigr) = s_{u_{\le t},\, u_t}$, where $u_{\le t}$ is the length-$t$ prefix of
$u$ and $u_t$ is its $t$-th coordinate. -/)
  (title := /-- Version space at a node -/)
  (latexEnv := "definition")]
def version_space (H : Set (X → Y)) (T : scaled_tree X Y) (u : List Bool) : Set (X → Y) :=
  {h ∈ H | ∀ t, ∀ ht : t < u.length,
    h (T.inst (u.take t)) = T.edge (u.take t) (u[t]'ht)}

@[blueprint "def:online-dim"
  (statement := /-- The \emph{online dimension} is
$\mathbb{D}_{\mathrm{onl}}(\mathcal{H}) := \sup_{T} \inf_{b \in \mathcal{P}(T)} \sum_{t \ge 0} \gamma_{b_{\le t}}$,
where the supremum ranges over all scaled Littlestone trees $T$ realizable by $\mathcal{H}$ (\cref{def:realizable-tree}),
$\mathcal{P}(T)$ is the set of infinite branches of $T$, $b_{\le t}$ is the prefix of \cref{def:branch-prefix}, and
$\gamma$ is the node gap of \cref{def:node-gap}. The value lies in $[0,\infty]$. -/)
  (title := /-- Online dimension -/)
  (latexEnv := "definition")]
noncomputable def online_dim (ℓ : Y → Y → ℝ) (H : Set (X → Y)) : ENNReal :=
  ⨆ (T : scaled_tree X Y) (_ : realizable_tree H T),
    ⨅ b : ℕ → Bool, ∑' t : ℕ, ENNReal.ofReal (node_gap ℓ T (branch_prefix b t))

@[blueprint "lem:cover-sum"
  (statement := /-- Let $\ell$ be a $c$-approximate pseudo-metric with $c \ge 1$ (\cref{def:approx-pseudometric}).
Assume $\mathcal{H}$ has finite diameter (\cref{def:finite-diameter}), so that the pointwise losses on $\mathcal{H}$ are
uniformly bounded and the induced sup pseudo-metric $d_\ell$ (\cref{def:induced-metric}) is a genuine supremum on
$\mathcal{H} \times \mathcal{H}$.
Let $u$ be an internal node of a scaled Littlestone tree, with version space $U := U_u$ and children version spaces
$U_0 := U_{u0}$ and $U_1 := U_{u1}$ (\cref{def:version-space}). Then for every $\varepsilon \in \bigl(0, \gamma_u/(2c)\bigr)$,
where $\gamma_u$ is the node gap of \cref{def:node-gap},
$N(U_0,\varepsilon) + N(U_1,\varepsilon) \le N(U,\varepsilon)$ (\cref{def:covering-number}). -/)
  (proof := /-- Fix $\varepsilon \in \bigl(0, \gamma_u/(2c)\bigr)$. For any $h_0 \in U_0$ and $h_1 \in U_1$, the version-space
conditions force $h_0(x_u) = s_{u,0}$ and $h_1(x_u) = s_{u,1}$. Because $\mathcal{H}$ has finite diameter, the pointwise
family $\{\ell(h_0(x), h_1(x))\}_{x \in \mathcal{X}}$ is bounded above, so its supremum $d_\ell(h_0,h_1)$ is a genuine
supremum and dominates every term; in particular
$d_\ell(h_0,h_1) \ge \ell\bigl(h_0(x_u), h_1(x_u)\bigr) = \ell(s_{u,0}, s_{u,1}) = \gamma_u$.
Suppose, for contradiction, that some $s \in \mathcal{H}$ satisfied $d_\ell(h_0,s) \le \varepsilon$ and $d_\ell(h_1,s) \le \varepsilon$
for some $h_0 \in U_0$ and $h_1 \in U_1$. By the $c$-approximate triangle inequality applied to $d_\ell$,
$d_\ell(h_0,h_1) \le c\bigl(d_\ell(h_0,s) + d_\ell(h_1,s)\bigr) \le 2c\varepsilon < \gamma_u$, a contradiction.
Thus no single center $s \in \mathcal{H}$ can be within $\varepsilon$ of a point of $U_0$ and a point of $U_1$ simultaneously.
Let $S \subseteq \mathcal{H}$ be a minimal $\varepsilon$-cover of $U$, so $|S| = N(U,\varepsilon)$, and set
$S_b := \{\, s \in S : \exists h \in U_b,\ d_\ell(h,s) \le \varepsilon \,\}$ for $b \in \{0,1\}$. Each $S_b$ is an
$\varepsilon$-cover of $U_b$, and $S_0 \cap S_1 = \varnothing$ by the previous claim, so
$N(U_0,\varepsilon) + N(U_1,\varepsilon) \le |S_0| + |S_1| \le |S| = N(U,\varepsilon)$. -/)
  (title := /-- Covers split below the gap -/)
  (latexEnv := "lemma")]
lemma cover_sum (ℓ : Y → Y → ℝ) (c : ℝ) (H : Set (X → Y)) (T : scaled_tree X Y)
    (u : List Bool) (ε : ℝ) (hℓ : approx_pseudometric c ℓ)
    (hdiam : finite_diameter ℓ H)
    (hε : 0 < ε) (hlt : ε < node_gap ℓ T u / (2 * c)) :
    covering_number ℓ H (version_space H T (u ++ [false])) ε
        + covering_number ℓ H (version_space H T (u ++ [true])) ε
      ≤ covering_number ℓ H (version_space H T u) ε := by
  classical
  obtain ⟨hc, -, -, htri⟩ := hℓ
  obtain ⟨M, hM⟩ := hdiam
  have hc' : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  haveI : Nonempty X := ⟨T.inst u⟩
  have hbdd : ∀ f, f ∈ H → ∀ g, g ∈ H →
      BddAbove (Set.range fun x => ℓ (f x) (g x)) := by
    intro f hf g hg
    exact ⟨M, by rintro y ⟨x, rfl⟩; exact hM f hf g hg x⟩
  have hdom : ∀ f, f ∈ H → ∀ g, g ∈ H → ∀ x,
      ℓ (f x) (g x) ≤ induced_metric ℓ f g := by
    intro f hf g hg x
    exact le_ciSup (hbdd f hf g hg) x
  have htri' : ∀ f, f ∈ H → ∀ g, g ∈ H → ∀ s, s ∈ H →
      induced_metric ℓ f g ≤ c * (induced_metric ℓ f s + induced_metric ℓ g s) := by
    intro f hf g hg s hs
    apply ciSup_le
    intro x
    refine le_trans (htri (f x) (g x) (s x)) ?_
    exact mul_le_mul_of_nonneg_left
      (add_le_add (hdom f hf s hs x) (hdom g hg s hs x)) hc'.le
  have heval : ∀ (b : Bool) (h : X → Y),
      h ∈ version_space H T (u ++ [b]) → h (T.inst u) = T.edge u b := by
    intro b h hh
    have hlen : u.length < (u ++ [b]).length := by simp
    have hcond := hh.2 u.length hlen
    rw [List.take_append_length] at hcond
    rw [List.getElem_concat_length rfl] at hcond
    exact hcond
  have hsub : ∀ (b : Bool),
      version_space H T (u ++ [b]) ⊆ version_space H T u := by
    intro b h hh
    refine ⟨hh.1, ?_⟩
    intro t ht
    have hlen : t < (u ++ [b]).length := by
      rw [List.length_append]; omega
    have hcond := hh.2 t hlen
    rw [List.take_append_of_le_length (le_of_lt ht),
      List.getElem_append_left ht] at hcond
    exact hcond
  refine le_sInf ?_
  rintro n ⟨S, hSH, rfl, hScov⟩
  set S0 := S.filter
    (fun s => ∃ h ∈ version_space H T (u ++ [false]), induced_metric ℓ h s ≤ ε) with hS0
  set S1 := S.filter
    (fun s => ∃ h ∈ version_space H T (u ++ [true]), induced_metric ℓ h s ≤ ε) with hS1
  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    rw [hS0, Finset.mem_filter] at ha
    rw [hS1, Finset.mem_filter] at ha'
    obtain ⟨haS, h0, h0mem, hd0⟩ := ha
    obtain ⟨-, h1, h1mem, hd1⟩ := ha'
    have haH : a ∈ H := hSH (Finset.mem_coe.mpr haS)
    have h0H : h0 ∈ H := (hsub false h0mem).1
    have h1H : h1 ∈ H := (hsub true h1mem).1
    have he0 : h0 (T.inst u) = T.edge u false := heval false h0 h0mem
    have he1 : h1 (T.inst u) = T.edge u true := heval true h1 h1mem
    have hge : node_gap ℓ T u ≤ induced_metric ℓ h0 h1 := by
      have hd := hdom h0 h0H h1 h1H (T.inst u)
      rw [he0, he1] at hd
      exact hd
    have hle : induced_metric ℓ h0 h1 ≤ c * (ε + ε) := by
      refine le_trans (htri' h0 h0H h1 h1H a haH) ?_
      exact mul_le_mul_of_nonneg_left (add_le_add hd0 hd1) hc'.le
    have h2c : (0 : ℝ) < 2 * c := mul_pos (by norm_num) hc'
    have hlt' : ε * (2 * c) < node_gap ℓ T u := (lt_div_iff₀ h2c).mp hlt
    have hcontra : node_gap ℓ T u < node_gap ℓ T u :=
      calc node_gap ℓ T u ≤ c * (ε + ε) := le_trans hge hle
        _ = ε * (2 * c) := by ring
        _ < node_gap ℓ T u := hlt'
    exact absurd hcontra (lt_irrefl _)
  have hN0 : covering_number ℓ H (version_space H T (u ++ [false])) ε
      ≤ (S0.card : ℕ∞) := by
    apply sInf_le
    refine ⟨S0, ?_, rfl, ?_⟩
    · intro x hx
      rw [Finset.mem_coe, hS0, Finset.mem_filter] at hx
      exact hSH (Finset.mem_coe.mpr hx.1)
    · intro v hv
      obtain ⟨s, hsS, hsd⟩ := hScov v (hsub false hv)
      refine ⟨s, ?_, hsd⟩
      rw [hS0, Finset.mem_filter]
      exact ⟨hsS, v, hv, hsd⟩
  have hN1 : covering_number ℓ H (version_space H T (u ++ [true])) ε
      ≤ (S1.card : ℕ∞) := by
    apply sInf_le
    refine ⟨S1, ?_, rfl, ?_⟩
    · intro x hx
      rw [Finset.mem_coe, hS1, Finset.mem_filter] at hx
      exact hSH (Finset.mem_coe.mpr hx.1)
    · intro v hv
      obtain ⟨s, hsS, hsd⟩ := hScov v (hsub true hv)
      refine ⟨s, ?_, hsd⟩
      rw [hS1, Finset.mem_filter]
      exact ⟨hsS, v, hv, hsd⟩
  calc covering_number ℓ H (version_space H T (u ++ [false])) ε
        + covering_number ℓ H (version_space H T (u ++ [true])) ε
      ≤ (S0.card : ℕ∞) + (S1.card : ℕ∞) := add_le_add hN0 hN1
    _ = ((S0.card + S1.card : ℕ) : ℕ∞) := by norm_cast
    _ ≤ ((S.card : ℕ) : ℕ∞) := by
        apply Nat.cast_le.mpr
        rw [← Finset.card_union_of_disjoint hdisj]
        exact Finset.card_le_card
          (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))

@[blueprint "lem:potential-drop"
  (statement := /-- Let $\ell$ be a $c$-approximate pseudo-metric with $c \ge 1$ (\cref{def:approx-pseudometric}) and let
$\mathcal{H}$ have finite diameter (\cref{def:finite-diameter}). Let $T$ be a scaled Littlestone tree realizable by
$\mathcal{H}$ (\cref{def:realizable-tree}) and let $u$ be an internal node with version space
$U := U_u$ and children version spaces $U_0, U_1$ (\cref{def:version-space}). Then there exists $b \in \{0,1\}$ such that
$\Phi(U_b) \le \Phi(U) - \dfrac{\gamma_u}{4c}$, where $\Phi$ is the entropy potential of \cref{def:entropy-potential}
and $\gamma_u$ the node gap of \cref{def:node-gap}. -/)
  (proof := /-- If $\Phi(U) = +\infty$ the claim is immediate, since $\Phi(U_b) \le \Phi(U) - \gamma_u/(4c) = +\infty$
for either child by the truncated subtraction convention on $[0,+\infty]$; so assume $\Phi(U) < +\infty$. Set
$I := \bigl(0, \gamma_u/(2c)\bigr)$. By \cref{lem:cover-sum}, for every $\varepsilon \in I$ we have
$N(U,\varepsilon) \ge N(U_0,\varepsilon) + N(U_1,\varepsilon)$, so for each such $\varepsilon$ there is $b \in \{0,1\}$ with
$N(U_b,\varepsilon) \le N(U,\varepsilon)/2$; here $N(U,\varepsilon) < \infty$ for a.e. $\varepsilon \in I$ because
$\Phi(U) < +\infty$ forces $\log_2 N(U,\varepsilon) < \infty$, hence $N(U,\varepsilon) \in \mathbb{N}$, off a null set.
Because $T$ is realizable by $\mathcal{H}$ (\cref{def:realizable-tree}), the
edge labels $s_{u,0}, s_{u,1}$ leaving $u$ are attained by members of $\mathcal{H}$, so
$\gamma_u = \ell(s_{u,0}, s_{u,1}) \le \operatorname{diam}(\mathcal{H})$; since $c \ge 1$ this yields
$I \subseteq \bigl(0, \operatorname{diam}(\mathcal{H})\bigr)$, so $I$ lies inside the domain of integration of $\Phi$.
For $b \in \{0,1\}$ define
$A_b := \{\, \varepsilon \in I : N(U_b,\varepsilon) \le N(U,\varepsilon)/2 \,\}$; these sets are measurable because
$\varepsilon \mapsto N(U,\varepsilon)$ is monotone, and $A_0 \cup A_1 = I$. Hence some $b$ satisfies
$|A_b| \ge |I|/2 = \gamma_u/(4c)$, where $|A_b|$ is the Lebesgue measure of $A_b$. For $\varepsilon \in A_b$ we have
$\log_2 N(U_b,\varepsilon) \le \log_2 N(U,\varepsilon) - 1$, while for $\varepsilon \notin A_b$ the inclusion
$U_b \subseteq U$ gives $N(U_b,\varepsilon) \le N(U,\varepsilon)$ and hence
$\log_2 N(U_b,\varepsilon) \le \log_2 N(U,\varepsilon)$. Integrating over $[0, \operatorname{diam}(\mathcal{H})]$ and using
that $\Phi(U)$ is finite yields $\Phi(U_b) \le \Phi(U) - |A_b| \le \Phi(U) - \gamma_u/(4c)$. -/)
  (title := /-- One-step potential drop -/)
  (latexEnv := "lemma")]
lemma potential_drop (ℓ : Y → Y → ℝ) (c : ℝ) (H : Set (X → Y)) (T : scaled_tree X Y)
    (u : List Bool) (hℓ : approx_pseudometric c ℓ) (hdiam : finite_diameter ℓ H)
    (hreal : realizable_tree H T) :
    ∃ b : Bool, entropy_potential ℓ H (version_space H T (u ++ [b]))
      ≤ entropy_potential ℓ H (version_space H T u)
        - ENNReal.ofReal (node_gap ℓ T u / (4 * c)) := by
  classical
  set γ := node_gap ℓ T u with hγ
  have hc : (1:ℝ) ≤ c := hℓ.1
  have hℓ0 := hℓ.2.1
  have htri := hℓ.2.2.2
  have hc' : (0:ℝ) < c := lt_of_lt_of_le one_pos hc
  haveI : Nonempty X := ⟨T.inst u⟩
  obtain ⟨M, hM⟩ := hdiam
  have hloss_nonneg : ∀ y1 y2, 0 ≤ ℓ y1 y2 := by
    intro y1 y2; have h := htri y1 y1 y2; rw [hℓ0] at h; nlinarith [h]
  have hbdd : ∀ f, f ∈ H → ∀ g, g ∈ H → BddAbove (Set.range fun x => ℓ (f x) (g x)) :=
    fun f hf g hg => ⟨M, by rintro y ⟨x, rfl⟩; exact hM f hf g hg x⟩
  have hdom : ∀ f, f ∈ H → ∀ g, g ∈ H → ∀ x, ℓ (f x) (g x) ≤ induced_metric ℓ f g :=
    fun f hf g hg x => le_ciSup (hbdd f hf g hg) x
  have hdiamge : ∀ f, f ∈ H → ∀ g, g ∈ H → induced_metric ℓ f g ≤ diameter ℓ H := by
    intro f hf g hg
    haveI : Nonempty H := ⟨⟨f, hf⟩⟩
    have hbddOuter : BddAbove (Set.range fun p : H => (⨆ q : H, induced_metric ℓ p.1 q.1)) := by
      refine ⟨M, ?_⟩; rintro y ⟨p, rfl⟩; apply ciSup_le; intro q; apply ciSup_le; intro x
      exact hM p.1 p.2 q.1 q.2 x
    have hbddInner : ∀ p : H, BddAbove (Set.range fun q : H => induced_metric ℓ p.1 q.1) :=
      fun p => ⟨M, by rintro y ⟨q, rfl⟩; apply ciSup_le; intro x; exact hM p.1 p.2 q.1 q.2 x⟩
    calc induced_metric ℓ f g ≤ ⨆ q : H, induced_metric ℓ (⟨f, hf⟩ : H).1 q.1 :=
          le_ciSup (hbddInner ⟨f, hf⟩) (⟨g, hg⟩ : H)
      _ ≤ diameter ℓ H := le_ciSup hbddOuter (⟨f, hf⟩ : H)
  have hne : ∀ w : List Bool, (version_space H T w).Nonempty := by
    intro w
    obtain ⟨h, hh, hcond⟩ := hreal (fun i => w.getD i false) w.length
    refine ⟨h, hh, ?_⟩
    intro t ht
    have hpref : branch_prefix (fun i => w.getD i false) t = w.take t := by
      apply List.ext_getElem
      · simp [branch_prefix]; omega
      · intro i h1 h2
        simp only [List.length_take, lt_min_iff] at h2
        simp only [branch_prefix, List.getElem_map, List.getElem_range]
        rw [List.getElem_take]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, h2.2]
    have hc2 := hcond t ht
    rw [hpref] at hc2
    rw [hc2]; congr 1
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, ht]
  have heval : ∀ (b : Bool) (h : X → Y),
      h ∈ version_space H T (u ++ [b]) → h (T.inst u) = T.edge u b := by
    intro b h hh
    have hlen : u.length < (u ++ [b]).length := by simp
    have hcond := hh.2 u.length hlen
    rw [List.take_append_length] at hcond
    rw [List.getElem_concat_length rfl] at hcond
    exact hcond
  have hsub : ∀ (b : Bool), version_space H T (u ++ [b]) ⊆ version_space H T u := by
    intro b h hh
    refine ⟨hh.1, ?_⟩
    intro t ht
    have hlen : t < (u ++ [b]).length := by rw [List.length_append]; omega
    have hcond := hh.2 t hlen
    rw [List.take_append_of_le_length (le_of_lt ht), List.getElem_append_left ht] at hcond
    exact hcond
  have mono : ∀ (V W : Set (X → Y)) (ε : ℝ), V ⊆ W →
      covering_number ℓ H V ε ≤ covering_number ℓ H W ε := by
    intro V W ε hVW
    apply sInf_le_sInf
    rintro n ⟨S, hSH, hcard, hcov⟩
    exact ⟨S, hSH, hcard, fun v hv => hcov v (hVW hv)⟩
  have pos : ∀ (W : Set (X → Y)) (ε : ℝ), W.Nonempty → 1 ≤ covering_number ℓ H W ε := by
    intro W ε hW
    obtain ⟨u0, hu0⟩ := hW
    apply le_sInf
    rintro n ⟨S, hSH, rfl, hcov⟩
    obtain ⟨s, hs, -⟩ := hcov u0 hu0
    have hSne : S.Nonempty := ⟨s, hs⟩
    exact_mod_cast hSne.card_pos
  have measN : ∀ (W : Set (X → Y)),
      Measurable (fun ε => (covering_number ℓ H W ε).toENNReal) := by
    intro W
    refine Antitone.measurable ?_
    intro ε ε' hle
    apply ENat.toENNReal_mono
    apply sInf_le_sInf
    rintro n ⟨S, hSH, hcard, hcov⟩
    refine ⟨S, hSH, hcard, fun v hv => ?_⟩
    obtain ⟨s, hs, hds⟩ := hcov v hv
    exact ⟨s, hs, le_trans hds hle⟩
  have nmono : ∀ (V W : Set (X → Y)) (ε : ℝ), V ⊆ W →
      (covering_number ℓ H V ε).toENNReal ≤ (covering_number ℓ H W ε).toENNReal :=
    fun V W ε h => ENat.toENNReal_mono (mono V W ε h)
  have n1 : ∀ (W : Set (X → Y)) (ε : ℝ), W.Nonempty →
      (1:ENNReal) ≤ (covering_number ℓ H W ε).toENNReal := by
    intro W ε hW; have := ENat.toENNReal_mono (pos W ε hW); simpa using this
  have ncover : ∀ (ε : ℝ), 0 < ε → ε < γ / (2 * c) →
      (covering_number ℓ H (version_space H T (u ++ [false])) ε).toENNReal
        + (covering_number ℓ H (version_space H T (u ++ [true])) ε).toENNReal
      ≤ (covering_number ℓ H (version_space H T u) ε).toENNReal := by
    intro ε hεpos hεlt
    have hcs := cover_sum ℓ c H T u ε hℓ ⟨M, hM⟩ hεpos hεlt
    have h2 := ENat.toENNReal_mono hcs
    rwa [ENat.toENNReal_add] at h2
  set μ := MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (diameter ℓ H)) with hμ
  set G : ENNReal → ENNReal :=
    fun x => if x = ⊤ then (⊤ : ENNReal) else ENNReal.ofReal (Real.logb 2 x.toReal) with hG
  have Gmono : Monotone G := by
    intro m n hmn
    simp only [hG]
    by_cases hn : n = ⊤
    · simp [hn]
    · have hm : m ≠ ⊤ := fun h => hn (top_le_iff.mp (h ▸ hmn))
      rw [if_neg hm, if_neg hn]
      rcases eq_or_ne m 0 with h0 | h0
      · subst h0; simp
      · exact ENNReal.ofReal_le_ofReal
          (Real.logb_le_logb_of_le (by norm_num) (ENNReal.toReal_pos h0 hm)
            (ENNReal.toReal_mono hn hmn))
  have Gmeas : Measurable G := by
    simp only [hG]
    refine Measurable.ite (measurableSet_singleton ⊤) measurable_const ?_
    apply ENNReal.measurable_ofReal.comp
    have hlogb : Measurable (fun r : ℝ => Real.logb 2 r) := by
      have h : (fun r : ℝ => Real.logb 2 r) = fun r => Real.log r / Real.log 2 := by
        funext r; rw [Real.logb]
      rw [h]; exact Real.measurable_log.div_const _
    exact hlogb.comp ENNReal.measurable_toReal
  have Gdrop : ∀ x y : ENNReal, 1 ≤ x → 2 * x ≤ y → G x + 1 ≤ G y := by
    intro x y hx hxy
    by_cases hy : y = ⊤
    · simp only [hG, if_pos hy]; exact le_top
    · have hxfin : x ≠ ⊤ := by
        rintro rfl; rw [ENNReal.mul_top (by norm_num)] at hxy; exact hy (top_le_iff.mp hxy)
      simp only [hG, if_neg hxfin, if_neg hy]
      have hxr : (1:ℝ) ≤ x.toReal := by have := ENNReal.toReal_mono hxfin hx; simpa using this
      have h2 : 2 * x.toReal ≤ y.toReal := by
        have := ENNReal.toReal_mono hy hxy
        rwa [ENNReal.toReal_mul, show ((2:ENNReal).toReal) = 2 by simp] at this
      have hstep : Real.logb 2 x.toReal + 1 ≤ Real.logb 2 y.toReal := by
        have hpos : (0:ℝ) < x.toReal := by linarith
        have h1 : Real.logb 2 x.toReal + 1 = Real.logb 2 (2 * x.toReal) := by
          rw [Real.logb_mul (by norm_num) (by positivity)]
          have h2' : Real.logb 2 2 = 1 := by rw [Real.logb_self_eq_one] <;> norm_num
          rw [h2']; ring
        rw [h1]; exact Real.logb_le_logb_of_le (by norm_num) (by positivity) h2
      calc ENNReal.ofReal (Real.logb 2 x.toReal) + 1
          = ENNReal.ofReal (Real.logb 2 x.toReal + 1) := by
            rw [ENNReal.ofReal_add (Real.logb_nonneg (by norm_num) hxr) (by norm_num),
              ENNReal.ofReal_one]
        _ ≤ ENNReal.ofReal (Real.logb 2 y.toReal) := ENNReal.ofReal_le_ofReal hstep
  have hphi : ∀ W : Set (X → Y), entropy_potential ℓ H W
      = ∫⁻ ε, G ((covering_number ℓ H W ε).toENNReal) ∂μ := by
    intro W
    unfold entropy_potential
    apply MeasureTheory.lintegral_congr
    intro ε
    simp only [hG]
    by_cases h : covering_number ℓ H W ε = ⊤
    · rw [if_pos h, if_pos (by simp [h])]
    · rw [if_neg h, if_neg (by simp [h])]
  have hγ0 : 0 ≤ γ := by rw [hγ]; exact hloss_nonneg _ _
  have hγdiam : γ ≤ diameter ℓ H := by
    obtain ⟨h0, h0mem⟩ := hne (u ++ [false])
    obtain ⟨h1, h1mem⟩ := hne (u ++ [true])
    have e0 : h0 (T.inst u) = T.edge u false := heval false h0 h0mem
    have e1 : h1 (T.inst u) = T.edge u true := heval true h1 h1mem
    have hdom01 := hdom h0 h0mem.1 h1 h1mem.1 (T.inst u)
    rw [e0, e1] at hdom01
    rw [hγ]
    exact le_trans hdom01 (hdiamge h0 h0mem.1 h1 h1mem.1)
  have hI0sub : Set.Ioo (0:ℝ) (γ / (2 * c)) ⊆ Set.Ioc (0:ℝ) (diameter ℓ H) := by
    intro ε hε
    refine ⟨hε.1, le_of_lt (lt_of_lt_of_le hε.2 ?_)⟩
    exact le_trans (div_le_self hγ0 (by linarith)) hγdiam
  set A : Bool → Set ℝ := fun b => Set.Ioc (0:ℝ) (diameter ℓ H) ∩
    {ε | 2 * (covering_number ℓ H (version_space H T (u ++ [b])) ε).toENNReal
      ≤ (covering_number ℓ H (version_space H T u) ε).toENNReal} with hA
  have hAmeas : ∀ b, MeasurableSet (A b) := by
    intro b
    refine MeasurableSet.inter measurableSet_Ioc ?_
    exact measurableSet_le (measurable_const.mul (measN _)) (measN _)
  have hunion : Set.Ioo (0:ℝ) (γ / (2 * c)) ⊆ A false ∪ A true := by
    intro ε hε
    have hcs := ncover ε hε.1 hε.2
    have hεD : ε ∈ Set.Ioc (0:ℝ) (diameter ℓ H) := hI0sub hε
    rcases le_total (covering_number ℓ H (version_space H T (u ++ [false])) ε).toENNReal
        (covering_number ℓ H (version_space H T (u ++ [true])) ε).toENNReal with hle | hle
    · refine Or.inl (Set.mem_inter hεD ?_)
      simp only [Set.mem_setOf_eq]
      calc 2 * (covering_number ℓ H (version_space H T (u ++ [false])) ε).toENNReal
          = (covering_number ℓ H (version_space H T (u ++ [false])) ε).toENNReal
            + (covering_number ℓ H (version_space H T (u ++ [false])) ε).toENNReal := two_mul _
        _ ≤ (covering_number ℓ H (version_space H T (u ++ [false])) ε).toENNReal
            + (covering_number ℓ H (version_space H T (u ++ [true])) ε).toENNReal := by gcongr
        _ ≤ _ := hcs
    · refine Or.inr (Set.mem_inter hεD ?_)
      simp only [Set.mem_setOf_eq]
      calc 2 * (covering_number ℓ H (version_space H T (u ++ [true])) ε).toENNReal
          = (covering_number ℓ H (version_space H T (u ++ [true])) ε).toENNReal
            + (covering_number ℓ H (version_space H T (u ++ [true])) ε).toENNReal := two_mul _
        _ ≤ (covering_number ℓ H (version_space H T (u ++ [false])) ε).toENNReal
            + (covering_number ℓ H (version_space H T (u ++ [true])) ε).toENNReal := by gcongr
        _ ≤ _ := hcs
  have hμI0 : μ (Set.Ioo (0:ℝ) (γ / (2 * c))) = ENNReal.ofReal (γ / (2 * c)) := by
    rw [hμ, MeasureTheory.Measure.restrict_apply measurableSet_Ioo,
      Set.inter_eq_self_of_subset_left hI0sub, Real.volume_Ioo]
    congr 1; ring
  have hhalf : (2:ENNReal) * ENNReal.ofReal (γ / (4 * c)) = ENNReal.ofReal (γ / (2 * c)) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; field_simp; ring
  have hsub_add : ENNReal.ofReal (γ / (2 * c)) ≤ μ (A false) + μ (A true) := by
    rw [← hμI0]
    exact le_trans (MeasureTheory.measure_mono hunion) (MeasureTheory.measure_union_le _ _)
  have hchoice : ENNReal.ofReal (γ / (4 * c)) ≤ μ (A false)
      ∨ ENNReal.ofReal (γ / (4 * c)) ≤ μ (A true) := by
    rcases le_or_gt (ENNReal.ofReal (γ / (4 * c))) (μ (A false)) with h0 | h0
    · exact Or.inl h0
    rcases le_or_gt (ENNReal.ofReal (γ / (4 * c))) (μ (A true)) with h1 | h1
    · exact Or.inr h1
    exfalso
    have hlt : μ (A false) + μ (A true)
        < ENNReal.ofReal (γ / (4 * c)) + ENNReal.ofReal (γ / (4 * c)) := ENNReal.add_lt_add h0 h1
    rw [← two_mul, hhalf] at hlt
    exact absurd (lt_of_le_of_lt hsub_add hlt) (lt_irrefl _)
  have key : ∀ b : Bool, ENNReal.ofReal (γ / (4 * c)) ≤ μ (A b) →
      entropy_potential ℓ H (version_space H T (u ++ [b])) ≤
        entropy_potential ℓ H (version_space H T u) - ENNReal.ofReal (γ / (4 * c)) := by
    intro b hb
    have step : entropy_potential ℓ H (version_space H T (u ++ [b])) + μ (A b) ≤
        entropy_potential ℓ H (version_space H T u) := by
      have hmf : Measurable (fun ε => G ((covering_number ℓ H (version_space H T (u ++ [b])) ε).toENNReal)) :=
        Gmeas.comp (measN (version_space H T (u ++ [b])))
      rw [hphi (version_space H T (u ++ [b])), hphi (version_space H T u),
        ← MeasureTheory.lintegral_indicator_one (hAmeas b),
        ← MeasureTheory.lintegral_add_left hmf]
      apply MeasureTheory.lintegral_mono
      intro ε
      dsimp only
      by_cases hεA : ε ∈ A b
      · rw [Set.indicator_of_mem hεA, Pi.one_apply]
        exact Gdrop _ _ (n1 _ ε (hne _)) hεA.2
      · rw [Set.indicator_of_notMem hεA, add_zero]
        exact Gmono (nmono _ _ ε (hsub b))
    refine ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top ?_
    calc entropy_potential ℓ H (version_space H T (u ++ [b])) + ENNReal.ofReal (γ / (4 * c))
        ≤ entropy_potential ℓ H (version_space H T (u ++ [b])) + μ (A b) := by gcongr
      _ ≤ entropy_potential ℓ H (version_space H T u) := step
  rcases hchoice with h | h
  · exact ⟨false, key false h⟩
  · exact ⟨true, key true h⟩

@[blueprint "lem:potential-lb"
  (statement := /-- Let $\ell$ be a $c$-approximate pseudo-metric with $c \ge 1$ (\cref{def:approx-pseudometric}) and let
$\mathcal{H}$ have finite diameter (\cref{def:finite-diameter}). Let $T$ be a scaled Littlestone tree realizable by
$\mathcal{H}$ (\cref{def:realizable-tree}) and let $u$ be an internal node with version space $U := U_u$
(\cref{def:version-space}). Then $\dfrac{\gamma_u}{4c} \le \Phi(U)$, where $\Phi$ is the entropy potential of
\cref{def:entropy-potential} and $\gamma_u$ the node gap of \cref{def:node-gap}. -/)
  (proof := /-- Set $\gamma := \gamma_u$ and $I := \bigl(0, \gamma/(2c)\bigr)$. Because $T$ is realizable by $\mathcal{H}$
(\cref{def:realizable-tree}), the edge labels $s_{u,0}, s_{u,1}$ leaving $u$ are attained by members of $\mathcal{H}$, so
$\gamma = \ell(s_{u,0}, s_{u,1}) \le \operatorname{diam}(\mathcal{H})$ (\cref{def:diameter}); since $c \ge 1$ this gives
$I \subseteq \bigl(0, \operatorname{diam}(\mathcal{H})\bigr)$, so $I$ lies in the domain of integration of $\Phi$
(\cref{def:entropy-potential}). Fix $\varepsilon \in I$. By \cref{lem:cover-sum},
$N(U_{u0},\varepsilon) + N(U_{u1},\varepsilon) \le N(U,\varepsilon)$ (\cref{def:covering-number}); since both children's
version spaces are non-empty (again by realizability), $N(U_{ub},\varepsilon) \ge 1$ for $b \in \{0,1\}$, so
$N(U,\varepsilon) \ge 2$ and hence $\log_2 N(U,\varepsilon) \ge 1$. Therefore the integrand of $\Phi(U)$ dominates the
indicator of $I$, and integrating gives
$\Phi(U) \ge \int_I 1\, d\varepsilon = |I| = \gamma/(2c) \ge \gamma/(4c)$. -/)
  (title := /-- Potential lower bound at an internal node -/)
  (latexEnv := "lemma")]
lemma potential_lb (ℓ : Y → Y → ℝ) (c : ℝ) (H : Set (X → Y)) (T : scaled_tree X Y)
    (u : List Bool) (hℓ : approx_pseudometric c ℓ) (hdiam : finite_diameter ℓ H)
    (hreal : realizable_tree H T) :
    ENNReal.ofReal (node_gap ℓ T u / (4 * c))
      ≤ entropy_potential ℓ H (version_space H T u) := by
  classical
  set γ := node_gap ℓ T u with hγ
  have hc : (1:ℝ) ≤ c := hℓ.1
  have hℓ0 := hℓ.2.1
  have htri := hℓ.2.2.2
  have hc' : (0:ℝ) < c := lt_of_lt_of_le one_pos hc
  haveI : Nonempty X := ⟨T.inst u⟩
  obtain ⟨M, hM⟩ := hdiam
  have hloss_nonneg : ∀ y1 y2, 0 ≤ ℓ y1 y2 := by
    intro y1 y2; have h := htri y1 y1 y2; rw [hℓ0] at h; nlinarith [h]
  have hbdd : ∀ f, f ∈ H → ∀ g, g ∈ H → BddAbove (Set.range fun x => ℓ (f x) (g x)) :=
    fun f hf g hg => ⟨M, by rintro y ⟨x, rfl⟩; exact hM f hf g hg x⟩
  have hdom : ∀ f, f ∈ H → ∀ g, g ∈ H → ∀ x, ℓ (f x) (g x) ≤ induced_metric ℓ f g :=
    fun f hf g hg x => le_ciSup (hbdd f hf g hg) x
  have hdiamge : ∀ f, f ∈ H → ∀ g, g ∈ H → induced_metric ℓ f g ≤ diameter ℓ H := by
    intro f hf g hg
    haveI : Nonempty H := ⟨⟨f, hf⟩⟩
    have hbddOuter : BddAbove (Set.range fun p : H => (⨆ q : H, induced_metric ℓ p.1 q.1)) := by
      refine ⟨M, ?_⟩; rintro y ⟨p, rfl⟩; apply ciSup_le; intro q; apply ciSup_le; intro x
      exact hM p.1 p.2 q.1 q.2 x
    have hbddInner : ∀ p : H, BddAbove (Set.range fun q : H => induced_metric ℓ p.1 q.1) :=
      fun p => ⟨M, by rintro y ⟨q, rfl⟩; apply ciSup_le; intro x; exact hM p.1 p.2 q.1 q.2 x⟩
    calc induced_metric ℓ f g ≤ ⨆ q : H, induced_metric ℓ (⟨f, hf⟩ : H).1 q.1 :=
          le_ciSup (hbddInner ⟨f, hf⟩) (⟨g, hg⟩ : H)
      _ ≤ diameter ℓ H := le_ciSup hbddOuter (⟨f, hf⟩ : H)
  have hne : ∀ w : List Bool, (version_space H T w).Nonempty := by
    intro w
    obtain ⟨h, hh, hcond⟩ := hreal (fun i => w.getD i false) w.length
    refine ⟨h, hh, ?_⟩
    intro t ht
    have hpref : branch_prefix (fun i => w.getD i false) t = w.take t := by
      apply List.ext_getElem
      · simp [branch_prefix]; omega
      · intro i h1 h2
        simp only [List.length_take, lt_min_iff] at h2
        simp only [branch_prefix, List.getElem_map, List.getElem_range]
        rw [List.getElem_take]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, h2.2]
    have hc2 := hcond t ht
    rw [hpref] at hc2
    rw [hc2]; congr 1
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, ht]
  have heval : ∀ (b : Bool) (h : X → Y),
      h ∈ version_space H T (u ++ [b]) → h (T.inst u) = T.edge u b := by
    intro b h hh
    have hlen : u.length < (u ++ [b]).length := by simp
    have hcond := hh.2 u.length hlen
    rw [List.take_append_length] at hcond
    rw [List.getElem_concat_length rfl] at hcond
    exact hcond
  have hsub : ∀ (b : Bool), version_space H T (u ++ [b]) ⊆ version_space H T u := by
    intro b h hh
    refine ⟨hh.1, ?_⟩
    intro t ht
    have hlen : t < (u ++ [b]).length := by rw [List.length_append]; omega
    have hcond := hh.2 t hlen
    rw [List.take_append_of_le_length (le_of_lt ht), List.getElem_append_left ht] at hcond
    exact hcond
  have pos : ∀ (W : Set (X → Y)) (ε : ℝ), W.Nonempty → 1 ≤ covering_number ℓ H W ε := by
    intro W ε hW
    obtain ⟨u0, hu0⟩ := hW
    apply le_sInf
    rintro n ⟨S, hSH, rfl, hcov⟩
    obtain ⟨s, hs, -⟩ := hcov u0 hu0
    have hSne : S.Nonempty := ⟨s, hs⟩
    exact_mod_cast hSne.card_pos
  have measN : ∀ (W : Set (X → Y)),
      Measurable (fun ε => (covering_number ℓ H W ε).toENNReal) := by
    intro W
    refine Antitone.measurable ?_
    intro ε ε' hle
    apply ENat.toENNReal_mono
    apply sInf_le_sInf
    rintro n ⟨S, hSH, hcard, hcov⟩
    refine ⟨S, hSH, hcard, fun v hv => ?_⟩
    obtain ⟨s, hs, hds⟩ := hcov v hv
    exact ⟨s, hs, le_trans hds hle⟩
  have n1 : ∀ (W : Set (X → Y)) (ε : ℝ), W.Nonempty →
      (1:ENNReal) ≤ (covering_number ℓ H W ε).toENNReal := by
    intro W ε hW; have := ENat.toENNReal_mono (pos W ε hW); simpa using this
  have ncover : ∀ (ε : ℝ), 0 < ε → ε < γ / (2 * c) →
      (covering_number ℓ H (version_space H T (u ++ [false])) ε).toENNReal
        + (covering_number ℓ H (version_space H T (u ++ [true])) ε).toENNReal
      ≤ (covering_number ℓ H (version_space H T u) ε).toENNReal := by
    intro ε hεpos hεlt
    have hcs := cover_sum ℓ c H T u ε hℓ ⟨M, hM⟩ hεpos hεlt
    have h2 := ENat.toENNReal_mono hcs
    rwa [ENat.toENNReal_add] at h2
  set μ := MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (diameter ℓ H)) with hμ
  set G : ENNReal → ENNReal :=
    fun x => if x = ⊤ then (⊤ : ENNReal) else ENNReal.ofReal (Real.logb 2 x.toReal) with hG
  have hphi : ∀ W : Set (X → Y), entropy_potential ℓ H W
      = ∫⁻ ε, G ((covering_number ℓ H W ε).toENNReal) ∂μ := by
    intro W
    unfold entropy_potential
    apply MeasureTheory.lintegral_congr
    intro ε
    simp only [hG]
    by_cases h : covering_number ℓ H W ε = ⊤
    · rw [if_pos h, if_pos (by simp [h])]
    · rw [if_neg h, if_neg (by simp [h])]
  have hG2 : G 2 = 1 := by
    simp only [hG]; rw [if_neg (by norm_num)]; norm_num [Real.logb_self_eq_one]
  have Gmono : Monotone G := by
    intro m n hmn
    simp only [hG]
    by_cases hn : n = ⊤
    · simp [hn]
    · have hm : m ≠ ⊤ := fun h => hn (top_le_iff.mp (h ▸ hmn))
      rw [if_neg hm, if_neg hn]
      rcases eq_or_ne m 0 with h0 | h0
      · subst h0; simp
      · exact ENNReal.ofReal_le_ofReal
          (Real.logb_le_logb_of_le (by norm_num) (ENNReal.toReal_pos h0 hm)
            (ENNReal.toReal_mono hn hmn))
  have hγ0 : 0 ≤ γ := by rw [hγ]; exact hloss_nonneg _ _
  have hγdiam : γ ≤ diameter ℓ H := by
    obtain ⟨h0, h0mem⟩ := hne (u ++ [false])
    obtain ⟨h1, h1mem⟩ := hne (u ++ [true])
    have e0 : h0 (T.inst u) = T.edge u false := heval false h0 h0mem
    have e1 : h1 (T.inst u) = T.edge u true := heval true h1 h1mem
    have hdom01 := hdom h0 h0mem.1 h1 h1mem.1 (T.inst u)
    rw [e0, e1] at hdom01
    rw [hγ]
    exact le_trans hdom01 (hdiamge h0 h0mem.1 h1 h1mem.1)
  have hI0sub : Set.Ioo (0:ℝ) (γ / (2 * c)) ⊆ Set.Ioc (0:ℝ) (diameter ℓ H) := by
    intro ε hε
    refine ⟨hε.1, le_of_lt (lt_of_lt_of_le hε.2 ?_)⟩
    exact le_trans (div_le_self hγ0 (by linarith)) hγdiam
  have hμI0 : μ (Set.Ioo (0:ℝ) (γ / (2 * c))) = ENNReal.ofReal (γ / (2 * c)) := by
    rw [hμ, MeasureTheory.Measure.restrict_apply measurableSet_Ioo,
      Set.inter_eq_self_of_subset_left hI0sub, Real.volume_Ioo]
    congr 1; ring
  have hind : ∀ ε, (Set.Ioo (0:ℝ) (γ / (2 * c))).indicator (fun _ => (1:ENNReal)) ε
      ≤ G ((covering_number ℓ H (version_space H T u) ε).toENNReal) := by
    intro ε
    by_cases hεI : ε ∈ Set.Ioo (0:ℝ) (γ / (2 * c))
    · rw [Set.indicator_of_mem hεI]
      have hcs := ncover ε hεI.1 hεI.2
      have h2le : (2:ENNReal)
          ≤ (covering_number ℓ H (version_space H T u) ε).toENNReal := by
        calc (2:ENNReal) = 1 + 1 := by norm_num
          _ ≤ (covering_number ℓ H (version_space H T (u ++ [false])) ε).toENNReal
              + (covering_number ℓ H (version_space H T (u ++ [true])) ε).toENNReal :=
                add_le_add (n1 _ ε (hne _)) (n1 _ ε (hne _))
          _ ≤ _ := hcs
      calc (1:ENNReal) = G 2 := hG2.symm
        _ ≤ G ((covering_number ℓ H (version_space H T u) ε).toENNReal) := Gmono h2le
    · rw [Set.indicator_of_notMem hεI]; exact bot_le
  calc ENNReal.ofReal (γ / (4 * c))
      ≤ ENNReal.ofReal (γ / (2 * c)) := by
        apply ENNReal.ofReal_le_ofReal; gcongr <;> linarith
    _ = μ (Set.Ioo (0:ℝ) (γ / (2 * c))) := hμI0.symm
    _ = ∫⁻ ε, (Set.Ioo (0:ℝ) (γ / (2 * c))).indicator (fun _ => (1:ENNReal)) ε ∂μ :=
        (MeasureTheory.lintegral_indicator_one measurableSet_Ioo).symm
    _ ≤ ∫⁻ ε, G ((covering_number ℓ H (version_space H T u) ε).toENNReal) ∂μ :=
        MeasureTheory.lintegral_mono hind
    _ = entropy_potential ℓ H (version_space H T u) := (hphi _).symm

@[blueprint "lem:potential-drop-add"
  (statement := /-- Let $\ell$ be a $c$-approximate pseudo-metric with $c \ge 1$ (\cref{def:approx-pseudometric}) and let
$\mathcal{H}$ have finite diameter (\cref{def:finite-diameter}). Let $T$ be a scaled Littlestone tree realizable by
$\mathcal{H}$ (\cref{def:realizable-tree}) and let $u$ be an internal node with version space $U := U_u$ and children
version spaces $U_0, U_1$ (\cref{def:version-space}). Then there exists $b \in \{0,1\}$ such that
$\Phi(U_b) + \dfrac{\gamma_u}{4c} \le \Phi(U)$, where $\Phi$ is the entropy potential of \cref{def:entropy-potential}
and $\gamma_u$ the node gap of \cref{def:node-gap}. -/)
  (proof := /-- By \cref{lem:potential-drop} there is $b \in \{0,1\}$ with
$\Phi(U_b) \le \Phi(U) - \gamma_u/(4c)$ in the truncated subtraction on $[0,+\infty]$. By \cref{lem:potential-lb},
$\gamma_u/(4c) \le \Phi(U)$, so the truncated subtraction is genuine and adding $\gamma_u/(4c)$ to both sides yields
$\Phi(U_b) + \gamma_u/(4c) \le \bigl(\Phi(U) - \gamma_u/(4c)\bigr) + \gamma_u/(4c) = \Phi(U)$. -/)
  (title := /-- One-step potential drop, additive form -/)
  (latexEnv := "lemma")]
lemma potential_drop_add (ℓ : Y → Y → ℝ) (c : ℝ) (H : Set (X → Y)) (T : scaled_tree X Y)
    (u : List Bool) (hℓ : approx_pseudometric c ℓ) (hdiam : finite_diameter ℓ H)
    (hreal : realizable_tree H T) :
    ∃ b : Bool, entropy_potential ℓ H (version_space H T (u ++ [b]))
      + ENNReal.ofReal (node_gap ℓ T u / (4 * c))
      ≤ entropy_potential ℓ H (version_space H T u) := by
  obtain ⟨b, hb⟩ := potential_drop ℓ c H T u hℓ hdiam hreal
  refine ⟨b, ?_⟩
  have hlb : ENNReal.ofReal (node_gap ℓ T u / (4 * c))
      ≤ entropy_potential ℓ H (version_space H T u) :=
    potential_lb ℓ c H T u hℓ hdiam hreal
  calc entropy_potential ℓ H (version_space H T (u ++ [b]))
        + ENNReal.ofReal (node_gap ℓ T u / (4 * c))
      ≤ (entropy_potential ℓ H (version_space H T u)
          - ENNReal.ofReal (node_gap ℓ T u / (4 * c)))
        + ENNReal.ofReal (node_gap ℓ T u / (4 * c)) := by gcongr
    _ = entropy_potential ℓ H (version_space H T u) := tsub_add_cancel_of_le hlb

@[blueprint "thm:potential-bound-general"
  (statement := /-- Let $T$ be a scaled Littlestone tree realizable by $\mathcal{H}$ (\cref{def:realizable-tree}), let
$\ell$ be a $c$-approximate pseudo-metric with $c \ge 1$ (\cref{def:approx-pseudometric}), and let $\mathcal{H}$ have
finite diameter (\cref{def:finite-diameter}). Then there exists a branch $b : \mathbb{N} \to \{0,1\}$ such that
$\sum_{i \ge 0} \gamma_{b_{\le i}} \le 4c\,\Phi(\mathcal{H})$, where $\gamma$ is the node gap of \cref{def:node-gap},
$b_{\le i}$ the prefix of \cref{def:branch-prefix}, and $\Phi$ the entropy potential of \cref{def:entropy-potential}. -/)
  (proof := /-- If $\Phi(\mathcal{H}) = +\infty$ then $4c\,\Phi(\mathcal{H}) = +\infty$ and the bound is trivial, so
the greedy construction works with the additive potential drop on $[0,+\infty]$ (no finiteness assumption is needed). Construct the
branch $b$ greedily: at each node $u$ reached, \cref{lem:potential-drop-add} provides a child bit $g(u) \in \{0,1\}$ with
$\Phi(U_{u\,g(u)}) + \dfrac{\gamma_u}{4c} \le \Phi(U_u)$, where $\gamma_u$ is the node gap of \cref{def:node-gap} and $\Phi$
the entropy potential of \cref{def:entropy-potential}. Define the nodes $u_0 := ()$ and $u_{n+1} := u_n \,g(u_n)$, and let
$b(n) := g(u_n)$, so that $b_{\le n} = u_n$ is the prefix of \cref{def:branch-prefix}. Writing $\Phi_n := \Phi(U_{u_n})$ and
$d_n := \gamma_{u_n}/(4c)$, the additive one-step bound reads $\Phi_{n+1} + d_n \le \Phi_n$. Telescoping by induction on $n$ gives,
for every $n$, $\sum_{i=0}^{n-1} d_i + \Phi_n \le \Phi_0$. Since $u_0 = ()$ has version space $\mathcal{H}$ (\cref{def:version-space}),
$\Phi_0 = \Phi(\mathcal{H})$, and dropping the non-negative term $\Phi_n$ yields $\sum_{i=0}^{n-1} d_i \le \Phi(\mathcal{H})$ for all
$n$. Passing to the supremum over $n$ gives $\sum_{i \ge 0} \dfrac{\gamma_{b_{\le i}}}{4c} \le \Phi(\mathcal{H})$. Multiplying the
non-negative term-by-term through by $4c$ and using $\gamma_{b_{\le i}} = 4c \cdot d_i$ gives
$\sum_{i \ge 0} \gamma_{b_{\le i}} \le 4c\,\Phi(\mathcal{H})$. -/)
  (title := /-- Entropy-potential upper bound -/)
  (latexEnv := "theorem")]
theorem potential_bound_general (ℓ : Y → Y → ℝ) (c : ℝ) (H : Set (X → Y))
    (T : scaled_tree X Y) (hℓ : approx_pseudometric c ℓ) (hdiam : finite_diameter ℓ H)
    (hreal : realizable_tree H T) :
    ∃ b : ℕ → Bool,
      ∑' i : ℕ, ENNReal.ofReal (node_gap ℓ T (branch_prefix b i))
        ≤ ENNReal.ofReal (4 * c) * entropy_potential ℓ H H := by
  classical
  have hc : (1:ℝ) ≤ c := hℓ.1
  have hc' : (0:ℝ) < c := lt_of_lt_of_le one_pos hc
  have hex : ∀ u : List Bool, ∃ b : Bool,
      entropy_potential ℓ H (version_space H T (u ++ [b]))
        + ENNReal.ofReal (node_gap ℓ T u / (4 * c))
        ≤ entropy_potential ℓ H (version_space H T u) :=
    fun u => potential_drop_add ℓ c H T u hℓ hdiam hreal
  choose g hgspec using hex
  set path : ℕ → List Bool :=
    fun n => Nat.rec (motive := fun _ => List Bool) [] (fun _ u => u ++ [g u]) n with hpath
  have hpath0 : path 0 = [] := rfl
  have hpathS : ∀ n, path (n + 1) = path n ++ [g (path n)] := fun n => rfl
  set bfun : ℕ → Bool := fun n => g (path n) with hbfun
  have hbranch : ∀ n, branch_prefix bfun n = path n := by
    intro n
    induction n with
    | zero => simp [branch_prefix, hpath0]
    | succ k ih =>
      have hb : branch_prefix bfun (k + 1) = branch_prefix bfun k ++ [bfun k] := by
        simp [branch_prefix, List.range_succ]
      rw [hb, ih]
  set Φn : ℕ → ENNReal := fun n => entropy_potential ℓ H (version_space H T (path n)) with hΦn
  set d : ℕ → ENNReal := fun n => ENNReal.ofReal (node_gap ℓ T (path n) / (4 * c)) with hd
  have hstep : ∀ n, Φn (n + 1) + d n ≤ Φn n := by
    intro n
    simp only [hΦn, hd]
    rw [hpathS n]
    exact hgspec (path n)
  have htel : ∀ n, (∑ i ∈ Finset.range n, d i) + Φn n ≤ Φn 0 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      calc (∑ i ∈ Finset.range k, d i) + d k + Φn (k + 1)
          = (∑ i ∈ Finset.range k, d i) + (Φn (k + 1) + d k) := by ring
        _ ≤ (∑ i ∈ Finset.range k, d i) + Φn k := by gcongr; exact hstep k
        _ ≤ Φn 0 := ih
  have hvs : version_space H T [] = H := by ext h; simp [version_space]
  have hΦ0 : Φn 0 = entropy_potential ℓ H H := by
    simp only [hΦn, hpath0, hvs]
  have hpartial : ∀ n, (∑ i ∈ Finset.range n, d i) ≤ entropy_potential ℓ H H := by
    intro n
    calc (∑ i ∈ Finset.range n, d i)
        ≤ (∑ i ∈ Finset.range n, d i) + Φn n := le_self_add
      _ ≤ Φn 0 := htel n
      _ = entropy_potential ℓ H H := hΦ0
  have hsum_d : (∑' i, d i) ≤ entropy_potential ℓ H H := by
    rw [ENNReal.tsum_eq_iSup_nat]; exact iSup_le hpartial
  have hrw : ∀ i, ENNReal.ofReal (node_gap ℓ T (branch_prefix bfun i))
      = ENNReal.ofReal (4 * c) * d i := by
    intro i
    rw [hbranch i]
    simp only [hd]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  refine ⟨bfun, ?_⟩
  calc ∑' i, ENNReal.ofReal (node_gap ℓ T (branch_prefix bfun i))
      = ∑' i, ENNReal.ofReal (4 * c) * d i := tsum_congr hrw
    _ = ENNReal.ofReal (4 * c) * ∑' i, d i := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (4 * c) * entropy_potential ℓ H H :=
        mul_le_mul_left' hsum_d _

@[blueprint "thm:intro_Donl-via-Phi"
  (statement := /-- Assume $\ell$ is a $c$-approximate pseudo-metric for some $c \ge 1$ (\cref{def:approx-pseudometric})
and that $\operatorname{diam}(\mathcal{H}) < \infty$ (\cref{def:finite-diameter}). Then the online dimension
(\cref{def:online-dim}) is bounded by the entropy potential (\cref{def:entropy-potential}):
$\mathbb{D}_{\mathrm{onl}}(\mathcal{H}) \le 4c \cdot \Phi(\mathcal{H})$. -/)
  (proof := /-- Fix any scaled Littlestone tree $T$ realizable by $\mathcal{H}$. By \cref{thm:potential-bound-general}
there exists a branch $b \in \mathcal{P}(T)$ with $\sum_{i \ge 0} \gamma_{b_{\le i}} \le 4c\,\Phi(\mathcal{H})$. Therefore
$\inf_{b \in \mathcal{P}(T)} \sum_{i \ge 0} \gamma_{b_{\le i}} \le 4c\,\Phi(\mathcal{H})$. Taking the supremum over all
trees $T$ realizable by $\mathcal{H}$ in the definition of $\mathbb{D}_{\mathrm{onl}}(\mathcal{H})$ (\cref{def:online-dim})
yields $\mathbb{D}_{\mathrm{onl}}(\mathcal{H}) \le 4c\,\Phi(\mathcal{H})$. -/)
  (title := /-- Online dimension via entropy potential -/)
  (latexEnv := "theorem")]
theorem intro_Donl_via_Phi (ℓ : Y → Y → ℝ) (c : ℝ) (H : Set (X → Y))
    (hℓ : approx_pseudometric c ℓ) (hdiam : finite_diameter ℓ H) :
    online_dim ℓ H ≤ ENNReal.ofReal (4 * c) * entropy_potential ℓ H H := by
  refine iSup_le (fun T => iSup_le (fun hreal => ?_))
  obtain ⟨b, hb⟩ := potential_bound_general ℓ c H T hℓ hdiam hreal
  exact le_trans (iInf_le _ b) hb

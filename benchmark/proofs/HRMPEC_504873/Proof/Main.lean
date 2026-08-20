import Architect
import Mathlib.InformationTheory.Hamming
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Finsupp.Fin
import Mathlib.Data.Real.Basic

set_option linter.all false
set_option maxHeartbeats 500000

variable {F : Type*} [Field F] [DecidableEq F]

@[blueprint "def:hyperplane"
  (statement := /-- An affine hyperplane in $\mathbb{F}^m$ is a pair consisting of a nonzero
  normal vector $a \in \mathbb{F}^m$ and an offset $b \in \mathbb{F}$; it represents the affine
  subspace of all points $x \in \mathbb{F}^m$ with $\sum_{i} a_i x_i = b$. -/)
  (title := /-- Affine hyperplane -/)
  (latexEnv := "definition")]
structure hyperplane (m : ℕ) (K : Type*) [Field K] where
  normal : Fin m → K
  offset : K
  normal_ne_zero : normal ≠ 0

@[blueprint "def:on-hyperplane"
  (statement := /-- A point $x \in \mathbb{F}^m$ lies on the hyperplane $h$ with normal $a$ and
  offset $b$ if and only if $\sum_{i} a_i x_i = b$. -/)
  (title := /-- Incidence of a point with a hyperplane -/)
  (latexEnv := "definition")]
def on_hyperplane {m : ℕ} (h : hyperplane m F) (x : Fin m → F) : Prop :=
  ∑ i, h.normal i * x i = h.offset

@[blueprint "def:in-general-position"
  (statement := /-- A finite set $\mathcal{H}$ of hyperplanes in $\mathbb{F}^m$ is in general
  position if every subset of size $m$ has exactly one common incident point and no subset of
  size $m+1$ has any common incident point, where incidence is as in \cref{def:on-hyperplane}. -/)
  (title := /-- Hyperplanes in general position -/)
  (latexEnv := "definition")]
def in_general_position {m : ℕ} (H : Finset (hyperplane m F)) : Prop :=
  (∀ S ⊆ H, S.card = m → ∃! x : Fin m → F, ∀ h ∈ S, on_hyperplane h x) ∧
    (∀ S ⊆ H, S.card = m + 1 → ¬∃ x : Fin m → F, ∀ h ∈ S, on_hyperplane h x)

@[blueprint "def:gap-domain"
  (statement := /-- For $m, t \in \mathbb{N}$, a finite set $T \subseteq \mathbb{F}^m$ is a GAP
  domain with parameters $(m, t)$ if there is a finite set $\mathcal{H}$ of exactly $t$ hyperplanes
  in general position (see \cref{def:in-general-position}) such that $T$ is exactly the set of
  points that are the common incident point of some $m$-element subset of $\mathcal{H}$
  (incidence as in \cref{def:on-hyperplane}). -/)
  (title := /-- GAP evaluation domain -/)
  (latexEnv := "definition")]
def gap_domain (m t : ℕ) (T : Finset (Fin m → F)) : Prop :=
  ∃ H : Finset (hyperplane m F), H.card = t ∧ in_general_position H ∧
    ∀ x : Fin m → F, x ∈ T ↔ ∃ S ⊆ H, S.card = m ∧ ∀ h ∈ S, on_hyperplane h x

@[blueprint "def:poly-eval-map"
  (statement := /-- For a finite set $T \subseteq \mathbb{F}^m$, the evaluation map sends an
  $m$-variate polynomial $p \in \mathbb{F}[X_1, \dots, X_m]$ to the tuple $(p(x))_{x \in T}$ in
  $\mathbb{F}^T$. It is an $\mathbb{F}$-linear map. -/)
  (title := /-- Polynomial evaluation map on a point set -/)
  (latexEnv := "definition")]
noncomputable def poly_eval_map (m : ℕ) (T : Finset (Fin m → F)) :
    MvPolynomial (Fin m) F →ₗ[F] (↥T → F) :=
  LinearMap.pi fun x : ↥T => (MvPolynomial.aeval (x : Fin m → F)).toLinearMap

@[blueprint "def:gap-code"
  (statement := /-- For $m, d \in \mathbb{N}$ and a finite set $T \subseteq \mathbb{F}^m$, the GAP
  code $\mathrm{GAP}_{m,d,T}$ is the image, under the evaluation map of \cref{def:poly-eval-map}, of
  the $\mathbb{F}$-vector space of $m$-variate polynomials of total degree at most $d$. It is an
  $\mathbb{F}$-linear subspace of $\mathbb{F}^T$. -/)
  (title := /-- GAP code -/)
  (latexEnv := "definition")]
noncomputable def gap_code (m d : ℕ) (T : Finset (Fin m → F)) : Submodule F (↥T → F) :=
  (MvPolynomial.restrictTotalDegree (Fin m) F d).map (poly_eval_map m T)

@[blueprint "def:hitting-set"
  (statement := /-- A finite set $S \subseteq \mathbb{F}^m$ is a hitting set for $m$-variate
  polynomials of degree at most $d$ if for every nonzero polynomial $f$ with total degree at most
  $d$ there is a point $x \in S$ with $f(x) \neq 0$. -/)
  (title := /-- Hitting set -/)
  (latexEnv := "definition")]
def hitting_set (m d : ℕ) (S : Finset (Fin m → F)) : Prop :=
  ∀ f : MvPolynomial (Fin m) F, f ≠ 0 → f.totalDegree ≤ d →
    ∃ x ∈ S, MvPolynomial.eval x f ≠ 0

@[blueprint "def:interpolating-set"
  (statement := /-- A finite set $S \subseteq \mathbb{F}^m$ is an interpolating set for $m$-variate
  polynomials of degree at most $d$ if for every function $g : S \to \mathbb{F}$ there is a unique
  polynomial $p$ with total degree at most $d$ such that $p(a) = g(a)$ for all $a \in S$. -/)
  (title := /-- Interpolating set -/)
  (latexEnv := "definition")]
def interpolating_set (m d : ℕ) (S : Finset (Fin m → F)) : Prop :=
  ∀ g : ↥S → F, ∃! p : MvPolynomial (Fin m) F,
    p.totalDegree ≤ d ∧ ∀ a : ↥S, MvPolynomial.eval (a : Fin m → F) p = g a

@[blueprint "def:code-min-dist"
  (statement := /-- The minimum distance of a code $C \subseteq \mathbb{F}^{\iota}$ is the least
  Hamming distance between two distinct codewords of $C$. -/)
  (title := /-- Minimum distance of a code -/)
  (latexEnv := "definition")]
noncomputable def code_min_dist {ι : Type*} [Fintype ι] (C : Submodule F (ι → F)) : ℕ :=
  sInf {w : ℕ | ∃ c₁ ∈ C, ∃ c₂ ∈ C, c₁ ≠ c₂ ∧ hammingDist c₁ c₂ = w}

@[blueprint "def:code-rate"
  (statement := /-- The rate of a linear code $C \subseteq \mathbb{F}^{\iota}$ is the ratio
  $\dim_{\mathbb{F}} C / |\iota|$ of its $\mathbb{F}$-dimension to its block length. For a finite
  field this equals $\log_{|\mathbb{F}|} |C| / |\iota|$. -/)
  (title := /-- Rate of a linear code -/)
  (latexEnv := "definition")]
noncomputable def code_rate {ι : Type*} [Fintype ι] (C : Submodule F (ι → F)) : ℝ :=
  (Module.finrank F C : ℝ) / (Fintype.card ι : ℝ)

@[blueprint "def:code-rel-dist"
  (statement := /-- The relative distance of a code $C \subseteq \mathbb{F}^{\iota}$ is its minimum
  distance (see \cref{def:code-min-dist}) divided by its block length $|\iota|$. -/)
  (title := /-- Relative distance of a code -/)
  (latexEnv := "definition")]
noncomputable def code_rel_dist {ι : Type*} [Fintype ι] (C : Submodule F (ι → F)) : ℝ :=
  (code_min_dist C : ℝ) / (Fintype.card ι : ℝ)

@[blueprint "lem:findrank-deg-le-choose"
  (statement := /-- For $m, D \in \mathbb{N}$, the $\mathbb{F}$-dimension of the submodule of
  $m$-variate polynomials over $\mathbb{F}$ of total degree at most $D$ equals $\binom{m + D}{m}$. -/)
  (proof := /-- The submodule of polynomials of total degree at most $D$ has the canonical basis
  indexed by the exponent tuples $s \in \mathbb{N}^{\{1,\dots,m\}}$ with $\sum_i s_i \le D$, so its
  dimension is the number of such tuples. Prepending a slack coordinate $s_0 = D - \sum_i s_i$ gives
  a bijection between those tuples and the tuples in $\mathbb{N}^{\{0,1,\dots,m\}}$ summing to
  exactly $D$; by the stars-and-bars count there are $\binom{(m+1) + D - 1}{D} = \binom{m + D}{D}$ of
  them. Since $\binom{m + D}{D} = \binom{m + D}{m}$, the dimension equals $\binom{m + D}{m}$. -/)
  (title := /-- Dimension of the bounded total degree polynomial space -/)
  (latexEnv := "lemma")]
lemma findrank_deg_le_choose (m D : ℕ) :
    Module.finrank F (MvPolynomial.restrictTotalDegree (Fin m) F D) = (m + D).choose m := by
  classical
  have hc : ∀ (a : ℕ) (σ : Fin m →₀ ℕ),
      (Finsupp.cons a σ).sum (fun _ e => e) = a + σ.sum (fun _ e => e) := by
    intro a σ
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.sum_fintype _ _ (fun _ => rfl),
      Fin.sum_univ_succ, Finsupp.cons_zero]
    simp [Finsupp.cons_succ]
  have e : {n : Fin m →₀ ℕ // (n.sum fun _ e => e) ≤ D} ≃
      ↥(Finset.finsuppAntidiag (Finset.univ : Finset (Fin (m + 1))) D) :=
    { toFun := fun n => ⟨Finsupp.cons (D - (n.1.sum fun _ e => e)) n.1, by
        have hn := n.2
        rw [Finset.mem_finsuppAntidiag']
        refine ⟨?_, Finset.subset_univ _⟩
        rw [hc]
        omega⟩
      invFun := fun f => ⟨Finsupp.tail f.1, by
        have hf : (f.1.sum fun _ e => e) = D := (Finset.mem_finsuppAntidiag'.1 f.2).1
        have hcons := hc (f.1 0) (Finsupp.tail f.1)
        rw [Finsupp.cons_tail] at hcons
        omega⟩
      left_inv := fun n => by
        apply Subtype.ext
        simp only [Finsupp.tail_cons]
      right_inv := fun f => by
        apply Subtype.ext
        dsimp only
        have hf : (f.1.sum fun _ e => e) = D := (Finset.mem_finsuppAntidiag'.1 f.2).1
        have hcons := hc (f.1 0) (Finsupp.tail f.1)
        rw [Finsupp.cons_tail] at hcons
        have h0 : D - ((Finsupp.tail f.1).sum fun _ e => e) = f.1 0 := by omega
        rw [h0, Finsupp.cons_tail] }
  have hb : Module.finrank F (MvPolynomial.restrictTotalDegree (Fin m) F D)
      = Nat.card {n : Fin m →₀ ℕ // (n.sum fun _ e => e) ≤ D} :=
    Module.finrank_eq_nat_card_basis
      (MvPolynomial.basisRestrictSupport F {n : Fin m →₀ ℕ | (n.sum fun _ e => e) ≤ D})
  rw [hb, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin]
  have : m + 1 + D - 1 = m + D := by omega
  rw [this]
  exact Nat.choose_symm_add.symm

@[blueprint "lem:card-incident-le"
  (statement := /-- Let $m \in \mathbb{N}$ and let $\mathcal{H}$ be a finite set of hyperplanes in
  $\mathbb{F}^m$ in general position (see \cref{def:in-general-position}). Then for every point
  $z \in \mathbb{F}^m$ and every subset $S \subseteq \mathcal{H}$ all of whose hyperplanes are
  incident to $z$ (see \cref{def:on-hyperplane}), we have $|S| \le m$. -/)
  (proof := /-- Suppose $|S| > m$, i.e. $|S| \ge m + 1$. Choose a subset $S' \subseteq S$ with
  $|S'| = m + 1$. Then $S' \subseteq \mathcal{H}$ and every hyperplane of $S'$ is incident to $z$,
  so $z$ is a common incident point of an $(m+1)$-element subset of $\mathcal{H}$, contradicting the
  general-position condition (see \cref{def:in-general-position}). Hence $|S| \le m$. -/)
  (title := /-- At most $m$ hyperplanes through a point -/)
  (latexEnv := "lemma")]
lemma card_incident_le (m : ℕ) (H : Finset (hyperplane m F)) (hgp : in_general_position H)
    (z : Fin m → F) (S : Finset (hyperplane m F)) (hSH : S ⊆ H)
    (hz : ∀ h ∈ S, on_hyperplane h z) : S.card ≤ m := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨S', hS'sub, hS'card⟩ :=
    Finset.exists_subset_card_eq (show m + 1 ≤ S.card by omega)
  exact hgp.2 S' (hS'sub.trans hSH) hS'card ⟨z, fun h hh => hz h (hS'sub hh)⟩

@[blueprint "lem:incident-msubset-eq"
  (statement := /-- Let $m \in \mathbb{N}$ and let $\mathcal{H}$ be a finite set of hyperplanes in
  $\mathbb{F}^m$ in general position (see \cref{def:in-general-position}). If $S_1, S_2 \subseteq
  \mathcal{H}$ each have exactly $m$ elements and every hyperplane of $S_1$ and of $S_2$ is incident
  to a common point $z$ (see \cref{def:on-hyperplane}), then $S_1 = S_2$. -/)
  (proof := /-- The union $S_1 \cup S_2 \subseteq \mathcal{H}$ consists of hyperplanes all incident
  to $z$, so by \cref{lem:card-incident-le} we have $|S_1 \cup S_2| \le m$. Since $S_1 \subseteq
  S_1 \cup S_2$ and $|S_1| = m$, the inequality $|S_1 \cup S_2| \le |S_1|$ forces $S_1 = S_1 \cup
  S_2$. The same argument gives $S_2 = S_1 \cup S_2$, hence $S_1 = S_2$. -/)
  (title := /-- Uniqueness of the incident $m$-subset -/)
  (latexEnv := "lemma")]
lemma incident_msubset_eq (m : ℕ) (H : Finset (hyperplane m F)) (hgp : in_general_position H)
    (z : Fin m → F) (S₁ S₂ : Finset (hyperplane m F)) (h₁ : S₁ ⊆ H) (h₂ : S₂ ⊆ H)
    (hc₁ : S₁.card = m) (hc₂ : S₂.card = m)
    (hz₁ : ∀ h ∈ S₁, on_hyperplane h z) (hz₂ : ∀ h ∈ S₂, on_hyperplane h z) : S₁ = S₂ := by
  classical
  have hunion : (S₁ ∪ S₂).card ≤ m := by
    refine card_incident_le m H hgp z (S₁ ∪ S₂) (Finset.union_subset h₁ h₂) ?_
    intro h hh
    rcases Finset.mem_union.1 hh with h' | h'
    · exact hz₁ h h'
    · exact hz₂ h h'
  have e₁ : S₁ = S₁ ∪ S₂ :=
    Finset.eq_of_subset_of_card_le Finset.subset_union_left (by rw [hc₁]; exact hunion)
  have e₂ : S₂ = S₁ ∪ S₂ :=
    Finset.eq_of_subset_of_card_le Finset.subset_union_right (by rw [hc₂]; exact hunion)
  exact e₁.trans e₂.symm

@[blueprint "lem:gap-delta-poly"
  (statement := /-- Let $m, D \in \mathbb{N}$ and let $\mathcal{H}$ be a finite set of hyperplanes
  in $\mathbb{F}^m$ with $|\mathcal{H}| = m + D$ in general position (see
  \cref{def:in-general-position}), and let $T$ be characterised as the set of common incident points
  (see \cref{def:on-hyperplane}) of the $m$-element subsets of $\mathcal{H}$. Then for every
  $x \in T$ there is a polynomial $p$ of total degree at most $D$ with $p(x) \neq 0$ and $p(y) = 0$
  for every $y \in T$ with $y \neq x$. -/)
  (proof := /-- Fix $x \in T$ and an $m$-element subset $S_x \subseteq \mathcal{H}$ all of whose
  hyperplanes are incident to $x$. If some $h \in \mathcal{H}$ with $h \notin S_x$ were incident to
  $x$, then $\{h\} \cup S_x \subseteq \mathcal{H}$ would be a set of $m + 1$ hyperplanes incident to
  $x$, contradicting \cref{lem:card-incident-le}; hence every $h \in \mathcal{H}$ incident to $x$
  lies in $S_x$. For each hyperplane $h$ with normal $a$ and offset $b$ let $\ell_h = \sum_i a_i X_i
  - b$, a polynomial of total degree at most $1$ with $\ell_h(z) = 0$ if and only if $z$ is incident
  to $h$. Put $p = \prod_{h \in \mathcal{H} \setminus S_x} \ell_h$. Its total degree is at most
  $|\mathcal{H} \setminus S_x| = (m + D) - m = D$. Since no hyperplane of $\mathcal{H} \setminus
  S_x$ is incident to $x$, each factor $\ell_h(x)$ is nonzero, so $p(x) \neq 0$. For $y \in T$ with
  $y \neq x$, pick an $m$-element subset $S_y \subseteq \mathcal{H}$ incident to $y$. If $S_y = S_x$
  then $x$ and $y$ are both the unique common incident point of $S_x$ guaranteed by general
  position (see \cref{def:in-general-position}), forcing $x = y$; hence $S_y \neq S_x$, and as both
  have $m$ elements there is $h \in S_y \setminus S_x$. This $h$ lies in $\mathcal{H} \setminus S_x$
  and is incident to $y$, so $\ell_h(y) = 0$ and therefore $p(y) = 0$. -/)
  (title := /-- Vanishing delta polynomial for a GAP point -/)
  (latexEnv := "lemma")]
lemma gap_delta_poly (m D : ℕ) (H : Finset (hyperplane m F)) (hHcard : H.card = m + D)
    (hgp : in_general_position H) (T : Finset (Fin m → F))
    (hTmem : ∀ x : Fin m → F, x ∈ T ↔ ∃ S ⊆ H, S.card = m ∧ ∀ h ∈ S, on_hyperplane h x)
    (x : Fin m → F) (hx : x ∈ T) :
    ∃ p : MvPolynomial (Fin m) F, p.totalDegree ≤ D ∧ MvPolynomial.eval x p ≠ 0 ∧
      ∀ y ∈ T, y ≠ x → MvPolynomial.eval y p = 0 := by
  classical
  set L : hyperplane m F → MvPolynomial (Fin m) F :=
    fun h => (∑ i, MvPolynomial.C (h.normal i) * MvPolynomial.X i) - MvPolynomial.C h.offset
    with hL
  have hevalL : ∀ (h : hyperplane m F) (z : Fin m → F),
      MvPolynomial.eval z (L h) = (∑ i, h.normal i * z i) - h.offset := by
    intro h z
    rw [hL]
    simp only [map_sub, MvPolynomial.eval_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  have hzeroL : ∀ (h : hyperplane m F) (z : Fin m → F),
      MvPolynomial.eval z (L h) = 0 ↔ on_hyperplane h z := by
    intro h z
    rw [hevalL, on_hyperplane, sub_eq_zero]
  have hdegL : ∀ h : hyperplane m F, (L h).totalDegree ≤ 1 := by
    intro h
    rw [hL]
    show (((∑ i, MvPolynomial.C (h.normal i) * MvPolynomial.X i) - MvPolynomial.C h.offset :
      MvPolynomial (Fin m) F)).totalDegree ≤ 1
    rw [sub_eq_add_neg]
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine MvPolynomial.totalDegree_finsetSum_le ?_
      intro i _
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
    · rw [← map_neg MvPolynomial.C, MvPolynomial.totalDegree_C]; exact Nat.zero_le _
  obtain ⟨Sx, hSxH, hSxcard, hSxinc⟩ := (hTmem x).1 hx
  have hthru : ∀ h ∈ H, on_hyperplane h x → h ∈ Sx := by
    intro h hhH hhx
    by_contra hnot
    have hins : (insert h Sx) ⊆ H := Finset.insert_subset hhH hSxH
    have hcardins : (insert h Sx).card = m + 1 := by
      rw [Finset.card_insert_of_notMem hnot, hSxcard]
    have hle : (insert h Sx).card ≤ m := by
      refine card_incident_le m H hgp x (insert h Sx) hins ?_
      intro h' hh'
      rcases Finset.mem_insert.1 hh' with rfl | h''
      · exact hhx
      · exact hSxinc h' h''
    omega
  refine ⟨∏ h ∈ H \ Sx, L h, ?_, ?_, ?_⟩
  · refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    refine (Finset.sum_le_sum (fun h _ => hdegL h)).trans ?_
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_sdiff_of_subset hSxH, hHcard, hSxcard]
    omega
  · rw [MvPolynomial.eval_prod, Finset.prod_ne_zero_iff]
    intro h hh
    rw [Finset.mem_sdiff] at hh
    rw [ne_eq, hzeroL]
    intro hon
    exact hh.2 (hthru h hh.1 hon)
  · intro y hy hyx
    obtain ⟨Sy, hSyH, hSycard, hSyinc⟩ := (hTmem y).1 hy
    have hSyne : Sy ≠ Sx := by
      intro hSeq
      apply hyx
      obtain ⟨w, _, huniq⟩ := hgp.1 Sx hSxH hSxcard
      have hxw := huniq x hSxinc
      have hyw := huniq y (by rw [← hSeq]; exact hSyinc)
      rw [hxw, hyw]
    have hne : Sy \ Sx ≠ ∅ := by
      intro hempty
      rw [Finset.sdiff_eq_empty_iff_subset] at hempty
      exact hSyne (Finset.eq_of_subset_of_card_le hempty (by rw [hSxcard, hSycard]))
    obtain ⟨h, hh⟩ := Finset.nonempty_iff_ne_empty.2 hne
    rw [Finset.mem_sdiff] at hh
    rw [MvPolynomial.eval_prod]
    refine Finset.prod_eq_zero (i := h) ?_ ?_
    · rw [Finset.mem_sdiff]; exact ⟨hSyH hh.1, hh.2⟩
    · rw [hzeroL]; exact hSyinc h hh.1

@[blueprint "lem:geometric-hitting-set"
  (statement := /-- Let $m, D \in \mathbb{N}$ and let $T \subseteq \mathbb{F}^m$ be a GAP domain
  with parameters $(m, m + D)$ (see \cref{def:gap-domain}); that is, $T$ is the set of $m$-wise
  intersection points of $m + D$ hyperplanes in general position. Then $|T| = \binom{m+D}{m}$ and
  $T$ is an interpolating set for $m$-variate polynomials of degree at most $D$ (see
  \cref{def:interpolating-set}). -/)
  (proof := /-- Fix a set $\mathcal{H}$ of $m + D$ hyperplanes in general position whose $m$-wise
  common incident points form $T$ (see \cref{def:gap-domain}, \cref{def:on-hyperplane}). For the
  cardinality, map each $m$-element subset $S \subseteq \mathcal{H}$ to the unique common incident
  point guaranteed by general position (see \cref{def:in-general-position}). This map lands in $T$
  by definition of the domain, is injective by \cref{lem:incident-msubset-eq}, and is surjective
  since every point of $T$ arises from such a subset; hence $|T|$ equals the number of $m$-element
  subsets of $\mathcal{H}$, which is $\binom{m+D}{m}$. For the interpolating-set property, consider
  the $\mathbb{F}$-linear evaluation map $E$ from the space of $m$-variate polynomials of total
  degree at most $D$ to $\mathbb{F}^T$ sending $p$ to $(p(x))_{x \in T}$. Given $x \in T$,
  \cref{lem:gap-delta-poly} produces a polynomial $\delta_x$ of degree at most $D$ with
  $\delta_x(x) \neq 0$ and $\delta_x(y) = 0$ for all $y \in T$ with $y \neq x$; for any target data
  $g : T \to \mathbb{F}$ the combination $\sum_{x \in T} \frac{g(x)}{\delta_x(x)} \delta_x$ has
  degree at most $D$ and interpolates $g$, so $E$ is surjective. By \cref{lem:findrank-deg-le-choose}
  the domain has dimension $\binom{m+D}{m} = |T| = \dim \mathbb{F}^T$, so a surjective linear map
  between finite-dimensional spaces of equal dimension is injective; therefore the interpolating
  polynomial of degree at most $D$ is unique. Hence $T$ is an interpolating set for degree $D$ (see
  \cref{def:interpolating-set}). -/)
  (title := /-- Geometric hitting set (Bläser–Pandey) -/)
  (latexEnv := "lemma")]
lemma geometric_hitting_set (m D : ℕ) (T : Finset (Fin m → F))
    (hT : gap_domain m (m + D) T) :
    T.card = (m + D).choose m ∧ interpolating_set m D T := by
  classical
  obtain ⟨H, hHcard, hgp, hTmem⟩ := hT
  have hcard : T.card = (m + D).choose m := by
    have key : (H.powersetCard m).card = T.card := by
      apply Finset.card_bij
        (fun S hS => (hgp.1 S (Finset.mem_powersetCard.1 hS).1
          (Finset.mem_powersetCard.1 hS).2).choose)
      · intro S hS
        rw [Finset.mem_powersetCard] at hS
        exact (hTmem _).2 ⟨S, hS.1, hS.2, (hgp.1 S hS.1 hS.2).choose_spec.1⟩
      · intro S₁ hS₁ S₂ hS₂ heq
        rw [Finset.mem_powersetCard] at hS₁ hS₂
        refine incident_msubset_eq m H hgp _ S₁ S₂ hS₁.1 hS₂.1 hS₁.2 hS₂.2
          (hgp.1 S₁ hS₁.1 hS₁.2).choose_spec.1 ?_
        rw [heq]
        exact (hgp.1 S₂ hS₂.1 hS₂.2).choose_spec.1
      · intro x hx
        obtain ⟨S, hSH, hScard, hSinc⟩ := (hTmem x).1 hx
        refine ⟨S, Finset.mem_powersetCard.2 ⟨hSH, hScard⟩, ?_⟩
        exact ((hgp.1 S hSH hScard).choose_spec.2 x hSinc).symm
    rw [← key, Finset.card_powersetCard, hHcard]
  refine ⟨hcard, ?_⟩
  intro g
  have hex : ∀ w : ↥T → F, ∃ p : MvPolynomial (Fin m) F,
      p.totalDegree ≤ D ∧ ∀ a : ↥T, MvPolynomial.eval (a : Fin m → F) p = w a := by
    intro w
    choose δ hδdeg hδne hδzero using
      fun x : ↥T => gap_delta_poly m D H hHcard hgp T hTmem x.1 x.2
    refine ⟨∑ x : ↥T, MvPolynomial.C (w x / MvPolynomial.eval (x : Fin m → F) (δ x)) * δ x,
      ?_, ?_⟩
    · refine MvPolynomial.totalDegree_finsetSum_le ?_
      intro x _
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      exact hδdeg x
    · intro a
      rw [MvPolynomial.eval_sum, Finset.sum_eq_single a]
      · rw [map_mul, MvPolynomial.eval_C]
        exact div_mul_cancel₀ (w a) (hδne a)
      · intro x _ hxa
        rw [map_mul, MvPolynomial.eval_C]
        have hz : MvPolynomial.eval (a : Fin m → F) (δ x) = 0 :=
          hδzero x a.1 a.2 (fun h => hxa ((Subtype.ext h).symm))
        rw [hz, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ a) h
  obtain ⟨p, hpdeg, hpeval⟩ := hex g
  have hEval : ∀ (r : MvPolynomial (Fin m) F)
      (hr : r ∈ MvPolynomial.restrictTotalDegree (Fin m) F D) (a : ↥T),
      ((poly_eval_map m T).domRestrict (MvPolynomial.restrictTotalDegree (Fin m) F D)) ⟨r, hr⟩ a
        = MvPolynomial.eval (a : Fin m → F) r := by
    intro r hr a
    simp only [LinearMap.domRestrict_apply, poly_eval_map, LinearMap.pi_apply,
      AlgHom.toLinearMap_apply, MvPolynomial.aeval_eq_eval]
  have hfin : Module.finrank F (MvPolynomial.restrictTotalDegree (Fin m) F D)
      = Module.finrank F (↥T → F) := by
    rw [findrank_deg_le_choose, Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hcard]
  have hEsurj : Function.Surjective
      ((poly_eval_map m T).domRestrict (MvPolynomial.restrictTotalDegree (Fin m) F D)) := by
    intro w
    obtain ⟨q, hqdeg, hqeval⟩ := hex w
    refine ⟨⟨q, by rw [MvPolynomial.mem_restrictTotalDegree]; exact hqdeg⟩, ?_⟩
    funext a
    rw [hEval]
    exact hqeval a
  have hfree : Module.Free F ↥(MvPolynomial.restrictTotalDegree (Fin m) F D) :=
    Module.Free.of_basis (MvPolynomial.basisRestrictSupport F _)
  obtain ⟨φ⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (R := F)
    (M := ↥(MvPolynomial.restrictTotalDegree (Fin m) F D)) (M' := (↥T → F)) hfin
  have hEinj : Function.Injective
      ((poly_eval_map m T).domRestrict (MvPolynomial.restrictTotalDegree (Fin m) F D)) :=
    OrzechProperty.injective_of_surjective_of_injective φ.toLinearMap
      _ φ.injective hEsurj
  refine ⟨p, ⟨hpdeg, hpeval⟩, ?_⟩
  rintro q ⟨hq1, hq2⟩
  have hqmem : q ∈ MvPolynomial.restrictTotalDegree (Fin m) F D :=
    by rw [MvPolynomial.mem_restrictTotalDegree]; exact hq1
  have hpmem : p ∈ MvPolynomial.restrictTotalDegree (Fin m) F D :=
    by rw [MvPolynomial.mem_restrictTotalDegree]; exact hpdeg
  have heq : ((poly_eval_map m T).domRestrict
        (MvPolynomial.restrictTotalDegree (Fin m) F D)) ⟨q, hqmem⟩
      = ((poly_eval_map m T).domRestrict
        (MvPolynomial.restrictTotalDegree (Fin m) F D)) ⟨p, hpmem⟩ := by
    funext a
    rw [hEval, hEval, hq2 a, hpeval a]
  exact congrArg Subtype.val (hEinj heq)

@[blueprint "lem:interpolating-imp-hitting"
  (statement := /-- Let $m, d \in \mathbb{N}$ and let $S \subseteq \mathbb{F}^m$ be finite. If $S$
  is an interpolating set for $m$-variate polynomials of degree at most $d$ (see
  \cref{def:interpolating-set}), then $S$ is a hitting set for $m$-variate polynomials of degree at
  most $d$ (see \cref{def:hitting-set}). -/)
  (proof := /-- Let $f$ be a nonzero polynomial with total degree at most $d$. Suppose, for
  contradiction, that $f(x) = 0$ for every $x \in S$. Then both $f$ and the zero polynomial have
  degree at most $d$ and agree with the zero function on $S$, contradicting the uniqueness clause of
  the interpolating-set property (see \cref{def:interpolating-set}), since $f \neq 0$. Hence there
  is $x \in S$ with $f(x) \neq 0$, so $S$ is a hitting set (see \cref{def:hitting-set}). -/)
  (title := /-- An interpolating set is a hitting set -/)
  (latexEnv := "lemma")]
lemma interpolating_imp_hitting (m d : ℕ) (S : Finset (Fin m → F))
    (hS : interpolating_set m d S) : hitting_set m d S := by
  intro f hf hdeg
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  obtain ⟨p, _, huniq⟩ := hS 0
  have hfp : f = p :=
    huniq f ⟨hdeg, fun a => by simpa using h (a : Fin m → F) a.2⟩
  have h0p : (0 : MvPolynomial (Fin m) F) = p :=
    huniq 0 ⟨by simp, by simp⟩
  exact hf (hfp.trans h0p.symm)

@[blueprint "lem:card-finsupp-fin-sum-le"
  (statement := /-- For $m, k \in \mathbb{N}$, the number of finitely supported functions
  $d : \mathrm{Fin}\,m \to \mathbb{N}$ whose total sum $\sum_i d(i)$ is at most $k$ equals
  $\binom{k + m}{m}$. -/)
  (proof := /-- The set of such functions is the disjoint union, over $i$ ranging in
  $\{0, 1, \dots, k\}$, of the sets of functions with total sum exactly $i$; the latter is the
  finitely supported antidiagonal of the full index set $\mathrm{Fin}\,m$ at level $i$, whose
  cardinality is the multiset coefficient $\left(\!\!\binom{m}{i}\!\!\right)$. The union is disjoint
  because functions with distinct total sums are distinct. Summing over $i$ and using the identity
  $\sum_{i=0}^{k} \left(\!\!\binom{m}{i}\!\!\right) = \binom{k + m}{m}$ gives the claim. -/)
  (title := /-- Counting finitely supported functions of bounded sum -/)
  (latexEnv := "lemma")]
lemma card_finsupp_fin_sum_le (m k : ℕ) :
    Nat.card {d : Fin m →₀ ℕ | (d.sum fun _ e => e) ≤ k} = (k + m).choose m := by
  classical
  have hsum : ∀ d : Fin m →₀ ℕ,
      (Finset.univ : Finset (Fin m)).sum d = d.sum fun _ e => e := by
    intro d
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  rw [Nat.card_coe_set_eq]
  have hset : {d : Fin m →₀ ℕ | (d.sum fun _ e => e) ≤ k}
      = ↑((Finset.range (k + 1)).biUnion
          (fun i => (Finset.univ : Finset (Fin m)).finsuppAntidiag i)) := by
    ext d
    simp only [Set.mem_setOf_eq, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe,
      Finset.mem_range, Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true, hsum]
    constructor
    · intro hd
      exact ⟨d.sum fun _ e => e, Nat.lt_succ_of_le hd, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact Nat.lt_succ_iff.mp hi
  rw [hset, Set.ncard_coe_finset, Finset.card_biUnion]
  · have hcard : ∀ i ∈ Finset.range (k + 1),
        ((Finset.univ : Finset (Fin m)).finsuppAntidiag i).card = m.multichoose i := by
      intro i _
      rw [Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_congr rfl hcard, Nat.sum_range_multichoose]
  · intro i _ j _ hij
    simp only [Finset.disjoint_left, Finset.mem_finsuppAntidiag]
    rintro d ⟨hd1, _⟩ ⟨hd2, _⟩
    exact hij (by rw [← hd1, ← hd2])

@[blueprint "lem:finrank-restrict-total-degree"
  (statement := /-- For $m, k \in \mathbb{N}$, the $\mathbb{F}$-dimension of the submodule of
  $m$-variate polynomials of total degree at most $k$ equals $\binom{k + m}{m}$. -/)
  (proof := /-- The submodule of polynomials of total degree at most $k$ is, by definition, the
  submodule of polynomials supported on the set of exponent vectors $n$ with $\sum_i n(i) \le k$,
  and the monomials indexed by that set form a basis. Hence the dimension equals the cardinality of
  that index set, which by \cref{lem:card-finsupp-fin-sum-le} is $\binom{k + m}{m}$. -/)
  (title := /-- Dimension of bounded total degree polynomials, binomial form -/)
  (latexEnv := "lemma")]
lemma finrank_restrict_total_degree (m k : ℕ) :
    Module.finrank F (MvPolynomial.restrictTotalDegree (Fin m) F k) = (k + m).choose m := by
  have hb : Module.Basis _ F (MvPolynomial.restrictTotalDegree (Fin m) F k) :=
    MvPolynomial.basisRestrictSupport F {n | (n.sum fun _ e => e) ≤ k}
  rw [Module.finrank_eq_nat_card_basis hb]
  exact card_finsupp_fin_sum_le m k

@[blueprint "lem:hitting-sets-to-robust-interpolating-sets"
  (statement := /-- Let $m, d, D \in \mathbb{N}$ with $d < D$, and let $S \subseteq \mathbb{F}^m$ be
  a hitting set for $m$-variate polynomials of degree at most $D$ (see \cref{def:hitting-set}). Then
  for every nonzero $m$-variate polynomial $f$ with total degree at most $d$, the number of points
  of $S$ at which $f$ does not vanish is at least $\binom{D - d + m}{m}$. -/)
  (proof := /-- Suppose, for contradiction, that the number of points $x \in S$ with $f(x) \neq 0$
  is strictly less than $\binom{D - d + m}{m}$; write $N$ for the set of these points. Consider the
  $\mathbb{F}$-linear evaluation map $\varphi$ that sends a polynomial $p$ to the tuple
  $(p(x))_{x \in N}$, restricted to the space $V$ of polynomials of total degree at most $D - d$.
  The codomain $\mathbb{F}^N$ has dimension $|N|$, while by
  \cref{lem:finrank-restrict-total-degree} the domain $V$ has dimension $\binom{(D - d) + m}{m} =
  \binom{D - d + m}{m} > |N|$. Since the dimension of the domain exceeds that of the codomain,
  $\varphi$ is not injective, so its kernel contains a nonzero polynomial $g$; by construction $g$
  has total degree at most $D - d$ and vanishes at every point of $N$. Because
  $\mathbb{F}[X_1, \dots, X_m]$ has no zero divisors and $f, g \neq 0$, the product $f g$ is nonzero,
  and $\deg(f g) \le \deg f + \deg g \le d + (D - d) = D$. Now $f g$ vanishes at every point of $S$:
  at a point $x$ with $f(x) = 0$ this is immediate, and at a point $x$ with $f(x) \neq 0$ we have
  $x \in N$, so $g(x) = 0$. Thus $f g$ is a nonzero polynomial of total degree at most $D$ that
  vanishes on all of $S$, contradicting the hitting-set property of $S$ (see \cref{def:hitting-set}).
  Hence the number of nonvanishing points is at least $\binom{D - d + m}{m}$. -/)
  (title := /-- Hitting sets are robust interpolating sets -/)
  (latexEnv := "lemma")]
lemma hitting_sets_to_robust_interpolating_sets (m d D : ℕ) (hdD : d < D)
    (S : Finset (Fin m → F)) (hS : hitting_set m D S)
    (f : MvPolynomial (Fin m) F) (hf : f ≠ 0) (hdeg : f.totalDegree ≤ d) :
    (D - d + m).choose m ≤ (S.filter (fun x => MvPolynomial.eval x f ≠ 0)).card := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  set N := S.filter (fun x => MvPolynomial.eval x f ≠ 0) with hNdef
  set E : MvPolynomial (Fin m) F →ₗ[F] (↥N → F) :=
    LinearMap.pi (fun x : ↥N => (MvPolynomial.aeval ((x : Fin m → F))).toLinearMap) with hEdef
  set φ : ↥(MvPolynomial.restrictTotalDegree (Fin m) F (D - d)) →ₗ[F] (↥N → F) :=
    E.comp (MvPolynomial.restrictTotalDegree (Fin m) F (D - d)).subtype with hφdef
  have hval : ∀ (a : ↥(MvPolynomial.restrictTotalDegree (Fin m) F (D - d))) (x : ↥N),
      (φ a) x = MvPolynomial.eval (x : Fin m → F) (a : MvPolynomial (Fin m) F) := by
    intro a x
    simp only [hφdef, hEdef, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.pi_apply, AlgHom.toLinearMap_apply, MvPolynomial.aeval_eq_eval]
  have hfin : Module.finrank F (↥N → F) = N.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hdom : Module.finrank F ↥(MvPolynomial.restrictTotalDegree (Fin m) F (D - d))
      = (D - d + m).choose m := finrank_restrict_total_degree m (D - d)
  have hφinj : ¬ Function.Injective φ := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective (f := φ) hinj
    rw [hdom, hfin] at hle
    omega
  have hker : LinearMap.ker φ ≠ ⊥ := fun h => hφinj (LinearMap.ker_eq_bot.mp h)
  obtain ⟨g₀, hg₀mem, hg₀ne⟩ := (Submodule.ne_bot_iff _).mp hker
  set g : MvPolynomial (Fin m) F := (g₀ : MvPolynomial (Fin m) F) with hgdef
  have hgne : g ≠ 0 := (Submodule.coe_eq_zero.not).mpr hg₀ne
  have hgdeg : g.totalDegree ≤ D - d :=
    (MvPolynomial.mem_restrictTotalDegree _ _ _).mp g₀.2
  have hgeval : ∀ x ∈ N, MvPolynomial.eval x g = 0 := by
    intro x hx
    have hz : φ g₀ = 0 := LinearMap.mem_ker.mp hg₀mem
    have := hval g₀ ⟨x, hx⟩
    rw [hz] at this
    simpa using this.symm
  have hp0 : f * g ≠ 0 := mul_ne_zero hf hgne
  have hpdeg : (f * g).totalDegree ≤ D :=
    (MvPolynomial.totalDegree_mul f g).trans (by
      have := Nat.add_le_add hdeg hgdeg
      omega)
  obtain ⟨x, hxS, hxne⟩ := hS (f * g) hp0 hpdeg
  apply hxne
  rw [map_mul]
  by_cases hfx : MvPolynomial.eval x f = 0
  · rw [hfx, zero_mul]
  · have hxN : x ∈ N := Finset.mem_filter.mpr ⟨hxS, hfx⟩
    rw [hgeval x hxN, mul_zero]

@[blueprint "lem:gap-code-weight-bound"
  (statement := /-- Let $m, d, t \in \mathbb{N}$ with $m + d < t$ and let $T \subseteq \mathbb{F}^m$
  be a GAP domain with parameters $(m, t)$ (see \cref{def:gap-domain}). Then every nonzero codeword
  $c$ of $\mathrm{GAP}_{m,d,T}$ (see \cref{def:gap-code}) has Hamming weight at least
  $\binom{t - d}{m}$. -/)
  (proof := /-- Set $D = t - m$; since $m + d < t$ we have $d < D$ and $m + D = t$. By
  \cref{lem:geometric-hitting-set}, $T$ is an interpolating set for degree $D$, and by
  \cref{lem:interpolating-imp-hitting} it is a hitting set for degree $D$. Let $c$ be a nonzero
  codeword; by \cref{def:gap-code} there is a polynomial $f$ of total degree at most $d$ with
  $c = (f(x))_{x \in T}$. Since $c \neq 0$, the polynomial $f$ is not identically zero on $T$, so
  $f \neq 0$. By \cref{lem:hitting-sets-to-robust-interpolating-sets} applied with $d < D$, the
  number of points $x \in T$ with $f(x) \neq 0$ is at least $\binom{D - d + m}{m} = \binom{t-d}{m}$.
  As the Hamming weight of $c$ counts exactly those points, it is at least $\binom{t - d}{m}$. -/)
  (title := /-- Weight bound for GAP codewords -/)
  (latexEnv := "lemma")]
lemma gap_code_weight_bound (m d t : ℕ) (hmdt : m + d < t)
    (T : Finset (Fin m → F)) (hT : gap_domain m t T)
    (c : ↥T → F) (hc : c ∈ gap_code m d T) (hc0 : c ≠ 0) :
    (t - d).choose m ≤ hammingNorm c := by
  classical
  rw [gap_code, Submodule.mem_map] at hc
  obtain ⟨f, hfmem, hfc⟩ := hc
  have hdeg : f.totalDegree ≤ d := (MvPolynomial.mem_restrictTotalDegree _ _ _).mp hfmem
  have hcx : ∀ x : ↥T, c x = MvPolynomial.eval (x : Fin m → F) f := by
    intro x
    rw [← hfc]
    simp [poly_eval_map, LinearMap.pi_apply, MvPolynomial.aeval_eq_eval]
  have hf : f ≠ 0 := by
    intro h
    apply hc0
    rw [← hfc, h, map_zero]
  have hgap : gap_domain m (m + (t - m)) T := by
    have hmt : m + (t - m) = t := by omega
    rw [hmt]; exact hT
  have hgeo := geometric_hitting_set m (t - m) T hgap
  have hhit : hitting_set m (t - m) T := interpolating_imp_hitting m (t - m) T hgeo.2
  have hdD : d < t - m := by omega
  have hrob := hitting_sets_to_robust_interpolating_sets m d (t - m) hdD T hhit f hf hdeg
  have hchoose : (t - m - d + m).choose m = (t - d).choose m := by
    congr 1; omega
  rw [hchoose] at hrob
  have hham : hammingNorm c = (T.filter (fun x => MvPolynomial.eval x f ≠ 0)).card := by
    unfold hammingNorm
    apply Finset.card_bij (fun (a : ↥T) _ => (a : Fin m → F))
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact Finset.mem_filter.mpr ⟨a.2, by rw [hcx a] at ha; exact ha⟩
    · intro a₁ _ a₂ _ h
      exact Subtype.ext h
    · intro b hb
      rw [Finset.mem_filter] at hb
      refine ⟨⟨b, hb.1⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hcx ⟨b, hb.1⟩]; exact hb.2
  rw [hham]
  exact hrob

@[blueprint "thm:gap-code-distance"
  (statement := /-- Let $m, d, t \in \mathbb{N}$ with $m + d < t$ and let $T \subseteq \mathbb{F}^m$
  be a GAP domain with parameters $(m, t)$ (see \cref{def:gap-domain}). Then the minimum distance
  (see \cref{def:code-min-dist}) of $\mathrm{GAP}_{m,d,T}$ (see \cref{def:gap-code}) is at least
  $\binom{t - d}{m}$. -/)
  (proof := /-- Let $c_1$ and $c_2$ be distinct codewords of $\mathrm{GAP}_{m,d,T}$. Since the code
  is $\mathbb{F}$-linear (see \cref{def:gap-code}), the difference $c := c_1 - c_2$ is a nonzero
  codeword, and the Hamming distance between $c_1$ and $c_2$ equals the Hamming weight of $c$. By
  \cref{lem:gap-code-weight-bound}, this weight is at least $\binom{t - d}{m}$. Thus every pair of
  distinct codewords is at Hamming distance at least $\binom{t - d}{m}$. This distance set is
  nonempty: since $T$ is a GAP domain (see \cref{def:gap-domain}) with $m \le t$ hyperplanes, some
  $m$-element subset in general position has a common incident point, so $T \neq \emptyset$; hence
  the constant polynomial $1$ and the zero polynomial give two distinct codewords (see
  \cref{def:gap-code}). Therefore the minimum distance (see \cref{def:code-min-dist}), the infimum
  of the nonempty set of pairwise Hamming distances, is at least $\binom{t - d}{m}$. -/)
  (title := /-- Distance of the GAP code -/)
  (latexEnv := "theorem")]
theorem gap_code_distance (m d t : ℕ) (hmdt : m + d < t)
    (T : Finset (Fin m → F)) (hT : gap_domain m t T) :
    (t - d).choose m ≤ code_min_dist (gap_code m d T) := by
  classical
  have hTne : T.Nonempty := by
    obtain ⟨H, hHcard, hgp, hHT⟩ := hT
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (show m ≤ H.card by omega)
    obtain ⟨x, hx, _⟩ := hgp.1 S hSsub hScard
    exact ⟨x, (hHT x).2 ⟨S, hSsub, hScard, hx⟩⟩
  have hone : poly_eval_map m T 1 ∈ gap_code m d T := by
    rw [gap_code]
    exact Submodule.mem_map_of_mem ((MvPolynomial.mem_restrictTotalDegree _ _ _).mpr (by simp))
  have honeval : ∀ x : ↥T, poly_eval_map m T 1 x = 1 := by
    intro x; simp [poly_eval_map, LinearMap.pi_apply]
  apply le_csInf
  · obtain ⟨x0, hx0⟩ := hTne
    refine ⟨hammingDist (poly_eval_map m T 1) 0, poly_eval_map m T 1, hone, 0,
      (gap_code m d T).zero_mem, ?_, rfl⟩
    intro h
    have := honeval ⟨x0, hx0⟩
    rw [h] at this; simp at this
  · rintro w ⟨c₁, hc₁, c₂, hc₂, hne, rfl⟩
    have hdiff : c₂ - c₁ ∈ gap_code m d T := (gap_code m d T).sub_mem hc₂ hc₁
    have hdiff0 : c₂ - c₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hwb := gap_code_weight_bound m d t hmdt T hT (c₂ - c₁) hdiff hdiff0
    rw [hammingDist_eq_hammingNorm]
    have : -c₁ + c₂ = c₂ - c₁ := by ring
    rw [this]; exact hwb

@[blueprint "lem:card-finsupp-sum-le"
  (statement := /-- For $m, d \in \mathbb{N}$, the number of exponent tuples
  $(e_1, \dots, e_m) \in \mathbb{N}^m$ with $e_1 + \dots + e_m \le d$ equals $\binom{m + d}{m}$. -/)
  (proof := /-- Adjoin a slack coordinate $e_0 := d - (e_1 + \dots + e_m)$, which is well defined
  since $e_1 + \dots + e_m \le d$. This sends each tuple with $e_1 + \dots + e_m \le d$ to a tuple
  $(e_0, e_1, \dots, e_m) \in \mathbb{N}^{m+1}$ with $e_0 + e_1 + \dots + e_m = d$, and it is a
  bijection whose inverse drops the coordinate $e_0$. By the stars-and-bars count, the number of
  tuples in $\mathbb{N}^{m+1}$ summing to $d$ is $\binom{(m+1) + d - 1}{d} = \binom{m + d}{d}$, which
  equals $\binom{m + d}{m}$ by the symmetry of binomial coefficients. -/)
  (title := /-- Count of bounded-sum exponent tuples -/)
  (latexEnv := "lemma")]
lemma card_finsupp_sum_le (m d : ℕ) :
    Nat.card {n : Fin m →₀ ℕ // (n.sum fun _ e => e) ≤ d} = (m + d).choose m := by
  have hsum : ∀ (y : ℕ) (s : Fin m →₀ ℕ),
      (Finsupp.cons y s).sum (fun _ e => e) = y + s.sum (fun _ e => e) := by
    intro y s
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.sum_fintype _ _ (fun _ => rfl),
      Fin.sum_univ_succ]
    simp [Finsupp.cons_zero, Finsupp.cons_succ]
  have e : {n : Fin m →₀ ℕ // (n.sum fun _ e => e) ≤ d} ≃
      ↥((Finset.univ : Finset (Fin (m + 1))).finsuppAntidiag d) :=
    { toFun := fun n => ⟨Finsupp.cons (d - (n.1.sum fun _ e => e)) n.1, by
        have hn := n.2
        rw [Finset.mem_finsuppAntidiag']
        refine ⟨?_, Finset.subset_univ _⟩
        rw [hsum]
        omega⟩
      invFun := fun f => ⟨Finsupp.tail f.1, by
        have hf : (f.1.sum fun _ e => e) = d := (Finset.mem_finsuppAntidiag'.1 f.2).1
        have hcons : (Finsupp.cons (f.1 0) (Finsupp.tail f.1)).sum (fun _ e => e)
            = f.1 0 + (Finsupp.tail f.1).sum (fun _ e => e) := hsum _ _
        rw [Finsupp.cons_tail] at hcons
        omega⟩
      left_inv := fun n => by
        apply Subtype.ext
        dsimp only
        rw [Finsupp.tail_cons]
      right_inv := fun f => by
        apply Subtype.ext
        dsimp only
        have hf : (f.1.sum fun _ e => e) = d := (Finset.mem_finsuppAntidiag'.1 f.2).1
        have hcons : (Finsupp.cons (f.1 0) (Finsupp.tail f.1)).sum (fun _ e => e)
            = f.1 0 + (Finsupp.tail f.1).sum (fun _ e => e) := hsum _ _
        rw [Finsupp.cons_tail] at hcons
        have hval : d - (Finsupp.tail f.1).sum (fun _ e => e) = f.1 0 := by omega
        rw [hval, Finsupp.cons_tail] }
  rw [Nat.card_congr e, Nat.card_eq_finsetCard,
      Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin]
  have hmd : m + 1 + d - 1 = m + d := by omega
  rw [hmd]
  exact Nat.choose_symm_add.symm

@[blueprint "lem:dim-restrict-total-degree"
  (statement := /-- For $m, d \in \mathbb{N}$, the $\mathbb{F}$-dimension of the space of
  $m$-variate polynomials over $\mathbb{F}$ of total degree at most $d$ equals $\binom{m + d}{m}$.
  -/)
  (proof := /-- The submodule of $m$-variate polynomials of total degree at most $d$ carries the
  canonical basis indexed by the exponent tuples $(e_1, \dots, e_m) \in \mathbb{N}^m$ with
  $e_1 + \dots + e_m \le d$, so its dimension equals the number of such tuples. By
  \cref{lem:card-finsupp-sum-le} this number is $\binom{m + d}{m}$, hence the dimension is
  $\binom{m + d}{m}$. -/)
  (title := /-- Dimension of bounded total degree polynomials -/)
  (latexEnv := "lemma")]
lemma dim_restrict_total_degree (m d : ℕ) :
    Module.finrank F (MvPolynomial.restrictTotalDegree (Fin m) F d) = (m + d).choose m := by
  show Module.finrank F
      (MvPolynomial.restrictSupport F {n : Fin m →₀ ℕ | (n.sum fun _ e => e) ≤ d})
      = (m + d).choose m
  rw [Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport F _)]
  exact card_finsupp_sum_le m d

@[blueprint "lem:hitting-imp-eval-injective"
  (statement := /-- Let $m, d \in \mathbb{N}$ and let $T \subseteq \mathbb{F}^m$ be a hitting set
  for $m$-variate polynomials of degree at most $d$ (see \cref{def:hitting-set}). Then the
  evaluation map of \cref{def:poly-eval-map} is injective on the $\mathbb{F}$-vector space of
  $m$-variate polynomials of total degree at most $d$. -/)
  (proof := /-- The evaluation map is $\mathbb{F}$-linear (see \cref{def:poly-eval-map}), so it is
  injective on the degree-$\le d$ space if and only if its kernel meets that space only in $0$. Let
  $f$ have total degree at most $d$ and satisfy $(f(x))_{x \in T} = 0$, i.e. $f$ vanishes at every
  point of $T$. If $f$ were nonzero, the hitting-set property (see \cref{def:hitting-set}) would
  provide some $x \in T$ with $f(x) \neq 0$, a contradiction. Hence $f = 0$, and the map is
  injective on the degree-$\le d$ space. -/)
  (title := /-- Evaluation is injective over a hitting set -/)
  (latexEnv := "lemma")]
lemma hitting_imp_eval_injective (m d : ℕ) (T : Finset (Fin m → F))
    (hT : hitting_set m d T) :
    Set.InjOn (⇑(poly_eval_map m T)) (↑(MvPolynomial.restrictTotalDegree (Fin m) F d)) := by
  apply LinearMap.injOn_of_disjoint_ker (le_refl _)
  rw [Submodule.disjoint_def]
  intro f hf hfker
  rw [MvPolynomial.mem_restrictTotalDegree] at hf
  rw [LinearMap.mem_ker] at hfker
  by_contra hne
  obtain ⟨x, hxT, hx⟩ := hT f hne hf
  apply hx
  have hval := congrFun hfker ⟨x, hxT⟩
  simpa [poly_eval_map, MvPolynomial.aeval_eq_eval] using hval

@[blueprint "lem:finrank-gap-code"
  (statement := /-- Let $m, d, t \in \mathbb{N}$ with $m + d < t$ and let $T \subseteq \mathbb{F}^m$
  be a GAP domain with parameters $(m, t)$ (see \cref{def:gap-domain}). Then the $\mathbb{F}$-dimension
  of $\mathrm{GAP}_{m,d,T}$ (see \cref{def:gap-code}) equals $\binom{m + d}{m}$. -/)
  (proof := /-- Set $D = t - m$, so that $d < D$ and $m + D = t$. By \cref{lem:geometric-hitting-set},
  $T$ is an interpolating set for degree $D$, and by \cref{lem:interpolating-imp-hitting} it is a
  hitting set for degree $D$; since $d \le D$, it is also a hitting set for degree $d$. By
  \cref{lem:hitting-imp-eval-injective}, the evaluation map is injective on the space of
  $m$-variate polynomials of total degree at most $d$. By \cref{def:gap-code}, the code
  $\mathrm{GAP}_{m,d,T}$ is the image of that space under the evaluation map, so its dimension
  equals the dimension of the domain, which by \cref{lem:dim-restrict-total-degree} is
  $\binom{m + d}{m}$. -/)
  (title := /-- Dimension of the GAP code -/)
  (latexEnv := "lemma")]
lemma finrank_gap_code (m d t : ℕ) (hmdt : m + d < t)
    (T : Finset (Fin m → F)) (hT : gap_domain m t T) :
    Module.finrank F (gap_code m d T) = (m + d).choose m := by
  classical
  set D := t - m with hD
  have hmD : m + D = t := by omega
  have hdD : d ≤ D := by omega
  have hT' : gap_domain m (m + D) T := by rw [hmD]; exact hT
  have hinterp : interpolating_set m D T := (geometric_hitting_set m D T hT').2
  have hhitD : hitting_set m D T := interpolating_imp_hitting m D T hinterp
  have hhitd : hitting_set m d T := fun f hf hdeg => hhitD f hf (le_trans hdeg hdD)
  set p := MvPolynomial.restrictTotalDegree (Fin m) F d with hp
  set f := poly_eval_map m T with hf
  have hinj : Set.InjOn (⇑f) (↑p) := hitting_imp_eval_injective m d T hhitd
  have hdisj : Disjoint p (LinearMap.ker f) := LinearMap.disjoint_ker_iff_injOn.mpr hinj
  have hinjr : Function.Injective (f.domRestrict p) :=
    LinearMap.injective_domRestrict_iff.mpr hdisj
  have hfr : Module.finrank F p = Module.finrank F (p.map f) := by
    have e := LinearEquiv.ofInjective (f.domRestrict p) hinjr
    rw [LinearMap.range_domRestrict] at e
    exact e.finrank_eq
  calc Module.finrank F (gap_code m d T)
      = Module.finrank F (p.map f) := rfl
    _ = Module.finrank F p := hfr.symm
    _ = (m + d).choose m := dim_restrict_total_degree m d

@[blueprint "lem:gap-domain-card"
  (statement := /-- Let $m, t \in \mathbb{N}$ with $m \le t$ and let $T \subseteq \mathbb{F}^m$ be a
  GAP domain with parameters $(m, t)$ (see \cref{def:gap-domain}). Then $|T| = \binom{t}{m}$. -/)
  (proof := /-- Set $D = t - m$; since $m \le t$ we have $m + D = t$, so $T$ is a GAP domain with
  parameters $(m, m + D)$. By \cref{lem:geometric-hitting-set}, $|T| = \binom{m + D}{m} =
  \binom{t}{m}$. -/)
  (title := /-- Block length of the GAP code -/)
  (latexEnv := "lemma")]
lemma gap_domain_card (m t : ℕ) (hmt : m ≤ t)
    (T : Finset (Fin m → F)) (hT : gap_domain m t T) :
    T.card = t.choose m := by
  obtain ⟨h, _⟩ := geometric_hitting_set m (t - m) T (by rwa [Nat.add_sub_cancel' hmt])
  rwa [Nat.add_sub_cancel' hmt] at h

@[blueprint "lem:rate-prod-lower-bound"
  (statement := /-- Let $m, d, t \in \mathbb{N}$ and $\epsilon \in \mathbb{R}$ with $\epsilon > 0$,
  and suppose $t = m + d + \epsilon d$ as real numbers. Then
  $\binom{m + d}{m} / \binom{t}{m} \ge \left(\frac{1}{1 + \epsilon}\right)^m$. -/)
  (proof := /-- Expanding the binomial coefficients as falling products,
  $\binom{m+d}{m} / \binom{t}{m} = \prod_{i=0}^{m-1} \frac{m + d - i}{t - i}
  = \prod_{i=0}^{m-1} \frac{m + d - i}{m + d + \epsilon d - i}$, using $t = m + d + \epsilon d$. For
  each $0 \le i \le m - 1$ we have
  $(1 + \epsilon)(m + d - i) - (m + d + \epsilon d - i) = \epsilon (m - i) \ge 0$, so
  $\frac{m + d - i}{m + d + \epsilon d - i} \ge \frac{1}{1 + \epsilon}$. Multiplying these $m$
  inequalities yields $\binom{m + d}{m} / \binom{t}{m} \ge \left(\frac{1}{1 + \epsilon}\right)^m$.
  -/)
  (title := /-- Product lower bound for the rate -/)
  (latexEnv := "lemma")]
lemma rate_prod_lower_bound (m d t : ℕ) (ε : ℝ) (hε : 0 < ε)
    (ht : (t : ℝ) = (m : ℝ) + (d : ℝ) + ε * (d : ℝ)) :
    (1 / (1 + ε)) ^ m ≤ ((m + d).choose m : ℝ) / (t.choose m : ℝ) := by
  have prodrange : ∀ (n k : ℕ), n.descFactorial k = ∏ i ∈ Finset.range k, (n - i) := by
    intro n k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.descFactorial_succ, Finset.prod_range_succ, ih, Nat.mul_comm]
  have hm_le_t : m ≤ t := by
    have h : (m : ℝ) ≤ (t : ℝ) := by
      rw [ht]
      nlinarith [Nat.cast_nonneg (α := ℝ) d, mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) d)]
    exact_mod_cast h
  have hfac : ∀ i ∈ Finset.range m,
      (1 : ℝ) / (1 + ε) ≤ ((m + d - i : ℕ) : ℝ) / ((t - i : ℕ) : ℝ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hilt : (i : ℝ) < (m : ℝ) := by exact_mod_cast hi
    have ha : ((m + d - i : ℕ) : ℝ) = (m : ℝ) + (d : ℝ) - (i : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hb : ((t - i : ℕ) : ℝ) = (t : ℝ) - (i : ℝ) := by
      rw [Nat.cast_sub (by omega)]
    rw [ha, hb, ht]
    have hbpos : (0 : ℝ) < (m : ℝ) + (d : ℝ) + ε * (d : ℝ) - (i : ℝ) := by
      nlinarith [mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) d), Nat.cast_nonneg (α := ℝ) d]
    rw [div_le_div_iff₀ (by linarith) hbpos]
    nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hilt.le)]
  have key : ((m + d).choose m : ℝ) / (t.choose m : ℝ)
      = ∏ i ∈ Finset.range m, (((m + d - i : ℕ) : ℝ) / ((t - i : ℕ) : ℝ)) := by
    rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod,
        ← prodrange, ← prodrange,
        Nat.descFactorial_eq_factorial_mul_choose,
        Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    rw [mul_div_mul_left _ _ (by exact_mod_cast Nat.factorial_ne_zero m)]
  rw [key]
  have hlhs : (1 / (1 + ε)) ^ m = ∏ _i ∈ Finset.range m, (1 : ℝ) / (1 + ε) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [hlhs]
  apply Finset.prod_le_prod
  · intro i _; exact div_nonneg zero_le_one (by linarith)
  · exact hfac

@[blueprint "lem:choose-ratio-eq-desc-prod"
  (statement := /-- Let $a, b, m \in \mathbb{N}$. Then, as an identity of real numbers,
  $\binom{a}{m} / \binom{b}{m} = \prod_{i=0}^{m-1} \frac{a - i}{b - i}$, where each of the
  differences $a - i$ and $b - i$ is the truncated subtraction of natural numbers and the
  division is division of real numbers, with the convention $x / 0 = 0$. -/)
  (proof := /-- First we show that for all $n, k \in \mathbb{N}$ the falling factorial satisfies
  $n^{\underline{k}} = \prod_{i=0}^{k-1} (n - i)$, with truncated subtraction. We argue by
  induction on $k$. For $k = 0$ both sides equal $1$. For the step from $k$ to $k + 1$ we have
  $n^{\underline{k+1}} = (n - k) \cdot n^{\underline{k}}$ by the recursion defining the falling
  factorial, while $\prod_{i=0}^{k} (n - i) = \left(\prod_{i=0}^{k-1} (n - i)\right) \cdot (n - k)$
  by splitting off the last factor; the induction hypothesis and commutativity of multiplication
  identify the two.
  Now fix $a, b, m$. Splitting the product of quotients into a quotient of products and moving the
  casts $\mathbb{N} \to \mathbb{R}$ outside the products gives
  $\prod_{i=0}^{m-1} \frac{a - i}{b - i} = \frac{\prod_{i=0}^{m-1} (a - i)}{\prod_{i=0}^{m-1}
  (b - i)} = \frac{a^{\underline{m}}}{b^{\underline{m}}}$, the last step by the product formula
  just proved. Since $n^{\underline{m}} = m! \cdot \binom{n}{m}$ for every $n \in \mathbb{N}$, this
  equals $\frac{m! \cdot \binom{a}{m}}{m! \cdot \binom{b}{m}}$, and cancelling the nonzero real
  factor $m!$ from numerator and denominator yields $\binom{a}{m} / \binom{b}{m}$. -/)
  (title := /-- Binomial ratio as a product of falling-factorial factors -/)
  (latexEnv := "lemma")]
lemma choose_ratio_eq_desc_prod (a b m : ℕ) :
    (a.choose m : ℝ) / (b.choose m : ℝ)
      = ∏ i ∈ Finset.range m, (((a - i : ℕ) : ℝ) / ((b - i : ℕ) : ℝ)) := by
  have prodrange : ∀ (n k : ℕ), n.descFactorial k = ∏ i ∈ Finset.range k, (n - i) := by
    intro n k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.descFactorial_succ, Finset.prod_range_succ, ih, Nat.mul_comm]
  rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod,
      ← prodrange, ← prodrange,
      Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  rw [mul_div_mul_left _ _ (by exact_mod_cast Nat.factorial_ne_zero m)]

@[blueprint "lem:rel-dist-factor-lower-bound"
  (statement := /-- Let $m, d, i \in \mathbb{N}$ with $i < m$ and $0 < d$, and let $\epsilon \in
  \mathbb{R}$ with $\epsilon > 0$. Then
  $\frac{\epsilon}{1 + \epsilon} \le \frac{m + \epsilon d - 1 - i}{m + d + \epsilon d - 1 - i}$,
  the inequality being one of real numbers. -/)
  (proof := /-- Since $i < m$ as natural numbers we have $i + 1 \le m$, hence $i + 1 \le m$ as real
  numbers, and since $0 < d$ we have $1 \le d$ as real numbers. Together with $\epsilon > 0$ and
  $d \ge 1 > 0$ this gives $\epsilon d > 0$, so
  $m + d + \epsilon d - 1 - i = (m - 1 - i) + d + \epsilon d \ge 0 + 1 + \epsilon d > 0$;
  in particular the denominator is positive, and $1 + \epsilon > 0$ as well. The claimed inequality
  is therefore equivalent, after multiplying by the two positive denominators, to
  $\epsilon (m + d + \epsilon d - 1 - i) \le (m + \epsilon d - 1 - i)(1 + \epsilon)$. Expanding both
  sides, their difference is
  $(m + \epsilon d - 1 - i)(1 + \epsilon) - \epsilon (m + d + \epsilon d - 1 - i) = m - 1 - i$,
  which is nonnegative because $i + 1 \le m$. This proves the inequality. -/)
  (title := /-- Lower bound for a single relative-distance factor -/)
  (latexEnv := "lemma")]
lemma rel_dist_factor_lower_bound (m d i : ℕ) (hi : i < m) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ε / (1 + ε)
      ≤ ((m : ℝ) + ε * (d : ℝ) - 1 - (i : ℝ)) / ((m : ℝ) + (d : ℝ) + ε * (d : ℝ) - 1 - (i : ℝ)) := by
  have hiR : (i : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hi
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hεd : (0 : ℝ) < ε * (d : ℝ) := by nlinarith
  have hden : (0 : ℝ) < (m : ℝ) + (d : ℝ) + ε * (d : ℝ) - 1 - (i : ℝ) := by linarith
  rw [div_le_div_iff₀ (by linarith) hden]
  nlinarith

@[blueprint "lem:rel-dist-prod-lower-bound"
  (statement := /-- Let $m, d, t \in \mathbb{N}$ with $0 < d$, and let $\epsilon \in \mathbb{R}$ with
  $\epsilon > 0$, and suppose $t = m + d + \epsilon d - 1$ as real numbers. Then
  $\binom{t - d}{m} / \binom{t}{m} \ge \left(\frac{\epsilon}{1 + \epsilon}\right)^m$. -/)
  (proof := /-- Since $0 < d$ we have $1 \le d$ as real numbers, and with $\epsilon > 0$ this gives
  $\epsilon d > 0$. Hence the parameterization yields $m + d < t + 1$ as real numbers, so
  $m + d < t + 1$ as natural numbers and therefore $m + d \le t$; in particular $d \le t$ and
  $i < t - d$ for every $i < m$, so all the truncated subtractions of natural numbers occurring
  below agree with the corresponding real differences.
  By \cref{lem:choose-ratio-eq-desc-prod} applied to the natural numbers $t - d$, $t$ and $m$,
  $\binom{t - d}{m} / \binom{t}{m} = \prod_{i=0}^{m-1} \frac{t - d - i}{t - i}$. The left-hand side
  is a constant product, $\left(\frac{\epsilon}{1 + \epsilon}\right)^m =
  \prod_{i=0}^{m-1} \frac{\epsilon}{1 + \epsilon}$, so it suffices to compare the two products
  factorwise: since each factor $\frac{\epsilon}{1 + \epsilon}$ is nonnegative, being a quotient of
  the nonnegative number $\epsilon$ by the positive number $1 + \epsilon$, it is enough to show
  $\frac{\epsilon}{1 + \epsilon} \le \frac{t - d - i}{t - i}$ for every $i < m$.
  Fix such an $i$. Using $d \le t$, $i < t - d$ and $t = m + d + \epsilon d - 1$, the casts of the
  truncated differences evaluate to $t - d - i = m + \epsilon d - 1 - i$ and
  $t - i = m + d + \epsilon d - 1 - i$ as real numbers. The required factor inequality is then
  exactly \cref{lem:rel-dist-factor-lower-bound} for the parameters $m$, $d$, $i$ and $\epsilon$.
  Multiplying the $m$ factors yields
  $\binom{t - d}{m} / \binom{t}{m} \ge \left(\frac{\epsilon}{1 + \epsilon}\right)^m$. -/)
  (title := /-- Product lower bound for the relative distance -/)
  (latexEnv := "lemma")]
lemma rel_dist_prod_lower_bound (m d t : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε)
    (ht : (t : ℝ) = (m : ℝ) + (d : ℝ) + ε * (d : ℝ) - 1) :
    (ε / (1 + ε)) ^ m ≤ ((t - d).choose m : ℝ) / (t.choose m : ℝ) := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hεd : (0 : ℝ) < ε * (d : ℝ) := by nlinarith
  have hmd_le_t : m + d ≤ t := by
    have h : (m : ℝ) + (d : ℝ) < (t : ℝ) + 1 := by rw [ht]; linarith
    have h2 : m + d < t + 1 := by exact_mod_cast h
    omega
  rw [choose_ratio_eq_desc_prod (t - d) t m]
  have hlhs : (ε / (1 + ε)) ^ m = ∏ _i ∈ Finset.range m, ε / (1 + ε) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [hlhs]
  apply Finset.prod_le_prod
  · intro i _
    exact div_nonneg hε.le (by linarith)
  · intro i hi
    rw [Finset.mem_range] at hi
    have ha : ((t - d - i : ℕ) : ℝ) = (m : ℝ) + ε * (d : ℝ) - 1 - (i : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), ht]
      ring
    have hb : ((t - i : ℕ) : ℝ) = (m : ℝ) + (d : ℝ) + ε * (d : ℝ) - 1 - (i : ℝ) := by
      rw [Nat.cast_sub (by omega), ht]
    rw [ha, hb]
    exact rel_dist_factor_lower_bound m d i hi hd ε hε

@[blueprint "thm:gap-code-rate"
  (statement := /-- Let $m, d, t \in \mathbb{N}$ with $0 < d$ and $m + d < t$, let $\epsilon \in
  \mathbb{R}$ with $\epsilon > 0$ satisfy $t = m + d + \epsilon d - 1$, and let $T \subseteq
  \mathbb{F}^m$ be a GAP domain with parameters $(m, t)$ (see \cref{def:gap-domain}). Then the rate
  (see \cref{def:code-rate}) of $\mathrm{GAP}_{m,d,T}$ (see \cref{def:gap-code}) is at least
  $\left(\frac{1}{1 + \epsilon}\right)^m$. -/)
  (proof := /-- By \cref{lem:finrank-gap-code}, the $\mathbb{F}$-dimension of $\mathrm{GAP}_{m,d,T}$
  is $\binom{m + d}{m}$, and by \cref{lem:gap-domain-card} the block length is $|T| = \binom{t}{m}$;
  hence, by \cref{def:code-rate}, the rate equals $\binom{m + d}{m} / \binom{t}{m}$. Under the
  parameterization $t = m + d + \epsilon d$, \cref{lem:rate-prod-lower-bound} gives
  $\binom{m + d}{m} / \binom{t}{m} \ge \left(\frac{1}{1 + \epsilon}\right)^m$. Therefore the rate is
  at least $\left(\frac{1}{1 + \epsilon}\right)^m$. -/)
  (title := /-- Rate of the GAP code -/)
  (latexEnv := "theorem")]
theorem gap_code_rate (m d t : ℕ) (hd : 0 < d) (hmdt : m + d < t)
    (ε : ℝ) (hε : 0 < ε) (ht : (t : ℝ) = (m : ℝ) + (d : ℝ) + ε * (d : ℝ) - 1)
    (T : Finset (Fin m → F)) (hT : gap_domain m t T) :
    (1 / (1 + ε)) ^ m ≤ code_rate (gap_code m d T) := by
  classical
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hR : (m:ℝ) + (d:ℝ) < (t:ℝ) := by exact_mod_cast hmdt
  have hεd : (1:ℝ) < ε * (d:ℝ) := by linarith [ht, hR]
  set ε' : ℝ := ε - 1 / (d:ℝ) with hεdef
  have hε'pos : 0 < ε' := by
    have : (1:ℝ) / (d:ℝ) < ε := by rw [div_lt_iff₀ hdR]; linarith
    simp only [hεdef]; linarith
  have ht' : (t:ℝ) = (m:ℝ) + (d:ℝ) + ε' * (d:ℝ) := by
    have hd0 : (d:ℝ) ≠ 0 := ne_of_gt hdR
    rw [hεdef, sub_mul, one_div, inv_mul_cancel₀ hd0]; linarith [ht]
  have hrate : code_rate (gap_code m d T) = ((m + d).choose m : ℝ) / (t.choose m : ℝ) := by
    unfold code_rate
    rw [finrank_gap_code m d t hmdt T hT, Fintype.card_coe,
      gap_domain_card m t (by omega) T hT]
  rw [hrate]
  have hle : (1:ℝ) / (1 + ε) ≤ 1 / (1 + ε') :=
    one_div_le_one_div_of_le (by linarith) (by simp only [hεdef]; linarith [le_of_lt (by positivity : (0:ℝ) < 1/(d:ℝ))])
  calc (1 / (1 + ε)) ^ m ≤ (1 / (1 + ε')) ^ m :=
        pow_le_pow_left₀ (by positivity) hle m
    _ ≤ ((m + d).choose m : ℝ) / (t.choose m : ℝ) :=
        rate_prod_lower_bound m d t ε' hε'pos ht'

@[blueprint "thm:gap-code-rel-dist"
  (statement := /-- Let $m, d, t \in \mathbb{N}$ with $0 < d$ and $m + d < t$, let $\epsilon \in
  \mathbb{R}$ with $\epsilon > 0$ satisfy $t = m + d + \epsilon d - 1$, and let $T \subseteq
  \mathbb{F}^m$ be a GAP domain with parameters $(m, t)$ (see \cref{def:gap-domain}). Then the
  relative distance (see \cref{def:code-rel-dist}) of $\mathrm{GAP}_{m,d,T}$ (see \cref{def:gap-code})
  is at least $\left(\frac{\epsilon}{1 + \epsilon}\right)^m$. -/)
  (proof := /-- By \cref{thm:gap-code-distance}, the minimum distance of $\mathrm{GAP}_{m,d,T}$ is at
  least $\binom{t - d}{m}$, and by \cref{lem:gap-domain-card} the block length is $|T| =
  \binom{t}{m}$; hence, by \cref{def:code-rel-dist}, the relative distance is at least
  $\binom{t - d}{m} / \binom{t}{m}$. Under the parameterization $t = m + d + \epsilon d - 1$,
  \cref{lem:rel-dist-prod-lower-bound} gives
  $\binom{t - d}{m} / \binom{t}{m} \ge \left(\frac{\epsilon}{1 + \epsilon}\right)^m$. Therefore the
  relative distance is at least $\left(\frac{\epsilon}{1 + \epsilon}\right)^m$. -/)
  (title := /-- Relative distance of the GAP code -/)
  (latexEnv := "theorem")]
theorem gap_code_rel_dist (m d t : ℕ) (hd : 0 < d) (hmdt : m + d < t)
    (ε : ℝ) (hε : 0 < ε) (ht : (t : ℝ) = (m : ℝ) + (d : ℝ) + ε * (d : ℝ) - 1)
    (T : Finset (Fin m → F)) (hT : gap_domain m t T) :
    (ε / (1 + ε)) ^ m ≤ code_rel_dist (gap_code m d T) := by
  have hmt : m ≤ t := by omega
  have hrd : code_rel_dist (gap_code m d T)
      = (code_min_dist (gap_code m d T) : ℝ) / (t.choose m : ℝ) := by
    unfold code_rel_dist
    rw [Fintype.card_coe, gap_domain_card m t hmt T hT]
  rw [hrd]
  calc (ε / (1 + ε)) ^ m ≤ ((t - d).choose m : ℝ) / (t.choose m : ℝ) :=
        rel_dist_prod_lower_bound m d t hd ε hε ht
    _ ≤ (code_min_dist (gap_code m d T) : ℝ) / (t.choose m : ℝ) := by
        gcongr
        exact_mod_cast gap_code_distance m d t hmdt T hT

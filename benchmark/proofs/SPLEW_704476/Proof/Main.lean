import Architect
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:edge-weight"
  (statement := /-- Let $d \in \mathbb{N}$. For coefficients
    $a=(a_1,\ldots,a_{d+1})\in\mathbb{R}^{d+1}$ and a parameter vector
    $x=(x_1,\ldots,x_d)\in\mathbb{R}^d$, define the associated affine edge
    weight by
    \[
      \operatorname{wt}_a(x)=\sum_{i=1}^{d}a_i x_i+a_{d+1}.
    \] -/)
  (title := /-- Affine edge weight -/)
  (latexEnv := "definition")]
noncomputable def edge_weight {d : ℕ} (a : Fin (d + 1) → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  (∑ i : Fin d, a i.castSucc * x i) + a (Fin.last d)

@[blueprint "def:parametric-dag"
  (statement := /-- Let $d\in\mathbb{N}$. A parametric directed acyclic graph
    consists of a finite vertex set $V=\{0,\ldots,n-1\}$, distinguished
    vertices $s,t\in V$, and, for each ordered pair $(u,v)$, either no edge or
    one coefficient vector in $\mathbb{R}^{d+1}$. The coefficient vector gives
    the edge's affine weight through \cref{def:edge-weight}. The directed edge
    relation is required to have no nonempty directed closed walk. -/)
  (title := /-- Affine-weighted directed acyclic graph -/)
  (latexEnv := "definition")]
structure parametric_dag (d : ℕ) where
  n : ℕ
  weight : Fin n → Fin n → Option (Fin (d + 1) → ℝ)
  acyclic : ∀ v : Fin n,
    ¬Relation.TransGen (fun u w => (weight u w).isSome = true) v v
  s : Fin n
  t : Fin n

@[blueprint "def:st-path"
  (statement := /-- Let $G$ be a parametric directed acyclic graph. An
    $s$--$t$ path is a finite list of vertices whose first entry is $s$, whose
    last entry is $t$, and for which every consecutive ordered pair is an edge
    of $G$; see \cref{def:parametric-dag}. -/)
  (title := /-- Source-to-sink path -/)
  (latexEnv := "definition")]
def st_path {d : ℕ} (G : parametric_dag d)
    (p : List (Fin G.n)) : Prop :=
  p.head? = some G.s ∧ p.getLast? = some G.t ∧
    p.IsChain (fun u v => (G.weight u v).isSome = true)

@[blueprint "def:path-weight"
  (statement := /-- Let $G$ be a parametric directed acyclic graph, let $p$ be
    a list of vertices, and let $x\in\mathbb{R}^d$. The weight of $p$ at $x$ is
    the sum, over consecutive pairs in $p$, of their affine edge weights from
    \cref{def:edge-weight, def:parametric-dag}. A missing edge contributes zero;
    this convention is immaterial for lists satisfying \cref{def:st-path}. -/)
  (title := /-- Weight of a path at a parameter vector -/)
  (latexEnv := "definition")]
noncomputable def path_weight {d : ℕ} (G : parametric_dag d)
    (p : List (Fin G.n)) (x : Fin d → ℝ) : ℝ :=
  ((p.zip p.tail).map fun uv =>
      (G.weight uv.1 uv.2).elim 0 (fun a => edge_weight a x)).foldr (· + ·) 0

@[blueprint "def:shortest-path-at"
  (statement := /-- Let $G$ be a parametric directed acyclic graph and
    $x\in\mathbb{R}^d$. A list $p$ is a shortest $s$--$t$ path at $x$ if it is
    an $s$--$t$ path and its weight is at most the weight of every $s$--$t$
    path, using \cref{def:st-path, def:path-weight}. -/)
  (title := /-- Shortest path at a parameter vector -/)
  (latexEnv := "definition")]
def shortest_path_at {d : ℕ} (G : parametric_dag d)
    (p : List (Fin G.n)) (x : Fin d → ℝ) : Prop :=
  st_path G p ∧ ∀ q : List (Fin G.n),
    st_path G q → path_weight G p x ≤ path_weight G q x

@[blueprint "def:shortest-path-cover"
  (statement := /-- A set $\mathcal{S}$ of vertex lists is a shortest path
    cover of a parametric directed acyclic graph $G$ if every member of
    $\mathcal{S}$ is an $s$--$t$ path and, for every
    $x\in\mathbb{R}^d$, some member of $\mathcal{S}$ is a shortest path at
    $x$; see \cref{def:st-path, def:shortest-path-at}. -/)
  (title := /-- Parametric shortest path cover -/)
  (latexEnv := "definition")]
def shortest_path_cover {d : ℕ} (G : parametric_dag d)
    (S : Set (List (Fin G.n))) : Prop :=
  (∀ p ∈ S, st_path G p) ∧
    ∀ x : Fin d → ℝ, ∃ p ∈ S, shortest_path_at G p x

@[blueprint "def:mspc-size"
  (statement := /-- For a parametric directed acyclic graph $G$, define
    $|\operatorname{PSP}(G)|$ to be the least natural number occurring as the
    cardinality of a shortest path cover from
    \cref{def:shortest-path-cover}. If no such cardinality occurs, the infimum
    convention for natural numbers assigns the value zero. -/)
  (title := /-- Cardinality of a minimum shortest path cover -/)
  (latexEnv := "definition")]
noncomputable def mspc_size {d : ℕ} (G : parametric_dag d) : ℕ :=
  sInf {k : ℕ | ∃ S : Set (List (Fin G.n)),
    shortest_path_cover G S ∧ S.ncard = k}

@[blueprint "def:affine-sign-patterns"
  (statement := /-- For a finite family of affine functions on
    $\mathbb{R}^d$, the affine sign patterns are the three-valued sign vectors
    which occur at some point of $\mathbb{R}^d$. -/)
  (title := /-- Realized affine sign patterns -/)
  (latexEnv := "definition")]
noncomputable def affine_sign_patterns {d m : ℕ}
    (a : Fin m → Fin (d + 1) → ℝ) : Finset (Fin m → Ordering) :=
  (Set.range fun x : Fin d → ℝ =>
    fun j : Fin m => compare (edge_weight (a j) x) 0).toFinite.toFinset

@[blueprint "lem:affine-sign-zero-between"
  (statement := /-- Let $a_1,\ldots,a_m$ and $f$ be affine functions on
    $\mathbb{R}^d$. If two points have the same three-valued sign for every
    $a_j$, while $f$ is negative at the first point and positive at the
    second, then the segment joining them contains a zero of $f$ having the
    same sign vector for the functions $a_j$. -/)
  (proof := /-- Put
    $q=-f(x)/(f(y)-f(x))$ and $z=(1-q)x+qy$. The strict inequalities on
    $f(x)$ and $f(y)$ give $0<q<1$, and affine evaluation from
    \cref{def:edge-weight} gives $f(z)=0$. For each $j$, the common sign of
    $a_j(x)$ and $a_j(y)$ is preserved by this strict convex combination:
    two negative values give a negative value, two zero values give zero,
    and two positive values give a positive value. -/)
  (title := /-- A zero inside an affine sign cell -/)
  (latexEnv := "lemma")]
lemma affine_sign_zero_between {d m : ℕ}
    (a : Fin m → Fin (d + 1) → ℝ) (f : Fin (d + 1) → ℝ)
    (x y : Fin d → ℝ)
    (hsign : ∀ j, compare (edge_weight (a j) x) 0 =
      compare (edge_weight (a j) y) 0)
    (hfx : edge_weight f x < 0) (hfy : 0 < edge_weight f y) :
    ∃ z : Fin d → ℝ, edge_weight f z = 0 ∧
      ∀ j, compare (edge_weight (a j) z) 0 =
        compare (edge_weight (a j) x) 0 := by
  classical
  let q := -edge_weight f x / (edge_weight f y - edge_weight f x)
  let z : Fin d → ℝ := fun i => (1 - q) * x i + q * y i
  have hden : 0 < edge_weight f y - edge_weight f x :=
    sub_pos.mpr (lt_trans hfx hfy)
  have hq0 : 0 < q := div_pos (neg_pos.mpr hfx) hden
  have hq1 : q < 1 := by
    dsimp [q]
    rw [div_lt_one hden]
    simpa using hfy
  have haff (g : Fin (d + 1) → ℝ) :
      edge_weight g z = (1 - q) * edge_weight g x + q * edge_weight g y := by
    have hsum (s : Finset (Fin d)) :
        (∑ i ∈ s, g i.castSucc * z i) =
          (1 - q) * (∑ i ∈ s, g i.castSucc * x i) +
            q * (∑ i ∈ s, g i.castSucc * y i) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
          simp only [Finset.sum_insert, hi, not_false_eq_true]
          rw [ih]
          simp [z, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm,
            add_assoc, add_comm, add_left_comm]
    unfold edge_weight
    rw [hsum Finset.univ]
    have hc : (1 - q) * g (Fin.last d) + q * g (Fin.last d) =
        g (Fin.last d) := by
      rw [← add_mul]
      simp
    calc
      ((1 - q) * (∑ i, g i.castSucc * x i) +
          q * (∑ i, g i.castSucc * y i)) + g (Fin.last d) =
          ((1 - q) * (∑ i, g i.castSucc * x i) +
            q * (∑ i, g i.castSucc * y i)) +
              ((1 - q) * g (Fin.last d) + q * g (Fin.last d)) :=
        congrArg (fun t => ((1 - q) * (∑ i, g i.castSucc * x i) +
          q * (∑ i, g i.castSucc * y i)) + t) hc.symm
      _ = (1 - q) * ((∑ i, g i.castSucc * x i) + g (Fin.last d)) +
          q * ((∑ i, g i.castSucc * y i) + g (Fin.last d)) := by
        simp [mul_add, add_assoc, add_comm, add_left_comm]
  refine ⟨z, ?_, ?_⟩
  · rw [haff]
    dsimp [q]
    rw [one_sub_div (ne_of_gt hden)]
    have heq : edge_weight f y - edge_weight f x - -edge_weight f x =
        edge_weight f y := by simp
    rw [heq]
    simp only [neg_div, neg_mul]
    rw [add_eq_zero_iff_eq_neg, neg_neg]
    calc
      edge_weight f y / (edge_weight f y - edge_weight f x) * edge_weight f x =
          (edge_weight f y * edge_weight f x) /
            (edge_weight f y - edge_weight f x) := div_mul_eq_mul_div _ _ _
      _ = (edge_weight f x * edge_weight f y) /
            (edge_weight f y - edge_weight f x) := by rw [mul_comm]
      _ = edge_weight f x / (edge_weight f y - edge_weight f x) *
            edge_weight f y := (div_mul_eq_mul_div _ _ _).symm
  · intro j
    rw [haff]
    have hj := hsign j
    rcases lt_trichotomy (edge_weight (a j) x) 0 with hjx | hjx | hjx
    · have hjy : edge_weight (a j) y < 0 := by
        rw [compare_lt_iff_lt.mpr hjx] at hj
        exact compare_lt_iff_lt.mp hj.symm
      rw [compare_lt_iff_lt.mpr hjx]
      exact compare_lt_iff_lt.mpr <|
        add_neg (mul_neg_of_pos_of_neg (sub_pos.mpr hq1) hjx)
          (mul_neg_of_pos_of_neg hq0 hjy)
    · have hjy : edge_weight (a j) y = 0 := by
        rw [compare_eq_iff_eq.mpr hjx] at hj
        exact compare_eq_iff_eq.mp hj.symm
      rw [compare_eq_iff_eq.mpr hjx]
      exact compare_eq_iff_eq.mpr (by simp [hjx, hjy])
    · have hjy : 0 < edge_weight (a j) y := by
        rw [compare_gt_iff_gt.mpr hjx] at hj
        exact compare_gt_iff_gt.mp hj.symm
      rw [compare_gt_iff_gt.mpr hjx]
      exact compare_gt_iff_gt.mpr <|
        add_pos (mul_pos (sub_pos.mpr hq1) hjx) (mul_pos hq0 hjy)

@[blueprint "lem:affine-zero-hyperplane-parametrization"
  (statement := /-- Let $f$ and $a_1,\ldots,a_m$ be affine functions on
    $\mathbb{R}^{d+1}$. If one linear coefficient of $f$ is nonzero, then
    there are affine functions $b_1,\ldots,b_m$ on $\mathbb{R}^d$ and a map
    $\phi:\mathbb{R}^d\to\mathbb{R}^{d+1}$ whose image is exactly the zero
    set of $f$, such that $b_j(z)=a_j(\phi(z))$ for every $j$ and $z$. -/)
  (proof := /-- Choose a coordinate whose coefficient in $f$ is nonzero.
    Assign the other $d$ coordinates freely and solve the affine equation
    $f=0$ for the chosen coordinate. Substitution into each $a_j$ gives an
    affine function of the free coordinates. The same equation shows that
    every zero of $f$ is obtained by this parametrization. Expanding the
    finite sums in the definition of affine evaluation from
    \cref{def:edge-weight} verifies all identities. -/)
  (title := /-- Parametrizing a nonconstant affine zero hyperplane -/)
  (latexEnv := "lemma")]
lemma affine_zero_hyperplane_parametrization {d m : ℕ}
    (a : Fin m → Fin (d + 1 + 1) → ℝ) (f : Fin (d + 1 + 1) → ℝ)
    (k : Fin (d + 1)) (hk : f k.castSucc ≠ 0) :
    ∃ b : Fin m → Fin (d + 1) → ℝ,
      ∃ φ : (Fin d → ℝ) → (Fin (d + 1) → ℝ),
        (∀ z, edge_weight f (φ z) = 0) ∧
        (∀ x, edge_weight f x = 0 → ∃ z, φ z = x) ∧
        (∀ j z, edge_weight (b j) z = edge_weight (a j) (φ z)) := by
  classical
  let root : (Fin d → ℝ) → ℝ := fun z =>
    -((∑ q : Fin d, f (k.succAbove q).castSucc * z q) +
      f (Fin.last (d + 1))) / f k.castSucc
  let φ : (Fin d → ℝ) → (Fin (d + 1) → ℝ) := fun z i =>
    if hi : i = k then root z
    else z (Classical.choose (Fin.exists_succAbove_eq hi))
  let b : Fin m → Fin (d + 1) → ℝ := fun j i =>
    Fin.lastCases
      (a j (Fin.last (d + 1)) -
        a j k.castSucc * f (Fin.last (d + 1)) / f k.castSucc)
      (fun q => a j (k.succAbove q).castSucc -
        a j k.castSucc * f (k.succAbove q).castSucc / f k.castSucc) i
  have φ_k (z : Fin d → ℝ) : φ z k = root z := by simp [φ]
  have φ_succAbove (z : Fin d → ℝ) (q : Fin d) :
      φ z (k.succAbove q) = z q := by
    simp only [φ, dif_neg (Fin.succAbove_ne k q)]
    congr 1
    apply Fin.succAbove_right_inj.mp
    exact Classical.choose_spec
      (Fin.exists_succAbove_eq (Fin.succAbove_ne k q))
  have sum_succAbove (g : Fin (d + 1) → ℝ) :
      (∑ i, g i) = g k + ∑ q, g (k.succAbove q) := by
    have hrest : (∑ q : Fin d, g (k.succAbove q)) =
        ∑ i ∈ (Finset.univ : Finset (Fin (d + 1))).erase k, g i := by
      apply Finset.sum_bij (fun q _ => k.succAbove q)
      · intro q hq
        simp
      · intro q₁ hq₁ q₂ hq₂ heq
        exact Fin.succAbove_right_inj.mp heq
      · intro i hi
        have hik : i ≠ k := (Finset.mem_erase.mp hi).1
        obtain ⟨q, hq⟩ := Fin.exists_succAbove_eq hik
        exact ⟨q, Finset.mem_univ q, hq⟩
      · simp
    calc
      (∑ i, g i) =
          (∑ i ∈ (Finset.univ : Finset (Fin (d + 1))).erase k, g i) + g k :=
        (Finset.sum_erase_add Finset.univ g (Finset.mem_univ k)).symm
      _ = g k + ∑ i ∈ (Finset.univ : Finset (Fin (d + 1))).erase k, g i :=
        add_comm _ _
      _ = g k + ∑ q, g (k.succAbove q) := congrArg (fun t => g k + t) hrest.symm
  refine ⟨b, φ, ?_, ?_, ?_⟩
  · intro z
    unfold edge_weight
    rw [sum_succAbove]
    rw [φ_k]
    have hsumφ :
        (∑ q, f (k.succAbove q).castSucc * φ z (k.succAbove q)) =
          ∑ q, f (k.succAbove q).castSucc * z q := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [φ_succAbove]
    rw [hsumφ]
    dsimp [root]
    rw [neg_div, mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ hk]
    simp
  · intro x hx
    let z : Fin d → ℝ := fun q => x (k.succAbove q)
    refine ⟨z, funext fun i => ?_⟩
    by_cases hi : i = k
    · subst i
      rw [φ_k]
      dsimp [root, z]
      unfold edge_weight at hx
      rw [sum_succAbove] at hx
      have hmul : f k.castSucc * x k =
          -((∑ q, f (k.succAbove q).castSucc * x (k.succAbove q)) +
            f (Fin.last (d + 1))) := by
        rw [add_assoc] at hx
        exact add_eq_zero_iff_eq_neg.mp hx
      apply (div_eq_iff hk).2
      calc
        -((∑ q, f (k.succAbove q).castSucc * x (k.succAbove q)) +
            f (Fin.last (d + 1))) = f k.castSucc * x k := hmul.symm
        _ = x k * f k.castSucc := mul_comm _ _
    · simp only [φ, dif_neg hi, z]
      rw [Classical.choose_spec (Fin.exists_succAbove_eq hi)]
  · intro j z
    have hsum (s : Finset (Fin d)) :
        (∑ q ∈ s, (a j (k.succAbove q).castSucc -
          a j k.castSucc * f (k.succAbove q).castSucc / f k.castSucc) * z q) =
        (∑ q ∈ s, a j (k.succAbove q).castSucc * z q) -
          (a j k.castSucc / f k.castSucc) *
            (∑ q ∈ s, f (k.succAbove q).castSucc * z q) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert q s hq ih =>
          simp only [Finset.sum_insert, hq, not_false_eq_true]
          rw [ih]
          simp [sub_eq_add_neg, div_eq_mul_inv, mul_add, add_mul, neg_mul, mul_neg,
            mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]
    unfold edge_weight
    simp only [b, Fin.lastCases_castSucc, Fin.lastCases_last]
    rw [hsum Finset.univ]
    rw [sum_succAbove]
    rw [φ_k]
    have hsumφ :
        (∑ q, a j (k.succAbove q).castSucc * φ z (k.succAbove q)) =
          ∑ q, a j (k.succAbove q).castSucc * z q := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [φ_succAbove]
    rw [hsumφ]
    dsimp [root]
    simp only [sub_eq_add_neg, div_eq_mul_inv, mul_add, add_mul, neg_mul, mul_neg]
    rw [show a j k.castSucc *
          ((∑ q, f (k.succAbove q).castSucc * z q) * (f k.castSucc)⁻¹) =
        a j k.castSucc * (f k.castSucc)⁻¹ *
          (∑ q, f (k.succAbove q).castSucc * z q) by
      rw [mul_assoc, mul_comm (∑ q, f (k.succAbove q).castSucc * z q), ← mul_assoc]]
    rw [show a j k.castSucc * (f (Fin.last (d + 1)) * (f k.castSucc)⁻¹) =
        a j k.castSucc * f (Fin.last (d + 1)) * (f k.castSucc)⁻¹ by
      rw [mul_assoc]]
    rw [neg_add_rev]
    let S : ℝ := ∑ q, a j (k.succAbove q).castSucc * z q
    let A : ℝ := a j k.castSucc * (f k.castSucc)⁻¹ *
      (∑ q, f (k.succAbove q).castSucc * z q)
    let B : ℝ := a j k.castSucc * f (Fin.last (d + 1)) * (f k.castSucc)⁻¹
    let C : ℝ := a j (Fin.last (d + 1))
    change (S + -A) + (C + -B) = ((-B + -A) + S) + C
    calc
      (S + -A) + (C + -B) = S + (-A + (C + -B)) := by rw [add_assoc]
      _ = S + (-A + (-B + C)) := by rw [add_comm C (-B)]
      _ = S + ((-A + -B) + C) :=
        congrArg (fun t : ℝ => S + t) (add_assoc (-A) (-B) C).symm
      _ = (S + (-A + -B)) + C := (add_assoc S (-A + -B) C).symm
      _ = ((-A + -B) + S) + C := by rw [add_comm S (-A + -B)]
      _ = ((-B + -A) + S) + C := by rw [add_comm (-A) (-B)]

@[blueprint "lem:affine-sign-pattern-count"
  (statement := /-- For every $d,m\in\mathbb{N}$ and every family of $m$
    affine functions on $\mathbb{R}^d$, at most $(2m+1)^d$ distinct
    three-valued sign patterns are realized. -/)
  (proof := /-- The proof is by induction on the dimension and, within a
    fixed positive dimension, on the number of functions. In dimension zero
    there is only one parameter point, and for an empty family there is only
    one sign vector. On adjoining a final affine function, restriction of a
    sign vector to the preceding functions gives an old sign vector. Every
    fiber has one default member; each of its at most two further members can
    occur only when the corresponding old sign cell meets the zero
    hyperplane of the final function, by
    \cref{lem:affine-sign-zero-between}. If the final function is constant,
    no fiber splits. Otherwise,
    \cref{lem:affine-zero-hyperplane-parametrization} parametrizes its zero
    hyperplane by $\mathbb{R}^{d-1}$ and makes the restrictions of the
    preceding functions affine. Thus the number of new patterns is at most the
    old number plus twice the dimension-$(d-1)$ bound. The induction
    hypotheses and
    $(2m+1)^d+2(2m+1)^{d-1}\le(2m+3)^d$ complete the estimate. -/)
  (title := /-- Counting realized affine sign patterns -/)
  (latexEnv := "lemma")]
lemma affine_sign_pattern_count {d m : ℕ}
    (a : Fin m → Fin (d + 1) → ℝ) :
    (affine_sign_patterns a).card ≤ (2 * m + 1) ^ d := by
  classical
  induction d generalizing m with
  | zero =>
      have hsingle : affine_sign_patterns a =
          {fun j : Fin m => compare (edge_weight (a j) (fun i => Fin.elim0 i)) 0} := by
        ext s
        simp only [affine_sign_patterns, Set.Finite.mem_toFinset, Set.mem_range,
          Finset.mem_singleton]
        constructor
        · rintro ⟨x, rfl⟩
          congr
        · rintro rfl
          exact ⟨fun i => Fin.elim0 i, rfl⟩
      rw [hsingle]
      simp
  | succ d hd =>
      induction m with
      | zero =>
          have hsingle : affine_sign_patterns a = {fun i => Fin.elim0 i} := by
            ext s
            simp only [affine_sign_patterns, Set.Finite.mem_toFinset, Set.mem_range,
              Finset.mem_singleton]
            constructor
            · rintro ⟨x, rfl⟩
              funext i
              exact Fin.elim0 i
            · rintro rfl
              refine ⟨0, ?_⟩
              funext i
              exact Fin.elim0 i
          rw [hsingle]
          simp
      | succ m hm =>
          change (affine_sign_patterns a).card ≤ (2 * (m + 1) + 1) ^ (d + 1)
          let a₀ : Fin m → Fin (d + 1 + 1) → ℝ := fun j => a j.castSucc
          let f : Fin (d + 1 + 1) → ℝ := a (Fin.last m)
          let drop : (Fin (m + 1) → Ordering) → (Fin m → Ordering) :=
            fun s j => s j.castSucc
          let B := (affine_sign_patterns a₀).filter fun s =>
            ∃ x : Fin (d + 1) → ℝ,
              edge_weight f x = 0 ∧
                (fun j : Fin m => compare (edge_weight (a₀ j) x) 0) = s
          have hdrop {s : Fin (m + 1) → Ordering}
              (hs : s ∈ affine_sign_patterns a) :
              drop s ∈ affine_sign_patterns a₀ := by
            simp only [affine_sign_patterns, Set.Finite.mem_toFinset, Set.mem_range] at hs ⊢
            obtain ⟨x, rfl⟩ := hs
            refine ⟨x, ?_⟩
            rfl
          have hsplit {s t : Fin (m + 1) → Ordering}
              (hs : s ∈ affine_sign_patterns a) (ht : t ∈ affine_sign_patterns a)
              (hst : drop s = drop t) (hne : s ≠ t) : drop s ∈ B := by
            have hlast : s (Fin.last m) ≠ t (Fin.last m) := by
              intro heq
              apply hne
              funext i
              refine Fin.lastCases heq ?_ i
              intro j
              exact congrFun hst j
            refine Finset.mem_filter.mpr ⟨hdrop hs, ?_⟩
            have hs' := hs
            have ht' := ht
            simp only [affine_sign_patterns, Set.Finite.mem_toFinset, Set.mem_range] at hs' ht'
            obtain ⟨x, rfl⟩ := hs'
            obtain ⟨y, rfl⟩ := ht'
            by_cases hx : edge_weight f x = 0
            · exact ⟨x, hx, rfl⟩
            by_cases hy : edge_weight f y = 0
            · refine ⟨y, hy, ?_⟩
              exact hst.symm
            have hxy : edge_weight f x < 0 ∧ 0 < edge_weight f y ∨
                edge_weight f y < 0 ∧ 0 < edge_weight f x := by
              change compare (edge_weight f x) 0 ≠ compare (edge_weight f y) 0 at hlast
              rcases lt_or_gt_of_ne hx with hxlt | hxgt
              · rcases lt_or_gt_of_ne hy with hylt | hygt
                · exfalso
                  apply hlast
                  rw [compare_lt_iff_lt.mpr hxlt, compare_lt_iff_lt.mpr hylt]
                · exact Or.inl ⟨hxlt, hygt⟩
              · rcases lt_or_gt_of_ne hy with hylt | hygt
                · exact Or.inr ⟨hylt, hxgt⟩
                · exfalso
                  apply hlast
                  rw [compare_gt_iff_gt.mpr hxgt, compare_gt_iff_gt.mpr hygt]
            rcases hxy with hxy | hxy
            · obtain ⟨z, hz, hsign⟩ :=
                affine_sign_zero_between a₀ f x y (fun j => congrFun hst j)
                  hxy.1 hxy.2
              refine ⟨z, hz, ?_⟩
              funext j
              exact hsign j
            · obtain ⟨z, hz, hsign⟩ :=
                affine_sign_zero_between a₀ f y x (fun j => (congrFun hst j).symm)
                  hxy.1 hxy.2
              refine ⟨z, hz, ?_⟩
              funext j
              exact (hsign j).trans (congrFun hst j).symm
          have sum_le_sum_local (s : Finset (Fin m → Ordering))
              (u v : (Fin m → Ordering) → ℕ)
              (h : ∀ i ∈ s, u i ≤ v i) :
              (∑ i ∈ s, u i) ≤ ∑ i ∈ s, v i := by
            induction s using Finset.induction_on with
            | empty => simp
            | @insert i s hi ih =>
                rw [Finset.sum_insert hi, Finset.sum_insert hi]
                exact Nat.add_le_add (h i (Finset.mem_insert_self i s))
                  (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
          have sum_mono_nat (s t : Finset (Fin m → Ordering))
              (w : (Fin m → Ordering) → ℕ) (hst : s ⊆ t) :
              (∑ i ∈ s, w i) ≤ ∑ i ∈ t, w i := by
            induction s using Finset.induction_on generalizing t with
            | empty => simp
            | @insert i s hi ih =>
                have hit : i ∈ t := hst (Finset.mem_insert_self i s)
                have hsub : s ⊆ t.erase i := by
                  intro j hj
                  rw [Finset.mem_erase]
                  exact ⟨fun hji => hi (hji ▸ hj),
                    hst (Finset.mem_insert_of_mem hj)⟩
                rw [Finset.sum_insert hi]
                calc
                  w i + ∑ j ∈ s, w j ≤ w i + ∑ j ∈ t.erase i, w j :=
                    Nat.add_le_add_left (ih (t.erase i) hsub) (w i)
                  _ = ∑ j ∈ insert i (t.erase i), w j :=
                    (Finset.sum_insert (by simp : i ∉ t.erase i)).symm
                  _ = ∑ j ∈ t, w j := by rw [Finset.insert_erase hit]
          have sum_indicator (s t : Finset (Fin m → Ordering)) (hst : t ⊆ s) :
              (∑ i ∈ s, if i ∈ t then 3 else 1) = s.card + 2 * t.card := by
            induction s using Finset.induction_on generalizing t with
            | empty =>
                have ht : t = ∅ := by
                  ext i
                  constructor
                  · intro hi
                    simpa using hst hi
                  · intro hi
                    simpa using hi
                subst t
                simp
            | @insert i s hi ih =>
                by_cases hit : i ∈ t
                · have hsub : t.erase i ⊆ s := by
                    intro j hj
                    have hjt := (Finset.mem_erase.mp hj).2
                    have hjins := hst hjt
                    exact (Finset.mem_insert.mp hjins).resolve_left
                      (Finset.mem_erase.mp hj).1
                  have hsum : (∑ j ∈ s, if j ∈ t then 3 else 1) =
                      ∑ j ∈ s, if j ∈ t.erase i then 3 else 1 := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    have hji : j ≠ i := fun hji => hi (hji ▸ hj)
                    simp [Finset.mem_erase, hji]
                  rw [Finset.sum_insert hi]
                  simp only [hit, if_true]
                  rw [hsum, ih (t.erase i) hsub]
                  have hcardT : (t.erase i).card + 1 = t.card :=
                    Finset.card_erase_add_one hit
                  have hcardS : (insert i s).card = s.card + 1 := by simp [hi]
                  omega
                · have hsub : t ⊆ s := by
                    intro j hj
                    exact (Finset.mem_insert.mp (hst hj)).resolve_left
                      (fun hji => hit (hji ▸ hj))
                  simp [hi, hit, ih t hsub]
                  omega
          have hcard : (affine_sign_patterns a).card ≤
              (affine_sign_patterns a₀).card + 2 * B.card := by
            rw [Finset.card_eq_sum_card_image drop]
            calc
              ∑ p ∈ (affine_sign_patterns a).image drop,
                  ((affine_sign_patterns a).filter fun s => drop s = p).card
                  ≤ ∑ p ∈ (affine_sign_patterns a).image drop,
                      (if p ∈ B then 3 else 1) := by
                    apply sum_le_sum_local
                    intro p hp
                    split_ifs with hpB
                    · have hinj : Set.InjOn
                          (fun s : Fin (m + 1) → Ordering => s (Fin.last m))
                          (↑((affine_sign_patterns a).filter fun s => drop s = p) :
                            Set (Fin (m + 1) → Ordering)) := by
                        intro s hs t ht heq
                        simp only [Finset.mem_coe, Finset.mem_filter] at hs ht
                        funext i
                        refine Fin.lastCases heq ?_ i
                        intro j
                        change drop s j = drop t j
                        rw [hs.2, ht.2]
                      calc
                        ((affine_sign_patterns a).filter fun s => drop s = p).card =
                            (((affine_sign_patterns a).filter fun s => drop s = p).image
                              fun s => s (Fin.last m)).card :=
                          (Finset.card_image_iff.mpr hinj).symm
                        _ ≤ (Finset.univ : Finset Ordering).card := by
                          apply Finset.card_le_card
                          simp
                        _ = 3 := by decide
                    · rw [Finset.card_le_one]
                      intro s hs t ht
                      simp only [Finset.mem_filter] at hs ht
                      by_contra hne
                      apply hpB
                      rw [← hs.2]
                      exact hsplit hs.1 ht.1 (hs.2.trans ht.2.symm) hne
              _ ≤ ∑ p ∈ affine_sign_patterns a₀, (if p ∈ B then 3 else 1) := by
                    apply sum_mono_nat
                    intro p hp
                    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
                      exact hdrop hs
              _ = (affine_sign_patterns a₀).card + 2 * B.card := by
                    apply sum_indicator
                    intro p hp
                    exact (Finset.mem_filter.mp hp).1
          by_cases hconst : ∀ i : Fin (d + 1), f i.castSucc = 0
          · have hfconst (x : Fin (d + 1) → ℝ) :
                edge_weight f x = f (Fin.last (d + 1)) := by
              simp [edge_weight, hconst]
            have hinj : Set.InjOn drop ↑(affine_sign_patterns a) := by
              intro s hs t ht heq
              funext i
              refine Fin.lastCases ?_ ?_ i
              · have hs' := hs
                have ht' := ht
                simp only [Finset.mem_coe, affine_sign_patterns,
                  Set.Finite.mem_toFinset, Set.mem_range] at hs' ht'
                obtain ⟨x, rfl⟩ := hs'
                obtain ⟨y, rfl⟩ := ht'
                change compare (edge_weight f x) 0 = compare (edge_weight f y) 0
                rw [hfconst, hfconst]
              · intro j
                exact congrFun heq j
            have hproj : (affine_sign_patterns a).card ≤
                (affine_sign_patterns a₀).card := by
              calc
                (affine_sign_patterns a).card =
                    ((affine_sign_patterns a).image drop).card :=
                  (Finset.card_image_iff.mpr hinj).symm
                _ ≤ (affine_sign_patterns a₀).card := by
                  apply Finset.card_le_card
                  intro p hp
                  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
                  exact hdrop hs
            calc
              (affine_sign_patterns a).card ≤ (affine_sign_patterns a₀).card := hproj
              _ ≤ (2 * m + 1) ^ (d + 1) := hm a₀
              _ ≤ (2 * (m + 1) + 1) ^ (d + 1) :=
                Nat.pow_le_pow_left (by omega) (d + 1)
          · obtain ⟨k, hk⟩ : ∃ k : Fin (d + 1), f k.castSucc ≠ 0 := by
              simpa only [not_forall] using hconst
            obtain ⟨b, φ, hφzero, hφonto, hrestrict⟩ :=
              affine_zero_hyperplane_parametrization a₀ f k hk
            have hBsub : B ⊆ affine_sign_patterns b := by
              intro p hp
              obtain ⟨hpold, x, hfx, hpat⟩ := Finset.mem_filter.mp hp
              obtain ⟨z, hz⟩ := hφonto x hfx
              simp only [affine_sign_patterns, Set.Finite.mem_toFinset, Set.mem_range]
              refine ⟨z, ?_⟩
              funext j
              rw [hrestrict j z, hz]
              exact congrFun hpat j
            have hBcard : B.card ≤ (2 * m + 1) ^ d :=
              (Finset.card_le_card hBsub).trans (hd b)
            have hrec : (affine_sign_patterns a).card ≤
                (2 * m + 1) ^ (d + 1) + 2 * (2 * m + 1) ^ d :=
              hcard.trans (Nat.add_le_add (hm a₀) (Nat.mul_le_mul_left 2 hBcard))
            calc
              (affine_sign_patterns a).card ≤
                  (2 * m + 1) ^ (d + 1) + 2 * (2 * m + 1) ^ d := hrec
              _ = (2 * m + 1) ^ d * ((2 * m + 1) + 2) := by
                rw [pow_succ, Nat.mul_comm 2 ((2 * m + 1) ^ d), ← Nat.mul_add]
              _ ≤ (2 * (m + 1) + 1) ^ d * (2 * (m + 1) + 1) :=
                Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) d) (by omega)
              _ = (2 * (m + 1) + 1) ^ (d + 1) := by rw [pow_succ]

@[blueprint "lem:affine-comparison-bound"
  (statement := /-- Let $a_1,\ldots,a_m\in\mathbb{R}^{d+1}$ be coefficient
    vectors of affine functions. There is a finite family $\mathcal R$ of at
    most $(2m+1)^d$ subsets of $\mathbb{R}^d$ which covers
    $\mathbb{R}^d$ and on each member of which the truth value of every
    comparison $\operatorname{wt}_{a_j}(x)\le 0$ is constant, where affine
    evaluation is as in \cref{def:edge-weight}. -/)
  (proof := /-- Use the realized three-valued sign vectors from
    \cref{def:affine-sign-patterns}. For each realized vector $s$, let $Q_s$
    be the set of points at which every affine evaluation from
    \cref{def:edge-weight} has the sign prescribed by $s$, and let
    $\mathcal R$ be the finite set of these cells. Every point lies in the
    cell indexed by its own sign vector. If two points lie in the same cell,
    their comparisons with zero agree coordinatewise, so the corresponding
    weak inequalities are equivalent. The image defining $\mathcal R$ has
    cardinality at most the number of realized sign vectors, which is at most
    $(2m+1)^d$ by \cref{lem:affine-sign-pattern-count}. -/)
  (title := /-- Dimension-sensitive affine comparison bound -/)
  (latexEnv := "lemma")]
lemma affine_comparison_bound {d m : ℕ}
    (a : Fin m → Fin (d + 1) → ℝ) :
    ∃ R : Finset (Set (Fin d → ℝ)),
      (∀ x : Fin d → ℝ, ∃ Q ∈ R, x ∈ Q) ∧
      (∀ Q ∈ R, ∀ x ∈ Q, ∀ y ∈ Q, ∀ j : Fin m,
        (edge_weight (a j) x ≤ 0 ↔ edge_weight (a j) y ≤ 0)) ∧
      R.card ≤ (2 * m + 1) ^ d := by
  classical
  let cell : (Fin m → Ordering) → Set (Fin d → ℝ) := fun s =>
    {x | ∀ j, compare (edge_weight (a j) x) 0 = s j}
  let R : Finset (Set (Fin d → ℝ)) := (affine_sign_patterns a).image cell
  refine ⟨R, ?_, ?_, ?_⟩
  · intro x
    let s : Fin m → Ordering := fun j => compare (edge_weight (a j) x) 0
    refine ⟨cell s, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨s, ?_, rfl⟩
      simp only [affine_sign_patterns, Set.Finite.mem_toFinset, Set.mem_range]
      exact ⟨x, rfl⟩
    · intro j
      rfl
  · intro Q hQ x hx y hy j
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hQ
    change (∀ j, compare (edge_weight (a j) x) 0 = s j) at hx
    change (∀ j, compare (edge_weight (a j) y) 0 = s j) at hy
    rw [← compare_le_iff_le, ← compare_le_iff_le, hx j, hy j]
  · exact Finset.card_image_le.trans (affine_sign_pattern_count a)

@[blueprint "lem:balanced-cover-chain-nodup"
  (statement := /-- Let $G$ be a parametric directed acyclic graph. Every
    finite vertex list whose consecutive vertices are edges of $G$ has no
    repeated vertex. -/)
  (proof := /-- Regard every edge as a one-step member of the transitive
    closure of the edge relation. The chain property then implies pairwise
    transitive reachability between earlier and later entries. Equal entries
    would therefore give a nonempty directed closed walk, contrary to the
    acyclicity condition in \cref{def:parametric-dag}. -/)
  (title := /-- Vertex distinctness along an acyclic chain -/)
  (latexEnv := "lemma")]
lemma balanced_cover_chain_nodup {d : ℕ} (G : parametric_dag d)
    {p : List (Fin G.n)}
    (hp : p.IsChain (fun u v => (G.weight u v).isSome = true)) :
    p.Nodup := by
  have hchain : p.IsChain
      (Relation.TransGen (fun u v => (G.weight u v).isSome = true)) :=
    hp.imp fun _ _ h => Relation.TransGen.single h
  have hpair := hchain.pairwise
  exact hpair.imp (fun {u v} (huv : Relation.TransGen
      (fun a b => (G.weight a b).isSome = true) u v) => by
    intro huv_eq
    subst v
    exact G.acyclic u huv)

@[blueprint "lem:balanced-cover-path-weight-append"
  (statement := /-- Let $p$ and $q$ be vertex lists in a parametric directed
    acyclic graph, and suppose that the last vertex of $p$ equals the first
    vertex of $q$ whenever these vertices exist. Deleting the repeated first
    vertex of $q$ before concatenation makes path weight additive for every
    parameter vector. -/)
  (proof := /-- Induct on $p$. If $p$ is empty, the endpoint hypothesis forces
    $q$ to be empty. If $p$ is a singleton, the concatenation is $q$ and the
    weight of $p$ is zero. For a list with at least two entries, unfold the
    first edge contribution in \cref{def:path-weight} and apply the induction
    hypothesis to the tail, which has the same final vertex as $p$. -/)
  (title := /-- Additivity of path weight under overlapped concatenation -/)
  (latexEnv := "lemma")]
lemma balanced_cover_path_weight_append {d : ℕ} (G : parametric_dag d)
    (p q : List (Fin G.n)) (x : Fin d → ℝ)
    (hjoin : p.getLast? = q.head?) :
    path_weight G (p ++ q.tail) x = path_weight G p x + path_weight G q x := by
  induction p with
  | nil =>
      cases q <;> simp [path_weight] at hjoin ⊢
  | cons a p ih =>
      cases p with
      | nil =>
          cases q with
          | nil => simp [path_weight] at hjoin
          | cons b q =>
              simp only [List.getLast?_singleton, List.head?_cons] at hjoin
              cases Option.some.inj hjoin
              simp [path_weight]
      | cons b p =>
          simp only [List.getLast?_cons_cons] at hjoin
          change
            (G.weight a b).elim 0 (fun c => edge_weight c x) +
                path_weight G ((b :: p) ++ q.tail) x =
              ((G.weight a b).elim 0 (fun c => edge_weight c x) +
                path_weight G (b :: p) x) + path_weight G q x
          rw [ih hjoin]
          simp only [add_assoc]

@[blueprint "lem:balanced-cover-bounded-join"
  (statement := /-- Let $p$ be a directed path from $u$ to $z$ with at most
    $L$ edges and let $q$ be a directed path from $z$ to $v$ with at most
    $L$ edges. Then the overlapped concatenation $p\mathbin{+\!+}q.tail$ is a
    directed path from $u$ to $v$ with at most $2L$ edges. -/)
  (proof := /-- Rewrite $p$ as its initial segment followed by its last
    vertex $z$, and rewrite $q$ as $z$ followed by its tail. The overlap
    concatenation lemma for chains gives the edge condition. The endpoint
    identities follow from the nonemptiness of the two lists, and the length
    bound follows because exactly one copy of $z$ is retained. -/)
  (title := /-- Joining two bounded directed paths -/)
  (latexEnv := "lemma")]
lemma balanced_cover_bounded_join {d : ℕ} (G : parametric_dag d)
    (L : ℕ) (u z v : Fin G.n) (p q : List (Fin G.n))
    (hp_head : p.head? = some u) (hp_last : p.getLast? = some z)
    (hp_chain : p.IsChain (fun a b => (G.weight a b).isSome = true))
    (hp_len : p.length ≤ L + 1)
    (hq_head : q.head? = some z) (hq_last : q.getLast? = some v)
    (hq_chain : q.IsChain (fun a b => (G.weight a b).isSome = true))
    (hq_len : q.length ≤ L + 1) :
    (p ++ q.tail).head? = some u ∧
      (p ++ q.tail).getLast? = some v ∧
      (p ++ q.tail).IsChain
        (fun a b => (G.weight a b).isSome = true) ∧
      (p ++ q.tail).length ≤ 2 * L + 1 := by
  have hp_ne : p ≠ [] := by
    intro hp
    simp [hp] at hp_head
  have hq_ne : q ≠ [] := by
    intro hq
    simp [hq] at hq_head
  have hp_decomp : p.dropLast ++ [z] = p :=
    List.dropLast_append_getLast? z (by simpa [hp_last])
  have hq_decomp : z :: q.tail = q := by
    cases q with
    | nil => contradiction
    | cons a q =>
        simp only [List.head?_cons, Option.some.injEq] at hq_head
        subst a
        rfl
  have hchain : (p ++ q.tail).IsChain
      (fun a b => (G.weight a b).isSome = true) := by
    have hp_chain' := hp_chain
    have hq_chain' := hq_chain
    rw [← hp_decomp] at hp_chain'
    rw [← hq_decomp] at hq_chain'
    rw [← hp_decomp]
    exact hp_chain'.append_overlap hq_chain' (by simp)
  refine ⟨?_, ?_, hchain, ?_⟩
  · simpa [List.head?_append, hp_ne] using hp_head
  · cases q with
    | nil => contradiction
    | cons a q =>
        simp only [List.head?_cons, Option.some.injEq] at hq_head
        subst a
        cases q with
        | nil =>
            simp only [List.getLast?_singleton, Option.some.injEq] at hq_last
            subst v
            simpa using hp_last
        | cons b q =>
            rw [List.getLast?_append_of_ne_nil]
            · simpa using hq_last
            · simp
  · rw [List.length_append, List.length_tail]
    omega

@[blueprint "lem:balanced-cover-bounded-split"
  (statement := /-- Let $L\ge1$. Every directed path from $u$ to $v$ with at
    most $2L$ edges is the overlapped concatenation of a path from $u$ to some
    vertex $z$ and a path from $z$ to $v$, each having at most $L$ edges. -/)
  (proof := /-- If the original path already has at most $L$ edges, use it as
    the first part and the singleton list $[v]$ as the second. Otherwise, take
    the first $L+1$ vertices and drop the first $L$ vertices. These lists
    overlap at the vertex in position $L$. Taking and dropping preserve the
    chain relation; their endpoint and length properties follow from the list
    decomposition and the assumed $2L$ bound. -/)
  (title := /-- Splitting a bounded directed path -/)
  (latexEnv := "lemma")]
lemma balanced_cover_bounded_split {d : ℕ} (G : parametric_dag d)
    (L : ℕ) (hL : 1 ≤ L) (u v : Fin G.n) (p : List (Fin G.n))
    (hp_head : p.head? = some u) (hp_last : p.getLast? = some v)
    (hp_chain : p.IsChain (fun a b => (G.weight a b).isSome = true))
    (hp_len : p.length ≤ 2 * L + 1) :
    ∃ (z : Fin G.n) (p₁ p₂ : List (Fin G.n)),
      p₁.head? = some u ∧ p₁.getLast? = some z ∧
      p₁.IsChain (fun a b => (G.weight a b).isSome = true) ∧
      p₁.length ≤ L + 1 ∧
      p₂.head? = some z ∧ p₂.getLast? = some v ∧
      p₂.IsChain (fun a b => (G.weight a b).isSome = true) ∧
      p₂.length ≤ L + 1 ∧ p = p₁ ++ p₂.tail := by
  by_cases hshort : p.length ≤ L + 1
  · refine ⟨v, p, [v], hp_head, hp_last, hp_chain, hshort, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · simp
    · simp
  · have hindex : L < p.length := by omega
    let z : Fin G.n := p[L]
    refine ⟨z, p.take (L + 1), p.drop L, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.head?_take]
      simp [hp_head]
    · rw [List.getLast?_take]
      simp [z, hindex]
    · exact hp_chain.take _
    · simp
    · simpa [z] using (List.head?_drop (l := p) (i := L))
    · rw [List.getLast?_drop]
      simp [hindex, hp_last]
    · exact hp_chain.drop _
    · rw [List.length_drop]
      omega
    · simpa only [List.tail_drop] using (List.take_append_drop (L + 1) p).symm

@[blueprint "lem:balanced-cover-path-weight-affine"
  (statement := /-- The weight of every finite vertex list in a parametric
    directed acyclic graph is an affine function of the parameter vector:
    there is a coefficient vector whose affine evaluation equals the path
    weight at every parameter vector. -/)
  (proof := /-- Induct on the list. Lists of length at most one have weight
    zero. For a list beginning with two vertices, use the coefficient vector
    of their edge, or the zero vector if that edge is absent, and add it
    coordinatewise to the coefficient vector supplied by the induction
    hypothesis for the tail. Expanding \cref{def:edge-weight,def:path-weight}
    and distributing the finite sum proves the required identity. -/)
  (title := /-- Affineness of finite path weight -/)
  (latexEnv := "lemma")]
lemma balanced_cover_path_weight_affine {d : ℕ} (G : parametric_dag d)
    (p : List (Fin G.n)) :
    ∃ a : Fin (d + 1) → ℝ,
      ∀ x : Fin d → ℝ, edge_weight a x = path_weight G p x := by
  induction p with
  | nil =>
      refine ⟨fun _ => 0, ?_⟩
      intro x
      simp [edge_weight, path_weight]
  | cons u p ih =>
      cases p with
      | nil =>
          refine ⟨fun _ => 0, ?_⟩
          intro x
          simp [edge_weight, path_weight]
      | cons v p =>
          obtain ⟨b, hb⟩ := ih
          let c : Fin (d + 1) → ℝ := (G.weight u v).elim 0 id
          refine ⟨fun i => c i + b i, ?_⟩
          intro x
          have hedge : edge_weight c x =
              (G.weight u v).elim 0 (fun a => edge_weight a x) := by
            cases h : G.weight u v <;> simp [c, h, edge_weight]
          rw [edge_weight]
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib]
          calc
            (∑ i : Fin d, c i.castSucc * x i) +
                  (∑ i : Fin d, b i.castSucc * x i) +
                  (c (Fin.last d) + b (Fin.last d)) =
                ((∑ i : Fin d, c i.castSucc * x i) + c (Fin.last d)) +
                  ((∑ i : Fin d, b i.castSucc * x i) + b (Fin.last d)) := by
                    ac_rfl
            _ = edge_weight c x + edge_weight b x := rfl
            _ = (G.weight u v).elim 0 (fun a => edge_weight a x) +
                  path_weight G (v :: p) x := by rw [hedge, hb]
            _ = path_weight G (u :: v :: p) x := by rfl

@[blueprint "def:balanced-cover-assignment-good"
  (statement := /-- An assignment is good at a parameter vector $x$ and
    length bound $L$ if, for every ordered vertex pair, it records no path
    exactly when no directed path with at most $L$ edges exists, and otherwise
    records a minimum-weight such path at $x$. -/)
  (title := /-- Correct bounded-path assignment at one parameter -/)
  (latexEnv := "definition")]
def balanced_cover_assignment_good {d : ℕ} (G : parametric_dag d) (L : ℕ)
    (x : Fin d → ℝ)
    (f : Fin G.n → Fin G.n → Option (List (Fin G.n))) : Prop :=
  ∀ u v : Fin G.n,
    match f u v with
    | none => ¬ ∃ p : List (Fin G.n),
        p.head? = some u ∧ p.getLast? = some v ∧
        p.IsChain (fun a b => (G.weight a b).isSome = true) ∧
        p.length ≤ L + 1
    | some p =>
        (p.head? = some u ∧ p.getLast? = some v ∧
          p.IsChain (fun a b => (G.weight a b).isSome = true) ∧
          p.length ≤ L + 1) ∧
        ∀ q : List (Fin G.n),
          (q.head? = some u ∧ q.getLast? = some v ∧
            q.IsChain (fun a b => (G.weight a b).isSome = true) ∧
            q.length ≤ L + 1) →
          path_weight G p x ≤ path_weight G q x

@[blueprint "def:balanced-cover-family-good"
  (statement := /-- A finite family of pairs $(f,Q)$ is good for a length
    bound $L$ if its regions $Q$ cover the parameter space and every
    assignment $f$ is good, in the sense of
    \cref{def:balanced-cover-assignment-good}, at every point of its region. -/)
  (title := /-- Finite regional family of bounded-path assignments -/)
  (latexEnv := "definition")]
def balanced_cover_family_good {d : ℕ} (G : parametric_dag d) (L : ℕ)
    (F : Finset ((Fin G.n → Fin G.n → Option (List (Fin G.n))) ×
      Set (Fin d → ℝ))) : Prop :=
  (∀ x : Fin d → ℝ, ∃ e ∈ F, x ∈ e.2) ∧
    ∀ e ∈ F, ∀ x ∈ e.2, balanced_cover_assignment_good G L x e.1

@[blueprint "lem:balanced-cover-base-assignment"
  (statement := /-- For a parametric directed acyclic graph there is one
    parameter-independent assignment which, for every ordered pair of
    vertices, either records that no path with at most one edge exists or
    records a minimum-weight such path. -/)
  (proof := /-- Assign the singleton list $[u]$ when $u=v$, assign $[u,v]$
    when $u\ne v$ and the edge $uv$ exists, and assign nothing otherwise.
    A path with at most one edge has one or two vertices. Its endpoint and
    chain conditions force it to be exactly the corresponding assigned list;
    a two-vertex path from a vertex to itself is excluded by acyclicity in
    \cref{def:parametric-dag}. Hence the assignment is minimum for every
    parameter vector. -/)
  (title := /-- Parameter-independent one-edge shortest paths -/)
  (latexEnv := "lemma")]
lemma balanced_cover_base_assignment {d : ℕ} (G : parametric_dag d) :
    ∃ f : Fin G.n → Fin G.n → Option (List (Fin G.n)),
      ∀ x : Fin d → ℝ, balanced_cover_assignment_good G 1 x f := by
  classical
  let f : Fin G.n → Fin G.n → Option (List (Fin G.n)) := fun u v =>
    if u = v then some [u]
    else if (G.weight u v).isSome then some [u, v] else none
  have classify : ∀ (u v : Fin G.n) (p : List (Fin G.n)),
      p.head? = some u → p.getLast? = some v →
      p.IsChain (fun a b => (G.weight a b).isSome = true) →
      p.length ≤ 2 →
      (u = v ∧ p = [u]) ∨
        (u ≠ v ∧ p = [u, v] ∧ (G.weight u v).isSome = true) := by
    intro u v p hhead hlast hchain hlen
    cases p with
    | nil => simp at hhead
    | cons a p =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst a
        cases p with
        | nil =>
            simp only [List.getLast?_singleton, Option.some.injEq] at hlast
            subst v
            exact Or.inl ⟨rfl, rfl⟩
        | cons b p =>
            cases p with
            | nil =>
                simp only [List.getLast?_cons_cons, List.getLast?_singleton,
                  Option.some.injEq] at hlast
                subst b
                simp only [List.isChain_cons_cons, List.isChain_singleton,
                  and_true] at hchain
                by_cases huv : u = v
                · subst v
                  exact (G.acyclic u (Relation.TransGen.single hchain)).elim
                · exact Or.inr ⟨huv, rfl, hchain⟩
            | cons c p =>
                simp at hlen
  refine ⟨f, ?_⟩
  intro x u v
  change
    match f u v with
    | none => ¬ ∃ p : List (Fin G.n),
        p.head? = some u ∧ p.getLast? = some v ∧
        p.IsChain (fun a b => (G.weight a b).isSome = true) ∧ p.length ≤ 2
    | some p =>
        (p.head? = some u ∧ p.getLast? = some v ∧
          p.IsChain (fun a b => (G.weight a b).isSome = true) ∧ p.length ≤ 2) ∧
        ∀ q : List (Fin G.n),
          (q.head? = some u ∧ q.getLast? = some v ∧
            q.IsChain (fun a b => (G.weight a b).isSome = true) ∧ q.length ≤ 2) →
          path_weight G p x ≤ path_weight G q x
  by_cases huv : u = v
  · subst v
    simp only [f, if_pos, Option.some.injEq]
    refine ⟨by simp, ?_⟩
    intro q hq
    obtain ⟨hq_eq, rfl⟩ := (classify u u q hq.1 hq.2.1 hq.2.2.1 hq.2.2.2).resolve_right
      (fun h => h.1 rfl)
    simp
  · by_cases hedge : (G.weight u v).isSome
    · simp only [f, if_neg huv, if_pos hedge, Option.some.injEq]
      refine ⟨⟨by simp, by simp, ?_, by simp⟩, ?_⟩
      · simpa using hedge
      · intro q hq
        obtain ⟨_, rfl, _⟩ := (classify u v q hq.1 hq.2.1 hq.2.2.1 hq.2.2.2).resolve_left
          (fun h => huv h.1)
        exact le_rfl
    · simp only [f, if_neg huv, if_neg hedge]
      rintro ⟨q, hq⟩
      obtain ⟨_, _, hqedge⟩ := (classify u v q hq.1 hq.2.1 hq.2.2.1 hq.2.2.2).resolve_left
        (fun h => huv h.1)
      exact hedge hqedge

@[blueprint "lem:balanced-cover-refinement-round"
  (statement := /-- Let $L\ge1$ and let a finite regional family provide
    minimum paths with at most $L$ edges for every ordered vertex pair. The
    family can be refined to provide minimum paths with at most $2L$ edges,
    while increasing its cardinality by at most $(2n^4+1)^d$. -/)
  (proof := /-- For each old assignment and ordered pair $(u,v)$, concatenate
    its assigned paths for $(u,z)$ and $(z,v)$ over all $n$ choices of $z$.
    By \cref{lem:balanced-cover-bounded-split,lem:balanced-cover-bounded-join,
    lem:balanced-cover-path-weight-append}, these candidates contain a
    minimum path with at most $2L$ edges. Compare the candidates for every
    quadruple $(u,v,z,z')$. Their weights are affine by
    \cref{lem:balanced-cover-path-weight-affine}; padding the $n^4$ indexed
    comparisons when a candidate is absent is harmless. Apply
    \cref{lem:affine-comparison-bound} on each old region and intersect the
    resulting cells with that region. On every nonempty intersection, choose
    candidates minimizing at one representative point. Constancy of all
    pairwise comparisons makes the same choices minimum throughout the
    intersection. Taking the finite image of all old-region--new-cell pairs
    gives the claimed cover and cardinality multiplier. -/)
  (title := /-- One balanced refinement round -/)
  (latexEnv := "lemma")]
lemma balanced_cover_refinement_round {d : ℕ} (G : parametric_dag d)
    (L : ℕ) (hL : 1 ≤ L)
    (F : Finset ((Fin G.n → Fin G.n → Option (List (Fin G.n))) ×
      Set (Fin d → ℝ)))
    (hF : balanced_cover_family_good G L F) :
    ∃ F' : Finset ((Fin G.n → Fin G.n → Option (List (Fin G.n))) ×
        Set (Fin d → ℝ)),
      balanced_cover_family_good G (2 * L) F' ∧
      F'.card ≤ F.card * (2 * G.n ^ 4 + 1) ^ d := by
  classical
  rw [balanced_cover_family_good] at hF
  let candidate
      (f : Fin G.n → Fin G.n → Option (List (Fin G.n)))
      (u v z : Fin G.n) : Option (List (Fin G.n)) :=
    match f u z, f z v with
    | some p, some q => some (p ++ q.tail)
    | _, _ => none
  have candidate_valid : ∀ e ∈ F, ∀ x ∈ e.2, ∀ u v z p,
      candidate e.1 u v z = some p →
      p.head? = some u ∧ p.getLast? = some v ∧
      p.IsChain (fun a b => (G.weight a b).isSome = true) ∧
      p.length ≤ 2 * L + 1 := by
    intro e he x hx u v z p hp
    have hgood := hF.2 e he x hx
    cases huz : e.1 u z with
    | none => simp [candidate, huz] at hp
    | some p₁ =>
        cases hzv : e.1 z v with
        | none => simp [candidate, huz, hzv] at hp
        | some p₂ =>
            simp only [candidate, huz, hzv, Option.some.injEq] at hp
            subst p
            have h₁ := hgood u z
            have h₂ := hgood z v
            rw [huz] at h₁
            rw [hzv] at h₂
            exact balanced_cover_bounded_join G L u z v p₁ p₂
              h₁.1.1 h₁.1.2.1 h₁.1.2.2.1 h₁.1.2.2.2
              h₂.1.1 h₂.1.2.1 h₂.1.2.2.1 h₂.1.2.2.2
  have candidate_complete : ∀ e ∈ F, ∀ x ∈ e.2, ∀ u v p,
      p.head? = some u → p.getLast? = some v →
      p.IsChain (fun a b => (G.weight a b).isSome = true) →
      p.length ≤ 2 * L + 1 →
      ∃ z r, candidate e.1 u v z = some r ∧
        path_weight G r x ≤ path_weight G p x := by
    intro e he x hx u v p hp_head hp_last hp_chain hp_len
    obtain ⟨z, p₁, p₂, h₁head, h₁last, h₁chain, h₁len,
      h₂head, h₂last, h₂chain, h₂len, hp⟩ :=
      balanced_cover_bounded_split G L hL u v p hp_head hp_last hp_chain hp_len
    have hgood := hF.2 e he x hx
    have hu := hgood u z
    have hv := hgood z v
    cases huz : e.1 u z with
    | none =>
        rw [huz] at hu
        exact (hu ⟨p₁, h₁head, h₁last, h₁chain, h₁len⟩).elim
    | some r₁ =>
        rw [huz] at hu
        cases hzv : e.1 z v with
        | none =>
            rw [hzv] at hv
            exact (hv ⟨p₂, h₂head, h₂last, h₂chain, h₂len⟩).elim
        | some r₂ =>
            rw [hzv] at hv
            refine ⟨z, r₁ ++ r₂.tail, by simp [candidate, huz, hzv], ?_⟩
            rw [balanced_cover_path_weight_append G r₁ r₂ x
              (hu.1.2.1.trans hv.1.1.symm)]
            rw [hp, balanced_cover_path_weight_append G p₁ p₂ x
              (h₁last.trans h₂head.symm)]
            exact add_le_add (hu.2 p₁ ⟨h₁head, h₁last, h₁chain, h₁len⟩)
              (hv.2 p₂ ⟨h₂head, h₂last, h₂chain, h₂len⟩)
  let coeff (e : (Fin G.n → Fin G.n → Option (List (Fin G.n))) ×
      Set (Fin d → ℝ)) (u v z : Fin G.n) : Fin (d + 1) → ℝ :=
    Classical.choose
      (balanced_cover_path_weight_affine G ((candidate e.1 u v z).getD []))
  have coeff_spec : ∀ e u v z x,
      edge_weight (coeff e u v z) x =
        path_weight G ((candidate e.1 u v z).getD []) x := by
    intro e u v z x
    exact Classical.choose_spec
      (balanced_cover_path_weight_affine G ((candidate e.1 u v z).getD [])) x
  have edge_weight_sub : ∀ (a b : Fin (d + 1) → ℝ) (x : Fin d → ℝ),
      edge_weight (fun i => a i - b i) x = edge_weight a x - edge_weight b x := by
    intro a b x
    rw [edge_weight]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    change
      (∑ i : Fin d, a i.castSucc * x i) -
          (∑ i : Fin d, b i.castSucc * x i) +
          (a (Fin.last d) - b (Fin.last d)) =
        ((∑ i : Fin d, a i.castSucc * x i) + a (Fin.last d)) -
          ((∑ i : Fin d, b i.castSucc * x i) + b (Fin.last d))
    simp only [sub_eq_add_neg]
    rw [neg_add_rev]
    ac_rfl
  let Quad := Fin G.n × Fin G.n × Fin G.n × Fin G.n
  let enum : Quad ≃ Fin (Fintype.card Quad) := Fintype.equivFin Quad
  let comparison (e : (Fin G.n → Fin G.n → Option (List (Fin G.n))) ×
      Set (Fin d → ℝ)) (j : Fin (Fintype.card Quad)) : Fin (d + 1) → ℝ :=
    let t := enum.symm j
    fun i => coeff e t.1 t.2.1 t.2.2.1 i - coeff e t.1 t.2.1 t.2.2.2 i
  have comparison_spec : ∀ e u v z z' x,
      edge_weight (comparison e (enum (u, v, z, z'))) x =
        path_weight G ((candidate e.1 u v z).getD []) x -
          path_weight G ((candidate e.1 u v z').getD []) x := by
    intro e u v z z' x
    rw [show comparison e (enum (u, v, z, z')) =
        fun i => coeff e u v z i - coeff e u v z' i by
      simp [comparison, enum]]
    rw [edge_weight_sub, coeff_spec, coeff_spec]
  let cells (e : (Fin G.n → Fin G.n → Option (List (Fin G.n))) ×
      Set (Fin d → ℝ)) : Finset (Set (Fin d → ℝ)) :=
    Classical.choose (affine_comparison_bound (comparison e))
  have cells_spec : ∀ e,
      (∀ x : Fin d → ℝ, ∃ Q ∈ cells e, x ∈ Q) ∧
      (∀ Q ∈ cells e, ∀ x ∈ Q, ∀ y ∈ Q,
        ∀ j : Fin (Fintype.card Quad),
          (edge_weight (comparison e j) x ≤ 0 ↔
            edge_weight (comparison e j) y ≤ 0)) ∧
      (cells e).card ≤ (2 * G.n ^ 4 + 1) ^ d := by
    intro e
    have h := Classical.choose_spec (affine_comparison_bound (comparison e))
    simpa [cells, Quad, pow_succ, Nat.mul_assoc] using h
  let region (e : (Fin G.n → Fin G.n → Option (List (Fin G.n))) ×
      Set (Fin d → ℝ)) (Q : Set (Fin d → ℝ)) : Set (Fin d → ℝ) := e.2 ∩ Q
  let rep (e : (Fin G.n → Fin G.n → Option (List (Fin G.n))) ×
      Set (Fin d → ℝ)) (Q : Set (Fin d → ℝ)) : Fin d → ℝ :=
    if h : (region e Q).Nonempty then Classical.choose h else 0
  have rep_mem : ∀ e Q, (region e Q).Nonempty → rep e Q ∈ region e Q := by
    intro e Q h
    simp only [rep, dif_pos h]
    exact Classical.choose_spec h
  have selection_exists : ∀ e Q u v,
      ∃ o : Option (List (Fin G.n)),
        (o = none ↔ ∀ z, candidate e.1 u v z = none) ∧
        ∀ p, o = some p →
          ∃ z, candidate e.1 u v z = some p ∧
            ∀ z' r, candidate e.1 u v z' = some r →
              path_weight G p (rep e Q) ≤ path_weight G r (rep e Q) := by
    intro e Q u v
    let Z : Finset (Fin G.n) := Finset.univ.filter
      (fun z => (candidate e.1 u v z).isSome)
    by_cases hZ : Z.Nonempty
    · obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image Z
        (fun z => path_weight G ((candidate e.1 u v z).getD []) (rep e Q)) hZ
      have hzsome : (candidate e.1 u v z).isSome := by simpa [Z] using hz
      cases hcz : candidate e.1 u v z with
      | none => simp [hcz] at hzsome
      | some p =>
          refine ⟨some p, ?_, ?_⟩
          · constructor
            · intro h
              simp at h
            · intro hall
              exfalso
              simpa [hcz] using hall z
          · intro q hq
            simp only [Option.some.injEq] at hq
            subst q
            refine ⟨z, hcz, ?_⟩
            intro z' r hz'
            have hz'mem : z' ∈ Z := by simp [Z, hz']
            simpa [hcz, hz'] using hmin z' hz'mem
    · refine ⟨none, ?_, ?_⟩
      · constructor
        · intro _ z
          cases hz : candidate e.1 u v z with
          | none => rfl
          | some p =>
              exact (hZ ⟨z, by simp [Z, hz]⟩).elim
        · intro _
          rfl
      · intro p hp
        simp at hp
  let pick (e : (Fin G.n → Fin G.n → Option (List (Fin G.n))) ×
      Set (Fin d → ℝ)) (Q : Set (Fin d → ℝ)) (u v : Fin G.n) :=
    Classical.choose (selection_exists e Q u v)
  have pick_spec : ∀ e Q u v,
      (pick e Q u v = none ↔ ∀ z, candidate e.1 u v z = none) ∧
      ∀ p, pick e Q u v = some p →
        ∃ z, candidate e.1 u v z = some p ∧
          ∀ z' r, candidate e.1 u v z' = some r →
            path_weight G p (rep e Q) ≤ path_weight G r (rep e Q) := by
    intro e Q u v
    exact Classical.choose_spec (selection_exists e Q u v)
  have comparison_transfer : ∀ e Q, Q ∈ cells e →
      ∀ x, x ∈ region e Q → ∀ u v z z',
      path_weight G ((candidate e.1 u v z).getD []) (rep e Q) ≤
          path_weight G ((candidate e.1 u v z').getD []) (rep e Q) →
      path_weight G ((candidate e.1 u v z).getD []) x ≤
          path_weight G ((candidate e.1 u v z').getD []) x := by
    intro e Q hQ x hx u v z z' hle
    have hrep := rep_mem e Q ⟨x, hx⟩
    have hconst := (cells_spec e).2.1 Q hQ (rep e Q) hrep.2 x hx.2
      (enum (u, v, z, z'))
    rw [comparison_spec, comparison_spec] at hconst
    exact sub_nonpos.mp (hconst.mp (sub_nonpos.mpr hle))
  have pick_good : ∀ e ∈ F, ∀ Q ∈ cells e, ∀ x ∈ region e Q,
      balanced_cover_assignment_good G (2 * L) x (pick e Q) := by
    intro e he Q hQ x hx u v
    cases hpick : pick e Q u v with
    | none =>
        simp only
        intro hex
        obtain ⟨p, hp⟩ := hex
        obtain ⟨z, r, hzr, _⟩ := candidate_complete e he x hx.1 u v p
          hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
        have hnone := (pick_spec e Q u v).1.1 hpick z
        rw [hzr] at hnone
        contradiction
    | some p =>
        have hchosen := (pick_spec e Q u v).2 p hpick
        obtain ⟨z, hzp, hmin⟩ := hchosen
        refine ⟨candidate_valid e he x hx.1 u v z p hzp, ?_⟩
        intro q hq
        obtain ⟨z', r, hz'r, hrq⟩ := candidate_complete e he x hx.1 u v q
          hq.1 hq.2.1 hq.2.2.1 hq.2.2.2
        have hpr_rep := hmin z' r hz'r
        have hpr := comparison_transfer e Q hQ x hx u v z z' (by
          simpa [hzp, hz'r] using hpr_rep)
        have hpr' : path_weight G p x ≤ path_weight G r x := by
          simpa [hzp, hz'r] using hpr
        exact hpr'.trans hrq
  let indices := F.sigma fun e => cells e
  let F' : Finset ((Fin G.n → Fin G.n → Option (List (Fin G.n))) ×
      Set (Fin d → ℝ)) :=
    indices.image fun i => (pick i.1 i.2, region i.1 i.2)
  refine ⟨F', ?_, ?_⟩
  · rw [balanced_cover_family_good]
    constructor
    · intro x
      obtain ⟨e, he, hxe⟩ := hF.1 x
      obtain ⟨Q, hQ, hxQ⟩ := (cells_spec e).1 x
      refine ⟨(pick e Q, region e Q), ?_, hxe, hxQ⟩
      apply Finset.mem_image.mpr
      refine ⟨⟨e, Q⟩, ?_, rfl⟩
      simpa [indices] using And.intro he hQ
    · intro y hy x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      have hi' : i.1 ∈ F ∧ i.2 ∈ cells i.1 := by simpa [indices] using hi
      exact pick_good i.1 hi'.1 i.2 hi'.2 x hx
  · calc
      F'.card ≤ indices.card := Finset.card_image_le
      _ = ∑ e ∈ F, (cells e).card := by simp [indices]
      _ ≤ ∑ _e ∈ F, (2 * G.n ^ 4 + 1) ^ d := by
        have aux : ∀ S : Finset ((Fin G.n → Fin G.n → Option (List (Fin G.n))) ×
            Set (Fin d → ℝ)),
            (∀ e ∈ S, (cells e).card ≤ (2 * G.n ^ 4 + 1) ^ d) →
            (∑ e ∈ S, (cells e).card) ≤
              ∑ _e ∈ S, (2 * G.n ^ 4 + 1) ^ d := by
          intro S hS
          induction S using Finset.induction with
          | empty => simp
          | @insert e S he ih =>
              simp only [Finset.mem_insert] at hS
              rw [Finset.sum_insert he, Finset.sum_insert he]
              exact Nat.add_le_add (hS e (Or.inl rfl))
                (ih fun a ha => hS a (Or.inr ha))
        exact aux F fun e _ => (cells_spec e).2.2
      _ = F.card * (2 * G.n ^ 4 + 1) ^ d := by simp

@[blueprint "lem:balanced-shortest-path-cover"
  (statement := /-- Let $d\in\mathbb{N}$ and let $G$ be an affine-weighted
    directed acyclic graph on $n\ge 2$ vertices which has an $s$--$t$ path.
    Then $G$ has a finite shortest path cover $\mathcal S$ satisfying
    \[
      |\mathcal S|\le
      (2n^4+1)^{d(\lfloor\log_2 n\rfloor+1)}.
    \]
    The notions of directed acyclic graph and shortest path cover are those
    of \cref{def:parametric-dag, def:shortest-path-cover}. -/)
  (proof := /-- By \cref{lem:balanced-cover-base-assignment}, a singleton
    family whose region is all of $\mathbb{R}^d$ supplies minimum paths with
    at most one edge for every ordered pair of vertices. Apply
    \cref{lem:balanced-cover-refinement-round} inductively. After $k$ rounds
    the family supplies minimum paths with at most $2^k$ edges and has at
    most
    \[
      \bigl((2n^4+1)^d\bigr)^k=(2n^4+1)^{dk}
    \]
    members.

    Set $k=\lfloor\log_2 n\rfloor+1$. Every directed path has no repeated
    vertex by \cref{lem:balanced-cover-chain-nodup}, so it has at most $n$
    vertices. Since $n<2^k$, every $s$--$t$ path lies within the final length
    bound. Consequently the path assigned to $(s,t)$ on any final region is
    a globally shortest $s$--$t$ path there. The assumed existence of an
    $s$--$t$ path ensures that each nonempty final region has such an
    assignment.

    Take the assigned $s$--$t$ path from every nonempty final region and let
    $\mathcal S$ be the resulting finite image. The regional cover property
    shows that $\mathcal S$ is a shortest path cover, its cardinality is at
    most the number of final regions, and the preceding estimate with this
    value of $k$ is the required bound. -/)
  (title := /-- Balanced construction of a shortest path cover -/)
  (latexEnv := "lemma")]
lemma balanced_shortest_path_cover (d : ℕ) (G : parametric_dag d)
    (hn : 2 ≤ G.n) (hp : ∃ p : List (Fin G.n), st_path G p) :
    ∃ S : Set (List (Fin G.n)), S.Finite ∧ shortest_path_cover G S ∧
      S.ncard ≤
        (2 * G.n ^ 4 + 1) ^ (d * (Nat.log 2 G.n + 1)) := by
  classical
  let C := (2 * G.n ^ 4 + 1) ^ d
  have families : ∀ k : ℕ,
      ∃ F : Finset ((Fin G.n → Fin G.n → Option (List (Fin G.n))) ×
          Set (Fin d → ℝ)),
        balanced_cover_family_good G (2 ^ k) F ∧ F.card ≤ C ^ k := by
    intro k
    induction k with
    | zero =>
        obtain ⟨f, hf⟩ := balanced_cover_base_assignment G
        let F : Finset ((Fin G.n → Fin G.n → Option (List (Fin G.n))) ×
            Set (Fin d → ℝ)) := {(f, Set.univ)}
        refine ⟨F, ?_, ?_⟩
        · rw [balanced_cover_family_good]
          constructor
          · intro x
            exact ⟨(f, Set.univ), by simp [F]⟩
          · intro e he x hx
            have heq : e = (f, Set.univ) := by simpa [F] using he
            subst e
            simpa using hf x
        · simp [F, C]
    | succ k ih =>
        obtain ⟨F, hgood, hcard⟩ := ih
        obtain ⟨F', hgood', hcard'⟩ :=
          balanced_cover_refinement_round G (2 ^ k)
            (Nat.one_le_pow k 2 (by decide)) F hgood
        refine ⟨F', ?_, ?_⟩
        · simpa [pow_succ, Nat.mul_comm] using hgood'
        · calc
            F'.card ≤ F.card * C := by simpa [C] using hcard'
            _ ≤ C ^ k * C := Nat.mul_le_mul_right C hcard
            _ = C ^ (k + 1) := by rw [pow_succ]
  let K := Nat.log 2 G.n + 1
  obtain ⟨F, hF, hFcard⟩ := families K
  rw [balanced_cover_family_good] at hF
  have path_bounded : ∀ q : List (Fin G.n), st_path G q →
      q.head? = some G.s ∧ q.getLast? = some G.t ∧
      q.IsChain (fun a b => (G.weight a b).isSome = true) ∧
      q.length ≤ 2 ^ K + 1 := by
    intro q hq
    have hnodup := balanced_cover_chain_nodup G hq.2.2
    have hlen : q.length ≤ G.n := by
      simpa using hnodup.length_le_card
    have hpow : G.n < 2 ^ K := by
      simpa [K] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) G.n
    exact ⟨hq.1, hq.2.1, hq.2.2, by omega⟩
  obtain ⟨p₀, hp₀⟩ := hp
  have hp₀b := path_bounded p₀ hp₀
  let active := F.filter fun e => e.2.Nonempty
  let T : Finset (List (Fin G.n)) :=
    active.image fun e => (e.1 G.s G.t).getD []
  let S : Set (List (Fin G.n)) := ↑T
  have members_are_paths : ∀ p ∈ S, st_path G p := by
    intro p hpS
    have hpT : p ∈ T := hpS
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hpT
    have he' := Finset.mem_filter.mp he
    obtain ⟨x, hx⟩ := he'.2
    have hgood := hF.2 e he'.1 x hx G.s G.t
    cases hopt : e.1 G.s G.t with
    | none =>
        rw [hopt] at hgood
        exact (hgood ⟨p₀, hp₀b⟩).elim
    | some p =>
        rw [hopt] at hgood
        simpa [hopt, st_path] using
          And.intro hgood.1.1 (And.intro hgood.1.2.1 hgood.1.2.2.1)
  have cover : ∀ x : Fin d → ℝ, ∃ p ∈ S, shortest_path_at G p x := by
    intro x
    obtain ⟨e, he, hx⟩ := hF.1 x
    have hgood := hF.2 e he x hx G.s G.t
    cases hopt : e.1 G.s G.t with
    | none =>
        rw [hopt] at hgood
        exact (hgood ⟨p₀, hp₀b⟩).elim
    | some p =>
        rw [hopt] at hgood
        refine ⟨p, ?_, ?_⟩
        · change p ∈ T
          apply Finset.mem_image.mpr
          refine ⟨e, ?_, by simp [hopt]⟩
          exact Finset.mem_filter.mpr ⟨he, ⟨x, hx⟩⟩
        · refine ⟨?_, ?_⟩
          · exact ⟨hgood.1.1, hgood.1.2.1, hgood.1.2.2.1⟩
          · intro q hq
            exact hgood.2 q (path_bounded q hq)
  refine ⟨S, ?_, ⟨members_are_paths, cover⟩, ?_⟩
  · exact T.finite_toSet
  · calc
      S.ncard = T.card := by simp [S]
      _ ≤ active.card := Finset.card_image_le
      _ ≤ F.card := Finset.card_filter_le _ _
      _ ≤ C ^ K := hFcard
      _ = (2 * G.n ^ 4 + 1) ^ (d * (Nat.log 2 G.n + 1)) := by
        change ((2 * G.n ^ 4 + 1) ^ d) ^ (Nat.log 2 G.n + 1) = _
        rw [← pow_mul]

@[blueprint "lem:cover-recurrence"
  (statement := /-- For all $d,n\in\mathbb{N}$ with $n\ge2$,
    \[
      (2n^4+1)^{d(\lfloor\log_2 n\rfloor+1)}
      \le n^{12d\lfloor\log_2 n\rfloor}.
    \] -/)
  (proof := /-- Since $n\ge2$, one has $3\le n^2$, and therefore
    \[
      2n^4+1\le3n^4\le n^6.
    \]
    Moreover $\lfloor\log_2 n\rfloor\ge1$, whence
    $\lfloor\log_2 n\rfloor+1\le2\lfloor\log_2 n\rfloor$. Monotonicity of
    natural-number exponentiation in the base and exponent now gives
    \[
      (2n^4+1)^{d(\lfloor\log_2 n\rfloor+1)}
      \le (n^6)^{2d\lfloor\log_2 n\rfloor}
      =n^{12d\lfloor\log_2 n\rfloor}.
    \] -/)
  (title := /-- Solution of the cover-growth recurrence -/)
  (latexEnv := "lemma")]
lemma cover_recurrence (d n : ℕ) (hn : 2 ≤ n) :
    (2 * n ^ 4 + 1) ^ (d * (Nat.log 2 n + 1)) ≤
      n ^ (12 * d * Nat.log 2 n) := by
  have hlog : 1 ≤ Nat.log 2 n := Nat.log_pos (by omega) hn
  have hnpos : 0 < n := by omega
  have hpow1 : 1 ≤ n ^ 4 := Nat.one_le_pow 4 n hnpos
  have hfirst : 2 * n ^ 4 + 1 ≤ 3 * n ^ 4 := by omega
  have hsq : 3 ≤ n ^ 2 := by
    exact le_trans (by decide) (Nat.pow_le_pow_left hn 2)
  have hsecond : 3 * n ^ 4 ≤ n ^ 6 := by
    calc
      3 * n ^ 4 ≤ n ^ 2 * n ^ 4 := Nat.mul_le_mul_right _ hsq
      _ = n ^ 6 := by rw [← pow_add]
  have hbase : 2 * n ^ 4 + 1 ≤ n ^ 6 := le_trans hfirst hsecond
  have hdlog : d ≤ d * Nat.log 2 n := by
    simpa using Nat.mul_le_mul_left d hlog
  have hexp : d * (Nat.log 2 n + 1) ≤ 2 * d * Nat.log 2 n := by
    calc
      d * (Nat.log 2 n + 1) = d * Nat.log 2 n + d := by
        rw [Nat.mul_add, Nat.mul_one]
      _ ≤ d * Nat.log 2 n + d * Nat.log 2 n := Nat.add_le_add_left hdlog _
      _ = 2 * d * Nat.log 2 n := by rw [two_mul, Nat.add_mul]
  calc
    (2 * n ^ 4 + 1) ^ (d * (Nat.log 2 n + 1)) ≤
        (n ^ 6) ^ (d * (Nat.log 2 n + 1)) := Nat.pow_le_pow_left hbase _
    _ ≤ (n ^ 6) ^ (2 * d * Nat.log 2 n) :=
      Nat.pow_le_pow_right (Nat.pow_pos hnpos) hexp
    _ = n ^ (12 * d * Nat.log 2 n) := by
      rw [← pow_mul]
      simp [← Nat.mul_assoc]

@[blueprint "lem:solve-cover-recurrence"
  (statement := /-- Let $G$ be an affine-weighted directed acyclic graph
    having an $s$--$t$ path. For every parameter dimension $d$,
    \[
      |\operatorname{PSP}(G)|
      \le n^{12d\lfloor\log_2 n\rfloor},
    \]
    where $n$ is the number of vertices and the left-hand side is defined by
    \cref{def:mspc-size}. -/)
  (proof := /-- Because the source vertex belongs to $\operatorname{Fin}(n)$,
    one has $n\ge1$. If $n=1$, every $s$--$t$ path is nonempty and has no
    repeated vertex by \cref{lem:balanced-cover-chain-nodup}. Since
    $\operatorname{Fin}(1)$ has exactly one element, every such path is the
    singleton list consisting of the source vertex. This singleton path is
    therefore shortest for every parameter vector and by itself forms a
    shortest path cover. The definition in \cref{def:mspc-size} then gives
    $|\operatorname{PSP}(G)|\le1=n^{12d\lfloor\log_2 n\rfloor}$.

    Suppose now that $n\ge2$. By
    \cref{lem:balanced-shortest-path-cover} there is a finite shortest path
    cover $\mathcal S$ with
    \[
      |\mathcal S|\le
      (2n^4+1)^{d(\lfloor\log_2 n\rfloor+1)}.
    \]
    Since $|\mathcal S|$ is one of the natural numbers over which the
    infimum in \cref{def:mspc-size} is taken, that definition gives
    $|\operatorname{PSP}(G)|\le|\mathcal S|$. Applying
    \cref{lem:cover-recurrence} and transitivity proves the required
    estimate. -/)
  (title := /-- Uniform bound obtained from the balanced recurrence -/)
  (latexEnv := "lemma")]
lemma solve_cover_recurrence (d : ℕ) (G : parametric_dag d)
    (hp : ∃ p : List (Fin G.n), st_path G p) :
    mspc_size G ≤ G.n ^ (12 * d * Nat.log 2 G.n) := by
  by_cases hn : 2 ≤ G.n
  · obtain ⟨S, _, hScover, hScard⟩ :=
      balanced_shortest_path_cover d G hn hp
    calc
      mspc_size G ≤ S.ncard := by
        apply Nat.sInf_le
        exact ⟨S, hScover, rfl⟩
      _ ≤ (2 * G.n ^ 4 + 1) ^ (d * (Nat.log 2 G.n + 1)) := hScard
      _ ≤ G.n ^ (12 * d * Nat.log 2 G.n) := cover_recurrence d G.n hn
  · have hn1 : G.n = 1 := by
      have hslt : G.s.val < G.n := G.s.isLt
      omega
    have path_unique : ∀ q : List (Fin G.n), st_path G q → q = [G.s] := by
      intro q hq
      have hnodup := balanced_cover_chain_nodup G hq.2.2
      have hlen_le : q.length ≤ 1 := by
        simpa [hn1] using hnodup.length_le_card
      have hqne : q ≠ [] := by
        intro hqnil
        subst q
        simp [st_path] at hq
      have hlen_pos : 0 < q.length := List.length_pos_iff.mpr hqne
      have hlen : q.length = 1 := by omega
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
      subst q
      simpa using hq.1
    obtain ⟨p, hp⟩ := hp
    have hp_eq := path_unique p hp
    have hsingle_path : st_path G [G.s] := by simpa [hp_eq] using hp
    let S : Set (List (Fin G.n)) := {[G.s]}
    have hScover : shortest_path_cover G S := by
      constructor
      · intro q hq
        have hqeq : q = [G.s] := by simpa [S] using hq
        simpa [hqeq] using hsingle_path
      · intro x
        refine ⟨[G.s], by simp [S], hsingle_path, ?_⟩
        intro q hq
        rw [path_unique q hq]
    have hmspc : mspc_size G ≤ 1 := by
      apply Nat.sInf_le
      exact ⟨S, hScover, by simp [S]⟩
    simpa [hn1] using hmspc

@[blueprint "thm:linear-upper-bound"
  (statement := /-- There exists an absolute natural-number constant $C>0$
    such that, for every $d\in\mathbb{N}$ and every affine-weighted directed
    acyclic graph $G$ as in \cref{def:parametric-dag}, with $n=G.n$, one has
    \[
      |\operatorname{PSP}(G)|\le n^{C d\lfloor\log_2 n\rfloor}.
    \]
    Here $|\operatorname{PSP}(G)|$ is the least cardinality of a shortest path
    cover, with value zero if no such cover exists, as specified in
    \cref{def:mspc-size}. In particular,
    $|\operatorname{PSP}(G)|\in n^{O(d\log n)}$. -/)
  (proof := /-- Choose the absolute constant $C=12$, and fix a parameter
    dimension $d$ and an affine-weighted directed acyclic graph $G$. If $G$
    has an $s$--$t$ path, \cref{lem:solve-cover-recurrence} gives
    \[
      |\operatorname{PSP}(G)|
      \le n^{12d\lfloor\log_2 n\rfloor}.
    \]
    Suppose instead that $G$ has no $s$--$t$ path. A shortest path cover would,
    at the zero parameter vector, contain a shortest path and hence an
    $s$--$t$ path by
    \cref{def:shortest-path-cover, def:shortest-path-at}, a contradiction.
    Thus no shortest path cover exists. By the natural-number infimum
    convention in \cref{def:mspc-size}, one has
    $|\operatorname{PSP}(G)|=0$, which is at most
    $n^{12d\lfloor\log_2 n\rfloor}$. Since $12>0$, the two cases prove the
    asserted uniform estimate for every $G$. -/)
  (title := /-- Linear upper bound for minimum shortest path covers -/)
  (latexEnv := "theorem")]
theorem linear_upper_bound :
    ∃ C : ℕ, 0 < C ∧ ∀ (d : ℕ) (G : parametric_dag d),
      mspc_size G ≤ G.n ^ (C * d * Nat.log 2 G.n) := by
  refine ⟨12, by norm_num, ?_⟩
  intro d G
  by_cases hp : ∃ p : List (Fin G.n), st_path G p
  · exact solve_cover_recurrence d G hp
  · have hno_cover :
        ¬ ∃ S : Set (List (Fin G.n)), shortest_path_cover G S := by
      rintro ⟨S, hS⟩
      obtain ⟨p, _, hshort⟩ := hS.2 (fun _ => 0)
      exact hp ⟨p, hshort.1⟩
    have hset :
        {k : ℕ | ∃ S : Set (List (Fin G.n)),
          shortest_path_cover G S ∧ S.ncard = k} = ∅ := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨S, hS, _⟩
      exact hno_cover ⟨S, hS⟩
    rw [mspc_size, hset, Nat.sInf_empty]
    exact Nat.zero_le _

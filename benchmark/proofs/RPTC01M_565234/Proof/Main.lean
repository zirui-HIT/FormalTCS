import Architect
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Equiv.Fin.Basic

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:binary-matrix"
  (statement := /-- For nonnegative integers $r$ and $c$, an $r\times c$ binary matrix is a
  function from $\operatorname{Fin}(r)\times\operatorname{Fin}(c)$ to the Boolean values. -/)
  (title := /-- Binary matrices -/)
  (latexEnv := "definition")]
abbrev binary_matrix (r c : ℕ) := Matrix (Fin r) (Fin c) Bool

@[blueprint "def:matrix-weight"
  (statement := /-- The weight $\lVert A\rVert_1$ of a finite binary matrix $A$ is the number of
  ordered pairs $(i,j)$ for which $A(i,j)=1$. -/)
  (title := /-- Weight of a binary matrix -/)
  (latexEnv := "definition")]
def matrix_weight {r c : ℕ} (A : binary_matrix r c) : ℕ :=
  (Finset.univ.filter (fun p : Fin r × Fin c => A p.1 p.2 = true)).card

@[blueprint "def:contains-pattern"
  (statement := /-- Let $P$ be an $r\times c$ binary matrix and let $A$ be an $n\times m$ binary
  matrix.  We say that $A$ contains $P$ if there are strictly increasing maps
  $\rho:\operatorname{Fin}(r)\to\operatorname{Fin}(n)$ and
  $\kappa:\operatorname{Fin}(c)\to\operatorname{Fin}(m)$ such that every $1$-entry of $P$ maps
  to a $1$-entry of $A$.  Thus the permitted operations are deletion of rows and columns and
  replacement of selected $1$-entries by $0$-entries. -/)
  (title := /-- Ordered containment of a binary pattern -/)
  (latexEnv := "definition")]
def contains_pattern {r c n m : ℕ} (P : binary_matrix r c) (A : binary_matrix n m) : Prop :=
  ∃ ρ : Fin r → Fin n, StrictMono ρ ∧
    ∃ κ : Fin c → Fin m, StrictMono κ ∧
      ∀ i j, P i j = true → A (ρ i) (κ j) = true

@[blueprint "def:pattern-free"
  (statement := /-- A binary matrix $A$ is $P$-free if it does not contain the binary pattern $P$
  in the sense of \cref{def:contains-pattern}. -/)
  (title := /-- Pattern avoidance -/)
  (latexEnv := "definition")]
def pattern_free {r c n m : ℕ} (P : binary_matrix r c) (A : binary_matrix n m) : Prop :=
  ¬contains_pattern P A

@[blueprint "def:extremal-function"
  (statement := /-- For a fixed binary pattern $P$, the extremal function
  $\operatorname{Ex}(P,n)$ is the maximum weight of a $P$-free $n\times n$ binary matrix.  The
  maximum is taken over the finite set of all such matrices and is declared to be $0$ if that set
  is empty. -/)
  (title := /-- Extremal function of a binary pattern -/)
  (latexEnv := "definition")]
noncomputable def extremal_function {r c : ℕ} (P : binary_matrix r c) (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun A : binary_matrix n n => pattern_free P A)).sup matrix_weight

@[blueprint "def:pattern-s-zero"
  (statement := /-- The first exceptional weight-six pattern is
  \[
  S_0=\begin{pmatrix}1&0&1&0\\1&0&0&1\\0&1&0&1\end{pmatrix}.
  \] -/)
  (title := /-- The pattern $S_0$ -/)
  (latexEnv := "definition")]
def pattern_s_zero : binary_matrix 3 4 := fun i j =>
  decide ((i.1 = 0 ∧ (j.1 = 0 ∨ j.1 = 2)) ∨
    (i.1 = 1 ∧ (j.1 = 0 ∨ j.1 = 3)) ∨
    (i.1 = 2 ∧ (j.1 = 1 ∨ j.1 = 3)))

@[blueprint "def:pattern-s-one"
  (statement := /-- The second exceptional weight-six pattern is
  \[
  S_1=\begin{pmatrix}1&0&0&1\\1&0&1&0\\0&1&0&1\end{pmatrix}.
  \] -/)
  (title := /-- The pattern $S_1$ -/)
  (latexEnv := "definition")]
def pattern_s_one : binary_matrix 3 4 := fun i j =>
  decide ((i.1 = 0 ∧ (j.1 = 0 ∨ j.1 = 3)) ∨
    (i.1 = 1 ∧ (j.1 = 0 ∨ j.1 = 2)) ∨
    (i.1 = 2 ∧ (j.1 = 1 ∨ j.1 = 3)))

@[blueprint "def:pach-tardos-lower-bound"
  (statement := /-- A binary pattern $P$ has the Pach--Tardos lower bound if there are a constant
  $C\geq 0$ and an integer $N\geq 1$ such that, for every integer $n\geq N$,
  \[
  n\,2^{\sqrt{\log_2 n}-C\log_2(\log_2 n)}
    \leq \operatorname{Ex}(P,n).
  \]
  This is the quantified meaning of
  $\operatorname{Ex}(P,n)\geq n2^{\sqrt{\log n}-O(\log\log n)}$, with every logarithm in base
  two. -/)
  (title := /-- The Pach--Tardos asymptotic lower bound -/)
  (latexEnv := "definition")]
def pach_tardos_lower_bound {r c : ℕ} (P : binary_matrix r c) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    (n : ℝ) * Real.rpow 2
        (Real.sqrt (Real.logb 2 (n : ℝ)) -
          C * Real.logb 2 (Real.logb 2 (n : ℝ))) ≤
      (extremal_function P n : ℝ)

@[blueprint "def:covering-pattern"
  (statement := /-- Let $P$ be an $r\times(c+2)$ binary pattern.  We call $P$ a covering
  pattern if there are a distinguished row $k^*$, a set $J$ of other rows, and, for each
  $l\in J$, columns $a_l<b_l$ such that the following conditions hold:
  \begin{enumerate}
  \item row $k^*$ contains a $1$ in each of columns $0$ and $c+1$;
  \item $k^*\notin J$, at most one member of $J$ precedes $k^*$, and every row $l\in J$
  has a $1$ in each of columns $a_l$ and $b_l$ and has a common $1$-entry with row $k^*$;
  \item for every $q\in\{0,\ldots,c\}$, some $l\in J$ satisfies
  $a_l\leq q<b_l$.
  \end{enumerate}
  Thus the intervals $[a_l,b_l]$ cover every gap between consecutive columns from $0$ through
  $c+1$. -/)
  (title := /-- Covering binary patterns -/)
  (latexEnv := "definition")]
def covering_pattern {r c : ℕ} (P : binary_matrix r (c + 2)) : Prop :=
  ∃ k : Fin r, ∃ J : Finset (Fin r),
    ∃ left right : Fin r → Fin (c + 2),
      P k 0 = true ∧
      P k (Fin.last (c + 1)) = true ∧
      k ∉ J ∧
      (J.filter (fun l => l < k)).card ≤ 1 ∧
      (∀ l ∈ J,
        left l < right l ∧
        P l (left l) = true ∧
        P l (right l) = true ∧
        ∃ j : Fin (c + 2), P k j = true ∧ P l j = true) ∧
      ∀ q : Fin (c + 1), ∃ l ∈ J,
        (left l).val ≤ q.val ∧ q.val < (right l).val

@[blueprint "def:covering-construction"
  (statement := /-- For an integer $b$, put $m_b=2b\,2^{b}$ and let
  $S_b=\{2^{b}+1,\ldots,2^{b+1}\}$, encoded through the shift $s\mapsto 2^{b}+1+s$ for
  $s\in\{0,\ldots,2^{b}-1\}$.  The covering construction $A_b$ is the binary matrix whose rows
  are indexed by pairs $(s,r)$ with $s\in\{0,\ldots,2^{b}-1\}$ and $r\in[m_b]^{b}$, whose columns
  are indexed by pairs $(d,i)$ with $d\in[m_b]^{b}$ and $i\in\{0,1\}^{b}$, and whose entry at the
  row $(s,r)$ and column $(d,i)$ equals $1$ exactly when
  \[
    r(t)=d(t)+(2^{b}+1+s)\,i(t)\qquad\text{for every coordinate }t\in\{0,\ldots,b-1\}.
  \]
  Both index sets $\{0,\ldots,2^{b}-1\}\times[m_b]^{b}$ and $[m_b]^{b}\times\{0,1\}^{b}$ have
  cardinality $n_b=2^{b}m_b^{\,b}$, and each product is ordered lexicographically. -/)
  (title := /-- The covering construction $A_b$ -/)
  (latexEnv := "definition")]
def covering_construction (b : ℕ) :
    binary_matrix (2 ^ b * (2 * b * 2 ^ b) ^ b) ((2 * b * 2 ^ b) ^ b * 2 ^ b) :=
  fun row col =>
    let s := (finProdFinEquiv.symm row).1
    let r := finFunctionFinEquiv.symm (finProdFinEquiv.symm row).2
    let d := finFunctionFinEquiv.symm (finProdFinEquiv.symm col).1
    let i := finFunctionFinEquiv.symm (finProdFinEquiv.symm col).2
    decide (∀ t : Fin b, (r t).val = (d t).val + (2 ^ b + 1 + s.val) * (i t).val)

@[blueprint "lem:covering-construction-simple-properties"
  (statement := /-- Fix an integer $b\ge 0$, an index $s\in\{0,\ldots,2^{b}-1\}$, tuples
  $r,d\in[m_b]^{b}$ with $m_b=2b\,2^{b}$, and a tuple $i\in\{0,1\}^{b}$.  Let $(s,r)$ and $(d,i)$
  denote the corresponding lexicographic row and column indices of the covering construction of
  \cref{def:covering-construction}.  Then the entry of that construction at row $(s,r)$ and
  column $(d,i)$ equals $1$ if and only if $r(t)=d(t)+(2^{b}+1+s)\,i(t)$ for every coordinate
  $t\in\{0,\ldots,b-1\}$. -/)
  (proof := /-- This is immediate from the defining incidence of
  \cref{def:covering-construction}.  The lexicographic encodings that identify a row with the
  pair $(s,r)$ and a column with the pair $(d,i)$ are bijections onto the row and column index
  sets, so evaluating the construction at these encoded indices returns exactly the Boolean value
  $\big[\,\forall t,\ r(t)=d(t)+(2^{b}+1+s)\,i(t)\,\big]$ that defines the entry. -/)
  (title := /-- Incidence characterization of the covering construction -/)
  (latexEnv := "lemma")]
lemma covering_construction_simple_properties (b : ℕ)
    (s : Fin (2 ^ b)) (r d : Fin b → Fin (2 * b * 2 ^ b)) (i : Fin b → Fin 2) :
    covering_construction b
        (finProdFinEquiv (s, finFunctionFinEquiv r))
        (finProdFinEquiv (finFunctionFinEquiv d, finFunctionFinEquiv i)) = true ↔
      ∀ t : Fin b, (r t).val = (d t).val + (2 ^ b + 1 + s.val) * (i t).val := by
  simp only [covering_construction, Equiv.symm_apply_apply, decide_eq_true_eq]

@[blueprint "lem:covering-density-exp-bound"
  (statement := /-- For every integer $b\ge 2$ one has $b^{b}\le 8\,(b-1)^{b}$, as an inequality
  of real numbers. -/)
  (proof := /-- Write $b/(b-1)=1+1/(b-1)$.  The exponential bound $y+1\le e^{y}$ with
  $y=1/(b-1)$ gives $b/(b-1)\le e^{1/(b-1)}$, hence
  $\big(b/(b-1)\big)^{b}\le e^{b/(b-1)}$.  Since $b\ge 2$ we have
  $b/(b-1)=1+1/(b-1)\le 2$, so $e^{b/(b-1)}\le e^{2}<8$ because $e<2.72$.  Multiplying the
  resulting inequality $\big(b/(b-1)\big)^{b}\le 8$ by $(b-1)^{b}>0$ yields
  $b^{b}\le 8\,(b-1)^{b}$. -/)
  (title := /-- An exponential bound for the ratio $b/(b-1)$ -/)
  (latexEnv := "lemma")]
lemma covering_density_exp_bound (b : ℕ) (hb : 2 ≤ b) :
    (b : ℝ) ^ b ≤ 8 * ((b : ℝ) - 1) ^ b := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbm1pos : (0 : ℝ) < (b : ℝ) - 1 := by linarith
  have hne : (b : ℝ) - 1 ≠ 0 := ne_of_gt hbm1pos
  have hthis : 1 / ((b : ℝ) - 1) + 1 = (b : ℝ) / ((b : ℝ) - 1) := by
    rw [div_add_one hne]; congr 1; ring
  have hle_exp : (b : ℝ) / ((b : ℝ) - 1) ≤ Real.exp (1 / ((b : ℝ) - 1)) := by
    rw [← hthis]; exact Real.add_one_le_exp _
  have hratio_nn : (0 : ℝ) ≤ (b : ℝ) / ((b : ℝ) - 1) :=
    div_nonneg (by positivity) hbm1pos.le
  have hpow : ((b : ℝ) / ((b : ℝ) - 1)) ^ b
      ≤ Real.exp (1 / ((b : ℝ) - 1)) ^ b :=
    pow_le_pow_left₀ hratio_nn hle_exp b
  have hbx : (b : ℝ) * (1 / ((b : ℝ) - 1)) ≤ 2 := by
    rw [mul_one_div, div_le_iff₀ hbm1pos]; linarith
  have hexp : Real.exp (1 / ((b : ℝ) - 1)) ^ b ≤ 8 := by
    rw [← Real.exp_nat_mul]
    have h2le : Real.exp ((b : ℝ) * (1 / ((b : ℝ) - 1))) ≤ Real.exp 2 :=
      Real.exp_le_exp.mpr hbx
    have he2 : Real.exp 2 ≤ 8 := by
      have hb1 : Real.exp 1 ≤ 2.75 := by
        have h := Real.exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num)
          (n := 2) (by norm_num)
        norm_num [Finset.sum_range_succ, Nat.factorial] at h
        linarith
      have h1 : Real.exp 2 = Real.exp 1 ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [h1]; nlinarith [hb1, Real.exp_pos 1]
    linarith
  have hkey : ((b : ℝ) / ((b : ℝ) - 1)) ^ b ≤ 8 := le_trans hpow hexp
  have hcancel : (b : ℝ) / ((b : ℝ) - 1) * ((b : ℝ) - 1) = (b : ℝ) := by
    field_simp
  have hbb : (b : ℝ) ^ b = ((b : ℝ) / ((b : ℝ) - 1)) ^ b * ((b : ℝ) - 1) ^ b := by
    rw [← mul_pow, hcancel]
  rw [hbb]
  exact mul_le_mul_of_nonneg_right hkey (pow_nonneg hbm1pos.le b)

@[blueprint "lem:covering-density-weight-count"
  (statement := /-- For every integer $b\ge 2$, the weight of the covering construction of
  \cref{def:covering-construction} satisfies
  $\lVert A_b\rVert_1\ge 2^{b}\,2^{b}\,\big(2(b-1)2^{b}\big)^{b}$. -/)
  (proof := /-- By \cref{lem:covering-construction-simple-properties}, the entry of $A_b$ at the
  row encoded by $(s,r)$ and the column encoded by $(d,i)$ is a $1$ exactly when
  $r(t)=d(t)+(2^{b}+1+s)\,i(t)$ for every coordinate $t$.  Restrict attention to the triples
  $(s,i,d')$ with $s\in\{0,\ldots,2^{b}-1\}$, $i\in\{0,1\}^{b}$ and $d'(t)<2(b-1)2^{b}$ for every
  $t$.  For such a triple set $d(t)=d'(t)$ and $r(t)=d'(t)+(2^{b}+1+s)\,i(t)$; since
  $2^{b}+1+s\le 2^{b+1}$ and $i(t)\le 1$ we get $r(t)<2(b-1)2^{b}+2\cdot 2^{b}=2b\,2^{b}$, so the
  tuple $r$ lies in $[m_b]^{b}$ and the corresponding entry is a $1$.  The assignment
  $(s,i,d')\mapsto\big((s,r),(d,i)\big)$ is injective, because the lexicographic encodings and the
  inclusion $d'\mapsto d$ are injective.  Hence the number of these $1$-entries, which is
  $2^{b}\cdot 2^{b}\cdot\big(2(b-1)2^{b}\big)^{b}$, is a lower bound for $\lVert A_b\rVert_1$. -/)
  (title := /-- A combinatorial lower bound for the weight -/)
  (latexEnv := "lemma")]
lemma covering_density_weight_count (b : ℕ) (hb : 2 ≤ b) :
    2 ^ b * 2 ^ b * (2 * (b - 1) * 2 ^ b) ^ b
      ≤ matrix_weight (covering_construction b) := by
  classical
  have hkm : 2 * (b - 1) * 2 ^ b ≤ 2 * b * 2 ^ b := by
    have : b - 1 ≤ b := Nat.sub_le b 1
    gcongr
  have hmsplit : 2 * b * 2 ^ b = 2 * (b - 1) * 2 ^ b + 2 * 2 ^ b := by
    have h2b : 2 * b = 2 * (b - 1) + 2 := by omega
    calc 2 * b * 2 ^ b = (2 * (b - 1) + 2) * 2 ^ b := by rw [h2b]
      _ = 2 * (b - 1) * 2 ^ b + 2 * 2 ^ b := by ring
  have hval : ∀ (s : Fin (2 ^ b)) (i : Fin b → Fin 2)
      (d' : Fin b → Fin (2 * (b - 1) * 2 ^ b)) (t : Fin b),
      (d' t).val + (2 ^ b + 1 + s.val) * (i t).val < 2 * b * 2 ^ b := by
    intro s i d' t
    have hs := s.isLt
    have hd := (d' t).isLt
    have hi := (i t).isLt
    have hi2 : (i t).val = 0 ∨ (i t).val = 1 := by omega
    rw [hmsplit]
    rcases hi2 with h0 | h1
    · rw [h0]; omega
    · rw [h1]; omega
  have hcard : (Finset.univ :
      Finset (Fin (2 ^ b) × (Fin b → Fin 2) × (Fin b → Fin (2 * (b - 1) * 2 ^ b)))).card
      = 2 ^ b * 2 ^ b * (2 * (b - 1) * 2 ^ b) ^ b := by
    rw [Finset.card_univ]
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    ring
  have hle : (Finset.univ :
      Finset (Fin (2 ^ b) × (Fin b → Fin 2) × (Fin b → Fin (2 * (b - 1) * 2 ^ b)))).card
      ≤ matrix_weight (covering_construction b) := by
    show (Finset.univ :
        Finset (Fin (2 ^ b) × (Fin b → Fin 2) × (Fin b → Fin (2 * (b - 1) * 2 ^ b)))).card
        ≤ (Finset.univ.filter
            (fun p : Fin (2 ^ b * (2 * b * 2 ^ b) ^ b) × Fin ((2 * b * 2 ^ b) ^ b * 2 ^ b) =>
              covering_construction b p.1 p.2 = true)).card
    apply Finset.card_le_card_of_injOn
      (fun p : Fin (2 ^ b) × (Fin b → Fin 2) × (Fin b → Fin (2 * (b - 1) * 2 ^ b)) =>
        (finProdFinEquiv (p.1, finFunctionFinEquiv (fun t =>
            (⟨(p.2.2 t).val + (2 ^ b + 1 + p.1.val) * (p.2.1 t).val,
              hval p.1 p.2.1 p.2.2 t⟩ : Fin (2 * b * 2 ^ b)))),
         finProdFinEquiv (finFunctionFinEquiv (fun t => Fin.castLE hkm (p.2.2 t)),
            finFunctionFinEquiv p.2.1)))
    · intro p _
      obtain ⟨s, i, d'⟩ := p
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [covering_construction_simple_properties]
      intro t
      rfl
    · intro p _ q _ hpq
      obtain ⟨s, i, d'⟩ := p
      obtain ⟨s2, i2, d2'⟩ := q
      simp only [Prod.mk.injEq, Equiv.apply_eq_iff_eq] at hpq
      obtain ⟨⟨hs, _⟩, hdd, hi⟩ := hpq
      have hd' : d' = d2' := by
        funext t
        exact Fin.castLE_injective hkm (congrFun hdd t)
      subst hs; subst hi; subst hd'; rfl
  calc 2 ^ b * 2 ^ b * (2 * (b - 1) * 2 ^ b) ^ b
      = (Finset.univ :
          Finset (Fin (2 ^ b) × (Fin b → Fin 2)
            × (Fin b → Fin (2 * (b - 1) * 2 ^ b)))).card := hcard.symm
    _ ≤ matrix_weight (covering_construction b) := hle

@[blueprint "lem:covering-construction-density"
  (statement := /-- There is an absolute constant $c_0>0$ such that, for every integer
  $b\ge 2$, the weight of the covering construction of \cref{def:covering-construction}
  satisfies $\lVert A_b\rVert_1\ge c_0\,n_b\,2^{b}$, where $m_b=2b\,2^{b}$ and
  $n_b=2^{b}m_b^{\,b}$. -/)
  (proof := /-- Take the absolute constant $c_0=1/8$.  Fix an integer $b\ge 2$.  By
  \cref{lem:covering-density-weight-count} the weight of the covering construction is at least
  $2^{b}\,2^{b}\big(2(b-1)2^{b}\big)^{b}$, obtained by counting the $1$-entries produced by the
  triples $(s,i,d')$ with $d'(t)<2(b-1)2^{b}$.  It therefore suffices to check the real
  inequality
  $\tfrac18\,\big(2^{b}(2b\,2^{b})^{b}\big)2^{b}\le 2^{b}\,2^{b}\big(2(b-1)2^{b}\big)^{b}$.
  Cancelling the common positive factor $2^{b}\,2^{b}\,(2\cdot 2^{b})^{b}$ reduces this to
  $\tfrac18\,b^{b}\le(b-1)^{b}$, that is $b^{b}\le 8\,(b-1)^{b}$, which is exactly
  \cref{lem:covering-density-exp-bound}.  Hence $c_0=1/8$ satisfies the claim. -/)
  (title := /-- Weight of the covering construction -/)
  (latexEnv := "lemma")]
lemma covering_construction_density :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ b : ℕ, 2 ≤ b →
      c₀ * ((2 ^ b * (2 * b * 2 ^ b) ^ b : ℕ) : ℝ) * (2 ^ b : ℝ)
        ≤ (matrix_weight (covering_construction b) : ℝ) := by
  refine ⟨1 / 8, by norm_num, fun b hb => ?_⟩
  have hb1 : (1 : ℕ) ≤ b := by omega
  have hcount := covering_density_weight_count b hb
  have hexp := covering_density_exp_bound b hb
  have hcast : ((2 ^ b * 2 ^ b * (2 * (b - 1) * 2 ^ b) ^ b : ℕ) : ℝ)
      ≤ (matrix_weight (covering_construction b) : ℝ) := by exact_mod_cast hcount
  refine le_trans ?_ hcast
  have hbsub : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by rw [Nat.cast_sub hb1]; norm_num
  push_cast [hbsub]
  have factor_pos : (0 : ℝ) ≤ (2 : ℝ) ^ b * 2 ^ b * (2 * 2 ^ b) ^ b := by positivity
  have eLHS : (1 : ℝ) / 8 * ((2 : ℝ) ^ b * (2 * (b : ℝ) * 2 ^ b) ^ b) * 2 ^ b
      = ((2 : ℝ) ^ b * 2 ^ b * (2 * 2 ^ b) ^ b) * (1 / 8 * (b : ℝ) ^ b) := by
    rw [show (2 * (b : ℝ) * 2 ^ b) = (2 * 2 ^ b) * (b : ℝ) from by ring, mul_pow]; ring
  have eRHS : (2 : ℝ) ^ b * 2 ^ b * (2 * ((b : ℝ) - 1) * 2 ^ b) ^ b
      = ((2 : ℝ) ^ b * 2 ^ b * (2 * 2 ^ b) ^ b) * ((b : ℝ) - 1) ^ b := by
    rw [show (2 * ((b : ℝ) - 1) * 2 ^ b) = (2 * 2 ^ b) * ((b : ℝ) - 1) from by ring, mul_pow]; ring
  rw [eLHS, eRHS]
  exact mul_le_mul_of_nonneg_left (by linarith [hexp]) factor_pos

@[blueprint "lem:cov-free-high-eq"
  (statement := /-- Let $M$, $B$ and $s$ be natural numbers with $s\le B$, and let $x$ and $y$ be
  natural numbers with $x<M^{B}$ and $y<M^{B}$.  Assume that the base-$M$ digits of $x$ and $y$
  agree in every position $t$ with $s\le t<B$, that is,
  $\lfloor x/M^{t}\rfloor \bmod M=\lfloor y/M^{t}\rfloor \bmod M$.  Then
  $\lfloor x/M^{s}\rfloor=\lfloor y/M^{s}\rfloor$. -/)
  (proof := /-- We prove by induction on $k$ that
  $\lfloor x/M^{B-k}\rfloor=\lfloor y/M^{B-k}\rfloor$ for every $k\le B-s$, and then specialise
  to $k=B-s$, which gives $B-k=s$ because $s\le B$.

  For $k=0$ the claim reads $\lfloor x/M^{B}\rfloor=\lfloor y/M^{B}\rfloor$, and both sides
  vanish since $x<M^{B}$ and $y<M^{B}$.

  Assume the claim for $k$ and let $k+1\le B-s$.  Write $t=B-(k+1)$, so that $s\le t$, $t<B$ and
  $t+1=B-k$.  For any natural number $z$ the division identity
  $\lfloor z/M^{t}\rfloor=M\lfloor z/M^{t}/M\rfloor+\lfloor z/M^{t}\rfloor\bmod M$ together with
  $\lfloor z/M^{t}\rfloor/M=\lfloor z/M^{t+1}\rfloor$ yields
  $\lfloor z/M^{t}\rfloor=M\lfloor z/M^{B-k}\rfloor+\lfloor z/M^{t}\rfloor\bmod M$.  Applying this
  to $z=x$ and to $z=y$, the first summands agree by the induction hypothesis and the second
  summands agree by the digit hypothesis at position $t$.  Hence
  $\lfloor x/M^{t}\rfloor=\lfloor y/M^{t}\rfloor$, which is the claim for $k+1$. -/)
  (title := /-- Equal high digits force equal high blocks -/)
  (latexEnv := "lemma")]
lemma cov_free_high_eq (M bb s : ℕ) (hs : s ≤ bb) (x y : ℕ)
    (hx : x < M ^ bb) (hy : y < M ^ bb)
    (hdig : ∀ t, s ≤ t → t < bb → x / M ^ t % M = y / M ^ t % M) :
    x / M ^ s = y / M ^ s := by
  have main : ∀ k, k ≤ bb - s → x / M ^ (bb - k) = y / M ^ (bb - k) := by
    intro k
    induction k with
    | zero =>
        intro _
        simp only [Nat.sub_zero]
        rw [Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy]
    | succ k ih =>
        intro hk
        have ihk := ih (by omega)
        have hs'b : bb - (k + 1) < bb := by omega
        have hs'ge : s ≤ bb - (k + 1) := by omega
        have hstep : bb - (k + 1) + 1 = bb - k := by omega
        have hxsplit : ∀ z : ℕ,
            z / M ^ (bb - (k + 1)) = M * (z / M ^ (bb - k)) + z / M ^ (bb - (k + 1)) % M := by
          intro z
          have h1 : z / M ^ (bb - (k + 1)) / M = z / M ^ (bb - k) := by
            rw [Nat.div_div_eq_div_mul, ← pow_succ, hstep]
          have h2 := Nat.div_add_mod (z / M ^ (bb - (k + 1))) M
          rw [h1] at h2
          omega
        have hdigs := hdig (bb - (k + 1)) hs'ge hs'b
        rw [hxsplit x, hxsplit y, ihk, hdigs]
  have hfin := main (bb - s) (le_refl _)
  rwa [Nat.sub_sub_self hs] at hfin

@[blueprint "lem:cov-free-block-digit-mono"
  (statement := /-- Let $M$, $u$, $x$ and $y$ be natural numbers with $x\le y$ and with equal
  high blocks $\lfloor y/M^{u+1}\rfloor=\lfloor x/M^{u+1}\rfloor$.  Then the base-$M$ digits of
  $x$ and $y$ in position $u$ satisfy
  $\lfloor x/M^{u}\rfloor \bmod M\leq \lfloor y/M^{u}\rfloor \bmod M$. -/)
  (proof := /-- Since $x\le y$, monotonicity of division gives
  $\lfloor x/M^{u}\rfloor\le\lfloor y/M^{u}\rfloor$.  From $M^{u+1}=M^{u}\cdot M$ we get
  $\lfloor x/M^{u}\rfloor/M=\lfloor x/M^{u+1}\rfloor$ and
  $\lfloor y/M^{u}\rfloor/M=\lfloor y/M^{u+1}\rfloor$.  Writing the division identity
  $\lfloor z/M^{u}\rfloor=M\cdot(\lfloor z/M^{u}\rfloor/M)+\lfloor z/M^{u}\rfloor\bmod M$ for
  $z=x$ and $z=y$ and using the hypothesis
  $\lfloor y/M^{u+1}\rfloor=\lfloor x/M^{u+1}\rfloor$, both quotients by $M$ coincide.  Hence the
  two numbers $\lfloor x/M^{u}\rfloor$ and $\lfloor y/M^{u}\rfloor$ have the same multiple of $M$
  as their integral part, so the inequality
  $\lfloor x/M^{u}\rfloor\le\lfloor y/M^{u}\rfloor$ transfers to their residues modulo $M$. -/)
  (title := /-- Monotonicity of a digit inside a fixed block -/)
  (latexEnv := "lemma")]
lemma cov_free_block_digit_mono (M u x y : ℕ) (hxy : x ≤ y)
    (hblock : y / M ^ (u + 1) = x / M ^ (u + 1)) :
    x / M ^ u % M ≤ y / M ^ u % M := by
  have hdiv : x / M ^ u ≤ y / M ^ u := Nat.div_le_div_right hxy
  have hpow : M ^ (u + 1) = M ^ u * M := by rw [pow_succ]
  have hHx : x / M ^ u / M = x / M ^ (u + 1) := by
    rw [Nat.div_div_eq_div_mul, ← hpow]
  have hHy : y / M ^ u / M = y / M ^ (u + 1) := by
    rw [Nat.div_div_eq_div_mul, ← hpow]
  have hxmod := Nat.div_add_mod (x / M ^ u) M
  have hymod := Nat.div_add_mod (y / M ^ u) M
  rw [hHx] at hxmod
  rw [hHy, hblock] at hymod
  omega

@[blueprint "lem:cov-free-cover-sum"
  (statement := /-- Let $n$ be a natural number and let $g:\mathbb{N}\to\mathbb{Z}$ satisfy
  $g(q)\ge 0$ for every $q<n$.  Let $J$ be a finite index set and let $a,b:J\to\mathbb{N}$ be such
  that $b(l)\le n$ for every $l\in J$, and such that for every $q<n$ there exists $l\in J$ with
  $a(l)\le q<b(l)$.  Then
  \[
  \sum_{q=0}^{n-1}g(q)\ \leq\ \sum_{l\in J}\ \sum_{q=a(l)}^{b(l)-1}g(q).
  \] -/)
  (proof := /-- Fix $q<n$.  By the covering hypothesis there is $l_0\in J$ with
  $a(l_0)\le q<b(l_0)$.  Consider the family indexed by $l\in J$ whose $l$-th term is $g(q)$ when
  $a(l)\le q<b(l)$ and $0$ otherwise.  Every term of this family is nonnegative: the terms equal
  to $0$ are trivially nonnegative, and the remaining terms equal $g(q)\ge 0$ because $q<n$.
  Since the term at $l_0$ equals $g(q)$, bounding a single nonnegative term by the whole sum gives
  $g(q)\le\sum_{l\in J}[\,a(l)\le q<b(l)\,]\,g(q)$.

  Summing this inequality over $q\in\{0,\dots,n-1\}$ and exchanging the two finite sums yields
  \[
  \sum_{q=0}^{n-1}g(q)\ \leq\ \sum_{l\in J}\ \sum_{q=0}^{n-1}[\,a(l)\le q<b(l)\,]\,g(q).
  \]
  For each fixed $l\in J$ the inner sum equals the sum of $g$ over the set of $q<n$ satisfying
  $a(l)\le q<b(l)$, and that set is exactly $\{a(l),\dots,b(l)-1\}$: any such $q$ satisfies
  $q<b(l)\le n$, so the constraint $q<n$ is automatic.  This gives the asserted bound. -/)
  (title := /-- Covering intervals dominate a nonnegative sum -/)
  (latexEnv := "lemma")]
lemma cov_free_cover_sum {ι : Type*} (n : ℕ) (g : ℕ → ℤ) (hg : ∀ q, q < n → 0 ≤ g q)
    (J : Finset ι) (a b : ι → ℕ) (hb : ∀ l ∈ J, b l ≤ n)
    (hcov : ∀ q, q < n → ∃ l ∈ J, a l ≤ q ∧ q < b l) :
    ∑ q ∈ Finset.range n, g q ≤ ∑ l ∈ J, ∑ q ∈ Finset.Ico (a l) (b l), g q := by
  have key : ∀ q ∈ Finset.range n,
      g q ≤ ∑ l ∈ J, (if a l ≤ q ∧ q < b l then g q else 0) := by
    intro q hq
    rw [Finset.mem_range] at hq
    obtain ⟨l, hlJ, hal, hqb⟩ := hcov q hq
    have hnn : ∀ i ∈ J, (0:ℤ) ≤ (if a i ≤ q ∧ q < b i then g q else 0) := by
      intro i _
      by_cases hi : a i ≤ q ∧ q < b i
      · simp only [if_pos hi]; exact hg q hq
      · simp only [if_neg hi]; exact le_refl 0
    have hstep := Finset.single_le_sum
      (f := fun l' => if a l' ≤ q ∧ q < b l' then g q else 0) hnn hlJ
    calc g q = (if a l ≤ q ∧ q < b l then g q else 0) := by rw [if_pos ⟨hal, hqb⟩]
      _ ≤ ∑ l' ∈ J, (if a l' ≤ q ∧ q < b l' then g q else 0) := hstep
  calc ∑ q ∈ Finset.range n, g q
      ≤ ∑ q ∈ Finset.range n, ∑ l ∈ J, (if a l ≤ q ∧ q < b l then g q else 0) :=
        Finset.sum_le_sum key
    _ = ∑ l ∈ J, ∑ q ∈ Finset.range n, (if a l ≤ q ∧ q < b l then g q else 0) :=
        Finset.sum_comm
    _ = ∑ l ∈ J, ∑ q ∈ Finset.Ico (a l) (b l), g q := by
        apply Finset.sum_congr rfl
        intro l hlJ
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext q
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        constructor
        · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨lt_of_lt_of_le h2 (hb l hlJ), h1, h2⟩

@[blueprint "lem:cov-free-telescope-ico"
  (statement := /-- Let $f:\mathbb{N}\to\mathbb{Z}$ and let $m\le n$ be natural numbers.  Then
  $\sum_{q=m}^{n-1}\big(f(q+1)-f(q)\big)=f(n)-f(m)$. -/)
  (proof := /-- Because $m\le n$, the sum over $\{m,\dots,n-1\}$ equals the difference of the sums
  over $\{0,\dots,n-1\}$ and over $\{0,\dots,m-1\}$.  Each of these two sums telescopes:
  $\sum_{q=0}^{N-1}\big(f(q+1)-f(q)\big)=f(N)-f(0)$ for every natural number $N$.  Subtracting the
  two telescoped values gives $\big(f(n)-f(0)\big)-\big(f(m)-f(0)\big)=f(n)-f(m)$. -/)
  (title := /-- Telescoping over an integer interval -/)
  (latexEnv := "lemma")]
lemma cov_free_telescope_ico (f : ℕ → ℤ) (m n : ℕ) (hmn : m ≤ n) :
    ∑ q ∈ Finset.Ico m n, (f (q + 1) - f q) = f n - f m := by
  rw [Finset.sum_Ico_eq_sub _ hmn, Finset.sum_range_sub f n, Finset.sum_range_sub f m]
  ring

@[blueprint "lem:covering-construction-free"
  (statement := /-- Let $P$ be an $r\times(c+2)$ covering pattern in the sense of
  \cref{def:covering-pattern}.  Then for every integer $b\ge 2$ the covering construction $A_b$
  of \cref{def:covering-construction} is $P$-free in the sense of \cref{def:pattern-free}. -/)
  (proof := /-- Fix a distinguished row $k^*$, a covering set $J$, and endpoint columns
  $a_l<b_l$ for $l\in J$ as provided by \cref{def:covering-pattern}, and fix an integer
  $b\ge 2$.  Put $M=2b\,2^{b}$.  Suppose for contradiction that $A_b$ contains an ordered copy of
  $P$ in the sense of \cref{def:contains-pattern}, witnessed by strictly increasing maps $\rho$
  on rows and $\kappa$ on columns.  Decoding indices as in \cref{def:covering-construction}, write
  $s_l$ and $r_l$ for the two components of the row label $\rho(l)$, and $D_p$, $d_p$ and $i_p$
  for the column parameter of $\kappa(p)$, its base-$M$ digit tuple, and its bit tuple.  Put
  $w_l=2^{b}+1+s_l$, so $w_l>0$.  Every $1$-entry $P(l,p)=1$ of the pattern forces
  $r_l(t)=d_p(t)+w_l\,i_p(t)$ for every coordinate $t$, by the defining incidence of
  \cref{def:covering-construction}.  Since $\kappa$ is strictly increasing and $D_p$ is obtained
  from $\kappa(p)$ by division by $2^{b}$, the map $p\mapsto D_p$ is monotone; likewise
  $l\mapsto s_l$ is monotone in $l$.

  Let $p_0=0$ and $p_L=c+1$ denote the first and last columns, at which row $k^*$ has $1$-entries.
  The two decodings are injective, so if $d_{p_0}$ and $i_{p_0}$ agreed with $d_{p_L}$ and
  $i_{p_L}$ then $p_0=p_L$, contradicting $p_0<p_L$; and if the bit tuples agreed then the two
  incidence equations at row $k^*$ would force the digit tuples to agree as well.  Hence the set
  of coordinates $t$ with $i_{p_0}(t)\neq i_{p_L}(t)$ is nonempty; let $u$ be its largest element,
  so $i_{p_0}(t)=i_{p_L}(t)$ for every $t>u$.

  For $t>u$ the incidence equations at row $k^*$ give $d_{p_0}(t)=d_{p_L}(t)$, i.e. the base-$M$
  digits of $D_{p_0}$ and $D_{p_L}$ agree in all positions $t$ with $u+1\le t<b$.  Since
  $D_{p_0}<M^{b}$ and $D_{p_L}<M^{b}$, \cref{lem:cov-free-high-eq} yields
  $\lfloor D_{p_0}/M^{u+1}\rfloor=\lfloor D_{p_L}/M^{u+1}\rfloor$, and by monotonicity of
  $p\mapsto D_p$ the same high block $\lfloor D_p/M^{u+1}\rfloor$ occurs for every column $p$.
  Therefore \cref{lem:cov-free-block-digit-mono} applies to any pair of columns $p\le q$ and shows
  that the digit $A(p)=d_p(u)$ is a monotone function of $p$.

  Reading the incidence equations of a row $l$ at the single coordinate $u$ and subtracting them
  for two columns $p$ and $q$ carrying $1$-entries of row $l$ gives
  $A(q)-A(p)=w_l\big(i_p(u)-i_q(u)\big)$.  Applying this to $l=k^*$ with $p=p_0$ and $q=p_L$, and
  using $i_{p_0}(u)\neq i_{p_L}(u)$ together with $A(p_0)\le A(p_L)$ and $w_{k^*}>0$, we get
  $i_{p_0}(u)=1$, $i_{p_L}(u)=0$ and hence $A(p_L)-A(p_0)=w_{k^*}$.

  Extend $A$ to a monotone function on $\{0,\dots,c+1\}$ and consider the increments
  $g(q)=A(q+1)-A(q)$, which are nonnegative.  Each $l\in J$ satisfies $b_l\le c+1$, and by
  \cref{def:covering-pattern} the intervals $[a_l,b_l)$ cover $\{0,\dots,c\}$, so
  \cref{lem:cov-free-cover-sum} gives
  $\sum_{q=0}^{c}g(q)\le\sum_{l\in J}\sum_{q=a_l}^{b_l-1}g(q)$.  Both sides telescope by
  \cref{lem:cov-free-telescope-ico}, so
  $w_{k^*}=A(c+1)-A(0)\le\sum_{l\in J}\big(A(b_l)-A(a_l)\big)$.

  We now bound each summand.  Monotonicity of $A$ and $A(p_L)-A(p_0)=w_{k^*}$ give
  $A(b_l)-A(a_l)\le w_{k^*}$ for every $l\in J$.  Fix $l\in J$.  If $i_{a_l}(u)=i_{b_l}(u)$ then
  the displayed identity forces $A(b_l)-A(a_l)=0$.  Otherwise the same argument as above, using
  $A(a_l)\le A(b_l)$ and $w_l>0$, gives $i_{a_l}(u)=1$, $i_{b_l}(u)=0$ and
  $A(b_l)-A(a_l)=w_l$; combined with $A(b_l)-A(a_l)\le w_{k^*}$ this yields $s_l\le s_{k^*}$.
  Moreover $s_l\ne s_{k^*}$: if $s_l=s_{k^*}$ then $w_l=w_{k^*}$, and the common $1$-entry of
  rows $l$ and $k^*$ guaranteed by \cref{def:covering-pattern} would force $r_l=r_{k^*}$, whence
  $l=k^*$ by injectivity of the row decoding, contradicting $k^*\notin J$.  Thus $s_l<s_{k^*}$,
  so $l<k^*$ by monotonicity of $l\mapsto s_l$, and $A(b_l)-A(a_l)=w_l<w_{k^*}$.

  Consequently every $l\in J$ with $A(b_l)-A(a_l)\neq 0$ satisfies $l<k^*$, so the sum over $J$
  equals the sum over $\{l\in J: l<k^*\}$, a set of at most one element by
  \cref{def:covering-pattern}.  If that set is empty the sum is $0<w_{k^*}$; if it is a singleton
  $\{a\}$ then its unique term is either $0$ or $w_a<w_{k^*}$.  In both cases
  $\sum_{l\in J}\big(A(b_l)-A(a_l)\big)<w_{k^*}$, contradicting the lower bound obtained above.
  Hence no ordered copy of $P$ occurs, and $A_b$ is $P$-free in the sense of
  \cref{def:pattern-free}. -/)
  (title := /-- The covering construction avoids covering patterns -/)
  (latexEnv := "lemma")]
lemma covering_construction_free {r c : ℕ} (P : binary_matrix r (c + 2))
    (hP : covering_pattern P) :
    ∀ b : ℕ, 2 ≤ b → pattern_free P (covering_construction b) := by
  obtain ⟨k, J, left, right, hk0, hkL, hkJ, hcard, hJprop, hcov⟩ := hP
  intro b hb hcon
  set M := 2 * b * 2 ^ b with hMdef
  obtain ⟨ρ, hρ, κ, hκ, hone⟩ := hcon
  have hbpos : 0 < b := by omega
  have hMpos : 0 < M := by
    rw [hMdef]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) hbpos) (pow_pos (by norm_num) b)
  have hM1 : 1 ≤ M := hMpos
  set dcol : Fin (c + 2) → Fin b → ℕ :=
    fun p t => ((finFunctionFinEquiv.symm (finProdFinEquiv.symm (κ p)).1) t : ℕ) with hdcol
  set icol : Fin (c + 2) → Fin b → ℕ :=
    fun p t => ((finFunctionFinEquiv.symm (finProdFinEquiv.symm (κ p)).2) t : ℕ) with hicol
  set rrow : Fin r → Fin b → ℕ :=
    fun l t => ((finFunctionFinEquiv.symm (finProdFinEquiv.symm (ρ l)).2) t : ℕ) with hrrow
  set Dv : Fin (c + 2) → ℕ := fun p => ((finProdFinEquiv.symm (κ p)).1 : ℕ) with hDv
  set sv : Fin r → ℕ := fun l => ((finProdFinEquiv.symm (ρ l)).1 : ℕ) with hsv
  set wt : Fin r → ℕ := fun l => 2 ^ b + 1 + sv l with hwt
  have hwtpos : ∀ l, 0 < wt l := by
    intro l; rw [hwt]; positivity
  have hincid : ∀ (l : Fin r) (p : Fin (c + 2)), P l p = true → ∀ t : Fin b,
      rrow l t = dcol p t + wt l * icol p t := by
    intro l p hlp t
    have h := hone l p hlp
    simp only [covering_construction, decide_eq_true_eq] at h
    exact h t
  have hdd : ∀ (p : Fin (c + 2)) (t : Fin b), dcol p t = Dv p / M ^ (t : ℕ) % M := by
    intro p t
    show (finFunctionFinEquiv.symm (finProdFinEquiv.symm (κ p)).1 t : ℕ)
        = ((finProdFinEquiv.symm (κ p)).1 : ℕ) / M ^ (t : ℕ) % M
    rw [finFunctionFinEquiv_symm_apply_val]
  have hicol2 : ∀ (p : Fin (c + 2)) (t : Fin b), icol p t < 2 := by
    intro p t; rw [hicol]; exact (finFunctionFinEquiv.symm _ t).isLt
  have hDvlt : ∀ p : Fin (c + 2), Dv p < M ^ b := by
    intro p; rw [hDv]; exact (finProdFinEquiv.symm (κ p)).1.isLt
  have hDvval : ∀ p : Fin (c + 2), Dv p = (κ p).val / 2 ^ b := by
    intro p
    show ((finProdFinEquiv.symm (κ p)).1 : ℕ) = (κ p).val / 2 ^ b
    simp [finProdFinEquiv_symm_apply, Fin.divNat]
  have hDvmono : Monotone Dv := by
    intro p q hpq
    rw [hDvval, hDvval]
    exact Nat.div_le_div_right (hκ.monotone hpq)
  set p0 : Fin (c + 2) := 0 with hp0
  set pL : Fin (c + 2) := Fin.last (c + 1) with hpL
  have hp0le : ∀ p : Fin (c + 2), p0 ≤ p := fun p => by rw [hp0]; exact Fin.zero_le p
  have hpLge : ∀ p : Fin (c + 2), p ≤ pL := fun p => by rw [hpL]; exact Fin.le_last p
  have h0ltL : p0 < pL := by
    rw [hp0, hpL, Fin.lt_def, Fin.val_last]; simp
  have hcolinj : ∀ (p q : Fin (c + 2)),
      (∀ t, dcol p t = dcol q t) → (∀ t, icol p t = icol q t) → p = q := by
    intro p q hd hi
    have hd' : (finFunctionFinEquiv.symm (finProdFinEquiv.symm (κ p)).1)
        = (finFunctionFinEquiv.symm (finProdFinEquiv.symm (κ q)).1) := by
      funext t; exact Fin.val_injective (hd t)
    have hi' : (finFunctionFinEquiv.symm (finProdFinEquiv.symm (κ p)).2)
        = (finFunctionFinEquiv.symm (finProdFinEquiv.symm (κ q)).2) := by
      funext t; exact Fin.val_injective (hi t)
    have hd2 := finFunctionFinEquiv.symm.injective hd'
    have hi2 := finFunctionFinEquiv.symm.injective hi'
    have hpair : finProdFinEquiv.symm (κ p) = finProdFinEquiv.symm (κ q) :=
      Prod.ext hd2 hi2
    exact hκ.injective (finProdFinEquiv.symm.injective hpair)
  have hbits_ne : ∃ t : Fin b, icol p0 t ≠ icol pL t := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hdeq : ∀ t, dcol p0 t = dcol pL t := by
      intro t
      have e0 := hincid k p0 hk0 t
      have eL := hincid k pL hkL t
      have hii := hall t
      have : dcol p0 t + wt k * icol p0 t = dcol pL t + wt k * icol pL t := by
        rw [← e0, ← eL]
      rw [hii] at this
      omega
    exact absurd (hcolinj p0 pL hdeq hall) (ne_of_lt h0ltL)
  classical
  set Sdiff := (Finset.univ.filter (fun t : Fin b => icol p0 t ≠ icol pL t)) with hSdiff
  have hSne : Sdiff.Nonempty := by
    obtain ⟨t, ht⟩ := hbits_ne
    exact ⟨t, by rw [hSdiff, Finset.mem_filter]; exact ⟨Finset.mem_univ t, ht⟩⟩
  set u : Fin b := Sdiff.max' hSne with hu
  have humem : u ∈ Sdiff := Finset.max'_mem _ hSne
  have hune : icol p0 u ≠ icol pL u := by
    have := humem; rw [hSdiff, Finset.mem_filter] at this; exact this.2
  have hutop : ∀ t : Fin b, u < t → icol p0 t = icol pL t := by
    intro t htu
    by_contra hne
    have : t ∈ Sdiff := by rw [hSdiff, Finset.mem_filter]; exact ⟨Finset.mem_univ t, hne⟩
    have := Finset.le_max' _ t this
    rw [← hu] at this
    exact absurd this (not_le.mpr htu)
  have hwtval : ∀ l : Fin r, wt l = 2 ^ b + 1 + sv l := by
    intro l; rw [hwt]
  have hsvval : ∀ l : Fin r, sv l = (ρ l).val / M ^ b := by
    intro l
    show ((finProdFinEquiv.symm (ρ l)).1 : ℕ) = (ρ l).val / M ^ b
    simp [finProdFinEquiv_symm_apply, Fin.divNat, hMdef]
  have hsvmono : ∀ l m : Fin r, l ≤ m → sv l ≤ sv m := by
    intro l m hlm
    rw [hsvval, hsvval]
    exact Nat.div_le_div_right (hρ.monotone hlm)
  have hrowinj : ∀ l m : Fin r, sv l = sv m → (∀ t, rrow l t = rrow m t) → l = m := by
    intro l m hs hr
    simp only [hsv] at hs
    simp only [hrrow] at hr
    have hs' : (finProdFinEquiv.symm (ρ l)).1 = (finProdFinEquiv.symm (ρ m)).1 :=
      Fin.val_injective hs
    have hr' : (finFunctionFinEquiv.symm (finProdFinEquiv.symm (ρ l)).2)
        = (finFunctionFinEquiv.symm (finProdFinEquiv.symm (ρ m)).2) := by
      funext t; exact Fin.val_injective (hr t)
    have hr2 := finFunctionFinEquiv.symm.injective hr'
    have hpair : finProdFinEquiv.symm (ρ l) = finProdFinEquiv.symm (ρ m) := Prod.ext hs' hr2
    exact hρ.injective (finProdFinEquiv.symm.injective hpair)
  have hsvne : ∀ l ∈ J, sv l ≠ sv k := by
    intro l hlJ hsl
    obtain ⟨-, -, -, j, hkj, hlj⟩ := hJprop l hlJ
    have hwlk : wt l = wt k := by rw [hwtval, hwtval, hsl]
    have hreq : ∀ t, rrow l t = rrow k t := by
      intro t
      rw [hincid l j hlj t, hincid k j hkj t, hwlk]
    exact hkJ (hrowinj l k hsl hreq ▸ hlJ)
  have hdig_high : ∀ t : ℕ, u.val + 1 ≤ t → t < b →
      Dv p0 / M ^ t % M = Dv pL / M ^ t % M := by
    intro t ht htb
    have htlt : u.val < t := by omega
    have ht' : u < (⟨t, htb⟩ : Fin b) := by rw [Fin.lt_def]; exact htlt
    have hii := hutop ⟨t, htb⟩ ht'
    have e0 := hincid k p0 hk0 ⟨t, htb⟩
    have eL := hincid k pL hkL ⟨t, htb⟩
    have hd : dcol p0 ⟨t, htb⟩ = dcol pL ⟨t, htb⟩ := by
      rw [hii] at e0
      exact Nat.add_right_cancel (e0.symm.trans eL)
    rw [hdd p0 ⟨t, htb⟩, hdd pL ⟨t, htb⟩] at hd
    exact hd
  have hhigh0L : Dv p0 / M ^ (u.val + 1) = Dv pL / M ^ (u.val + 1) :=
    cov_free_high_eq M b (u.val + 1) u.isLt (Dv p0) (Dv pL) (hDvlt p0) (hDvlt pL) hdig_high
  have hhigh : ∀ p : Fin (c + 2), Dv p / M ^ (u.val + 1) = Dv p0 / M ^ (u.val + 1) := by
    intro p
    have h1 : Dv p0 / M ^ (u.val + 1) ≤ Dv p / M ^ (u.val + 1) :=
      Nat.div_le_div_right (hDvmono (hp0le p))
    have h2 : Dv p / M ^ (u.val + 1) ≤ Dv pL / M ^ (u.val + 1) :=
      Nat.div_le_div_right (hDvmono (hpLge p))
    omega
  have hAmono : ∀ p q : Fin (c + 2), p ≤ q → dcol p u ≤ dcol q u := by
    intro p q hpq
    rw [hdd p u, hdd q u]
    exact cov_free_block_digit_mono M u.val (Dv p) (Dv q) (hDvmono hpq)
      (by rw [hhigh p, hhigh q])
  have hkeyd : ∀ (l : Fin r) (p q : Fin (c + 2)), P l p = true → P l q = true →
      (dcol q u : ℤ) - (dcol p u : ℤ)
        = (wt l : ℤ) * ((icol p u : ℤ) - (icol q u : ℤ)) := by
    intro l p q hlp hlq
    have ep := hincid l p hlp u
    have eq' := hincid l q hlq u
    have : dcol p u + wt l * icol p u = dcol q u + wt l * icol q u := by rw [← ep, ← eq']
    have hz : ((dcol p u : ℤ) + (wt l : ℤ) * (icol p u : ℤ))
        = (dcol q u : ℤ) + (wt l : ℤ) * (icol q u : ℤ) := by exact_mod_cast this
    linarith
  have hbit0 : icol p0 u = 1 ∧ icol pL u = 0 := by
    have h0 := hicol2 p0 u
    have hL := hicol2 pL u
    by_cases h0e : icol p0 u = 0
    · exfalso
      have hLe : icol pL u = 1 := by omega
      have hkey := hkeyd k p0 pL hk0 hkL
      rw [h0e, hLe] at hkey
      have hmono := hAmono p0 pL (hp0le pL)
      have hwk : (0 : ℤ) < (wt k : ℤ) := by exact_mod_cast hwtpos k
      have : (dcol p0 u : ℤ) ≤ (dcol pL u : ℤ) := by exact_mod_cast hmono
      push_cast at hkey
      linarith
    · exact ⟨by omega, by omega⟩
  have hgapk : (dcol pL u : ℤ) - (dcol p0 u : ℤ) = (wt k : ℤ) := by
    have hkey := hkeyd k p0 pL hk0 hkL
    rw [hbit0.1, hbit0.2] at hkey
    simpa using hkey
  set col : ℕ → Fin (c + 2) := fun q => ⟨min q (c + 1), by omega⟩ with hcolf
  set fA : ℕ → ℤ := fun q => (dcol (col q) u : ℤ) with hfAf
  have hcolmono : ∀ q q' : ℕ, q ≤ q' → col q ≤ col q' := by
    intro q q' hq
    have h1 : (col q).val = min q (c + 1) := rfl
    have h2 : (col q').val = min q' (c + 1) := rfl
    rw [Fin.le_def, h1, h2]
    omega
  have hcolself : ∀ p : Fin (c + 2), col p.val = p := by
    intro p
    apply Fin.val_injective
    have h1 : (col p.val).val = min p.val (c + 1) := rfl
    have := p.isLt
    rw [h1]
    omega
  have hAcolval : ∀ p : Fin (c + 2), fA p.val = (dcol p u : ℤ) := by
    intro p
    have h1 : fA p.val = (dcol (col p.val) u : ℤ) := rfl
    rw [h1, hcolself p]
  have hf0 : fA 0 = (dcol p0 u : ℤ) := by
    have h1 : (p0 : ℕ) = 0 := by rw [hp0]; rfl
    have := hAcolval p0
    rwa [h1] at this
  have hfL : fA (c + 1) = (dcol pL u : ℤ) := by
    have h1 : (pL : ℕ) = c + 1 := by rw [hpL, Fin.val_last]
    have := hAcolval pL
    rwa [h1] at this
  have hfAmono : ∀ q q' : ℕ, q ≤ q' → fA q ≤ fA q' := by
    intro q q' hq
    have h1 : fA q = (dcol (col q) u : ℤ) := rfl
    have h2 : fA q' = (dcol (col q') u : ℤ) := rfl
    rw [h1, h2]
    exact_mod_cast hAmono (col q) (col q') (hcolmono q q' hq)
  have hgnn : ∀ q : ℕ, q < c + 1 → 0 ≤ fA (q + 1) - fA q := by
    intro q _
    have := hfAmono q (q + 1) (Nat.le_succ q)
    linarith
  have hbnd : ∀ l ∈ J, (right l).val ≤ c + 1 := by
    intro l _
    have := (right l).isLt
    omega
  have hcov' : ∀ q : ℕ, q < c + 1 → ∃ l ∈ J, (left l).val ≤ q ∧ q < (right l).val := by
    intro q hq
    obtain ⟨l, hlJ, h1, h2⟩ := hcov ⟨q, hq⟩
    exact ⟨l, hlJ, h1, h2⟩
  have hsum1 := cov_free_cover_sum (c + 1) (fun q => fA (q + 1) - fA q) hgnn J
    (fun l => (left l).val) (fun l => (right l).val) hbnd hcov'
  have htel0 : ∑ q ∈ Finset.range (c + 1), (fA (q + 1) - fA q) = fA (c + 1) - fA 0 := by
    rw [Finset.range_eq_Ico]
    exact cov_free_telescope_ico fA 0 (c + 1) (Nat.zero_le _)
  have hlrle : ∀ l ∈ J, (left l).val ≤ (right l).val := by
    intro l hlJ
    have h := (hJprop l hlJ).1
    rw [Fin.lt_def] at h
    omega
  have htelJ : ∀ l ∈ J, ∑ q ∈ Finset.Ico (left l).val (right l).val, (fA (q + 1) - fA q)
      = fA (right l).val - fA (left l).val := by
    intro l hlJ
    exact cov_free_telescope_ico fA _ _ (hlrle l hlJ)
  have hkeytot : (wt k : ℤ) ≤ ∑ l ∈ J, (fA (right l).val - fA (left l).val) := by
    calc (wt k : ℤ) = fA (c + 1) - fA 0 := by rw [hfL, hf0]; linarith [hgapk]
      _ = ∑ q ∈ Finset.range (c + 1), (fA (q + 1) - fA q) := htel0.symm
      _ ≤ ∑ l ∈ J, ∑ q ∈ Finset.Ico (left l).val (right l).val, (fA (q + 1) - fA q) := hsum1
      _ = ∑ l ∈ J, (fA (right l).val - fA (left l).val) := Finset.sum_congr rfl htelJ
  have hylub : ∀ l ∈ J, fA (right l).val - fA (left l).val ≤ (wt k : ℤ) := by
    intro l hlJ
    rw [hAcolval, hAcolval]
    have h1 : dcol p0 u ≤ dcol (left l) u := hAmono p0 (left l) (hp0le _)
    have h2 : dcol (right l) u ≤ dcol pL u := hAmono (right l) pL (hpLge _)
    have h1' : (dcol p0 u : ℤ) ≤ (dcol (left l) u : ℤ) := by exact_mod_cast h1
    have h2' : (dcol (right l) u : ℤ) ≤ (dcol pL u : ℤ) := by exact_mod_cast h2
    linarith [hgapk]
  have hdich : ∀ l ∈ J, fA (right l).val - fA (left l).val = 0 ∨
      (l < k ∧ fA (right l).val - fA (left l).val < (wt k : ℤ)) := by
    intro l hlJ
    obtain ⟨hlt, hpl, hpr, -⟩ := hJprop l hlJ
    have hkey := hkeyd l (left l) (right l) hpl hpr
    have hub := hylub l hlJ
    rw [hAcolval, hAcolval] at hub ⊢
    have hmono : dcol (left l) u ≤ dcol (right l) u := hAmono _ _ (le_of_lt hlt)
    have hmono' : (dcol (left l) u : ℤ) ≤ (dcol (right l) u : ℤ) := by exact_mod_cast hmono
    have hi1 := hicol2 (left l) u
    have hi2 := hicol2 (right l) u
    have hwl : (0 : ℤ) < (wt l : ℤ) := by exact_mod_cast hwtpos l
    by_cases hbits : icol (left l) u = icol (right l) u
    · left
      rw [hbits] at hkey
      simp only [sub_self, mul_zero] at hkey
      exact hkey
    · right
      have hb1 : icol (left l) u = 1 ∧ icol (right l) u = 0 := by
        by_cases h0 : icol (left l) u = 0
        · exfalso
          have hr1 : icol (right l) u = 1 := by omega
          rw [h0, hr1] at hkey
          push_cast at hkey
          linarith
        · exact ⟨by omega, by omega⟩
      rw [hb1.1, hb1.2] at hkey
      push_cast at hkey
      have hwlk : wt l ≤ wt k := by
        have h' : (wt l : ℤ) ≤ (wt k : ℤ) := by linarith
        exact_mod_cast h'
      have hsvlek : sv l ≤ sv k := by
        rw [hwtval, hwtval] at hwlk
        omega
      have hsvlt : sv l < sv k := lt_of_le_of_ne hsvlek (hsvne l hlJ)
      refine ⟨?_, ?_⟩
      · by_contra hnlt
        have hkl : k ≤ l := not_lt.mp hnlt
        have := hsvmono k l hkl
        omega
      · have hwlt : wt l < wt k := by rw [hwtval, hwtval]; omega
        have hwlt' : (wt l : ℤ) < (wt k : ℤ) := by exact_mod_cast hwlt
        linarith
  have hzeroout : ∀ l ∈ J, fA (right l).val - fA (left l).val ≠ 0 → l < k := by
    intro l hlJ hne
    rcases hdich l hlJ with h | h
    · exact absurd h hne
    · exact h.1
  have hsumeq : ∑ l ∈ J.filter (fun l => l < k), (fA (right l).val - fA (left l).val)
      = ∑ l ∈ J, (fA (right l).val - fA (left l).val) :=
    Finset.sum_filter_of_ne hzeroout
  have hcard' : (J.filter (fun l => l < k)).card ≤ 1 := hcard
  have hwkpos : (0 : ℤ) < (wt k : ℤ) := by exact_mod_cast hwtpos k
  have hfinal : ∑ l ∈ J, (fA (right l).val - fA (left l).val) < (wt k : ℤ) := by
    rw [← hsumeq]
    by_cases hJe : J.filter (fun l => l < k) = ∅
    · rw [hJe, Finset.sum_empty]
      exact hwkpos
    · obtain ⟨a, ha⟩ := Finset.nonempty_of_ne_empty hJe
      have hsingle : J.filter (fun l => l < k) = {a} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨ha, ?_⟩
        intro x hx
        exact Finset.card_le_one.mp hcard' x hx a ha
      have haJ : a ∈ J := (Finset.mem_filter.mp ha).1
      rw [hsingle, Finset.sum_singleton]
      rcases hdich a haJ with h | h
      · rw [h]; exact hwkpos
      · exact h.2
  linarith [hkeytot, hfinal]

@[blueprint "def:interpolation-order"
  (statement := /-- For a natural number $b$ the interpolation order is
  $n_b=2^{b}\,(2b\,2^{b})^{b}$, the common cardinality of the two index sets of the covering
  construction of \cref{def:covering-construction}. -/)
  (title := /-- The interpolation order $n_b$ -/)
  (latexEnv := "definition")]
def interpolation_order (b : ℕ) : ℕ := 2 ^ b * (2 * b * 2 ^ b) ^ b

@[blueprint "lem:interpolation-order-ge-succ"
  (statement := /-- For every natural number $b$ one has $b+1\le n_{b+1}$, where $n_b$ is the
  interpolation order of \cref{def:interpolation-order}. -/)
  (proof := /-- By \cref{def:interpolation-order} the value $n_{b+1}$ equals
  $2^{b+1}\,(2(b+1)2^{b+1})^{b+1}$.  The second factor is a positive power, hence at least $1$,
  so $n_{b+1}\ge 2^{b+1}$.  Since $b+1<2^{b+1}$ for every natural number, we conclude
  $b+1\le n_{b+1}$. -/)
  (title := /-- Diagonal growth of the interpolation order -/)
  (latexEnv := "lemma")]
lemma interpolation_order_ge_succ (b : ℕ) : b + 1 ≤ interpolation_order (b + 1) := by
  have h1 : 1 ≤ (2 * (b + 1) * 2 ^ (b + 1)) ^ (b + 1) := Nat.one_le_pow _ _ (by positivity)
  have h2 : 2 ^ (b + 1) ≤ interpolation_order (b + 1) := by
    unfold interpolation_order
    calc 2 ^ (b + 1) = 2 ^ (b + 1) * 1 := (mul_one _).symm
      _ ≤ 2 ^ (b + 1) * (2 * (b + 1) * 2 ^ (b + 1)) ^ (b + 1) := by gcongr
  have h3 : b + 1 < 2 ^ (b + 1) := Nat.lt_two_pow_self
  omega

@[blueprint "lem:interpolation-order-ge-sq"
  (statement := /-- For every natural number $b\ge 1$ one has $2^{b^{2}}\le n_{b}$, where $n_b$
  is the interpolation order of \cref{def:interpolation-order}. -/)
  (proof := /-- By \cref{def:interpolation-order} we have
  $n_{b}=2^{b}\,(2b\,2^{b})^{b}$.  Since $b\ge 1$ gives $2^{b}\le 2b\,2^{b}$, raising to the
  $b$-th power yields $2^{b^{2}}=(2^{b})^{b}\le (2b\,2^{b})^{b}$, and multiplying by the positive
  factor $2^{b}$ gives $2^{b^{2}}\le n_{b}$. -/)
  (title := /-- Lower bound for the interpolation order -/)
  (latexEnv := "lemma")]
lemma interpolation_order_ge_sq (b : ℕ) (hb : 1 ≤ b) :
    2 ^ (b * b) ≤ interpolation_order b := by
  have hb1 : 2 ^ b ≤ 2 * b * 2 ^ b := by
    have h1 : 1 ≤ 2 * b := by omega
    calc 2 ^ b = 1 * 2 ^ b := (one_mul _).symm
      _ ≤ 2 * b * 2 ^ b := by gcongr
  have h2 : (2 ^ b) ^ b ≤ (2 * b * 2 ^ b) ^ b := Nat.pow_le_pow_left hb1 b
  unfold interpolation_order
  calc 2 ^ (b * b) = (2 ^ b) ^ b := by rw [← pow_mul]
    _ ≤ (2 * b * 2 ^ b) ^ b := h2
    _ ≤ 2 ^ b * (2 * b * 2 ^ b) ^ b := Nat.le_mul_of_pos_left _ (by positivity)

@[blueprint "lem:covering-construction-interpolation"
  (statement := /-- Let $P$ be an $r\times(c+2)$ covering pattern in the sense of
  \cref{def:covering-pattern}, and suppose there is a real constant $c_0>0$ such that the
  covering constructions $A_b$ of \cref{def:covering-construction} are $P$-free
  (\cref{def:pattern-free}) and satisfy $\lVert A_b\rVert_1\ge c_0\,n_b\,2^{b}$ for every integer
  $b\ge 2$, where $n_b=2^{b}(2b\,2^{b})^{b}$.  Then $P$ satisfies the Pach--Tardos lower bound of
  \cref{def:pach-tardos-lower-bound}. -/)
  (proof := /-- We prove \cref{def:pach-tardos-lower-bound} with constant $C=1$ and threshold
  $N=\max(N_0,1)$, where $N_0$ is chosen below; fix an integer $n\ge 1024$ large enough that
  $\log_2\log_2 n\ge 6-2\log_2(c_0/2)$, which is possible because $\log_2\log_2 n\to\infty$.
  Write $n_k=2^{k}(2k\,2^{k})^{k}$ for the interpolation order of \cref{def:interpolation-order},
  and let $b$ be the greatest index $k\le n$ with $n_k\le n$.  Since $n_0=1$ and $n_2=1024\le n$
  we have $b\ge 2$, and by maximality $n_b\le n<n_{b+1}$; the second inequality holds even when
  $b+1>n$ because then $n<b+1\le n_{b+1}$ by \cref{lem:interpolation-order-ge-succ}.

  Set $L=\log_2 n$.  For every $k\ge 1$ a direct computation from
  \cref{def:interpolation-order} gives $\log_2 n_k=k^{2}+2k+k\log_2 k$.  Writing $B=b$ and
  $t=\log_2(B+1)\ge 0$, the bound $n<n_{b+1}$ yields $L<(B+1)^{2}+2(B+1)+(B+1)t$, while
  $2^{b^{2}}\le n_b\le n$ from \cref{lem:interpolation-order-ge-sq} yields $B^{2}\le L$.  In
  particular $L>0$ and $B+1\le L$, so $t\le\log_2 L$.  The upper bound on $L$ gives
  $L\le(B+2+t/2)^{2}$, hence $\sqrt{L}\le B+2+t/2$, and combining with $t\le\log_2 L$ and the
  hypothesis on $\log_2\log_2 n$ we obtain $\sqrt{L}-\log_2 L\le\log_2(c_0/2)+B$.

  Set $m=n_b$; because $n_b\ge m$ divides the ambient order at least once, $q:=\lfloor n/m\rfloor
  \ge 1$ and $n\le 2qm$.  Both index sets of \cref{def:covering-construction} have cardinality
  $m$, so $A_b$ may be viewed as an $m\times m$ matrix; let $E$ be the $n\times n$ binary matrix
  whose entry at $(i,j)$ equals $1$ exactly when $\lfloor i/m\rfloor=\lfloor j/m\rfloor<q$ and
  $A_b$ has a $1$ at $(i\bmod m,j\bmod m)$.  Mapping $(\beta,(a,d))$ with $A_b(a,d)=1$ to
  $(a+m\beta,d+m\beta)$ is injective from $q$ disjoint copies of the $1$-entries of $A_b$ into the
  $1$-entries of $E$, so $\lVert E\rVert_1\ge q\,\lVert A_b\rVert_1\ge q\,c_0\,m\,2^{b}\ge
  \tfrac12 c_0\,n\,2^{b}$, using $\lVert A_b\rVert_1\ge c_0\,m\,2^{b}$ and $n\le 2qm$.

  We claim $E$ is $P$-free (\cref{def:pattern-free}).  Suppose row and column embeddings
  $\rho,\kappa$ witnessed an ordered copy of $P$ in $E$.  Every named $1$-entry of $E$ lies in a
  block, so from $P(k^*,0)=P(k^*,c+1)=1$ the columns $\kappa 0,\dots,\kappa(c+1)$ all lie in the
  block $\beta=\lfloor\kappa 0/m\rfloor$, and each row $l\in J$ shares a $1$-column with $k^*$ by
  \cref{def:covering-pattern}, so $\rho l$ and $\rho k^*$ also lie in block $\beta$.  Restricting
  $P$ to the rows $K=\{k^*\}\cup J$ through the increasing reindexing of $K$ therefore produces an
  ordered copy, inside a single block $A_b$, of the pattern $Q$ obtained by that restriction.
  The reindexing carries the distinguished row, covering set, and endpoints of
  \cref{def:covering-pattern} to corresponding data for $Q$, so $Q$ is again a covering pattern;
  but \cref{lem:covering-construction-free} states that $A_b$ is $Q$-free for $b\ge 2$, a
  contradiction.  Hence $E$ is $P$-free, so $\lVert E\rVert_1\le\operatorname{Ex}(P,n)$.

  Combining the two displays, $\tfrac12 c_0\,n\,2^{b}\le\operatorname{Ex}(P,n)$.  Finally
  $\tfrac12 c_0\,2^{b}=2^{\log_2(c_0/2)+b}\ge 2^{\sqrt{L}-\log_2 L}$ by the exponent bound above,
  so $n\,2^{\sqrt{\log_2 n}-\log_2\log_2 n}\le\operatorname{Ex}(P,n)$, which is the bound of
  \cref{def:pach-tardos-lower-bound} with $C=1$. -/)
  (title := /-- Block-diagonal interpolation to all orders -/)
  (latexEnv := "lemma")]
lemma covering_construction_interpolation {r c : ℕ} (P : binary_matrix r (c + 2))
    (hP : covering_pattern P) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hfree : ∀ b : ℕ, 2 ≤ b → pattern_free P (covering_construction b))
    (hdense : ∀ b : ℕ, 2 ≤ b →
      c₀ * ((2 ^ b * (2 * b * 2 ^ b) ^ b : ℕ) : ℝ) * (2 ^ b : ℝ)
        ≤ (matrix_weight (covering_construction b) : ℝ)) :
    pach_tardos_lower_bound P := by
  classical
  refine ⟨1, by norm_num, ?_⟩
  have hb2 : (1:ℝ) < 2 := by norm_num
  have htend : Filter.Tendsto (fun n : ℕ => Real.logb 2 (Real.logb 2 (n:ℝ)))
      Filter.atTop Filter.atTop :=
    (Real.tendsto_logb_atTop hb2).comp
      ((Real.tendsto_logb_atTop hb2).comp tendsto_natCast_atTop_atTop)
  set thr : ℝ := 6 - 2 * Real.logb 2 (c₀ / 2) with hthr
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      (n:ℝ) * Real.rpow 2
          (Real.sqrt (Real.logb 2 (n:ℝ)) - 1 * Real.logb 2 (Real.logb 2 (n:ℝ)))
        ≤ (extremal_function P n : ℝ) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1024, fun n hn => hn⟩,
      htend.eventually_ge_atTop thr] with n hn1024 hnthr
    have hn0 : 0 < n := by omega
    have hpred0 : interpolation_order 0 ≤ n := by
      have h0 : interpolation_order 0 = 1 := by decide
      omega
    have hpred2 : interpolation_order 2 ≤ n := by
      have h0 : interpolation_order 2 = 1024 := by decide
      omega
    set b := Nat.findGreatest (fun k => interpolation_order k ≤ n) n with hb
    have hb2 : 2 ≤ b := Nat.le_findGreatest (by omega) hpred2
    have hble : interpolation_order b ≤ n :=
      Nat.findGreatest_spec (P := fun k => interpolation_order k ≤ n) (m := 0)
        (by omega) hpred0
    have hblt : n < interpolation_order (b + 1) := by
      rcases Nat.lt_or_ge n (b + 1) with h | h
      · have hgs : b + 1 ≤ interpolation_order (b + 1) := interpolation_order_ge_succ b
        omega
      · have hg := Nat.findGreatest_is_greatest
          (P := fun k => interpolation_order k ≤ n) (n := n) (k := b + 1)
          (by rw [← hb]; omega) h
        omega
    have hnR : (0:ℝ) < n := by exact_mod_cast hn0
    have hc2 : (0:ℝ) < c₀ / 2 := by linarith
    set L := Real.logb 2 (n:ℝ) with hLdef
    have hlogid : ∀ k : ℕ, 1 ≤ k →
        Real.logb 2 ((interpolation_order k : ℕ):ℝ)
          = (k:ℝ)^2 + 2*(k:ℝ) + (k:ℝ) * Real.logb 2 (k:ℝ) := by
      intro k hk
      have hkr : (0:ℝ) < k := by exact_mod_cast hk
      unfold interpolation_order
      push_cast
      rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
        Real.logb_pow, Real.logb_mul (by positivity) (by positivity),
        Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      ring
    have hEx : c₀ / 2 * (n:ℝ) * (2:ℝ) ^ b ≤ (extremal_function P n : ℝ) := by
      set m := 2 ^ b * (2 * b * 2 ^ b) ^ b with hm
      have hmpos : 0 < m := by rw [hm]; positivity
      have hcol : m = (2 * b * 2 ^ b) ^ b * 2 ^ b := by rw [hm]; ring
      have hmle : m ≤ n := hble
      set A := covering_construction b with hA
      set B : binary_matrix n n := fun i j =>
        (decide (i.val / m = j.val / m ∧ i.val / m < n / m)) &&
          A ⟨i.val % m, Nat.mod_lt _ hmpos⟩ ⟨j.val % m, hcol ▸ Nat.mod_lt _ hmpos⟩
        with hB
      have hBweight : (n / m) * matrix_weight A ≤ matrix_weight B := by
        classical
        have hmulq : m * (n / m) ≤ n := by
          rw [Nat.mul_comm]; exact Nat.div_mul_le_self n m
        have hq : ∀ (β : Fin (n / m)) (x : ℕ), x < m → x + m * β.val < n := by
          intro β x hx
          have hβ : β.val + 1 ≤ n / m := β.isLt
          have e1 : m * (β.val + 1) = m + m * β.val := by ring
          have h2 : m * (β.val + 1) ≤ m * (n / m) := by gcongr
          omega
        set T : Finset (Fin m × Fin ((2 * b * 2 ^ b) ^ b * 2 ^ b)) :=
          Finset.univ.filter (fun p => A p.1 p.2 = true) with hT
        set trueB : Finset (Fin n × Fin n) :=
          Finset.univ.filter (fun p => B p.1 p.2 = true) with htrueB
        set S := (Finset.univ : Finset (Fin (n / m))) ×ˢ T with hS
        set f : (Fin (n / m) × Fin m × Fin ((2 * b * 2 ^ b) ^ b * 2 ^ b)) → Fin n × Fin n :=
          fun t => (⟨t.2.1.val + m * t.1.val, hq t.1 _ t.2.1.isLt⟩,
            ⟨t.2.2.val + m * t.1.val, hq t.1 _ (lt_of_lt_of_eq t.2.2.isLt hcol.symm)⟩) with hf
        have hTcard : T.card = matrix_weight A := rfl
        have hScard : S.card = (n / m) * matrix_weight A := by
          rw [hS, Finset.card_product, Finset.card_univ, Fintype.card_fin, hTcard]
        have hweqB : matrix_weight B = trueB.card := rfl
        have hmaps : ∀ t ∈ S, f t ∈ trueB := by
          intro t ht
          rw [hS, Finset.mem_product, hT, Finset.mem_filter] at ht
          obtain ⟨-, -, hAt⟩ := ht
          rw [htrueB, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have ha : (t.2.1.val) < m := t.2.1.isLt
          have hd : (t.2.2.val) < m := lt_of_lt_of_eq t.2.2.isLt hcol.symm
          have hdivi : (t.2.1.val + m * t.1.val) / m = t.1.val := by
            rw [Nat.add_mul_div_left _ _ hmpos, Nat.div_eq_of_lt ha, zero_add]
          have hdivj : (t.2.2.val + m * t.1.val) / m = t.1.val := by
            rw [Nat.add_mul_div_left _ _ hmpos, Nat.div_eq_of_lt hd, zero_add]
          have hmodi : (t.2.1.val + m * t.1.val) % m = t.2.1.val := by
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
          have hmodj : (t.2.2.val + m * t.1.val) % m = t.2.2.val := by
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
          have hidx1 : (⟨(t.2.1.val + m * t.1.val) % m, Nat.mod_lt _ hmpos⟩ : Fin m) = t.2.1 :=
            Fin.ext hmodi
          have hidx2 : (⟨(t.2.2.val + m * t.1.val) % m,
              lt_of_lt_of_eq (Nat.mod_lt _ hmpos) hcol⟩ :
              Fin ((2 * b * 2 ^ b) ^ b * 2 ^ b)) = t.2.2 := by
            apply Fin.ext; exact hmodj
          show (decide (_ ∧ _) && A _ _) = true
          rw [hidx1, hidx2, hdivi, hdivj]
          simp only [and_self, t.1.isLt, decide_true, Bool.true_and, hAt]
        have hinj : Set.InjOn f ↑S := by
          intro t₁ _ t₂ _ hEq
          rw [hf] at hEq
          simp only [Prod.mk.injEq, Fin.mk.injEq] at hEq
          obtain ⟨h1, h2⟩ := hEq
          have ha1 : t₁.2.1.val < m := t₁.2.1.isLt
          have ha2 : t₂.2.1.val < m := t₂.2.1.isLt
          have hd1 : t₁.2.2.val < m := lt_of_lt_of_eq t₁.2.2.isLt hcol.symm
          have hd2 : t₂.2.2.val < m := lt_of_lt_of_eq t₂.2.2.isLt hcol.symm
          have hβ : t₁.1.val = t₂.1.val := by
            have := congrArg (· / m) h1
            simpa [Nat.add_mul_div_left _ _ hmpos, Nat.div_eq_of_lt ha1,
              Nat.div_eq_of_lt ha2] using this
          have haa : t₁.2.1.val = t₂.2.1.val := by
            rw [hβ] at h1; omega
          have hdd : t₁.2.2.val = t₂.2.2.val := by
            rw [hβ] at h2; omega
          have e1 : t₁.1 = t₂.1 := Fin.ext hβ
          have e2 : t₁.2.1 = t₂.2.1 := Fin.ext haa
          have e3 : t₁.2.2 = t₂.2.2 := Fin.ext hdd
          exact Prod.ext e1 (Prod.ext e2 e3)
        calc (n / m) * matrix_weight A = S.card := hScard.symm
          _ ≤ trueB.card := Finset.card_le_card_of_injOn f hmaps hinj
          _ = matrix_weight B := hweqB.symm
      have hBfree : pattern_free P B := by
        rw [pattern_free]
        rintro ⟨ρ, hρ, κ, hκ, hcopy⟩
        obtain ⟨kstar, J, left, right, hk0, hklast, hkJ, hcard1, hJprop, hcov⟩ := hP
        have hBentry : ∀ i j : Fin n, B i j = true →
            i.val / m = j.val / m ∧ i.val / m < n / m ∧
              A ⟨i.val % m, Nat.mod_lt _ hmpos⟩
                ⟨j.val % m, lt_of_lt_of_eq (Nat.mod_lt _ hmpos) hcol⟩ = true := by
          intro i j hij
          rw [hB] at hij
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hij
          exact ⟨hij.1.1, hij.1.2, hij.2⟩
        set β := (κ 0).val / m with hβ
        have hcol0 : (ρ kstar).val / m = (κ 0).val / m ∧ (ρ kstar).val / m < n / m :=
          ⟨(hBentry _ _ (hcopy kstar 0 hk0)).1, (hBentry _ _ (hcopy kstar 0 hk0)).2.1⟩
        have hcollast : (ρ kstar).val / m = (κ (Fin.last (c+1))).val / m :=
          (hBentry _ _ (hcopy kstar (Fin.last (c+1)) hklast)).1
        have hβlt : β < n / m := by rw [hβ, ← hcol0.1]; exact hcol0.2
        have hlastβ : (κ (Fin.last (c+1))).val / m = β := by
          rw [hβ, ← hcollast, hcol0.1]
        have hκmono : Monotone (fun j => (κ j).val) := by
          intro a b hab
          exact Nat.le_of_lt_succ (Nat.lt_succ_of_le (Fin.val_le_of_le (hκ.monotone hab)))
        have hcolβ : ∀ j : Fin (c+2), (κ j).val / m = β := by
          intro j
          have h1 : (κ 0).val ≤ (κ j).val := hκmono (Fin.zero_le j)
          have h2 : (κ j).val ≤ (κ (Fin.last (c+1))).val := hκmono (Fin.le_last j)
          have hd1 : β ≤ (κ j).val / m := by rw [hβ]; exact Nat.div_le_div_right h1
          have hd2 : (κ j).val / m ≤ β := by
            rw [← hlastβ]; exact Nat.div_le_div_right h2
          omega
        have hrowβ : ∀ k : Fin r, (k = kstar ∨ k ∈ J) → (ρ k).val / m = β := by
          intro k hk
          rcases hk with hk | hk
          · rw [hk, hcol0.1, hβ]
          · obtain ⟨-, -, -, jj, hkjj, hljj⟩ := hJprop k hk
            have := (hBentry _ _ (hcopy k jj hljj)).1
            rw [this, hcolβ jj]
        have hmod_lt : ∀ a d : ℕ, a / m = d / m → a < d → a % m < d % m := by
          intro a d hq had
          have ea := Nat.div_add_mod a m
          have eb := Nat.div_add_mod d m
          rw [hq] at ea
          omega
        set K : Finset (Fin r) := insert kstar J with hK
        set e := K.orderEmbOfFin (rfl : K.card = K.card) with he
        have hemem : ∀ i, e i ∈ K := fun i => K.orderEmbOfFin_mem rfl i
        have herange : ∀ k, k ∈ K → ∃ i, e i = k := by
          intro k hk
          have : k ∈ Set.range (e : Fin K.card → Fin r) := by
            rw [he, Finset.range_orderEmbOfFin]; exact hk
          exact this
        have heSM : StrictMono (e : Fin K.card → Fin r) := (K.orderEmbOfFin rfl).strictMono
        have hemem2 : ∀ i, e i = kstar ∨ e i ∈ J := by
          intro i; exact Finset.mem_insert.mp (hemem i)
        obtain ⟨kstar', hkstar'⟩ : ∃ i, e i = kstar :=
          herange kstar (by rw [hK]; exact Finset.mem_insert_self _ _)
        set Q : binary_matrix K.card (c + 2) := fun i j => P (e i) j with hQ
        have hrowβe : ∀ i, (ρ (e i)).val / m = β := fun i => hrowβ (e i) (hemem2 i)
        have hQcontains : contains_pattern Q (covering_construction b) := by
          refine ⟨fun i => ⟨(ρ (e i)).val % m, Nat.mod_lt _ hmpos⟩, ?_,
            fun j => ⟨(κ j).val % m, lt_of_lt_of_eq (Nat.mod_lt _ hmpos) hcol⟩, ?_, ?_⟩
          · intro i₁ i₂ hi
            have hlt : e i₁ < e i₂ := heSM hi
            have hρ' : (ρ (e i₁)).val < (ρ (e i₂)).val := hρ hlt
            exact hmod_lt _ _ (by rw [hrowβe, hrowβe]) hρ'
          · intro j₁ j₂ hj
            have hκ' : (κ j₁).val < (κ j₂).val := hκ hj
            exact hmod_lt _ _ (by rw [hcolβ, hcolβ]) hκ'
          · intro i j hij
            have hPij : P (e i) j = true := hij
            have := (hBentry _ _ (hcopy (e i) j hPij)).2.2
            rw [← hA]; exact this
        have hQcov : covering_pattern Q := by
          refine ⟨kstar', Finset.univ.filter (fun i => e i ∈ J),
            fun i => left (e i), fun i => right (e i), ?_, ?_, ?_, ?_, ?_, ?_⟩
          · show P (e kstar') 0 = true; rw [hkstar']; exact hk0
          · show P (e kstar') (Fin.last (c + 1)) = true; rw [hkstar']; exact hklast
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hkstar']; exact hkJ
          · refine le_trans (Finset.card_le_card_of_injOn (fun i => e i) ?_ ?_) hcard1
            · intro i hi
              rw [Finset.mem_coe, Finset.mem_filter] at hi
              obtain ⟨hiJ, hilt⟩ := hi
              have hi2 : e i ∈ J := (Finset.mem_filter.mp hiJ).2
              rw [Finset.mem_coe, Finset.mem_filter]
              exact ⟨hi2, by rw [← hkstar']; exact heSM hilt⟩
            · intro a _ bb _ hab; exact e.injective hab
          · intro l hl
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
            obtain ⟨hlr, hleft, hright, jj, hkj, hlj⟩ := hJprop (e l) hl
            refine ⟨hlr, hleft, hright, jj, ?_, hlj⟩
            show P (e kstar') jj = true; rw [hkstar']; exact hkj
          · intro q
            obtain ⟨l, hlJ, hql, hqr⟩ := hcov q
            obtain ⟨i, hei⟩ := herange l (by rw [hK]; exact Finset.mem_insert_of_mem hlJ)
            refine ⟨i, ?_, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [hei]; exact hlJ
            · show (left (e i)).val ≤ q.val; rw [hei]; exact hql
            · show q.val < (right (e i)).val; rw [hei]; exact hqr
        exact covering_construction_free Q hQcov b hb2 hQcontains
      have hle_sup : matrix_weight B ≤ extremal_function P n := by
        classical
        exact Finset.le_sup (by simp [hBfree])
      have hq1 : 1 ≤ n / m := (Nat.one_le_div_iff hmpos).mpr hmle
      have hqm : n ≤ 2 * (n / m * m) := by
        have hdm : n / m * m + n % m = n := Nat.div_add_mod' n m
        have hmod : n % m < m := Nat.mod_lt _ hmpos
        have hmm : m ≤ n / m * m := Nat.le_mul_of_pos_left m (by omega)
        omega
      have hdenseb := hdense b hb2
      have hAweight : c₀ * (m:ℝ) * (2:ℝ) ^ b ≤ (matrix_weight A : ℝ) := by
        have : ((2 ^ b * (2 * b * 2 ^ b) ^ b : ℕ):ℝ) = (m:ℝ) := by rw [hm]
        rw [hA]; rw [← this]; exact hdenseb
      have hqmR : (n:ℝ) / 2 ≤ ((n / m : ℕ):ℝ) * (m:ℝ) := by
        have hcast : (n:ℝ) ≤ 2 * (((n / m : ℕ):ℝ) * (m:ℝ)) := by exact_mod_cast hqm
        linarith
      have h2bpos : (0:ℝ) < (2:ℝ)^b := by positivity
      have hcpos : (0:ℝ) ≤ c₀ * (2:ℝ) ^ b := by positivity
      have hchain : c₀ / 2 * (n:ℝ) * (2:ℝ) ^ b ≤ ((n / m : ℕ):ℝ) * (matrix_weight A : ℝ) := by
        have h1 : c₀ / 2 * (n:ℝ) * (2:ℝ) ^ b
            ≤ ((n / m : ℕ):ℝ) * (c₀ * (m:ℝ) * (2:ℝ) ^ b) := by
          have := mul_le_mul_of_nonneg_left hqmR hcpos
          nlinarith [this]
        have h2 : ((n / m : ℕ):ℝ) * (c₀ * (m:ℝ) * (2:ℝ) ^ b)
            ≤ ((n / m : ℕ):ℝ) * (matrix_weight A : ℝ) := by
          apply mul_le_mul_of_nonneg_left hAweight (by positivity)
        linarith
      have hweightR : ((n / m : ℕ):ℝ) * (matrix_weight A : ℝ) ≤ (matrix_weight B : ℝ) := by
        exact_mod_cast hBweight
      have hsupR : (matrix_weight B : ℝ) ≤ (extremal_function P n : ℝ) := by
        exact_mod_cast hle_sup
      linarith
    have hkey : Real.sqrt L - Real.logb 2 L ≤ Real.logb 2 (c₀ / 2) + (b:ℝ) := by
      have hBb : (2:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb2
      set B := (b:ℝ) with hBdef
      set t := Real.logb 2 (B + 1) with htdef
      have ht0 : 0 ≤ t := Real.logb_nonneg (by norm_num) (by linarith)
      have hLub : L < (B+1)^2 + 2*(B+1) + (B+1) * t := by
        have h1 : L < Real.logb 2 ((interpolation_order (b+1) : ℕ):ℝ) :=
          Real.logb_lt_logb (by norm_num) hnR (by exact_mod_cast hblt)
        rw [hlogid (b+1) (by omega)] at h1
        push_cast at h1
        convert h1 using 3 <;> push_cast <;> ring
      have hLbb : (B*B) ≤ L := by
        have h23 : (2^(b*b) : ℕ) ≤ n := le_trans (interpolation_order_ge_sq b (by omega)) hble
        have h4 : Real.logb 2 ((2^(b*b) : ℕ):ℝ) ≤ L := by
          have : ((2^(b*b) : ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast h23
          rw [hLdef]; gcongr
        have h5 : Real.logb 2 ((2^(b*b) : ℕ):ℝ) = B * B := by
          push_cast
          rw [show ((2:ℝ)^(b*b)) = (2:ℝ)^(b*b) from rfl, Real.logb_pow,
            Real.logb_self_eq_one (by norm_num)]
          push_cast; ring
        rw [h5] at h4; exact h4
      have hLpos : 0 < L := lt_of_lt_of_le (by nlinarith) hLbb
      have hBL : B + 1 ≤ L := by nlinarith
      have htlog : t ≤ Real.logb 2 L := by rw [htdef]; gcongr
      have hsqle : L ≤ (B + 2 + t/2)^2 := by nlinarith [sq_nonneg (1 + t/2)]
      have hsqrt : Real.sqrt L ≤ B + 2 + t/2 := by
        rw [show B + 2 + t/2 = Real.sqrt ((B + 2 + t/2)^2) from
          (Real.sqrt_sq (by linarith)).symm]
        exact Real.sqrt_le_sqrt hsqle
      linarith [hnthr]
    have hrpow_le :
        Real.rpow 2 (Real.sqrt L - 1 * Real.logb 2 L) ≤ c₀ / 2 * (2:ℝ) ^ b := by
      have e1 : c₀ / 2 * (2:ℝ) ^ b = Real.rpow 2 (Real.logb 2 (c₀ / 2) + (b:ℝ)) := by
        rw [show Real.rpow 2 (Real.logb 2 (c₀ / 2) + (b:ℝ))
              = (2:ℝ) ^ (Real.logb 2 (c₀ / 2) + (b:ℝ)) from rfl,
          Real.rpow_add (by norm_num),
          Real.rpow_logb (by norm_num) (by norm_num) hc2, Real.rpow_natCast]
      rw [e1]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by rw [one_mul]; linarith [hkey])
    calc (n:ℝ) * Real.rpow 2 (Real.sqrt L - 1 * Real.logb 2 L)
        ≤ (n:ℝ) * (c₀ / 2 * (2:ℝ) ^ b) :=
          mul_le_mul_of_nonneg_left hrpow_le (le_of_lt hnR)
      _ = c₀ / 2 * (n:ℝ) * (2:ℝ) ^ b := by ring
      _ ≤ (extremal_function P n : ℝ) := hEx
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  exact ⟨max N 1, le_max_right _ _, fun n hn => hN n (le_trans (le_max_left _ _) hn)⟩

@[blueprint "lem:covering-pattern-lower-bound"
  (statement := /-- Let $r$ and $c$ be nonnegative integers and let $P$ be an
  $r\times(c+2)$ binary matrix which is a covering pattern in the sense of
  \cref{def:covering-pattern}.  Then $P$ satisfies the Pach--Tardos lower bound of
  \cref{def:pach-tardos-lower-bound}: there are a real constant $C\geq 0$ and an integer
  $N\geq 1$ such that
  \[
    n\,2^{\sqrt{\log_2 n}-C\log_2(\log_2 n)}\leq\operatorname{Ex}(P,n)
  \]
  for every integer $n\geq N$. -/)
  (proof := /-- Let $r$ and $c$ be nonnegative integers and let $P$ be an $r\times(c+2)$
  binary matrix satisfying the covering condition of \cref{def:covering-pattern}.  The proof
  assembles the three established properties of the covering construction $A_b$ of
  \cref{def:covering-construction}.

  First, apply \cref{lem:covering-construction-density} and let $c_0$ be the resulting real
  constant, so that $c_0>0$ and $c_0\,n_b\,2^{b}\le\lVert A_b\rVert_1$ for every integer
  $b\ge 2$, where $n_b=2^{b}(2b\,2^{b})^{b}$ is the common row and column count of $A_b$.

  Second, since $P$ is a covering pattern, \cref{lem:covering-construction-free} applied to $P$
  shows that $A_b$ is $P$-free in the sense of \cref{def:pattern-free} for every integer
  $b\ge 2$.

  Third, apply \cref{lem:covering-construction-interpolation} to $P$, to the covering hypothesis
  on $P$, to the constant $c_0$ together with its positivity, to the $P$-freeness statement
  supplied by \cref{lem:covering-construction-free}, and to the weight lower bound supplied by
  \cref{lem:covering-construction-density}.  These are exactly the five hypotheses of that
  lemma, and its conclusion is that $P$ satisfies the Pach--Tardos lower bound of
  \cref{def:pach-tardos-lower-bound}, which is the assertion to be proved. -/)
  (title := /-- Lower bound for covering patterns -/)
  (latexEnv := "lemma")]
lemma covering_pattern_lower_bound {r c : ℕ} (P : binary_matrix r (c + 2))
    (hP : covering_pattern P) : pach_tardos_lower_bound P := by
  obtain ⟨c₀, hc₀, hdense⟩ := covering_construction_density
  exact covering_construction_interpolation P hP c₀ hc₀
    (covering_construction_free P hP) hdense

@[blueprint "lem:s-zero-lower-bound"
  (statement := /-- There exist a real constant $C\geq 0$ and an integer $N\geq 1$ such that,
  for every integer $n\geq N$,
  \[
    n2^{\sqrt{\log_2 n}-C\log_2(\log_2 n)}\leq \operatorname{Ex}(S_0,n).
  \]
  Thus the pattern $S_0$ of \cref{def:pattern-s-zero} satisfies the Pach--Tardos lower bound of
  \cref{def:pach-tardos-lower-bound}. -/)
  (proof := /-- We verify the covering condition of \cref{def:covering-pattern}.  In the matrix
  $S_0$ of \cref{def:pattern-s-zero}, take row $1$ as the distinguished row and
  $J=\{0,2\}$.  Assign the intervals $[0,2]$ and $[1,3]$ to rows $0$ and $2$, respectively.
  The distinguished row contains $1$ in columns $0$ and $3$.  Row $0$ contains $1$ at both
  endpoints of $[0,2]$ and shares column $0$ with row $1$; row $2$ contains $1$ at both endpoints
  of $[1,3]$ and shares column $3$ with row $1$.  Exactly one row of $J$ precedes row $1$.
  Moreover, $[0,2]$ covers the gaps indexed by $0$ and $1$, while $[1,3]$ covers those indexed by
  $1$ and $2$.  Hence $S_0$ is a covering pattern, so
  \cref{lem:covering-pattern-lower-bound} yields the asserted lower bound. -/)
  (title := /-- Lower bound for $S_0$ -/)
  (latexEnv := "lemma")]
lemma s_zero_lower_bound : pach_tardos_lower_bound pattern_s_zero := by
  apply covering_pattern_lower_bound
  refine ⟨1, {0, 2}, ![0, 0, 1], ![2, 0, 3], ?_⟩
  decide

@[blueprint "lem:s-one-covering"
  (statement := /-- The pattern $S_1$ of \cref{def:pattern-s-one} is a covering pattern in the
  sense of \cref{def:covering-pattern}. -/)
  (proof := /-- Choose row $0$ as the distinguished row and take $J=\{1,2\}$.  The
  distinguished row has $1$-entries in columns $0$ and $3$.  For row $1$ choose the interval
  $[0,2]$, and for row $2$ choose the interval $[1,3]$.  Row $1$ shares the $1$-entry in
  column $0$ with the distinguished row, while row $2$ shares the $1$-entry in column $3$.
  Both covering rows follow the distinguished row, so none precedes it.  Finally, the gaps
  after columns $0$ and $1$ lie in $[0,2]$, and the gaps after columns $1$ and $2$ lie in
  $[1,3]$.  These entries and inequalities are exactly those displayed in
  \cref{def:pattern-s-one}, and they verify every clause of
  \cref{def:covering-pattern}. -/)
  (title := /-- The covering structure of $S_1$ -/)
  (latexEnv := "lemma")]
lemma s_one_covering : @covering_pattern 3 2 pattern_s_one := by
  refine ⟨0, {1, 2}, ![0, 0, 1], ![0, 2, 3], ?_⟩
  decide

@[blueprint "lem:s-one-lower-bound"
  (statement := /-- There exist a real constant $C\geq 0$ and an integer $N\geq 1$ such that,
  for every integer $n\geq N$,
  \[
    n2^{\sqrt{\log_2 n}-C\log_2(\log_2 n)}\leq \operatorname{Ex}(S_1,n).
  \]
  Thus the pattern $S_1$ of \cref{def:pattern-s-one} satisfies the Pach--Tardos lower bound of
  \cref{def:pach-tardos-lower-bound}. -/)
  (proof := /-- By \cref{lem:s-one-covering}, the pattern $S_1$ satisfies the covering
  condition.  Applying \cref{lem:covering-pattern-lower-bound} to this verification gives the
  asserted Pach--Tardos lower bound. -/)
  (title := /-- Lower bound for $S_1$ -/)
  (latexEnv := "lemma")]
lemma s_one_lower_bound : pach_tardos_lower_bound pattern_s_one := by
  exact covering_pattern_lower_bound pattern_s_one s_one_covering

@[blueprint "thm:PT-refutation"
  (statement := /-- Each of the two exceptional weight-six patterns $S_0$ of
  \cref{def:pattern-s-zero} and $S_1$ of \cref{def:pattern-s-one} satisfies the Pach--Tardos
  lower bound of \cref{def:pach-tardos-lower-bound}.  Explicitly, there are a real constant
  $C\geq 0$ and an integer $N\geq 1$ such that
  \[
    n2^{\sqrt{\log_2 n}-C\log_2(\log_2 n)}\leq \operatorname{Ex}(S_0,n)
    \quad\text{for every integer } n\geq N,
  \]
  and, for a possibly different such pair $C$ and $N$,
  \[
    n2^{\sqrt{\log_2 n}-C\log_2(\log_2 n)}\leq \operatorname{Ex}(S_1,n)
    \quad\text{for every integer } n\geq N.
  \]
  This is the quantified form of
  $\operatorname{Ex}(S_0,n),\operatorname{Ex}(S_1,n)\geq n2^{\sqrt{\log n}-O(\log\log n)}$. -/)
  (proof := /-- The first assertion is \cref{lem:s-zero-lower-bound}, and the second assertion is
  \cref{lem:s-one-lower-bound}.  Taking these two assertions as the two components of a
  conjunction proves the theorem. -/)
  (title := /-- A refutation of the Pach--Tardos conjecture for $0$--$1$ matrices -/)
  (latexEnv := "theorem")]
theorem PT_refutation :
    pach_tardos_lower_bound pattern_s_zero ∧ pach_tardos_lower_bound pattern_s_one := by
  exact ⟨s_zero_lower_bound, s_one_lower_bound⟩

import Architect
import Mathlib

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:line"
  (statement := /-- A \emph{line} is a non-vertical affine function of one real variable,
recorded by its slope $a\in\RR$ and its intercept $b\in\RR$; it represents the map
$\delta\mapsto a\delta+b$. This is the ambient object of a planar line arrangement, where the
horizontal axis carries the parameter $\delta$. -/)
  (title := /-- Non-vertical line in the plane -/)
  (latexEnv := "definition")]
structure line where
  slope : ℝ
  intercept : ℝ

@[blueprint "def:line-decidable-eq"
  (statement := /-- Equality of lines is decidable, since a line is determined by its slope and
intercept (see \cref{def:line}); we record this as an instance so that finite sets of lines are
well behaved. -/)
  (title := /-- Decidable equality of lines -/)
  (latexEnv := "definition")]
noncomputable instance line_decidable_eq : DecidableEq line := Classical.decEq line

@[blueprint "def:line-value"
  (statement := /-- The \emph{value} of a line $\ell$ with slope $a$ and intercept $b$ at a
parameter $\delta\in\RR$ is $a\delta+b$. -/)
  (title := /-- Value of a line at a parameter -/)
  (latexEnv := "definition")]
def line_value (l : line) (δ : ℝ) : ℝ := l.slope * δ + l.intercept

@[blueprint "def:line-arrangement"
  (statement := /-- A \emph{line arrangement} is a finite set of indexed lines: an element is a
pair $(r,\ell)$ consisting of a label $r\in\NN_0$ and an affine line $\ell$ (see
\cref{def:line}). Its cardinality is the number $m$ of indexed copies. Thus two elements with
different labels may carry the same affine line; retaining such coincident but distinct copies is
essential for arrangements arising from equal-population states. -/)
  (title := /-- Line arrangement -/)
  (latexEnv := "definition")]
abbrev line_arrangement := Finset (ℕ × line)

@[blueprint "def:k-level-vertices"
  (statement := /-- Let $A$ be a line arrangement and $k\in\NN_0$. The \emph{$k$-level vertices}
of $A$ are the points $q=(x,y)\in\RR^2$ for which two indexed elements of $A$ carry distinct
affine lines $\ell_1$ and $\ell_2$ satisfying $\ell_1(x)=\ell_2(x)=y$, and which lie in the
closure of the edges having exactly $k$ indexed lines below them. Explicitly, if $b$ indexed
elements $(r,\ell)\in A$ satisfy $\ell(x)<y$ and $r$ indexed elements satisfy
$\ell(x)=y$, then the incidence condition is
\[
 b\leq k<b+r.
\]
Thus all indexed copies through a degenerate crossing contribute to its incidence range.
Coincident copies alone do not create a vertex, since the two witnessing affine lines must still
be distinct. -/)
  (title := /-- Vertices of the $k$-level of an arrangement -/)
  (latexEnv := "definition")]
def k_level_vertices (A : line_arrangement) (k : ℕ) : Set (ℝ × ℝ) :=
  { q |
      (∃ l₁ ∈ A, ∃ l₂ ∈ A,
        l₁.2 ≠ l₂.2 ∧ line_value l₁.2 q.1 = q.2 ∧ line_value l₂.2 q.1 = q.2) ∧
      (A.filter (fun l => line_value l.2 q.1 < q.2)).card ≤ k ∧
      k < (A.filter (fun l => line_value l.2 q.1 < q.2)).card +
        (A.filter (fun l => line_value l.2 q.1 = q.2)).card }

@[blueprint "def:k-level-complexity"
  (statement := /-- The \emph{complexity} of the $k$-level of a line arrangement $A$ is the
number of vertices of that level, i.e. the cardinality of the set of $k$-level vertices of $A$
(see \cref{def:k-level-vertices}), including every degenerate crossing whose incidence range
contains $k$. -/)
  (title := /-- Complexity of the $k$-level -/)
  (latexEnv := "definition")]
noncomputable def k_level_complexity (A : line_arrangement) (k : ℕ) : ℕ :=
  (k_level_vertices A k).ncard

@[blueprint "def:eventually-two-scale-dominates"
  (statement := /-- A function $g:\NN_0\to\RR$ has \emph{eventual two-scale domination} if
there are constants $D>0$ and $N\in\NN_0$ such that, whenever $n\ge N$ and
$m\le 2n-1$,
\[
 \max\{1,g(m)\}\le Dg(n).
\]
In particular, $g(n)$ is eventually positive, every value $g(m)$ at a cardinality arising from
the reduction to at most $2n-1$ lines is controlled by $g(n)$, and fixed additive constants can
be absorbed into the same bound. -/)
  (title := /-- Eventual domination at the two-to-one cardinality scale -/)
  (latexEnv := "definition")]
def eventually_two_scale_dominates (g : ℕ → ℝ) : Prop :=
  ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ m : ℕ, m ≤ 2 * n - 1 →
    max 1 (g m) ≤ D * g n

@[blueprint "def:k-level-bounded-by"
  (statement := /-- A function $g:\NN_0\to\RR$ \emph{bounds the $k$-level complexity} if
there exist a constant $C>0$ and a threshold $N\in\NN_0$ such that for every $m\ge N$, every
line arrangement $A$ with exactly $m$ lines, and every $k$ with $0\le k\le m$, the complexity
of the $k$-level of $A$ (see \cref{def:k-level-complexity}) is at most $C\,g(m)$, and if $g$
also has the eventual two-scale domination property of
\cref{def:eventually-two-scale-dominates}. The latter condition is the regularity hypothesis
needed to transfer the bound from an arrangement with at most $2n-1$ lines to a bound expressed
in terms of $g(n)$. -/)
  (title := /-- Regular uniform $\calO(g)$ upper bound on $k$-level complexity -/)
  (latexEnv := "definition")]
def k_level_bounded_by (g : ℕ → ℝ) : Prop :=
  (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ A : line_arrangement,
      A.card = m → ∀ k : ℕ, k ≤ m →
        (k_level_complexity A k : ℝ) ≤ C * g m) ∧
    eventually_two_scale_dominates g

@[blueprint "def:apportionment-instance"
  (statement := /-- An \emph{apportionment instance} consists of a number of states $n\in\NN$, a
population vector $p:\{1,\dots,n\}\to\NN$ with $p_i>0$ for every state $i$, and a house size
$H\in\NN$ with $H>0$. -/)
  (title := /-- Apportionment instance -/)
  (latexEnv := "definition")]
structure apportionment_instance where
  n : ℕ
  p : Fin n → ℕ
  H : ℕ
  hn : 0 < n
  hp : ∀ i, 0 < p i
  hH : 0 < H

@[blueprint "def:round-delta-set"
  (statement := /-- For a threshold $\delta\in\RR$ and a real number $x$, the
\emph{$\delta$-rounding set} $\llbracket x\rrbracket_\delta$ is the set of integers to which $x$
may round under the stationary rule: if the fractional part $\{x\}$ exceeds $\delta$ then $x$
rounds up to $\lceil x\rceil$; if $\{x\}$ is below $\delta$ then $x$ rounds down to $\lfloor
x\rfloor$; and if $\{x\}=\delta$ then both $\lfloor x\rfloor$ and $\lceil x\rceil$ are admitted
(a tie). -/)
  (title := /-- Stationary $\delta$-rounding set -/)
  (latexEnv := "definition")]
def round_delta_set (δ x : ℝ) : Set ℤ :=
  { z |
      (δ < Int.fract x ∧ z = ⌈x⌉) ∨
      (Int.fract x < δ ∧ z = ⌊x⌋) ∨
      (Int.fract x = δ ∧ (z = ⌊x⌋ ∨ z = ⌈x⌉)) }

@[blueprint "def:divisor-output"
  (statement := /-- The \emph{stationary $\delta$-divisor output} of an apportionment instance
$(p,H)$ at threshold $\delta$ is the set of allocations $x:\{1,\dots,n\}\to\NN_0$ for which there
exists a divisor $\lambda>0$ with $x_i\in\llbracket\lambda p_i\rrbracket_\delta$ for every state
$i$ (see \cref{def:round-delta-set}) and $\sum_{i} x_i = H$. -/)
  (title := /-- Output of the stationary $\delta$-divisor method -/)
  (latexEnv := "definition")]
def divisor_output (inst : apportionment_instance) (δ : ℝ) : Set (Fin inst.n → ℕ) :=
  { x |
      (∃ lam : ℝ, 0 < lam ∧ ∀ i, ((x i : ℤ)) ∈ round_delta_set δ (lam * (inst.p i : ℝ))) ∧
      (∑ i, x i) = inst.H }

@[blueprint "def:breaking-points"
  (statement := /-- The set of \emph{breaking points} of an apportionment instance $(p,H)$ is the
terminal endpoint $1$, together with every threshold $\delta\in(0,1]$ at which the divisor
output changes as $\delta$ increases: for every $\varepsilon>0$ there is
$a\in(\delta-\varepsilon,\delta)$ with $f(p,H;a)\neq f(p,H;\delta)$, where $f$ is the divisor
output of \cref{def:divisor-output}. Thus $1$ is included even when the output is locally constant
from the left there, in accordance with the recursive convention that the final threshold is
always $\tau_B=1$. -/)
  (title := /-- Breaking points of an apportionment instance -/)
  (latexEnv := "definition")]
def breaking_points (inst : apportionment_instance) : Set ℝ :=
  { δ |
      δ ∈ Set.Ioc (0 : ℝ) 1 ∧
      (δ = 1 ∨
        ∀ ε : ℝ, 0 < ε →
          ∃ a ∈ Set.Ioo (δ - ε) δ, divisor_output inst a ≠ divisor_output inst δ) }

@[blueprint "def:num-breaking-points"
  (statement := /-- The \emph{number of breaking points} of an apportionment instance $(p,H)$ is
the cardinality of its set of breaking points (see \cref{def:breaking-points}). -/)
  (title := /-- Number of breaking points -/)
  (latexEnv := "definition")]
noncomputable def num_breaking_points (inst : apportionment_instance) : ℕ :=
  (breaking_points inst).ncard

@[blueprint "def:apportionment-arrangement"
  (statement := /-- The \emph{arrangement associated with} an apportionment instance $(p,H)$ is
$\mathcal{L}(p,H)=\{(iH+t,\ell_{i,t})\mid i\in\{0,\dots,n-1\},+t\in\{0,\dots,H-1\}\}$, where $\ell_{i,t}$ is the line with slope $1/p_i$ and intercept
$t/p_i$, i.e. $\ell_{i,t}(\delta)=(t+\delta)/p_i$ (see \cref{def:line}). Because $H>0$ and
$0\le t<H$, the label $iH+t$ uniquely identifies the pair $(i,t)$. Consequently equal
populations may produce coincident affine lines, but their indexed copies remain distinct elements
of the arrangement (see \cref{def:line-arrangement}). -/)
  (title := /-- Line arrangement associated with an apportionment instance -/)
  (latexEnv := "definition")]
noncomputable def apportionment_arrangement (inst : apportionment_instance) : line_arrangement :=
  (Finset.univ ×ˢ Finset.range inst.H).image
    (fun it : Fin inst.n × ℕ =>
      (it.1.val * inst.H + it.2,
        { slope := 1 / (inst.p it.1 : ℝ),
          intercept := (it.2 : ℝ) / (inst.p it.1 : ℝ) }))

@[blueprint "def:top-level-window-complexity"
  (statement := /-- The \emph{windowed complexity of the $(H-1)$-level} of an apportionment
instance $(p,H)$ is the number of vertices of the $(H-1)$-level of the associated indexed arrangement
$\mathcal{L}(p,H)$ (see \cref{def:k-level-vertices}, \cref{def:apportionment-arrangement}) whose
parameter coordinate $\delta$ lies in the window $[0,1]$; that is, the cardinality of the set of
$(H-1)$-level vertices $q=(\delta,y)$ with $\delta\in[0,1]$. This restricts the count to the
portion of the level traced by the upper level function $\lambda_H$ over the parameter window
$\delta\in[0,1]$. At a crossing with $b$ indexed lines strictly below and $r$ indexed lines
passing through it, the crossing is counted precisely when $b\leq H-1<b+r$; hence coincident
indexed copies contribute separately to the incidence range. The global count of $(H-1)$-level
vertices over all $\delta\in\RR$ is not the intended measure. -/)
  (title := /-- Windowed complexity of the $(H-1)$-level over $\delta\in[0,1]$ -/)
  (latexEnv := "definition")]
noncomputable def top_level_window_complexity (inst : apportionment_instance) : ℕ :=
  (k_level_vertices (apportionment_arrangement inst) (inst.H - 1) ∩
      { q : ℝ × ℝ | q.1 ∈ Set.Icc (0 : ℝ) 1 }).ncard

@[blueprint "lem:round-delta-set-nat-iff"
  (statement := /-- Let $0<\delta<1$, let $y\in\RR$, and let $x\in\NN_0$. Then $x$ belongs
to the stationary $\delta$-rounding set of $y$ if and only if
$x-1+\delta\leq y\leq x+\delta$. -/)
  (proof := /-- Unfold \cref{def:round-delta-set}. If the fractional part of $y$ is larger
than $\delta$, then $x=\lceil y\rceil$ and $\lfloor y\rfloor=x-1$; if it is smaller, then
$x=\lfloor y\rfloor$; and at equality either adjacent integer is admitted. In each case the
identity $y=\lfloor y\rfloor+\{y\}$ gives the displayed interval. Conversely, compare
$\{y\}$ with $\delta$. The two interval inequalities force respectively
$\lceil y\rceil=x$, $\lfloor y\rfloor=x$, or one of these two equalities in the tie case,
which is precisely membership in the rounding set. -/)
  (title := /-- Interval characterization of stationary rounding -/)
  (latexEnv := "lemma")]
lemma round_delta_set_nat_iff (δ y : ℝ) (x : ℕ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ((x : ℤ) ∈ round_delta_set δ y) ↔
      (x : ℝ) - 1 + δ ≤ y ∧ y ≤ (x : ℝ) + δ := by
  rw [round_delta_set]
  change
    ((δ < Int.fract y ∧ (x : ℤ) = ⌈y⌉) ∨
      (Int.fract y < δ ∧ (x : ℤ) = ⌊y⌋) ∨
      (Int.fract y = δ ∧ ((x : ℤ) = ⌊y⌋ ∨ (x : ℤ) = ⌈y⌉))) ↔ _
  have hy := Int.floor_add_fract y
  have hfract0 := Int.fract_nonneg y
  have hfract1 := Int.fract_lt_one y
  constructor
  · rintro (⟨hfract, hceil⟩ | ⟨hfract, hfloor⟩ | ⟨hfract, hfloor | hceil⟩)
    · have hceil' : ⌈y⌉ = (x : ℤ) := hceil.symm
      have hbounds := Int.ceil_eq_iff.mp hceil'
      have hyne : y ≠ (x : ℝ) := by
        intro heq
        subst y
        have : Int.fract (x : ℝ) = 0 := by simp
        linarith
      have hylt : y < (x : ℝ) := lt_of_le_of_ne hbounds.2 hyne
      have hfloor' : ⌊y⌋ = (x : ℤ) - 1 := by
        apply Int.floor_eq_iff.mpr
        constructor
        · norm_num at hbounds ⊢
          linarith
        · simpa using hylt
      rw [hfloor'] at hy
      norm_num at hy ⊢
      constructor <;> linarith
    · have hfloor' : ⌊y⌋ = (x : ℤ) := hfloor.symm
      rw [hfloor'] at hy
      norm_num at hy ⊢
      constructor <;> linarith
    · have hfloor' : ⌊y⌋ = (x : ℤ) := hfloor.symm
      rw [hfloor', hfract] at hy
      norm_num at hy ⊢
      constructor <;> linarith
    · have hceil' : ⌈y⌉ = (x : ℤ) := hceil.symm
      have hbounds := Int.ceil_eq_iff.mp hceil'
      have hyne : y ≠ (x : ℝ) := by
        intro heq
        subst y
        have : Int.fract (x : ℝ) = 0 := by simp
        linarith
      have hylt : y < (x : ℝ) := lt_of_le_of_ne hbounds.2 hyne
      have hfloor' : ⌊y⌋ = (x : ℤ) - 1 := by
        apply Int.floor_eq_iff.mpr
        constructor
        · norm_num at hbounds ⊢
          linarith
        · simpa using hylt
      rw [hfloor', hfract] at hy
      norm_num at hy ⊢
      constructor <;> linarith
  · rintro ⟨hlower, hupper⟩
    rcases lt_trichotomy δ (Int.fract y) with hfract | hfract | hfract
    · left
      refine ⟨hfract, ?_⟩
      symm
      apply Int.ceil_eq_iff.mpr
      constructor
      · norm_num at hlower ⊢
        linarith
      · by_contra hnot
        have hxy : (x : ℝ) < y := lt_of_not_ge hnot
        have hxfloor : (x : ℤ) ≤ ⌊y⌋ := Int.le_floor.mpr (le_of_lt hxy)
        have hxfloor' : (x : ℝ) ≤ (⌊y⌋ : ℝ) := by exact_mod_cast hxfloor
        linarith
    · right
      right
      refine ⟨hfract.symm, ?_⟩
      have hfloor_lower : (x : ℤ) - 1 ≤ ⌊y⌋ := by
        have hcast : (x : ℝ) - 1 ≤ (⌊y⌋ : ℝ) := by linarith
        exact_mod_cast hcast
      have hylt : y < (x : ℝ) + 1 := by linarith
      have hfloor_upper : ⌊y⌋ ≤ (x : ℤ) := by
        have hlt : ⌊y⌋ < (x : ℤ) + 1 := by
          apply Int.floor_lt.mpr
          norm_num
          exact hylt
        omega
      have hor : ⌊y⌋ = (x : ℤ) - 1 ∨ ⌊y⌋ = (x : ℤ) := by
        omega
      rcases hor with h | h
      · right
        symm
        apply Int.ceil_eq_iff.mpr
        have hcast : (⌊y⌋ : ℝ) = (x : ℝ) - 1 := by exact_mod_cast h
        norm_num
        constructor <;> linarith
      · left
        exact_mod_cast h.symm
    · right
      left
      refine ⟨hfract, ?_⟩
      symm
      apply Int.floor_eq_iff.mpr
      constructor
      · by_contra hnot
        have hyx : y < (x : ℝ) := lt_of_not_ge hnot
        have hfloorx : ⌊y⌋ < (x : ℤ) := Int.floor_lt.mpr hyx
        have hfloorx' : (⌊y⌋ : ℝ) ≤ (x : ℝ) - 1 := by
          exact_mod_cast (show ⌊y⌋ ≤ (x : ℤ) - 1 by omega)
        linarith
      · norm_num
        linarith

@[blueprint "lem:divisor-output-pairwise-iff"
  (statement := /-- Let $(p,H)$ be an apportionment instance, let $0<\delta<1$, and let
$x\in\NN_0^n$. Then $x$ is a stationary $\delta$-divisor output if and only if
$\sum_i x_i=H$ and, for every pair of states $i,j$,
\[
 \frac{x_i-1+\delta}{p_i}\leq \frac{x_j+\delta}{p_j}.
\] -/)
  (proof := /-- By \cref{lem:round-delta-set-nat-iff}, a common divisor $\lambda>0$
exists precisely when all intervals
$[(x_i-1+\delta)/p_i,(x_i+\delta)/p_i]$ have a common positive point.
Such a point implies every lower endpoint is at most every upper endpoint. Conversely, choose
an index at which the finitely many lower endpoints attain their maximum. The pairwise
inequalities put this maximum below every upper endpoint. Since $H>0$ and
$\sum_i x_i=H$, some $x_i$ is positive, so the maximum lower endpoint is positive and is a
valid common divisor. Applying \cref{lem:round-delta-set-nat-iff} again proves the converse. -/)
  (title := /-- Pairwise interval criterion for divisor outputs -/)
  (latexEnv := "lemma")]
lemma divisor_output_pairwise_iff (inst : apportionment_instance) (δ : ℝ)
    (x : Fin inst.n → ℕ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    x ∈ divisor_output inst δ ↔
      (∑ i, x i) = inst.H ∧
        ∀ i j, ((x i : ℝ) - 1 + δ) / (inst.p i : ℝ) ≤
          ((x j : ℝ) + δ) / (inst.p j : ℝ) := by
  constructor
  · rintro ⟨⟨lam, hlam, hround⟩, hsum⟩
    refine ⟨hsum, ?_⟩
    intro i j
    have hpi : 0 < (inst.p i : ℝ) := by exact_mod_cast inst.hp i
    have hpj : 0 < (inst.p j : ℝ) := by exact_mod_cast inst.hp j
    have hi := (round_delta_set_nat_iff δ (lam * (inst.p i : ℝ)) (x i) hδ0 hδ1).mp
      (hround i)
    have hj := (round_delta_set_nat_iff δ (lam * (inst.p j : ℝ)) (x j) hδ0 hδ1).mp
      (hround j)
    calc
      ((x i : ℝ) - 1 + δ) / (inst.p i : ℝ) ≤ lam :=
        (div_le_iff₀ hpi).mpr hi.1
      _ ≤ ((x j : ℝ) + δ) / (inst.p j : ℝ) :=
        (le_div_iff₀ hpj).mpr hj.2
  · rintro ⟨hsum, hpairs⟩
    let lower : Fin inst.n → ℝ :=
      fun i => ((x i : ℝ) - 1 + δ) / (inst.p i : ℝ)
    haveI : Nonempty (Fin inst.n) := ⟨⟨0, inst.hn⟩⟩
    obtain ⟨imax, -, hmax⟩ :=
      Finset.exists_max_image Finset.univ lower Finset.univ_nonempty
    have hsumpos : 0 < ∑ i, x i := by simpa [hsum] using inst.hH
    rw [Finset.sum_pos_iff] at hsumpos
    obtain ⟨ipos, -, hipos⟩ := hsumpos
    have hpi : 0 < (inst.p ipos : ℝ) := by exact_mod_cast inst.hp ipos
    have hxi : 1 ≤ (x ipos : ℝ) := by exact_mod_cast hipos
    have hlowerpos : 0 < lower ipos := by
      dsimp [lower]
      exact div_pos (by linarith) hpi
    have hlampos : 0 < lower imax :=
      lt_of_lt_of_le hlowerpos (hmax ipos (Finset.mem_univ ipos))
    refine ⟨⟨lower imax, hlampos, ?_⟩, hsum⟩
    intro i
    have hpi' : 0 < (inst.p i : ℝ) := by exact_mod_cast inst.hp i
    apply (round_delta_set_nat_iff δ (lower imax * (inst.p i : ℝ))
      (x i) hδ0 hδ1).mpr
    constructor
    · exact (div_le_iff₀ hpi').mp (hmax i (Finset.mem_univ i))
    · exact (le_div_iff₀ hpi').mp (hpairs imax i)

@[blueprint "lem:strict-divisor-interval-indices"
  (statement := /-- Let $x\in\NN_0^n$ satisfy $\sum_i x_i=H$, and let
$0<\delta<1$. If the upper divisor endpoint belonging to state $j$ is strictly below the lower
endpoint belonging to state $i$, then $x_i>0$ and $x_j<H$. -/)
  (proof := /-- If $x_i=0$, its lower endpoint is negative because $\delta<1$, whereas every
upper endpoint is positive because $\delta>0$, contradicting the strict reverse inequality.
Thus $x_i>0$. Every coordinate is at most the total $H$. If $x_j=H$, all other coordinates
vanish. For $i=j$ the lower endpoint is strictly smaller than the upper endpoint, and for
$i\ne j$ the already established positivity of $x_i$ contradicts that vanishing. Hence
$x_j<H$. -/)
  (title := /-- Indices in a reversed divisor interval are internal -/)
  (latexEnv := "lemma")]
lemma strict_divisor_interval_indices (inst : apportionment_instance)
    (x : Fin inst.n → ℕ) (δ : ℝ) (hsum : (∑ i, x i) = inst.H)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {i j : Fin inst.n}
    (hbad : ((x j : ℝ) + δ) / (inst.p j : ℝ) <
      ((x i : ℝ) - 1 + δ) / (inst.p i : ℝ)) :
    0 < x i ∧ x j < inst.H := by
  have hpi : 0 < (inst.p i : ℝ) := by exact_mod_cast inst.hp i
  have hpj : 0 < (inst.p j : ℝ) := by exact_mod_cast inst.hp j
  have hxi : 0 < x i := by
    by_contra hnot
    have hxiz : x i = 0 := by omega
    have hlowerneg : ((x i : ℝ) - 1 + δ) / (inst.p i : ℝ) < 0 := by
      rw [hxiz]
      norm_num
      exact div_neg_of_neg_of_pos (by linarith) hpi
    have hupperpos : 0 < ((x j : ℝ) + δ) / (inst.p j : ℝ) := by
      apply div_pos
      · positivity
      · exact hpj
    linarith
  refine ⟨hxi, ?_⟩
  have hxjle : x j ≤ inst.H := by
    calc
      x j ≤ ∑ k ∈ Finset.univ, x k :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      _ = inst.H := by simpa using hsum
  by_contra hnot
  have hxjeq : x j = inst.H := by omega
  by_cases hij : i = j
  · subst j
    have hpi' : 0 < (inst.p i : ℝ) := by exact_mod_cast inst.hp i
    have hcross := (div_lt_div_iff₀ hpi' hpi').mp hbad
    nlinarith
  · have hdecomp := Finset.sum_erase_add (s := Finset.univ) (f := x)
        (Finset.mem_univ j)
    have hrest : ∑ k ∈ Finset.univ.erase j, x k = 0 := by
      rw [hxjeq] at hdecomp
      simpa [hsum] using hdecomp
    have hile : x i ≤ ∑ k ∈ Finset.univ.erase j, x k := by
      apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      simp [hij]
    omega

@[blueprint "lem:apportionment-line-index-injective"
  (statement := /-- For an apportionment instance, the map sending a pair $(i,t)$ with
$0\leq t<H$ to the indexed arrangement element labelled $iH+t$ is injective. -/)
  (proof := /-- Equality of two image elements gives equality of their labels. Reduction of
$iH+t=jH+u$ modulo the positive integer $H$ yields $t=u$, since both remainders are smaller
than $H$. Division by $H$ then gives $i=j$. Thus the original state--index pairs coincide. -/)
  (title := /-- Injectivity of apportionment line indices -/)
  (latexEnv := "lemma")]
lemma apportionment_line_index_injective (inst : apportionment_instance) :
    ∀ a : Fin inst.n × ℕ,
      a ∈ (Finset.univ : Finset (Fin inst.n)) ×ˢ Finset.range inst.H →
      ∀ b : Fin inst.n × ℕ,
        b ∈ (Finset.univ : Finset (Fin inst.n)) ×ˢ Finset.range inst.H →
        ((a.1.val * inst.H + a.2,
          { slope := 1 / (inst.p a.1 : ℝ),
            intercept := (a.2 : ℝ) / (inst.p a.1 : ℝ) }) : ℕ × line) =
        ((b.1.val * inst.H + b.2,
          { slope := 1 / (inst.p b.1 : ℝ),
            intercept := (b.2 : ℝ) / (inst.p b.1 : ℝ) }) : ℕ × line) → a = b := by
  rintro ⟨i, t⟩ hit ⟨j, u⟩ hju hpair
  have ht : t < inst.H := Finset.mem_range.mp (Finset.mem_product.mp hit).2
  have hu : u < inst.H := Finset.mem_range.mp (Finset.mem_product.mp hju).2
  have hlabel : i.val * inst.H + t = j.val * inst.H + u :=
    congrArg Prod.fst hpair
  have htu : t = u := by
    have hmod := congrArg (fun z => z % inst.H) hlabel
    simpa [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ht,
      Nat.mod_eq_of_lt hu] using hmod
  have hij : i.val = j.val := by
    have hdiv := congrArg (fun z => z / inst.H) hlabel
    have hi : (i.val * inst.H + t) / inst.H = i.val := by
      rw [Nat.mul_comm i.val inst.H, Nat.mul_add_div inst.hH,
        Nat.div_eq_of_lt ht, Nat.add_zero]
    have hj : (j.val * inst.H + u) / inst.H = j.val := by
      rw [Nat.mul_comm j.val inst.H, Nat.mul_add_div inst.hH,
        Nat.div_eq_of_lt hu, Nat.add_zero]
    exact hi.symm.trans (hdiv.trans hj)
  exact Prod.ext (Fin.ext hij) htu

@[blueprint "lem:apportionment-prefix-card"
  (statement := /-- Let $x\in\NN_0^n$ satisfy $x_i\leq H$ for every state. Among the pairs
$(i,t)$ with $0\leq t<H$, exactly $\sum_i x_i$ satisfy $t<x_i$. -/)
  (proof := /-- Write the cardinality as a sum of indicator functions and sum first over the
state index. For a fixed $i$, the admissible indices form
$\{0,\ldots,H-1\}\cap\{t:t<x_i\}=\{0,\ldots,x_i-1\}$ because $x_i\leq H$.
This fiber has cardinality $x_i$; summing the fiber cardinalities over all states proves the
formula. -/)
  (title := /-- Cardinality of allocation-prefix line indices -/)
  (latexEnv := "lemma")]
lemma apportionment_prefix_card (inst : apportionment_instance)
    (x : Fin inst.n → ℕ) (hx : ∀ i, x i ≤ inst.H) :
    ((Finset.univ ×ˢ Finset.range inst.H).filter
      (fun it : Fin inst.n × ℕ => it.2 < x it.1)).card = ∑ i, x i := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.card_filter]
  have heq : (Finset.range inst.H).filter (fun t => t < x i) =
      Finset.range (x i) := by
    have hxi := hx i
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [heq, Finset.card_range]

@[blueprint "lem:allocation-binding-level-vertex"
  (statement := /-- Let $0<\delta<1$ and let $x\in\NN_0^n$ have sum $H$. Suppose every
lower divisor endpoint of $x$ is at most every upper endpoint, and suppose the lower endpoint
for state $i$ equals the upper endpoint for state $j$. If $x_i>0$, $x_j<H$, and the corresponding
two affine lines are distinct, then their common point is a vertex of the $(H-1)$-level of the
apportionment arrangement. -/)
  (proof := /-- Put $y=(x_i-1+\delta)/p_i=(x_j+\delta)/p_j$. The pairwise inequalities show
that, for every state $s$, its lower endpoint is at most $y$ and its upper endpoint is at least
$y$. By \cref{lem:apportionment-prefix-card}, the line indices $t<x_s$ number exactly $H$.
Every line strictly below $y$ has such an index, and the line $(i,x_i-1)$ belongs to this prefix
but lies on $y$; hence at most $H-1$ indexed lines lie strictly below. Conversely every prefix
line lies at or below $y$, so at least $H$ indexed lines lie at or below. The indexing map is
injective by \cref{lem:apportionment-line-index-injective}, so these pair counts are the
corresponding arrangement counts. The two assumed distinct lines witness a crossing, and the
two cardinal bounds give the incidence inequalities for \cref{def:k-level-vertices}. -/)
  (title := /-- A binding allocation interval gives a top-level vertex -/)
  (latexEnv := "lemma")]
lemma allocation_binding_level_vertex (inst : apportionment_instance)
    (x : Fin inst.n → ℕ) (δ : ℝ) (i j : Fin inst.n)
    (hsum : (∑ s, x s) = inst.H)
    (hpairs : ∀ r s, ((x r : ℝ) - 1 + δ) / (inst.p r : ℝ) ≤
      ((x s : ℝ) + δ) / (inst.p s : ℝ))
    (hbind : ((x i : ℝ) - 1 + δ) / (inst.p i : ℝ) =
      ((x j : ℝ) + δ) / (inst.p j : ℝ))
    (hxi : 0 < x i) (hxj : x j < inst.H)
    (hne : (⟨1 / (inst.p i : ℝ),
        ((x i - 1 : ℕ) : ℝ) / (inst.p i : ℝ)⟩ : line) ≠
      (⟨1 / (inst.p j : ℝ),
        (x j : ℝ) / (inst.p j : ℝ)⟩ : line)) :
    (δ, ((x i : ℝ) - 1 + δ) / (inst.p i : ℝ)) ∈
      k_level_vertices (apportionment_arrangement inst) (inst.H - 1) := by
  classical
  let D : Finset (Fin inst.n × ℕ) :=
    Finset.univ ×ˢ Finset.range inst.H
  let f : Fin inst.n × ℕ → ℕ × line := fun it =>
    (it.1.val * inst.H + it.2,
      { slope := 1 / (inst.p it.1 : ℝ),
        intercept := (it.2 : ℝ) / (inst.p it.1 : ℝ) })
  let y : ℝ := ((x i : ℝ) - 1 + δ) / (inst.p i : ℝ)
  have hvalue (r : Fin inst.n) (t : ℕ) (z : ℝ) :
      line_value (⟨1 / (inst.p r : ℝ),
        (t : ℝ) / (inst.p r : ℝ)⟩ : line) z =
        ((t : ℝ) + z) / (inst.p r : ℝ) := by
    unfold line_value
    dsimp
    ring
  have hxle : ∀ r, x r ≤ inst.H := by
    intro r
    calc
      x r ≤ ∑ s ∈ Finset.univ, x s :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
      _ = inst.H := by simpa using hsum
  have hlowery : ∀ r, ((x r : ℝ) - 1 + δ) / (inst.p r : ℝ) ≤ y := by
    intro r
    dsimp [y]
    simpa [hbind] using hpairs r j
  have hyupper : ∀ r, y ≤ ((x r : ℝ) + δ) / (inst.p r : ℝ) := by
    intro r
    dsimp [y]
    exact hpairs i r
  let B := D.filter (fun it => line_value (f it).2 δ < y)
  let P := D.filter (fun it => it.2 < x it.1)
  let C := D.filter (fun it => line_value (f it).2 δ ≤ y)
  have hBP : B ⊆ P := by
    intro it hit
    have hitD := (Finset.mem_filter.mp hit).1
    have hitlt := (Finset.mem_filter.mp hit).2
    apply Finset.mem_filter.mpr
    refine ⟨hitD, ?_⟩
    have hp : 0 < (inst.p it.1 : ℝ) := by exact_mod_cast inst.hp it.1
    have hv := hvalue it.1 it.2 δ
    have hu := hyupper it.1
    dsimp [f] at hitlt
    rw [hvalue] at hitlt
    have hcast : (it.2 : ℝ) < (x it.1 : ℝ) := by
      have hq : ((it.2 : ℝ) + δ) / (inst.p it.1 : ℝ) <
          ((x it.1 : ℝ) + δ) / (inst.p it.1 : ℝ) :=
        lt_of_lt_of_le hitlt hu
      have := (div_lt_div_iff_of_pos_right hp).mp hq
      linarith
    exact_mod_cast hcast
  have hwiH : x i - 1 < inst.H := by
    have := hxle i
    omega
  have hwiP : (i, x i - 1) ∈ P := by
    apply Finset.mem_filter.mpr
    constructor
    · simp [D, hwiH]
    · dsimp
      omega
  have hwiB : (i, x i - 1) ∉ B := by
    intro hmem
    have hlt := (Finset.mem_filter.mp hmem).2
    dsimp [f, y] at hlt
    rw [hvalue] at hlt
    norm_num [Nat.cast_sub (by omega : 1 ≤ x i)] at hlt
  have hBproper : B ⊂ P := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hBP, ?_⟩
    intro heq
    exact hwiB (heq ▸ hwiP)
  have hBcard : B.card < inst.H := by
    have hlt := Finset.card_lt_card hBproper
    have hPcard : P.card = inst.H := by
      dsimp [P, D]
      rw [apportionment_prefix_card inst x hxle, hsum]
    omega
  have hPC : P ⊆ C := by
    intro it hit
    have hitD := (Finset.mem_filter.mp hit).1
    have hitt := (Finset.mem_filter.mp hit).2
    apply Finset.mem_filter.mpr
    refine ⟨hitD, ?_⟩
    have hp : 0 < (inst.p it.1 : ℝ) := by exact_mod_cast inst.hp it.1
    have htle : (it.2 : ℝ) ≤ (x it.1 : ℝ) - 1 := by
      change it.2 < x it.1 at hitt
      calc
        (it.2 : ℝ) ≤ ((x it.1 - 1 : ℕ) : ℝ) := by
          exact_mod_cast (show it.2 ≤ x it.1 - 1 by omega)
        _ = (x it.1 : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ x it.1)]
          norm_num
    have hl := hlowery it.1
    dsimp [f]
    rw [hvalue]
    apply le_trans ?_ hl
    apply (div_le_div_iff_of_pos_right hp).mpr
    linarith
  have hCcard : inst.H ≤ C.card := by
    have hcard := Finset.card_le_card hPC
    have hPcard : P.card = inst.H := by
      dsimp [P, D]
      rw [apportionment_prefix_card inst x hxle, hsum]
    omega
  have hinj : ∀ a ∈ D, ∀ b ∈ D, f a = f b → a = b := by
    intro a ha b hb hab
    exact apportionment_line_index_injective inst a ha b hb hab
  have hbelow :
      ((apportionment_arrangement inst).filter
        (fun l => line_value l.2 δ < y)).card = B.card := by
    unfold apportionment_arrangement
    rw [Finset.filter_image]
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    apply hinj a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
  have hle :
      ((apportionment_arrangement inst).filter
        (fun l => line_value l.2 δ ≤ y)).card = C.card := by
    unfold apportionment_arrangement
    rw [Finset.filter_image]
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    apply hinj a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
  have hsplit :
      ((apportionment_arrangement inst).filter
          (fun l => line_value l.2 δ < y)).card +
        ((apportionment_arrangement inst).filter
          (fun l => line_value l.2 δ = y)).card =
        ((apportionment_arrangement inst).filter
          (fun l => line_value l.2 δ ≤ y)).card := by
    let L := (apportionment_arrangement inst).filter
      (fun l => line_value l.2 δ < y)
    let E := (apportionment_arrangement inst).filter
      (fun l => line_value l.2 δ = y)
    have hdis : Disjoint L E := by
      apply Finset.disjoint_left.mpr
      intro l hl hleq
      have hlt := (Finset.mem_filter.mp hl).2
      have heq := (Finset.mem_filter.mp hleq).2
      linarith
    rw [← Finset.card_union_of_disjoint hdis]
    apply congrArg Finset.card
    ext l
    simp only [L, E, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hlA, hlt⟩ | ⟨hlA, heq⟩)
      · exact ⟨hlA, le_of_lt hlt⟩
      · exact ⟨hlA, le_of_eq heq⟩
    · rintro ⟨hlA, hleq⟩
      rcases lt_or_eq_of_le hleq with hlt | heq
      · exact Or.inl ⟨hlA, hlt⟩
      · exact Or.inr ⟨hlA, heq⟩
  refine ⟨?_, ?_, ?_⟩
  · let li : ℕ × line := f (i, x i - 1)
    let lj : ℕ × line := f (j, x j)
    refine ⟨li, ?_, lj, ?_, ?_, ?_, ?_⟩
    · unfold apportionment_arrangement
      apply Finset.mem_image.mpr
      refine ⟨(i, x i - 1), ?_, rfl⟩
      simp [hwiH]
    · unfold apportionment_arrangement
      apply Finset.mem_image.mpr
      refine ⟨(j, x j), ?_, rfl⟩
      simp [hxj]
    · simpa [li, lj, f] using hne
    · dsimp [li, f, y]
      rw [hvalue]
      norm_num [Nat.cast_sub (by omega : 1 ≤ x i)]
    · dsimp [lj, f, y]
      rw [hvalue]
      exact hbind.symm
  · rw [hbelow]
    omega
  · rw [hsplit, hle]
    omega

@[blueprint "lem:finite-line-order-stable"
  (statement := /-- Let $A$ be a finite indexed line arrangement and fix
$\delta\in\RR$. There is an $\varepsilon>0$ such that, whenever
$|a-\delta|<\varepsilon$, every strict ordering between the values at $\delta$ of two lines
in $A$ remains the same at $a$. -/)
  (proof := /-- Each affine line is continuous. Hence, for each ordered pair of indexed lines
whose values are strictly ordered at $\delta$, continuity preserves that strict inequality on
some neighbourhood of $\delta$. Intersect these neighbourhoods over the finitely many ordered
pairs in $A$. The resulting neighbourhood contains a metric ball of some positive radius
$\varepsilon$, which has the asserted simultaneous stability property. -/)
  (title := /-- Local stability of all strict line orders -/)
  (latexEnv := "lemma")]
lemma finite_line_order_stable (A : line_arrangement) (δ : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : ℝ, dist a δ < ε →
      ∀ l₁ ∈ A, ∀ l₂ ∈ A,
        line_value l₁.2 δ < line_value l₂.2 δ →
          line_value l₁.2 a < line_value l₂.2 a := by
  have hcont (l : line) : Continuous (fun z : ℝ => line_value l z) := by
    unfold line_value
    fun_prop
  have hev : ∀ᶠ a in nhds δ, ∀ l₁ ∈ A, ∀ l₂ ∈ A,
      line_value l₁.2 δ < line_value l₂.2 δ →
        line_value l₁.2 a < line_value l₂.2 a := by
    rw [Filter.eventually_all_finset]
    intro l₁ hl₁
    rw [Filter.eventually_all_finset]
    intro l₂ hl₂
    by_cases hlt : line_value l₁.2 δ < line_value l₂.2 δ
    · filter_upwards [
        (hcont l₁.2).continuousAt.eventually_lt (hcont l₂.2).continuousAt hlt] with a ha
      exact fun _ => ha
    · exact Filter.Eventually.of_forall (fun _ h => (hlt h).elim)
  rcases Metric.eventually_nhds_iff.mp hev with ⟨ε, hε, hev⟩
  exact ⟨ε, hε, fun a ha => hev ha⟩

@[blueprint "lem:interior-breaking-point-level-vertex"
  (statement := /-- Every breaking point $\delta\ne1$ of an apportionment instance is the
parameter coordinate of a vertex on the $(H-1)$-level of its associated indexed arrangement. -/)
  (proof := /-- Let $0<\delta<1$ be such a breaking point. By
\cref{lem:finite-line-order-stable}, choose a left neighbourhood of $\delta$ on which every
strict ordering of arrangement lines at $\delta$ persists. The definition
\cref{def:breaking-points} supplies $a<\delta$ in this neighbourhood with a different divisor
output. By \cref{lem:divisor-output-pairwise-iff}, an allocation present at $a$ but absent at
$\delta$ would contain a reversed pair of interval endpoints at $\delta$; the corresponding
strict line order would persist at $a$, contradicting feasibility there. Hence some allocation
$x$ is feasible at $\delta$ but not at $a$. A pairwise interval inequality for $x$ therefore
fails at $a$. It cannot be strict at $\delta$, again by line-order stability, so the relevant
lower and upper endpoints coincide at $\delta$. By
\cref{lem:strict-divisor-interval-indices}, their indices lie in the arrangement; the two lines
are distinct because their order is strict at $a$. Finally
\cref{lem:allocation-binding-level-vertex} shows that their common point is a vertex of the
$(H-1)$-level. -/)
  (title := /-- Interior breaking points occur at top-level vertices -/)
  (latexEnv := "lemma")]
lemma interior_breaking_point_level_vertex (inst : apportionment_instance) (δ : ℝ)
    (hδ : δ ∈ breaking_points inst) (hδne : δ ≠ 1) :
    ∃ y : ℝ, (δ, y) ∈
      k_level_vertices (apportionment_arrangement inst) (inst.H - 1) := by
  classical
  rcases hδ with ⟨hδmem, hδone | hbreak⟩
  · exact (hδne hδone).elim
  have hδ0 : 0 < δ := hδmem.1
  have hδ1 : δ < 1 := lt_of_le_of_ne hδmem.2 hδne
  obtain ⟨ε, hε, hstable⟩ :=
    finite_line_order_stable (apportionment_arrangement inst) δ
  let η := min ε δ
  have hη : 0 < η := lt_min hε hδ0
  obtain ⟨a, hamem, hdiff⟩ := hbreak η hη
  have haη : δ - η < a := hamem.1
  have haδ : a < δ := hamem.2
  have ha0 : 0 < a := by
    have hηδ : η ≤ δ := min_le_right ε δ
    linarith
  have ha1 : a < 1 := lt_trans haδ hδ1
  have hdist : dist a δ < ε := by
    have hηε : η ≤ ε := min_le_left ε δ
    rw [Real.dist_eq]
    rw [abs_of_neg (sub_neg.mpr haδ)]
    linarith
  have horders := hstable a hdist
  have hdiff' : divisor_output inst a ≠ divisor_output inst δ := hdiff
  have hex : ∃ x : Fin inst.n → ℕ,
      ¬(x ∈ divisor_output inst a ↔ x ∈ divisor_output inst δ) := by
    by_contra hnot
    push Not at hnot
    apply hdiff'
    ext x
    exact hnot x
  obtain ⟨x, hx⟩ := hex
  have haiff := divisor_output_pairwise_iff inst a x ha0 ha1
  have hδiff := divisor_output_pairwise_iff inst δ x hδ0 hδ1
  by_cases hxa : x ∈ divisor_output inst a
  · have hxδ : x ∉ divisor_output inst δ := by
      intro hxδ
      exact hx ⟨fun _ => hxδ, fun _ => hxa⟩
    exfalso
    rcases haiff.mp hxa with ⟨hsum, hpairs_a⟩
    have hnotpairs : ¬ ∀ r s, ((x r : ℝ) - 1 + δ) / (inst.p r : ℝ) ≤
        ((x s : ℝ) + δ) / (inst.p s : ℝ) := by
      intro hpairs
      exact hxδ (hδiff.mpr ⟨hsum, hpairs⟩)
    push Not at hnotpairs
    obtain ⟨i, j, hbadδ⟩ := hnotpairs
    obtain ⟨hxi, hxj⟩ :=
      strict_divisor_interval_indices inst x δ hsum hδ0 hδ1 hbadδ
    have hxiH : x i - 1 < inst.H := by
      have hile : x i ≤ inst.H := by
        calc
          x i ≤ ∑ s ∈ Finset.univ, x s :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          _ = inst.H := by simpa using hsum
      omega
    let li : ℕ × line :=
      (i.val * inst.H + (x i - 1),
        ⟨1 / (inst.p i : ℝ), ((x i - 1 : ℕ) : ℝ) / (inst.p i : ℝ)⟩)
    let lj : ℕ × line :=
      (j.val * inst.H + x j,
        ⟨1 / (inst.p j : ℝ), (x j : ℝ) / (inst.p j : ℝ)⟩)
    have hli : li ∈ apportionment_arrangement inst := by
      unfold apportionment_arrangement
      apply Finset.mem_image.mpr
      refine ⟨(i, x i - 1), ?_, rfl⟩
      simp [hxiH]
    have hlj : lj ∈ apportionment_arrangement inst := by
      unfold apportionment_arrangement
      apply Finset.mem_image.mpr
      refine ⟨(j, x j), ?_, rfl⟩
      simp [hxj]
    have hvalue_i (z : ℝ) : line_value li.2 z =
        ((x i : ℝ) - 1 + z) / (inst.p i : ℝ) := by
      dsimp [li, line_value]
      rw [Nat.cast_sub (by omega : 1 ≤ x i)]
      ring
    have hvalue_j (z : ℝ) : line_value lj.2 z =
        ((x j : ℝ) + z) / (inst.p j : ℝ) := by
      dsimp [lj, line_value]
      ring
    have hpersist := horders lj hlj li hli
    have hbadline : line_value lj.2 δ < line_value li.2 δ := by
      rw [hvalue_j, hvalue_i]
      exact hbadδ
    have hpers := hpersist hbadline
    rw [hvalue_j, hvalue_i] at hpers
    exact (not_lt_of_ge (hpairs_a i j)) hpers
  · have hxδ : x ∈ divisor_output inst δ := by
      by_contra hxδ
      exact hx ⟨fun ha => (hxa ha).elim, fun hδout => (hxδ hδout).elim⟩
    rcases hδiff.mp hxδ with ⟨hsum, hpairsδ⟩
    have hnotpairs : ¬ ∀ r s, ((x r : ℝ) - 1 + a) / (inst.p r : ℝ) ≤
        ((x s : ℝ) + a) / (inst.p s : ℝ) := by
      intro hpairs
      exact hxa (haiff.mpr ⟨hsum, hpairs⟩)
    push Not at hnotpairs
    obtain ⟨i, j, hbada⟩ := hnotpairs
    obtain ⟨hxi, hxj⟩ :=
      strict_divisor_interval_indices inst x a hsum ha0 ha1 hbada
    have hxiH : x i - 1 < inst.H := by
      have hile : x i ≤ inst.H := by
        calc
          x i ≤ ∑ s ∈ Finset.univ, x s :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          _ = inst.H := by simpa using hsum
      omega
    let li : ℕ × line :=
      (i.val * inst.H + (x i - 1),
        ⟨1 / (inst.p i : ℝ), ((x i - 1 : ℕ) : ℝ) / (inst.p i : ℝ)⟩)
    let lj : ℕ × line :=
      (j.val * inst.H + x j,
        ⟨1 / (inst.p j : ℝ), (x j : ℝ) / (inst.p j : ℝ)⟩)
    have hli : li ∈ apportionment_arrangement inst := by
      unfold apportionment_arrangement
      apply Finset.mem_image.mpr
      refine ⟨(i, x i - 1), ?_, rfl⟩
      simp [hxiH]
    have hlj : lj ∈ apportionment_arrangement inst := by
      unfold apportionment_arrangement
      apply Finset.mem_image.mpr
      refine ⟨(j, x j), ?_, rfl⟩
      simp [hxj]
    have hvalue_i (z : ℝ) : line_value li.2 z =
        ((x i : ℝ) - 1 + z) / (inst.p i : ℝ) := by
      dsimp [li, line_value]
      rw [Nat.cast_sub (by omega : 1 ≤ x i)]
      ring
    have hvalue_j (z : ℝ) : line_value lj.2 z =
        ((x j : ℝ) + z) / (inst.p j : ℝ) := by
      dsimp [lj, line_value]
      ring
    have hleδ := hpairsδ i j
    have hbind : ((x i : ℝ) - 1 + δ) / (inst.p i : ℝ) =
        ((x j : ℝ) + δ) / (inst.p j : ℝ) := by
      apply le_antisymm hleδ
      by_contra hnot
      have hstrict : ((x i : ℝ) - 1 + δ) / (inst.p i : ℝ) <
          ((x j : ℝ) + δ) / (inst.p j : ℝ) :=
        lt_of_not_ge hnot
      have hpersist := horders li hli lj hlj
      have hstrictline : line_value li.2 δ < line_value lj.2 δ := by
        rw [hvalue_i, hvalue_j]
        exact hstrict
      have hpers := hpersist hstrictline
      rw [hvalue_i, hvalue_j] at hpers
      exact (not_lt_of_ge (le_of_lt hbada)) hpers
    have hne : li.2 ≠ lj.2 := by
      intro heq
      have heqv : line_value li.2 a = line_value lj.2 a := congrArg (fun l => line_value l a) heq
      rw [hvalue_i, hvalue_j] at heqv
      linarith
    refine ⟨((x i : ℝ) - 1 + δ) / (inst.p i : ℝ), ?_⟩
    apply allocation_binding_level_vertex inst x δ i j hsum hpairsδ hbind hxi hxj
    simpa [li, lj] using hne

@[blueprint "lem:local-k-level-vertices-finite"
  (statement := /-- For every finite indexed line arrangement $A$ and every level index $k$,
the set of vertices of the $k$-level is finite. -/)
  (proof := /-- Every vertex is the intersection of two distinct affine lines in $A$. Associate
to each ordered pair of indexed lines the point obtained by solving their affine equations
(using an arbitrary value when the slopes coincide). These points form a finite image of
$A\times A$. For a genuine vertex, equality of the two line values and distinctness of the lines
force distinct slopes; solving the equation shows that the vertex is exactly the associated
image point. Thus the vertex set is contained in a finite set. -/)
  (title := /-- Finiteness of level vertices for a finite arrangement -/)
  (latexEnv := "lemma")]
lemma local_k_level_vertices_finite (A : line_arrangement) (k : ℕ) :
    (k_level_vertices A k).Finite := by
  classical
  let cross (ls : (ℕ × line) × (ℕ × line)) : ℝ × ℝ :=
    let x := (ls.2.2.intercept - ls.1.2.intercept) /
      (ls.1.2.slope - ls.2.2.slope)
    (x, line_value ls.1.2 x)
  let V : Finset (ℝ × ℝ) := (A ×ˢ A).image cross
  apply V.finite_toSet.subset
  intro q hq
  obtain ⟨⟨l₁, hl₁, l₂, hl₂, hne, hv₁, hv₂⟩, hlevel⟩ := hq
  have hs : l₁.2.slope ≠ l₂.2.slope := by
    intro heq
    have hi : l₁.2.intercept = l₂.2.intercept := by
      simp only [line_value] at hv₁ hv₂
      rw [heq] at hv₁
      linarith
    apply hne
    have hli : Function.Injective (fun l : line => (l.slope, l.intercept)) := by
      intro a b h
      cases a
      cases b
      simp_all
    exact hli (Prod.ext heq hi)
  have hx :
      q.1 = (l₂.2.intercept - l₁.2.intercept) /
        (l₁.2.slope - l₂.2.slope) := by
    apply (eq_div_iff (sub_ne_zero.mpr hs)).2
    simp only [line_value] at hv₁ hv₂
    linarith
  have hqcross : q = cross (l₁, l₂) := by
    apply Prod.ext
    · simpa [cross] using hx
    · simp only [cross]
      rw [← hv₁, hx]
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr
    ⟨(l₁, l₂), Finset.mem_product.mpr ⟨hl₁, hl₂⟩, hqcross.symm⟩)

@[blueprint "lem:breaking-points-le-top-level"
  (statement := /-- For every apportionment instance $(p,H)$, the number of breaking points of
$(p,H)$ (see \cref{def:num-breaking-points}) is at most one more than the windowed complexity of
the $(H-1)$-level of the associated arrangement $\mathcal{L}(p,H)$ over the parameter window
$\delta\in[0,1]$ (see \cref{def:top-level-window-complexity}). The additive $+1$ accounts for the
terminal endpoint $\delta=1$ of the parameter window, which is always the last breaking point of
$(p,H)$ yet need not be a two-line crossing vertex of the arrangement. -/)
  (proof := /-- Let $B$ be the set of breaking points from \cref{def:breaking-points}, and let
$V$ be the set of vertices of the $(H-1)$-level whose parameter coordinate lies in $[0,1]$, as
in \cref{def:top-level-window-complexity}. By
\cref{lem:interior-breaking-point-level-vertex}, for every $\delta\in B\setminus\{1\}$ one
may choose $y_\delta$ such that $(\delta,y_\delta)\in V$. The map
$\delta\mapsto(\delta,y_\delta)$ is injective because its first coordinate is $\delta$.
The set $V$ is finite by \cref{lem:local-k-level-vertices-finite}; hence
$\#(B\setminus\{1\})\leq\#V$. Since
$B\subseteq(B\setminus\{1\})\cup\{1\}$, subadditivity of finite cardinality gives
$\#B\leq\#V+1$. Expanding \cref{def:num-breaking-points} and
\cref{def:top-level-window-complexity} yields the stated inequality. -/)
  (title := /-- Breaking points are bounded by the $(H-1)$-level complexity -/)
  (latexEnv := "lemma")]
lemma breaking_points_le_top_level (inst : apportionment_instance) :
    num_breaking_points inst ≤ top_level_window_complexity inst + 1 := by
  classical
  let S : Set ℝ := breaking_points inst \ {1}
  let V : Set (ℝ × ℝ) :=
    k_level_vertices (apportionment_arrangement inst) (inst.H - 1) ∩
      {q : ℝ × ℝ | q.1 ∈ Set.Icc (0 : ℝ) 1}
  let φ : ℝ → ℝ × ℝ := fun δ =>
    if h : δ ∈ breaking_points inst ∧ δ ≠ 1 then
      (δ, Classical.choose
        (interior_breaking_point_level_vertex inst δ h.1 h.2))
    else (δ, 0)
  have hφfst (δ : ℝ) : (φ δ).1 = δ := by
    dsimp [φ]
    split <;> rfl
  have hmap : ∀ δ ∈ S, φ δ ∈ V := by
    intro δ hδ
    have hbp : δ ∈ breaking_points inst := hδ.1
    have hne : δ ≠ 1 := by
      simpa using hδ.2
    have hwindow : δ ∈ Set.Icc (0 : ℝ) 1 := by
      have hb := hbp
      change δ ∈ Set.Ioc (0 : ℝ) 1 ∧ _ at hb
      exact ⟨le_of_lt hb.1.1, hb.1.2⟩
    dsimp [φ]
    rw [dif_pos ⟨hbp, hne⟩]
    exact ⟨Classical.choose_spec
      (interior_breaking_point_level_vertex inst δ hbp hne), hwindow⟩
  have hinj : Set.InjOn φ S := by
    intro a ha b hb hab
    have hfst := congrArg Prod.fst hab
    rw [hφfst a, hφfst b] at hfst
    exact hfst
  have hVfinite : V.Finite := by
    exact (local_k_level_vertices_finite
      (apportionment_arrangement inst) (inst.H - 1)).inter_of_left _
  have hle : S.ncard ≤ V.ncard :=
    Set.ncard_le_ncard_of_injOn φ hmap hinj hVfinite
  have himagefinite : (φ '' S).Finite := by
    apply hVfinite.subset
    rintro q ⟨δ, hδ, rfl⟩
    exact hmap δ hδ
  have hSfinite : S.Finite :=
    Set.Finite.of_finite_image himagefinite hinj
  have hsubset : breaking_points inst ⊆ S ∪ ({1} : Set ℝ) := by
    intro δ hδ
    by_cases hδone : δ = 1
    · exact Or.inr (by simpa [hδone])
    · exact Or.inl ⟨hδ, by simpa [hδone]⟩
  unfold num_breaking_points top_level_window_complexity
  change (breaking_points inst).ncard ≤ V.ncard + 1
  calc
    (breaking_points inst).ncard ≤ (S ∪ ({1} : Set ℝ)).ncard :=
      Set.ncard_le_ncard hsubset (hSfinite.union (Set.finite_singleton 1))
    _ ≤ S.ncard + ({1} : Set ℝ).ncard := Set.ncard_union_le _ _
    _ = S.ncard + 1 := by simp
    _ ≤ V.ncard + 1 := Nat.add_le_add_right hle 1

@[blueprint "lem:finite-order-statistic-rank"
  (statement := /-- Let $\alpha$ be a linearly ordered type, let $s\subseteq\alpha$ be finite,
let $f:\alpha\to\RR$ be monotone, and let $H\geq1$ satisfy
$H\leq\#s$. Then there exists $y\in\RR$ such that at least $H$ elements $x\in s$
satisfy $f(x)\leq y$, whereas fewer than $H$ elements satisfy $f(x)<y$. -/)
  (proof := /-- Enumerate $s$ increasingly and let $e$ be its element of index $H-1$.
Take $y=f(e)$. The first $H$ elements have value at most $y$ by monotonicity. Conversely,
any element whose value is strictly less than $y$ must occur strictly before $e$, and hence
among the first $H-1$ elements. The two cardinality bounds follow. -/)
  (title := /-- A finite order statistic realizes its rank cut -/)
  (latexEnv := "lemma")]
lemma finite_order_statistic_rank {α : Type} [LinearOrder α] (s : Finset α)
    (f : α → ℝ) (hf : Monotone f) {H : ℕ} (hH : 0 < H) (hcard : H ≤ s.card) :
    ∃ y : ℝ, H ≤ (s.filter fun x => f x ≤ y).card ∧
      (s.filter fun x => f x < y).card < H := by
  classical
  let e : Fin s.card ≃o {x // x ∈ s} := s.orderIsoOfFin rfl
  let j : Fin s.card := ⟨H - 1, by omega⟩
  let y : ℝ := f (e j)
  let lower : Finset α :=
    Finset.univ.image fun i : Fin H => e ⟨i, lt_of_lt_of_le i.isLt hcard⟩
  have lower_card : lower.card = H := by
    rw [Finset.card_image_iff.mpr]
    · simp [lower]
    · intro a ha b hb hab
      exact Fin.ext (congrArg (fun z : Fin s.card => z.val)
        (e.injective (Subtype.ext hab)))
  have lower_subset : lower ⊆ s.filter fun x => f x ≤ y := by
    intro x hx
    simp only [lower, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    simp only [Finset.mem_filter, (e ⟨i, lt_of_lt_of_le i.isLt hcard⟩).property,
      true_and, y]
    apply hf
    exact e.monotone (by simp [j]; omega)
  refine ⟨y, ?_, ?_⟩
  · rw [← lower_card]
    exact Finset.card_le_card lower_subset
  · let upper : Finset α :=
      Finset.univ.image fun i : Fin (H - 1) =>
        e ⟨i, lt_of_lt_of_le i.isLt (by omega)⟩
    have upper_card : upper.card = H - 1 := by
      rw [Finset.card_image_iff.mpr]
      · simp [upper]
      · intro a ha b hb hab
        exact Fin.ext (congrArg (fun z : Fin s.card => z.val)
          (e.injective (Subtype.ext hab)))
    have upper_subset : (s.filter fun x => f x < y) ⊆ upper := by
      intro x hx
      have hxs : x ∈ s := (Finset.mem_filter.mp hx).1
      let i : Fin s.card := e.symm ⟨x, hxs⟩
      have hix : (e i : α) = x := by simp [i]
      have hij : i < j := by
        by_contra hn
        have hji : j ≤ i := le_of_not_gt hn
        have hmono : f (e j) ≤ f (e i) := hf (e.monotone hji)
        exact (not_le_of_gt (Finset.mem_filter.mp hx).2) (by simpa [y, hix] using hmono)
      simp only [upper, Finset.mem_image, Finset.mem_univ, true_and]
      change i.val < H - 1 at hij
      exact ⟨⟨i, hij⟩, hix⟩
    have hc := Finset.card_le_card upper_subset
    rw [upper_card] at hc
    omega

@[blueprint "lem:apportionment-arrangement-card"
  (statement := /-- The indexed line arrangement associated with an apportionment instance
having $n$ states and house size $H$ has exactly $nH$ elements. -/)
  (proof := /-- By \cref{def:apportionment-arrangement}, the arrangement is the image of the
$nH$ pairs $(i,t)$ with
$i\in\{0,\ldots,n-1\}$ and $t\in\{0,\ldots,H-1\}$. Its label $iH+t$ determines
$t$ by reduction modulo $H$ and then determines $i$ by division by $H$. Since $H>0$,
the labeling map is injective, so taking its image preserves the product cardinality. -/)
  (title := /-- Cardinality of the apportionment line arrangement -/)
  (latexEnv := "lemma")]
lemma apportionment_arrangement_card (inst : apportionment_instance) :
    (apportionment_arrangement inst).card = inst.n * inst.H := by
  classical
  unfold apportionment_arrangement
  rw [Finset.card_image_iff.mpr]
  · simp
  · rintro ⟨i, t⟩ hit ⟨j, u⟩ hju hpair
    have ht : t < inst.H := by
      exact Finset.mem_range.mp (Finset.mem_product.mp hit).2
    have hu : u < inst.H := by
      exact Finset.mem_range.mp (Finset.mem_product.mp hju).2
    have hlabel : i.val * inst.H + t = j.val * inst.H + u :=
      congrArg Prod.fst hpair
    have htu : t = u := by
      have hmod := congrArg (fun z => z % inst.H) hlabel
      simpa [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ht,
        Nat.mod_eq_of_lt hu] using hmod
    have hij : i.val = j.val := by
      have hdiv := congrArg (fun z => z / inst.H) hlabel
      have hi : (i.val * inst.H + t) / inst.H = i.val := by
        rw [Nat.mul_comm i.val inst.H, Nat.mul_add_div inst.hH,
          Nat.div_eq_of_lt ht, Nat.add_zero]
      have hj : (j.val * inst.H + u) / inst.H = j.val := by
        rw [Nat.mul_comm j.val inst.H, Nat.mul_add_div inst.hH,
          Nat.div_eq_of_lt hu, Nat.add_zero]
      exact hi.symm.trans (hdiv.trans hj)
    exact Prod.ext (Fin.ext hij) htu

@[blueprint "lem:apportionment-endpoint-shift-card"
  (statement := /-- Let $P$ be any decidable predicate on real line values. Among the indexed
lines of an apportionment instance, the number satisfying $P$ at parameter $0$ is at most
the number satisfying $P$ at parameter $1$, plus the number $n$ of states. -/)
  (proof := /-- Use the indexing by pairs $(i,t)$ from
\cref{def:apportionment-arrangement}. A line with $t=0$ is sent to its state
$i$, giving at most $n$ exceptional images. A line with $t>0$ is sent to the indexed line
$(i,t-1)$. The identity $\ell_{i,t-1}(1)=\ell_{i,t}(0)$ shows that the latter line satisfies
$P$ at parameter $1$. The map is injective on both cases, and its two cases have disjoint
images, which proves the cardinality inequality. -/)
  (title := /-- Endpoint shift estimate for indexed apportionment lines -/)
  (latexEnv := "lemma")]
lemma apportionment_endpoint_shift_card (inst : apportionment_instance)
    (P : ℝ → Prop) [DecidablePred P] :
    ((apportionment_arrangement inst).filter fun l => P (line_value l.2 0)).card ≤
      ((apportionment_arrangement inst).filter fun l => P (line_value l.2 1)).card + inst.n := by
  classical
  let I : Finset (Fin inst.n × ℕ) := Finset.univ ×ˢ Finset.range inst.H
  let φ (it : Fin inst.n × ℕ) : ℕ × line :=
    (it.1.val * inst.H + it.2,
      { slope := 1 / (inst.p it.1 : ℝ),
        intercept := (it.2 : ℝ) / (inst.p it.1 : ℝ) })
  have φ_inj : Set.InjOn φ I := by
    rintro ⟨i, t⟩ hit ⟨j, u⟩ hju hpair
    have ht : t < inst.H := Finset.mem_range.mp (Finset.mem_product.mp hit).2
    have hu : u < inst.H := Finset.mem_range.mp (Finset.mem_product.mp hju).2
    have hlabel : i.val * inst.H + t = j.val * inst.H + u :=
      congrArg Prod.fst hpair
    have htu : t = u := by
      have hmod := congrArg (fun z => z % inst.H) hlabel
      simpa [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ht,
        Nat.mod_eq_of_lt hu] using hmod
    have hij : i.val = j.val := by
      have hdiv := congrArg (fun z => z / inst.H) hlabel
      have hi : (i.val * inst.H + t) / inst.H = i.val := by
        rw [Nat.mul_comm i.val inst.H, Nat.mul_add_div inst.hH,
          Nat.div_eq_of_lt ht, Nat.add_zero]
      have hj : (j.val * inst.H + u) / inst.H = j.val := by
        rw [Nat.mul_comm j.val inst.H, Nat.mul_add_div inst.hH,
          Nat.div_eq_of_lt hu, Nat.add_zero]
      exact hi.symm.trans (hdiv.trans hj)
    exact Prod.ext (Fin.ext hij) htu
  let S₀ : Finset (Fin inst.n × ℕ) :=
    I.filter fun it => P (line_value (φ it).2 0)
  let S₁ : Finset (Fin inst.n × ℕ) :=
    I.filter fun it => P (line_value (φ it).2 1)
  have card_zero :
      ((apportionment_arrangement inst).filter fun l => P (line_value l.2 0)).card =
        S₀.card := by
    change ((I.image φ).filter fun l => P (line_value l.2 0)).card = S₀.card
    rw [Finset.filter_image]
    exact Finset.card_image_iff.mpr fun a ha b hb hab =>
      φ_inj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab
  have card_one :
      ((apportionment_arrangement inst).filter fun l => P (line_value l.2 1)).card =
        S₁.card := by
    change ((I.image φ).filter fun l => P (line_value l.2 1)).card = S₁.card
    rw [Finset.filter_image]
    exact Finset.card_image_iff.mpr fun a ha b hb hab =>
      φ_inj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab
  let shift : {x // x ∈ S₀} → Fin inst.n ⊕ {x // x ∈ S₁} := fun x =>
    if ht : x.1.2 = 0 then Sum.inl x.1.1
    else Sum.inr ⟨(x.1.1, x.1.2 - 1), by
      have hx := Finset.mem_filter.mp x.2
      have hI := Finset.mem_product.mp hx.1
      have htH := Finset.mem_range.mp hI.2
      have htpos : 0 < x.1.2 := Nat.pos_of_ne_zero ht
      have hpR : (inst.p x.1.1 : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt (inst.hp x.1.1)
      have hval :
          line_value (φ (x.1.1, x.1.2 - 1)).2 1 =
            line_value (φ x.1).2 0 := by
        simp only [φ, line_value]
        field_simp [hpR]
        norm_cast
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_univ _, Finset.mem_range.mpr (by omega)⟩, hval ▸ hx.2⟩⟩
  have shift_inj : Function.Injective shift := by
    intro a b hab
    by_cases ha : a.1.2 = 0 <;> by_cases hb : b.1.2 = 0
    · simp only [shift, dif_pos ha, dif_pos hb, Sum.inl.injEq] at hab
      apply Subtype.ext
      exact Prod.ext hab (ha.trans hb.symm)
    · simp [shift, ha, hb] at hab
    · simp [shift, ha, hb] at hab
    · simp only [shift, dif_neg ha, dif_neg hb, Sum.inr.injEq, Subtype.mk.injEq,
        Prod.mk.injEq] at hab
      apply Subtype.ext
      apply Prod.ext hab.1
      omega
  have hc := Fintype.card_le_of_injective shift shift_inj
  rw [card_zero, card_one]
  simpa [Nat.add_comm] using hc

@[blueprint "lem:k-level-vertices-finite"
  (statement := /-- For every finite indexed line arrangement $A$ and every level index $k$,
the set of vertices of the $k$-level of $A$ is finite. -/)
  (proof := /-- Associate to each ordered pair of indexed lines the point obtained by solving
their affine intersection equation. There are finitely many such pairs. If two distinct affine
lines pass through a common point, then their slopes are distinct, and solving the two linear
equations shows that the common point is the associated intersection point. Every vertex from
\cref{def:k-level-vertices} therefore belongs to this finite image. -/)
  (title := /-- Finiteness of every level's vertex set -/)
  (latexEnv := "lemma")]
lemma k_level_vertices_finite (A : line_arrangement) (k : ℕ) :
    (k_level_vertices A k).Finite := by
  classical
  let cross (ls : (ℕ × line) × (ℕ × line)) : ℝ × ℝ :=
    let x := (ls.2.2.intercept - ls.1.2.intercept) /
      (ls.1.2.slope - ls.2.2.slope)
    (x, line_value ls.1.2 x)
  let V : Finset (ℝ × ℝ) := (A ×ˢ A).image cross
  apply V.finite_toSet.subset
  intro q hq
  obtain ⟨⟨l₁, hl₁, l₂, hl₂, hne, hv₁, hv₂⟩, hlevel⟩ := hq
  have hs : l₁.2.slope ≠ l₂.2.slope := by
    intro heq
    have hi : l₁.2.intercept = l₂.2.intercept := by
      simp only [line_value] at hv₁ hv₂
      rw [heq] at hv₁
      linarith
    apply hne
    have hli : Function.Injective (fun l : line => (l.slope, l.intercept)) := by
      intro a b h
      cases a
      cases b
      simp_all
    exact hli (Prod.ext heq hi)
  have hx :
      q.1 = (l₂.2.intercept - l₁.2.intercept) /
        (l₁.2.slope - l₂.2.slope) := by
    apply (eq_div_iff (sub_ne_zero.mpr hs)).2
    simp only [line_value] at hv₁ hv₂
    linarith
  have hqcross : q = cross (l₁, l₂) := by
    apply Prod.ext
    · simpa [cross] using hx
    · simp only [cross]
      rw [← hv₁, hx]
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr
    ⟨(l₁, l₂), Finset.mem_product.mpr ⟨hl₁, hl₂⟩, hqcross.symm⟩)

@[blueprint "lem:k-level-complexity-card-bound"
  (statement := /-- For every finite indexed line arrangement $A$ and every
$k\in\NN_0$, the complexity of the $k$-level is at most $(\#A)^2$. -/)
  (proof := /-- By \cref{lem:k-level-vertices-finite}, the vertex set is finite. For every
vertex choose an ordered pair of indexed elements of $A$ carrying two distinct affine lines
through that vertex, as permitted by \cref{def:k-level-vertices}. Two affine lines which are
not identical have at most one common point, so two different vertices cannot be assigned the
same ordered pair. This gives an injection from the $k$-level vertex set into $A\times A$.
The latter has cardinality $(\#A)^2$, and the assertion follows from
\cref{def:k-level-complexity}. -/)
  (title := /-- Quadratic cardinality bound for a level -/)
  (latexEnv := "lemma")]
lemma k_level_complexity_card_bound (A : line_arrangement) (k : ℕ) :
    k_level_complexity A k ≤ A.card ^ 2 := by
  classical
  let Q := {q // q ∈ k_level_vertices A k}
  have hQfinite : (k_level_vertices A k).Finite := k_level_vertices_finite A k
  letI : Fintype Q := hQfinite.fintype
  choose l₁ hl₁ l₂ hl₂ hne hv₁ hv₂ using fun q : Q => q.2.1
  let f : Q → {l // l ∈ A} × {l // l ∈ A} := fun q =>
    (⟨l₁ q, hl₁ q⟩, ⟨l₂ q, hl₂ q⟩)
  have hs (q : Q) : (l₁ q).2.slope ≠ (l₂ q).2.slope := by
    intro heq
    have hi : (l₁ q).2.intercept = (l₂ q).2.intercept := by
      have hq₁ := hv₁ q
      have hq₂ := hv₂ q
      simp only [line_value] at hq₁ hq₂
      rw [heq] at hq₁
      linarith
    apply hne q
    cases h₁ : (l₁ q).2
    cases h₂ : (l₂ q).2
    simp_all
  have hx (q : Q) :
      q.1.1 = ((l₂ q).2.intercept - (l₁ q).2.intercept) /
        ((l₁ q).2.slope - (l₂ q).2.slope) := by
    apply (eq_div_iff (sub_ne_zero.mpr (hs q))).2
    have hq₁ := hv₁ q
    have hq₂ := hv₂ q
    simp only [line_value] at hq₁ hq₂
    linarith
  have hf : Function.Injective f := by
    intro q r hqr
    have h₁ : l₁ q = l₁ r := congrArg (fun p => p.1.1) hqr
    have h₂ : l₂ q = l₂ r := congrArg (fun p => p.2.1) hqr
    have hfirst : q.1.1 = r.1.1 := by
      rw [hx q, hx r, h₁, h₂]
    apply Subtype.ext
    apply Prod.ext hfirst
    rw [← hv₁ q, ← hv₁ r, h₁, hfirst]
  calc
    k_level_complexity A k = Fintype.card Q := by
      simp [k_level_complexity, Q]
    _ ≤ Fintype.card ({l // l ∈ A} × {l // l ∈ A}) :=
      Fintype.card_le_of_injective f hf
    _ = A.card ^ 2 := by simp [pow_two]

@[blueprint "lem:reduction-lines"
  (statement := /-- For every apportionment instance $(p,H)$ with $n$ states there exists a line
arrangement $A'$ (see \cref{def:line-arrangement}) with at most $2n-1$ lines, together with an
index $k\in\NN_0$ satisfying $k\le \#A'$, such that the complexity of the $k$-level of $A'$ (see
\cref{def:k-level-complexity}) is at least the windowed complexity of the $(H-1)$-level of the
associated arrangement $\mathcal{L}(p,H)$ over the parameter window $\delta\in[0,1]$ (see
\cref{def:top-level-window-complexity}). -/)
  (proof := /-- Let $L=\mathcal{L}(p,H)$ be the indexed arrangement of
\cref{def:apportionment-arrangement}. By \cref{lem:apportionment-arrangement-card},
$\#L=nH\ge H$. Apply \cref{lem:finite-order-statistic-rank} to the line values at parameters
$0$ and $1$. This gives $y_0,y_1\in\RR$ such that, at parameter $s\in\{0,1\}$, at least
$H$ lines have value at most $y_s$, whereas fewer than $H$ lines have value strictly less than
$y_s$. Every line of $L$ has positive slope. If $y_1\le y_0$, the $H$ lines whose values at
$1$ are at most $y_1$ would all have values at $0$ strictly below $y_0$, contradicting the rank
condition at $0$. Hence $y_0<y_1$.

Let
\[
 R=\{\ell\in L:\ell(1)\le y_0\},\qquad
 B=\{\ell\in L:\ell(0)<y_1\},
\]
and retain the band
\[
 A'=\{\ell\in L:y_0<\ell(1)\ \text{and}\ \ell(0)<y_1\}.
\]
The endpoint-shift estimate \cref{lem:apportionment-endpoint-shift-card}, applied first to the
predicate $z\le y_0$ and then to $z<y_1$, yields
\[
 H\le \#R+n,\qquad \#B\le H-1+n.
\]
The sets $A'$ and $R$ are disjoint and their union is contained in $B$. Therefore
$\#A'+\#R\le\#B$, and the preceding two inequalities give $\#A'\le2n-1$. Moreover, every
line whose value at $0$ is at most $y_0$ belongs to $A'\cup R$, so
$H\le\#A'+\#R$. Since $R$ is contained in the set of lines whose value at $1$ is strictly
less than $y_1$, one also has $\#R<H$. Thus
\[
 k=H-1-\#R
\]
is a natural number satisfying $k\le\#A'$.

Let $q=(\delta,y)$ be a vertex counted by
\cref{def:top-level-window-complexity}. The incidence inequalities of
\cref{def:k-level-vertices} imply that at most $H-1$ lines lie strictly below $q$ and at least
$H$ lie at or below it. Comparing these inequalities with the endpoint rank conditions, using
$0\le\delta\le1$ and positivity of every slope, gives $y_0\le y\le y_1$. At
$\delta=0$ one additionally has $y\le y_0$, and at $\delta=1$ one has $y_1\le y$.
Consequently every line of $R$ lies strictly below $q$. Conversely, a line of $L$ outside both
$R$ and $A'$ satisfies $\ell(0)\ge y_1$ and lies strictly above $q$. Hence every line through
$q$ is retained, and the lines below $q$ decompose as the disjoint union of $R$ and the retained
lines below $q$.

If $b$ and $r$ denote, respectively, the numbers of retained lines below and through $q$, the
original incidence inequalities become
\[
 \#R+b\le H-1<\#R+b+r.
\]
After subtracting $\#R$, these are precisely $b\le k<b+r$, so $q$ is a vertex of the global
$k$-level of $A'$. Thus the windowed source vertex set is contained in the target vertex set.
The latter is finite by \cref{lem:k-level-vertices-finite}; taking finite cardinalities and
using \cref{def:k-level-complexity} proves the claimed inequality. -/)
  (title := /-- Reduction to an arrangement of at most $2n-1$ lines -/)
  (latexEnv := "lemma")]
lemma reduction_lines (inst : apportionment_instance) :
    ∃ A : line_arrangement, A.card ≤ 2 * inst.n - 1 ∧
      ∃ k : ℕ, k ≤ A.card ∧
        top_level_window_complexity inst ≤
          k_level_complexity A k := by
  classical
  let L := apportionment_arrangement inst
  have hLcard : L.card = inst.n * inst.H := by
    simpa [L] using apportionment_arrangement_card inst
  have hHcard : inst.H ≤ L.card := by
    rw [hLcard]
    exact Nat.le_mul_of_pos_left inst.H inst.hn
  have endpoint_rank (δ : ℝ) :
      ∃ y : ℝ, inst.H ≤ (L.filter fun l => line_value l.2 δ ≤ y).card ∧
        (L.filter fun l => line_value l.2 δ < y).card < inst.H := by
    let key (l : ℕ × line) : ℝ ×ₗ (ℕ ×ₗ (ℝ ×ₗ ℝ)) :=
      toLex (line_value l.2 δ,
        toLex (l.1, toLex (l.2.slope, l.2.intercept)))
    have key_inj : Function.Injective key := by
      rintro ⟨na, ⟨sa, ba⟩⟩ ⟨nb, ⟨sb, bb⟩⟩ h
      simp only [key, line_value, Prod.mk.injEq] at h
      simp only [Prod.mk.injEq, line.mk.injEq]
      aesop
    letI : LinearOrder (ℕ × line) := LinearOrder.lift' key key_inj
    apply finite_order_statistic_rank L (fun l => line_value l.2 δ) ?_
      inst.hH hHcard
    intro a b hab
    change key a ≤ key b at hab
    simpa [key] using Prod.Lex.monotone_fst (key a) (key b) hab
  obtain ⟨y₀, h₀le, h₀lt⟩ := endpoint_rank 0
  obtain ⟨y₁, h₁le, h₁lt⟩ := endpoint_rank 1
  have slope_pos {l : ℕ × line} (hl : l ∈ L) : 0 < l.2.slope := by
    change l ∈ apportionment_arrangement inst at hl
    unfold apportionment_arrangement at hl
    obtain ⟨⟨i, t⟩, hit, rfl⟩ := Finset.mem_image.mp hl
    change 0 < 1 / (inst.p i : ℝ)
    have hp : (0 : ℝ) < inst.p i := by exact_mod_cast inst.hp i
    positivity
  have value_strict {l : ℕ × line} (hl : l ∈ L) :
      line_value l.2 0 < line_value l.2 1 := by
    have hs := slope_pos hl
    simp only [line_value]
    linarith
  have hy : y₀ < y₁ := by
    by_contra hn
    have hsub :
        (L.filter fun l => line_value l.2 1 ≤ y₁) ⊆
          L.filter fun l => line_value l.2 0 < y₀ := by
      intro l hl
      have hm := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨hm.1, lt_of_lt_of_le (value_strict hm.1)
        (hm.2.trans (le_of_not_gt hn))⟩
    have hc := Finset.card_le_card hsub
    omega
  let R := L.filter fun l => line_value l.2 1 ≤ y₀
  let B := L.filter fun l => line_value l.2 0 < y₁
  let A := L.filter fun l => y₀ < line_value l.2 1 ∧ line_value l.2 0 < y₁
  have hdis : Disjoint A R := by
    rw [Finset.disjoint_left]
    intro l hA hR
    simp only [A, R, Finset.mem_filter] at hA hR
    linarith [hA.2.1, hR.2]
  have hunion : A ∪ R ⊆ B := by
    intro l hl
    simp only [Finset.mem_union] at hl
    rcases hl with hA | hR
    · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hA).1,
        (Finset.mem_filter.mp hA).2.2⟩
    · have hm := Finset.mem_filter.mp hR
      exact Finset.mem_filter.mpr ⟨hm.1,
        lt_of_lt_of_le (value_strict hm.1) (hm.2.trans hy.le)⟩
  have hsum : A.card + R.card ≤ B.card := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact Finset.card_le_card hunion
  have hRlower : inst.H ≤ R.card + inst.n := by
    have hs := apportionment_endpoint_shift_card inst (fun z => z ≤ y₀)
    change (L.filter fun l => line_value l.2 0 ≤ y₀).card ≤ R.card + inst.n at hs
    exact h₀le.trans hs
  have hBupper : B.card ≤ inst.H - 1 + inst.n := by
    have hs := apportionment_endpoint_shift_card inst (fun z => z < y₁)
    change B.card ≤ (L.filter fun l => line_value l.2 1 < y₁).card + inst.n at hs
    omega
  have hAcard : A.card ≤ 2 * inst.n - 1 := by omega
  have hARlower : inst.H ≤ A.card + R.card := by
    have hsub :
        (L.filter fun l => line_value l.2 0 ≤ y₀) ⊆ A ∪ R := by
      intro l hl
      have hm := Finset.mem_filter.mp hl
      by_cases hb : line_value l.2 1 ≤ y₀
      · exact Finset.mem_union_right A (Finset.mem_filter.mpr ⟨hm.1, hb⟩)
      · exact Finset.mem_union_left R (Finset.mem_filter.mpr
          ⟨hm.1, lt_of_not_ge hb, lt_of_le_of_lt hm.2 hy⟩)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis] at hc
    exact h₀le.trans hc
  have hRlt : R.card < inst.H := by
    have hsub : R ⊆ L.filter fun l => line_value l.2 1 < y₁ := by
      intro l hl
      have hm := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨hm.1, lt_of_le_of_lt hm.2 hy⟩
    exact (Finset.card_le_card hsub).trans_lt h₁lt
  let k := inst.H - 1 - R.card
  have hk : k ≤ A.card := by
    dsimp [k]
    omega
  refine ⟨A, hAcard, k, hk, ?_⟩
  unfold top_level_window_complexity k_level_complexity
  apply Set.ncard_le_ncard ?_ (k_level_vertices_finite A k)
  intro q hq
  obtain ⟨hqlevel, hwindow⟩ := hq
  change q ∈ k_level_vertices L (inst.H - 1) at hqlevel
  simp only [Set.mem_setOf_eq, Set.mem_Icc] at hwindow
  obtain ⟨⟨l₁, hl₁, l₂, hl₂, hne, hv₁, hv₂⟩, hbelow, htotal⟩ := hqlevel
  let BL := L.filter fun l => line_value l.2 q.1 < q.2
  let OL := L.filter fun l => line_value l.2 q.1 = q.2
  let QL := L.filter fun l => line_value l.2 q.1 ≤ q.2
  change BL.card ≤ inst.H - 1 at hbelow
  change inst.H - 1 < BL.card + OL.card at htotal
  have hdisLO : Disjoint BL OL := by
    rw [Finset.disjoint_left]
    intro l hb ho
    simp only [BL, OL, Finset.mem_filter] at hb ho
    linarith
  have hQL : QL = BL ∪ OL := by
    ext l
    simp only [QL, BL, OL, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hm
      rcases lt_or_eq_of_le hm.2 with hlt | heq
      · exact Or.inl ⟨hm.1, hlt⟩
      · exact Or.inr ⟨hm.1, heq⟩
    · rintro (hm | hm)
      · exact ⟨hm.1, hm.2.le⟩
      · exact ⟨hm.1, hm.2.le⟩
  have hQLcard : inst.H ≤ QL.card := by
    rw [hQL, Finset.card_union_of_disjoint hdisLO]
    omega
  have hy₀q : y₀ ≤ q.2 := by
    by_contra hn
    have hsub : QL ⊆ L.filter fun l => line_value l.2 0 < y₀ := by
      intro l hl
      have hm := Finset.mem_filter.mp hl
      have hs := slope_pos hm.1
      have hmono : line_value l.2 0 ≤ line_value l.2 q.1 := by
        simp only [line_value]
        nlinarith [hwindow.1]
      exact Finset.mem_filter.mpr ⟨hm.1,
        lt_of_le_of_lt hmono (lt_of_le_of_lt hm.2 (lt_of_not_ge hn))⟩
    have hc := Finset.card_le_card hsub
    omega
  have hqy₁ : q.2 ≤ y₁ := by
    by_contra hn
    have hsub :
        (L.filter fun l => line_value l.2 1 ≤ y₁) ⊆ BL := by
      intro l hl
      have hm := Finset.mem_filter.mp hl
      have hs := slope_pos hm.1
      have hmono : line_value l.2 q.1 ≤ line_value l.2 1 := by
        simp only [line_value]
        nlinarith [hwindow.2]
      exact Finset.mem_filter.mpr ⟨hm.1,
        lt_of_le_of_lt (hmono.trans hm.2) (lt_of_not_ge hn)⟩
    have hc := Finset.card_le_card hsub
    omega
  have at_zero_upper (hx : q.1 = 0) : q.2 ≤ y₀ := by
    by_contra hn
    have hsub :
        (L.filter fun l => line_value l.2 0 ≤ y₀) ⊆ BL := by
      intro l hl
      have hm := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨hm.1, by
        rw [hx]
        exact lt_of_le_of_lt hm.2 (lt_of_not_ge hn)⟩
    have hc := Finset.card_le_card hsub
    omega
  have at_one_lower (hx : q.1 = 1) : y₁ ≤ q.2 := by
    by_contra hn
    have hsub : QL ⊆ L.filter fun l => line_value l.2 1 < y₁ := by
      intro l hl
      have hm := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨hm.1, by
        rw [← hx]
        exact lt_of_le_of_lt hm.2 (lt_of_not_ge hn)⟩
    have hc := Finset.card_le_card hsub
    omega
  have hRbelow : R ⊆ BL := by
    intro l hl
    have hm := Finset.mem_filter.mp hl
    have hs := slope_pos hm.1
    apply Finset.mem_filter.mpr
    refine ⟨hm.1, ?_⟩
    by_cases hx : q.1 = 1
    · rw [hx]
      exact lt_of_le_of_lt hm.2 (hy.trans_le (at_one_lower hx))
    · have hxl : q.1 < 1 := lt_of_le_of_ne hwindow.2 hx
      have hvlt : line_value l.2 q.1 < line_value l.2 1 := by
        simp only [line_value]
        nlinarith
      exact lt_of_lt_of_le hvlt (hm.2.trans hy₀q)
  have outside_above {l : ℕ × line} (hl : l ∈ L) (hnA : l ∉ A) (hnR : l ∉ R) :
      q.2 < line_value l.2 q.1 := by
    have hlow : y₀ < line_value l.2 1 := by
      by_contra hn
      exact hnR (Finset.mem_filter.mpr ⟨hl, le_of_not_gt hn⟩)
    have hhigh : y₁ ≤ line_value l.2 0 := by
      by_contra hn
      exact hnA (Finset.mem_filter.mpr
        ⟨hl, hlow, lt_of_not_ge hn⟩)
    have hs := slope_pos hl
    by_cases hx : q.1 = 0
    · rw [hx]
      exact (at_zero_upper hx).trans_lt (hy.trans_le hhigh)
    · have hxpos : 0 < q.1 := lt_of_le_of_ne hwindow.1 (Ne.symm hx)
      have hvlt : line_value l.2 0 < line_value l.2 q.1 := by
        simp only [line_value]
        nlinarith
      exact hqy₁.trans_lt (hhigh.trans_lt hvlt)
  have incident_mem {l : ℕ × line} (hl : l ∈ L)
      (hv : line_value l.2 q.1 = q.2) : l ∈ A := by
    by_contra hnA
    by_cases hR : l ∈ R
    · have hb := Finset.mem_filter.mp (hRbelow hR)
      linarith
    · have ha := outside_above hl hnA hR
      linarith
  let BA := A.filter fun l => line_value l.2 q.1 < q.2
  let OA := A.filter fun l => line_value l.2 q.1 = q.2
  have hBL : BL = R ∪ BA := by
    ext l
    constructor
    · intro hl
      have hm := Finset.mem_filter.mp hl
      by_cases hR : l ∈ R
      · exact Finset.mem_union_left BA hR
      · by_cases hA : l ∈ A
        · exact Finset.mem_union_right R (Finset.mem_filter.mpr ⟨hA, hm.2⟩)
        · have ha := outside_above hm.1 hA hR
          linarith
    · intro hl
      rcases Finset.mem_union.mp hl with hR | hA
      · exact hRbelow hR
      · have hm := Finset.mem_filter.mp hA
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm.1).1, hm.2⟩
  have hdisRBA : Disjoint R BA := by
    rw [Finset.disjoint_left]
    intro l hR hA
    exact Finset.disjoint_left.mp hdis (Finset.mem_filter.mp hA).1 hR
  have hBLcard : BL.card = R.card + BA.card := by
    rw [hBL, Finset.card_union_of_disjoint hdisRBA]
  have hOL : OL = OA := by
    ext l
    constructor
    · intro hl
      have hm := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨incident_mem hm.1 hm.2, hm.2⟩
    · intro hl
      have hm := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm.1).1, hm.2⟩
  refine ⟨⟨l₁, incident_mem hl₁ hv₁, l₂, incident_mem hl₂ hv₂,
    hne, hv₁, hv₂⟩, ?_, ?_⟩
  · change BA.card ≤ k
    dsimp [k]
    rw [hBLcard] at hbelow
    omega
  · change k < BA.card + OA.card
    dsimp [k]
    rw [hBLcard, hOL] at htotal
    omega

@[blueprint "def:regular-k-level-crossings"
  (statement := /-- Let $A$ be an indexed line arrangement and let $k,r\in\NN_0$. The set
$R_{k,r}(A)$ of \emph{regular $k$-level crossings of lower rank $r$} consists of the points
$q=(\delta,y)$ which are vertices of the $k$-level of $A$ (see
\cref{def:k-level-vertices}), whose parameter satisfies $0<\delta<1$, through which exactly two
indexed lines of $A$ pass, and below which exactly $r$ indexed lines of $A$ pass. The last
condition records the strict-below count, rather than only membership in the closed $k$-level:
at a simple crossing the latter permits both $r=k$ and $r+1=k$. -/)
  (title := /-- Regular $k$-level crossings with prescribed lower rank -/)
  (latexEnv := "definition")]
def regular_k_level_crossings (A : line_arrangement) (k r : ℕ) : Set (ℝ × ℝ) :=
  { q |
      q ∈ k_level_vertices A k ∧
      q.1 ∈ Set.Ioo (0 : ℝ) 1 ∧
      (A.filter (fun l => line_value l.2 q.1 = q.2)).card = 2 ∧
      (A.filter (fun l => line_value l.2 q.1 < q.2)).card = r }

@[blueprint "def:stable-k-level-perturbation-data"
  (statement := /-- Let $A$ be an indexed line arrangement and let $k\in\NN_0$. A
\emph{stable $k$-level perturbation datum} consists of an indexed line arrangement $A'$ with
$\#A'=\#A$ and an injective map from the $k$-level vertices of $A$ into
\[
 R_{k,k}(A')\cup R_{k,k-1}(A'),
\]
where the regular crossing sets are those of \cref{def:regular-k-level-crossings}. In addition,
the first-coordinate projection must be injective on this entire union. Thus every original
level vertex is retained as a distinct simple crossing of one of the two admissible
strict-below ranks, and no two retained regular crossings have the same abscissa. -/)
  (title := /-- Stable perturbation data for a level -/)
  (latexEnv := "definition")]
def stable_k_level_perturbation_data (A : line_arrangement) (k : ℕ) : Prop :=
  ∃ A' : line_arrangement,
    A'.card = A.card ∧
    Set.InjOn (fun q : ℝ × ℝ => q.1)
      (regular_k_level_crossings A' k k ∪ regular_k_level_crossings A' k (k - 1)) ∧
    ∃ φ : ℝ × ℝ → ℝ × ℝ,
      Set.MapsTo φ (k_level_vertices A k)
        (regular_k_level_crossings A' k k ∪ regular_k_level_crossings A' k (k - 1)) ∧
      Set.InjOn φ (k_level_vertices A k)

@[blueprint "def:k-level-witnessed-by"
  (statement := /-- A function $h:\NN_0\to\RR$ \emph{stably witnesses a $k$-level lower
bound} if there exist a constant $c>0$ and a threshold $N\in\NN_0$ such that for every
$m\ge N$ there are a line arrangement $A$ with exactly $m$ indexed lines and an index
$k\le m$ for which
\[
 c h(m)\le \operatorname{comp}_k(A),
\]
and $A$ carries stable $k$-level perturbation data in the sense of
\cref{def:stable-k-level-perturbation-data}. The last requirement explicitly records the
generic-perturbation input needed to transfer the lower-bound witness to an apportionment
instance. -/)
  (title := /-- Stable $\Omega(h)$ witnesses for $k$-level complexity -/)
  (latexEnv := "definition")]
def k_level_witnessed_by (h : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ A : line_arrangement, A.card = m ∧
    ∃ k : ℕ, k ≤ m ∧ c * h m ≤ (k_level_complexity A k : ℝ) ∧
      stable_k_level_perturbation_data A k

@[blueprint "lem:k-level-stable-regularization"
  (statement := /-- Let $A$ be a finite indexed line arrangement, let $k\in\NN_0$, and suppose
that $A$ carries stable perturbation data as in
\cref{def:stable-k-level-perturbation-data}. Then there exist an indexed line arrangement $A'$ with
$|A'|=|A|$ and an integer $r\in\NN_0$ such that $r=k$ or $r+1=k$, the first-coordinate
projection is injective on the regular crossing set $R_{k,r}(A')$ of
\cref{def:regular-k-level-crossings}, and
\[
 \operatorname{comp}_k(A)\leq 2\,|R_{k,r}(A')|.
\]
Thus a single one of the two possible strict-below ranks contains at least half of the retained
vertices. -/)
  (proof := /-- Let $V$ be the set of $k$-level vertices of $A$. It is finite by
\cref{lem:k-level-vertices-finite}. Unpack the stable perturbation datum from
\cref{def:stable-k-level-perturbation-data}, obtaining $A'$ and an injective map
\[
 V\longrightarrow R_{k,k}(A')\cup R_{k,k-1}(A').
\]
Consequently,
\[
 |V|\leq |R_{k,k}(A')|+|R_{k,k-1}(A')|.
\]
At least one summand is therefore at least $|V|/2$. If the first summand has this property, set
$r=k$. Otherwise set $r=k-1$; when $k>0$ this gives $r+1=k$, while for $k=0$ it again gives
$r=k$. The first-coordinate projection is injective on the chosen crossing set because the
perturbation datum makes it injective on their union. Since
$|V|=\operatorname{comp}_k(A)$ by \cref{def:k-level-complexity}, the selected rank satisfies
$\operatorname{comp}_k(A)\leq 2|R_{k,r}(A')|$. -/)
  (title := /-- Stable regularization of a possibly degenerate $k$-level -/)
  (latexEnv := "lemma")]
lemma k_level_stable_regularization (A : line_arrangement) (k : ℕ)
    (hstable : stable_k_level_perturbation_data A k) :
    ∃ A' : line_arrangement, ∃ r : ℕ,
      A'.card = A.card ∧
      (r = k ∨ r + 1 = k) ∧
      Set.InjOn (fun q : ℝ × ℝ => q.1) (regular_k_level_crossings A' k r) ∧
      (k_level_complexity A k : ℝ) ≤
        2 * ((regular_k_level_crossings A' k r).ncard : ℝ) := by
  obtain ⟨A', hcard, hinj, φ, hmap, hφ⟩ := hstable
  have hRk : (regular_k_level_crossings A' k k).Finite :=
    (k_level_vertices_finite A' k).subset (fun q hq => hq.1)
  have hRkm : (regular_k_level_crossings A' k (k - 1)).Finite :=
    (k_level_vertices_finite A' k).subset (fun q hq => hq.1)
  have hU : (regular_k_level_crossings A' k k ∪
      regular_k_level_crossings A' k (k - 1)).Finite :=
    hRk.union hRkm
  have hle : (k_level_vertices A k).ncard ≤
      (regular_k_level_crossings A' k k ∪
        regular_k_level_crossings A' k (k - 1)).ncard :=
    Set.ncard_le_ncard_of_injOn φ hmap hφ hU
  have hsum : (k_level_vertices A k).ncard ≤
      (regular_k_level_crossings A' k k).ncard +
        (regular_k_level_crossings A' k (k - 1)).ncard :=
    hle.trans (Set.ncard_union_le _ _)
  by_cases hlarge : (k_level_vertices A k).ncard ≤
      2 * (regular_k_level_crossings A' k k).ncard
  · refine ⟨A', k, hcard, Or.inl rfl, hinj.mono Set.subset_union_left, ?_⟩
    change ((k_level_vertices A k).ncard : ℝ) ≤
      2 * ((regular_k_level_crossings A' k k).ncard : ℝ)
    exact_mod_cast hlarge
  · have hother : (k_level_vertices A k).ncard ≤
        2 * (regular_k_level_crossings A' k (k - 1)).ncard := by
      omega
    refine ⟨A', k - 1, hcard, ?_, hinj.mono Set.subset_union_right, ?_⟩
    · omega
    · change ((k_level_vertices A k).ncard : ℝ) ≤
        2 * ((regular_k_level_crossings A' k (k - 1)).ncard : ℝ)
      exact_mod_cast hother

@[blueprint "lem:finite-rational-function-approximation"
  (statement := /-- Let $I$ be a finite type, let $x:I\to\RR$, and let $U$ be a
neighbourhood of $x$ in the product topology on $I\to\RR$. Then there is a rational-valued
function $y:I\to\QQ$ whose coordinatewise real image belongs to $U$. -/)
  (proof := /-- The rational numbers have dense image in $\RR$. The product of this dense map
over the finite coordinate type $I$ again has dense image in the product topology. Hence its
range meets every neighbourhood of $x$, and a preimage of such a point is the required
rational-valued function. -/)
  (title := /-- Simultaneous rational approximation in finitely many coordinates -/)
  (latexEnv := "lemma")]
lemma finite_rational_function_approximation {ι : Type} [Fintype ι]
    (x : ι → ℝ) (U : Set (ι → ℝ)) (hU : U ∈ nhds x) :
    ∃ y : ι → ℚ, (fun i => (y i : ℝ)) ∈ U := by
  have hdense : DenseRange (Pi.map (fun _ : ι => ((↑) : ℚ → ℝ))) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨y, hy⟩ := hdense.mem_nhds hU
  refine ⟨y, ?_⟩
  change (fun i => (y i : ℝ)) ∈ U at hy
  exact hy

@[blueprint "lem:finite-rational-common-multiplier"
  (statement := /-- For a rational-valued function $f$ on a finite type $I$, there are a
positive integer $m$ and an integer-valued function $z$ such that
$z_i=m f_i$ for every $i\in I$. -/)
  (proof := /-- Take $m$ to be the product of the positive reduced denominators of the
finitely many values $f_i$. Each denominator divides $m$. Multiplying the reduced numerator
of $f_i$ by the corresponding quotient $m/\operatorname{den}(f_i)$ therefore gives an integer
$z_i$, and the numerator--denominator formula for rational numbers yields $z_i=m f_i$. -/)
  (title := /-- A finite rational family has a common integral multiplier -/)
  (latexEnv := "lemma")]
lemma finite_rational_common_multiplier {ι : Type} [Fintype ι] (f : ι → ℚ) :
    ∃ m : ℕ, 0 < m ∧ ∃ z : ι → ℤ,
      ∀ i, (z i : ℚ) = (m : ℚ) * f i := by
  classical
  let m : ℕ := ∏ i, (f i).den
  have hm : 0 < m := by
    dsimp [m]
    exact Finset.prod_pos fun i _ => (f i).den_pos
  have hdvd (i : ι) : (f i).den ∣ m := by
    dsimp [m]
    exact Finset.dvd_prod_of_mem (fun j => (f j).den) (Finset.mem_univ i)
  let q : ι → ℕ := fun i => Classical.choose (hdvd i)
  have hq (i : ι) : (f i).den * q i = m :=
    (Classical.choose_spec (hdvd i)).symm
  let z : ι → ℤ := fun i =>
    (f i).num * (q i : ℤ)
  refine ⟨m, hm, z, ?_⟩
  intro i
  calc
    (z i : ℚ) = ((f i).num : ℚ) * (q i : ℕ) := by
      simp [z]
    _ = (m : ℚ) * (((f i).num : ℚ) / ((f i).den : ℚ)) := by
      rw [← hq i]
      push_cast
      field_simp [ne_of_gt (f i).den_pos]
    _ = (m : ℚ) * f i := by rw [Rat.num_div_den]

@[blueprint "lem:regular-crossings-rational-model"
  (statement := /-- Let $A$ be a finite indexed line arrangement and let $R_{k,r}(A)$ have
pairwise distinct parameter coordinates. Then, after identifying the elements of $A$ with
$\{0,\ldots,|A|-1\}$, there are positive rational numbers $P_i$, rational numbers $T_i$, and
an injective assignment $q\mapsto(x_q,y_q)$ such that $x_q>0$, two distinct selected lines
$(T_i+x)/P_i$ meet at $(x_q,y_q)$, and exactly $r$ selected lines lie below that point. -/)
  (proof := /-- Add to every slope the same sufficiently large real number. This common shear
preserves all incidences and vertical comparisons and makes every slope positive. For each
$q\in R_{k,r}(A)$ choose the two distinct incident indexed lines. Their intersection parameter
is a continuous rational expression in their slopes and intercepts near the sheared
arrangement. The value of every other line at that moving intersection is continuous as well.

The crossing set is finite by \cref{lem:k-level-vertices-finite}, and the line set is finite by
hypothesis. Hence continuity gives one neighbourhood of the sheared coefficient function on
which all slopes remain positive, all chosen crossing
parameters remain positive and pairwise distinct, and every strict-below predicate agrees with
its value in the original arrangement. By
\cref{lem:finite-rational-function-approximation}, this neighbourhood contains a
rational-valued coefficient function. Writing a positive rational-slope line $ax+b$ as
$(b/a+x)/(1/a)$ gives rational parameters $P=1/a>0$ and $T=b/a$. The preserved strict-below
predicates and the defining rank condition in \cref{def:regular-k-level-crossings} give the
asserted cardinality. -/)
  (title := /-- Rational modeling of finitely many regular crossings -/)
  (latexEnv := "lemma")]
lemma regular_crossings_rational_model (A : line_arrangement) (k r : ℕ)
    (hinj : Set.InjOn (fun q : ℝ × ℝ => q.1)
      (regular_k_level_crossings A k r)) :
    ∃ P T : Fin A.card → ℚ, (∀ i, 0 < P i) ∧
      ∃ ψ : ℝ × ℝ → ℝ × ℝ,
        Set.InjOn (fun q => (ψ q).1) (regular_k_level_crossings A k r) ∧
        ∀ q ∈ regular_k_level_crossings A k r,
          0 < (ψ q).1 ∧ ∃ i j : Fin A.card,
            P i ≠ P j ∧
            (((T i : ℝ) + (ψ q).1) / (P i : ℝ) = (ψ q).2 ∧
              ((T j : ℝ) + (ψ q).1) / (P j : ℝ) = (ψ q).2) ∧
            ((Finset.univ : Finset (Fin A.card)).filter (fun s =>
              ((T s : ℝ) + (ψ q).1) / (P s : ℝ) < (ψ q).2)).card = r := by
  classical
  let R : Set (ℝ × ℝ) := regular_k_level_crossings A k r
  have hRfinite : R.Finite :=
    (k_level_vertices_finite A k).subset fun q hq => hq.1
  let Q := {q // q ∈ R}
  letI : Fintype Q := hRfinite.fintype
  let e : Fin A.card ≃ {l // l ∈ A} :=
    (Fintype.equivFinOfCardEq (α := {l // l ∈ A}) (by simp)).symm
  let L : Fin A.card → ℕ × line := fun i => (e i).1
  have hLmem (i : Fin A.card) : L i ∈ A := (e i).2
  have hLinj : Function.Injective L := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  choose l₁ hl₁ l₂ hl₂ hlines hval₁ hval₂ using
    fun q : Q => q.2.1.1
  let i₁ : Q → Fin A.card := fun q => e.symm ⟨l₁ q, hl₁ q⟩
  let i₂ : Q → Fin A.card := fun q => e.symm ⟨l₂ q, hl₂ q⟩
  have hLi₁ (q : Q) : L (i₁ q) = l₁ q := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨l₁ q, hl₁ q⟩)
  have hLi₂ (q : Q) : L (i₂ q) = l₂ q := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨l₂ q, hl₂ q⟩)
  have hslope_ne (q : Q) : (L (i₁ q)).2.slope ≠ (L (i₂ q)).2.slope := by
    intro hs
    have hi : (L (i₁ q)).2.intercept = (L (i₂ q)).2.intercept := by
      have hv1 : line_value (L (i₁ q)).2 q.1.1 = q.1.2 := by
        simpa [hLi₁ q] using hval₁ q
      have hv2 : line_value (L (i₂ q)).2 q.1.1 = q.1.2 := by
        simpa [hLi₂ q] using hval₂ q
      simp only [line_value] at hv1 hv2
      rw [hs] at hv1
      linarith
    apply hlines q
    rw [← hLi₁ q, ← hLi₂ q]
    cases h₁ : (L (i₁ q)).2
    cases h₂ : (L (i₂ q)).2
    simp only [line.mk.injEq]
    exact ⟨by simpa [h₁, h₂] using hs, by simpa [h₁, h₂] using hi⟩
  have hincident (q : Q) (s : Fin A.card) :
      line_value (L s).2 q.1.1 = q.1.2 ↔ s = i₁ q ∨ s = i₂ q := by
    let Inc := A.filter fun l => line_value l.2 q.1.1 = q.1.2
    have hmem1 : l₁ q ∈ Inc := by
      exact Finset.mem_filter.mpr ⟨hl₁ q, hval₁ q⟩
    have hmem2 : l₂ q ∈ Inc := by
      exact Finset.mem_filter.mpr ⟨hl₂ q, hval₂ q⟩
    have hlne : l₁ q ≠ l₂ q := by
      intro h
      exact hlines q (congrArg Prod.snd h)
    have hpaircard : ({l₁ q, l₂ q} : Finset (ℕ × line)).card = 2 := by
      exact Finset.card_pair_eq_two_iff.mpr hlne
    have hcard : Inc.card = 2 := q.2.2.2.1
    have hpairsub : ({l₁ q, l₂ q} : Finset (ℕ × line)) ⊆ Inc := by
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · exact hmem1
      · exact hmem2
    have heq : Inc = {l₁ q, l₂ q} := by
      exact (Finset.eq_of_subset_of_card_le hpairsub (by rw [hcard, hpaircard])).symm
    constructor
    · intro hs
      have hm : L s ∈ Inc := Finset.mem_filter.mpr ⟨hLmem s, hs⟩
      rw [heq] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · left
        exact hLinj (hm.trans (hLi₁ q).symm)
      · right
        exact hLinj (hm.trans (hLi₂ q).symm)
    · rintro (rfl | rfl)
      · simpa [hLi₁ q] using hval₁ q
      · simpa [hLi₂ q] using hval₂ q
  let M : ℝ := 1 + ∑ i : Fin A.card, |(L i).2.slope|
  have hM (i : Fin A.card) : 0 < (L i).2.slope + M := by
    have hsingle : |(L i).2.slope| ≤ ∑ j : Fin A.card, |(L j).2.slope| :=
      Finset.single_le_sum
        (f := fun j : Fin A.card => |(L j).2.slope|) (s := Finset.univ)
        (fun _ _ => abs_nonneg _) (by simp)
    dsimp [M]
    nlinarith [neg_abs_le (L i).2.slope]
  let Coeff := Fin A.card × Bool → ℝ
  let slope : Coeff → Fin A.card → ℝ := fun F i => F (i, false)
  let intercept : Coeff → Fin A.card → ℝ := fun F i => F (i, true)
  let value : Coeff → Fin A.card → ℝ → ℝ := fun F i x =>
    slope F i * x + intercept F i
  let F₀ : Coeff := fun z =>
    if z.2 then (L z.1).2.intercept else (L z.1).2.slope + M
  have hF₀slope (i : Fin A.card) : slope F₀ i = (L i).2.slope + M := by
    simp [slope, F₀]
  have hF₀intercept (i : Fin A.card) : intercept F₀ i = (L i).2.intercept := by
    simp [intercept, F₀]
  let root : Coeff → Q → ℝ := fun F q =>
    (intercept F (i₂ q) - intercept F (i₁ q)) /
      (slope F (i₁ q) - slope F (i₂ q))
  let height : Coeff → Q → ℝ := fun F q => value F (i₁ q) (root F q)
  have hroot₀ (q : Q) : root F₀ q = q.1.1 := by
    have hv1 : line_value (L (i₁ q)).2 q.1.1 = q.1.2 := by
      simpa [hLi₁ q] using hval₁ q
    have hv2 : line_value (L (i₂ q)).2 q.1.1 = q.1.2 := by
      simpa [hLi₂ q] using hval₂ q
    dsimp [root]
    rw [hF₀intercept, hF₀intercept, hF₀slope, hF₀slope]
    have hd : (L (i₁ q)).2.slope + M - ((L (i₂ q)).2.slope + M) =
        (L (i₁ q)).2.slope - (L (i₂ q)).2.slope := by ring
    rw [hd]
    apply (div_eq_iff (sub_ne_zero.mpr (hslope_ne q))).2
    simp only [line_value] at hv1 hv2
    linarith
  have hheight₀ (q : Q) : height F₀ q = q.1.2 + M * q.1.1 := by
    dsimp [height, value]
    rw [hroot₀, hF₀slope, hF₀intercept]
    have hv1 : line_value (L (i₁ q)).2 q.1.1 = q.1.2 := by
      simpa [hLi₁ q] using hval₁ q
    simp only [line_value] at hv1
    linarith
  have hvalue₀ (q : Q) (s : Fin A.card) :
      value F₀ s (root F₀ q) = line_value (L s).2 q.1.1 + M * q.1.1 := by
    dsimp [value]
    rw [hroot₀, hF₀slope, hF₀intercept]
    simp only [line_value]
    ring
  have hroot_cont (q : Q) : ContinuousAt (fun F => root F q) F₀ := by
    dsimp [root, slope, intercept]
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · change slope F₀ (i₁ q) - slope F₀ (i₂ q) ≠ 0
      rw [hF₀slope, hF₀slope]
      simpa using sub_ne_zero.mpr (hslope_ne q)
  have hheight_cont (q : Q) : ContinuousAt (fun F => height F q) F₀ := by
    have hs : ContinuousAt (fun F : Coeff => slope F (i₁ q)) F₀ := by
      dsimp [slope]
      exact continuousAt_apply (i₁ q, false) F₀
    have hi : ContinuousAt (fun F : Coeff => intercept F (i₁ q)) F₀ := by
      dsimp [intercept]
      exact continuousAt_apply (i₁ q, true) F₀
    convert (hs.mul (hroot_cont q)).add hi using 1 <;> rfl
  have hvalue_cont (q : Q) (s : Fin A.card) :
      ContinuousAt (fun F => value F s (root F q)) F₀ := by
    have hs : ContinuousAt (fun F : Coeff => slope F s) F₀ := by
      dsimp [slope]
      exact continuousAt_apply (s, false) F₀
    have hi : ContinuousAt (fun F : Coeff => intercept F s) F₀ := by
      dsimp [intercept]
      exact continuousAt_apply (s, true) F₀
    convert (hs.mul (hroot_cont q)).add hi using 1 <;> rfl
  let Good : Set Coeff := {F |
    (∀ i, 0 < slope F i) ∧
    (∀ q, slope F (i₁ q) ≠ slope F (i₂ q)) ∧
    (∀ q, 0 < root F q) ∧
    (∀ q s, value F s (root F q) < height F q ↔
      line_value (L s).2 q.1.1 < q.1.2) ∧
    ∀ q₁ q₂, q₁ ≠ q₂ → root F q₁ ≠ root F q₂ }
  have hGood : Good ∈ nhds F₀ := by
    have hslope_event : ∀ᶠ F in nhds F₀,
        ∀ i : Fin A.card, 0 < slope F i := by
      rw [Filter.eventually_all]
      intro i
      exact continuousAt_const.eventually_lt (by fun_prop) (by simpa [hF₀slope] using hM i)
    have hden_event : ∀ᶠ F in nhds F₀,
        ∀ q : Q, slope F (i₁ q) ≠ slope F (i₂ q) := by
      rw [Filter.eventually_all]
      intro q
      have hc : ContinuousAt (fun F => slope F (i₁ q) - slope F (i₂ q)) F₀ := by
        dsimp [slope]
        fun_prop
      have hn : slope F₀ (i₁ q) - slope F₀ (i₂ q) ≠ 0 := by
        rw [hF₀slope, hF₀slope]
        simpa using sub_ne_zero.mpr (hslope_ne q)
      filter_upwards [hc.eventually_ne hn] with F hF
      exact sub_ne_zero.mp hF
    have hroot_event : ∀ᶠ F in nhds F₀, ∀ q : Q, 0 < root F q := by
      rw [Filter.eventually_all]
      intro q
      exact continuousAt_const.eventually_lt (hroot_cont q)
        (by rw [hroot₀]; exact q.2.2.1.1)
    have hbelow_event : ∀ᶠ F in nhds F₀, ∀ q : Q, ∀ s : Fin A.card,
        value F s (root F q) < height F q ↔
          line_value (L s).2 q.1.1 < q.1.2 := by
      rw [Filter.eventually_all]
      intro q
      rw [Filter.eventually_all]
      intro s
      by_cases hbelow : line_value (L s).2 q.1.1 < q.1.2
      · have hlt : value F₀ s (root F₀ q) < height F₀ q := by
          rw [hvalue₀, hheight₀]
          linarith
        filter_upwards [(hvalue_cont q s).eventually_lt (hheight_cont q) hlt] with F hF
        exact ⟨fun _ => hbelow, fun _ => hF⟩
      · have hge : q.1.2 ≤ line_value (L s).2 q.1.1 := le_of_not_gt hbelow
        by_cases heq : line_value (L s).2 q.1.1 = q.1.2
        · rcases (hincident q s).mp heq with rfl | rfl
          · filter_upwards [hden_event] with F hF
            have hequal : value F (i₁ q) (root F q) = height F q := rfl
            exact ⟨fun h => ((ne_of_lt h) hequal).elim,
              fun h => (hbelow h).elim⟩
          · filter_upwards [hden_event] with F hF
            have hequal : value F (i₂ q) (root F q) = height F q := by
              dsimp [height, value, root]
              have hd := hF q
              field_simp [sub_ne_zero.mpr hd]
              ring
            exact ⟨fun h => ((ne_of_lt h) hequal).elim,
              fun h => (hbelow h).elim⟩
        · have habove : q.1.2 < line_value (L s).2 q.1.1 :=
            lt_of_le_of_ne hge (Ne.symm heq)
          have hlt : height F₀ q < value F₀ s (root F₀ q) := by
            rw [hvalue₀, hheight₀]
            linarith
          filter_upwards [(hheight_cont q).eventually_lt (hvalue_cont q s) hlt] with F hF
          exact ⟨fun h => (not_lt_of_ge (le_of_lt hF) h).elim,
            fun h => (hbelow h).elim⟩
    have hinj_event : ∀ᶠ F in nhds F₀, ∀ q₁ : Q, ∀ q₂ : Q,
        q₁ ≠ q₂ → root F q₁ ≠ root F q₂ := by
      rw [Filter.eventually_all]
      intro q₁
      rw [Filter.eventually_all]
      intro q₂
      by_cases heq : q₁ = q₂
      · exact Filter.Eventually.of_forall fun F h => (h heq).elim
      · have hne : root F₀ q₁ ≠ root F₀ q₂ := by
          rw [hroot₀, hroot₀]
          intro hx
          exact heq (Subtype.ext (hinj q₁.2 q₂.2 hx))
        have hc : ContinuousAt (fun F => root F q₁ - root F q₂) F₀ :=
          (hroot_cont q₁).sub (hroot_cont q₂)
        have hne0 : root F₀ q₁ - root F₀ q₂ ≠ 0 := sub_ne_zero.mpr hne
        filter_upwards [hc.eventually_ne hne0] with F hF
        exact fun _ => sub_ne_zero.mp hF
    filter_upwards [hslope_event, hden_event, hroot_event, hbelow_event, hinj_event]
      with F hs hd hr hb hi
    exact ⟨hs, hd, hr, hb, hi⟩
  obtain ⟨G, hG⟩ := finite_rational_function_approximation F₀ Good hGood
  let a : Fin A.card → ℚ := fun i => G (i, false)
  let b : Fin A.card → ℚ := fun i => G (i, true)
  let P : Fin A.card → ℚ := fun i => 1 / a i
  let T : Fin A.card → ℚ := fun i => b i / a i
  have hGa (i : Fin A.card) : (a i : ℝ) = slope (fun z => (G z : ℝ)) i := by rfl
  have hGb (i : Fin A.card) : (b i : ℝ) = intercept (fun z => (G z : ℝ)) i := by rfl
  have ha (i : Fin A.card) : 0 < a i := by
    have haR : (0 : ℝ) < (a i : ℝ) := by
      rw [hGa]
      exact hG.1 i
    exact_mod_cast haR
  have hP (i : Fin A.card) : 0 < P i := by
    dsimp [P]
    exact one_div_pos.mpr (ha i)
  let ψ : ℝ × ℝ → ℝ × ℝ := fun q =>
    if hq : q ∈ R then
      (root (fun z => (G z : ℝ)) ⟨q, hq⟩,
        height (fun z => (G z : ℝ)) ⟨q, hq⟩)
    else (0, 0)
  have hψQ (q : Q) : ψ q.1 =
      (root (fun z => (G z : ℝ)) q, height (fun z => (G z : ℝ)) q) := by
    simp [ψ, q.2]
  refine ⟨P, T, hP, ψ, ?_, ?_⟩
  · intro q₁ hq₁ q₂ hq₂ heq
    let q₁' : Q := ⟨q₁, hq₁⟩
    let q₂' : Q := ⟨q₂, hq₂⟩
    have hr := hG.2.2.2.2 q₁' q₂'
    by_contra hne
    have hqne : q₁' ≠ q₂' := by
      intro h
      apply hne
      exact congrArg Subtype.val h
    apply hr hqne
    have hψ1 : (ψ q₁).1 = root (fun z => (G z : ℝ)) q₁' := by
      simpa [q₁'] using congrArg Prod.fst (hψQ q₁')
    have hψ2 : (ψ q₂).1 = root (fun z => (G z : ℝ)) q₂' := by
      simpa [q₂'] using congrArg Prod.fst (hψQ q₂')
    exact hψ1.symm.trans (heq.trans hψ2)
  · intro q hq
    let q' : Q := ⟨q, hq⟩
    have hψ := hψQ q'
    have hden := hG.2.1 q'
    have hpos := hG.2.2.1 q'
    have hbelow := hG.2.2.2.1 q'
    refine ⟨?_, i₁ q', i₂ q', ?_, ?_, ?_⟩
    · change 0 < (ψ q'.1).1
      rw [hψQ q']
      exact hpos
    · intro hP12
      have ha12 : a (i₁ q') = a (i₂ q') := by
        dsimp [P] at hP12
        field_simp [ne_of_gt (ha (i₁ q')), ne_of_gt (ha (i₂ q'))] at hP12
        linarith
      apply hden
      rw [← hGa, ← hGa]
      exact_mod_cast ha12
    · have hinc1 : (((T (i₁ q') : ℚ) : ℝ) + (ψ q).1) / (P (i₁ q') : ℝ) =
          (ψ q).2 := by
        rw [hψ]
        dsimp [T, P, height, value]
        push_cast
        field_simp [ne_of_gt (show (0 : ℝ) < (a (i₁ q') : ℝ) by exact_mod_cast ha (i₁ q'))]
        ring
      have hinc2 : (((T (i₂ q') : ℚ) : ℝ) + (ψ q).1) / (P (i₂ q') : ℝ) =
          (ψ q).2 := by
        rw [hψ]
        dsimp [T, P, height, value, root]
        push_cast
        have ha1R : (0 : ℝ) < (a (i₁ q') : ℝ) := by exact_mod_cast ha (i₁ q')
        have ha2R : (0 : ℝ) < (a (i₂ q') : ℝ) := by exact_mod_cast ha (i₂ q')
        field_simp [ne_of_gt ha1R, ne_of_gt ha2R, sub_ne_zero.mpr hden]
        ring
      exact ⟨hinc1, hinc2⟩
    · rw [← q'.2.2.2.2]
      have hline (s : Fin A.card) : ((T s : ℝ) + (ψ q).1) / (P s : ℝ) =
          value (fun z => (G z : ℝ)) s (root (fun z => (G z : ℝ)) q') := by
        rw [hψ]
        dsimp [T, P, value]
        push_cast
        field_simp [ne_of_gt (show (0 : ℝ) < (a s : ℝ) by exact_mod_cast ha s)]
        ring
      have hselected (s : Fin A.card) :
          ((T s : ℝ) + (ψ q).1) / (P s : ℝ) < (ψ q).2 ↔
            line_value (L s).2 q'.1.1 < q'.1.2 := by
        rw [hline, show (ψ q).2 = height (fun z => (G z : ℝ)) q' by rw [hψ]]
        exact hbelow s
      apply Finset.card_bij (fun s _ => L s)
      · intro s hs
        have hslt := (Finset.mem_filter.mp hs).2
        exact Finset.mem_filter.mpr ⟨hLmem s, (hselected s).mp hslt⟩
      · intro s₁ hs₁ s₂ hs₂ heq
        exact hLinj heq
      · intro l hl
        have hlA := (Finset.mem_filter.mp hl).1
        let s : Fin A.card := e.symm ⟨l, hlA⟩
        have hLs : L s = l := by
          exact congrArg Subtype.val (e.apply_symm_apply ⟨l, hlA⟩)
        refine ⟨s, ?_, hLs⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ s,
          (hselected s).mpr (by simpa [hLs] using (Finset.mem_filter.mp hl).2)⟩

@[blueprint "lem:left-output-jump-is-breaking-point"
  (statement := /-- Let $(p,H)$ be an apportionment instance, let $0<\delta<1$, and let
$x$ be an allocation belonging to the divisor output at $\delta$. If there is an $\eta>0$
such that $x$ does not belong to the divisor output at any
$a\in(\delta-\eta,\delta)$, then $\delta$ is a breaking point of $(p,H)$. -/)
  (proof := /-- Fix $\varepsilon>0$ and put
$d=\min\{\eta/2,\varepsilon/2\}$ and $a=\delta-d$. Positivity of $\eta$ and
$\varepsilon$ gives $0<d<\eta$ and $0<d<\varepsilon$, so
$a\in(\delta-\eta,\delta)\cap(\delta-\varepsilon,\delta)$. The allocation $x$ is absent from
the divisor output at $a$ but present at $\delta$, whence these two output sets differ.
Together with $0<\delta<1$, this is exactly the nonterminal alternative in the definition of
breaking points from \cref{def:breaking-points}. -/)
  (title := /-- A persistent left-hand output jump is a breaking point -/)
  (latexEnv := "lemma")]
lemma left_output_jump_is_breaking_point (inst : apportionment_instance) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (x : Fin inst.n → ℕ)
    (hx : x ∈ divisor_output inst δ) (η : ℝ) (hη : 0 < η)
    (hleft : ∀ a ∈ Set.Ioo (δ - η) δ, x ∉ divisor_output inst a) :
    δ ∈ breaking_points inst := by
  refine ⟨⟨hδ0, le_of_lt hδ1⟩, Or.inr ?_⟩
  intro ε hε
  let d : ℝ := min (η / 2) (ε / 2)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hdη : d < η := by
    have hle : d ≤ η / 2 := min_le_left _ _
    linarith
  have hdε : d < ε := by
    have hle : d ≤ ε / 2 := min_le_right _ _
    linarith
  let a : ℝ := δ - d
  have haη : a ∈ Set.Ioo (δ - η) δ := by
    constructor <;> dsimp [a] <;> linarith
  have haε : a ∈ Set.Ioo (δ - ε) δ := by
    constructor <;> dsimp [a] <;> linarith
  refine ⟨a, haε, ?_⟩
  intro heq
  apply hleft a haη
  rw [heq]
  exact hx

@[blueprint "lem:integral-selected-line-model-realization"
  (statement := /-- Let $S\subseteq\RR^2$ be finite, let $n>0$, and assign to each
$i\in\{0,\ldots,n-1\}$ positive integers $p_i$ and nonnegative integers $t_i$. Suppose that
an injective map $\phi:S\to(0,1)$ has the following property. For every $q\in S$, two selected
lines $(t_i+\delta)/p_i$ and $(t_j+\delta)/p_j$ meet at $\delta=\phi(q)$, the first has smaller
slope than the second, exactly $r$ selected lines lie below their common value, and every
selected line is at vertical distance less than $1/p_s$ from that value. Then there is an
apportionment instance with $n$ states and at least $|S|$ breaking points. -/)
  (proof := /-- Set $H=1+r+\sum_s t_s$ and use the $p_s$ as the population vector. At a
modeled crossing $\delta=\phi(q)$, let the base allocation give state $s$ the value $t_s+1$
when its selected line lies below the crossing, and $t_s$ otherwise; give one additional seat
to the incident line having smaller slope. The rank hypothesis makes the coordinate sum equal
to $H$. The vertical-margin hypothesis places the common crossing value in every coordinate's
rounding interval, so the pairwise criterion of
\cref{lem:divisor-output-pairwise-iff} proves feasibility at $\delta$.

Immediately to the left, the smaller-slope incident line lies strictly above the other incident
line. The pairwise interval inequality from the former state's lower endpoint to the latter
state's upper endpoint therefore fails, so the same allocation is infeasible throughout the
left interval $(0,\delta)$. By
\cref{lem:left-output-jump-is-breaking-point}, $\delta$ is a breaking point. Thus $\phi$ maps
$S$ injectively into the breaking-point set. That set is finite: away from the endpoint $1$,
\cref{lem:interior-breaking-point-level-vertex} injects it into the windowed top-level vertex
set, which is finite by \cref{lem:local-k-level-vertices-finite}. Taking finite cardinalities
proves the result. -/)
  (title := /-- Integral selected-line models yield breaking points -/)
  (latexEnv := "lemma")]
lemma integral_selected_line_model_realization (n r : ℕ) (hn : 0 < n)
    (p t : Fin n → ℕ) (hp : ∀ i, 0 < p i) (S : Set (ℝ × ℝ))
    (hSfinite : S.Finite) (φ : ℝ × ℝ → ℝ) (hφ : Set.InjOn φ S)
    (hmodel : ∀ q ∈ S, ∃ i j : Fin n,
      1 / (p i : ℝ) < 1 / (p j : ℝ) ∧
      φ q ∈ Set.Ioo (0 : ℝ) 1 ∧
      ((t i : ℝ) + φ q) / (p i : ℝ) =
        ((t j : ℝ) + φ q) / (p j : ℝ) ∧
      ((Finset.univ : Finset (Fin n)).filter (fun s =>
        ((t s : ℝ) + φ q) / (p s : ℝ) <
          ((t i : ℝ) + φ q) / (p i : ℝ))).card = r ∧
      ∀ s : Fin n,
        |((t s : ℝ) + φ q) / (p s : ℝ) -
          ((t i : ℝ) + φ q) / (p i : ℝ)| < 1 / (p s : ℝ)) :
    ∃ inst : apportionment_instance, inst.n = n ∧
      (S.ncard : ℝ) ≤ (num_breaking_points inst : ℝ) := by
  classical
  let H : ℕ := 1 + r + ∑ s, t s
  have hH : 0 < H := by
    dsimp [H]
    omega
  let inst : apportionment_instance :=
    { n := n
      p := p
      H := H
      hn := hn
      hp := hp
      hH := hH }
  have hmap : ∀ q ∈ S, φ q ∈ breaking_points inst := by
    intro q hq
    obtain ⟨i, j, hslope, hδ, hij, hcount, hmargin⟩ := hmodel q hq
    let δ : ℝ := φ q
    let y : ℝ := ((t i : ℝ) + δ) / (p i : ℝ)
    let v : Fin n → ℝ := fun s => ((t s : ℝ) + δ) / (p s : ℝ)
    let b : Fin n → ℕ := fun s => t s + if v s < y then 1 else 0
    let x : Fin n → ℕ := fun s => b s + if s = i then 1 else 0
    have hvi : v i = y := by rfl
    have hvj : v j = y := by
      simpa [δ, y, v] using hij.symm
    have hbase : (∑ s, b s) = (∑ s, t s) + r := by
      have hindicator : (∑ s : Fin n, if v s < y then 1 else 0) = r := by
        rw [← hcount]
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro s hs
        by_cases hsy : v s < y <;> simp [hsy, δ, y, v]
      simp only [b, Finset.sum_add_distrib]
      rw [hindicator]
    have hxsum : (∑ s, x s) = H := by
      rw [show (∑ s, x s) = (∑ s, b s) + 1 by
        simp only [x, Finset.sum_add_distrib]
        simp]
      rw [hbase]
      dsimp [H]
      omega
    have hxδ : x ∈ divisor_output inst δ := by
      apply (divisor_output_pairwise_iff inst δ x hδ.1 hδ.2).2
      refine ⟨?_, ?_⟩
      · simpa [inst] using hxsum
      · have hinterval : ∀ s : Fin n,
            ((x s : ℝ) - 1 + δ) / (p s : ℝ) ≤ y ∧
              y ≤ ((x s : ℝ) + δ) / (p s : ℝ) := by
          intro s
          have hps : 0 < (p s : ℝ) := by exact_mod_cast hp s
          have hstep : 0 < 1 / (p s : ℝ) := one_div_pos.mpr hps
          have hm := hmargin s
          have hm' : |v s - y| < 1 / (p s : ℝ) := by
            simpa [δ, y, v] using hm
          have hlow : v s - 1 / (p s : ℝ) < y := by
            have := (abs_lt.mp hm').2
            linarith
          have hupp : y < v s + 1 / (p s : ℝ) := by
            have := (abs_lt.mp hm').1
            linarith
          by_cases hsi : s = i
          · subst s
            have hnot : ¬v i < y := by simp [hvi]
            have hxi : x i = t i + 1 := by simp [x, b, hnot]
            rw [hxi]
            constructor
            · rw [show ((((t i + 1 : ℕ) : ℝ) - 1 + δ) / (p i : ℝ)) = v i by
                simp only [Nat.cast_add, Nat.cast_one]
                dsimp [v]
                ring]
            · rw [show ((((t i + 1 : ℕ) : ℝ) + δ) / (p i : ℝ)) =
                  v i + 1 / (p i : ℝ) by
                simp only [Nat.cast_add, Nat.cast_one]
                dsimp [v]
                ring]
              simpa [hvi] using le_of_lt hupp
          · by_cases hbelow : v s < y
            · have hxs : x s = t s + 1 := by simp [x, b, hsi, hbelow]
              rw [hxs]
              constructor
              · rw [show ((((t s + 1 : ℕ) : ℝ) - 1 + δ) / (p s : ℝ)) = v s by
                    simp only [Nat.cast_add, Nat.cast_one]
                    dsimp [v]
                    ring]
                exact le_of_lt hbelow
              · rw [show ((((t s + 1 : ℕ) : ℝ) + δ) / (p s : ℝ)) =
                    v s + 1 / (p s : ℝ) by
                    simp only [Nat.cast_add, Nat.cast_one]
                    dsimp [v]
                    ring]
                exact le_of_lt hupp
            · have hxs : x s = t s := by simp [x, b, hsi, hbelow]
              rw [hxs]
              constructor
              · rw [show (((t s : ℝ) - 1 + δ) / (p s : ℝ)) =
                    v s - 1 / (p s : ℝ) by
                    dsimp [v]
                    ring]
                exact le_of_lt hlow
              · rw [show (((t s : ℝ) + δ) / (p s : ℝ)) = v s by rfl]
                exact le_of_not_gt hbelow
        intro a c
        exact (hinterval a).1.trans (hinterval c).2
    have hleft : ∀ a ∈ Set.Ioo (δ - δ) δ, x ∉ divisor_output inst a := by
      intro a ha hxa
      have ha0 : 0 < a := by simpa using ha.1
      have ha1 : a < 1 := lt_trans ha.2 hδ.2
      have hpairs := (divisor_output_pairwise_iff inst a x ha0 ha1).1 hxa |>.2
      have hji : j ≠ i := by
        intro hji
        subst j
        exact (lt_irrefl _ hslope)
      have hnoti : ¬v i < y := by simp [hvi]
      have hnotj : ¬v j < y := by simp [hvj]
      have hxi : x i = t i + 1 := by simp [x, b, hnoti]
      have hxj : x j = t j := by simp [x, b, hji, hnotj]
      have hpair := hpairs i j
      rw [show inst.p i = p i by rfl, show inst.p j = p j by rfl, hxi, hxj] at hpair
      have hpair' : ((t i : ℝ) + a) / (p i : ℝ) ≤
          ((t j : ℝ) + a) / (p j : ℝ) := by
        convert hpair using 1 <;> push_cast <;> ring
      have hi_aff : ((t i : ℝ) + a) / (p i : ℝ) =
          v i + (1 / (p i : ℝ)) * (a - δ) := by
        dsimp [v]
        ring
      have hj_aff : ((t j : ℝ) + a) / (p j : ℝ) =
          v j + (1 / (p j : ℝ)) * (a - δ) := by
        dsimp [v]
        ring
      rw [hi_aff, hj_aff, hvi, hvj] at hpair'
      have hprod : 0 < (1 / (p i : ℝ) - 1 / (p j : ℝ)) * (a - δ) :=
        mul_pos_of_neg_of_neg (sub_neg.mpr hslope) (sub_neg.mpr ha.2)
      nlinarith
    exact left_output_jump_is_breaking_point inst δ hδ.1 hδ.2 x hxδ δ hδ.1 hleft
  have hBPfinite : (breaking_points inst).Finite := by
    let B : Set ℝ := breaking_points inst \ {1}
    let V : Set (ℝ × ℝ) :=
      k_level_vertices (apportionment_arrangement inst) (inst.H - 1) ∩
        {q : ℝ × ℝ | q.1 ∈ Set.Icc (0 : ℝ) 1}
    let ψ : ℝ → ℝ × ℝ := fun δ =>
      if h : δ ∈ breaking_points inst ∧ δ ≠ 1 then
        (δ, Classical.choose
          (interior_breaking_point_level_vertex inst δ h.1 h.2))
      else (δ, 0)
    have hψfst (δ : ℝ) : (ψ δ).1 = δ := by
      dsimp [ψ]
      split <;> rfl
    have hψmap : ∀ δ ∈ B, ψ δ ∈ V := by
      intro δ hδ
      have hbp : δ ∈ breaking_points inst := hδ.1
      have hne : δ ≠ 1 := by simpa using hδ.2
      have hwindow : δ ∈ Set.Icc (0 : ℝ) 1 := by
        exact ⟨le_of_lt hbp.1.1, hbp.1.2⟩
      dsimp [ψ]
      rw [dif_pos ⟨hbp, hne⟩]
      exact ⟨Classical.choose_spec
        (interior_breaking_point_level_vertex inst δ hbp hne), hwindow⟩
    have hψinj : Set.InjOn ψ B := by
      intro a ha b hb hab
      have := congrArg Prod.fst hab
      simpa [hψfst] using this
    have hVfinite : V.Finite :=
      (local_k_level_vertices_finite
        (apportionment_arrangement inst) (inst.H - 1)).inter_of_left _
    have hBfinite : B.Finite := by
      have himage : (ψ '' B).Finite := by
        apply hVfinite.subset
        rintro z ⟨δ, hδ, rfl⟩
        exact hψmap δ hδ
      exact Set.Finite.of_finite_image himage hψinj
    apply (hBfinite.union (Set.finite_singleton 1)).subset
    intro δ hδ
    by_cases hδone : δ = 1
    · exact Or.inr (by simpa [hδone])
    · exact Or.inl ⟨hδ, by simpa [hδone]⟩
  refine ⟨inst, rfl, ?_⟩
  exact_mod_cast Set.ncard_le_ncard_of_injOn φ hmap hφ hBPfinite

@[blueprint "lem:rational-selected-line-model-realization"
  (statement := /-- Let $S\subseteq\RR^2$ be finite and let $n>0$. For each state $i$, let
$P_i>0$ and $T_i$ be rational numbers, representing the selected line
$(T_i+\delta)/P_i$. Suppose that an injective assignment $q\mapsto(x_q,y_q)$ associates to
every $q\in S$ a positive-parameter crossing of two distinct selected lines, with exactly $r$
selected lines below it. Then there is an apportionment instance with $n$ states and at least
$|S|$ breaking points. -/)
  (proof := /-- Use \cref{lem:finite-rational-common-multiplier} to choose a positive integer
$m$ for which $P_i^0=mP_i$ and $T_i^0=mT_i$ are integers. The modeled crossing parameter then
becomes $x_q^0=mx_q$, without changing its height or any vertical comparison. Choose an integer
$C$ larger than the finitely many absolute values and separation ratios occurring in the model,
and put
\[
 t_i=T_i^0+CP_i^0,\qquad p_i=P_i^0+t_i.
\]
The choice of $C$ makes $t_i\ge0$ and $p_i>0$. It also makes the parameters
\[
 \phi(q)=\frac{x_q^0}{1+C+y_q}
\]
lie in $(0,1)$ and remain pairwise distinct.

For every selected line and every modeled crossing, direct expansion gives
\[
 \frac{t_i+\phi(q)}{p_i}-\frac{C+y_q}{1+C+y_q}
 =\frac{P_i^0}{p_i(1+C+y_q)}
  \left(\frac{T_i^0+x_q^0}{P_i^0}-y_q\right).
\]
All factors outside the parentheses are positive. Hence the transformation preserves every
strict vertical comparison and every incidence, so exactly $r$ selected lines remain below the
transformed crossing. The defining lower bound on $C$ also makes the absolute value on the left
strictly smaller than $1/p_i$. Thus the transformed data satisfy
\cref{lem:integral-selected-line-model-realization}, which supplies the required instance and
cardinality inequality. -/)
  (title := /-- Rational selected-line models yield apportionment instances -/)
  (latexEnv := "lemma")]
lemma rational_selected_line_model_realization (n r : ℕ) (hn : 0 < n)
    (P T : Fin n → ℚ) (hP : ∀ i, 0 < P i) (S : Set (ℝ × ℝ))
    (hSfinite : S.Finite) (ψ : ℝ × ℝ → ℝ × ℝ)
    (hψ : Set.InjOn (fun q => (ψ q).1) S)
    (hmodel : ∀ q ∈ S,
      0 < (ψ q).1 ∧ ∃ i j : Fin n,
        P i ≠ P j ∧
        (((T i : ℝ) + (ψ q).1) / (P i : ℝ) = (ψ q).2 ∧
          ((T j : ℝ) + (ψ q).1) / (P j : ℝ) = (ψ q).2) ∧
        ((Finset.univ : Finset (Fin n)).filter (fun s =>
          ((T s : ℝ) + (ψ q).1) / (P s : ℝ) < (ψ q).2)).card = r) :
    ∃ inst : apportionment_instance, inst.n = n ∧
      (S.ncard : ℝ) ≤ (num_breaking_points inst : ℝ) := by
  classical
  let f : Fin n ⊕ Fin n → ℚ := fun u =>
    Sum.elim P T u
  obtain ⟨m, hm, z, hz⟩ := finite_rational_common_multiplier f
  let Pz : Fin n → ℤ := fun i => z (Sum.inl i)
  let Tz : Fin n → ℤ := fun i => z (Sum.inr i)
  have hPzq (i : Fin n) : (Pz i : ℚ) = (m : ℚ) * P i := by
    simpa [Pz, f] using hz (Sum.inl i)
  have hTzq (i : Fin n) : (Tz i : ℚ) = (m : ℚ) * T i := by
    simpa [Tz, f] using hz (Sum.inr i)
  have hPzpos (i : Fin n) : 0 < Pz i := by
    have hqpos : (0 : ℚ) < (Pz i : ℚ) := by
      rw [hPzq i]
      exact mul_pos (by exact_mod_cast hm) (hP i)
    exact_mod_cast hqpos
  let P₀ : Fin n → ℕ := fun i => (Pz i).toNat
  have hP₀pos (i : Fin n) : 0 < P₀ i := by
    simpa [P₀] using hPzpos i
  have hP₀z (i : Fin n) : (P₀ i : ℤ) = Pz i := by
    simp [P₀, Int.toNat_of_nonneg (le_of_lt (hPzpos i))]
  have hP₀q (i : Fin n) : (P₀ i : ℚ) = (m : ℚ) * P i := by
    rw [← hPzq i]
    exact_mod_cast hP₀z i
  have hP₀r (i : Fin n) : (P₀ i : ℝ) = (m : ℝ) * (P i : ℝ) := by
    exact_mod_cast hP₀q i
  have hTzr (i : Fin n) : (Tz i : ℝ) = (m : ℝ) * (T i : ℝ) := by
    exact_mod_cast hTzq i
  let Q := {q // q ∈ S}
  letI : Fintype Q := hSfinite.fintype
  let x₀ : Q → ℝ := fun q => (m : ℝ) * (ψ q.1).1
  let y₀ : Q → ℝ := fun q => (ψ q.1).2
  let old : Fin n → Q → ℝ := fun i q =>
    ((Tz i : ℝ) + x₀ q) / (P₀ i : ℝ)
  have hold (i : Fin n) (q : Q) :
      old i q = ((T i : ℝ) + (ψ q.1).1) / (P i : ℝ) := by
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hPiR : (0 : ℝ) < (P i : ℝ) := by exact_mod_cast hP i
    dsimp [old, x₀]
    rw [hTzr i, hP₀r i]
    field_simp
  have hx₀pos (q : Q) : 0 < x₀ q := by
    have hmq := (hmodel q.1 q.2).1
    dsimp [x₀]
    positivity
  have hx₀inj : Function.Injective x₀ := by
    intro q₁ q₂ heq
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hx : (ψ q₁.1).1 = (ψ q₂.1).1 := by
      dsimp [x₀] at heq
      nlinarith
    exact Subtype.ext (hψ q₁.2 q₂.2 hx)
  let crossingTerm (q : Q) : ℝ :=
    x₀ q + |y₀ q| + 2 +
      ∑ i : Fin n, (P₀ i : ℝ) * |old i q - y₀ q|
  let separationTerm (q₁ q₂ : Q) : ℝ :=
    if x₀ q₁ < x₀ q₂ then
      |x₀ q₁ * (1 + y₀ q₂) - x₀ q₂ * (1 + y₀ q₁)| /
        (x₀ q₂ - x₀ q₁)
    else 0
  have hcrossingTerm_nonneg (q : Q) : 0 ≤ crossingTerm q := by
    dsimp [crossingTerm]
    have hx := hx₀pos q
    positivity
  have hseparationTerm_nonneg (q₁ q₂ : Q) : 0 ≤ separationTerm q₁ q₂ := by
    dsimp [separationTerm]
    split
    · positivity
    · positivity
  let B : ℝ :=
    2 + ∑ i : Fin n, |(Tz i : ℝ)| +
      ∑ q : Q, crossingTerm q +
      ∑ q₁ : Q, ∑ q₂ : Q, separationTerm q₁ q₂
  obtain ⟨C, hC⟩ := exists_nat_gt B
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    have hqsum : 0 ≤ ∑ q : Q, crossingTerm q :=
      Finset.sum_nonneg fun q _ => hcrossingTerm_nonneg q
    have hssep : 0 ≤ ∑ q₁ : Q, ∑ q₂ : Q, separationTerm q₁ q₂ :=
      Finset.sum_nonneg fun q₁ _ => Finset.sum_nonneg fun q₂ _ =>
        hseparationTerm_nonneg q₁ q₂
    positivity
  have hCpos : 0 < C := by
    exact_mod_cast (lt_of_le_of_lt hBnonneg hC)
  have hCT (i : Fin n) : |(Tz i : ℝ)| < C := by
    have hle : |(Tz i : ℝ)| ≤ ∑ j : Fin n, |(Tz j : ℝ)| := by
      exact Finset.single_le_sum
        (f := fun j : Fin n => |(Tz j : ℝ)|) (s := Finset.univ)
        (fun _ _ => abs_nonneg _) (by simp)
    have hrest : 0 ≤ ∑ q : Q, crossingTerm q := by
      apply Finset.sum_nonneg
      intro q hq
      exact hcrossingTerm_nonneg q
    have hsep : 0 ≤ ∑ q₁ : Q, ∑ q₂ : Q, separationTerm q₁ q₂ := by
      apply Finset.sum_nonneg
      intro q₁ hq₁
      apply Finset.sum_nonneg
      intro q₂ hq₂
      exact hseparationTerm_nonneg q₁ q₂
    dsimp [B] at hC
    nlinarith
  have hCQ (q : Q) : crossingTerm q < C := by
    have hterm : crossingTerm q ≤ ∑ z : Q, crossingTerm z := by
      apply Finset.single_le_sum
      · intro z hz
        exact hcrossingTerm_nonneg z
      · exact Finset.mem_univ q
    have hTsum : 0 ≤ ∑ i : Fin n, |(Tz i : ℝ)| := by positivity
    have hsep : 0 ≤ ∑ q₁ : Q, ∑ q₂ : Q, separationTerm q₁ q₂ := by
      apply Finset.sum_nonneg
      intro q₁ hq₁
      apply Finset.sum_nonneg
      intro q₂ hq₂
      exact hseparationTerm_nonneg q₁ q₂
    dsimp [B] at hC
    nlinarith
  have hCS (q₁ q₂ : Q) : separationTerm q₁ q₂ < C := by
    have hinner : separationTerm q₁ q₂ ≤ ∑ z : Q, separationTerm q₁ z := by
      apply Finset.single_le_sum
      · intro z hz
        exact hseparationTerm_nonneg q₁ z
      · exact Finset.mem_univ q₂
    have houter : (∑ z : Q, separationTerm q₁ z) ≤
        ∑ w : Q, ∑ z : Q, separationTerm w z := by
      exact Finset.single_le_sum
        (f := fun w : Q => ∑ z : Q, separationTerm w z) (s := Finset.univ)
        (fun w _ => Finset.sum_nonneg fun z _ => hseparationTerm_nonneg w z) (by simp)
    have hTsum : 0 ≤ ∑ i : Fin n, |(Tz i : ℝ)| := by positivity
    have hQsum : 0 ≤ ∑ q : Q, crossingTerm q := by
      apply Finset.sum_nonneg
      intro q hq
      exact hcrossingTerm_nonneg q
    dsimp [B] at hC
    nlinarith
  have hshiftpos (i : Fin n) : 0 < Tz i + (C : ℤ) * (P₀ i : ℤ) := by
    have hPone : (1 : ℤ) ≤ P₀ i := by exact_mod_cast hP₀pos i
    have hTlower : -(C : ℤ) < Tz i := by
      exact_mod_cast (neg_lt_of_abs_lt (hCT i))
    nlinarith
  let t : Fin n → ℕ := fun i => (Tz i + (C : ℤ) * (P₀ i : ℤ)).toNat
  have htz (i : Fin n) : (t i : ℤ) = Tz i + (C : ℤ) * (P₀ i : ℤ) := by
    simp [t, Int.toNat_of_nonneg (le_of_lt (hshiftpos i))]
  have htr (i : Fin n) : (t i : ℝ) =
      (Tz i : ℝ) + (C : ℝ) * (P₀ i : ℝ) := by
    exact_mod_cast htz i
  let p : Fin n → ℕ := fun i => P₀ i + t i
  have hp (i : Fin n) : 0 < p i := by
    have hi := hP₀pos i
    dsimp [p]
    omega
  let φ : ℝ × ℝ → ℝ := fun q =>
    if hq : q ∈ S then
      x₀ ⟨q, hq⟩ / (1 + (C : ℝ) + y₀ ⟨q, hq⟩)
    else 0
  have hdenpos (q : Q) : 0 < 1 + (C : ℝ) + y₀ q := by
    have hbound := hCQ q
    dsimp [crossingTerm] at hbound
    have hx := hx₀pos q
    have hsum : 0 ≤ ∑ i : Fin n, (P₀ i : ℝ) * |old i q - y₀ q| := by
      positivity
    nlinarith [neg_abs_le (y₀ q)]
  have hdenx (q : Q) : x₀ q < 1 + (C : ℝ) + y₀ q := by
    have hbound := hCQ q
    dsimp [crossingTerm] at hbound
    have hsum : 0 ≤ ∑ i : Fin n, (P₀ i : ℝ) * |old i q - y₀ q| := by
      positivity
    nlinarith [neg_abs_le (y₀ q)]
  have hφQ (q : Q) : φ q.1 = x₀ q / (1 + (C : ℝ) + y₀ q) := by
    simp [φ, q.2]
  have hφinj : Set.InjOn φ S := by
    intro q₁ hq₁ q₂ hq₂ heq
    let a : Q := ⟨q₁, hq₁⟩
    let b : Q := ⟨q₂, hq₂⟩
    by_contra hab
    have habQ : a ≠ b := by
      intro h
      apply hab
      exact congrArg Subtype.val h
    have hxne : x₀ a ≠ x₀ b := fun h => habQ (hx₀inj h)
    rcases lt_or_gt_of_ne hxne with hxab | hxba
    · have hsep := hCS a b
      rw [show separationTerm a b =
          |x₀ a * (1 + y₀ b) - x₀ b * (1 + y₀ a)| /
            (x₀ b - x₀ a) by simp [separationTerm, hxab]] at hsep
      have hgap : 0 < x₀ b - x₀ a := sub_pos.mpr hxab
      have hscaled :
          |x₀ a * (1 + y₀ b) - x₀ b * (1 + y₀ a)| <
            (C : ℝ) * (x₀ b - x₀ a) := by
        exact (div_lt_iff₀ hgap).mp hsep
      have hlt : x₀ a / (1 + (C : ℝ) + y₀ a) <
          x₀ b / (1 + (C : ℝ) + y₀ b) := by
        apply (div_lt_div_iff₀ (hdenpos a) (hdenpos b)).2
        have habs := le_abs_self
          (x₀ a * (1 + y₀ b) - x₀ b * (1 + y₀ a))
        nlinarith
      have := heq
      rw [hφQ a, hφQ b] at this
      exact (ne_of_lt hlt) this
    · have hsep := hCS b a
      rw [show separationTerm b a =
          |x₀ b * (1 + y₀ a) - x₀ a * (1 + y₀ b)| /
            (x₀ a - x₀ b) by simp [separationTerm, hxba]] at hsep
      have hgap : 0 < x₀ a - x₀ b := sub_pos.mpr hxba
      have hscaled :
          |x₀ b * (1 + y₀ a) - x₀ a * (1 + y₀ b)| <
            (C : ℝ) * (x₀ a - x₀ b) := by
        exact (div_lt_iff₀ hgap).mp hsep
      have hlt : x₀ b / (1 + (C : ℝ) + y₀ b) <
          x₀ a / (1 + (C : ℝ) + y₀ a) := by
        apply (div_lt_div_iff₀ (hdenpos b) (hdenpos a)).2
        have habs := le_abs_self
          (x₀ b * (1 + y₀ a) - x₀ a * (1 + y₀ b))
        nlinarith
      have := heq
      rw [hφQ a, hφQ b] at this
      exact (ne_of_gt hlt) this
  apply integral_selected_line_model_realization n r hn p t hp S hSfinite φ hφinj
  intro q hq
  let q' : Q := ⟨q, hq⟩
  obtain ⟨hxq, i, j, hPij, hinc, hcount⟩ := hmodel q hq
  have hxi : old i q' = y₀ q' := by
    rw [hold]
    simpa [q', y₀] using hinc.1
  have hxj : old j q' = y₀ q' := by
    rw [hold]
    simpa [q', y₀] using hinc.2
  have hφq : φ q = x₀ q' / (1 + (C : ℝ) + y₀ q') := hφQ q'
  let y' : ℝ := ((C : ℝ) + y₀ q') / (1 + (C : ℝ) + y₀ q')
  have hproject (s : Fin n) :
      ((t s : ℝ) + φ q) / (p s : ℝ) - y' =
        (P₀ s : ℝ) * (old s q' - y₀ q') /
          ((p s : ℝ) * (1 + (C : ℝ) + y₀ q')) := by
    have hpR : (0 : ℝ) < (p s : ℝ) := by exact_mod_cast hp s
    have hP₀R : (0 : ℝ) < (P₀ s : ℝ) := by exact_mod_cast hP₀pos s
    have hpformula : (p s : ℝ) = (P₀ s : ℝ) +
        (Tz s : ℝ) + (C : ℝ) * (P₀ s : ℝ) := by
      dsimp [p]
      push_cast
      rw [htr s]
      ring
    rw [hφq, htr s]
    dsimp [y', old]
    field_simp [ne_of_gt hpR, ne_of_gt hP₀R, ne_of_gt (hdenpos q')]
    rw [hpformula]
    ring
  have hpi_ne_pj : p i ≠ p j := by
    intro hpij
    have hvi := hproject i
    have hvj := hproject j
    rw [hxi, sub_self, mul_zero, zero_div] at hvi
    rw [hxj, sub_self, mul_zero, zero_div] at hvj
    have hti : ((t i : ℝ) + φ q) / (p i : ℝ) = y' := sub_eq_zero.mp hvi
    have htj : ((t j : ℝ) + φ q) / (p j : ℝ) = y' := sub_eq_zero.mp hvj
    have htij : t i = t j := by
      rw [hpij] at hti
      have hpjR : (0 : ℝ) < (p j : ℝ) := by exact_mod_cast hp j
      have hfrac : ((t i : ℝ) + φ q) / (p j : ℝ) =
          ((t j : ℝ) + φ q) / (p j : ℝ) := hti.trans htj.symm
      have hnum := (div_left_inj' (ne_of_gt hpjR)).mp hfrac
      have : (t i : ℝ) = (t j : ℝ) := by linarith
      exact_mod_cast this
    have hP₀ij : P₀ i = P₀ j := by
      dsimp [p] at hpij
      omega
    apply hPij
    have hmQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
    apply (mul_left_cancel₀ (ne_of_gt hmQ))
    rw [← hP₀q i, ← hP₀q j, hP₀ij]
  let i' : Fin n := if p j < p i then i else j
  let j' : Fin n := if p j < p i then j else i
  have hslope : 1 / (p i' : ℝ) < 1 / (p j' : ℝ) := by
    have hcases := lt_or_gt_of_ne hpi_ne_pj
    rcases hcases with hijp | hjip
    · simp [i', j', hijp, not_lt_of_ge (le_of_lt hijp)]
      have hip : (0 : ℝ) < (p i : ℝ) := by exact_mod_cast hp i
      have hijR : (p i : ℝ) < (p j : ℝ) := by exact_mod_cast hijp
      simpa [one_div] using one_div_lt_one_div_of_lt hip hijR
    · simp [i', j', hjip]
      have hjp : (0 : ℝ) < (p j : ℝ) := by exact_mod_cast hp j
      have hjiR : (p j : ℝ) < (p i : ℝ) := by exact_mod_cast hjip
      simpa [one_div] using one_div_lt_one_div_of_lt hjp hjiR
  have hi'inc : ((t i' : ℝ) + φ q) / (p i' : ℝ) = y' := by
    have hi := hproject i
    have hj := hproject j
    rw [hxi, sub_self, mul_zero, zero_div] at hi
    rw [hxj, sub_self, mul_zero, zero_div] at hj
    simp only [sub_eq_zero] at hi hj
    dsimp [i']
    split <;> assumption
  have hj'inc : ((t j' : ℝ) + φ q) / (p j' : ℝ) = y' := by
    have hi := hproject i
    have hj := hproject j
    rw [hxi, sub_self, mul_zero, zero_div] at hi
    rw [hxj, sub_self, mul_zero, zero_div] at hj
    simp only [sub_eq_zero] at hi hj
    dsimp [j']
    split <;> assumption
  refine ⟨i', j', hslope, ?_, hi'inc.trans hj'inc.symm, ?_, ?_⟩
  · rw [hφq]
    exact ⟨div_pos (hx₀pos q') (hdenpos q'),
      (div_lt_one (hdenpos q')).2 (hdenx q')⟩
  · rw [← hcount]
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hfactor : 0 < (P₀ s : ℝ) /
        ((p s : ℝ) * (1 + (C : ℝ) + y₀ q')) := by
      apply div_pos
      · exact_mod_cast hP₀pos s
      · exact mul_pos (by exact_mod_cast hp s) (hdenpos q')
    have hproject_factor :
        ((t s : ℝ) + φ q) / (p s : ℝ) - y' =
          ((P₀ s : ℝ) / ((p s : ℝ) * (1 + (C : ℝ) + y₀ q'))) *
            (old s q' - y₀ q') := by
      rw [hproject s]
      ring
    rw [hi'inc]
    constructor
    · intro hslt
      have hneg : old s q' - y₀ q' < 0 := by
        have hprod : ((P₀ s : ℝ) /
            ((p s : ℝ) * (1 + (C : ℝ) + y₀ q'))) *
              (old s q' - y₀ q') < 0 := by
          rw [← hproject_factor]
          exact sub_neg.mpr hslt
        nlinarith
      rw [hold] at hneg
      simpa [q', y₀] using hneg
    · intro hslt
      have hneg : old s q' - y₀ q' < 0 := by
        rw [hold]
        simpa [q', y₀] using hslt
      have hprod := mul_neg_of_pos_of_neg hfactor hneg
      apply sub_neg.mp
      rw [hproject_factor]
      exact hprod
  · intro s
    have hbound := hCQ q'
    dsimp [crossingTerm] at hbound
    have hmargin : (P₀ s : ℝ) * |old s q' - y₀ q'| <
        1 + (C : ℝ) + y₀ q' := by
      have hsingle : (P₀ s : ℝ) * |old s q' - y₀ q'| ≤
          ∑ z : Fin n, (P₀ z : ℝ) * |old z q' - y₀ q'| := by
        exact Finset.single_le_sum
          (f := fun z : Fin n => (P₀ z : ℝ) * |old z q' - y₀ q'|)
          (s := Finset.univ) (fun z _ => by positivity) (by simp)
      have hx := hx₀pos q'
      nlinarith [neg_abs_le (y₀ q')]
    have hsproj := hproject s
    rw [hi'inc]
    rw [hproject s]
    have hpR : (0 : ℝ) < (p s : ℝ) := by exact_mod_cast hp s
    have hden := hdenpos q'
    have hP₀R : (0 : ℝ) < (P₀ s : ℝ) := by exact_mod_cast hP₀pos s
    rw [abs_div, abs_mul, abs_of_pos hP₀R,
      abs_mul, abs_of_pos hpR, abs_of_pos hden]
    apply (div_lt_div_iff₀ (mul_pos hpR hden) hpR).2
    nlinarith

@[blueprint "lem:regular-arrangement-realization"
  (statement := /-- Let $A$ be a nonempty indexed line arrangement, let $k,r\in\NN_0$, and
suppose that distinct points of $R_{k,r}(A)$ have distinct first coordinates, where
$R_{k,r}(A)$ is the regular crossing set of \cref{def:regular-k-level-crossings}. Then there is
an apportionment instance $(p,H)$ with exactly $|A|$ states such that
\[
 |R_{k,r}(A)|\leq \#\operatorname{BP}(p,H),
\]
where $\operatorname{BP}(p,H)$ is the breaking-point set of
\cref{def:breaking-points}. -/)
  (proof := /-- The regular crossing set is finite because it is contained in the finite
$k$-level vertex set of \cref{lem:k-level-vertices-finite}. Apply
\cref{lem:regular-crossings-rational-model} to obtain positive rational parameters $P_i$,
rational parameters $T_i$, and an injective assignment of the regular crossings to positive
crossing parameters. At each assigned crossing, two selected lines
$(T_i+x)/P_i$ meet and exactly $r$ selected lines lie strictly below their common value.

The hypotheses of \cref{lem:rational-selected-line-model-realization} now hold with
$n=|A|$; the required positivity of $n$ is the assumed nonemptiness of $A$. That lemma clears
denominators, performs the projective normalization that places all modeled crossings in the
divisor interval with the required vertical margins, and realizes the injectively assigned
crossings as breaking points. Its cardinality conclusion is precisely the asserted inequality. -/)
  (title := /-- Realization of regular level crossings as breaking points -/)
  (latexEnv := "lemma")]
lemma regular_arrangement_realization (A : line_arrangement) (k r : ℕ)
    (hA : 0 < A.card)
    (hinj : Set.InjOn (fun q : ℝ × ℝ => q.1) (regular_k_level_crossings A k r)) :
    ∃ inst : apportionment_instance, inst.n = A.card ∧
      ((regular_k_level_crossings A k r).ncard : ℝ) ≤
        (num_breaking_points inst : ℝ) := by
  have hRfinite : (regular_k_level_crossings A k r).Finite :=
    (k_level_vertices_finite A k).subset fun q hq => hq.1
  obtain ⟨P, T, hP, ψ, hψ, hmodel⟩ :=
    regular_crossings_rational_model A k r hinj
  exact rational_selected_line_model_realization A.card r hA P T hP
    (regular_k_level_crossings A k r) hRfinite ψ hψ hmodel

@[blueprint "lem:instance-realizes-arrangement"
  (statement := /-- Let $h:\NN_0\to\RR$ witness a $k$-level lower bound in the sense of
\cref{def:k-level-witnessed-by}. Then there exist a constant $c\in\RR$ with $c>0$ and a threshold
$N\in\NN_0$ such that, for every $n\in\NN_0$ with $n\ge N$, there is an apportionment instance
$(p,H)$ with exactly $n$ states and at least $c\,h(n)$ breaking points (see
\cref{def:num-breaking-points}). -/)
  (proof := /-- Choose $c_0>0$ and $N_0$ from
\cref{def:k-level-witnessed-by}, and set $c=c_0/2$ and $N=\max\{N_0,1\}$. Fix $n\ge N$.
The witness hypothesis supplies an indexed arrangement $A$ with $|A|=n$, an index $k\leq n$,
stable $k$-level perturbation data, and the inequality
\[
 c_0h(n)\leq\operatorname{comp}_k(A).
\]
Apply \cref{lem:k-level-stable-regularization} to $A$, $k$, and this perturbation datum. It
gives an arrangement $A'$ of the same cardinality, a rank $r$ equal to $k$ or $k-1$, and a
regular crossing set
$R_{k,r}(A')$ with injective parameter projection such that
\[
 \operatorname{comp}_k(A)\leq 2|R_{k,r}(A')|.
\]
Because $n\ge1$, the arrangement $A'$ is nonempty. Therefore
\cref{lem:regular-arrangement-realization} supplies an apportionment instance $(p,H)$ with
exactly $|A'|=n$ states and at least $|R_{k,r}(A')|$ breaking points. Combining the three
inequalities and dividing by the positive number $2$ yields
\[
 (c_0/2)h(n)\leq \#\operatorname{BP}(p,H).
\]
Finally $c_0/2>0$, so the choices of $c$ and $N$ satisfy all the asserted quantifiers. -/)
  (title := /-- Asymptotic transfer from level complexity to breaking points -/)
  (latexEnv := "lemma")]
lemma instance_realizes_arrangement (h : ℕ → ℝ) (hh : k_level_witnessed_by h) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ inst : apportionment_instance, inst.n = n ∧
        c * h n ≤ (num_breaking_points inst : ℝ) := by
  rcases hh with ⟨c₀, hc₀, N₀, hw⟩
  refine ⟨c₀ / 2, by positivity, max N₀ 1, ?_⟩
  intro n hn
  have hN₀ : N₀ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnpos : 0 < n :=
    lt_of_lt_of_le Nat.zero_lt_one (le_trans (Nat.le_max_right _ _) hn)
  obtain ⟨A, hA, k, hk, hcomplex, hstable⟩ := hw n hN₀
  obtain ⟨A', r, hcard, hr, hinj, hcross⟩ :=
    k_level_stable_regularization A k hstable
  have hA' : 0 < A'.card := by
    rw [hcard, hA]
    exact hnpos
  obtain ⟨inst, hinst, hbreaking⟩ :=
    regular_arrangement_realization A' k r hA' hinj
  refine ⟨inst, ?_, ?_⟩
  · calc
      inst.n = A'.card := hinst
      _ = A.card := hcard
      _ = n := hA
  · linarith [hcomplex, hcross, hbreaking]

@[blueprint "thm:main-upper-bound"
  (statement := /-- Let $g:\NN_0\to\RR$ satisfy the uniform level-complexity bound and the
eventual two-scale regularity condition in \cref{def:k-level-bounded-by}. Then there exist a
constant $C>0$ and a threshold $N\in\NN_0$ such that, for every apportionment instance $(p,H)$
with $n\ge N$ states, the number of breaking points of $(p,H)$ (see
\cref{def:num-breaking-points}) is at most $C\,g(n)$. -/)
  (proof := /-- Unpack \cref{def:k-level-bounded-by}. Let $C_0>0$ and $N_0$ be the constants
for the level-complexity bound, and let $D>0$ and $N_1$ be the constants in
\cref{def:eventually-two-scale-dominates}. Increase the threshold so that $n\ge N_1$, and fix
an apportionment instance with $n$ states. By \cref{lem:reduction-lines}, there are an
arrangement $A$, of cardinality $m\leq 2n-1$, and an index $k\leq m$ such that the windowed
top-level complexity of the instance is at most $\operatorname{comp}_k(A)$.

Suppose first that $m\ge N_0$. The level-complexity bound gives
\[
 \operatorname{comp}_k(A)\leq C_0g(m),
\]
whereas two-scale domination gives
$g(m)\leq\max\{1,g(m)\}\leq Dg(n)$. Suppose instead that $m<N_0$. By
\cref{lem:k-level-complexity-card-bound},
$\operatorname{comp}_k(A)\leq m^2<N_0^2$, while two-scale domination gives
$1\leq Dg(n)$. Thus in both cases the level complexity is at most a constant, independent of
$n$, times $Dg(n)$.

Finally, \cref{lem:breaking-points-le-top-level} adds at most one to the windowed complexity.
The same inequality $1\leq Dg(n)$ absorbs this additive term. Since
$B=C_0+N_0^2+2$ is positive and dominates both $C_0+1$ and $N_0^2+1$, the preceding estimates
give
\[
 \#\operatorname{BP}(p,H)\leq B D g(n).
\]
Taking $C=DB>0$ proves the asserted eventual bound. -/)
  (title := /-- Upper bound on the number of breaking points -/)
  (latexEnv := "theorem")]
theorem main_upper_bound (g : ℕ → ℝ) (hg : k_level_bounded_by g) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ inst : apportionment_instance, N ≤ inst.n →
      (num_breaking_points inst : ℝ) ≤ C * g inst.n := by
  rcases hg with ⟨⟨C₀, hC₀, N₀, hlevel⟩, D, hD, N₁, hscale⟩
  let B : ℝ := C₀ + (N₀ : ℝ) ^ 2 + 2
  have hB : 0 < B := by
    dsimp [B]
    nlinarith [sq_nonneg (N₀ : ℝ)]
  refine ⟨D * B, mul_pos hD hB, N₁, ?_⟩
  intro inst hn
  obtain ⟨A, hcard, k, hk, hwindow⟩ := reduction_lines inst
  have hscale' := hscale inst.n hn A.card hcard
  have hunit : (1 : ℝ) ≤ D * g inst.n :=
    le_trans (le_max_left 1 (g A.card)) hscale'
  have hgA : g A.card ≤ D * g inst.n :=
    le_trans (le_max_right 1 (g A.card)) hscale'
  have hDgn : 0 ≤ D * g inst.n := by
    linarith
  have hbreak :
      (num_breaking_points inst : ℝ) ≤
        (top_level_window_complexity inst : ℝ) + 1 := by
    exact_mod_cast breaking_points_le_top_level inst
  have hwindow' :
      (top_level_window_complexity inst : ℝ) ≤
        (k_level_complexity A k : ℝ) := by
    exact_mod_cast hwindow
  calc
    (num_breaking_points inst : ℝ) ≤
        (top_level_window_complexity inst : ℝ) + 1 := hbreak
    _ ≤ (k_level_complexity A k : ℝ) + 1 := by
      linarith
    _ ≤ D * B * g inst.n := by
      by_cases hlarge : N₀ ≤ A.card
      · have hlevel' := hlevel A.card hlarge A rfl k hk
        have hmul :
            C₀ * g A.card ≤ C₀ * (D * g inst.n) :=
          mul_le_mul_of_nonneg_left hgA hC₀.le
        have hcoef : C₀ + 1 ≤ B := by
          dsimp [B]
          nlinarith [sq_nonneg (N₀ : ℝ)]
        have hmul' :
            (C₀ + 1) * (D * g inst.n) ≤ B * (D * g inst.n) :=
          mul_le_mul_of_nonneg_right hcoef hDgn
        calc
          (k_level_complexity A k : ℝ) + 1 ≤ C₀ * g A.card + 1 := by
            linarith
          _ ≤ C₀ * (D * g inst.n) + D * g inst.n :=
            add_le_add hmul hunit
          _ = (C₀ + 1) * (D * g inst.n) := by
            ring
          _ ≤ B * (D * g inst.n) := hmul'
          _ = D * B * g inst.n := by
            ring
      · have hcardle : A.card ≤ N₀ :=
          Nat.le_of_lt (Nat.lt_of_not_ge hlarge)
        have hcardle' : (A.card : ℝ) ≤ (N₀ : ℝ) := by
          exact_mod_cast hcardle
        have hsquare : (A.card : ℝ) ^ 2 ≤ (N₀ : ℝ) ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hcardle')
            (add_nonneg (Nat.cast_nonneg A.card) (Nat.cast_nonneg N₀))]
        have hquad :
            (k_level_complexity A k : ℝ) ≤ (A.card : ℝ) ^ 2 := by
          exact_mod_cast k_level_complexity_card_bound A k
        have hcoef : (N₀ : ℝ) ^ 2 + 1 ≤ B := by
          dsimp [B]
          linarith
        have hsmall_nonneg : 0 ≤ (N₀ : ℝ) ^ 2 + 1 := by
          positivity
        have hmul :
            ((N₀ : ℝ) ^ 2 + 1) * (D * g inst.n) ≤
              B * (D * g inst.n) :=
          mul_le_mul_of_nonneg_right hcoef hDgn
        calc
          (k_level_complexity A k : ℝ) + 1 ≤ (A.card : ℝ) ^ 2 + 1 := by
            linarith
          _ ≤ (N₀ : ℝ) ^ 2 + 1 := by
            linarith
          _ = ((N₀ : ℝ) ^ 2 + 1) * 1 := by
            ring
          _ ≤ ((N₀ : ℝ) ^ 2 + 1) * (D * g inst.n) :=
            mul_le_mul_of_nonneg_left hunit hsmall_nonneg
          _ ≤ B * (D * g inst.n) := hmul
          _ = D * B * g inst.n := by
            ring

@[blueprint "thm:main-lower-bound"
  (statement := /-- Let $h:\NN_0\to\RR$ witness a $k$-level lower bound in the sense of
\cref{def:k-level-witnessed-by}. Then there exist a constant $c>0$ and a threshold $N\in\NN_0$ such
that for every $n\in\NN_0$ with $n\ge N$ there is an apportionment instance $(p,H)$ with exactly $n$ states whose
number of breaking points (see \cref{def:num-breaking-points}) is at least $c\,h(n)$; that is,
there is an apportionment instance with $n$ states and $\Omega(h(n))$ breaking points. -/)
  (proof := /-- Let $h$ satisfy \cref{def:k-level-witnessed-by}, with constant $c>0$ and threshold
$N_0$. Apply the asymptotic transfer of \cref{lem:instance-realizes-arrangement} to $h$ and this
witness hypothesis. It supplies a constant $c'>0$ and a threshold $N'$ such that every
$n\ge N'$ admits an apportionment instance with exactly $n$ states and at least $c'h(n)$ breaking
points. Taking $c=c'$ and $N=N'$ gives precisely the asserted conclusion. -/)
  (title := /-- Lower bound on the number of breaking points -/)
  (latexEnv := "theorem")]
theorem main_lower_bound (h : ℕ → ℝ) (hh : k_level_witnessed_by h) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ inst : apportionment_instance, inst.n = n ∧
        c * h n ≤ (num_breaking_points inst : ℝ) := by
  exact instance_realizes_arrangement h hh

@[blueprint "thm:main"
  (statement := /-- Let $g:\NN_0\to\RR$ bound the $k$-level complexity as in
\cref{def:k-level-bounded-by}, and let $h:\NN_0\to\RR$ witness a $k$-level lower bound as in
\cref{def:k-level-witnessed-by}. Then: (i) there exist a constant $C>0$ and a threshold $N$ such
that for every apportionment instance with $n\ge N$ states, the number of breaking points is at
most $C\,g(n)$, i.e. $\calO(g(n))$; and (ii) there exist a constant $c>0$ and a threshold $N'$ such
that for every $n\ge N'$ there is an apportionment instance with $n$ states whose number of
breaking points is at least $c\,h(n)$, i.e. $\Omega(h(n))$. -/)
  (proof := /-- The first conclusion is \cref{thm:main-upper-bound} applied to $g$, and the second
conclusion is \cref{thm:main-lower-bound} applied to $h$. -/)
  (title := /-- Main theorem: tight bounds on breaking points via $k$-level complexity -/)
  (latexEnv := "theorem")]
theorem main (g h : ℕ → ℝ) (hg : k_level_bounded_by g) (hh : k_level_witnessed_by h) :
    (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ inst : apportionment_instance, N ≤ inst.n →
        (num_breaking_points inst : ℝ) ≤ C * g inst.n) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ inst : apportionment_instance, inst.n = n ∧
          c * h n ≤ (num_breaking_points inst : ℝ)) := by
  exact ⟨main_upper_bound g hg, main_lower_bound h hh⟩

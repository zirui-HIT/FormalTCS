import Architect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Linarith

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:apportionment-election"
  (statement := /-- For a positive integer $n$, an $n$-party election consists of a vote vector
  $v\colon \operatorname{Fin}(n)\to\mathbb{R}$, a positive integer house size $H$, the
  coordinate restrictions $0\leq v_i<1$ for every party $i$, and the identity
  $\sum_i v_i=H$. -/)
  (title := /-- Admissible election -/)
  (latexEnv := "definition")]
structure apportionment_election (n : ℕ) where
  votes : Fin n → ℝ
  seats : ℕ
  seats_pos : 0 < seats
  votes_mem_unit : ∀ i, votes i ∈ Set.Ico (0 : ℝ) 1
  sum_votes : (∑ i, votes i) = (seats : ℝ)

@[blueprint "def:apportionment-instance"
  (statement := /-- An $n$-dimensional apportionment instance is an infinite sequence
  $(v^t)_{t\in\mathbb{N}_0}$ of admissible $n$-party elections in the sense of
  \cref{def:apportionment-election}. -/)
  (title := /-- Apportionment instance -/)
  (latexEnv := "definition")]
abbrev apportionment_instance (n : ℕ) := ℕ → apportionment_election n

@[blueprint "def:seat-allocation"
  (statement := /-- An allocation in dimension $n$ is a finite set of parties. Membership means
  that the party receives the unique seat it can receive in the current election, as each vote
  coordinate lies in $[0,1)$. -/)
  (title := /-- Single-election seat allocation -/)
  (latexEnv := "definition")]
abbrev seat_allocation (n : ℕ) := Finset (Fin n)

@[blueprint "def:apportionment-state"
  (statement := /-- A cumulative apportionment state in dimension $n$ is a pair
  $\theta=(V,A)$, where $V_i\in\mathbb{R}$ is the cumulative vote entitlement and
  $A_i\in\mathbb{N}_0$ is the cumulative number of allocated seats for every party
  $i\in\operatorname{Fin}(n)$. -/)
  (title := /-- Cumulative apportionment state -/)
  (latexEnv := "definition")]
structure apportionment_state (n : ℕ) where
  cumulativeVotes : Fin n → ℝ
  cumulativeSeats : Fin n → ℕ

@[blueprint "def:online-apportionment-method"
  (statement := /-- A deterministic online apportionment method in dimension $n$ is a family of
  choice functions indexed by $t\in\mathbb{N}_0$.  At time $t$, the choice function receives
  exactly the cumulative state $\theta^{t-1}=(V^{t-1},A^{t-1})$ from
  \cref{def:apportionment-state} and the current election $v^t$.  It returns an allocation of
  cardinality $H^t$ containing only parties $i$ for which $v_i^t>0$. -/)
  (title := /-- Deterministic online apportionment method -/)
  (latexEnv := "definition")]
structure online_apportionment_method (n : ℕ) where
  choose : ℕ → apportionment_state n → apportionment_election n → seat_allocation n
  card_choose : ∀ t state election, (choose t state election).card = election.seats
  choose_positive :
    ∀ t state election i, i ∈ choose t state election → 0 < election.votes i

@[blueprint "def:online-apportionment-method-family"
  (statement := /-- An online apportionment method, without a fixed dimension, is a family
  $M=(M_n)_{n\in\mathbb{N}_0}$ in which $M_n$ is a deterministic online apportionment method
  for $n$ parties as in \cref{def:online-apportionment-method}. -/)
  (title := /-- Dimension-parametric online method -/)
  (latexEnv := "definition")]
abbrev online_apportionment_method_family :=
  (n : ℕ) → online_apportionment_method n

@[blueprint "def:induced-state"
  (statement := /-- Let $M$ be an online method and $v$ an instance.  The state before time
  $0$ has both cumulative vectors identically zero.  Recursively, if the state before time $t$ is
  $(V,A)$ and $X^t$ is the allocation selected by $M$ from $(t,(V,A),v^t)$, then the state before
  time $t+1$ is $(V',A')$, where $V'_i=V_i+v_i^t$ and
  $A'_i=A_i+\mathbf{1}_{\{i\in X^t\}}$ for every party $i$. -/)
  (title := /-- Cumulative state induced by a method and an instance -/)
  (latexEnv := "definition")]
def induced_state {n : ℕ} (method : online_apportionment_method n)
    (input : apportionment_instance n) : ℕ → apportionment_state n
  | 0 => { cumulativeVotes := fun _ => 0, cumulativeSeats := fun _ => 0 }
  | t + 1 =>
      let state := induced_state method input t
      let allocation := method.choose t state (input t)
      { cumulativeVotes := fun i => state.cumulativeVotes i + (input t).votes i
        cumulativeSeats := fun i => state.cumulativeSeats i + if i ∈ allocation then 1 else 0 }

@[blueprint "def:allocation-at"
  (statement := /-- The allocation made at time $t$ is the output of the online chooser applied
  at index $t$ to the cumulative state induced before time $t$ and to the current election
  $v^t$. -/)
  (title := /-- Allocation at a given time -/)
  (latexEnv := "definition")]
def allocation_at {n : ℕ} (method : online_apportionment_method n)
    (input : apportionment_instance n) (t : ℕ) : seat_allocation n :=
  method.choose t (induced_state method input t) (input t)

@[blueprint "def:cumulative-votes"
  (statement := /-- For a party $i$ and time $t$, its cumulative vote entitlement is
  $V_i^t=\sum_{k=0}^{t}v_i^k$. -/)
  (title := /-- Cumulative vote entitlement -/)
  (latexEnv := "definition")]
def cumulative_votes {n : ℕ} (input : apportionment_instance n)
    (t : ℕ) (i : Fin n) : ℝ :=
  ∑ k ∈ Finset.range (t + 1), (input k).votes i

@[blueprint "def:cumulative-seats"
  (statement := /-- For a method $M$, instance $v$, party $i$, and time $t$, the cumulative
  allocation $A_i^t$ is the number, regarded as a real number, of elections through time $t$ in
  which $i$ belongs to the allocation selected by $M$. -/)
  (title := /-- Cumulative allocated seats -/)
  (latexEnv := "definition")]
def cumulative_seats {n : ℕ} (method : online_apportionment_method n)
    (input : apportionment_instance n) (t : ℕ) (i : Fin n) : ℝ :=
  ∑ k ∈ Finset.range (t + 1),
    if i ∈ allocation_at method input k then (1 : ℝ) else 0

@[blueprint "def:apportionment-surplus"
  (statement := /-- The surplus of party $i$ through time $t$ is
  $s_i^t=A_i^t-V_i^t$, where $A_i^t$ and $V_i^t$ are given by
  \cref{def:cumulative-seats,def:cumulative-votes}. -/)
  (title := /-- Cumulative apportionment surplus -/)
  (latexEnv := "definition")]
def apportionment_surplus {n : ℕ} (method : online_apportionment_method n)
    (input : apportionment_instance n) (t : ℕ) (i : Fin n) : ℝ :=
  cumulative_seats method input t i - cumulative_votes input t i

@[blueprint "def:proportional"
  (statement := /-- A method $M$ is $\alpha$-proportional on an instance $v$ if, for every
  time $t\in\mathbb{N}_0$ and every party $i$, its cumulative discrepancy satisfies
  $\lvert A_i^t-V_i^t\rvert\leq\alpha$. -/)
  (title := /-- Weak proportionality -/)
  (latexEnv := "definition")]
def proportional {n : ℕ} (method : online_apportionment_method n)
    (input : apportionment_instance n) (α : ℝ) : Prop :=
  ∀ t i, |apportionment_surplus method input t i| ≤ α

@[blueprint "def:strictly-proportional"
  (statement := /-- A method $M$ is strictly $\alpha$-proportional on an instance $v$ if, for
  every time $t\in\mathbb{N}_0$ and every party $i$, its cumulative discrepancy satisfies
  $\lvert A_i^t-V_i^t\rvert<\alpha$. -/)
  (title := /-- Strict proportionality -/)
  (latexEnv := "definition")]
def strictly_proportional {n : ℕ} (method : online_apportionment_method n)
    (input : apportionment_instance n) (α : ℝ) : Prop :=
  ∀ t i, |apportionment_surplus method input t i| < α

@[blueprint "def:admissible-allocation"
  (statement := /-- For an admissible election $v$ of house size $H$, an allocation $X$ is
  admissible if $|X|=H$ and every party in $X$ has strictly positive current vote. -/)
  (title := /-- Admissibility of a one-step allocation -/)
  (latexEnv := "definition")]
def admissible_allocation {n : ℕ} (election : apportionment_election n)
    (allocation : seat_allocation n) : Prop :=
  allocation.card = election.seats ∧
    ∀ i, i ∈ allocation → 0 < election.votes i

@[blueprint "def:allocation-rounding-error"
  (statement := /-- Given an election $v$ and an allocation $X$, the one-step rounding error of
  party $i$ is $r_i(X,v)=\mathbf{1}_{\{i\in X\}}-v_i$. -/)
  (title := /-- One-step allocation error -/)
  (latexEnv := "definition")]
def allocation_rounding_error {n : ℕ} (election : apportionment_election n)
    (allocation : seat_allocation n) (i : Fin n) : ℝ :=
  (if i ∈ allocation then 1 else 0) - election.votes i

@[blueprint "def:skew-edge-invariant"
  (statement := /-- Let $s\in\mathbb{R}^n$.  A matrix $e=(e_{ij})$ is a bounded skew-edge
  representation of $s$ if $e_{ii}=0$, $e_{ij}=-e_{ji}$,
  $|e_{ij}|\leq 1/2$, and $s_i=\sum_j e_{ij}$ for every $i$. -/)
  (title := /-- Bounded skew-edge representation -/)
  (latexEnv := "definition")]
def skew_edge_invariant {n : ℕ} (s : Fin n → ℝ)
    (edge : Fin n → Fin n → ℝ) : Prop :=
  (∀ i, edge i i = 0) ∧
    (∀ i j, edge i j = -edge j i) ∧
    (∀ i j, |edge i j| ≤ (1 : ℝ) / 2) ∧
    (∀ i, s i = ∑ j, edge i j)

@[blueprint "def:greedy-step-spec"
  (statement := /-- Suppose that the present surplus vector $s$ has a bounded skew-edge
  representation $e$.  A pair $(X,e')$ satisfies the greedy one-step specification for the
  current election $v$ if $X$ is admissible and $e'$ is a bounded skew-edge representation of
  the updated surplus $s+r(X,v)$. -/)
  (title := /-- Specification of a greedy rounding step -/)
  (latexEnv := "definition")]
def greedy_step_spec {n : ℕ} (s : Fin n → ℝ) (edge : Fin n → Fin n → ℝ)
    (election : apportionment_election n) (allocation : seat_allocation n)
    (nextEdge : Fin n → Fin n → ℝ) : Prop :=
  skew_edge_invariant s edge ∧ admissible_allocation election allocation ∧
    skew_edge_invariant
      (fun i => s i + allocation_rounding_error election allocation i) nextEdge

@[blueprint "def:cyclic-half-open-three"
  (statement := /-- A skew-edge matrix in dimension three has the cyclic half-open orientation
  if the directed edges $0\to1$, $1\to2$, and $2\to0$ all lie in
  $[-1/2,1/2)$.  By skew-symmetry, the reverse directed edges then lie in
  $(-1/2,1/2]$. -/)
  (title := /-- Cyclic half-open endpoint convention -/)
  (latexEnv := "definition")]
def cyclic_half_open_three (edge : Fin 3 → Fin 3 → ℝ) : Prop :=
  edge 0 1 ∈ Set.Ico (-(1 : ℝ) / 2) ((1 : ℝ) / 2) ∧
    edge 1 2 ∈ Set.Ico (-(1 : ℝ) / 2) ((1 : ℝ) / 2) ∧
    edge 2 0 ∈ Set.Ico (-(1 : ℝ) / 2) ((1 : ℝ) / 2)

@[blueprint "lem:skew-edge-invariant-bound"
  (statement := /-- Let $n$ be positive.  If $s\in\mathbb{R}^n$ has a bounded skew-edge
  representation, then $|s_i|\leq(n-1)/2$ for every coordinate $i$. -/)
  (proof := /-- Fix $i$.  By \cref{def:skew-edge-invariant}, $s_i$ is the sum of the
  $n-1$ off-diagonal entries $e_{ij}$ with $j\ne i$, since $e_{ii}=0$.  The triangle
  inequality and $|e_{ij}|\leq 1/2$ therefore give
  $|s_i|\leq\sum_{j\ne i}|e_{ij}|\leq(n-1)/2$. -/)
  (title := /-- Discrepancy bound from the skew-edge invariant -/)
  (latexEnv := "lemma")]
lemma skew_edge_invariant_bound {n : ℕ} (hn : 0 < n) (s : Fin n → ℝ)
    (edge : Fin n → Fin n → ℝ) (hInvariant : skew_edge_invariant s edge) :
    ∀ i, |s i| ≤ (((n : ℝ) - 1) / 2) := by
  intro i
  rw [hInvariant.2.2.2 i]
  have h_abs (t : Finset (Fin n)) :
      |∑ j ∈ t, edge i j| ≤ ∑ j ∈ t, |edge i j| := by
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        exact (abs_add_le (edge i a) (∑ j ∈ t, edge i j)).trans
          (add_le_add_right ih |edge i a|)
  have h_bound (t : Finset (Fin n)) :
      (∑ j ∈ t, |edge i j|) ≤ ∑ j ∈ t, (1 : ℝ) / 2 := by
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        exact add_le_add (hInvariant.2.2.1 i a) ih
  calc
    |∑ j, edge i j| = |∑ j ∈ Finset.univ.erase i, edge i j| := by
      congr 1
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hInvariant.1 i, add_zero]
    _ ≤ ∑ j ∈ Finset.univ.erase i, |edge i j| := h_abs _
    _ ≤ ∑ j ∈ Finset.univ.erase i, (1 : ℝ) / 2 := h_bound _
    _ = ((n : ℝ) - 1) / 2 := by
      have hn1 : 1 ≤ n := hn
      simp [Finset.card_erase_of_mem, Nat.cast_sub hn1]
      rfl

@[blueprint "lem:complementary-matrix-round-pair"
  (statement := /-- Let $m$ be a finite matrix with entries in $[0,1]$ and
  $m_{ij}+m_{ji}=1$ for distinct indices.  If two diagonal entries are strictly between zero
  and one, they can be transferred against their complementary off-diagonal pair so that all
  row sums and the diagonal sum are preserved, every previously integral diagonal entry is
  unchanged, and at least one of the selected diagonal entries becomes integral. -/)
  (proof := /-- If $m_{pq}$ is at least $1-m_{pp}$, increase $m_{pp}$ and $m_{qp}$ while
  decreasing $m_{pq}$ and $m_{qq}$ by the smaller of $1-m_{pp}$ and $m_{qq}$.  Otherwise make
  the opposite transfer by the smaller of $m_{pp}$ and $1-m_{qq}$.  The chosen comparison
  guarantees that the complementary off-diagonal pair stays in $[0,1]$, the minimum guarantees
  that one selected diagonal reaches an endpoint, and the four signed changes cancel in each
  affected row, complementary pair, and diagonal sum. -/)
  (title := /-- A pairwise complementary-matrix rounding move -/)
  (latexEnv := "lemma")]
lemma complementary_matrix_round_pair {n : ℕ} (m : Fin n → Fin n → ℝ)
    (hBounds : ∀ i j, 0 ≤ m i j ∧ m i j ≤ 1)
    (hComplement : ∀ i j, i ≠ j → m i j + m j i = 1)
    (p q : Fin n) (hpq : p ≠ q) (hp : 0 < m p p ∧ m p p < 1)
    (hq : 0 < m q q ∧ m q q < 1) :
    ∃ m' : Fin n → Fin n → ℝ,
      (∀ i j, 0 ≤ m' i j ∧ m' i j ≤ 1) ∧
      (∀ i j, i ≠ j → m' i j + m' j i = 1) ∧
      (∀ i, ∑ j, m' i j = ∑ j, m i j) ∧
      ((∑ i, m' i i) = ∑ i, m i i) ∧
      (∀ i, m i i = 0 ∨ m i i = 1 → m' i i = m i i) ∧
      ((m' p p = 0 ∨ m' p p = 1) ∨ (m' q q = 0 ∨ m' q q = 1)) := by
  classical
  have transfer (ε : ℝ)
      (hpp : 0 ≤ m p p + ε ∧ m p p + ε ≤ 1)
      (hqq : 0 ≤ m q q - ε ∧ m q q - ε ≤ 1)
      (hpq' : 0 ≤ m p q - ε ∧ m p q - ε ≤ 1)
      (hend : m p p + ε = 0 ∨ m p p + ε = 1 ∨
        m q q - ε = 0 ∨ m q q - ε = 1) :
      ∃ m' : Fin n → Fin n → ℝ,
        (∀ i j, 0 ≤ m' i j ∧ m' i j ≤ 1) ∧
        (∀ i j, i ≠ j → m' i j + m' j i = 1) ∧
        (∀ i, ∑ j, m' i j = ∑ j, m i j) ∧
        ((∑ i, m' i i) = ∑ i, m i i) ∧
        (∀ i, m i i = 0 ∨ m i i = 1 → m' i i = m i i) ∧
        ((m' p p = 0 ∨ m' p p = 1) ∨ (m' q q = 0 ∨ m' q q = 1)) := by
    let c : Fin n → Fin n → ℝ := fun i j =>
      if i = p ∨ i = q then
        if j = p then ε else if j = q then -ε else 0
      else 0
    let m' : Fin n → Fin n → ℝ := fun i j => m i j + c i j
    have hcPair : ∀ i j, i ≠ j → c i j + c j i = 0 := by
      intro i j hij
      dsimp [c]
      by_cases hip : i = p <;> by_cases hiq : i = q <;>
        by_cases hjp : j = p <;> by_cases hjq : j = q <;> simp_all
    have hcRow : ∀ i, ∑ j, c i j = 0 := by
      intro i
      by_cases hi : i = p ∨ i = q
      · simp only [c, hi, if_pos]
        have hfun : (fun j : Fin n => if j = p then ε else if j = q then -ε else 0) =
            fun j => (if j = p then ε else 0) + (if j = q then -ε else 0) := by
          funext j
          by_cases hjp : j = p <;> by_cases hjq : j = q <;> simp_all
        rw [hfun, Finset.sum_add_distrib]
        rw [Finset.sum_eq_single p, Finset.sum_eq_single q] <;> simp_all
      · simp [c, hi]
    have hcDiag : (∑ i, c i i) = 0 := by
      have hfun : (fun i : Fin n => c i i) =
          fun i => (if i = p then ε else 0) + (if i = q then -ε else 0) := by
        funext i
        by_cases hip : i = p <;> by_cases hiq : i = q <;> simp_all [c]
      rw [hfun, Finset.sum_add_distrib]
      rw [Finset.sum_eq_single p, Finset.sum_eq_single q] <;> simp_all
    refine ⟨m', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      by_cases hip : i = p
      · subst i
        by_cases hjp : j = p
        · subst j
          simpa [m', c] using hpp
        · by_cases hjq : j = q
          · subst j
            simpa [m', c, hpq, Ne.symm hpq] using hpq'
          · simpa [m', c, hjp, hjq] using hBounds p j
      · by_cases hiq : i = q
        · subst i
          by_cases hjp : j = p
          · subst j
            simp only [m', c, hpq, Ne.symm hpq, or_true, if_pos]
            have hcomp := hComplement p q hpq
            have hqp : m q p = 1 - m p q := by
              apply (eq_sub_iff_add_eq).2
              simpa [add_comm] using hcomp
            rw [hqp]
            constructor
            · rw [show 1 - m p q + ε = 1 - (m p q - ε) by
                simp only [sub_eq_add_neg, neg_add_rev, neg_neg]
                exact (add_assoc 1 (-m p q) ε).trans
                  (congrArg (fun z : ℝ => 1 + z) (add_comm (-m p q) ε))]
              exact sub_nonneg.mpr hpq'.2
            · rw [show 1 - m p q + ε = 1 - (m p q - ε) by
                simp only [sub_eq_add_neg, neg_add_rev, neg_neg]
                exact (add_assoc 1 (-m p q) ε).trans
                  (congrArg (fun z : ℝ => 1 + z) (add_comm (-m p q) ε))]
              exact sub_le_self 1 hpq'.1
          · by_cases hjq : j = q
            · subst j
              simpa [m', c, hpq, Ne.symm hpq] using hqq
            · simpa [m', c, hjp, hjq] using hBounds q j
        · simpa [m', c, hip, hiq] using hBounds i j
    · intro i j hij
      calc
        m' i j + m' j i = (m i j + m j i) + (c i j + c j i) := by
          dsimp [m']
          ac_rfl
        _ = 1 := by rw [hComplement i j hij, hcPair i j hij]; norm_num
    · intro i
      change (Finset.univ.sum fun j => m i j + c i j) = Finset.univ.sum (m i)
      rw [Finset.sum_add_distrib, hcRow i, add_zero]
    · change (Finset.univ.sum fun i => m i i + c i i) =
          Finset.univ.sum fun i => m i i
      rw [Finset.sum_add_distrib, hcDiag, add_zero]
    · intro i hi
      rcases hi with hi | hi
      · have hip : i ≠ p := by
          intro h
          subst i
          exact hp.1.ne' hi
        have hiq : i ≠ q := by
          intro h
          subst i
          exact hq.1.ne' hi
        simp [m', c, hip, hiq]
      · have hip : i ≠ p := by
          intro h
          subst i
          exact hp.2.ne hi
        have hiq : i ≠ q := by
          intro h
          subst i
          exact hq.2.ne hi
        simp [m', c, hip, hiq]
    · simp only [m', c, hpq, Ne.symm hpq, or_true, if_pos, if_false]
      rcases hend with hend | hend | hend | hend
      · exact Or.inl (Or.inl hend)
      · exact Or.inl (Or.inr hend)
      · exact Or.inr (Or.inl (by simpa only [sub_eq_add_neg] using hend))
      · exact Or.inr (Or.inr (by simpa only [sub_eq_add_neg] using hend))
  by_cases hdir : 1 - m p p ≤ m p q
  · let δ := min (1 - m p p) (m q q)
    have hδnonneg : 0 ≤ δ := by
      dsimp [δ]
      exact le_min (sub_nonneg.mpr (le_of_lt hp.2)) (le_of_lt hq.1)
    have hδp : δ ≤ 1 - m p p := min_le_left _ _
    have hδq : δ ≤ m q q := min_le_right _ _
    have hδedge : δ ≤ m p q := hδp.trans hdir
    have hnewpqUpper : m p q - δ ≤ 1 :=
      (sub_le_self _ hδnonneg).trans (hBounds p q).2
    have hend : m p p + δ = 0 ∨ m p p + δ = 1 ∨
        m q q - δ = 0 ∨ m q q - δ = 1 := by
      rcases min_choice (1 - m p p) (m q q) with hδ | hδ
      · right; left; dsimp [δ]; rw [hδ, add_comm, sub_add_cancel]
      · right; right; left; dsimp [δ]; rw [hδ, sub_self]
    exact transfer δ
      ⟨add_nonneg (le_of_lt hp.1) hδnonneg,
        by simpa [add_comm] using (le_sub_iff_add_le).1 hδp⟩
      ⟨sub_nonneg.mpr hδq, (sub_le_self _ hδnonneg).trans (le_of_lt hq.2)⟩
      ⟨sub_nonneg.mpr hδedge, hnewpqUpper⟩ hend
  · let δ := min (m p p) (1 - m q q)
    have hδnonneg : 0 ≤ δ := by
      dsimp [δ]
      exact le_min (le_of_lt hp.1) (sub_nonneg.mpr (le_of_lt hq.2))
    have hδp : δ ≤ m p p := min_le_left _ _
    have hδq : δ ≤ 1 - m q q := min_le_right _ _
    have hδedge : δ ≤ 1 - m p q := by
      apply hδp.trans
      apply le_of_lt
      apply (lt_sub_iff_add_lt).2
      have h := (lt_sub_iff_add_lt).1 (lt_of_not_ge hdir)
      simpa [add_comm] using h
    have hnewpqLower : 0 ≤ m p q + δ :=
      add_nonneg (hBounds p q).1 hδnonneg
    have hend : m p p - δ = 0 ∨ m p p - δ = 1 ∨
        m q q + δ = 0 ∨ m q q + δ = 1 := by
      rcases min_choice (m p p) (1 - m q q) with hδ | hδ
      · left; dsimp [δ]; rw [hδ, sub_self]
      · right; right; right; dsimp [δ]; rw [hδ, add_comm, sub_add_cancel]
    have hqUpper : m q q + δ ≤ 1 := by
      simpa [add_comm] using (le_sub_iff_add_le).1 hδq
    have hedgeUpper : m p q + δ ≤ 1 := by
      simpa [add_comm] using (le_sub_iff_add_le).1 hδedge
    exact transfer (-δ)
      (by simpa only [sub_eq_add_neg] using
        And.intro (sub_nonneg.mpr hδp) ((sub_le_self _ hδnonneg).trans (le_of_lt hp.2)))
      (by simpa only [sub_neg_eq_add] using
        And.intro (add_nonneg (le_of_lt hq.1) hδnonneg) hqUpper)
      (by simpa only [sub_neg_eq_add] using
        And.intro hnewpqLower hedgeUpper)
      (by simpa only [sub_eq_add_neg, sub_neg, neg_neg] using hend)

@[blueprint "lem:bounded-skew-matrix-diagonal-rounding"
  (statement := /-- Let $m$ be a finite real matrix with entries in $[0,1]$, with
  $m_{ij}+m_{ji}=1$ off the diagonal, and with integral diagonal sum $H$.  There is a matrix
  $m'$ with the same row sums and diagonal sum, the same bounds and complementary-pair
  identities, and diagonal entries all belonging to $\{0,1\}$.  Moreover, every zero diagonal
  entry of $m$ remains zero in $m'$. -/)
  (proof := /-- Repeatedly select two nonintegral diagonal entries and apply
  \cref{lem:complementary-matrix-round-pair}.  A signed transfer between
  the two diagonal entries and the corresponding complementary off-diagonal pair preserves both
  affected row sums and the identity $m_{ij}+m_{ji}=1$.  Choose the sign according to whether
  $m_{ij}$ has enough room below or above; then increase the transfer until one of the two
  diagonal entries reaches $0$ or $1$.  This never changes a diagonal entry already equal to
  zero or one, so induction on the number of nonintegral diagonal entries terminates.  That
  number cannot be one, because the diagonal sum is the integer $H$. -/)
  (title := /-- Rounding the diagonal of a complementary matrix -/)
  (latexEnv := "lemma")]
lemma bounded_skew_matrix_diagonal_rounding {n H : ℕ} (m : Fin n → Fin n → ℝ)
    (hBounds : ∀ i j, 0 ≤ m i j ∧ m i j ≤ 1)
    (hComplement : ∀ i j, i ≠ j → m i j + m j i = 1)
    (hDiagonalSum : (∑ i, m i i) = (H : ℝ)) :
    ∃ m' : Fin n → Fin n → ℝ,
      (∀ i j, 0 ≤ m' i j ∧ m' i j ≤ 1) ∧
      (∀ i j, i ≠ j → m' i j + m' j i = 1) ∧
      (∀ i, ∑ j, m' i j = ∑ j, m i j) ∧
      ((∑ i, m' i i) = (H : ℝ)) ∧
      (∀ i, m' i i = 0 ∨ m' i i = 1) ∧
      (∀ i, m i i = 0 → m' i i = 0) := by
  classical
  let bad : (Fin n → Fin n → ℝ) → Finset (Fin n) := fun x =>
    Finset.univ.filter fun i => x i i ≠ 0 ∧ x i i ≠ 1
  let Good : (Fin n → Fin n → ℝ) → Prop := fun x =>
    (∀ i j, 0 ≤ x i j ∧ x i j ≤ 1) ∧
    (∀ i j, i ≠ j → x i j + x j i = 1) ∧
    (∀ i, ∑ j, x i j = ∑ j, m i j) ∧
    ((∑ i, x i i) = (H : ℝ)) ∧
    (∀ i, m i i = 0 → x i i = 0)
  have hmGood : Good m := by
    refine ⟨hBounds, hComplement, ?_, hDiagonalSum, ?_⟩
    · intro i
      rfl
    · intro i hi
      exact hi
  have hex : ∃ k : ℕ, ∃ x : Fin n → Fin n → ℝ,
      Good x ∧ (bad x).card = k := by
    exact ⟨(bad m).card, m, hmGood, rfl⟩
  let k := Nat.find hex
  obtain ⟨x, hxGood, hxCard⟩ := Nat.find_spec hex
  have hminimal : ∀ y : Fin n → Fin n → ℝ, Good y → k ≤ (bad y).card := by
    intro y hy
    exact Nat.find_min' hex ⟨y, hy, rfl⟩
  have hbadEmpty : bad x = ∅ := by
    by_contra hne
    have hbadNonempty : (bad x).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨p, hpBad⟩ := hbadNonempty
    have hpNe : x p p ≠ 0 ∧ x p p ≠ 1 := by
      simpa [bad] using hpBad
    have hp : 0 < x p p ∧ x p p < 1 := by
      exact ⟨lt_of_le_of_ne (hxGood.1 p p).1 hpNe.1.symm,
        lt_of_le_of_ne (hxGood.1 p p).2 hpNe.2⟩
    have hqExists : ∃ q, q ∈ bad x ∧ q ≠ p := by
      by_contra hnone
      have hother : ∀ i, i ≠ p → x i i = 0 ∨ x i i = 1 := by
        intro i hip
        by_cases hi0 : x i i = 0
        · exact Or.inl hi0
        · by_cases hi1 : x i i = 1
          · exact Or.inr hi1
          · exfalso
            exact hnone ⟨i, by simp [bad, hi0, hi1], hip⟩
      let ones := (Finset.univ.erase p).filter fun i => x i i = 1
      have hsumOther : (∑ i ∈ Finset.univ.erase p, x i i) = (ones.card : ℝ) := by
        calc
          (∑ i ∈ Finset.univ.erase p, x i i) =
              ∑ i ∈ Finset.univ.erase p, (if x i i = 1 then (1 : ℝ) else 0) := by
                apply Finset.sum_congr rfl
                intro i hi
                have hip : i ≠ p := by
                  intro h
                  subst i
                  simpa using hi
                rcases hother i hip with hi0 | hi1
                · simp [hi0]
                · simp [hi1]
          _ = (ones.card : ℝ) := by
            rw [← Finset.sum_filter]
            simp [ones]
      have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => x i i) (Finset.mem_univ p)
      have hpSum : x p p + (ones.card : ℝ) = (H : ℝ) := by
        calc
          x p p + (ones.card : ℝ) =
              (∑ i ∈ Finset.univ.erase p, x i i) + x p p := by
                rw [hsumOther]
                exact add_comm _ _
          _ = ∑ i, x i i := hsplit
          _ = (H : ℝ) := hxGood.2.2.2.1
      have hcardReal : (ones.card : ℝ) < (H : ℝ) := by
        calc
          (ones.card : ℝ) = 0 + (ones.card : ℝ) := by rw [zero_add]
          _ < x p p + (ones.card : ℝ) := by
            simpa [add_comm] using add_lt_add_right hp.1 (ones.card : ℝ)
          _ = (H : ℝ) := hpSum
      have hhouseReal : (H : ℝ) < (ones.card : ℝ) + 1 := by
        calc
          (H : ℝ) = x p p + (ones.card : ℝ) := hpSum.symm
          _ < 1 + (ones.card : ℝ) := by
            simpa [add_comm] using add_lt_add_right hp.2 (ones.card : ℝ)
          _ = (ones.card : ℝ) + 1 := add_comm _ _
      have hcardNat : ones.card < H := (Nat.cast_lt (α := ℝ)).mp hcardReal
      have hhouseNat : H < ones.card + 1 := by
        exact (Nat.cast_lt (α := ℝ)).mp (by simpa using hhouseReal)
      exact (not_lt_of_ge (Nat.succ_le_of_lt hcardNat)) hhouseNat
    obtain ⟨q, hqBad, hqp⟩ := hqExists
    have hqNe : x q q ≠ 0 ∧ x q q ≠ 1 := by
      simpa [bad] using hqBad
    have hq : 0 < x q q ∧ x q q < 1 := by
      exact ⟨lt_of_le_of_ne (hxGood.1 q q).1 hqNe.1.symm,
        lt_of_le_of_ne (hxGood.1 q q).2 hqNe.2⟩
    obtain ⟨y, hyBounds, hyComplement, hyRows, hyDiagonal, hyIntegral, hyEndpoint⟩ :=
      complementary_matrix_round_pair x hxGood.1 hxGood.2.1 p q hqp.symm hp hq
    have hyGood : Good y := by
      refine ⟨hyBounds, hyComplement, ?_, ?_, ?_⟩
      · intro i
        exact (hyRows i).trans (hxGood.2.2.1 i)
      · exact hyDiagonal.trans hxGood.2.2.2.1
      · intro i hi
        have hxi : x i i = 0 := hxGood.2.2.2.2 i hi
        exact (hyIntegral i (Or.inl hxi)).trans hxi
    have hsubset : bad y ⊆ bad x := by
      intro i hi
      have hiNe : y i i ≠ 0 ∧ y i i ≠ 1 := by simpa [bad] using hi
      by_cases hi0 : x i i = 0
      · have := hyIntegral i (Or.inl hi0)
        exact False.elim (hiNe.1 (this.trans hi0))
      · by_cases hi1 : x i i = 1
        · have := hyIntegral i (Or.inr hi1)
          exact False.elim (hiNe.2 (this.trans hi1))
        · simp [bad, hi0, hi1]
    have hstrict : bad y ⊂ bad x := by
      apply (Finset.ssubset_iff_of_subset hsubset).2
      rcases hyEndpoint with hpEnd | hqEnd
      · refine ⟨p, hpBad, ?_⟩
        intro hpMem
        have hpNeY : y p p ≠ 0 ∧ y p p ≠ 1 := by simpa [bad] using hpMem
        exact hpEnd.elim hpNeY.1 hpNeY.2
      · refine ⟨q, hqBad, ?_⟩
        intro hqMem
        have hqNeY : y q q ≠ 0 ∧ y q q ≠ 1 := by simpa [bad] using hqMem
        exact hqEnd.elim hqNeY.1 hqNeY.2
    have hless : (bad y).card < (bad x).card := Finset.card_lt_card hstrict
    have hminY : k ≤ (bad y).card := hminimal y hyGood
    change (bad x).card = k at hxCard
    rw [hxCard] at hless
    exact (not_lt_of_ge hminY) hless
  refine ⟨x, hxGood.1, hxGood.2.1, hxGood.2.2.1, hxGood.2.2.2.1, ?_,
    hxGood.2.2.2.2⟩
  intro i
  have hi : i ∉ bad x := by simp [hbadEmpty]
  by_cases hi0 : x i i = 0
  · exact Or.inl hi0
  · right
    by_contra hi1
    exact hi (by simp [bad, hi0, hi1])

@[blueprint "lem:bounded-skew-rounding-step"
  (statement := /-- Let $n$ be positive, let $s\in\mathbb{R}^n$ have a bounded skew-edge
  representation, and let $v$ be an admissible $n$-party election.  There are an allocation
  $X$ and a new edge matrix $e'$ satisfying the greedy one-step specification for $(s,v)$. -/)
  (proof := /-- Form the complementary matrix $m$ by putting $m_{ii}=v_i$ and
  $m_{ij}=1/2-e_{ij}$ for $i\ne j$.  The election conditions and
  \cref{def:skew-edge-invariant} imply that its entries lie in $[0,1]$, its off-diagonal pairs
  sum to one, and its diagonal sum is the integer house size.  Apply
  \cref{lem:bounded-skew-matrix-diagonal-rounding}.  Let $X$ be the set of indices whose rounded
  diagonal entry is one.  Preservation of the diagonal sum gives $|X|=H$, and preservation of
  initial diagonal zeroes ensures that every member of $X$ has positive vote.  Define $e'_{ii}=0$
  and $e'_{ij}=1/2-m'_{ij}$ for $i\ne j$.  The complementary-pair identities and bounds give
  skew-symmetry and the half-unit bound for $e'$.  Finally, preservation of each row sum gives
  $\sum_j e'_{ij}=s_i+\mathbf{1}_{\{i\in X\}}-v_i$.  Thus $(X,e')$ satisfies
  \cref{def:greedy-step-spec}. -/)
  (title := /-- One-step bounded-skew rounding -/)
  (latexEnv := "lemma")]
lemma bounded_skew_rounding_step {n : ℕ} (hn : 0 < n) (s : Fin n → ℝ)
    (edge : Fin n → Fin n → ℝ) (hInvariant : skew_edge_invariant s edge)
    (election : apportionment_election n) :
    ∃ allocation : seat_allocation n, ∃ nextEdge : Fin n → Fin n → ℝ,
      greedy_step_spec s edge election allocation nextEdge := by
  classical
  rcases hInvariant with ⟨hEdgeDiag, hEdgeSkew, hEdgeBound, hEdgeRow⟩
  have hhalf : (1 : ℝ) / 2 + (1 : ℝ) / 2 = 1 := by
    rw [← add_div, add_self_div_two]
  let m : Fin n → Fin n → ℝ := fun i j =>
    if i = j then election.votes i else (1 : ℝ) / 2 - edge i j
  have hmBounds : ∀ i j, 0 ≤ m i j ∧ m i j ≤ 1 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa [m] using And.intro (election.votes_mem_unit i).1
        (le_of_lt (election.votes_mem_unit i).2)
    · have he := (abs_le.mp (hEdgeBound i j))
      constructor
      · simp only [m, hij, if_false]
        exact sub_nonneg.mpr he.2
      · simp only [m, hij, if_false]
        apply (sub_le_iff_le_add).2
        have hnonneg : 0 ≤ (1 : ℝ) / 2 + edge i j := by
          simpa [add_comm] using (neg_le_iff_add_nonneg').1 he.1
        calc
          (1 : ℝ) / 2 = (1 : ℝ) / 2 + 0 := by rw [add_zero]
          _ ≤ (1 : ℝ) / 2 + ((1 : ℝ) / 2 + edge i j) :=
            by simpa [add_assoc, add_comm, add_left_comm] using
              add_le_add_left hnonneg ((1 : ℝ) / 2)
          _ = 1 + edge i j := by rw [← add_assoc, hhalf]
  have hmComplement : ∀ i j, i ≠ j → m i j + m j i = 1 := by
    intro i j hij
    simp only [m, hij, Ne.symm hij, if_false]
    rw [hEdgeSkew i j]
    calc
      (1 : ℝ) / 2 - -edge j i + ((1 : ℝ) / 2 - edge j i) =
          ((1 : ℝ) / 2 + (1 : ℝ) / 2) + (edge j i + -edge j i) := by
            simp only [sub_eq_add_neg, neg_neg]
            ac_rfl
      _ = 1 := by rw [add_neg_cancel, add_zero, hhalf]
  have hmDiagonalSum : (∑ i, m i i) = (election.seats : ℝ) := by
    simpa [m] using election.sum_votes
  obtain ⟨m', hm'Bounds, hm'Complement, hm'Rows, hm'DiagonalSum, hm'Diagonal,
      hm'Zero⟩ :=
    bounded_skew_matrix_diagonal_rounding m hmBounds hmComplement hmDiagonalSum
  let allocation : seat_allocation n := Finset.univ.filter fun i => m' i i = 1
  let nextEdge : Fin n → Fin n → ℝ := fun i j =>
    if i = j then 0 else (1 : ℝ) / 2 - m' i j
  refine ⟨allocation, nextEdge, ?_⟩
  unfold greedy_step_spec
  refine ⟨⟨hEdgeDiag, hEdgeSkew, hEdgeBound, hEdgeRow⟩, ?_, ?_⟩
  · constructor
    · have hcast : (allocation.card : ℝ) = (election.seats : ℝ) := by
        calc
        (allocation.card : ℝ) = ∑ i, m' i i := by
          have hsum : (∑ i, m' i i) =
              ∑ i, (if m' i i = 1 then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            rcases hm'Diagonal i with hi0 | hi1
            · simp [hi0]
            · simp [hi1]
          rw [hsum]
          rw [← Finset.sum_filter]
          simp [allocation]
        _ = (election.seats : ℝ) := hm'DiagonalSum
      exact Nat.cast_injective hcast
    · intro i hi
      have hiOne : m' i i = 1 := by simpa [allocation] using hi
      have hVoteNonzero : election.votes i ≠ 0 := by
        intro hzero
        have hmZero : m i i = 0 := by simp [m, hzero]
        have := hm'Zero i hmZero
        rw [hiOne] at this
        norm_num at this
      exact lt_of_le_of_ne (election.votes_mem_unit i).1 hVoteNonzero.symm
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      simp [nextEdge]
    · intro i j
      by_cases hij : i = j
      · subst j
        simp [nextEdge]
      · have hcomp := hm'Complement i j hij
        have hji : m' j i = 1 - m' i j := by
          apply (eq_sub_iff_add_eq).2
          simpa [add_comm] using hcomp
        simp only [nextEdge, hij, Ne.symm hij, if_false, hji]
        have hsecond : (1 : ℝ) / 2 - (1 - m' i j) =
            m' i j - (1 : ℝ) / 2 := by
          apply (sub_eq_sub_iff_add_eq_add).2
          simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hhalf
        rw [hsecond, neg_sub]
    · intro i j
      by_cases hij : i = j
      · subst j
        simp [nextEdge]
      · simp only [nextEdge, hij, if_false]
        apply abs_le.mpr
        constructor
        · apply (neg_le_sub_iff_le_add).2
          rw [hhalf]
          exact (hm'Bounds i j).2
        · exact sub_le_self _ (hm'Bounds i j).1
    · intro i
      let off : Finset (Fin n) := Finset.univ.erase i
      let constant : ℝ := ∑ _j ∈ off, (1 : ℝ) / 2
      have hiMem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
      have hnextSum : (∑ j, nextEdge i j) =
          constant - ∑ j ∈ off, m' i j := by
        calc
          (∑ j, nextEdge i j) = ∑ j ∈ off, nextEdge i j := by
            have hsplit := Finset.sum_erase_add
              (s := (Finset.univ : Finset (Fin n))) (f := nextEdge i) hiMem
            simpa [off, nextEdge] using hsplit.symm
          _ = ∑ j ∈ off, ((1 : ℝ) / 2 - m' i j) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hij : i ≠ j := by
              intro h
              subst j
              simpa [off] using hj
            simp [nextEdge, hij]
          _ = constant - ∑ j ∈ off, m' i j := by
            rw [Finset.sum_sub_distrib]
      have hedgeSum : (∑ j, edge i j) =
          constant - ∑ j ∈ off, m i j := by
        rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n)))
          (f := edge i) hiMem]
        rw [hEdgeDiag i, add_zero]
        have hoff : (∑ j ∈ off, edge i j) =
            ∑ j ∈ off, ((1 : ℝ) / 2 - m i j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hij : i ≠ j := by
            intro h
            subst j
            simpa [off] using hj
          simp [m, hij]
        rw [hoff, Finset.sum_sub_distrib]
      have hmSplit : (∑ j ∈ off, m' i j) + m' i i =
          (∑ j ∈ off, m i j) + m i i := by
        calc
          (∑ j ∈ off, m' i j) + m' i i = ∑ j, m' i j :=
            Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n)))
              (f := m' i) hiMem
          _ = ∑ j, m i j := hm'Rows i
          _ = (∑ j ∈ off, m i j) + m i i :=
            (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n)))
              (f := m i) hiMem).symm
      have hdiff : (∑ j ∈ off, m i j) - (∑ j ∈ off, m' i j) =
          m' i i - m i i := by
        apply (sub_eq_sub_iff_add_eq_add).2
        simpa [add_comm] using hmSplit.symm
      have hmDiag : m i i = election.votes i := by simp [m]
      have hm'DiagIndicator : m' i i = if i ∈ allocation then 1 else 0 := by
        rcases hm'Diagonal i with hi0 | hi1
        · simp [allocation, hi0]
        · simp [allocation, hi1]
      change s i + allocation_rounding_error election allocation i = ∑ j, nextEdge i j
      rw [hnextSum, hEdgeRow i, hedgeSum]
      unfold allocation_rounding_error
      rw [← hmDiag, ← hm'DiagIndicator]
      symm
      calc
        constant - (∑ j ∈ off, m' i j) =
            ((∑ j ∈ off, m i j) - (∑ j ∈ off, m' i j)) +
              (constant - ∑ j ∈ off, m i j) :=
                sub_eq_sub_add_sub constant (∑ j ∈ off, m' i j)
                  (∑ j ∈ off, m i j)
        _ = (constant - ∑ j ∈ off, m i j) + (m' i i - m i i) := by
          rw [hdiff, add_comm]

@[blueprint "lem:cyclic-three-strict-bound"
  (statement := /-- If $s\in\mathbb{R}^3$ has a bounded skew-edge representation with the cyclic
  half-open orientation, then $|s_i|<1$ for every coordinate $i$. -/)
  (proof := /-- Fix a vertex $i$ of the directed cycle.  By
  \cref{def:skew-edge-invariant}, its row sum is the sum of its two off-diagonal edge values.
  By \cref{def:cyclic-half-open-three}, the outgoing cyclic edge belongs to
  $[-1/2,1/2)$, whereas skew-symmetry places the incoming cyclic edge in
  $(-1/2,1/2]$.  Their sum consequently lies in $(-1,1)$, and hence $|s_i|<1$. -/)
  (title := /-- Strict three-party bound from cyclic endpoints -/)
  (latexEnv := "lemma")]
lemma cyclic_three_strict_bound (s : Fin 3 → ℝ) (edge : Fin 3 → Fin 3 → ℝ)
    (hInvariant : skew_edge_invariant s edge) (hCyclic : cyclic_half_open_three edge) :
    ∀ i, |s i| < 1 := by
  rcases hInvariant with ⟨hdiag, hskew, _, hsum⟩
  rcases hCyclic with ⟨⟨h01l, h01u⟩, ⟨h12l, h12u⟩, ⟨h20l, h20u⟩⟩
  have hhalf : (1 : ℝ) / 2 + 1 / 2 = 1 := by
    rw [← add_div]
    norm_num
  have hsub : (1 : ℝ) - 1 / 2 = 1 / 2 := (sub_eq_iff_eq_add).2 hhalf.symm
  have hshift (x : ℝ) (hx : (-(1 : ℝ) / 2) ≤ x) : (1 : ℝ) / 2 ≤ 1 + x := by
    calc
      (1 : ℝ) / 2 = 1 - 1 / 2 := hsub.symm
      _ = 1 + (-(1 : ℝ) / 2) := by rw [sub_eq_add_neg, neg_div]
      _ ≤ 1 + x := add_le_add_right hx 1
  have hshiftRight (x : ℝ) (hx : (-(1 : ℝ) / 2) ≤ x) : (1 : ℝ) / 2 ≤ x + 1 := by
    simpa only [add_comm] using hshift x hx
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  obtain rfl | rfl | rfl := hi
  · rw [hsum, huniv]
    simp [hdiag, hskew 0 2, abs_lt]
    exact ⟨h20u.trans_le (hshift _ h01l), h01u.trans_le (hshift _ h20l)⟩
  · rw [hsum, huniv]
    simp [hdiag, hskew 1 0, abs_lt]
    exact ⟨h01u.trans_le (hshiftRight _ h12l), h12u.trans_le (hshiftRight _ h01l)⟩
  · rw [hsum, huniv]
    simp [hdiag, hskew 2 1, abs_lt]
    exact ⟨h12u.trans_le (hshift _ h20l), h20u.trans_le (hshift _ h12l)⟩

@[blueprint "lem:cyclic-three-strict-representation"
  (statement := /-- Let $t\in\mathbb{R}^3$ have coordinate sum zero and satisfy
  $|t_i|<1$ for every $i$.  Then $t$ has a bounded skew-edge representation whose cyclic
  edges $0\to1$, $1\to2$, and $2\to0$ lie in $[-1/2,1/2)$. -/)
  (proof := /-- Put $q_0=0$, $q_1=t_1$, and $q_2=-t_0$.  The zero-sum identity shows that every
  difference $q_i-q_j$ is one of $\pm t_0,\pm t_1,\pm t_2$, and therefore has absolute value
  less than one.  If $m=\min\{q_0,q_1,q_2\}$, the three numbers
  $a_i=q_i-m-1/2$ consequently belong to $[-1/2,1/2)$.  Assign $a_0,a_1,a_2$ to the cyclic
  edges and their negatives to the reverse edges.  Direct subtraction gives row sums
  $t_0,t_1,t_2$, while the construction gives a zero diagonal, skew-symmetry, the half-unit
  bound, and the required half-open cyclic convention; hence
  \cref{def:skew-edge-invariant, def:cyclic-half-open-three} hold. -/)
  (title := /-- Cyclic representation of a strict three-vector -/)
  (latexEnv := "lemma")]
lemma cyclic_three_strict_representation (t : Fin 3 → ℝ)
    (hsum : t 0 + t 1 + t 2 = 0) (hstrict : ∀ i, |t i| < 1) :
    ∃ edge : Fin 3 → Fin 3 → ℝ,
      skew_edge_invariant t edge ∧ cyclic_half_open_three edge := by
  have ht0 := (abs_lt.mp (hstrict 0))
  have ht1 := (abs_lt.mp (hstrict 1))
  have ht2 := (abs_lt.mp (hstrict 2))
  let q0 : ℝ := 0
  let q1 : ℝ := t 1
  let q2 : ℝ := -t 0
  let m : ℝ := min q0 (min q1 q2)
  have hq01 : |q0 - q1| < 1 := by
    simpa [q0, q1] using hstrict 1
  have hq02 : |q0 - q2| < 1 := by
    dsimp [q0, q2]
    simpa using hstrict 0
  have hq12 : |q1 - q2| < 1 := by
    dsimp [q1, q2]
    have : t 1 + t 0 = -t 2 :=
      (eq_neg_iff_add_eq_zero).2 (by simpa [add_comm] using hsum)
    rw [sub_neg_eq_add, this, abs_neg]
    exact hstrict 2
  have hq (q : ℝ) (hmle : m ≤ q) (hq0 : |q - q0| < 1) (hq1 : |q - q1| < 1)
      (hq2 : |q - q2| < 1) : -(1 : ℝ) / 2 ≤ q - m - 1 / 2 ∧
        q - m - 1 / 2 < (1 : ℝ) / 2 := by
    have hmgt : q - 1 < m := by
      dsimp [m]
      rw [lt_min_iff, lt_min_iff]
      constructor
      · rw [sub_lt_iff_lt_add]
        calc
          q < 1 + q0 := sub_lt_iff_lt_add.mp (abs_lt.mp hq0).2
          _ = q0 + 1 := add_comm _ _
      constructor
      · rw [sub_lt_iff_lt_add]
        calc
          q < 1 + q1 := sub_lt_iff_lt_add.mp (abs_lt.mp hq1).2
          _ = q1 + 1 := add_comm _ _
      · rw [sub_lt_iff_lt_add]
        calc
          q < 1 + q2 := sub_lt_iff_lt_add.mp (abs_lt.mp hq2).2
          _ = q2 + 1 := add_comm _ _
    have hqm : q - m < 1 := by
      rw [sub_lt_iff_lt_add]
      have := (sub_lt_iff_lt_add.mp hmgt)
      simpa [add_comm] using this
    have hhalf : (1 : ℝ) / 2 + 1 / 2 = 1 := by
      rw [← add_div]
      norm_num
    have hsub : (1 : ℝ) - 1 / 2 = 1 / 2 := (sub_eq_iff_eq_add).2 hhalf.symm
    constructor
    · calc
        -(1 : ℝ) / 2 = 0 - 1 / 2 := by rw [zero_sub, neg_div]
        _ ≤ (q - m) - 1 / 2 := sub_le_sub_right (sub_nonneg.mpr hmle) _
    · calc
        q - m - 1 / 2 < 1 - 1 / 2 := sub_lt_sub_right hqm _
        _ = 1 / 2 := hsub
  have hm0 : m ≤ q0 := by
    dsimp [m]
    exact min_le_left _ _
  have hm1 : m ≤ q1 := by
    dsimp [m]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hm2 : m ≤ q2 := by
    dsimp [m]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hq0b := hq q0 hm0 (by simp) hq01 hq02
  have hq1b := hq q1 hm1 (by simpa [abs_sub_comm] using hq01) (by simp) hq12
  have hq2b := hq q2 hm2 (by simpa [abs_sub_comm] using hq02)
    (by simpa [abs_sub_comm] using hq12) (by simp)
  let a : ℝ := q0 - m - 1 / 2
  let b : ℝ := q1 - m - 1 / 2
  let c : ℝ := q2 - m - 1 / 2
  let nextEdge : Fin 3 → Fin 3 → ℝ := fun i j =>
    if i = 0 ∧ j = 1 then a else if i = 1 ∧ j = 0 then -a else
    if i = 1 ∧ j = 2 then b else if i = 2 ∧ j = 1 then -b else
    if i = 2 ∧ j = 0 then c else if i = 0 ∧ j = 2 then -c else 0
  refine ⟨nextEdge, ?_, ?_⟩
  have hi (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have haAbs : |a| ≤ (2 : ℝ)⁻¹ := by
    rw [← one_div]
    rw [abs_le]
    simpa only [a, neg_div] using And.intro hq0b.1 (le_of_lt hq0b.2)
  have hbAbs : |b| ≤ (2 : ℝ)⁻¹ := by
    rw [← one_div]
    rw [abs_le]
    simpa only [b, neg_div] using And.intro hq1b.1 (le_of_lt hq1b.2)
  have hcAbs : |c| ≤ (2 : ℝ)⁻¹ := by
    rw [← one_div]
    rw [abs_le]
    simpa only [c, neg_div] using And.intro hq2b.1 (le_of_lt hq2b.2)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      obtain rfl | rfl | rfl := hi i <;> simp [nextEdge]
    · intro i j
      obtain rfl | rfl | rfl := hi i <;>
        obtain rfl | rfl | rfl := hi j <;> simp [nextEdge]
    · intro i j
      obtain rfl | rfl | rfl := hi i <;>
        obtain rfl | rfl | rfl := hi j <;>
          simp [nextEdge, haAbs, hbAbs, hcAbs]
    · intro i
      have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      have ht2eq : t 2 = -(t 0 + t 1) :=
        (eq_neg_iff_add_eq_zero).2
          (by simpa [add_assoc, add_left_comm, add_comm] using hsum)
      obtain rfl | rfl | rfl := hi i <;> rw [huniv] <;>
        simp [nextEdge, a, b, c, q0, q1, q2, sub_eq_add_neg, hsum, ht2eq,
          add_assoc, add_left_comm, add_comm]
  · refine ⟨?_, ?_, ?_⟩
    · simpa [nextEdge, a, neg_div] using hq0b
    · simpa [nextEdge, b, neg_div] using hq1b
    · simpa [nextEdge, c, neg_div] using hq2b

@[blueprint "lem:cyclic-three-strict-rounding-allocation"
  (statement := /-- Let a three-party surplus vector have a bounded skew-edge representation
  satisfying the cyclic half-open convention, and let $v$ be an admissible election.  There is
  an admissible allocation $X$ for which every coordinate of $s+\mathbf{1}_X-v$ has absolute
  value strictly less than one. -/)
  (proof := /-- By \cref{lem:cyclic-three-strict-bound}, every initial surplus lies strictly
  between $-1$ and $1$.  Write $d_i=s_i-v_i$.  The election sum implies
  $d_0+d_1+d_2=-H$, where the house size $H$ is either one or two.  Declare a party mandatory
  when $d_i\leq-1$ and eligible when it has positive vote and $d_i<0$.  The strict initial
  bounds show that every mandatory party is eligible.  If $H=1$, two mandatory parties would,
  together with $d_k<1$ for the remaining party, force the sum below $-1$; moreover at least one
  eligible party exists, since every positive-vote party having $d_i\geq0$ would contradict the
  zero sum of the initial surpluses.  If $H=2$, all three votes are positive; three mandatory
  parties would force the sum below $-2$, while fewer than two eligible parties would force the
  sum above $-2$.  Thus the mandatory set has cardinality at most $H$ and the eligible set has
  cardinality at least $H$.  Choose an intermediate set $X$ of cardinality $H$.  Membership in
  the eligible set gives $-1<d_i+1<1$ for allocated parties, and exclusion from the mandatory
  set gives $-1<d_i<1$ for unallocated parties. -/)
  (title := /-- Strictly bounded allocation in dimension three -/)
  (latexEnv := "lemma")]
lemma cyclic_three_strict_rounding_allocation (s : Fin 3 → ℝ)
    (edge : Fin 3 → Fin 3 → ℝ) (hInvariant : skew_edge_invariant s edge)
    (hCyclic : cyclic_half_open_three edge) (election : apportionment_election 3) :
    ∃ allocation : seat_allocation 3,
      admissible_allocation election allocation ∧
        ∀ i, |s i + allocation_rounding_error election allocation i| < 1 := by
  classical
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  have hs := cyclic_three_strict_bound s edge hInvariant hCyclic
  have hs0 := abs_lt.mp (hs 0)
  have hs1 := abs_lt.mp (hs 1)
  have hs2 := abs_lt.mp (hs 2)
  have hv0 := election.votes_mem_unit 0
  have hv1 := election.votes_mem_unit 1
  have hv2 := election.votes_mem_unit 2
  have hsumS : s 0 + s 1 + s 2 = 0 := by
    rw [hInvariant.2.2.2 0, hInvariant.2.2.2 1, hInvariant.2.2.2 2,
      huniv]
    simp [hInvariant.1, hInvariant.2.1 1 0, hInvariant.2.1 2 0,
      hInvariant.2.1 2 1, add_assoc, add_left_comm, add_comm]
  have hsumV : election.votes 0 + election.votes 1 + election.votes 2 =
      (election.seats : ℝ) := by
    rw [← election.sum_votes, huniv]
    simp [add_assoc, add_left_comm, add_comm]
  let d : Fin 3 → ℝ := fun i => s i - election.votes i
  have hd0lo : -2 < d 0 := by
    have h := add_lt_add hs0.1 (neg_lt_neg hv0.2)
    calc
      (-2 : ℝ) = -1 + -1 := by rw [← neg_add, one_add_one_eq_two]
      _ < s 0 + -election.votes 0 := h
      _ = d 0 := by simp [d, sub_eq_add_neg]
  have hd1lo : -2 < d 1 := by
    have h := add_lt_add hs1.1 (neg_lt_neg hv1.2)
    calc
      (-2 : ℝ) = -1 + -1 := by rw [← neg_add, one_add_one_eq_two]
      _ < s 1 + -election.votes 1 := h
      _ = d 1 := by simp [d, sub_eq_add_neg]
  have hd2lo : -2 < d 2 := by
    have h := add_lt_add hs2.1 (neg_lt_neg hv2.2)
    calc
      (-2 : ℝ) = -1 + -1 := by rw [← neg_add, one_add_one_eq_two]
      _ < s 2 + -election.votes 2 := h
      _ = d 2 := by simp [d, sub_eq_add_neg]
  have hd0hi : d 0 < 1 := (sub_le_self _ hv0.1).trans_lt hs0.2
  have hd1hi : d 1 < 1 := (sub_le_self _ hv1.1).trans_lt hs1.2
  have hd2hi : d 2 < 1 := (sub_le_self _ hv2.1).trans_lt hs2.2
  have hsumD : d 0 + d 1 + d 2 = -(election.seats : ℝ) := by
    calc
      d 0 + d 1 + d 2 = (s 0 + s 1 + s 2) -
          (election.votes 0 + election.votes 1 + election.votes 2) := by
            simp [d, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = 0 - (election.seats : ℝ) := by rw [hsumS, hsumV]
      _ = -(election.seats : ℝ) := zero_sub _
  have hseatCast : (election.seats : ℝ) < 3 := by
    rw [← hsumV]
    have h := add_lt_add (add_lt_add hv0.2 hv1.2) hv2.2
    calc
      election.votes 0 + election.votes 1 + election.votes 2 < 1 + 1 + 1 := h
      _ = 3 := by rw [one_add_one_eq_two, two_add_one_eq_three]
  have hseatLt : election.seats < 3 := by
    by_contra h
    have hc : (3 : ℝ) ≤ (election.seats : ℝ) := Nat.cast_le.mpr (Nat.le_of_not_gt h)
    exact (not_le_of_gt hseatCast) hc
  have hseat : election.seats = 1 ∨ election.seats = 2 := by
    have hpos := election.seats_pos
    omega
  let mandatory : Finset (Fin 3) := Finset.univ.filter fun i => d i ≤ -1
  let eligible : Finset (Fin 3) :=
    Finset.univ.filter fun i => 0 < election.votes i ∧ d i < 0
  have hmandatoryEligible : mandatory ⊆ eligible := by
    intro i hi
    simp only [mandatory, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
    have hsi := (abs_lt.mp (hs i)).1
    have hsv : s i + 1 ≤ election.votes i := by
      have h₁ := add_le_add_right hi (election.votes i)
      have h₂ := add_le_add_right h₁ 1
      simpa [d, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h₂
    have hspos : 0 < s i + 1 := by
      calc
        0 = 1 + -1 := (add_neg_cancel 1).symm
        _ < 1 + s i := add_lt_add_right hsi 1
        _ = s i + 1 := add_comm _ _
    have hsiv : s i < election.votes i :=
      (lt_add_of_pos_right (s i) zero_lt_one).trans_le hsv
    exact ⟨(by
      exact hspos.trans_le hsv), (sub_neg.mpr hsiv)⟩
  rcases hseat with hH | hH
  · have hM01 : ¬(d 0 ≤ -1 ∧ d 1 ≤ -1) := by
      rintro ⟨h0, h1⟩
      have hlt : d 0 + d 1 + d 2 < -1 + -1 + 1 :=
        add_lt_add_of_le_of_lt (add_le_add h0 h1) hd2hi
      rw [hsumD, hH] at hlt
      norm_num at hlt
    have hM02 : ¬(d 0 ≤ -1 ∧ d 2 ≤ -1) := by
      rintro ⟨h0, h2⟩
      have hlt : d 0 + d 2 + d 1 < -1 + -1 + 1 :=
        add_lt_add_of_le_of_lt (add_le_add h0 h2) hd1hi
      have hreorder : d 0 + d 2 + d 1 = d 0 + d 1 + d 2 := by
        simp [add_assoc, add_left_comm, add_comm]
      rw [hreorder, hsumD, hH] at hlt
      norm_num at hlt
    have hM12 : ¬(d 1 ≤ -1 ∧ d 2 ≤ -1) := by
      rintro ⟨h1, h2⟩
      have hlt : d 1 + d 2 + d 0 < -1 + -1 + 1 :=
        add_lt_add_of_le_of_lt (add_le_add h1 h2) hd0hi
      have hreorder : d 1 + d 2 + d 0 = d 0 + d 1 + d 2 := by
        simp [add_assoc, add_left_comm, add_comm]
      rw [hreorder, hsumD, hH] at hlt
      norm_num at hlt
    have hMcard : mandatory.card ≤ election.seats := by
      rw [hH]
      rw [Finset.card_le_one]
      intro i hi j hj
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      have hcases (k : Fin 3) : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      obtain rfl | rfl | rfl := hcases i <;>
        obtain rfl | rfl | rfl := hcases j <;> simp_all
    have hAcard : election.seats ≤ eligible.card := by
      rw [hH]
      by_cases he0 : 0 < election.votes 0 ∧ d 0 < 0
      · apply Finset.card_pos.mpr
        exact ⟨0, by simp [eligible, he0]⟩
      by_cases he1 : 0 < election.votes 1 ∧ d 1 < 0
      · apply Finset.card_pos.mpr
        exact ⟨1, by simp [eligible, he1]⟩
      by_cases he2 : 0 < election.votes 2 ∧ d 2 < 0
      · apply Finset.card_pos.mpr
        exact ⟨2, by simp [eligible, he2]⟩
      exfalso
      by_cases hp0 : 0 < election.votes 0
      · have hd0 : 0 ≤ d 0 := not_lt.mp (fun h => he0 ⟨hp0, h⟩)
        by_cases hp1 : 0 < election.votes 1
        · have hd1 : 0 ≤ d 1 := not_lt.mp (fun h => he1 ⟨hp1, h⟩)
          by_cases hp2 : 0 < election.votes 2
          · have hd2 : 0 ≤ d 2 := not_lt.mp (fun h => he2 ⟨hp2, h⟩)
            have hnonneg : 0 ≤ d 0 + d 1 + d 2 := add_nonneg (add_nonneg hd0 hd1) hd2
            rw [hsumD, hH] at hnonneg
            norm_num at hnonneg
          · have hv2z : election.votes 2 = 0 :=
              le_antisymm (not_lt.mp hp2) hv2.1
            have hd2 : -1 < d 2 := by simpa [d, hv2z] using hs2.1
            have hlt : -1 < d 0 + d 1 + d 2 :=
              hd2.trans_le (by
                have := add_nonneg hd0 hd1
                simpa [add_assoc, add_left_comm, add_comm] using
                  add_le_add_left this (d 2))
            rw [hsumD, hH] at hlt
            norm_num at hlt
        · have hv1z : election.votes 1 = 0 :=
            le_antisymm (not_lt.mp hp1) hv1.1
          by_cases hp2 : 0 < election.votes 2
          · have hd2 : 0 ≤ d 2 := not_lt.mp (fun h => he2 ⟨hp2, h⟩)
            have hd1 : -1 < d 1 := by simpa [d, hv1z] using hs1.1
            have hlt : -1 < d 0 + d 1 + d 2 :=
              hd1.trans_le (by
                have := add_nonneg hd0 hd2
                simpa [add_assoc, add_left_comm, add_comm] using
                  add_le_add_left this (d 1))
            rw [hsumD, hH] at hlt
            norm_num at hlt
          · have hv2z : election.votes 2 = 0 :=
              le_antisymm (not_lt.mp hp2) hv2.1
            have hv0one : election.votes 0 = 1 := by
              simpa [hv1z, hv2z, hH] using hsumV
            exact (ne_of_lt hv0.2) hv0one
      · have hv0z : election.votes 0 = 0 :=
          le_antisymm (not_lt.mp hp0) hv0.1
        by_cases hp1 : 0 < election.votes 1
        · have hd1 : 0 ≤ d 1 := not_lt.mp (fun h => he1 ⟨hp1, h⟩)
          by_cases hp2 : 0 < election.votes 2
          · have hd2 : 0 ≤ d 2 := not_lt.mp (fun h => he2 ⟨hp2, h⟩)
            have hd0 : -1 < d 0 := by simpa [d, hv0z] using hs0.1
            have hlt : -1 < d 0 + d 1 + d 2 :=
              hd0.trans_le (by
                calc
                  d 0 ≤ d 0 + (d 1 + d 2) := by
                    simpa using add_le_add_left (add_nonneg hd1 hd2) (d 0)
                  _ = d 0 + d 1 + d 2 := by rw [add_assoc])
            rw [hsumD, hH] at hlt
            norm_num at hlt
          · have hv2z : election.votes 2 = 0 :=
              le_antisymm (not_lt.mp hp2) hv2.1
            have hv1one : election.votes 1 = 1 := by
              simpa [hv0z, hv2z, hH] using hsumV
            exact (ne_of_lt hv1.2) hv1one
        · have hv1z : election.votes 1 = 0 :=
            le_antisymm (not_lt.mp hp1) hv1.1
          have hv2one : election.votes 2 = 1 := by
            simpa [hv0z, hv1z, hH] using hsumV
          exact (ne_of_lt hv2.2) hv2one
    obtain ⟨allocation, hMsub, hsubA, hcard⟩ :=
      Finset.exists_subsuperset_card_eq hmandatoryEligible hMcard hAcard
    refine ⟨allocation, ?_, ?_⟩
    · refine ⟨hcard, ?_⟩
      intro i hi
      exact (Finset.mem_filter.mp (hsubA hi)).2.1
    · intro i
      rw [abs_lt]
      by_cases hi : i ∈ allocation
      · have hei := (Finset.mem_filter.mp (hsubA hi)).2
        simp only [allocation_rounding_error, if_pos hi]
        constructor
        · have hdlo : -2 < d i := by
            have hsi := (abs_lt.mp (hs i)).1
            have hvi := (election.votes_mem_unit i).2
            calc
              (-2 : ℝ) = -1 + -1 := by rw [← neg_add, one_add_one_eq_two]
              _ < s i + -election.votes i := add_lt_add hsi (neg_lt_neg hvi)
              _ = d i := by simp [d, sub_eq_add_neg]
          calc
            (-1 : ℝ) = 1 + -2 := by
              rw [← one_add_one_eq_two, neg_add]
              simp [add_assoc]
            _ < 1 + d i := add_lt_add_right hdlo 1
            _ = s i + (1 - election.votes i) := by
              simp [d, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        · calc
            s i + (1 - election.votes i) = 1 + d i := by
              simp [d, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
            _ < 1 + 0 := add_lt_add_right hei.2 1
            _ = 1 := add_zero 1
      · have hnotM : i ∉ mandatory := fun him => hi (hMsub him)
        have hdlo : -1 < d i := lt_of_not_ge
          (fun h => hnotM (by simp [mandatory, h]))
        have hdhi : d i < 1 :=
          (sub_le_self _ (election.votes_mem_unit i).1).trans_lt (abs_lt.mp (hs i)).2
        simpa only [allocation_rounding_error, if_neg hi, zero_sub,
          zero_add, sub_eq_add_neg, d] using And.intro hdlo hdhi
  · have hv0p : 0 < election.votes 0 := by
      by_contra h
      have hv0z : election.votes 0 = 0 := le_antisymm (not_lt.mp h) hv0.1
      have hlt : election.votes 1 + election.votes 2 < 1 + 1 := add_lt_add hv1.2 hv2.2
      have heq : election.votes 1 + election.votes 2 = 2 := by
        simpa [hv0z, hH] using hsumV
      rw [heq] at hlt
      rw [one_add_one_eq_two] at hlt
      exact (lt_irrefl 2) hlt
    have hv1p : 0 < election.votes 1 := by
      by_contra h
      have hv1z : election.votes 1 = 0 := le_antisymm (not_lt.mp h) hv1.1
      have hlt : election.votes 0 + election.votes 2 < 1 + 1 := add_lt_add hv0.2 hv2.2
      have heq : election.votes 0 + election.votes 2 = 2 := by
        simpa [hv1z, hH, add_assoc, add_left_comm, add_comm] using hsumV
      rw [heq] at hlt
      rw [one_add_one_eq_two] at hlt
      exact (lt_irrefl 2) hlt
    have hv2p : 0 < election.votes 2 := by
      by_contra h
      have hv2z : election.votes 2 = 0 := le_antisymm (not_lt.mp h) hv2.1
      have hlt : election.votes 0 + election.votes 1 < 1 + 1 := add_lt_add hv0.2 hv1.2
      have heq : election.votes 0 + election.votes 1 = 2 := by
        simpa [hv2z, hH] using hsumV
      rw [heq] at hlt
      rw [one_add_one_eq_two] at hlt
      exact (lt_irrefl 2) hlt
    have hM012 : ¬(d 0 ≤ -1 ∧ d 1 ≤ -1 ∧ d 2 ≤ -1) := by
      rintro ⟨h0, h1, h2⟩
      have hle : d 0 + d 1 + d 2 ≤ -1 + -1 + -1 :=
        add_le_add (add_le_add h0 h1) h2
      have hneg : (-1 : ℝ) + -1 + -1 < -2 := by
        have h := add_lt_add_left (neg_lt_neg zero_lt_one) (-2 : ℝ)
        simpa [← one_add_one_eq_two, neg_add, add_assoc] using h
      have hle' : (-2 : ℝ) ≤ -1 + -1 + -1 := by
        calc
          (-2 : ℝ) = -(election.seats : ℝ) := by rw [hH]; norm_num
          _ = d 0 + d 1 + d 2 := hsumD.symm
          _ ≤ -1 + -1 + -1 := hle
      exact (not_le_of_gt hneg) hle'
    have hMcard : mandatory.card ≤ election.seats := by
      have hproper : mandatory ⊂ (Finset.univ : Finset (Fin 3)) := by
        refine ⟨Finset.subset_univ _, ?_⟩
        intro heq
        apply hM012
        have hm0 : 0 ∈ mandatory := heq (by simp)
        have hm1 : 1 ∈ mandatory := heq (by simp)
        have hm2 : 2 ∈ mandatory := heq (by simp)
        exact ⟨(Finset.mem_filter.mp hm0).2, (Finset.mem_filter.mp hm1).2,
          (Finset.mem_filter.mp hm2).2⟩
      have hcardlt := Finset.card_lt_card hproper
      rw [Finset.card_univ, Fintype.card_fin] at hcardlt
      omega
    have hD01 : ¬(0 ≤ d 0 ∧ 0 ≤ d 1) := by
      rintro ⟨h0, h1⟩
      have hlt : -2 < d 2 + d 0 + d 1 :=
        hd2lo.trans_le (by
          calc
            d 2 ≤ d 2 + (d 0 + d 1) := by
              simpa using add_le_add_left (add_nonneg h0 h1) (d 2)
            _ = d 2 + d 0 + d 1 := by rw [add_assoc])
      have hreorder : d 2 + d 0 + d 1 = d 0 + d 1 + d 2 := by
        simp [add_assoc, add_left_comm, add_comm]
      rw [hreorder, hsumD, hH] at hlt
      norm_num at hlt
    have hD02 : ¬(0 ≤ d 0 ∧ 0 ≤ d 2) := by
      rintro ⟨h0, h2⟩
      have hlt : -2 < d 1 + d 0 + d 2 :=
        hd1lo.trans_le (by
          calc
            d 1 ≤ d 1 + (d 0 + d 2) := by
              simpa using add_le_add_left (add_nonneg h0 h2) (d 1)
            _ = d 1 + d 0 + d 2 := by rw [add_assoc])
      have hreorder : d 1 + d 0 + d 2 = d 0 + d 1 + d 2 := by
        simp [add_assoc, add_left_comm, add_comm]
      rw [hreorder, hsumD, hH] at hlt
      norm_num at hlt
    have hD12 : ¬(0 ≤ d 1 ∧ 0 ≤ d 2) := by
      rintro ⟨h1, h2⟩
      have hlt : -2 < d 0 + d 1 + d 2 :=
        hd0lo.trans_le (by
          calc
            d 0 ≤ d 0 + (d 1 + d 2) := by
              simpa using add_le_add_left (add_nonneg h1 h2) (d 0)
            _ = d 0 + d 1 + d 2 := by rw [add_assoc])
      rw [hsumD, hH] at hlt
      norm_num at hlt
    have hAcard : election.seats ≤ eligible.card := by
      rw [hH]
      by_cases hd0 : d 0 < 0
      · by_cases hd1 : d 1 < 0
        · calc
            2 = ({0, 1} : Finset (Fin 3)).card := by decide
            _ ≤ eligible.card := Finset.card_le_card (by
              intro i hi
              simp at hi
              rcases hi with rfl | rfl
              · simp [eligible, hv0p, hd0]
              · simp [eligible, hv1p, hd1])
        · have hd1n : 0 ≤ d 1 := not_lt.mp hd1
          have hd2 : d 2 < 0 := by
            by_contra hn
            exact hD12 ⟨hd1n, not_lt.mp hn⟩
          calc
            2 = ({0, 2} : Finset (Fin 3)).card := by decide
            _ ≤ eligible.card := Finset.card_le_card (by
              intro i hi
              simp at hi
              rcases hi with rfl | rfl
              · simp [eligible, hv0p, hd0]
              · simp [eligible, hv2p, hd2])
      · have hd0n : 0 ≤ d 0 := not_lt.mp hd0
        have hd1 : d 1 < 0 := by
          by_contra hn
          exact hD01 ⟨hd0n, not_lt.mp hn⟩
        have hd2 : d 2 < 0 := by
          by_contra hn
          exact hD02 ⟨hd0n, not_lt.mp hn⟩
        calc
          2 = ({1, 2} : Finset (Fin 3)).card := by decide
          _ ≤ eligible.card := Finset.card_le_card (by
            intro i hi
            simp at hi
            rcases hi with rfl | rfl
            · simp [eligible, hv1p, hd1]
            · simp [eligible, hv2p, hd2])
    obtain ⟨allocation, hMsub, hsubA, hcard⟩ :=
      Finset.exists_subsuperset_card_eq hmandatoryEligible hMcard hAcard
    refine ⟨allocation, ?_, ?_⟩
    · refine ⟨hcard, ?_⟩
      intro i hi
      exact (Finset.mem_filter.mp (hsubA hi)).2.1
    · intro i
      rw [abs_lt]
      by_cases hi : i ∈ allocation
      · have hei := (Finset.mem_filter.mp (hsubA hi)).2
        simp only [allocation_rounding_error, if_pos hi]
        constructor
        · have hdlo : -2 < d i := by
            have hsi := (abs_lt.mp (hs i)).1
            have hvi := (election.votes_mem_unit i).2
            calc
              (-2 : ℝ) = -1 + -1 := by rw [← neg_add, one_add_one_eq_two]
              _ < s i + -election.votes i := add_lt_add hsi (neg_lt_neg hvi)
              _ = d i := by simp [d, sub_eq_add_neg]
          calc
            (-1 : ℝ) = 1 + -2 := by
              rw [← one_add_one_eq_two, neg_add]
              simp [add_assoc]
            _ < 1 + d i := add_lt_add_right hdlo 1
            _ = s i + (1 - election.votes i) := by
              simp [d, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        · calc
            s i + (1 - election.votes i) = 1 + d i := by
              simp [d, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
            _ < 1 + 0 := add_lt_add_right hei.2 1
            _ = 1 := add_zero 1
      · have hnotM : i ∉ mandatory := fun him => hi (hMsub him)
        have hdlo : -1 < d i := lt_of_not_ge
          (fun h => hnotM (by simp [mandatory, h]))
        have hdhi : d i < 1 :=
          (sub_le_self _ (election.votes_mem_unit i).1).trans_lt (abs_lt.mp (hs i)).2
        simpa only [allocation_rounding_error, if_neg hi, zero_sub,
          zero_add, sub_eq_add_neg, d] using And.intro hdlo hdhi

@[blueprint "lem:cyclic-three-rounding-step"
  (statement := /-- Let $s\in\mathbb{R}^3$ have a bounded skew-edge representation satisfying
  the cyclic half-open convention, and let $v$ be an admissible three-party election.  There are
  an allocation $X$ and a new edge matrix $e'$ satisfying the greedy one-step specification,
  with $e'$ again satisfying the cyclic half-open convention. -/)
  (proof := /-- By \cref{lem:cyclic-three-strict-rounding-allocation}, choose an admissible
  allocation $X$ such that every coordinate of the updated surplus
  $t=s+\mathbf{1}_X-v$ has absolute value strictly less than one.  The coordinate sum of $s$ is
  zero by \cref{def:skew-edge-invariant}; admissibility of $X$ and the election sum show that the
  coordinate sum of $t$ is also zero.  Apply
  \cref{lem:cyclic-three-strict-representation} to obtain a bounded skew-edge representation of
  $t$ satisfying the cyclic half-open convention.  Together with the original invariant and the
  admissibility of $X$, this is precisely \cref{def:greedy-step-spec}. -/)
  (title := /-- Cyclic one-step rounding in dimension three -/)
  (latexEnv := "lemma")]
lemma cyclic_three_rounding_step (s : Fin 3 → ℝ) (edge : Fin 3 → Fin 3 → ℝ)
    (hInvariant : skew_edge_invariant s edge) (hCyclic : cyclic_half_open_three edge)
    (election : apportionment_election 3) :
    ∃ allocation : seat_allocation 3, ∃ nextEdge : Fin 3 → Fin 3 → ℝ,
      greedy_step_spec s edge election allocation nextEdge ∧ cyclic_half_open_three nextEdge := by
  classical
  obtain ⟨allocation, hAdmissible, hStrict⟩ :=
    cyclic_three_strict_rounding_allocation s edge hInvariant hCyclic election
  let t : Fin 3 → ℝ := fun i =>
    s i + allocation_rounding_error election allocation i
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  have hsumS : s 0 + s 1 + s 2 = 0 := by
    rw [hInvariant.2.2.2 0, hInvariant.2.2.2 1, hInvariant.2.2.2 2,
      huniv]
    simp [hInvariant.1, hInvariant.2.1 1 0, hInvariant.2.1 2 0,
      hInvariant.2.1 2 1, add_assoc, add_left_comm, add_comm]
  have hsumV : election.votes 0 + election.votes 1 + election.votes 2 =
      (election.seats : ℝ) := by
    rw [← election.sum_votes, huniv]
    simp [add_assoc, add_left_comm, add_comm]
  have hcount : (∑ i : Fin 3, if i ∈ allocation then (1 : ℝ) else 0) =
      (allocation.card : ℝ) := by
    calc
      (∑ i : Fin 3, if i ∈ allocation then (1 : ℝ) else 0) =
          ∑ i ∈ allocation, (1 : ℝ) := by
            rw [← Finset.sum_filter]
            simp
      _ = (allocation.card : ℝ) := by simp
  have hcountThree : (if 0 ∈ allocation then (1 : ℝ) else 0) +
      (if 1 ∈ allocation then (1 : ℝ) else 0) +
      (if 2 ∈ allocation then (1 : ℝ) else 0) = (allocation.card : ℝ) := by
    rw [← hcount, huniv]
    simp [add_assoc, add_left_comm, add_comm]
  have hsumT : t 0 + t 1 + t 2 = 0 := by
    calc
      t 0 + t 1 + t 2 = (s 0 + s 1 + s 2) +
          ((if 0 ∈ allocation then (1 : ℝ) else 0) +
            (if 1 ∈ allocation then (1 : ℝ) else 0) +
            (if 2 ∈ allocation then (1 : ℝ) else 0)) -
          (election.votes 0 + election.votes 1 + election.votes 2) := by
            simp [t, allocation_rounding_error, sub_eq_add_neg,
              add_assoc, add_left_comm, add_comm]
      _ = 0 := by rw [hsumS, hcountThree, hAdmissible.1, hsumV]; simp
  have hStrictT : ∀ i, |t i| < 1 := by
    intro i
    exact hStrict i
  obtain ⟨nextEdge, hNextInvariant, hNextCyclic⟩ :=
    cyclic_three_strict_representation t hsumT hStrictT
  refine ⟨allocation, nextEdge, ?_, hNextCyclic⟩
  exact ⟨hInvariant, hAdmissible, hNextInvariant⟩

@[blueprint "lem:greedy-induced-state-cumulative"
  (statement := /-- For every online apportionment method, instance, time $t$, and party $i$,
  the cumulative-vote and cumulative-seat coordinates in the induced state before time $t$
  equal the corresponding explicit sums over the elections with indices less than $t$. -/)
  (proof := /-- Induct on $t$.  At time zero, unfold
  \cref{def:induced-state}; both sums are empty.  For the successor step, unfold
  \cref{def:induced-state,def:allocation-at}, split each range sum into its preceding range and
  final summand, and apply the two induction hypotheses.  The natural-number cast in the seat
  coordinate distributes over the update, so the resulting expressions agree. -/)
  (title := /-- Induced states equal the explicit cumulative sums -/)
  (latexEnv := "lemma")]
lemma greedy_induced_state_cumulative {n : ℕ} (method : online_apportionment_method n)
    (input : apportionment_instance n) (t : ℕ) (i : Fin n) :
    (induced_state method input t).cumulativeVotes i =
        ∑ k ∈ Finset.range t, (input k).votes i ∧
      ((induced_state method input t).cumulativeSeats i : ℝ) =
        ∑ k ∈ Finset.range t, if i ∈ allocation_at method input k then (1 : ℝ) else 0 := by
  induction t with
  | zero =>
      simp [induced_state]
  | succ t ih =>
      simp [induced_state, allocation_at, Finset.sum_range_succ, ih.1, ih.2]

@[blueprint "lem:greedy-online-method-of-step"
  (statement := /-- Fix a dimension $n$ and a predicate $P$ on edge matrices which holds for the
  zero matrix.  Suppose that, from every bounded skew-edge representation satisfying $P$ and
  every admissible election, one can choose an admissible allocation and a new bounded
  skew-edge representation satisfying $P$ for the updated surplus.  Then there is an online
  apportionment method such that, after every election of every instance, its cumulative
  surplus has a bounded skew-edge representation satisfying $P$. -/)
  (proof := /-- For a cumulative state, define its surplus as cumulative seats minus cumulative
  votes.  If that surplus has a bounded skew-edge representation satisfying $P$, use classical
  choice on the assumed step rule; otherwise use the same rule at the zero surplus and zero
  matrix.  The admissibility component of the rule makes these allocations into an online
  method.  Induction on time shows that every state reachable by this method is in the first
  branch: the zero state has the zero representation, and the preservation component of the
  step rule supplies the representation at the successor state.  Finally,
  \cref{lem:greedy-induced-state-cumulative} identifies the surplus of the reachable state after
  time $t$ with the explicit cumulative surplus through time $t$. -/)
  (title := /-- Online realization of an invariant-preserving step rule -/)
  (latexEnv := "lemma")]
lemma greedy_online_method_of_step {n : ℕ}
    (edgeProperty : (Fin n → Fin n → ℝ) → Prop)
    (hZeroProperty : edgeProperty (fun _ _ => 0))
    (step : ∀ (s : Fin n → ℝ) (edge : Fin n → Fin n → ℝ),
      skew_edge_invariant s edge → edgeProperty edge →
      ∀ election : apportionment_election n,
        ∃ allocation : seat_allocation n, ∃ nextEdge : Fin n → Fin n → ℝ,
          greedy_step_spec s edge election allocation nextEdge ∧ edgeProperty nextEdge) :
    ∃ method : online_apportionment_method n,
      ∀ input : apportionment_instance n, ∀ t : ℕ,
        ∃ edge : Fin n → Fin n → ℝ,
          skew_edge_invariant (apportionment_surplus method input t) edge ∧
            edgeProperty edge := by
  classical
  let zeroSurplus : Fin n → ℝ := fun _ => 0
  let zeroEdge : Fin n → Fin n → ℝ := fun _ _ => 0
  have hZeroInvariant : skew_edge_invariant zeroSurplus zeroEdge := by
    simp [skew_edge_invariant, zeroSurplus, zeroEdge]
  let stateSurplus : apportionment_state n → Fin n → ℝ := fun state i =>
    (state.cumulativeSeats i : ℝ) - state.cumulativeVotes i
  have hStepPair (s : Fin n → ℝ) (edge : Fin n → Fin n → ℝ)
      (hInvariant : skew_edge_invariant s edge) (hProperty : edgeProperty edge)
      (election : apportionment_election n) :
      ∃ result : seat_allocation n × (Fin n → Fin n → ℝ),
        greedy_step_spec s edge election result.1 result.2 ∧ edgeProperty result.2 := by
    rcases step s edge hInvariant hProperty election with
      ⟨allocation, nextEdge, hSpec, hNextProperty⟩
    exact ⟨(allocation, nextEdge), hSpec, hNextProperty⟩
  let decision : apportionment_state n → apportionment_election n →
      seat_allocation n × (Fin n → Fin n → ℝ) := fun state election =>
    if h : ∃ edge, skew_edge_invariant (stateSurplus state) edge ∧ edgeProperty edge then
      Classical.choose
        (hStepPair (stateSurplus state) (Classical.choose h)
          (Classical.choose_spec h).1 (Classical.choose_spec h).2 election)
    else
      Classical.choose (hStepPair zeroSurplus zeroEdge hZeroInvariant hZeroProperty election)
  have hDecisionAdmissible (state : apportionment_state n)
      (election : apportionment_election n) :
      admissible_allocation election (decision state election).1 := by
    by_cases h : ∃ edge,
        skew_edge_invariant (stateSurplus state) edge ∧ edgeProperty edge
    · simp only [decision, dif_pos h]
      exact (Classical.choose_spec
        (hStepPair (stateSurplus state) (Classical.choose h)
          (Classical.choose_spec h).1 (Classical.choose_spec h).2 election)).1.2.1
    · simp only [decision, dif_neg h]
      exact (Classical.choose_spec
        (hStepPair zeroSurplus zeroEdge hZeroInvariant hZeroProperty election)).1.2.1
  have hDecisionPreserves (state : apportionment_state n)
      (election : apportionment_election n)
      (h : ∃ edge, skew_edge_invariant (stateSurplus state) edge ∧ edgeProperty edge) :
      skew_edge_invariant
          (fun i => stateSurplus state i +
            allocation_rounding_error election (decision state election).1 i)
          (decision state election).2 ∧ edgeProperty (decision state election).2 := by
    dsimp [decision]
    rw [dif_pos h]
    exact ⟨(Classical.choose_spec
        (hStepPair (stateSurplus state) (Classical.choose h)
          (Classical.choose_spec h).1 (Classical.choose_spec h).2 election)).1.2.2,
      (Classical.choose_spec
        (hStepPair (stateSurplus state) (Classical.choose h)
          (Classical.choose_spec h).1 (Classical.choose_spec h).2 election)).2⟩
  let method : online_apportionment_method n :=
    { choose := fun _ state election => (decision state election).1
      card_choose := by
        intro t state election
        exact (hDecisionAdmissible state election).1
      choose_positive := by
        intro t state election i hi
        exact (hDecisionAdmissible state election).2 i hi }
  have hReachable (input : apportionment_instance n) :
      ∀ t : ℕ, ∃ edge : Fin n → Fin n → ℝ,
        skew_edge_invariant (stateSurplus (induced_state method input t)) edge ∧
          edgeProperty edge := by
    intro t
    induction t with
    | zero =>
        exact ⟨zeroEdge, by simpa [induced_state, stateSurplus, zeroSurplus] using hZeroInvariant,
          hZeroProperty⟩
    | succ t ih =>
        rcases ih with ⟨edge, hInvariant, hProperty⟩
        have hGood : ∃ edge,
            skew_edge_invariant (stateSurplus (induced_state method input t)) edge ∧
              edgeProperty edge := ⟨edge, hInvariant, hProperty⟩
        have hNext := hDecisionPreserves (induced_state method input t) (input t) hGood
        have hSurplusUpdate :
            stateSurplus (induced_state method input (t + 1)) =
              fun i => stateSurplus (induced_state method input t) i +
                allocation_rounding_error (input t)
                  (decision (induced_state method input t) (input t)).1 i := by
          funext i
          by_cases hi : i ∈ (decision (induced_state method input t) (input t)).1
          · simp [induced_state, stateSurplus, method, allocation_rounding_error, hi]
            simp only [sub_eq_add_neg, neg_add_rev]
            ac_rfl
          · simp [induced_state, stateSurplus, method, allocation_rounding_error, hi]
            simp only [sub_eq_add_neg, neg_add_rev]
            ac_rfl
        refine ⟨(decision (induced_state method input t) (input t)).2, ?_, hNext.2⟩
        rw [hSurplusUpdate]
        exact hNext.1
  refine ⟨method, ?_⟩
  intro input t
  rcases hReachable input (t + 1) with ⟨edge, hInvariant, hProperty⟩
  refine ⟨edge, ?_, hProperty⟩
  have hState := greedy_induced_state_cumulative method input (t + 1)
  have hSurplus : apportionment_surplus method input t =
      stateSurplus (induced_state method input (t + 1)) := by
    funext i
    have hi := hState i
    simp [apportionment_surplus, cumulative_votes, cumulative_seats, stateSurplus,
      hi.1, hi.2]
  rw [hSurplus]
  exact hInvariant

@[blueprint "lem:greedy-upper-guarantee"
  (statement := /-- Let $n$ be a positive integer.  There exists a dimension-parametric online
  apportionment method $M$ such that $M_n$ is $(n-1)/2$-proportional on every $n$-dimensional
  instance and $M_3$ is strictly $1$-proportional on every three-dimensional instance. -/)
  (proof := /-- Apply \cref{lem:greedy-online-method-of-step} with the trivial edge predicate and
  the transition supplied by \cref{lem:bounded-skew-rounding-step}.  The resulting method
  maintains a bounded skew-edge representation of its cumulative surplus on every instance, so
  \cref{lem:skew-edge-invariant-bound} gives the uniform $(n-1)/2$ estimate.  Apply the same
  realization lemma in dimension three with the cyclic half-open predicate.  The zero matrix
  satisfies that predicate, and \cref{lem:cyclic-three-rounding-step} preserves it; hence
  \cref{lem:cyclic-three-strict-bound} gives strict discrepancy below $1$.  Choose arbitrary
  online methods in unused dimensions, use the cyclic method in dimension three, and use the
  bounded method in dimension $n$ when $n\ne3$.  If $n=3$, apply
  \cref{lem:skew-edge-invariant-bound} directly to the cyclic method's maintained invariant to
  obtain the required weak bound.  These components form the asserted dimension-parametric
  family. -/)
  (title := /-- Greedy-method upper guarantees -/)
  (latexEnv := "lemma")]
lemma greedy_upper_guarantee (n : ℕ) (hn : 0 < n) :
    ∃ method : online_apportionment_method_family,
      (∀ input : apportionment_instance n,
        proportional (method n) input (((n : ℝ) - 1) / 2)) ∧
      (∀ input : apportionment_instance 3,
        strictly_proportional (method 3) input 1) := by
  classical
  have hBoundedStep (m : ℕ) (hm : 0 < m) :
      ∀ (s : Fin m → ℝ) (edge : Fin m → Fin m → ℝ),
        skew_edge_invariant s edge → (fun _ : Fin m → Fin m → ℝ => True) edge →
        ∀ election : apportionment_election m,
          ∃ allocation : seat_allocation m, ∃ nextEdge : Fin m → Fin m → ℝ,
            greedy_step_spec s edge election allocation nextEdge ∧
              (fun _ : Fin m → Fin m → ℝ => True) nextEdge := by
    intro s edge hInvariant hProperty election
    rcases bounded_skew_rounding_step hm s edge hInvariant election with
      ⟨allocation, nextEdge, hSpec⟩
    exact ⟨allocation, nextEdge, hSpec, trivial⟩
  obtain ⟨boundedMethod, hBoundedInvariant⟩ :=
    greedy_online_method_of_step (n := n) (fun _ => True) trivial (hBoundedStep n hn)
  have hBoundedGuarantee : ∀ input : apportionment_instance n,
      proportional boundedMethod input (((n : ℝ) - 1) / 2) := by
    intro input t i
    rcases hBoundedInvariant input t with ⟨edge, hInvariant, hProperty⟩
    exact skew_edge_invariant_bound hn (apportionment_surplus boundedMethod input t)
      edge hInvariant i
  have hCyclicZero : cyclic_half_open_three (fun _ _ => 0) := by
    norm_num [cyclic_half_open_three, div_eq_mul_inv]
  obtain ⟨cyclicMethod, hCyclicInvariant⟩ :=
    greedy_online_method_of_step (n := 3) cyclic_half_open_three hCyclicZero
      (fun s edge hInvariant hCyclic election =>
        cyclic_three_rounding_step s edge hInvariant hCyclic election)
  have hCyclicGuarantee : ∀ input : apportionment_instance 3,
      strictly_proportional cyclicMethod input 1 := by
    intro input t i
    rcases hCyclicInvariant input t with ⟨edge, hInvariant, hCyclic⟩
    exact cyclic_three_strict_bound (apportionment_surplus cyclicMethod input t)
      edge hInvariant hCyclic i
  have hAnyMethod (m : ℕ) : Nonempty (online_apportionment_method m) := by
    by_cases hm : 0 < m
    · rcases greedy_online_method_of_step (n := m) (fun _ => True) trivial
          (hBoundedStep m hm) with ⟨method, hInvariant⟩
      exact ⟨method⟩
    · have hmZero : m = 0 := Nat.eq_zero_of_not_pos hm
      subst m
      have hNoElection (election : apportionment_election 0) : False := by
        have hSeats : (election.seats : ℝ) = 0 := by
          simpa using election.sum_votes.symm
        have hSeatsPositive : (0 : ℝ) < election.seats :=
          Nat.cast_pos.mpr election.seats_pos
        exact (ne_of_gt hSeatsPositive) hSeats
      exact ⟨{
        choose := fun _ _ election => (hNoElection election).elim
        card_choose := by
          intro t state election
          exact (hNoElection election).elim
        choose_positive := by
          intro t state election i hi
          exact (hNoElection election).elim }⟩
  let family : online_apportionment_method_family := fun m =>
    if hThree : m = 3 then
      cast (by rw [hThree]) cyclicMethod
    else if hN : m = n then
      cast (by rw [hN]) boundedMethod
    else
      Classical.choice (hAnyMethod m)
  refine ⟨family, ?_, ?_⟩
  · intro input t i
    by_cases hnThree : n = 3
    · subst n
      rw [show family 3 = cyclicMethod by simp [family]]
      rcases hCyclicInvariant input t with ⟨edge, hInvariant, hCyclic⟩
      exact skew_edge_invariant_bound hn (apportionment_surplus cyclicMethod input t)
        edge hInvariant i
    · simpa [family, hnThree] using hBoundedGuarantee input t i
  · intro input t i
    simpa [family] using hCyclicGuarantee input t i

@[blueprint "lem:adversarial-lower-bound"
  (statement := /-- Let $n\geq2$ be an integer and let $\varepsilon>0$.  Every deterministic
  online apportionment method on $n$ parties fails to be $((n-1)/2-\varepsilon)$-proportional on
  some $n$-dimensional instance. -/)
  (proof := /-- Fix $n\geq2$, $\varepsilon>0$ and a method $M$, and put
  $\alpha=(n-1)/2-\varepsilon$ and $\delta=\min\{\varepsilon/(n-1),1/2\}$, so that
  $0<\delta\leq1/2$ and $(n-1)\delta\leq\varepsilon$.  Against a cumulative state with surplus
  vector $s$, the adversary selects a pair of parties $a\neq b$ with $0\leq s_a-s_b\leq1-\delta$
  whenever one exists, and answers with the one-seat election whose votes are $1-\delta/2$ at
  $a$, $\delta/2$ at $b$, and zero elsewhere; recursion on time assembles these answers into a
  single instance whose induced states are exactly the states used by the adversary.  Suppose $M$
  were $\alpha$-proportional on that instance.  Then $2\alpha=(n-1)-2\varepsilon<(n-1)(1-\delta)$,
  so the $n$ numbers $(s_i+\alpha)/(1-\delta)$ lie in $[0,n-1)$ and two of them have the same
  integer part, which produces the required pair.  Since $M$ must award the single seat to $a$ or
  to $b$, the potential $\Phi=\sum_i s_i^2$ grows by $\delta(s_a-s_b)+\delta^2/2$ in the first
  case and by $2u^2-2u(s_a-s_b)$ with $u=1-\delta/2$ in the second, and both quantities are at
  least $\delta^2/2$.  Hence $\Phi\geq t\delta^2/2$ after $t$ elections, whereas proportionality
  forces $\Phi\leq n\alpha^2$; choosing $t$ large enough is a contradiction. -/)
  (title := /-- Adversarial proportionality lower bound -/)
  (latexEnv := "lemma")]
lemma adversarial_lower_bound (n : ℕ) (hn : 1 < n) (ε : ℝ) (hε : 0 < ε) :
    ∀ method : online_apportionment_method n,
      ∃ input : apportionment_instance n,
        ¬ proportional method input (((n : ℝ) - 1) / 2 - ε) := by
  classical
  intro method
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  obtain ⟨δ, hδpos, hδhalf, hδgap⟩ :
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ((n : ℝ) - 1) * δ ≤ ε := by
    have hinv : (0 : ℝ) < ((n : ℝ) - 1)⁻¹ := inv_pos.mpr hN
    have hcancel : ((n : ℝ) - 1) * (ε * ((n : ℝ) - 1)⁻¹) = ε := by
      have h1 : ((n : ℝ) - 1) * ((n : ℝ) - 1)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hN)
      calc ((n : ℝ) - 1) * (ε * ((n : ℝ) - 1)⁻¹)
          = (((n : ℝ) - 1) * ((n : ℝ) - 1)⁻¹) * ε := by ring
        _ = 1 * ε := by rw [h1]
        _ = ε := one_mul ε
    refine ⟨min (ε * ((n : ℝ) - 1)⁻¹) (1 / 2), lt_min (mul_pos hε hinv) (by norm_num),
      min_le_right _ _, ?_⟩
    have h2 : ((n : ℝ) - 1) * min (ε * ((n : ℝ) - 1)⁻¹) (1 / 2)
        ≤ ((n : ℝ) - 1) * (ε * ((n : ℝ) - 1)⁻¹) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (le_of_lt hN)
    linarith
  have hpigGen : ∀ (A c : ℝ) (σ : Fin n → ℝ), 0 < c → (∀ i, |σ i| ≤ A) →
      2 * A < ((n : ℝ) - 1) * c →
      ∃ p : Fin n × Fin n, p.1 ≠ p.2 ∧ 0 ≤ σ p.1 - σ p.2 ∧ σ p.1 - σ p.2 ≤ c := by
    intro A c σ hc hσ hAc
    have hcinv : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc
    obtain ⟨x, hx⟩ : ∃ g : Fin n → ℝ, ∀ k, g k = (σ k + A) * c⁻¹ := ⟨_, fun _ => rfl⟩
    obtain ⟨bk, hbk⟩ : ∃ g : Fin n → ℕ, ∀ k, g k = (⌊x k⌋).toNat := ⟨_, fun _ => rfl⟩
    have hxc : ∀ k, x k * c = σ k + A := by
      intro k
      rw [hx k]
      calc (σ k + A) * c⁻¹ * c = (σ k + A) * (c⁻¹ * c) := by ring
        _ = (σ k + A) * 1 := by rw [inv_mul_cancel₀ (ne_of_gt hc)]
        _ = σ k + A := mul_one _
    have hxnonneg : ∀ k, 0 ≤ x k := by
      intro k
      rw [hx k]
      have h1 := (abs_le.mp (hσ k)).1
      exact mul_nonneg (by linarith) (le_of_lt hcinv)
    have hxlt : ∀ k, x k < (n : ℝ) - 1 := by
      intro k
      have h2 : σ k + A < ((n : ℝ) - 1) * c := by
        have h3 := (abs_le.mp (hσ k)).2
        linarith
      have h4 : x k * c < ((n : ℝ) - 1) * c := by rw [hxc k]; exact h2
      have h5 : x k * c * c⁻¹ < ((n : ℝ) - 1) * c * c⁻¹ := mul_lt_mul_of_pos_right h4 hcinv
      have h6 : x k * c * c⁻¹ = x k := by
        calc x k * c * c⁻¹ = x k * (c * c⁻¹) := by ring
          _ = x k * 1 := by rw [mul_inv_cancel₀ (ne_of_gt hc)]
          _ = x k := mul_one _
      have h7 : ((n : ℝ) - 1) * c * c⁻¹ = (n : ℝ) - 1 := by
        calc ((n : ℝ) - 1) * c * c⁻¹ = ((n : ℝ) - 1) * (c * c⁻¹) := by ring
          _ = ((n : ℝ) - 1) * 1 := by rw [mul_inv_cancel₀ (ne_of_gt hc)]
          _ = (n : ℝ) - 1 := mul_one _
      rw [h6, h7] at h5
      exact h5
    have hbucket : ∀ k : Fin n, bk k ∈ Finset.range (n - 1) := by
      intro k
      have h6 : ⌊x k⌋ < ((n - 1 : ℕ) : ℤ) := by
        rw [Int.floor_lt]
        have hcast : (((n - 1 : ℕ) : ℤ) : ℝ) = (n : ℝ) - 1 := by
          have h1 : (1 : ℕ) ≤ n := le_of_lt hn
          push_cast [h1]
          ring
        rw [hcast]
        exact hxlt k
      have h7 : (0 : ℤ) ≤ ⌊x k⌋ := Int.floor_nonneg.mpr (hxnonneg k)
      rw [Finset.mem_range, hbk k]
      omega
    have hcard : (Finset.range (n - 1)).card < (Finset.univ : Finset (Fin n)).card := by
      rw [Finset.card_range, Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨i, -, j, -, hij, hbeq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (fun k _ => hbucket k)
    rw [hbk i, hbk j] at hbeq
    have hfl : ⌊x i⌋ = ⌊x j⌋ := by
      have h1 : (0 : ℤ) ≤ ⌊x i⌋ := Int.floor_nonneg.mpr (hxnonneg i)
      have h2 : (0 : ℤ) ≤ ⌊x j⌋ := Int.floor_nonneg.mpr (hxnonneg j)
      omega
    have hlt1 : x i < x j + 1 := by
      have h1 := Int.lt_floor_add_one (x i)
      have h2 := Int.floor_le (x j)
      rw [hfl] at h1
      linarith
    have hlt2 : x j < x i + 1 := by
      have h1 := Int.lt_floor_add_one (x j)
      have h2 := Int.floor_le (x i)
      rw [← hfl] at h1
      linarith
    have hgap : ∀ k l : Fin n, x k < x l + 1 → σ k - σ l ≤ c := by
      intro k l hkl
      have h1 : (x k - x l) * c < 1 * c := mul_lt_mul_of_pos_right (by linarith) hc
      have h2 : (x k - x l) * c = σ k - σ l := by
        have h3 : (x k - x l) * c = x k * c - x l * c := by ring
        rw [h3, hxc k, hxc l]
        ring
      rw [h2, one_mul] at h1
      exact le_of_lt h1
    rcases le_or_gt (σ j) (σ i) with h | h
    · exact ⟨(i, j), hij, by linarith, hgap i j hlt1⟩
    · exact ⟨(j, i), Ne.symm hij, by linarith, hgap j i hlt2⟩
  have hstrict : 2 * (((n : ℝ) - 1) / 2 - ε) < ((n : ℝ) - 1) * (1 - δ) := by
    have h1 : ((n : ℝ) - 1) * (1 - δ) = ((n : ℝ) - 1) - ((n : ℝ) - 1) * δ := by ring
    linarith
  obtain ⟨surp, hsurp⟩ :
      ∃ f : apportionment_state n → Fin n → ℝ,
        ∀ θ i, f θ i = ((θ.cumulativeSeats i : ℝ) - θ.cumulativeVotes i) :=
    ⟨fun θ i => ((θ.cumulativeSeats i : ℝ) - θ.cumulativeVotes i), fun _ _ => rfl⟩
  have hi0 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    intro h
    have h2 := congrArg Fin.val h
    simp at h2
  obtain ⟨pairOf, hpne, hpspec⟩ :
      ∃ g : (Fin n → ℝ) → Fin n × Fin n,
        (∀ σ, (g σ).1 ≠ (g σ).2) ∧
        (∀ σ : Fin n → ℝ, (∀ i, |σ i| ≤ ((n : ℝ) - 1) / 2 - ε) →
          0 ≤ σ (g σ).1 - σ (g σ).2 ∧ σ (g σ).1 - σ (g σ).2 ≤ 1 - δ) := by
    refine ⟨fun σ => if h : ∃ p : Fin n × Fin n, p.1 ≠ p.2 ∧ 0 ≤ σ p.1 - σ p.2 ∧
        σ p.1 - σ p.2 ≤ 1 - δ then Classical.choose h else (⟨0, by omega⟩, ⟨1, by omega⟩), ?_, ?_⟩
    · intro σ
      dsimp only
      by_cases h : ∃ p : Fin n × Fin n, p.1 ≠ p.2 ∧ 0 ≤ σ p.1 - σ p.2 ∧ σ p.1 - σ p.2 ≤ 1 - δ
      · rw [dif_pos h]
        exact (Classical.choose_spec h).1
      · rw [dif_neg h]
        exact hi0
    · intro σ hσ
      dsimp only
      have h := hpigGen (((n : ℝ) - 1) / 2 - ε) (1 - δ) σ (by linarith) hσ hstrict
      rw [dif_pos h]
      exact ⟨(Classical.choose_spec h).2.1, (Classical.choose_spec h).2.2⟩
  have hvsum : ∀ a b : Fin n, a ≠ b →
      (∑ i, ((if i = a then 1 - δ / 2 else 0) + (if i = b then δ / 2 else 0))) = ((1 : ℕ) : ℝ) := by
    intro a b hab
    rw [Finset.sum_add_distrib]
    have h1 : (∑ i, (if i = a then 1 - δ / 2 else (0 : ℝ))) = 1 - δ / 2 := by
      rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a) (fun c _ hc => if_neg hc)]
      exact if_pos rfl
    have h2 : (∑ i, (if i = b then δ / 2 else (0 : ℝ))) = δ / 2 := by
      rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ b) (fun c _ hc => if_neg hc)]
      exact if_pos rfl
    rw [h1, h2]
    push_cast
    ring
  have hvmem : ∀ a b : Fin n, a ≠ b → ∀ i : Fin n,
      ((if i = a then 1 - δ / 2 else 0) + (if i = b then δ / 2 else (0 : ℝ)))
        ∈ Set.Ico (0 : ℝ) 1 := by
    intro a b hab i
    rw [Set.mem_Ico]
    by_cases hia : i = a
    · have hib : i ≠ b := by rw [hia]; exact hab
      rw [if_pos hia, if_neg hib]
      constructor <;> linarith
    · by_cases hib : i = b
      · rw [if_neg hia, if_pos hib]
        constructor <;> linarith
      · rw [if_neg hia, if_neg hib]
        constructor <;> linarith
  obtain ⟨elect, hseats, hvotes⟩ :
      ∃ f : (Fin n → ℝ) → apportionment_election n,
        (∀ σ, (f σ).seats = 1) ∧
        (∀ σ i, (f σ).votes i =
          (if i = (pairOf σ).1 then 1 - δ / 2 else 0) + (if i = (pairOf σ).2 then δ / 2 else 0)) :=
    ⟨fun σ =>
      { votes := fun i =>
          (if i = (pairOf σ).1 then 1 - δ / 2 else 0) + (if i = (pairOf σ).2 then δ / 2 else 0)
        seats := 1
        seats_pos := Nat.one_pos
        votes_mem_unit := hvmem _ _ (hpne σ)
        sum_votes := hvsum _ _ (hpne σ) },
      fun _ => rfl, fun _ _ => rfl⟩
  obtain ⟨θ, hθ0, hθsucc⟩ :
      ∃ st : ℕ → apportionment_state n,
        st 0 = { cumulativeVotes := fun _ => 0, cumulativeSeats := fun _ => 0 } ∧
        ∀ t, st (t + 1) =
          { cumulativeVotes := fun i => (st t).cumulativeVotes i + (elect (surp (st t))).votes i
            cumulativeSeats := fun i => (st t).cumulativeSeats i +
              if i ∈ method.choose t (st t) (elect (surp (st t))) then 1 else 0 } :=
    ⟨fun t => Nat.rec (motive := fun _ => apportionment_state n)
        { cumulativeVotes := fun _ => 0, cumulativeSeats := fun _ => 0 }
        (fun k st =>
          { cumulativeVotes := fun i => st.cumulativeVotes i + (elect (surp st)).votes i
            cumulativeSeats := fun i => st.cumulativeSeats i +
              if i ∈ method.choose k st (elect (surp st)) then 1 else 0 }) t,
      rfl, fun _ => rfl⟩
  have hstate : ∀ t, induced_state method (fun t => elect (surp (θ t))) t = θ t := by
    intro t
    induction t with
    | zero => rw [hθ0]; rfl
    | succ t ih =>
        rw [hθsucc t]
        simp only [induced_state, ih]
  have hlink : ∀ t i,
      apportionment_surplus method (fun t => elect (surp (θ t))) t i = surp (θ (t + 1)) i := by
    intro t i
    obtain ⟨h1, h2⟩ :=
      greedy_induced_state_cumulative method (fun t => elect (surp (θ t))) (t + 1) i
    rw [hstate (t + 1)] at h1 h2
    rw [apportionment_surplus, cumulative_seats, cumulative_votes, hsurp, ← h1, ← h2]
  have hkey : ∀ (a b : Fin n) (σ σ' : Fin n → ℝ), a ≠ b →
      0 ≤ σ a - σ b → σ a - σ b ≤ 1 - δ →
      ((σ' a = σ a + δ / 2 ∧ σ' b = σ b - δ / 2) ∨
        (σ' a = σ a - (1 - δ / 2) ∧ σ' b = σ b + (1 - δ / 2))) →
      (∀ i, i ≠ a → i ≠ b → σ' i = σ i) →
      (∑ i, (σ i) ^ 2) + δ ^ 2 / 2 ≤ ∑ i, (σ' i) ^ 2 := by
    intro a b σ σ' hab hg1 hg2 hcase hrest
    have hsp : ∑ i, ((σ' i) ^ 2 - (σ i) ^ 2)
        = ((σ' a) ^ 2 - (σ a) ^ 2) + ((σ' b) ^ 2 - (σ b) ^ 2) := by
      have hsub : ∑ i ∈ ({a, b} : Finset (Fin n)), ((σ' i) ^ 2 - (σ i) ^ 2)
          = ∑ i, ((σ' i) ^ 2 - (σ i) ^ 2) := by
        refine Finset.sum_subset (Finset.subset_univ _) ?_
        intro k _ hk
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        rw [hrest k hk.1 hk.2]
        ring
      rw [← hsub, Finset.sum_pair hab]
    have hsum : (∑ i, (σ' i) ^ 2) - ∑ i, (σ i) ^ 2
        = ((σ' a) ^ 2 - (σ a) ^ 2) + ((σ' b) ^ 2 - (σ b) ^ 2) := by
      rw [← Finset.sum_sub_distrib]
      exact hsp
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at hsum
      nlinarith [hsum, mul_nonneg (le_of_lt hδpos) hg1]
    · rw [h1, h2] at hsum
      nlinarith [hsum, mul_le_mul_of_nonneg_left hg2 (show (0 : ℝ) ≤ 1 - δ / 2 by linarith),
        mul_nonneg (le_of_lt hδpos) (show (0 : ℝ) ≤ 1 - δ by linarith)]
  have hstep : ∀ t, (∀ i, |surp (θ t) i| ≤ ((n : ℝ) - 1) / 2 - ε) →
      (∑ i, (surp (θ t) i) ^ 2) + δ ^ 2 / 2 ≤ ∑ i, (surp (θ (t + 1)) i) ^ 2 := by
    intro t hbt
    obtain ⟨hg1, hg2⟩ := hpspec (surp (θ t)) hbt
    have hab := hpne (surp (θ t))
    have hcard : (method.choose t (θ t) (elect (surp (θ t)))).card = 1 := by
      rw [method.card_choose, hseats]
    obtain ⟨x, hxeq⟩ := Finset.card_eq_one.mp hcard
    have hmem : ∀ i, i ∈ method.choose t (θ t) (elect (surp (θ t))) ↔ i = x := by
      intro i
      rw [hxeq, Finset.mem_singleton]
    have hxpos : 0 < (elect (surp (θ t))).votes x :=
      method.choose_positive t (θ t) (elect (surp (θ t))) x ((hmem x).mpr rfl)
    have hupd : ∀ i, surp (θ (t + 1)) i
        = surp (θ t) i + (if i = x then (1 : ℝ) else 0) - (elect (surp (θ t))).votes i := by
      intro i
      rw [hsurp, hsurp, hθsucc t]
      dsimp only
      by_cases hi : i = x
      · rw [if_pos ((hmem i).mpr hi), if_pos hi]
        push_cast
        ring
      · rw [if_neg (fun hc => hi ((hmem i).mp hc)), if_neg hi]
        push_cast
        ring
    have hva : (elect (surp (θ t))).votes (pairOf (surp (θ t))).1 = 1 - δ / 2 := by
      rw [hvotes, if_pos rfl, if_neg hab]
      ring
    have hvb : (elect (surp (θ t))).votes (pairOf (surp (θ t))).2 = δ / 2 := by
      rw [hvotes, if_neg (Ne.symm hab), if_pos rfl]
      ring
    have hv0 : ∀ i, i ≠ (pairOf (surp (θ t))).1 → i ≠ (pairOf (surp (θ t))).2 →
        (elect (surp (θ t))).votes i = 0 := by
      intro i h1 h2
      rw [hvotes, if_neg h1, if_neg h2]
      ring
    have hxab : x = (pairOf (surp (θ t))).1 ∨ x = (pairOf (surp (θ t))).2 := by
      by_contra hcon
      rw [not_or] at hcon
      rw [hv0 x hcon.1 hcon.2] at hxpos
      exact absurd hxpos (lt_irrefl 0)
    refine hkey (pairOf (surp (θ t))).1 (pairOf (surp (θ t))).2 (surp (θ t)) (surp (θ (t + 1)))
      hab hg1 hg2 ?_ ?_
    · rcases hxab with h | h
      · left
        refine ⟨?_, ?_⟩
        · rw [hupd, hva, if_pos h.symm]
          ring
        · rw [hupd, hvb, if_neg (fun hc => hab (hc.trans h).symm)]
          ring
      · right
        refine ⟨?_, ?_⟩
        · rw [hupd, hva, if_neg (fun hc => hab (hc.trans h))]
          ring
        · rw [hupd, hvb, if_pos h.symm]
          ring
    · intro i h1 h2
      have hix : i ≠ x := by
        rcases hxab with h | h
        · rw [h]; exact h1
        · rw [h]; exact h2
      rw [hupd, hv0 i h1 h2, if_neg hix]
      ring
  refine ⟨fun t => elect (surp (θ t)), ?_⟩
  intro hprop
  have hα0 : (0 : ℝ) ≤ ((n : ℝ) - 1) / 2 - ε :=
    le_trans (abs_nonneg _) (hprop 0 ⟨0, by omega⟩)
  have hb : ∀ t i, |surp (θ t) i| ≤ ((n : ℝ) - 1) / 2 - ε := by
    intro t i
    cases t with
    | zero =>
        have h0 : surp (θ 0) i = 0 := by
          rw [hsurp, hθ0]
          norm_num
        rw [h0, abs_zero]
        exact hα0
    | succ t =>
        rw [← hlink t i]
        exact hprop t i
  have hgrow : ∀ t : ℕ, (t : ℝ) * (δ ^ 2 / 2) ≤ ∑ i, (surp (θ t) i) ^ 2 := by
    intro t
    induction t with
    | zero =>
        have h0 : (0 : ℝ) ≤ ∑ i, (surp (θ 0) i) ^ 2 :=
          Finset.sum_nonneg (fun i _ => sq_nonneg _)
        simpa using h0
    | succ t ih =>
        have h1 := hstep t (hb t)
        have h2 : ((t + 1 : ℕ) : ℝ) * (δ ^ 2 / 2) = (t : ℝ) * (δ ^ 2 / 2) + δ ^ 2 / 2 := by
          push_cast
          ring
        rw [h2]
        linarith
  have hbnd : ∀ t, (∑ i, (surp (θ t) i) ^ 2) ≤ (n : ℝ) * (((n : ℝ) - 1) / 2 - ε) ^ 2 := by
    intro t
    have h1 : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        (surp (θ t) i) ^ 2 ≤ (((n : ℝ) - 1) / 2 - ε) ^ 2 := by
      intro i _
      obtain ⟨hl, hu⟩ := abs_le.mp (hb t i)
      exact sq_le_sq' hl hu
    calc (∑ i, (surp (θ t) i) ^ 2) ≤ ∑ _i : Fin n, (((n : ℝ) - 1) / 2 - ε) ^ 2 :=
          Finset.sum_le_sum h1
      _ = (n : ℝ) * (((n : ℝ) - 1) / 2 - ε) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hδ2 : (0 : ℝ) < δ ^ 2 / 2 := div_pos (pow_pos hδpos 2) (by norm_num)
  obtain ⟨T, hT⟩ := exists_nat_gt (((n : ℝ) * (((n : ℝ) - 1) / 2 - ε) ^ 2) * (δ ^ 2 / 2)⁻¹)
  have h1 := mul_lt_mul_of_pos_right hT hδ2
  have h2 : ((n : ℝ) * (((n : ℝ) - 1) / 2 - ε) ^ 2) * (δ ^ 2 / 2)⁻¹ * (δ ^ 2 / 2)
      = (n : ℝ) * (((n : ℝ) - 1) / 2 - ε) ^ 2 := by
    calc ((n : ℝ) * (((n : ℝ) - 1) / 2 - ε) ^ 2) * (δ ^ 2 / 2)⁻¹ * (δ ^ 2 / 2)
        = ((n : ℝ) * (((n : ℝ) - 1) / 2 - ε) ^ 2) * ((δ ^ 2 / 2)⁻¹ * (δ ^ 2 / 2)) := by ring
      _ = ((n : ℝ) * (((n : ℝ) - 1) / 2 - ε) ^ 2) * 1 := by
          rw [inv_mul_cancel₀ (ne_of_gt hδ2)]
      _ = (n : ℝ) * (((n : ℝ) - 1) / 2 - ε) ^ 2 := mul_one _
  rw [h2] at h1
  have h3 := hgrow T
  have h4 := hbnd T
  linarith

@[blueprint "thm:app-quota"
  (statement := /-- Let $n\geq2$ be an integer.  There exists an online apportionment method
  that is $(n-1)/2$-proportional on every $n$-dimensional instance and strictly
  $1$-proportional on every three-dimensional instance.  Conversely, for every
  $\varepsilon>0$, every deterministic online apportionment method on $n$ parties fails to be
  $((n-1)/2-\varepsilon)$-proportional on some $n$-dimensional instance. -/)
  (proof := /-- The asserted online method and both of its uniform upper guarantees are precisely
  \cref{lem:greedy-upper-guarantee}.  For the converse, fix $\varepsilon>0$.  By
  \cref{lem:adversarial-lower-bound}, every deterministic online apportionment method on $n$
  parties fails to be $((n-1)/2-\varepsilon)$-proportional on some $n$-dimensional instance.
  Since $\varepsilon$ was arbitrary, conjoining this
  lower bound with the two upper guarantees proves the theorem. -/)
  (title := /-- Optimal proportionality of online apportionment -/)
  (latexEnv := "theorem")]
theorem app_quota (n : ℕ) (hn : 1 < n) :
    (∃ method : online_apportionment_method_family,
      (∀ input : apportionment_instance n,
        proportional (method n) input (((n : ℝ) - 1) / 2)) ∧
      (∀ input : apportionment_instance 3,
        strictly_proportional (method 3) input 1)) ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ method : online_apportionment_method n,
        ∃ input : apportionment_instance n,
          ¬ proportional method input (((n : ℝ) - 1) / 2 - ε)) := by
  refine ⟨greedy_upper_guarantee n (Nat.zero_lt_of_lt hn), ?_⟩
  intro ε hε
  exact adversarial_lower_bound n hn ε hε

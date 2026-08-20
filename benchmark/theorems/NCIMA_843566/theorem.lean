import Mathlib

set_option linter.all false
set_option maxHeartbeats 500000

structure line where
  slope : ℝ
  intercept : ℝ

noncomputable instance line_decidable_eq : DecidableEq line := Classical.decEq line

def line_value (l : line) (δ : ℝ) : ℝ := l.slope * δ + l.intercept

abbrev line_arrangement := Finset (ℕ × line)

def k_level_vertices (A : line_arrangement) (k : ℕ) : Set (ℝ × ℝ) :=
  { q |
      (∃ l₁ ∈ A, ∃ l₂ ∈ A,
        l₁.2 ≠ l₂.2 ∧ line_value l₁.2 q.1 = q.2 ∧ line_value l₂.2 q.1 = q.2) ∧
      (A.filter (fun l => line_value l.2 q.1 < q.2)).card ≤ k ∧
      k < (A.filter (fun l => line_value l.2 q.1 < q.2)).card +
        (A.filter (fun l => line_value l.2 q.1 = q.2)).card }

noncomputable def k_level_complexity (A : line_arrangement) (k : ℕ) : ℕ :=
  (k_level_vertices A k).ncard

def eventually_two_scale_dominates (g : ℕ → ℝ) : Prop :=
  ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ m : ℕ, m ≤ 2 * n - 1 →
    max 1 (g m) ≤ D * g n

def k_level_bounded_by (g : ℕ → ℝ) : Prop :=
  (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ A : line_arrangement,
      A.card = m → ∀ k : ℕ, k ≤ m →
        (k_level_complexity A k : ℝ) ≤ C * g m) ∧
    eventually_two_scale_dominates g

structure apportionment_instance where
  n : ℕ
  p : Fin n → ℕ
  H : ℕ
  hn : 0 < n
  hp : ∀ i, 0 < p i
  hH : 0 < H

def round_delta_set (δ x : ℝ) : Set ℤ :=
  { z |
      (δ < Int.fract x ∧ z = ⌈x⌉) ∨
      (Int.fract x < δ ∧ z = ⌊x⌋) ∨
      (Int.fract x = δ ∧ (z = ⌊x⌋ ∨ z = ⌈x⌉)) }

def divisor_output (inst : apportionment_instance) (δ : ℝ) : Set (Fin inst.n → ℕ) :=
  { x |
      (∃ lam : ℝ, 0 < lam ∧ ∀ i, ((x i : ℤ)) ∈ round_delta_set δ (lam * (inst.p i : ℝ))) ∧
      (∑ i, x i) = inst.H }

def breaking_points (inst : apportionment_instance) : Set ℝ :=
  { δ |
      δ ∈ Set.Ioc (0 : ℝ) 1 ∧
      (δ = 1 ∨
        ∀ ε : ℝ, 0 < ε →
          ∃ a ∈ Set.Ioo (δ - ε) δ, divisor_output inst a ≠ divisor_output inst δ) }

noncomputable def num_breaking_points (inst : apportionment_instance) : ℕ :=
  (breaking_points inst).ncard

def regular_k_level_crossings (A : line_arrangement) (k r : ℕ) : Set (ℝ × ℝ) :=
  { q |
      q ∈ k_level_vertices A k ∧
      q.1 ∈ Set.Ioo (0 : ℝ) 1 ∧
      (A.filter (fun l => line_value l.2 q.1 = q.2)).card = 2 ∧
      (A.filter (fun l => line_value l.2 q.1 < q.2)).card = r }

def stable_k_level_perturbation_data (A : line_arrangement) (k : ℕ) : Prop :=
  ∃ A' : line_arrangement,
    A'.card = A.card ∧
    Set.InjOn (fun q : ℝ × ℝ => q.1)
      (regular_k_level_crossings A' k k ∪ regular_k_level_crossings A' k (k - 1)) ∧
    ∃ φ : ℝ × ℝ → ℝ × ℝ,
      Set.MapsTo φ (k_level_vertices A k)
        (regular_k_level_crossings A' k k ∪ regular_k_level_crossings A' k (k - 1)) ∧
      Set.InjOn φ (k_level_vertices A k)

def k_level_witnessed_by (h : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ A : line_arrangement, A.card = m ∧
    ∃ k : ℕ, k ≤ m ∧ c * h m ≤ (k_level_complexity A k : ℝ) ∧
      stable_k_level_perturbation_data A k

theorem main (g h : ℕ → ℝ) (hg : k_level_bounded_by g) (hh : k_level_witnessed_by h) :
    (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ inst : apportionment_instance, N ≤ inst.n →
        (num_breaking_points inst : ℝ) ≤ C * g inst.n) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ inst : apportionment_instance, inst.n = n ∧
          c * h n ≤ (num_breaking_points inst : ℝ)) := by sorry

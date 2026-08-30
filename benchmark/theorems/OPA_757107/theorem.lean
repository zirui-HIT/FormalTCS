import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Fintype.Card

open scoped BigOperators

structure apportionment_election (n : ℕ) where
  votes : Fin n → ℝ
  seats : ℕ
  seats_pos : 0 < seats
  votes_mem_unit : ∀ i, votes i ∈ Set.Ico (0 : ℝ) 1
  sum_votes : (∑ i, votes i) = (seats : ℝ)

abbrev apportionment_instance (n : ℕ) := ℕ → apportionment_election n

abbrev seat_allocation (n : ℕ) := Finset (Fin n)

structure apportionment_state (n : ℕ) where
  cumulativeVotes : Fin n → ℝ
  cumulativeSeats : Fin n → ℕ

structure online_apportionment_method (n : ℕ) where
  choose : ℕ → apportionment_state n → apportionment_election n → seat_allocation n
  card_choose : ∀ t state election, (choose t state election).card = election.seats
  choose_positive :
    ∀ t state election i, i ∈ choose t state election → 0 < election.votes i

abbrev online_apportionment_method_family :=
  (n : ℕ) → online_apportionment_method n

def induced_state {n : ℕ} (method : online_apportionment_method n)
    (input : apportionment_instance n) : ℕ → apportionment_state n
  | 0 => { cumulativeVotes := fun _ => 0, cumulativeSeats := fun _ => 0 }
  | t + 1 =>
      let state := induced_state method input t
      let allocation := method.choose t state (input t)
      { cumulativeVotes := fun i => state.cumulativeVotes i + (input t).votes i
        cumulativeSeats := fun i => state.cumulativeSeats i + if i ∈ allocation then 1 else 0 }

def allocation_at {n : ℕ} (method : online_apportionment_method n)
    (input : apportionment_instance n) (t : ℕ) : seat_allocation n :=
  method.choose t (induced_state method input t) (input t)

def cumulative_votes {n : ℕ} (input : apportionment_instance n)
    (t : ℕ) (i : Fin n) : ℝ :=
  ∑ k ∈ Finset.range (t + 1), (input k).votes i

def cumulative_seats {n : ℕ} (method : online_apportionment_method n)
    (input : apportionment_instance n) (t : ℕ) (i : Fin n) : ℝ :=
  ∑ k ∈ Finset.range (t + 1),
    if i ∈ allocation_at method input k then (1 : ℝ) else 0

def apportionment_surplus {n : ℕ} (method : online_apportionment_method n)
    (input : apportionment_instance n) (t : ℕ) (i : Fin n) : ℝ :=
  cumulative_seats method input t i - cumulative_votes input t i

def proportional {n : ℕ} (method : online_apportionment_method n)
    (input : apportionment_instance n) (α : ℝ) : Prop :=
  ∀ t i, |apportionment_surplus method input t i| ≤ α

def strictly_proportional {n : ℕ} (method : online_apportionment_method n)
    (input : apportionment_instance n) (α : ℝ) : Prop :=
  ∀ t i, |apportionment_surplus method input t i| < α

theorem app_quota (n : ℕ) (hn : 1 < n) :
    (∃ method : online_apportionment_method_family,
      (∀ input : apportionment_instance n,
        proportional (method n) input (((n : ℝ) - 1) / 2)) ∧
      (∀ input : apportionment_instance 3,
        strictly_proportional (method 3) input 1)) ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ method : online_apportionment_method n,
        ∃ input : apportionment_instance n,
          ¬ proportional method input (((n : ℝ) - 1) / 2 - ε)) := by sorry

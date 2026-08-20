import Mathlib.InformationTheory.Hamming
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.Finite.Basic

set_option linter.all false

def generates_units {F : Type*} [Field F] (γ : Fˣ) : Prop :=
  ∀ x : Fˣ, x ∈ Subgroup.zpowers γ

def frs_eval_points {F : Type*} [Field F] {s n : ℕ} (γ : Fˣ) (α : Fin n → F) :
    Fin s → Fin n → F :=
  fun i j => (γ : F) ^ (i : ℕ) * α j

def appropriate_eval_points {F : Type*} [Field F] {s n : ℕ} (γ : Fˣ) (α : Fin n → F) : Prop :=
  Function.Injective fun p : Fin s × Fin n => frs_eval_points γ α p.1 p.2

def frs_encode {F : Type*} [Field F] {s n : ℕ} (γ : Fˣ) (α : Fin n → F) (f : Polynomial F) :
    Fin n → Fin s → F :=
  fun j i => Polynomial.eval (frs_eval_points γ α i j) f

def frs_code {F : Type*} [Field F] {s n : ℕ} (k : ℕ) (γ : Fˣ) (α : Fin n → F) :
    Set (Fin n → Fin s → F) :=
  {c | ∃ f ∈ Polynomial.degreeLT F k, c = frs_encode γ α f}

noncomputable def frs_rate (s n k : ℕ) : ℝ :=
  (k : ℝ) / ((s : ℝ) * (n : ℝ))

noncomputable def frs_decoding_radius (s n k L : ℕ) : ℝ :=
  (L : ℝ) / ((L : ℝ) + 1) * (1 - (s : ℝ) * frs_rate s n k / ((s : ℝ) - (L : ℝ) + 1))

def list_decodable {n : ℕ} {A : Type*} [DecidableEq A] (C : Set (Fin n → A)) (ρ : ℝ) (L : ℕ) :
    Prop :=
  ∀ y : Fin n → A, {c ∈ C | (hammingDist c y : ℝ) ≤ ρ * (n : ℝ)}.ncard ≤ L

theorem frs_list_decodable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {s n : ℕ} (k L : ℕ)
    (hs : 1 ≤ s) (hn : 1 ≤ n) (hL : 1 ≤ L) (hk : 1 ≤ k) (hkn : k ≤ n) (hsL : L ≤ s) (γ : Fˣ)
    (hγ : generates_units γ) (α : Fin n → F) (hα : appropriate_eval_points (s := s) γ α) :
    list_decodable (frs_code (s := s) k γ α) (frs_decoding_radius s n k L) L := by sorry

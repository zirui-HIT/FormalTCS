import Mathlib

abbrev labeled_point (X : Type) := X × Bool

abbrev weighted_labeled_point (X : Type) := labeled_point X × Nat

abbrev hypothesis_class (X : Type) := Set (X → Bool)

def error_count {X : Type} (h : X → Bool) (S : List (labeled_point X)) : Nat :=
  S.countP (fun z => h z.1 != z.2)

def weighted_error {X : Type} (h : X → Bool)
    (W : List (weighted_labeled_point X)) : Nat :=
  (W.map (fun z => if h z.1.1 != z.1.2 then z.2 else 0)).sum

def robustly_realizable {X : Type} (H : hypothesis_class X) (b : Nat)
    (S : List (labeled_point X)) : Prop :=
  ∃ h : X → Bool, h ∈ H ∧ error_count h S ≤ b

def weighted_robustly_realizable {X : Type} (H : hypothesis_class X) (b : Nat)
    (W : List (weighted_labeled_point X)) : Prop :=
  ∃ h : X → Bool, h ∈ H ∧ weighted_error h W ≤ b

def robust_agreement {X : Type} (H : hypothesis_class X) (b : Nat)
    (S : List (labeled_point X)) (x : X) (y : Bool) : Prop :=
  ∀ h : X → Bool, h ∈ H → error_count h S ≤ b → h x = y

def robust_certificate {X : Type} (H : hypothesis_class X) (b : Nat)
    (S : List (labeled_point X)) (x : X) (y : Bool) : Prop :=
  robustly_realizable H b S ∧ robust_agreement H b S x y

def proper_subsequence {X : Type} (S' S : List (labeled_point X)) : Prop :=
  List.Sublist S' S ∧ S' ≠ S

def robust_hollow_star_weight_shape {X : Type} (b : Nat)
    (W : List (weighted_labeled_point X)) : Prop :=
  ∃ i : Nat, i < W.length ∧
    ∀ j : Nat, ∀ hj : j < W.length,
      (W.get ⟨j, hj⟩).2 = if j = i then b + 1 else 1

def robust_hollow_star {X : Type} (H : hypothesis_class X) (b : Nat)
    (W : List (weighted_labeled_point X)) : Prop :=
  robust_hollow_star_weight_shape b W ∧
    ¬ weighted_robustly_realizable H b W ∧
    ∀ i : Nat, i < W.length →
      weighted_robustly_realizable H b (W.eraseIdx i)

def robust_hollow_star_number {X : Type} (H : hypothesis_class X)
    (b s : Nat) : Prop :=
  (∀ W : List (weighted_labeled_point X),
      robust_hollow_star H b W → W.length ≤ s) ∧
    ∃ W : List (weighted_labeled_point X),
      robust_hollow_star H b W ∧ W.length = s

theorem robust_hollow_star_characterizes_minimum_certificate_size {X : Type}
    (H : hypothesis_class X) (b s : Nat) (S : List (labeled_point X))
    (x : X) (y : Bool) (hnum : robust_hollow_star_number H b s)
    (hreal : robustly_realizable H b S)
    (hagree : robust_agreement H b S x y) :
    (∃ S' : List (labeled_point X),
      List.Sublist S' S ∧ robust_certificate H b S' x y ∧ S'.length ≤ s - 1) ∧
    (∃ S₀ : List (labeled_point X), ∃ x₀ : X, ∃ y₀ : Bool,
      S₀.length = s - 1 ∧
      robustly_realizable H b S₀ ∧
      robust_agreement H b S₀ x₀ y₀ ∧
      ∀ S' : List (labeled_point X),
        proper_subsequence S' S₀ →
          ¬ robust_certificate H b S' x₀ y₀) := by
  sorry

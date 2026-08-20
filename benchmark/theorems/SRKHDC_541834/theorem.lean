import Mathlib.Data.Real.Sign
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Matrix.Rank

abbrev binary_string (n : ℕ) := Fin n → Bool

def exact_hamming_matrix (n k : ℕ) :
    Matrix (binary_string n) (binary_string n) Bool :=
  fun x y => decide (hammingDist x y = k)

def boolean_sign : Bool → ℝ
  | false => -1
  | true => 1

def sign_realizes {I J : Type*}
    (M : Matrix I J Bool) (A : Matrix I J ℝ) : Prop :=
  ∀ i j, Real.sign (A i j) = boolean_sign (M i j)

noncomputable def sign_rank {I J : Type*} [Fintype J]
    (M : Matrix I J Bool) : ℕ :=
  sInf {r : ℕ | ∃ A : Matrix I J ℝ,
    sign_realizes M A ∧ Matrix.rank A = r}

theorem sign_rank_of_exact_hamming_distance :
    ∃ c : ℕ, ∀ n k : ℕ,
      sign_rank (exact_hamming_matrix n k) ≤ 2 ^ (c * (k + 1)) := by sorry

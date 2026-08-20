import Mathlib

namespace Proof.Types.QProjection

/-- The `q`-th base-`n` digit of `c` (Definition 3.14). -/
def digit (c n q : ℕ) : ℕ := (c / n ^ q) % n

/-- The γ-th smallest element of `Q` (0-indexed), via the sorted list of `Q`.
Returns `0` when `γ` is out of range. -/
def qElem (Q : Finset ℕ) (γ : ℕ) : ℕ := (Q.sort (· ≤ ·)).getD γ 0

/-- The Q-projection of a row selection `R` and column selection `C`
(Definition 3.15).

Let `ℓ = Q.card` and let `q_0 < q_1 < … < q_{ℓ-1}` be the sorted elements of `Q`.

* If `Q = ∅`, returns `(∅, {0})`.
* Otherwise returns `(S, D)` where
  - `S = { m*γ + r : γ < ℓ, r < m, (m*q_γ + r) ∈ R }`, and
  - `D = { Σ_{γ<ℓ} (digit c n q_γ) * n^γ : c ∈ C }`. -/
def qProjection (R C : Finset ℕ) (m n p : ℕ) (Q : Finset ℕ) :
    Finset ℕ × Finset ℕ :=
  if Q = ∅ then
    (∅, {0})
  else
    let ℓ := Q.card
    let S : Finset ℕ :=
      ((Finset.range ℓ).product (Finset.range m)).filter
          (fun pr => (m * qElem Q pr.1 + pr.2) ∈ R)
        |>.image (fun pr => m * pr.1 + pr.2)
    let D : Finset ℕ :=
      C.image (fun c => ∑ γ ∈ Finset.range ℓ, digit c n (qElem Q γ) * n ^ γ)
    (S, D)

end Proof.Types.QProjection

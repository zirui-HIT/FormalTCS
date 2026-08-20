import Architect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.Lattice.Nat

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

@[blueprint "def:booleanize"
  (statement := /-- For a residue $x\in \mathbb{F}_p=\mathbb{Z}/p\mathbb{Z}$, its Booleanization records whether $x$ is the residue $1$. Thus two residues have the same Booleanization precisely when either both are $1$ or neither is $1$. -/)
  (title := /-- Booleanization over a prime residue field -/)
  (latexEnv := "definition")]
def booleanize {p : ℕ} (x : ZMod p) : Bool :=
  decide (x = 1)

@[blueprint "def:boolean-disagreement-count"
  (statement := /-- Let $M$ and $L$ be matrices over $\mathbb{Z}/p\mathbb{Z}$ with the same finite row type $I$ and column type $J$. Their Boolean disagreement count is the cardinality of the set of pairs $(i,j)\in I\times J$ at which the Booleanizations of $M_{ij}$ and $L_{ij}$ differ. -/)
  (title := /-- Boolean disagreement count -/)
  (latexEnv := "definition")]
def boolean_disagreement_count {p : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M L : Matrix ι κ (ZMod p)) : ℕ :=
  ((Finset.univ : Finset (ι × κ)).filter fun ij ↦
    booleanize (M ij.1 ij.2) ≠ booleanize (L ij.1 ij.2)).card

@[blueprint "def:boolean-rigidity"
  (statement := /-- Let $p$ be prime, let $I$ and $J$ be finite index types, let $M\in\mathbb{F}_p^{I\times J}$, and let $r\in\mathbb{N}$. The Boolean rigidity of $M$ at rank $r$ is the minimum Boolean disagreement count between $M$ and a matrix $L\in\mathbb{F}_p^{I\times J}$ of rank at most $r$. The minimum is expressed as the infimum of the corresponding nonempty set of natural numbers. -/)
  (title := /-- Boolean matrix rigidity -/)
  (latexEnv := "definition")]
noncomputable def boolean_rigidity {p : ℕ} [Fact p.Prime]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ (ZMod p)) (r : ℕ) : ℕ :=
  sInf {s : ℕ | ∃ L : Matrix ι κ (ZMod p),
    Matrix.rank L ≤ r ∧ boolean_disagreement_count M L = s}

@[blueprint "def:is-sign-matrix"
  (statement := /-- A matrix $A\in\mathbb{F}_p^{I\times J}$ is a sign matrix if, for every $(i,j)\in I\times J$, the entry $A_{ij}$ is equal in $\mathbb{F}_p$ to either $1$ or $-1$. -/)
  (title := /-- Sign matrices over a residue field -/)
  (latexEnv := "definition")]
def is_sign_matrix {p : ℕ} {ι κ : Type*} (A : Matrix ι κ (ZMod p)) : Prop :=
  ∀ i j, A i j = 1 ∨ A i j = -1

@[blueprint "def:kronecker-power"
  (statement := /-- Let $A\in\mathbb{F}_p^{q\times q}$ and let $n\in\mathbb{N}$. Its $n$-fold Kronecker power is the matrix whose rows and columns are indexed by functions $x,y:\operatorname{Fin}(n)\to\operatorname{Fin}(q)$ and whose $(x,y)$-entry is $\prod_{t\in\operatorname{Fin}(n)}A_{x(t),y(t)}$. Since this index type has cardinality $q^n$, the resulting matrix has dimensions $q^n\times q^n$. -/)
  (title := /-- Uniformly indexed Kronecker powers -/)
  (latexEnv := "definition")]
def kronecker_power {p q : ℕ} (A : Matrix (Fin q) (Fin q) (ZMod p)) (n : ℕ) :
    Matrix (Fin n → Fin q) (Fin n → Fin q) (ZMod p) :=
  Matrix.of fun x y ↦ ∏ t : Fin n, A (x t) (y t)

@[blueprint "lem:tensor-kernel-sum-square-bound"
  (statement := /-- Let $q\in\mathbb N$, let $S\in\mathbb R^{q\times q}$, and let $\beta\ge0$. Suppose that
  \[
    \sum_{i=1}^q\left(\sum_{j=1}^q S_{ij}v_j\right)^2
      \le \beta\sum_{j=1}^q v_j^2
  \]
  for every $v\in\mathbb R^q$. Then, for every $n\in\mathbb N$ and every real vector $g$ indexed by $[q]^n$,
  \[
    \sum_{x\in[q]^n}\left(\sum_{y\in[q]^n}
      \left(\prod_{t=1}^n S_{x_t y_t}\right)g_y\right)^2
      \le \beta^n\sum_{y\in[q]^n}g_y^2.
  \] -/)
  (proof := /-- Proceed by induction on $n$. For $n=0$, both index types are singletons and the assertion is an identity. For the successor step, split each word into its first coordinate and its remaining coordinates. Apply the assumed one-step estimate to the sum over the first output coordinate. After interchanging the resulting finite sums, apply the induction hypothesis separately for each fixed first input coordinate. Multiplication by the remaining factor $\beta$ yields $\beta^{n+1}$, and reassembling the first coordinate with the tail gives the asserted right-hand side. -/)
  (title := /-- Tensorization of a finite-kernel squared-norm estimate -/)
  (latexEnv := "lemma")]
lemma tensor_kernel_sum_square_bound
    (q : ℕ) (S : Matrix (Fin q) (Fin q) ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hS : ∀ v : Fin q → ℝ,
      (∑ i : Fin q, (∑ j : Fin q, S i j * v j) ^ 2) ≤
        β * ∑ j : Fin q, (v j) ^ 2) :
    ∀ (n : ℕ) (g : (Fin n → Fin q) → ℝ),
      (∑ x : Fin n → Fin q,
        (∑ y : Fin n → Fin q, (∏ t : Fin n, S (x t) (y t)) * g y) ^ 2) ≤
          β ^ n * ∑ y : Fin n → Fin q, (g y) ^ 2 := by
  intro n
  induction n with
  | zero =>
      intro g
      simp
  | succ n ih =>
      intro g
      let e := Fin.consEquiv (fun _ : Fin (n + 1) => Fin q)
      have he (f : (Fin (n + 1) → Fin q) → ℝ) :
          (∑ x, f x) = ∑ a : Fin q, ∑ x' : Fin n → Fin q, f (e (a, x')) := by
        calc
          (∑ x, f x) = ∑ z : Fin q × (Fin n → Fin q), f (e z) :=
            (e.sum_comp f).symm
          _ = ∑ a : Fin q, ∑ x' : Fin n → Fin q, f (e (a, x')) :=
            Fintype.sum_prod_type _
      let h : Fin q → (Fin n → Fin q) → ℝ := fun b x' =>
        ∑ y' : Fin n → Fin q, (∏ t : Fin n, S (x' t) (y' t)) * g (e (b, y'))
      have hinner (a : Fin q) (x' : Fin n → Fin q) :
          (∑ y : Fin (n + 1) → Fin q,
            (∏ t : Fin (n + 1), S ((e (a, x')) t) (y t)) * g y) =
            ∑ b : Fin q, S a b * h b x' := by
        rw [he]
        dsimp [e, Fin.consEquiv]
        simp_rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        simp_rw [mul_assoc, ← Finset.mul_sum]
        rfl
      conv_lhs => rw [he]
      conv_rhs => rw [he]
      simp_rw [hinner]
      have hb (b : Fin q) :
          (∑ x' : Fin n → Fin q, (h b x') ^ 2) ≤
            β ^ n * ∑ y' : Fin n → Fin q, (g (e (b, y'))) ^ 2 := by
        simpa [h] using ih (fun y' => g (e (b, y')))
      calc
        (∑ a : Fin q, ∑ x' : Fin n → Fin q, (∑ b : Fin q, S a b * h b x') ^ 2) =
            ∑ x' : Fin n → Fin q, ∑ a : Fin q, (∑ b : Fin q, S a b * h b x') ^ 2 := by
              rw [Finset.sum_comm]
        _ ≤ ∑ x' : Fin n → Fin q, β * ∑ b : Fin q, (h b x') ^ 2 := by
              gcongr with x'
              exact hS (fun b => h b x')
        _ = β * ∑ b : Fin q, ∑ x' : Fin n → Fin q, (h b x') ^ 2 := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
        _ ≤ β * ∑ b : Fin q,
              (β ^ n * ∑ y' : Fin n → Fin q, (g (e (b, y'))) ^ 2) := by
              gcongr with b
              exact hb b
        _ = β ^ (n + 1) *
              ∑ a : Fin q, ∑ x' : Fin n → Fin q, (g (e (a, x'))) ^ 2 := by
              rw [pow_succ]
              simp_rw [Finset.mul_sum]
              ring_nf

@[blueprint "lem:sign-matrix-base-sum-square-bound"
  (statement := /-- Let $p$ be prime, let $q\in\mathbb N$, and let $A\in\{-1,1\}^{q\times q}$ over $\mathbb F_p$ have rank greater than $1$. Define $S_{ij}=1$ if $A_{ij}=1$ and $S_{ij}=-1$ otherwise. Then $\beta=q^2-2$ satisfies $0\le\beta<q^2$, and for every $v\in\mathbb R^q$,
  \[
    \sum_i\left(\sum_j S_{ij}v_j\right)^2
      \le \beta\sum_jv_j^2.
  \] -/)
  (proof := /-- By \cref{def:is-sign-matrix}, all entries of $A$ are signs. The rank hypothesis first implies $q\ge2$ and excludes characteristic two. If every row were equal to a fixed row or its negative, $A$ would be an outer product and hence would have rank at most one. Thus two rows are neither equal nor negatives. Their agreement and disagreement coordinate sets are both nonempty. Splitting their two linear forms into the agreement and disagreement coordinates and applying Cauchy--Schwarz on each part bounds the sum of their squares by $2(q-1)\sum_jv_j^2$. Applying the ordinary Cauchy--Schwarz bound $q\sum_jv_j^2$ to each of the other $q-2$ rows gives the total factor $q^2-2$. The inequalities $0\le q^2-2<q^2$ follow from $q\ge2$. -/)
  (title := /-- Strict squared-norm bound for a non-rank-one sign matrix -/)
  (latexEnv := "lemma")]
lemma sign_matrix_base_sum_square_bound
    (p q : ℕ) [Fact p.Prime]
    (A : Matrix (Fin q) (Fin q) (ZMod p))
    (hA : is_sign_matrix A) (hrank : 1 < Matrix.rank A) :
    let S : Matrix (Fin q) (Fin q) ℝ :=
      fun i j => if A i j = 1 then 1 else -1
    0 ≤ (q : ℝ) ^ 2 - 2 ∧ (q : ℝ) ^ 2 - 2 < (q : ℝ) ^ 2 ∧
      ∀ v : Fin q → ℝ,
        (∑ i : Fin q, (∑ j : Fin q, S i j * v j) ^ 2) ≤
          ((q : ℝ) ^ 2 - 2) * ∑ j : Fin q, (v j) ^ 2 := by
  classical
  dsimp only
  have hq : 2 ≤ q := by
    have h := Matrix.rank_le_card_width A
    simp only [Fintype.card_fin] at h
    omega
  have hp : p ≠ 2 := by
    intro hp
    subst p
    simp only [is_sign_matrix] at hA
    have hAe :
        A = Matrix.vecMulVec (fun _ : Fin q => (1 : ZMod 2)) (fun _ : Fin q => 1) := by
      ext i j
      rcases hA i j with hij | hij
      · simpa [Matrix.vecMulVec] using hij
      · have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
        have hm : (-1 : ZMod 2) = 1 := by
          calc
            (-1 : ZMod 2) = 1 - 2 := by ring
            _ = 1 := by rw [htwo]; ring
        simpa [Matrix.vecMulVec, hm] using hij
    have hle :=
      Matrix.rank_vecMulVec_le (fun _ : Fin q => (1 : ZMod 2)) (fun _ : Fin q => 1)
    rw [hAe] at hrank
    omega
  have hqR : (2 : ℝ) ≤ q := by
    exact_mod_cast hq
  constructor
  · nlinarith [sq_nonneg (q : ℝ)]
  constructor
  · linarith
  let a₀ : Fin q := ⟨0, by omega⟩
  have hcoord (i k : Fin q) (j : Fin q) :
      A i j = A k j ∨ A i j = -A k j := by
    rcases hA i j with hi | hi <;> rcases hA k j with h₀ | h₀
    · left
      rw [hi, h₀]
    · right
      rw [hi, h₀]
      ring
    · right
      rw [hi, h₀]
    · left
      rw [hi, h₀]
  have hpair :
      ∃ a b : Fin q,
        (∃ j : Fin q, A a j = A b j) ∧
          ∃ j : Fin q, A a j = -A b j := by
    by_contra hn
    have hn' :
        ∀ a b : Fin q,
          ¬((∃ j : Fin q, A a j = A b j) ∧
            ∃ j : Fin q, A a j = -A b j) := by
      simpa using hn
    have hrows (i : Fin q) :
        (∀ j : Fin q, A i j = A a₀ j) ∨
          ∀ j : Fin q, A i j = -A a₀ j := by
      by_cases hi : ∀ j : Fin q, A i j = A a₀ j
      · exact Or.inl hi
      · right
        have hne : ∃ j : Fin q, A i j ≠ A a₀ j := not_forall.mp hi
        obtain ⟨j, hj⟩ := hne
        have hjneg : A i j = -A a₀ j := (hcoord i a₀ j).resolve_left hj
        intro k
        rcases hcoord i a₀ k with hk | hk
        · exact False.elim (hn' i a₀ ⟨⟨k, hk⟩, ⟨j, hjneg⟩⟩)
        · exact hk
    let c : Fin q → ZMod p := fun i =>
      if ∀ j : Fin q, A i j = A a₀ j then 1 else -1
    have hAe : A = Matrix.vecMulVec c (A a₀) := by
      ext i j
      by_cases hi : ∀ j : Fin q, A i j = A a₀ j
      · simp [c, Matrix.vecMulVec, hi, hi j]
      · have hineg := (hrows i).resolve_left hi
        simp [c, Matrix.vecMulVec, hi, hineg j]
    have hle := Matrix.rank_vecMulVec_le c (A a₀)
    rw [hAe] at hrank
    omega
  obtain ⟨a, b, ⟨je, hje⟩, jd, hjd⟩ := hpair
  have hpgt : 2 < p := by
    have hpge := (Fact.out : Nat.Prime p).two_le
    omega
  letI : Fact (2 < p) := ⟨hpgt⟩
  intro v
  have hab : a ≠ b := by
    intro hab
    subst b
    rcases hA a jd with hj | hj
    · have hne : (1 : ZMod p) ≠ -1 := Ne.symm ZMod.neg_one_ne_one
      exact hne (by simpa [hj] using hjd)
    · exact ZMod.neg_one_ne_one (by simpa [hj] using hjd)
  let S : Matrix (Fin q) (Fin q) ℝ :=
    fun i j => if A i j = 1 then 1 else -1
  change (∑ i : Fin q, (∑ j : Fin q, S i j * v j) ^ 2) ≤
    ((q : ℝ) ^ 2 - 2) * ∑ j : Fin q, (v j) ^ 2
  have hSsign (i j : Fin q) : S i j = 1 ∨ S i j = -1 := by
    simp only [S]
    split_ifs <;> simp
  have hSsq (i j : Fin q) : (S i j) ^ 2 = 1 := by
    rcases hSsign i j with h | h <;> rw [h] <;> norm_num
  have hSe : S a je = S b je := by
    simp only [S]
    rw [hje]
  have hSd : S a jd = -S b jd := by
    rcases hA a jd with ha | ha <;> rcases hA b jd with hb | hb
    · exfalso
      have hne : (1 : ZMod p) ≠ -1 := Ne.symm ZMod.neg_one_ne_one
      exact hne (by simpa [ha, hb] using hjd)
    · simp [S, ha, hb, ZMod.neg_one_ne_one]
    · simp [S, ha, hb, ZMod.neg_one_ne_one]
    · exfalso
      exact ZMod.neg_one_ne_one (by simpa [ha, hb] using hjd)
  let E : Finset (Fin q) := Finset.univ.filter fun j => S a j = S b j
  let D : Finset (Fin q) := Finset.univ \ E
  have hjeE : je ∈ E := by
    simp [E, hSe]
  have hjdnot : S a jd ≠ S b jd := by
    intro heq
    rcases hSsign b jd with hb | hb <;> rw [hb] at heq hSd <;>
      norm_num at heq hSd <;> linarith
  have hjdD : jd ∈ D := by
    simp [D, E, hjdnot]
  have hEcard : E.card ≤ q - 1 := by
    have hproper : E ⊂ (Finset.univ : Finset (Fin q)) := by
      refine ⟨Finset.subset_univ E, ?_⟩
      intro h
      have hjmem : jd ∈ E := h (Finset.mem_univ jd)
      exact hjdnot (by simpa [E] using hjmem)
    have hc := Finset.card_lt_card hproper
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  have hDcard : D.card ≤ q - 1 := by
    have hproper : D ⊂ (Finset.univ : Finset (Fin q)) := by
      refine ⟨Finset.subset_univ D, ?_⟩
      intro h
      have hnot : je ∉ D := by simp [D, hjeE]
      exact hnot (h (Finset.mem_univ je))
    have hc := Finset.card_lt_card hproper
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  have hEqOnE (j : Fin q) (hj : j ∈ E) : S b j = S a j := by
    have h := (by simpa [E] using hj : S a j = S b j)
    exact h.symm
  have hNegOnD (j : Fin q) (hj : j ∈ D) : S b j = -S a j := by
    have hnot : S a j ≠ S b j := by
      simpa [D, E] using hj
    rcases hSsign a j with ha | ha <;> rcases hSsign b j with hb | hb <;>
      simp [ha, hb] at hnot ⊢
  have hED : E ∪ D = (Finset.univ : Finset (Fin q)) := by
    simp [D]
  have hdis : Disjoint E D := by
    simpa [D] using (Finset.disjoint_sdiff : Disjoint E
      ((Finset.univ : Finset (Fin q)) \ E))
  have hsplit (f : Fin q → ℝ) :
      (∑ j : Fin q, f j) = (∑ j ∈ E, f j) + ∑ j ∈ D, f j := by
    rw [← hED, Finset.sum_union hdis]
  let u : ℝ := ∑ j ∈ E, S a j * v j
  let d : ℝ := ∑ j ∈ D, S a j * v j
  have hFa : (∑ j : Fin q, S a j * v j) = u + d := by
    simpa [u, d] using hsplit (fun j => S a j * v j)
  have hFb : (∑ j : Fin q, S b j * v j) = u - d := by
    rw [hsplit]
    have hE :
        (∑ j ∈ E, S b j * v j) = ∑ j ∈ E, S a j * v j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hEqOnE j hj]
    have hD :
        (∑ j ∈ D, S b j * v j) = -(∑ j ∈ D, S a j * v j) := by
      calc
        (∑ j ∈ D, S b j * v j) = ∑ j ∈ D, -(S a j * v j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hNegOnD j hj]
          ring
        _ = -(∑ j ∈ D, S a j * v j) := by
          rw [Finset.sum_neg_distrib]
    rw [hE, hD]
    rfl
  have hu :
      u ^ 2 ≤ (E.card : ℝ) * ∑ j ∈ E, (v j) ^ 2 := by
    have hc :=
      Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) E (fun j => S a j) v
    simp_rw [hSsq] at hc
    simpa [u] using hc
  have hd :
      d ^ 2 ≤ (D.card : ℝ) * ∑ j ∈ D, (v j) ^ 2 := by
    have hc :=
      Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) D (fun j => S a j) v
    simp_rw [hSsq] at hc
    simpa [d] using hc
  have hEcardR : (E.card : ℝ) ≤ (q : ℝ) - 1 := by
    have hc : (E.card : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by
      exact_mod_cast hEcard
    simpa [Nat.cast_sub (by omega : 1 ≤ q)] using hc
  have hDcardR : (D.card : ℝ) ≤ (q : ℝ) - 1 := by
    have hc : (D.card : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by
      exact_mod_cast hDcard
    simpa [Nat.cast_sub (by omega : 1 ≤ q)] using hc
  have hu' :
      u ^ 2 ≤ ((q : ℝ) - 1) * ∑ j ∈ E, (v j) ^ 2 :=
    hu.trans (mul_le_mul_of_nonneg_right hEcardR
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hd' :
      d ^ 2 ≤ ((q : ℝ) - 1) * ∑ j ∈ D, (v j) ^ 2 :=
    hd.trans (mul_le_mul_of_nonneg_right hDcardR
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hvsplit :
      (∑ j : Fin q, (v j) ^ 2) =
        (∑ j ∈ E, (v j) ^ 2) + ∑ j ∈ D, (v j) ^ 2 :=
    hsplit (fun j => (v j) ^ 2)
  have habbound :
      (∑ j : Fin q, S a j * v j) ^ 2 +
          (∑ j : Fin q, S b j * v j) ^ 2 ≤
        (2 * ((q : ℝ) - 1)) * ∑ j : Fin q, (v j) ^ 2 := by
    rw [hFa, hFb, hvsplit]
    nlinarith
  let V : ℝ := ∑ j : Fin q, (v j) ^ 2
  let F : Fin q → ℝ := fun i => (∑ j : Fin q, S i j * v j) ^ 2
  have hrow (i : Fin q) : F i ≤ (q : ℝ) * V := by
    have hc :=
      Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) (Finset.univ : Finset (Fin q))
        (fun j => S i j) v
    simp_rw [hSsq] at hc
    simpa [F, V] using hc
  have hpairF : F a + F b ≤ 2 * ((q : ℝ) - 1) * V := by
    simpa [F, V] using habbound
  let R : Finset (Fin q) := (Finset.univ.erase a).erase b
  have hbmem : b ∈ (Finset.univ.erase a : Finset (Fin q)) := by
    simp [hab.symm]
  have hrowsplit :
      (∑ i : Fin q, F i) = F a + F b + ∑ i ∈ R, F i := by
    have haerase := Finset.sum_erase_add (Finset.univ : Finset (Fin q)) F
      (Finset.mem_univ a)
    have hberase := Finset.sum_erase_add (Finset.univ.erase a) F hbmem
    dsimp only [R]
    linarith
  have hRcard : R.card = q - 2 := by
    dsimp only [R]
    rw [Finset.card_erase_of_mem hbmem]
    rw [Finset.card_erase_of_mem (Finset.mem_univ a)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hRbound :
      (∑ i ∈ R, F i) ≤ ((q : ℝ) - 2) * (q : ℝ) * V := by
    calc
      (∑ i ∈ R, F i) ≤ ∑ i ∈ R, (q : ℝ) * V := by
        gcongr with i hi
        exact hrow i
      _ = (R.card : ℝ) * ((q : ℝ) * V) := by
        simp
      _ = ((q : ℝ) - 2) * (q : ℝ) * V := by
        rw [hRcard]
        push_cast
        rw [Nat.cast_sub hq]
        ring
  have hV : 0 ≤ V := Finset.sum_nonneg fun _ _ => sq_nonneg _
  change (∑ i : Fin q, F i) ≤ ((q : ℝ) ^ 2 - 2) * V
  rw [hrowsplit]
  nlinarith

@[blueprint "lem:matrix-distinct-rows-le-pow-rank"
  (statement := /-- Let $p$ be prime, let $I$ and $J$ be finite index types, and let $L\in\mathbb F_p^{I\times J}$. If $\operatorname{rank}(L)\le r$, then $L$ has at most $p^r$ distinct rows. -/)
  (proof := /-- Every row belongs to the subspace spanned by the rows of $L$. The dimension of this subspace is the matrix rank, and a vector space of dimension $d$ over $\mathbb F_p$ has exactly $p^d$ elements. Hence the image of the row map has cardinality at most $p^{\operatorname{rank}(L)}\le p^r$. -/)
  (title := /-- Number of distinct rows of a finite-field matrix -/)
  (latexEnv := "lemma")]
lemma matrix_distinct_rows_le_pow_rank
    (p r : ℕ) [Fact p.Prime]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : Matrix ι κ (ZMod p)) (hr : Matrix.rank L ≤ r) :
    (Finset.univ.image L.row).card ≤ p ^ r := by
  classical
  let W := Submodule.span (ZMod p) (Set.range L.row)
  let rowsW : Finset W := Finset.univ.image fun i =>
    ⟨L.row i, Submodule.subset_span (Set.mem_range_self i)⟩
  have himage : rowsW.image Subtype.val = Finset.univ.image L.row := by
    ext w
    simp [rowsW]
  have hrowscard :
      (Finset.univ.image L.row).card = rowsW.card := by
    rw [← himage, Finset.card_image_of_injective rowsW Subtype.val_injective]
  have hdim : Module.finrank (ZMod p) W = Matrix.rank L := by
    simpa [W] using (Matrix.rank_eq_finrank_span_row L).symm
  calc
    (Finset.univ.image L.row).card = rowsW.card := hrowscard
    _ ≤ Fintype.card W := Finset.card_le_univ rowsW
    _ = p ^ Module.finrank (ZMod p) W := by
      simpa using
        (Module.card_fintype (Module.finBasis (R := ZMod p) (M := W)))
    _ = p ^ Matrix.rank L := by rw [hdim]
    _ ≤ p ^ r := Nat.pow_le_pow_right ((Fact.out : Nat.Prime p).pos) hr

@[blueprint "lem:zmod-sign-product"
  (statement := /-- Let $p>2$ be prime and let $(f_i)_{i\in I}$ be a finite family in $\mathbb F_p$ whose entries all belong to $\{-1,1\}$. Mapping $1$ to the real number $1$ and $-1$ to the real number $-1$ commutes with the finite product of the family. -/)
  (proof := /-- The two-element set $\{-1,1\}$ is closed under multiplication. Since $p>2$, its two elements are distinct, so the real sign assigned to a product of two signs is the product of their assigned real signs. Induction over the finite index set, starting from the empty product, proves the claim. -/)
  (title := /-- Real signs commute with products of odd-characteristic field signs -/)
  (latexEnv := "lemma")]
lemma zmod_sign_product
    (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    {ι : Type*} [Fintype ι] (f : ι → ZMod p)
    (hf : ∀ i, f i = 1 ∨ f i = -1) :
    (if (∏ i : ι, f i) = 1 then (1 : ℝ) else -1) =
      ∏ i : ι, (if f i = 1 then (1 : ℝ) else -1) := by
  classical
  letI : Fact (2 < p) := ⟨hp⟩
  let s : ZMod p → ℝ := fun x => if x = 1 then 1 else -1
  have hmul (x y : ZMod p) (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
      s (x * y) = s x * s y := by
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      simp [s, hx, hy, ZMod.neg_one_ne_one]
  have hs (t : Finset ι) :
      ((∏ i ∈ t, f i) = 1 ∨ (∏ i ∈ t, f i) = -1) ∧
        s (∏ i ∈ t, f i) = ∏ i ∈ t, s (f i) := by
    induction t using Finset.induction_on with
    | empty =>
        simp [s]
    | @insert a t ha ih =>
        rcases ih with ⟨ihsign, ihprod⟩
        constructor
        · rcases hf a with hfa | hfa <;> rcases ihsign with ht | ht <;>
            simp [Finset.prod_insert, ha, hfa, ht]
        · rw [Finset.prod_insert ha, Finset.prod_insert ha]
          rw [hmul _ _ (hf a) ihsign, ihprod]
  simpa [s] using (hs Finset.univ).2

@[blueprint "lem:prime-power-contraction-constants"
  (statement := /-- Let $p\ge2$ be a prime and let $\delta\in(0,1)$. There exist real constants $c_1>0$ and $c_2\in(0,1)$ such that, for every $n\in\mathbb N$,
  \[
    p^{\lfloor c_1n\rfloor}\delta^n\le c_2^{2n}.
  \] -/)
  (proof := /-- Put $c_2=(1+\delta)/2$ and $\alpha=\delta/c_2^2$. The inequalities $0<\delta<1$ imply $0<c_2<1$ and $0<\alpha<1$. Choose a positive integer $K$ such that $p\alpha^K<1$, and put $c_1=K^{-1}$. If $m=\lfloor c_1n\rfloor$, then $Km\le n$. Antitonicity of the powers of $\alpha$ and the choice of $K$ give
  \[
    p^m\alpha^n\le p^m\alpha^{Km}
      =(p\alpha^K)^m\le1.
  \]
  Since $\delta=c_2^2\alpha$, multiplication by $c_2^{2n}$ yields
  $p^{\lfloor c_1n\rfloor}\delta^n\le c_2^{2n}$. -/)
  (title := /-- Constants absorbing a low-rank row-count factor -/)
  (latexEnv := "lemma")]
lemma prime_power_contraction_constants
    (p : ℕ) [Fact p.Prime] (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ c₂ < 1 ∧
      ∀ n : ℕ,
        (p : ℝ) ^ ⌊c₁ * (n : ℝ)⌋₊ * δ ^ n ≤ c₂ ^ (2 * n) := by
  have hpR : (1 : ℝ) < p := by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  let c₂ := (1 + δ) / 2
  have hc₂ : 0 < c₂ := by
    dsimp only [c₂]
    linarith
  have hc₂lt : c₂ < 1 := by
    dsimp only [c₂]
    linarith
  have hδc₂sq : δ < c₂ ^ 2 := by
    have hsq : 0 < (1 - δ) ^ 2 := sq_pos_of_pos (sub_pos.mpr hδ1)
    dsimp only [c₂]
    nlinarith
  let α := δ / c₂ ^ 2
  have hα0 : 0 < α := div_pos hδ0 (sq_pos_of_pos hc₂)
  have hα1 : α < 1 := by
    dsimp only [α]
    rw [div_lt_one (sq_pos_of_pos hc₂)]
    exact hδc₂sq
  have hp0 : 0 < (p : ℝ) := lt_trans zero_lt_one hpR
  have hp_inv_lt_one : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).2 hpR
  obtain ⟨k, hkpow, _⟩ :=
    exists_nat_pow_near_of_lt_one (inv_pos.mpr hp0) hp_inv_lt_one.le hα0 hα1
  let K := k + 1
  have hKpow : α ^ K < (p : ℝ)⁻¹ := by
    simpa [K] using hkpow
  have hK : 0 < K := by
    simp [K]
  have hblock : (p : ℝ) * α ^ K ≤ 1 := by
    apply le_of_lt
    calc
      (p : ℝ) * α ^ K < (p : ℝ) * (p : ℝ)⁻¹ :=
        mul_lt_mul_of_pos_left hKpow hp0
      _ = 1 := mul_inv_cancel₀ hp0.ne'
  let c₁ := ((K : ℝ))⁻¹
  have hc₁ : 0 < c₁ := inv_pos.mpr (by exact_mod_cast hK)
  have hδα : c₂ ^ 2 * α = δ := by
    dsimp only [α]
    field_simp
  refine ⟨c₁, c₂, hc₁, hc₂, hc₂lt, ?_⟩
  intro n
  let m := ⌊c₁ * (n : ℝ)⌋₊
  have hfloor : (m : ℝ) ≤ c₁ * (n : ℝ) :=
    Nat.floor_le (mul_nonneg hc₁.le (Nat.cast_nonneg n))
  have hKmR : (K : ℝ) * (m : ℝ) ≤ (n : ℝ) := by
    calc
      (K : ℝ) * (m : ℝ) ≤ (K : ℝ) * (c₁ * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg K)
      _ = (n : ℝ) := by
        dsimp only [c₁]
        field_simp
  have hKm : K * m ≤ n := by
    exact_mod_cast hKmR
  have hαpow : α ^ n ≤ α ^ (K * m) :=
    pow_le_pow_of_le_one hα0.le hα1.le hKm
  have hfactor : (p : ℝ) ^ m * α ^ n ≤ 1 := by
    calc
      (p : ℝ) ^ m * α ^ n ≤ (p : ℝ) ^ m * α ^ (K * m) :=
        mul_le_mul_of_nonneg_left hαpow (pow_nonneg hp0.le m)
      _ = (p : ℝ) ^ m * (α ^ K) ^ m := by rw [pow_mul]
      _ = ((p : ℝ) * α ^ K) ^ m := (mul_pow (p : ℝ) (α ^ K) m).symm
      _ ≤ 1 := pow_le_one₀ (mul_nonneg hp0.le (pow_nonneg hα0.le K)) hblock
  calc
    (p : ℝ) ^ ⌊c₁ * (n : ℝ)⌋₊ * δ ^ n
        = c₂ ^ (2 * n) * ((p : ℝ) ^ m * α ^ n) := by
          dsimp only [m]
          rw [← hδα, mul_pow, pow_mul]
          ring
    _ ≤ c₂ ^ (2 * n) * 1 :=
      mul_le_mul_of_nonneg_left hfactor (pow_nonneg hc₂.le (2 * n))
    _ = c₂ ^ (2 * n) := mul_one _

@[blueprint "lem:boolean-disagreement-correlation-identity"
  (statement := /-- For two matrices $M,L$ over $\mathbb Z/p\mathbb Z$, assign the real sign $1$ to an entry equal to $1$ and $-1$ to every other entry. Their total signed correlation equals the number of matrix positions minus twice their Boolean disagreement count. -/)
  (proof := /-- At each matrix position, the two Booleanizations agree exactly when the corresponding real signs agree. Thus the product of the signs is $1$ at an agreement and $-1$ at a disagreement, equivalently one minus twice the disagreement indicator. Summing this pointwise identity over the finite product of the row and column index sets gives the formula, using \cref{def:booleanize, def:boolean-disagreement-count}. -/)
  (title := /-- Boolean disagreements as signed correlation -/)
  (latexEnv := "lemma")]
lemma boolean_disagreement_correlation_identity
    (p : ℕ) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M L : Matrix ι κ (ZMod p)) :
    (∑ i : ι, ∑ j : κ,
      (if M i j = 1 then (1 : ℝ) else -1) *
        (if L i j = 1 then (1 : ℝ) else -1)) =
      (Fintype.card ι : ℝ) * Fintype.card κ -
        2 * (boolean_disagreement_count M L : ℝ) := by
  classical
  let d : ι × κ → Prop := fun ij =>
    booleanize (M ij.1 ij.2) ≠ booleanize (L ij.1 ij.2)
  have hd :
      (boolean_disagreement_count M L : ℝ) =
        ∑ ij : ι × κ, if d ij then (1 : ℝ) else 0 := by
    simpa [boolean_disagreement_count, d] using
      (Finset.natCast_card_filter (R := ℝ) d (Finset.univ : Finset (ι × κ)))
  rw [hd]
  calc
    (∑ i : ι, ∑ j : κ,
        (if M i j = 1 then (1 : ℝ) else -1) *
          (if L i j = 1 then (1 : ℝ) else -1)) =
        ∑ ij : ι × κ,
        (if M ij.1 ij.2 = 1 then (1 : ℝ) else -1) *
          (if L ij.1 ij.2 = 1 then (1 : ℝ) else -1) :=
            (Fintype.sum_prod_type
              (fun ij : ι × κ =>
                (if M ij.1 ij.2 = 1 then (1 : ℝ) else -1) *
                  (if L ij.1 ij.2 = 1 then (1 : ℝ) else -1))).symm
    _ =
        ∑ ij : ι × κ, (1 - 2 * if d ij then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro ij _
          by_cases hM : M ij.1 ij.2 = 1 <;>
            by_cases hL : L ij.1 ij.2 = 1 <;>
            simp [d, booleanize, hM, hL] <;> norm_num
    _ = (Fintype.card ι : ℝ) * Fintype.card κ -
          2 * ∑ ij : ι × κ, if d ij then (1 : ℝ) else 0 := by
            simp [Finset.sum_sub_distrib, Finset.mul_sum]

@[blueprint "lem:kronecker-candidate-correlation-square-bound"
  (statement := /-- Let $S$ be a real $q\times q$ kernel whose squared operator estimate has factor $\beta\ge0$. For a matrix $L$ over $\mathbb F_p$, indexed by words of length $n$ and having rank at most $r$, the squared correlation between $S^{\otimes n}$ and the real sign interpretation of $L$ is at most
  \[
    q^{2n}p^r\beta^n.
  \] -/)
  (proof := /-- Group the row indices according to their row of $L$. By \cref{lem:matrix-distinct-rows-le-pow-rank}, the set of distinct rows has cardinality at most $p^r$. For each distinct row $w$, let $e_w$ be the indicator of its row class and let $g_w$ be its real sign interpretation. Expressing the correlation as the sum of the products of $e_w$ with $S^{\otimes n}g_w$, Cauchy--Schwarz bounds its square by
  \[
    \Bigl(\sum_w\lVert e_w\rVert_2^2\Bigr)
    \Bigl(\sum_w\lVert S^{\otimes n}g_w\rVert_2^2\Bigr).
  \]
  The row classes partition the $q^n$ indices, so the first factor is $q^n$. Every $g_w$ has squared norm $q^n$, and \cref{lem:tensor-kernel-sum-square-bound} bounds each corresponding term in the second factor by $\beta^nq^n$. Multiplication and the bound on the number of rows give the claim. -/)
  (title := /-- Correlation bound from tensor contraction and few rows -/)
  (latexEnv := "lemma")]
lemma kronecker_candidate_correlation_square_bound
    (p q n r : ℕ) [Fact p.Prime]
    (S : Matrix (Fin q) (Fin q) ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hS : ∀ v : Fin q → ℝ,
      (∑ i : Fin q, (∑ j : Fin q, S i j * v j) ^ 2) ≤
        β * ∑ j : Fin q, (v j) ^ 2)
    (L : Matrix (Fin n → Fin q) (Fin n → Fin q) (ZMod p))
    (hr : Matrix.rank L ≤ r) :
    (∑ x : Fin n → Fin q, ∑ y : Fin n → Fin q,
      (∏ t : Fin n, S (x t) (y t)) *
        (if L x y = 1 then (1 : ℝ) else -1)) ^ 2 ≤
      (q : ℝ) ^ (2 * n) * (p : ℝ) ^ r * β ^ n := by
  classical
  let rows : Finset ((Fin n → Fin q) → ZMod p) :=
    Finset.univ.image L.row
  let P : Finset (((Fin n → Fin q) → ZMod p) × (Fin n → Fin q)) :=
    rows.product Finset.univ
  let g : ((Fin n → Fin q) → ZMod p) → (Fin n → Fin q) → ℝ :=
    fun w y => if w y = 1 then 1 else -1
  let e : (((Fin n → Fin q) → ZMod p) × (Fin n → Fin q)) → ℝ :=
    fun wx => if L.row wx.2 = wx.1 then 1 else 0
  let h : (((Fin n → Fin q) → ZMod p) × (Fin n → Fin q)) → ℝ :=
    fun wx => ∑ y : Fin n → Fin q,
      (∏ t : Fin n, S (wx.2 t) (y t)) * g wx.1 y
  have hrow (x : Fin n → Fin q) : L.row x ∈ rows := by
    simp [rows]
  have hesum (x : Fin n → Fin q) :
      (∑ w ∈ rows, e (w, x) ^ 2) = 1 := by
    simp [e, hrow x]
  have he :
      (∑ wx ∈ P, e wx ^ 2) = (q : ℝ) ^ n := by
    calc
      (∑ wx ∈ P, e wx ^ 2) =
          ∑ w ∈ rows, ∑ x : Fin n → Fin q, e (w, x) ^ 2 := by
            simpa [P] using
              (Finset.sum_product rows (Finset.univ : Finset (Fin n → Fin q))
                (fun wx => e wx ^ 2))
      _ = ∑ x : Fin n → Fin q, ∑ w ∈ rows, e (w, x) ^ 2 := by
            rw [Finset.sum_comm]
      _ = ∑ _x : Fin n → Fin q, (1 : ℝ) := by
            simp_rw [hesum]
      _ = (q : ℝ) ^ n := by
            simp
  have hgsq (w : (Fin n → Fin q) → ZMod p) :
      (∑ y : Fin n → Fin q, (g w y) ^ 2) = (q : ℝ) ^ n := by
    simp [g]
  have hhrow (w : (Fin n → Fin q) → ZMod p) :
      (∑ x : Fin n → Fin q, h (w, x) ^ 2) ≤
        β ^ n * (q : ℝ) ^ n := by
    simpa [h, hgsq w] using
      tensor_kernel_sum_square_bound q S β hβ hS n (g w)
  have hrowscard : rows.card ≤ p ^ r := by
    simpa [rows] using matrix_distinct_rows_le_pow_rank p r L hr
  have hh :
      (∑ wx ∈ P, h wx ^ 2) ≤ (p : ℝ) ^ r * (β ^ n * (q : ℝ) ^ n) := by
    calc
      (∑ wx ∈ P, h wx ^ 2) =
          ∑ w ∈ rows, ∑ x : Fin n → Fin q, h (w, x) ^ 2 := by
            simpa [P] using
              (Finset.sum_product rows (Finset.univ : Finset (Fin n → Fin q))
                (fun wx => h wx ^ 2))
      _ ≤ ∑ _w ∈ rows, β ^ n * (q : ℝ) ^ n := by
            gcongr with w hw
            exact hhrow w
      _ = (rows.card : ℝ) * (β ^ n * (q : ℝ) ^ n) := by
            simp
      _ ≤ (p : ℝ) ^ r * (β ^ n * (q : ℝ) ^ n) := by
            gcongr
            exact_mod_cast hrowscard
  have hcorr :
      (∑ x : Fin n → Fin q, ∑ y : Fin n → Fin q,
        (∏ t : Fin n, S (x t) (y t)) *
          (if L x y = 1 then (1 : ℝ) else -1)) =
        ∑ wx ∈ P, e wx * h wx := by
    calc
      (∑ x : Fin n → Fin q, ∑ y : Fin n → Fin q,
          (∏ t : Fin n, S (x t) (y t)) *
            (if L x y = 1 then (1 : ℝ) else -1)) =
          ∑ x : Fin n → Fin q, h (L.row x, x) := by
            apply Finset.sum_congr rfl
            intro x _
            rfl
      _ = ∑ x : Fin n → Fin q, ∑ w ∈ rows, e (w, x) * h (w, x) := by
            apply Finset.sum_congr rfl
            intro x _
            simp [e, hrow x]
      _ = ∑ w ∈ rows, ∑ x : Fin n → Fin q, e (w, x) * h (w, x) := by
            rw [Finset.sum_comm]
      _ = ∑ wx ∈ P, e wx * h wx := by
            simpa [P] using
              (Finset.sum_product rows (Finset.univ : Finset (Fin n → Fin q))
                (fun wx => e wx * h wx)).symm
  rw [hcorr]
  calc
    (∑ wx ∈ P, e wx * h wx) ^ 2 ≤
        (∑ wx ∈ P, e wx ^ 2) * ∑ wx ∈ P, h wx ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) P e h
    _ = (q : ℝ) ^ n * ∑ wx ∈ P, h wx ^ 2 := by rw [he]
    _ ≤ (q : ℝ) ^ n * ((p : ℝ) ^ r * (β ^ n * (q : ℝ) ^ n)) :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg (Nat.cast_nonneg q) n)
    _ = (q : ℝ) ^ (2 * n) * (p : ℝ) ^ r * β ^ n := by
      rw [show 2 * n = n + n by omega, pow_add]
      ring

@[blueprint "thm:kronecker-power-boolean-rigidity-lower-bound"
  (statement := /-- Let $p$ be a prime number, let $q\in\mathbb{N}$, and let $A\in\{-1,1\}^{q\times q}\subseteq\mathbb{F}_p^{q\times q}$ have rank greater than $1$ over $\mathbb{F}_p$. Then there exist real constants $c_1>0$ and $c_2\in(0,1)$ such that, for every positive integer $n$, the $n$-fold Kronecker power of $A$ satisfies
  \[
    \operatorname{Rig}^{\mathrm{bool}}_{A^{\otimes n}}\!\left(\left\lfloor c_1n\right\rfloor\right)
      \ge q^{2n}\left(\frac12-c_2^n\right).
  \]
  Here the floor makes explicit the integral rank threshold implicit in the expression $c_1n$. -/)
  (proof := /-- The rank bound by the number of columns gives $q\ge2$. Moreover $p\ne2$: if $p=2$, then $1=-1$, so \cref{def:is-sign-matrix} makes $A$ an outer product of two all-ones vectors, contradicting the rank hypothesis. Hence $p>2$.

  Let $S_{ij}=1$ when $A_{ij}=1$ and $S_{ij}=-1$ otherwise, and put
  \[
    \beta=q^2-2,\qquad \delta=\frac{\beta}{q^2}.
  \]
  By \cref{lem:sign-matrix-base-sum-square-bound}, one has $0<\beta<q^2$ and the one-step squared-norm estimate for $S$ with factor $\beta$. Thus $0<\delta<1$. Apply \cref{lem:prime-power-contraction-constants} to obtain $c_1>0$ and $0<c_2<1$ such that
  \[
    p^{\lfloor c_1n\rfloor}\delta^n\le c_2^{2n}
  \]
  for every natural number $n$.

  Fix $n>0$, write $r=\lfloor c_1n\rfloor$, and choose a rank-minimizing matrix $L$ in the definition of \cref{def:boolean-rigidity}. Let $C$ be the total correlation between the real sign interpretations of $A^{\otimes n}$ and $L$. Since $p>2$, \cref{lem:zmod-sign-product} and \cref{def:kronecker-power} identify the first of these sign matrices with $S^{\otimes n}$. Therefore \cref{lem:kronecker-candidate-correlation-square-bound} gives
  \[
    C^2\le q^{2n}p^r\beta^n
      =q^{4n}p^r\delta^n
      \le \bigl(q^{2n}c_2^n\bigr)^2.
  \]
  The right-hand side has a nonnegative square root, so $C\le q^{2n}c_2^n$.

  By \cref{lem:boolean-disagreement-correlation-identity}, if $d$ is the Boolean disagreement count between $A^{\otimes n}$ and $L$, then
  \[
    C=q^{2n}-2d.
  \]
  Consequently
  \[
    d\ge q^{2n}\left(\frac12-\frac12c_2^n\right)
      \ge q^{2n}\left(\frac12-c_2^n\right).
  \]
  Since $L$ realizes the minimum in \cref{def:boolean-rigidity}, this is the required rigidity bound. -/)
  (title := /-- Boolean rigidity lower bound for Kronecker powers -/)
  (latexEnv := "theorem")]
theorem kronecker_power_boolean_rigidity_lower_bound
    (p q : ℕ) [Fact p.Prime]
    (A : Matrix (Fin q) (Fin q) (ZMod p))
    (hA : is_sign_matrix A) (hrank : 1 < Matrix.rank A) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ c₂ < 1 ∧
      ∀ n : ℕ, 0 < n →
        (q : ℝ) ^ (2 * n) * ((1 / 2 : ℝ) - c₂ ^ n) ≤
          (boolean_rigidity (kronecker_power A n) ⌊c₁ * (n : ℝ)⌋₊ : ℝ) := by
  classical
  have hq : 2 ≤ q := by
    have h := Matrix.rank_le_card_width A
    simp only [Fintype.card_fin] at h
    omega
  have hpne : p ≠ 2 := by
    intro hp
    subst p
    simp only [is_sign_matrix] at hA
    have hAe :
        A = Matrix.vecMulVec (fun _ : Fin q => (1 : ZMod 2))
          (fun _ : Fin q => 1) := by
      ext i j
      rcases hA i j with hij | hij
      · simpa [Matrix.vecMulVec] using hij
      · have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
        have hm : (-1 : ZMod 2) = 1 := by
          calc
            (-1 : ZMod 2) = 1 - 2 := by ring
            _ = 1 := by rw [htwo]; ring
        simpa [Matrix.vecMulVec, hm] using hij
    have hle :=
      Matrix.rank_vecMulVec_le (fun _ : Fin q => (1 : ZMod 2))
        (fun _ : Fin q => 1)
    rw [hAe] at hrank
    omega
  have hp : 2 < p := by
    have hpge := (Fact.out : Nat.Prime p).two_le
    omega
  let S : Matrix (Fin q) (Fin q) ℝ :=
    fun i j => if A i j = 1 then 1 else -1
  let β : ℝ := (q : ℝ) ^ 2 - 2
  have hbase :
      0 ≤ β ∧ β < (q : ℝ) ^ 2 ∧
        ∀ v : Fin q → ℝ,
          (∑ i : Fin q, (∑ j : Fin q, S i j * v j) ^ 2) ≤
            β * ∑ j : Fin q, (v j) ^ 2 := by
    simpa [S, β] using sign_matrix_base_sum_square_bound p q A hA hrank
  obtain ⟨hβ0, hβlt, hS⟩ := hbase
  have hqR : (2 : ℝ) ≤ q := by
    exact_mod_cast hq
  have hq2pos : 0 < (q : ℝ) ^ 2 := by positivity
  have hβpos : 0 < β := by
    dsimp only [β]
    nlinarith [sq_nonneg (q : ℝ)]
  let δ : ℝ := β / (q : ℝ) ^ 2
  have hδ0 : 0 < δ := div_pos hβpos hq2pos
  have hδ1 : δ < 1 := by
    dsimp only [δ]
    rwa [div_lt_one hq2pos]
  obtain ⟨c₁, c₂, hc₁, hc₂, hc₂lt, hconstants⟩ :=
    prime_power_contraction_constants p δ hδ0 hδ1
  refine ⟨c₁, c₂, hc₁, hc₂, hc₂lt, ?_⟩
  intro n hn
  let M := kronecker_power A n
  let r := ⌊c₁ * (n : ℝ)⌋₊
  have hset :
      {s : ℕ | ∃ L : Matrix (Fin n → Fin q) (Fin n → Fin q) (ZMod p),
        Matrix.rank L ≤ r ∧ boolean_disagreement_count M L = s}.Nonempty := by
    refine ⟨boolean_disagreement_count M 0, 0, ?_, rfl⟩
    simp
  change
    (q : ℝ) ^ (2 * n) * ((1 / 2 : ℝ) - c₂ ^ n) ≤
      (sInf {s : ℕ |
        ∃ L : Matrix (Fin n → Fin q) (Fin n → Fin q) (ZMod p),
          Matrix.rank L ≤ r ∧ boolean_disagreement_count M L = s} : ℕ)
  obtain ⟨L, hLrank, hLcount⟩ := Nat.sInf_mem hset
  rw [← hLcount]
  let C : ℝ :=
    ∑ x : Fin n → Fin q, ∑ y : Fin n → Fin q,
      (if M x y = 1 then (1 : ℝ) else -1) *
        (if L x y = 1 then (1 : ℝ) else -1)
  have hCkernel :
      C = ∑ x : Fin n → Fin q, ∑ y : Fin n → Fin q,
        (∏ t : Fin n, S (x t) (y t)) *
          (if L x y = 1 then (1 : ℝ) else -1) := by
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    have hz :=
      zmod_sign_product p hp (fun t : Fin n => A (x t) (y t))
        (fun t => hA (x t) (y t))
    dsimp only [C, M, S, kronecker_power, Matrix.of_apply]
    exact congrArg
      (fun z : ℝ => z * (if L x y = 1 then (1 : ℝ) else -1)) hz
  have hCsq :
      C ^ 2 ≤ (q : ℝ) ^ (2 * n) * (p : ℝ) ^ r * β ^ n := by
    rw [hCkernel]
    exact kronecker_candidate_correlation_square_bound
      p q n r S β hβ0 hS L hLrank
  have hβδ : β = (q : ℝ) ^ 2 * δ := by
    dsimp only [δ]
    field_simp
  have hcontract : (p : ℝ) ^ r * δ ^ n ≤ c₂ ^ (2 * n) := by
    exact hconstants n
  have hCsq' :
      C ^ 2 ≤ ((q : ℝ) ^ (2 * n) * c₂ ^ n) ^ 2 := by
    calc
      C ^ 2 ≤ (q : ℝ) ^ (2 * n) * (p : ℝ) ^ r * β ^ n := hCsq
      _ = ((q : ℝ) ^ (2 * n)) ^ 2 *
          ((p : ℝ) ^ r * δ ^ n) := by
            rw [hβδ, mul_pow]
            rw [show 2 * n = n + n by omega, pow_add]
            ring
      _ ≤ ((q : ℝ) ^ (2 * n)) ^ 2 * c₂ ^ (2 * n) :=
        mul_le_mul_of_nonneg_left hcontract
          (sq_nonneg ((q : ℝ) ^ (2 * n)))
      _ = ((q : ℝ) ^ (2 * n) * c₂ ^ n) ^ 2 := by
            rw [show 2 * n = n + n by omega, pow_add]
            ring
  have hC :
      C ≤ (q : ℝ) ^ (2 * n) * c₂ ^ n := by
    have hright : 0 ≤ (q : ℝ) ^ (2 * n) * c₂ ^ n :=
      mul_nonneg (pow_nonneg (Nat.cast_nonneg q) (2 * n))
        (pow_nonneg hc₂.le n)
    nlinarith [sq_nonneg (C + (q : ℝ) ^ (2 * n) * c₂ ^ n)]
  have hCid :
      C = (q : ℝ) ^ (2 * n) -
        2 * (boolean_disagreement_count M L : ℝ) := by
    simpa [C, show 2 * n = n + n by omega, pow_add] using
      boolean_disagreement_correlation_identity p M L
  have hqpow : 0 ≤ (q : ℝ) ^ (2 * n) :=
    pow_nonneg (Nat.cast_nonneg q) (2 * n)
  have hc₂pow : 0 ≤ c₂ ^ n := pow_nonneg hc₂.le n
  nlinarith

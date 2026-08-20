import Architect
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

noncomputable section

@[blueprint "def:partite-distribution"
  (statement := /-- A finite $d$-partite distribution consists of finite coordinate spaces, a finite set of top faces with one coordinate in each part, and a nonnegative probability weight on the top faces. Each top face is determined by its complete coordinate tuple: if $x_i=y_i$ for every $i\in[d]$, then $x=y$. Thus the top faces form a finite subset of the full coordinate product. Faces absent from a simplicial complex are represented by weight zero. -/)
  (title := /-- Finite partite distributions -/)
  (latexEnv := "definition")]
structure partite_distribution (d : ℕ) where
  Face : Type
  [faceFintype : Fintype Face]
  Coord : Fin d → Type
  [coordFintype : ∀ i, Fintype (Coord i)]
  coordinate : (x : Face) → (i : Fin d) → Coord i
  coordinate_injective : ∀ {x y : Face}, (∀ i, coordinate x i = coordinate y i) → x = y
  weight : Face → ℝ
  weight_nonnegative : ∀ x, 0 ≤ weight x
  weight_sum_one : ∑ x, weight x = 1

@[blueprint "def:partite-agree-on"
  (statement := /-- For a partite distribution $X$, a coordinate set $S$, and faces $x,z$, the predicate $x =_S z$ means that $x_i=z_i$ for every $i\in S$. -/)
  (title := /-- Agreement on a coordinate set -/)
  (latexEnv := "definition")]
def partite_agree_on {d : ℕ} (X : partite_distribution d) (S : Finset (Fin d))
    (x z : X.Face) : Prop :=
  ∀ i, i ∈ S → X.coordinate x i = X.coordinate z i

@[blueprint "def:partite-fiber-mass"
  (statement := /-- The mass $\mu_X[z_S]$ of the fiber determined by $z$ on $S$ is the sum of the weights of all faces agreeing with $z$ on $S$. -/)
  (title := /-- Mass of a conditioned fiber -/)
  (latexEnv := "definition")]
noncomputable def partite_fiber_mass {d : ℕ} (X : partite_distribution d)
    (S : Finset (Fin d)) (z : X.Face) : ℝ := by
  classical
  letI : Fintype X.Face := X.faceFintype
  exact ∑ x, if partite_agree_on X S x z then X.weight x else 0

@[blueprint "def:partite-conditional-expectation"
  (statement := /-- For a real function $f$ on the top faces, $E_Sf(z)$ is its weighted conditional expectation on the fiber $x_S=z_S$. It is set equal to zero when that fiber has zero mass. -/)
  (title := /-- Conditional expectation on coordinates -/)
  (latexEnv := "definition")]
noncomputable def partite_conditional_expectation {d : ℕ} (X : partite_distribution d)
    (S : Finset (Fin d)) (f : X.Face → ℝ) (z : X.Face) : ℝ := by
  classical
  letI : Fintype X.Face := X.faceFintype
  let m := partite_fiber_mass X S z
  exact if m = 0 then 0
    else (∑ x, if partite_agree_on X S x z then X.weight x * f x else 0) / m

@[blueprint "def:partite-qnorm"
  (statement := /-- For $q>0$, the weighted $q$-norm of $f$ is
  \[
    \|f\|_{q,X}=\left(\sum_x\mu_X(x)|f(x)|^q\right)^{1/q}.
  \] -/)
  (title := /-- Weighted q-norm -/)
  (latexEnv := "definition")]
noncomputable def partite_qnorm {d : ℕ} (X : partite_distribution d)
    (q : ℝ) (f : X.Face → ℝ) : ℝ := by
  classical
  letI : Fintype X.Face := X.faceFintype
  exact Real.rpow (∑ x, X.weight x * Real.rpow |f x| q) (1 / q)

@[blueprint "def:conditioned-coordinate-mass"
  (statement := /-- Given a feasible conditioning $x_S=z_S$, the unnormalized mass of the additional event $x_i=a$ is the total weight of faces satisfying both constraints. -/)
  (title := /-- Conditioned coordinate mass -/)
  (latexEnv := "definition")]
noncomputable def conditioned_coordinate_mass {d : ℕ} (X : partite_distribution d)
    (S : Finset (Fin d)) (z : X.Face) (i : Fin d) (a : X.Coord i) : ℝ := by
  classical
  letI : Fintype X.Face := X.faceFintype
  exact ∑ x, if partite_agree_on X S x z ∧ X.coordinate x i = a then X.weight x else 0

@[blueprint "def:conditioned-coordinate-qnorm"
  (statement := /-- On a feasible fiber $x_S=z_S$, the conditioned marginal $q$-norm on coordinate $i$ uses the probability weights
  $\mu_X[x_i=a,x_S=z_S]/\mu_X[x_S=z_S]$. The value is defined to be zero for an infeasible fiber. -/)
  (title := /-- Conditioned marginal q-norm -/)
  (latexEnv := "definition")]
noncomputable def conditioned_coordinate_qnorm {d : ℕ} (X : partite_distribution d)
    (S : Finset (Fin d)) (z : X.Face) (i : Fin d) (q : ℝ)
    (g : X.Coord i → ℝ) : ℝ := by
  classical
  letI : Fintype (X.Coord i) := X.coordFintype i
  let m := partite_fiber_mass X S z
  exact if m = 0 then 0 else
    Real.rpow
      (∑ a, conditioned_coordinate_mass X S z i a / m * Real.rpow |g a| q)
      (1 / q)

@[blueprint "def:conditioned-marginal-average"
  (statement := /-- For distinct unconditioned coordinates $i,j$, the operator $A_{i,j}^{S,z}$ sends $g$ on the $j$th part to
  $a\mapsto \mathbb{E}[g(x_j)\mid x_S=z_S,\ x_i=a]$, with value zero when the conditioning event has zero mass. -/)
  (title := /-- Conditioned marginal adjacency operator -/)
  (latexEnv := "definition")]
noncomputable def conditioned_marginal_average {d : ℕ} (X : partite_distribution d)
    (S : Finset (Fin d)) (z : X.Face) (i j : Fin d)
    (g : X.Coord j → ℝ) (a : X.Coord i) : ℝ := by
  classical
  letI : Fintype X.Face := X.faceFintype
  let m := conditioned_coordinate_mass X S z i a
  exact if m = 0 then 0 else
    (∑ x, if partite_agree_on X S x z ∧ X.coordinate x i = a
      then X.weight x * g (X.coordinate x j) else 0) / m

@[blueprint "def:conditioned-stationary-average"
  (statement := /-- The stationary operator $\Pi_{i,j}^{S,z}$ sends $g$ to the constant function whose value is
  $\mathbb{E}[g(x_j)\mid x_S=z_S]$. -/)
  (title := /-- Conditioned stationary operator -/)
  (latexEnv := "definition")]
noncomputable def conditioned_stationary_average {d : ℕ} (X : partite_distribution d)
    (S : Finset (Fin d)) (z : X.Face) (j : Fin d)
    (g : X.Coord j → ℝ) : ℝ :=
  partite_conditional_expectation X S (fun x => g (X.coordinate x j)) z

@[blueprint "def:conditioned-marginal-deviation"
  (statement := /-- The conditioned marginal deviation is
  $(A_{i,j}^{S,z}-\Pi_{i,j}^{S,z})g$. -/)
  (title := /-- Conditioned marginal deviation -/)
  (latexEnv := "definition")]
noncomputable def conditioned_marginal_deviation {d : ℕ} (X : partite_distribution d)
    (S : Finset (Fin d)) (z : X.Face) (i j : Fin d)
    (g : X.Coord j → ℝ) : X.Coord i → ℝ :=
  fun a => conditioned_marginal_average X S z i j g a -
    conditioned_stationary_average X S z j g

@[blueprint "def:is-q-gamma-product"
  (statement := /-- A partite distribution $X$ is a $(q,\gamma)$-product if, after every feasible conditioning $x_S=z_S$, every pair of distinct coordinates $i,j\notin S$ satisfies
  \[
    \|(A_{i,j}^{S,z}-\Pi_{i,j}^{S,z})g\|_{q,i\mid S,z}
      \leq \gamma\|g\|_{q,j\mid S,z}
  \]
  for every real function $g$ on the $j$th part. -/)
  (title := /-- Partite q-norm products -/)
  (latexEnv := "definition")]
def is_q_gamma_product {d : ℕ} (X : partite_distribution d) (q γ : ℝ) : Prop :=
  ∀ (S : Finset (Fin d)) (z : X.Face) (i j : Fin d),
    i ∉ S → j ∉ S → i ≠ j → 0 < partite_fiber_mass X S z →
      ∀ g : X.Coord j → ℝ,
        conditioned_coordinate_qnorm X S z i q
            (conditioned_marginal_deviation X S z i j g) ≤
          γ * conditioned_coordinate_qnorm X S z j q g

@[blueprint "def:efron-stein-component"
  (statement := /-- For $S\subseteq[d]$, the Efron--Stein component of $f$ is
  \[
    f^{=S}(z)=\sum_{T\subseteq S}(-1)^{|S\setminus T|}E_Tf(z).
  \] -/)
  (title := /-- Efron--Stein components -/)
  (latexEnv := "definition")]
noncomputable def efron_stein_component {d : ℕ} (X : partite_distribution d)
    (S : Finset (Fin d)) (f : X.Face → ℝ) : X.Face → ℝ := by
  classical
  exact fun z => ∑ T ∈ S.powerset,
    (-1 : ℝ) ^ (S.card - T.card) * partite_conditional_expectation X T f z

@[blueprint "def:generalized-noise"
  (statement := /-- For $r\in\mathbb{R}^d$, the generalized noise operator is
  \[
    T_rf=\sum_{S\subseteq[d]}\left(\prod_{i\in S}r_i\right)f^{=S}.
  \] -/)
  (title := /-- Generalized noise operator -/)
  (latexEnv := "definition")]
noncomputable def generalized_noise {d : ℕ} (X : partite_distribution d)
    (r : Fin d → ℝ) (f : X.Face → ℝ) : X.Face → ℝ := by
  classical
  exact fun x => ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
    (∏ i ∈ S, r i) * efron_stein_component X S f x

@[blueprint "def:scalar-noise"
  (statement := /-- For $\rho\in\mathbb{R}$, the scalar noise operator is
  $T_\rho f=\sum_{S\subseteq[d]}\rho^{|S|}f^{=S}$. -/)
  (title := /-- Scalar noise operator -/)
  (latexEnv := "definition")]
noncomputable def scalar_noise {d : ℕ} (X : partite_distribution d)
    (ρ : ℝ) (f : X.Face → ℝ) : X.Face → ℝ := by
  classical
  exact fun x => ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
    ρ ^ S.card * efron_stein_component X S f x

@[blueprint "def:rademacher-sign"
  (statement := /-- A Boolean Rademacher variable is interpreted as the sign $-1$ at 	exttt{false} and $1$ at 	exttt{true}. -/)
  (title := /-- Boolean Rademacher signs -/)
  (latexEnv := "definition")]
def rademacher_sign : Bool → ℝ
  | false => -1
  | true => 1

@[blueprint "def:partite-symmetrization"
  (statement := /-- The symmetrization of $g$ is the function on
  $\{\pm1\}^d\times X$ defined by
  $\widetilde g(r,x)=T_rg(x)$. -/)
  (title := /-- Symmetrization -/)
  (latexEnv := "definition")]
noncomputable def partite_symmetrization {d : ℕ} (X : partite_distribution d)
    (g : X.Face → ℝ) (r : Fin d → Bool) (x : X.Face) : ℝ :=
  generalized_noise X (fun i => rademacher_sign (r i)) g x

@[blueprint "def:symmetrized-qnorm"
  (statement := /-- The $q$-norm of a symmetrized function is taken with respect to the uniform probability measure on the sign cube and the original face distribution:
  \[
    \|\widetilde g\|_q
      =\left(2^{-d}\sum_{r\in\{\pm1\}^d}
        \sum_x\mu_X(x)|\widetilde g(r,x)|^q\right)^{1/q}.
  \] -/)
  (title := /-- Symmetrized q-norm -/)
  (latexEnv := "definition")]
noncomputable def symmetrized_qnorm {d : ℕ} (X : partite_distribution d)
    (q : ℝ) (g : X.Face → ℝ) : ℝ := by
  classical
  letI : Fintype X.Face := X.faceFintype
  exact Real.rpow
    (((2 : ℝ) ^ d)⁻¹ * ∑ r : Fin d → Bool, ∑ x,
      X.weight x * Real.rpow |partite_symmetrization X g r x| q)
    (1 / q)

@[blueprint "def:exponential-error"
  (statement := /-- For a growth rate $b>0$, dimension $d$, and expansion parameter $\gamma$, set
  $\varepsilon_b(d,\gamma)=2^{bd}\gamma$. This is the explicit representative of $2^{O(d)}\gamma$. -/)
  (title := /-- Exponentially amplified error -/)
  (latexEnv := "definition")]
noncomputable def exponential_error (growth : ℝ) (d : ℕ) (γ : ℝ) : ℝ :=
  Real.rpow 2 (growth * (d : ℝ)) * γ

@[blueprint "def:exponentially-small"
  (statement := /-- For a decay rate $a>0$, the predicate
  $\gamma\leq 2^{-ad}$ is the explicit representative of
  $\gamma\leq 2^{-\Omega(d)}$. -/)
  (title := /-- Exponentially small expansion parameter -/)
  (latexEnv := "definition")]
def exponentially_small (decay : ℝ) (d : ℕ) (γ : ℝ) : Prop :=
  γ ≤ Real.rpow 2 (-(decay * (d : ℝ)))

@[blueprint "def:upper-symmetrization-bound"
  (statement := /-- The predicate $mathsf{Upper}(q,a,b)$ asserts uniformly in $d$, $X$, $\gamma$, and $f$ that every $(q,\gamma)$-product satisfying $\gamma\leq2^{-ad}$ obeys
  \[
    \|f\|_q\leq(1+2^{bd}\gamma)\|\widetilde{T_2f}\|_q.
  \] -/)
  (title := /-- Uniform upper symmetrization estimate -/)
  (latexEnv := "definition")]
def upper_symmetrization_bound (q decay growth : ℝ) : Prop :=
  ∀ (d : ℕ) (X : partite_distribution d) (γ : ℝ) (f : X.Face → ℝ),
    0 ≤ γ → is_q_gamma_product X q γ → exponentially_small decay d γ →
      partite_qnorm X q f ≤
        (1 + exponential_error growth d γ) *
          symmetrized_qnorm X q (scalar_noise X 2 f)

@[blueprint "def:lower-symmetrization-bound"
  (statement := /-- The predicate $mathsf{Lower}(q,c,a,b)$ asserts uniformly in $d$, $X$, $\gamma$, and $f$ that every $(q,\gamma)$-product satisfying $\gamma\leq2^{-ad}$ obeys
  \[
    (1-2^{bd}\gamma)\|\widetilde{T_cf}\|_q\leq\|f\|_q.
  \] -/)
  (title := /-- Uniform lower symmetrization estimate -/)
  (latexEnv := "definition")]
def lower_symmetrization_bound (q c decay growth : ℝ) : Prop :=
  ∀ (d : ℕ) (X : partite_distribution d) (γ : ℝ) (f : X.Face → ℝ),
    0 ≤ γ → is_q_gamma_product X q γ → exponentially_small decay d γ →
      (1 - exponential_error growth d γ) *
          symmetrized_qnorm X q (scalar_noise X c f) ≤
        partite_qnorm X q f

@[blueprint "lem:efron-two-point-weighted-amgm"
  (statement := /-- For nonnegative real numbers $a,b$ and $t\in[0,1]$,
  \[
    a^t b^{1-t}\leq ta+(1-t)b.
  \] -/)
  (proof := /-- The endpoint and zero cases follow from the defining identities for real powers. In the remaining case all quantities are positive. Divide $a$ and $b$ by their positive weighted arithmetic mean $A=ta+(1-t)b$. Applying $\log x\leq x-1$ to the two normalized numbers and taking the same weighted sum shows that the logarithm of their weighted geometric mean is nonpositive. Monotonicity of the exponential gives that this normalized geometric mean is at most one. Multiplication by $A$, together with the laws for real powers of products and sums of exponents, gives the claimed inequality. -/)
  (title := /-- Two-point weighted arithmetic--geometric mean inequality -/)
  (latexEnv := "lemma")]
lemma efron_two_point_weighted_amgm (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    a ^ t * b ^ (1 - t) ≤ t * a + (1 - t) * b := by
  rcases eq_or_lt_of_le ht0 with rfl | ht
  · simp
  rcases eq_or_lt_of_le (sub_nonneg.mpr ht1) with htc | htc
  · have ht_one : t = 1 := by linarith
    subst t
    simp
  rcases eq_or_lt_of_le ha with rfl | ha
  · rw [Real.zero_rpow (ne_of_gt ht), zero_mul]
    positivity
  rcases eq_or_lt_of_le hb with rfl | hb
  · rw [Real.zero_rpow (ne_of_gt htc), mul_zero]
    positivity
  let A := t * a + (1 - t) * b
  have hA : 0 < A := add_pos (mul_pos ht ha) (mul_pos htc hb)
  have hxa : 0 < a / A := div_pos ha hA
  have hxb : 0 < b / A := div_pos hb hA
  have hlog_a := Real.log_le_sub_one_of_pos hxa
  have hlog_b := Real.log_le_sub_one_of_pos hxb
  have hlog : t * Real.log (a / A) + (1 - t) * Real.log (b / A) ≤ 0 := by
    calc
      t * Real.log (a / A) + (1 - t) * Real.log (b / A) ≤
          t * (a / A - 1) + (1 - t) * (b / A - 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hlog_a ht0)
          (mul_le_mul_of_nonneg_left hlog_b (sub_nonneg.mpr ht1))
      _ = 0 := by
        dsimp [A] at hA ⊢
        field_simp [ne_of_gt hA]
        ring
  have hnormalized : (a / A) ^ t * (b / A) ^ (1 - t) ≤ 1 := by
    rw [Real.rpow_def_of_pos hxa, Real.rpow_def_of_pos hxb, ← Real.exp_add]
    calc
      Real.exp (Real.log (a / A) * t + Real.log (b / A) * (1 - t)) ≤
          Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith [hlog])
      _ = 1 := Real.exp_zero
  calc
    a ^ t * b ^ (1 - t) =
        (A * (a / A)) ^ t * (A * (b / A)) ^ (1 - t) := by
          congr 2 <;> field_simp [ne_of_gt hA]
    _ = (A ^ t * (a / A) ^ t) * (A ^ (1 - t) * (b / A) ^ (1 - t)) := by
          rw [Real.mul_rpow hA.le hxa.le, Real.mul_rpow hA.le hxb.le]
    _ = A * ((a / A) ^ t * (b / A) ^ (1 - t)) := by
          calc
            (A ^ t * (a / A) ^ t) * (A ^ (1 - t) * (b / A) ^ (1 - t)) =
                (A ^ t * A ^ (1 - t)) * ((a / A) ^ t * (b / A) ^ (1 - t)) := by ring
            _ = A ^ (t + (1 - t)) * ((a / A) ^ t * (b / A) ^ (1 - t)) := by
              rw [Real.rpow_add hA]
            _ = A * ((a / A) ^ t * (b / A) ^ (1 - t)) := by
              rw [show t + (1 - t) = 1 by ring, Real.rpow_one]
    _ ≤ A * 1 := mul_le_mul_of_nonneg_left hnormalized hA.le
    _ = t * a + (1 - t) * b := by simp [A]

@[blueprint "lem:efron-rpow-tangent"
  (statement := /-- If $q\geq1$ and $x\geq0$, then
  \[
    qx-(q-1)\leq x^q.
  \] -/)
  (proof := /-- Apply \cref{lem:efron-two-point-weighted-amgm} to $a=x^q$, $b=1$, and $t=1/q$. Since $q>0$, the power-of-a-power identity gives $(x^q)^{1/q}=x$. Multiplying the resulting inequality by $q$ and rearranging yields the stated tangent bound. -/)
  (title := /-- Tangent bound for a real power -/)
  (latexEnv := "lemma")]
lemma efron_rpow_tangent (q x : ℝ) (hq : 1 ≤ q) (hx : 0 ≤ x) :
    q * x - (q - 1) ≤ x ^ q := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have ht0 : 0 ≤ 1 / q := by positivity
  have ht1 : 1 / q ≤ 1 := by
    rw [div_le_one hqpos]
    exact hq
  have h := efron_two_point_weighted_amgm (x ^ q) 1 (1 / q)
    (Real.rpow_nonneg hx q) zero_le_one ht0 ht1
  have hroot : (x ^ q) ^ (1 / q) = x := by
    rw [← Real.rpow_mul hx]
    field_simp
    rw [Real.rpow_one]
  rw [hroot, Real.one_rpow, mul_one] at h
  have hm := mul_le_mul_of_nonneg_left h hqpos.le
  have hm' : q * x ≤ x ^ q + (q - 1) := by
    calc
      q * x ≤ q * (1 / q * x ^ q + (1 - 1 / q) * 1) := hm
      _ = x ^ q + (q - 1) := by
        field_simp [hqne]
  linarith

@[blueprint "lem:efron-weighted-rpow-mean-le"
  (statement := /-- Let $I$ be finite, let $q\geq1$, and let nonnegative weights $(w_i)_{i\in I}$ sum to one. For every family of nonnegative reals $(a_i)_{i\in I}$,
  \[
    \left(\sum_i w_i a_i\right)^q\leq\sum_i w_i a_i^q.
  \] -/)
  (proof := /-- Put $M=\sum_iw_i a_i$. If $M=0$, the claim follows from nonnegativity. Otherwise apply \cref{lem:efron-rpow-tangent} to each $a_i/M$, multiply by $w_i$, and sum. Since the weights sum to one and the weighted mean of $a_i/M$ is one, this gives $1\leq\sum_iw_i(a_i/M)^q$. The laws for powers of quotients then identify the right-hand side with $(\sum_iw_i a_i^q)/M^q$; multiplication by the positive number $M^q$ proves the result. -/)
  (title := /-- Finite weighted Jensen inequality for real powers -/)
  (latexEnv := "lemma")]
lemma efron_weighted_rpow_mean_le {ι : Type} [Fintype ι] (q : ℝ) (hq : 1 ≤ q)
    (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i)
    (hwsum : ∑ i, w i = 1) :
    (∑ i, w i * a i) ^ q ≤ ∑ i, w i * (a i) ^ q := by
  let M := ∑ i, w i * a i
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (ha i)
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  rcases eq_or_lt_of_le hM0 with hM | hM
  · rw [show (∑ i, w i * a i) = 0 from hM.symm,
      Real.zero_rpow (ne_of_gt hqpos)]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.rpow_nonneg (ha i) q)
  have hMne : M ≠ 0 := ne_of_gt hM
  have htangent : ∀ i, q * (a i / M) - (q - 1) ≤ (a i / M) ^ q :=
    fun i => efron_rpow_tangent q (a i / M) hq (div_nonneg (ha i) hM0)
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (htangent i) (hw i)
  have hone : 1 ≤ ∑ i, w i * (a i / M) ^ q := by
    calc
      1 = ∑ i, w i * (q * (a i / M) - (q - 1)) := by
        rw [show (∑ i, w i * (q * (a i / M) - (q - 1))) =
            q / M * (∑ i, w i * a i) - (q - 1) * (∑ i, w i) by
          calc
            (∑ i, w i * (q * (a i / M) - (q - 1))) =
                ∑ i, (q / M * (w i * a i) - (q - 1) * w i) := by
              apply Finset.sum_congr rfl
              intro i hi
              field_simp [hMne]
            _ = q / M * (∑ i, w i * a i) - (q - 1) * (∑ i, w i) := by
              rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]]
        rw [show (∑ i, w i * a i) = M from rfl, hwsum]
        field_simp [hMne]
        ring
      _ ≤ ∑ i, w i * (a i / M) ^ q := hsum
  have hnormalized : (∑ i, w i * (a i / M) ^ q) =
      (∑ i, w i * (a i) ^ q) / M ^ q := by
    simp_rw [Real.div_rpow (ha _) hM0]
    simp_rw [div_eq_mul_inv, ← mul_assoc]
    rw [Finset.sum_mul]
  rw [hnormalized] at hone
  have hMq : 0 < M ^ q := Real.rpow_pos_of_pos hM q
  calc
    M ^ q = M ^ q * 1 := by ring
    _ ≤ M ^ q * ((∑ i, w i * (a i) ^ q) / M ^ q) :=
      mul_le_mul_of_nonneg_left hone hMq.le
    _ = ∑ i, w i * (a i) ^ q := by field_simp [ne_of_gt hMq]

@[blueprint "lem:efron-conditional-qnorm-le"
  (statement := /-- Let $X$ be a finite partite distribution, let $q\geq1$, and let $T\subseteq[d]$. For every real function $f$ on the top faces,
  \[
    \|E_Tf\|_q\leq\|f\|_q.
  \] -/)
  (proof := /-- On a fiber of positive mass, normalize the face weights by that mass. The absolute value of the weighted average is at most the corresponding average of $|f|$, and \cref{lem:efron-weighted-rpow-mean-le} bounds its $q$th power by the average of $|f|^q$. A zero-mass fiber contributes zero by definition. Multiply the fiberwise estimates by the face weights and sum. After interchanging the two finite sums, the coefficient of a fixed face $x$ is its weight times the total normalized weight of the fiber of $x$, hence is exactly its weight. Monotonicity of the power $1/q$ yields the norm contraction. -/)
  (title := /-- Conditional expectation contracts the weighted q-norm -/)
  (latexEnv := "lemma")]
lemma efron_conditional_qnorm_le {d : ℕ} (X : partite_distribution d)
    (q : ℝ) (hq : 1 ≤ q) (T : Finset (Fin d)) (f : X.Face → ℝ) :
    partite_qnorm X q (partite_conditional_expectation X T f) ≤
      partite_qnorm X q f := by
  classical
  letI : Fintype X.Face := X.faceFintype
  have hagree_refl (x : X.Face) : partite_agree_on X T x x := by
    intro i hi
    rfl
  have hagree_symm {x z : X.Face} (h : partite_agree_on X T x z) :
      partite_agree_on X T z x := by
    intro i hi
    exact (h i hi).symm
  have hagree_trans {x y z : X.Face} (hxy : partite_agree_on X T x y)
      (hyz : partite_agree_on X T y z) : partite_agree_on X T x z := by
    intro i hi
    exact (hxy i hi).trans (hyz i hi)
  have hmass_nonneg (z : X.Face) : 0 ≤ partite_fiber_mass X T z := by
    unfold partite_fiber_mass
    exact Finset.sum_nonneg fun x _ => by
      split_ifs
      · exact X.weight_nonnegative x
      · exact le_rfl
  have hweight_le_mass (z : X.Face) : X.weight z ≤ partite_fiber_mass X T z := by
    unfold partite_fiber_mass
    calc
      X.weight z = if partite_agree_on X T z z then X.weight z else 0 := by
        simp [hagree_refl]
      _ ≤ ∑ x, if partite_agree_on X T x z then X.weight x else 0 := by
        refine Finset.single_le_sum (s := Finset.univ)
          (f := fun x => if partite_agree_on X T x z then X.weight x else 0) ?_
          (Finset.mem_univ z)
        intro x hx
        by_cases h : partite_agree_on X T x z
        · simp [h, X.weight_nonnegative x]
        · simp [h]
  have hmass_eq {x z : X.Face} (hxz : partite_agree_on X T x z) :
      partite_fiber_mass X T x = partite_fiber_mass X T z := by
    unfold partite_fiber_mass
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hyx : partite_agree_on X T y x
    · have hyz := hagree_trans hyx hxz
      simp [hyx, hyz]
    · have hyz : ¬partite_agree_on X T y z := by
        intro hyz
        exact hyx (hagree_trans hyz (hagree_symm hxz))
      simp [hyx, hyz]
  have hfiber (z : X.Face) :
      |partite_conditional_expectation X T f z| ^ q ≤
        ∑ x, (if partite_agree_on X T x z then
          X.weight x / partite_fiber_mass X T z else 0) * |f x| ^ q := by
    by_cases hm : partite_fiber_mass X T z = 0
    · simp [partite_conditional_expectation, hm,
        Real.zero_rpow (ne_of_gt (lt_of_lt_of_le zero_lt_one hq))]
    have hmpos : 0 < partite_fiber_mass X T z :=
      lt_of_le_of_ne (hmass_nonneg z) (Ne.symm hm)
    let wz : X.Face → ℝ := fun x => if partite_agree_on X T x z then
      X.weight x / partite_fiber_mass X T z else 0
    have hwz (x : X.Face) : 0 ≤ wz x := by
      dsimp [wz]
      split_ifs
      · exact div_nonneg (X.weight_nonnegative x) hmpos.le
      · exact le_rfl
    have hwz_sum : ∑ x, wz x = 1 := by
      dsimp [wz]
      rw [show (∑ x, if partite_agree_on X T x z then
          X.weight x / partite_fiber_mass X T z else 0) =
          partite_fiber_mass X T z / partite_fiber_mass X T z by
        calc
          (∑ x, if partite_agree_on X T x z then
              X.weight x / partite_fiber_mass X T z else 0) =
              ∑ x, (if partite_agree_on X T x z then X.weight x else 0) /
                partite_fiber_mass X T z := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases h : partite_agree_on X T x z <;> simp [h]
          _ = (∑ x, if partite_agree_on X T x z then X.weight x else 0) /
                partite_fiber_mass X T z := by
            simp_rw [div_eq_mul_inv]
            rw [Finset.sum_mul]
          _ = partite_fiber_mass X T z / partite_fiber_mass X T z := by rfl]
      exact div_self hm
    have habs : |partite_conditional_expectation X T f z| ≤ ∑ x, wz x * |f x| := by
      have hs := Finset.abs_sum_le_sum_abs
        (f := fun x : X.Face => if partite_agree_on X T x z then X.weight x * f x else 0)
        Finset.univ
      rw [partite_conditional_expectation, if_neg hm, abs_div, abs_of_pos hmpos]
      dsimp [wz]
      rw [div_eq_mul_inv]
      refine (mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr hmpos.le)).trans_eq ?_
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : partite_agree_on X T x z
      · simp [h, abs_mul, abs_of_nonneg (X.weight_nonnegative x), div_eq_mul_inv]
        ring
      · simp [h]
    have hjensen := efron_weighted_rpow_mean_le q hq wz (fun x => |f x|)
      hwz (fun x => abs_nonneg (f x)) hwz_sum
    exact (Real.rpow_le_rpow (abs_nonneg _) habs (le_trans zero_le_one hq)).trans hjensen
  have hsum :
      (∑ z, X.weight z * |partite_conditional_expectation X T f z| ^ q) ≤
        ∑ z, X.weight z * (∑ x, (if partite_agree_on X T x z then
          X.weight x / partite_fiber_mass X T z else 0) * |f x| ^ q) :=
    Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hfiber z) (X.weight_nonnegative z)
  have hkernel :
      (∑ z, X.weight z * (∑ x, (if partite_agree_on X T x z then
          X.weight x / partite_fiber_mass X T z else 0) * |f x| ^ q) =
        ∑ x, X.weight x * |f x| ^ q) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hwx : X.weight x = 0
    · simp [hwx]
    have hwxpos : 0 < X.weight x := lt_of_le_of_ne (X.weight_nonnegative x) (Ne.symm hwx)
    have hmxpos : 0 < partite_fiber_mass X T x :=
      lt_of_lt_of_le hwxpos (hweight_le_mass x)
    have hinner : (∑ z, X.weight z *
        ((if partite_agree_on X T x z then
          X.weight x / partite_fiber_mass X T z else 0) * |f x| ^ q)) =
        X.weight x * |f x| ^ q := by
      calc
        (∑ z, X.weight z *
            ((if partite_agree_on X T x z then
              X.weight x / partite_fiber_mass X T z else 0) * |f x| ^ q)) =
            (∑ z, if partite_agree_on X T z x then X.weight z else 0) *
              (X.weight x / partite_fiber_mass X T x * |f x| ^ q) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro z hz
          by_cases hzx : partite_agree_on X T z x
          · have hxz := hagree_symm hzx
            rw [if_pos hzx, if_pos hxz, ← hmass_eq hxz]
          · have hxz : ¬partite_agree_on X T x z := fun h => hzx (hagree_symm h)
            simp [hzx, hxz]
        _ = partite_fiber_mass X T x *
              (X.weight x / partite_fiber_mass X T x * |f x| ^ q) := by rfl
        _ = X.weight x * |f x| ^ q := by field_simp [ne_of_gt hmxpos]
    exact hinner
  rw [hkernel] at hsum
  unfold partite_qnorm
  exact Real.rpow_le_rpow
    (Finset.sum_nonneg fun z _ => mul_nonneg (X.weight_nonnegative z)
      (Real.rpow_nonneg (abs_nonneg _) q)) hsum (by positivity)

@[blueprint "lem:efron-qnorm-finset-sum-le-card"
  (statement := /-- Let $X$ be a finite partite distribution, let $q\geq1$, let $s$ be a finite index set, and suppose $\|g_i\|_q\leq C$ for every $i\in s$, where $C\geq0$. Then
  \[
    \left\|\sum_{i\in s}g_i\right\|_q\leq |s|C.
  \] -/)
  (proof := /-- The assertion is immediate when $s$ is empty. Otherwise put $n=|s|>0$. For each face, divide the absolute value of the sum by $n$, bound it by the average of the absolute values of the summands, and apply \cref{lem:efron-weighted-rpow-mean-le} with the uniform weights $1/n$ on $s$. After multiplication by the face weights and interchange of the finite sums, the resulting $q$th-power sum is at most the average of the corresponding sums for the $g_i$. Raising each hypothesis $\|g_i\|_q\leq C$ to the $q$th power bounds these sums by $C^q$. Clearing the positive factor $n^q$ and taking the power $1/q$ gives the claimed bound. -/)
  (title := /-- Cardinality bound for a finite q-norm sum -/)
  (latexEnv := "lemma")]
lemma efron_qnorm_finset_sum_le_card {d : ℕ} (X : partite_distribution d)
    {ι : Type} [Fintype ι] (q : ℝ) (hq : 1 ≤ q) (s : Finset ι)
    (g : ι → X.Face → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ i ∈ s, partite_qnorm X q (g i) ≤ C) :
    partite_qnorm X q (fun x => ∑ i ∈ s, g i x) ≤ (s.card : ℝ) * C := by
  classical
  letI : Fintype X.Face := X.faceFintype
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  by_cases hs : s = ∅
  · subst s
    simp only [Finset.sum_empty, Nat.cast_zero, zero_mul]
    unfold partite_qnorm
    simp [Real.zero_rpow (ne_of_gt hqpos),
      Real.zero_rpow (one_div_ne_zero (ne_of_gt hqpos))]
    rw [Real.zero_rpow (inv_ne_zero (ne_of_gt hqpos))]
  let n : ℝ := s.card
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast s.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
  have hn0 : 0 ≤ n := hn.le
  have hnne : n ≠ 0 := ne_of_gt hn
  let wi : ι → ℝ := fun i => if i ∈ s then 1 / n else 0
  have hwi (i : ι) : 0 ≤ wi i := by
    dsimp [wi]
    split_ifs
    · positivity
    · exact le_rfl
  have hwi_sum : ∑ i, wi i = 1 := by
    have hc : (s.card : ℝ) * (1 / n) = 1 := by
      rw [show (s.card : ℝ) = n from rfl]
      field_simp
    simpa [wi, nsmul_eq_mul] using hc
  have hcomponent (i : ι) (hi : i ∈ s) :
      (∑ x, X.weight x * |g i x| ^ q) ≤ C ^ q := by
    have hbase : 0 ≤ ∑ x, X.weight x * |g i x| ^ q :=
      Finset.sum_nonneg fun x _ => mul_nonneg (X.weight_nonnegative x)
        (Real.rpow_nonneg (abs_nonneg _) q)
    have hgi := hg i hi
    unfold partite_qnorm at hgi
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg hbase (1 / q)) hgi
      (le_trans zero_le_one hq)
    have hleft : ((∑ x, X.weight x * |g i x| ^ q) ^ (1 / q)) ^ q =
        ∑ x, X.weight x * |g i x| ^ q := by
      rw [← Real.rpow_mul hbase]
      field_simp
      rw [Real.rpow_one]
    rw [hleft] at hp
    exact hp
  have hpoint (x : X.Face) :
      (|∑ i ∈ s, g i x| / n) ^ q ≤ ∑ i, wi i * |g i x| ^ q := by
    have habs : |∑ i ∈ s, g i x| / n ≤ ∑ i, wi i * |g i x| := by
      have hsabs := Finset.abs_sum_le_sum_abs (f := fun i => g i x) s
      have hdiv := div_le_div_of_nonneg_right hsabs hn0
      calc
        |∑ i ∈ s, g i x| / n ≤ (∑ i ∈ s, |g i x|) / n := hdiv
        _ = ∑ i, wi i * |g i x| := by
          rw [div_eq_mul_inv, Finset.sum_mul]
          simp [wi, mul_comm]
    have hjensen := efron_weighted_rpow_mean_le q hq wi (fun i => |g i x|)
      hwi (fun i => abs_nonneg _) hwi_sum
    exact (Real.rpow_le_rpow (by positivity) habs (le_trans zero_le_one hq)).trans hjensen
  have htotal :
      (∑ x, X.weight x * (|∑ i ∈ s, g i x| / n) ^ q) ≤ C ^ q := by
    calc
      (∑ x, X.weight x * (|∑ i ∈ s, g i x| / n) ^ q) ≤
          ∑ x, X.weight x * (∑ i, wi i * |g i x| ^ q) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpoint x)
          (X.weight_nonnegative x)
      _ = ∑ i, wi i * (∑ x, X.weight x * |g i x| ^ q) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ ≤ ∑ i, wi i * C ^ q := Finset.sum_le_sum fun i _ => by
        by_cases hi : i ∈ s
        · exact mul_le_mul_of_nonneg_left (hcomponent i hi) (hwi i)
        · simp [wi, hi]
      _ = C ^ q := by rw [← Finset.sum_mul, hwi_sum, one_mul]
  have hnormalized :
      (∑ x, X.weight x * (|∑ i ∈ s, g i x| / n) ^ q) =
        (∑ x, X.weight x * |∑ i ∈ s, g i x| ^ q) / n ^ q := by
    simp_rw [Real.div_rpow (abs_nonneg _) hn0]
    simp_rw [div_eq_mul_inv, ← mul_assoc]
    rw [Finset.sum_mul]
  rw [hnormalized] at htotal
  have hnq : 0 < n ^ q := Real.rpow_pos_of_pos hn q
  have hraw : (∑ x, X.weight x * |∑ i ∈ s, g i x| ^ q) ≤ (n * C) ^ q := by
    calc
      (∑ x, X.weight x * |∑ i ∈ s, g i x| ^ q) =
          n ^ q * ((∑ x, X.weight x * |∑ i ∈ s, g i x| ^ q) / n ^ q) := by
        field_simp [ne_of_gt hnq]
      _ ≤ n ^ q * C ^ q := mul_le_mul_of_nonneg_left htotal hnq.le
      _ = (n * C) ^ q := (Real.mul_rpow hn0 hC).symm
  unfold partite_qnorm
  have hroot :
      (∑ x, X.weight x * |∑ i ∈ s, g i x| ^ q) ^ (1 / q) ≤
        ((n * C) ^ q) ^ (1 / q) := Real.rpow_le_rpow
      (Finset.sum_nonneg fun x _ => mul_nonneg (X.weight_nonnegative x)
        (Real.rpow_nonneg (abs_nonneg _) q)) hraw (by positivity)
  have hright : ((n * C) ^ q) ^ (1 / q) = n * C := by
    rw [← Real.rpow_mul (mul_nonneg hn0 hC)]
    field_simp
    rw [Real.rpow_one]
  rw [hright] at hroot
  simpa [n] using hroot

@[blueprint "lem:efron-component-qnorm-le"
  (statement := /-- Let $X$ be a finite partite distribution, let $q\geq1$, and let $S\subseteq[d]$. Then every real function $f$ on the top faces satisfies
  \[
    \|f^{=S}\|_q\leq 2^{|S|}\|f\|_q.
  \] -/)
  (proof := /-- Expand $f^{=S}$ as the alternating sum of the conditional expectations $E_Tf$ over $T\subseteq S$. The coefficient $(-1)^{|S|-|T|}$ has absolute value one, so \cref{lem:efron-conditional-qnorm-le} bounds the $q$-norm of every summand by $\|f\|_q$. Apply \cref{lem:efron-qnorm-finset-sum-le-card} to this sum and use $|\{T:T\subseteq S\}|=2^{|S|}$ to obtain the stated inequality. -/)
  (title := /-- Contraction bound for Efron--Stein components -/)
  (latexEnv := "lemma")]
lemma efron_component_qnorm_le {d : ℕ} (X : partite_distribution d)
    (q : ℝ) (hq : 1 ≤ q) (S : Finset (Fin d)) (f : X.Face → ℝ) :
    partite_qnorm X q (efron_stein_component X S f) ≤
      (2 : ℝ) ^ S.card * partite_qnorm X q f := by
  classical
  letI : Fintype X.Face := X.faceFintype
  have hC : 0 ≤ partite_qnorm X q f := by
    unfold partite_qnorm
    exact Real.rpow_nonneg (Finset.sum_nonneg fun x _ =>
      mul_nonneg (X.weight_nonnegative x) (Real.rpow_nonneg (abs_nonneg _) q)) (1 / q)
  let g : Finset (Fin d) → X.Face → ℝ := fun T x =>
    (-1 : ℝ) ^ (S.card - T.card) * partite_conditional_expectation X T f x
  have hg (T : Finset (Fin d)) (hT : T ∈ S.powerset) :
      partite_qnorm X q (g T) ≤ partite_qnorm X q f := by
    calc
      partite_qnorm X q (g T) =
          partite_qnorm X q (partite_conditional_expectation X T f) := by
        unfold partite_qnorm
        congr 2
        funext x
        dsimp [g]
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      _ ≤ partite_qnorm X q f := efron_conditional_qnorm_le X q hq T f
  have hsum := efron_qnorm_finset_sum_le_card X q hq S.powerset g
    (partite_qnorm X q f) hC hg
  change partite_qnorm X q (fun x => ∑ T ∈ S.powerset,
    (-1 : ℝ) ^ (S.card - T.card) * partite_conditional_expectation X T f x) ≤
      (2 : ℝ) ^ S.card * partite_qnorm X q f
  simpa [g, Finset.card_powerset] using hsum

@[blueprint "lem:noise-qnorm-nonnegative-scale"
  (statement := /-- Let $X$ be a finite partite distribution and let $q\geq1$. For every nonnegative real number $a$ and every real-valued function $g$ on the top faces,
  \[
    \|ag\|_q=a\|g\|_q.
  \] -/)
  (proof := /-- Expand the norm using \cref{def:partite-qnorm}. Since $a\geq0$, one has $|ag(x)|^q=a^q|g(x)|^q$ for every face $x$. Factor $a^q$ out of the weighted finite sum and then use $(a^q)^{1/q}=a$, which holds because $q\geq1$ and hence $q>0$. -/)
  (title := /-- Nonnegative homogeneity of the q-norm -/)
  (latexEnv := "lemma")]
lemma noise_qnorm_nonnegative_scale {d : ℕ} (X : partite_distribution d)
    (q : ℝ) (hq : 1 ≤ q) (a : ℝ) (ha : 0 ≤ a) (g : X.Face → ℝ) :
    partite_qnorm X q (fun x => a * g x) = a * partite_qnorm X q g := by
  classical
  letI : Fintype X.Face := X.faceFintype
  unfold partite_qnorm
  have hmoment : 0 ≤ ∑ x, X.weight x * |g x| ^ q :=
    Finset.sum_nonneg fun x _ => mul_nonneg (X.weight_nonnegative x)
      (Real.rpow_nonneg (abs_nonneg _) q)
  have habs (x : X.Face) : |a * g x| ^ q = a ^ q * |g x| ^ q := by
    rw [abs_mul, abs_of_nonneg ha, Real.mul_rpow ha (abs_nonneg _)]
  change (∑ x, X.weight x * |a * g x| ^ q) ^ (1 / q) =
    a * (∑ x, X.weight x * |g x| ^ q) ^ (1 / q)
  rw [show (∑ x, X.weight x * |a * g x| ^ q) =
      a ^ q * ∑ x, X.weight x * |g x| ^ q by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [habs]
    ring]
  rw [Real.mul_rpow (Real.rpow_nonneg ha q) hmoment]
  have haroot : (a ^ q) ^ (1 / q) = a := by
    rw [← Real.rpow_mul ha]
    field_simp
    rw [Real.rpow_one]
  rw [haroot]

@[blueprint "lem:noise-qnorm-weighted-average-le"
  (statement := /-- Let $X$ be a finite partite distribution, let $q\geq1$, and let $w_i\geq0$ be finitely many weights with $\sum_i w_i=1$. If $\|g_i\|_q\leq C$ for every $i$, where $C\geq0$, then
  \[
    \left\|\sum_i w_i g_i\right\|_q\leq C.
  \] -/)
  (proof := /-- Pointwise, the triangle inequality bounds the absolute value of the weighted sum by the weighted sum of the absolute values. Apply \cref{lem:efron-weighted-rpow-mean-le} to these absolute values. After multiplication by the face weights and interchange of the two finite sums, raising each norm hypothesis to the $q$th power bounds every component moment by $C^q$. The weights sum to one, so the total $q$th moment is at most $C^q$; taking the positive $q$th root proves the assertion. -/)
  (title := /-- Convex weighted-average bound for the q-norm -/)
  (latexEnv := "lemma")]
lemma noise_qnorm_weighted_average_le {d : ℕ} (X : partite_distribution d)
    {ι : Type} [Fintype ι] (q : ℝ) (hq : 1 ≤ q)
    (w : ι → ℝ) (g : ι → X.Face → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hg : ∀ i, partite_qnorm X q (g i) ≤ C) :
    partite_qnorm X q (fun x => ∑ i, w i * g i x) ≤ C := by
  classical
  letI : Fintype X.Face := X.faceFintype
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hcomponent (i : ι) :
      (∑ x, X.weight x * |g i x| ^ q) ≤ C ^ q := by
    have hbase : 0 ≤ ∑ x, X.weight x * |g i x| ^ q :=
      Finset.sum_nonneg fun x _ => mul_nonneg (X.weight_nonnegative x)
        (Real.rpow_nonneg (abs_nonneg _) q)
    have hgi := hg i
    unfold partite_qnorm at hgi
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg hbase (1 / q)) hgi
      (le_trans zero_le_one hq)
    have hleft : ((∑ x, X.weight x * |g i x| ^ q) ^ (1 / q)) ^ q =
        ∑ x, X.weight x * |g i x| ^ q := by
      rw [← Real.rpow_mul hbase]
      field_simp
      rw [Real.rpow_one]
    rw [hleft] at hp
    exact hp
  have hpoint (x : X.Face) :
      |∑ i, w i * g i x| ^ q ≤ ∑ i, w i * |g i x| ^ q := by
    have habs : |∑ i, w i * g i x| ≤ ∑ i, w i * |g i x| := by
      calc
        |∑ i, w i * g i x| ≤ ∑ i, |w i * g i x| :=
          Finset.abs_sum_le_sum_abs (f := fun i => w i * g i x) Finset.univ
        _ = ∑ i, w i * |g i x| := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [abs_mul, abs_of_nonneg (hw i)]
    have hjensen := efron_weighted_rpow_mean_le q hq w (fun i => |g i x|)
      hw (fun i => abs_nonneg _) hwsum
    exact (Real.rpow_le_rpow (abs_nonneg _) habs
      (le_trans zero_le_one hq)).trans hjensen
  have htotal :
      (∑ x, X.weight x * |∑ i, w i * g i x| ^ q) ≤ C ^ q := by
    calc
      (∑ x, X.weight x * |∑ i, w i * g i x| ^ q) ≤
          ∑ x, X.weight x * (∑ i, w i * |g i x| ^ q) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpoint x)
          (X.weight_nonnegative x)
      _ = ∑ i, w i * (∑ x, X.weight x * |g i x| ^ q) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ ≤ ∑ i, w i * C ^ q :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hcomponent i) (hw i)
      _ = C ^ q := by rw [← Finset.sum_mul, hwsum, one_mul]
  unfold partite_qnorm
  have hroot :
      (∑ x, X.weight x * |∑ i, w i * g i x| ^ q) ^ (1 / q) ≤
        (C ^ q) ^ (1 / q) := Real.rpow_le_rpow
      (Finset.sum_nonneg fun x _ => mul_nonneg (X.weight_nonnegative x)
        (Real.rpow_nonneg (abs_nonneg _) q)) htotal (by positivity)
  have hright : (C ^ q) ^ (1 / q) = C := by
    rw [← Real.rpow_mul hC]
    field_simp
    rw [Real.rpow_one]
  rw [hright] at hroot
  exact hroot

@[blueprint "lem:noise-two-qnorm-le"
  (statement := /-- Let $X$ be a finite $d$-partite distribution and $q\geq1$. Then
  \[
    \|T_2f\|_q\leq 5^d\|f\|_q
  \]
  for every real function $f$ on the top faces. -/)
  (proof := /-- For each $S\subseteq[d]$, put
  $w_S=4^{|S|}/5^d$ and $g_S=(5^d/2^{|S|})f^{=S}$. The binomial theorem gives
  $\sum_S w_S=1$, and all these weights are nonnegative. By
  \cref{lem:noise-qnorm-nonnegative-scale, lem:efron-component-qnorm-le},
  \[
    \|g_S\|_q\leq
      \frac{5^d}{2^{|S|}}2^{|S|}\|f\|_q
      =5^d\|f\|_q.
  \]
  Apply \cref{lem:noise-qnorm-weighted-average-le} to obtain
  $\|\sum_S w_Sg_S\|_q\leq5^d\|f\|_q$. Finally,
  $w_Sg_S=2^{|S|}f^{=S}$ for every $S$, so the weighted sum is exactly $T_2f$. -/)
  (title := /-- Exponential norm bound for two-noise -/)
  (latexEnv := "lemma")]
lemma noise_two_qnorm_le {d : ℕ} (X : partite_distribution d)
    (q : ℝ) (hq : 1 ≤ q) (f : X.Face → ℝ) :
    partite_qnorm X q (scalar_noise X 2 f) ≤
      (5 : ℝ) ^ d * partite_qnorm X q f := by
  classical
  letI : Fintype X.Face := X.faceFintype
  have hnorm : 0 ≤ partite_qnorm X q f := by
    unfold partite_qnorm
    exact Real.rpow_nonneg (Finset.sum_nonneg fun x _ =>
      mul_nonneg (X.weight_nonnegative x)
        (Real.rpow_nonneg (abs_nonneg _) q)) (1 / q)
  have hpow : (∑ S : Finset (Fin d), (4 : ℝ) ^ S.card) = (5 : ℝ) ^ d := by
    calc
      (∑ S : Finset (Fin d), (4 : ℝ) ^ S.card) =
          ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
            (4 : ℝ) ^ S.card := by rw [Finset.powerset_univ]
      _ = ∑ m ∈ Finset.range (d + 1), d.choose m • (4 : ℝ) ^ m := by
        simpa using (Finset.sum_powerset_apply_card
          (f := fun m => (4 : ℝ) ^ m)
          (x := (Finset.univ : Finset (Fin d))))
      _ = (5 : ℝ) ^ d := by
        rw [show (5 : ℝ) ^ d = (4 + 1) ^ d by norm_num, add_pow]
        apply Finset.sum_congr rfl
        intro m hm
        simp [nsmul_eq_mul, mul_comm]
  let w : Finset (Fin d) → ℝ :=
    fun S => (4 : ℝ) ^ S.card / (5 : ℝ) ^ d
  let g : Finset (Fin d) → X.Face → ℝ :=
    fun S x => ((5 : ℝ) ^ d / (2 : ℝ) ^ S.card) *
      efron_stein_component X S f x
  have hw : ∀ S, 0 ≤ w S := fun S => by
    dsimp [w]
    positivity
  have hwsum : ∑ S, w S = 1 := by
    simp only [w, div_eq_mul_inv]
    rw [← Finset.sum_mul, hpow,
      mul_inv_cancel₀ (by positivity : (5 : ℝ) ^ d ≠ 0)]
  have hg : ∀ S, partite_qnorm X q (g S) ≤
      (5 : ℝ) ^ d * partite_qnorm X q f := by
    intro S
    dsimp [g]
    rw [noise_qnorm_nonnegative_scale X q hq
      ((5 : ℝ) ^ d / (2 : ℝ) ^ S.card) (by positivity)]
    calc
      ((5 : ℝ) ^ d / (2 : ℝ) ^ S.card) *
          partite_qnorm X q (efron_stein_component X S f) ≤
          ((5 : ℝ) ^ d / (2 : ℝ) ^ S.card) *
            ((2 : ℝ) ^ S.card * partite_qnorm X q f) :=
        mul_le_mul_of_nonneg_left (efron_component_qnorm_le X q hq S f)
          (by positivity)
      _ = (5 : ℝ) ^ d * partite_qnorm X q f := by
        field_simp
  have havg := noise_qnorm_weighted_average_le X q hq w g
    ((5 : ℝ) ^ d * partite_qnorm X q f) (mul_nonneg (by positivity) hnorm)
    hw hwsum hg
  have hrepresentation :
      (fun x => ∑ S, w S * g S x) = scalar_noise X 2 f := by
    funext x
    unfold scalar_noise
    rw [Finset.powerset_univ]
    apply Finset.sum_congr rfl
    intro S hS
    dsimp [w, g]
    field_simp
    rw [show (4 : ℝ) ^ S.card =
      (2 : ℝ) ^ S.card * (2 : ℝ) ^ S.card by
        rw [← mul_pow]
        norm_num]
    ring
  rw [hrepresentation] at havg
  exact havg

@[blueprint "lem:conditional-expectation-tower-local"
  (statement := /-- Let $X$ be a finite $d$-partite distribution, let $S\subseteq T\subseteq[d]$, and let $f$ be real-valued on the top faces. Then
  \[
    E_S(E_Tf)=E_Sf.
  \] -/)
  (proof := /-- Expand both conditional expectations using \cref{def:partite-conditional-expectation}. The $T$-fibers partition every positive-mass $S$-fiber. Within each $T$-fiber, the normalized weights sum to one, so interchanging the two finite sums leaves precisely the normalized weighted sum over the original $S$-fiber. If the $S$-fiber has zero mass, all three conditional expectations in the identity vanish. -/)
  (title := /-- Tower law for coordinate conditional expectations -/)
  (latexEnv := "lemma")]
lemma conditional_expectation_tower_local {d : ℕ} (X : partite_distribution d)
    (S T : Finset (Fin d)) (hST : S ⊆ T) (f : X.Face → ℝ) :
    partite_conditional_expectation X S
        (partite_conditional_expectation X T f) =
      partite_conditional_expectation X S f := by
  classical
  letI : Fintype X.Face := X.faceFintype
  have hagree_refl (x : X.Face) (U : Finset (Fin d)) :
      partite_agree_on X U x x := by
    intro i hi
    rfl
  have hagree_symm {x y : X.Face} {U : Finset (Fin d)}
      (h : partite_agree_on X U x y) : partite_agree_on X U y x := by
    intro i hi
    exact (h i hi).symm
  have hagree_trans {x y z : X.Face} {U : Finset (Fin d)}
      (hxy : partite_agree_on X U x y) (hyz : partite_agree_on X U y z) :
      partite_agree_on X U x z := by
    intro i hi
    exact (hxy i hi).trans (hyz i hi)
  have hagree_mono {x y : X.Face} (h : partite_agree_on X T x y) :
      partite_agree_on X S x y := by
    intro i hi
    exact h i (hST hi)
  have hmass_eq {x y : X.Face} (hxy : partite_agree_on X T x y) :
      partite_fiber_mass X T x = partite_fiber_mass X T y := by
    unfold partite_fiber_mass
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hux : partite_agree_on X T u x
    · have huy := hagree_trans hux hxy
      simp [hux, huy]
    · have huy : ¬partite_agree_on X T u y := by
        intro huy
        exact hux (hagree_trans huy (hagree_symm hxy))
      simp [hux, huy]
  have hweight_le_mass (x : X.Face) :
      X.weight x ≤ partite_fiber_mass X T x := by
    unfold partite_fiber_mass
    calc
      X.weight x = if partite_agree_on X T x x then X.weight x else 0 := by
        simp [hagree_refl]
      _ ≤ ∑ y, if partite_agree_on X T y x then X.weight y else 0 := by
        refine Finset.single_le_sum (s := Finset.univ)
          (f := fun y => if partite_agree_on X T y x then X.weight y else 0) ?_
          (Finset.mem_univ x)
        intro y hy
        by_cases h : partite_agree_on X T y x
        · simp [h, X.weight_nonnegative y]
        · simp [h]
  funext z
  unfold partite_conditional_expectation
  by_cases hmS : partite_fiber_mass X S z = 0
  · simp [hmS]
  simp only [hmS, if_false]
  congr 1
  simp only [mul_ite, mul_zero]
  calc
    (∑ y, if partite_agree_on X S y z then
        if partite_fiber_mass X T y = 0 then 0
        else X.weight y *
          ((∑ x, if partite_agree_on X T x y then X.weight x * f x else 0) /
            partite_fiber_mass X T y)
      else 0) =
        ∑ y, ∑ x, if partite_agree_on X S y z ∧
            partite_agree_on X T x y ∧ partite_fiber_mass X T y ≠ 0 then
          X.weight y * (X.weight x * f x) / partite_fiber_mass X T y else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hyz : partite_agree_on X S y z
      · by_cases hmy : partite_fiber_mass X T y = 0
        · simp [hyz, hmy]
        · simp only [hyz, hmy, if_true, if_false]
          rw [div_eq_mul_inv, ← mul_assoc, Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxy : partite_agree_on X T x y
          · simp [hxy, hmy, div_eq_mul_inv]
          · simp [hxy]
      · simp [hyz]
    _ = ∑ x, ∑ y, if partite_agree_on X S y z ∧
            partite_agree_on X T x y ∧ partite_fiber_mass X T y ≠ 0 then
          X.weight y * (X.weight x * f x) / partite_fiber_mass X T y else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x, if partite_agree_on X S x z then X.weight x * f x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxz : partite_agree_on X S x z
      · by_cases hmx : partite_fiber_mass X T x = 0
        · have hwx : X.weight x = 0 := by
            have := hweight_le_mass x
            rw [hmx] at this
            exact le_antisymm this (X.weight_nonnegative x)
          simp only [hxz, if_true, hwx, zero_mul]
          apply Finset.sum_eq_zero
          intro y hy
          by_cases hxy : partite_agree_on X T x y
          · have hmy : partite_fiber_mass X T y = 0 := by
              rw [← hmass_eq hxy, hmx]
            simp [hmy]
          · simp [hxy]
        · have hs_yz {y : X.Face} (hxy : partite_agree_on X T x y) :
              partite_agree_on X S y z :=
            hagree_trans (hagree_symm (hagree_mono hxy)) hxz
          calc
            (∑ y, if partite_agree_on X S y z ∧ partite_agree_on X T x y ∧
                partite_fiber_mass X T y ≠ 0 then
                X.weight y * (X.weight x * f x) / partite_fiber_mass X T y else 0) =
                ∑ y, if partite_agree_on X T y x then
                  X.weight y * (X.weight x * f x) / partite_fiber_mass X T x else 0 := by
              apply Finset.sum_congr rfl
              intro y hy
              by_cases hyx : partite_agree_on X T y x
              · have hxy := hagree_symm hyx
                have hmy : partite_fiber_mass X T y ≠ 0 := by
                  rw [← hmass_eq hxy]
                  exact hmx
                simp [hyx, hxy, hs_yz hxy, hmy, hmass_eq hxy]
              · have hxy : ¬partite_agree_on X T x y := by
                  intro hxy
                  exact hyx (hagree_symm hxy)
                simp [hyx, hxy]
            _ = partite_fiber_mass X T x *
                (X.weight x * f x) / partite_fiber_mass X T x := by
              unfold partite_fiber_mass
              rw [div_eq_mul_inv, Finset.sum_mul, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro y hy
              by_cases hyx : partite_agree_on X T y x <;>
                simp [hyx, div_eq_mul_inv]
            _ = X.weight x * f x := by field_simp
            _ = if partite_agree_on X S x z then X.weight x * f x else 0 := by
              simp [hxz]
      · simp only [hxz, if_false]
        apply Finset.sum_eq_zero
        intro y hy
        by_cases hxy : partite_agree_on X T x y
        · have hyz : ¬partite_agree_on X S y z := by
            intro hyz
            exact hxz (hagree_trans (hagree_mono hxy) hyz)
          simp [hyz]
        · simp [hxy]

@[blueprint "lem:conditional-expectation-sub-local"
  (statement := /-- Coordinate conditional expectation is linear over subtraction:
  \[
    E_S(f-g)=E_Sf-E_Sg.
  \] -/)
  (proof := /-- Expand \cref{def:partite-conditional-expectation}. On a positive-mass fiber, distribute the face weights over subtraction and use the finite-sum subtraction identity, then distribute division by the common fiber mass. On a zero-mass fiber all three terms vanish. -/)
  (title := /-- Subtraction linearity of coordinate conditioning -/)
  (latexEnv := "lemma")]
lemma conditional_expectation_sub_local {d : ℕ} (X : partite_distribution d)
    (S : Finset (Fin d)) (f g : X.Face → ℝ) :
    partite_conditional_expectation X S (fun x => f x - g x) = fun z =>
      partite_conditional_expectation X S f z -
        partite_conditional_expectation X S g z := by
  classical
  letI : Fintype X.Face := X.faceFintype
  funext z
  unfold partite_conditional_expectation
  by_cases hm : partite_fiber_mass X S z = 0
  · simp [hm]
  simp only [hm, if_false]
  rw [← sub_div]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxz : partite_agree_on X S x z
  · simp [hxz]
    ring
  · simp [hxz]

@[blueprint "lem:conditional-expectation-congr-positive-weight-local"
  (statement := /-- If two real functions on a finite partite distribution agree at every face of positive weight, then all of their coordinate conditional expectations agree pointwise. -/)
  (proof := /-- Expand \cref{def:partite-conditional-expectation}. Every numerator summand at a positive-weight face agrees by hypothesis, while a zero-weight face contributes zero for both functions. The fiber masses are identical, so the normalized sums agree in both the positive- and zero-mass cases. -/)
  (title := /-- Conditional expectation ignores null-face values -/)
  (latexEnv := "lemma")]
lemma conditional_expectation_congr_positive_weight_local {d : ℕ}
    (X : partite_distribution d) (S : Finset (Fin d)) (f g : X.Face → ℝ)
    (hfg : ∀ x, X.weight x ≠ 0 → f x = g x) :
    partite_conditional_expectation X S f =
      partite_conditional_expectation X S g := by
  classical
  letI : Fintype X.Face := X.faceFintype
  funext z
  unfold partite_conditional_expectation
  by_cases hm : partite_fiber_mass X S z = 0
  · simp [hm]
  simp only [hm, if_false]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hw : X.weight x = 0
  · simp [hw]
  · rw [hfg x hw]

@[blueprint "lem:conditional-expectation-fiber-constant-local"
  (statement := /-- If two faces $x,z$ agree on $S$, then $E_Sf(x)=E_Sf(z)$. -/)
  (proof := /-- Expand \cref{def:partite-conditional-expectation}. Agreement of $x$ and $z$ on $S$ makes the two fiber predicates equivalent for every face, so the fiber masses and weighted numerators coincide. The zero-mass branches therefore also coincide. -/)
  (title := /-- Conditional expectations are constant on fibers -/)
  (latexEnv := "lemma")]
lemma conditional_expectation_fiber_constant_local {d : ℕ}
    (X : partite_distribution d) (S : Finset (Fin d)) (f : X.Face → ℝ)
    (x z : X.Face) (hxz : partite_agree_on X S x z) :
    partite_conditional_expectation X S f x =
      partite_conditional_expectation X S f z := by
  classical
  letI : Fintype X.Face := X.faceFintype
  have heq (y : X.Face) :
      partite_agree_on X S y x ↔ partite_agree_on X S y z := by
    constructor
    · intro hy i hi
      exact (hy i hi).trans (hxz i hi)
    · intro hy i hi
      exact (hy i hi).trans (hxz i hi).symm
  have hmass : partite_fiber_mass X S x = partite_fiber_mass X S z := by
    unfold partite_fiber_mass
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h : partite_agree_on X S y x
    · simp [h, (heq y).mp h]
    · have h' : ¬partite_agree_on X S y z := fun h' => h ((heq y).mpr h')
      simp [h, h']
  unfold partite_conditional_expectation
  rw [hmass]
  by_cases hm : partite_fiber_mass X S z = 0
  · simp [hm]
  simp only [hm, if_false]
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases h : partite_agree_on X S y x
  · simp [h, (heq y).mp h]
  · have h' : ¬partite_agree_on X S y z := fun h' => h ((heq y).mpr h')
    simp [h, h']

@[blueprint "lem:conditional-expectation-reverse-tower-positive-local"
  (statement := /-- Let $S\subseteq T$. At every face $z$ of positive weight,
  \[
    E_T(E_Sf)(z)=E_Sf(z).
  \] -/)
  (proof := /-- The $T$-fiber of a positive-weight face has positive mass. Since $S\subseteq T$, \cref{lem:conditional-expectation-fiber-constant-local} shows that $E_Sf$ has the constant value $E_Sf(z)$ throughout this $T$-fiber. Expanding \cref{def:partite-conditional-expectation}, its normalized weighted average is therefore the same value. -/)
  (title := /-- Reverse tower law on positive-weight faces -/)
  (latexEnv := "lemma")]
lemma conditional_expectation_reverse_tower_positive_local {d : ℕ}
    (X : partite_distribution d) (S T : Finset (Fin d)) (hST : S ⊆ T)
    (f : X.Face → ℝ) (z : X.Face) (hwz : X.weight z ≠ 0) :
    partite_conditional_expectation X T
        (partite_conditional_expectation X S f) z =
      partite_conditional_expectation X S f z := by
  classical
  letI : Fintype X.Face := X.faceFintype
  have hweight_le_mass : X.weight z ≤ partite_fiber_mass X T z := by
    unfold partite_fiber_mass
    calc
      X.weight z = if partite_agree_on X T z z then X.weight z else 0 := by
        simp [partite_agree_on]
      _ ≤ ∑ x, if partite_agree_on X T x z then X.weight x else 0 := by
        refine Finset.single_le_sum (s := Finset.univ)
          (f := fun x => if partite_agree_on X T x z then X.weight x else 0) ?_
          (Finset.mem_univ z)
        intro x hx
        by_cases h : partite_agree_on X T x z
        · simp [h, X.weight_nonnegative x]
        · simp [h]
  have hwpos : 0 < X.weight z :=
    lt_of_le_of_ne (X.weight_nonnegative z) (Ne.symm hwz)
  have hmpos : 0 < partite_fiber_mass X T z :=
    lt_of_lt_of_le hwpos hweight_le_mass
  rw [partite_conditional_expectation]
  simp only [ne_of_gt hmpos, if_false]
  have hnum :
      (∑ x, if partite_agree_on X T x z then
          X.weight x * partite_conditional_expectation X S f x else 0) =
        partite_fiber_mass X T z * partite_conditional_expectation X S f z := by
    calc
      (∑ x, if partite_agree_on X T x z then
          X.weight x * partite_conditional_expectation X S f x else 0) =
          ∑ x, (if partite_agree_on X T x z then X.weight x else 0) *
            partite_conditional_expectation X S f z := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxz : partite_agree_on X T x z
        · have hsxz : partite_agree_on X S x z := fun i hi => hxz i (hST hi)
          rw [conditional_expectation_fiber_constant_local X S f x z hsxz]
          simp [hxz]
        · simp [hxz]
      _ = partite_fiber_mass X T z * partite_conditional_expectation X S f z := by
        rw [← Finset.sum_mul]
        rfl
  rw [hnum]
  field_simp

@[blueprint "lem:conditional-expectation-weighted-sum-local"
  (statement := /-- For every coordinate set $S$ and real function $f$ on a finite partite distribution,
  \[
    \sum_x\mu_X(x)E_Sf(x)=\sum_x\mu_X(x)f(x).
  \] -/)
  (proof := /-- Apply \cref{lem:conditional-expectation-tower-local} with the empty coordinate set below $S$. By \cref{def:partite-conditional-expectation}, conditioning on the empty set is the constant weighted average: its fiber has mass one by the normalization of the distribution. Evaluating the tower identity therefore gives the asserted equality. -/)
  (title := /-- Conditional expectation preserves the weighted sum -/)
  (latexEnv := "lemma")]
lemma conditional_expectation_weighted_sum_local {d : ℕ}
    (X : partite_distribution d) (S : Finset (Fin d)) (f : X.Face → ℝ) :
    letI : Fintype X.Face := X.faceFintype
    ∑ x, X.weight x * partite_conditional_expectation X S f x =
      ∑ x, X.weight x * f x := by
  classical
  letI : Fintype X.Face := X.faceFintype
  have huniv : (Finset.univ : Finset X.Face).Nonempty := by
    by_contra h
    have hempty : (Finset.univ : Finset X.Face) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp h
    have hsum := X.weight_sum_one
    rw [show (∑ x, X.weight x) = ∑ x ∈ (Finset.univ : Finset X.Face),
        X.weight x by simp, hempty] at hsum
    simp at hsum
  have ht := congrFun
    (conditional_expectation_tower_local X ∅ S (Finset.empty_subset S) f)
    huniv.choose
  simpa [partite_conditional_expectation, partite_fiber_mass,
    partite_agree_on, X.weight_sum_one] using ht

@[blueprint "def:partite-coordinate-fiber-average-local"
  (statement := /-- For a conditioning $x_S=z_S$, a coordinate $j$, and a real function $f$ on top faces, this is the conditional average of $f$ after additionally fixing $x_j=a$; it is zero when the refined fiber has zero mass. -/)
  (title := /-- Average on a refined coordinate fiber -/)
  (latexEnv := "definition")]
noncomputable def partite_coordinate_fiber_average_local {d : ℕ}
    (X : partite_distribution d) (S : Finset (Fin d)) (z : X.Face)
    (j : Fin d) (f : X.Face → ℝ) (a : X.Coord j) : ℝ := by
  classical
  letI : Fintype X.Face := X.faceFintype
  let m := conditioned_coordinate_mass X S z j a
  exact if m = 0 then 0 else
    (∑ x, if partite_agree_on X S x z ∧ X.coordinate x j = a
      then X.weight x * f x else 0) / m

@[blueprint "lem:coordinate-fiber-average-eq-conditional-local"
  (statement := /-- Let $x_S=z_S$. The average of $f$ on the fiber obtained by also fixing the $j$th coordinate to $x_j$ equals $E_{S\cup\{j\}}f(x)$. -/)
  (proof := /-- Expand \cref{def:partite-coordinate-fiber-average-local, def:partite-conditional-expectation}. Under the hypothesis $x_S=z_S$, a face agrees with $x$ on $S\cup\{j\}$ exactly when it agrees with $z$ on $S$ and has $j$th coordinate $x_j$. Consequently the two fiber masses and the two weighted numerators coincide, including in the zero-mass case. -/)
  (title := /-- Coordinate-fiber and face-fiber averages agree -/)
  (latexEnv := "lemma")]
lemma coordinate_fiber_average_eq_conditional_local {d : ℕ}
    (X : partite_distribution d) (S : Finset (Fin d)) (z x : X.Face)
    (j : Fin d) (f : X.Face → ℝ) (hxz : partite_agree_on X S x z) :
    partite_coordinate_fiber_average_local X S z j f (X.coordinate x j) =
      partite_conditional_expectation X (insert j S) f x := by
  classical
  letI : Fintype X.Face := X.faceFintype
  have heq (y : X.Face) :
      (partite_agree_on X S y z ∧ X.coordinate y j = X.coordinate x j) ↔
        partite_agree_on X (insert j S) y x := by
    constructor
    · rintro ⟨hyz, hj⟩ i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hj
      · exact (hyz i hi).trans (hxz i hi).symm
    · intro hyx
      constructor
      · intro i hi
        exact (hyx i (Finset.mem_insert_of_mem hi)).trans (hxz i hi)
      · exact hyx j (Finset.mem_insert_self j S)
  have hmass : conditioned_coordinate_mass X S z j (X.coordinate x j) =
      partite_fiber_mass X (insert j S) x := by
    unfold conditioned_coordinate_mass partite_fiber_mass
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h : partite_agree_on X S y z ∧ X.coordinate y j = X.coordinate x j
    · simp [h, (heq y).mp h]
    · have h' : ¬partite_agree_on X (insert j S) y x := fun h' => h ((heq y).mpr h')
      simp [h, h']
  unfold partite_coordinate_fiber_average_local partite_conditional_expectation
  rw [hmass]
  by_cases hm : partite_fiber_mass X (insert j S) x = 0
  · simp [hm]
  simp only [hm, if_false]
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases h : partite_agree_on X S y z ∧ X.coordinate y j = X.coordinate x j
  · simp [h, (heq y).mp h]
  · have h' : ¬partite_agree_on X (insert j S) y x := fun h' => h ((heq y).mpr h')
    simp [h, h']

@[blueprint "lem:coordinate-fiber-average-constant-local"
  (statement := /-- If $z$ and $z'$ lie in the same $S$-fiber, then the two functions on the $j$th coordinate obtained by averaging $f$ over the refined fibers $(z_S,x_j=a)$ and $(z'_S,x_j=a)$ are equal. -/)
  (proof := /-- Expand \cref{def:partite-coordinate-fiber-average-local}. Agreement of $z$ and $z'$ on $S$ makes the two fiber predicates equivalent for every face. Hence the conditioned coordinate masses and weighted numerators agree for every coordinate value, including when their common mass is zero. -/)
  (title := /-- Coordinate-fiber averages are constant on base fibers -/)
  (latexEnv := "lemma")]
lemma coordinate_fiber_average_constant_local {d : ℕ}
    (X : partite_distribution d) (S : Finset (Fin d)) (z z' : X.Face)
    (j : Fin d) (f : X.Face → ℝ) (hzz' : partite_agree_on X S z z') :
    partite_coordinate_fiber_average_local X S z j f =
      partite_coordinate_fiber_average_local X S z' j f := by
  classical
  letI : Fintype X.Face := X.faceFintype
  have heq (x : X.Face) :
      partite_agree_on X S x z ↔ partite_agree_on X S x z' := by
    constructor
    · intro hx i hi
      exact (hx i hi).trans (hzz' i hi)
    · intro hx i hi
      exact (hx i hi).trans (hzz' i hi).symm
  funext a
  have hmass : conditioned_coordinate_mass X S z j a =
      conditioned_coordinate_mass X S z' j a := by
    unfold conditioned_coordinate_mass
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : partite_agree_on X S x z
    · simp [h, (heq x).mp h]
    · have h' : ¬partite_agree_on X S x z' := fun h' => h ((heq x).mpr h')
      simp [h, h']
  unfold partite_coordinate_fiber_average_local
  rw [hmass]
  by_cases hm : conditioned_coordinate_mass X S z' j a = 0
  · simp [hm]
  simp only [hm, if_false]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : partite_agree_on X S x z
  · simp [h, (heq x).mp h]
  · have h' : ¬partite_agree_on X S x z' := fun h' => h ((heq x).mpr h')
    simp [h, h']

@[blueprint "lem:conditioned-marginal-deviation-composition-local"
  (statement := /-- Fix a base fiber $x_S=z_S$ and let $g(a)$ be the conditional average of $f$ after additionally fixing $x_j=a$. Then the conditioned $(i,j)$ marginal deviation evaluated at $z_i$ is
  \[
    (A_{i,j}^{S,z}-\Pi_{i,j}^{S,z})g(z_i)
      =E_{S\cup\{i\}}E_{S\cup\{j\}}f(z)-E_Sf(z).
  \] -/)
  (proof := /-- For the adjacency term, expand \cref{def:conditioned-marginal-average}. Its conditioning event is exactly the $(S\cup\{i\})$-fiber of $z$, and \cref{lem:coordinate-fiber-average-eq-conditional-local} identifies the integrand with $E_{S\cup\{j\}}f$. For the stationary term, the same bridge identifies its $S$-fiber average with $E_SE_{S\cup\{j\}}f(z)$; \cref{lem:conditional-expectation-tower-local} reduces this to $E_Sf(z)$. Subtracting the two identities and using \cref{def:conditioned-marginal-deviation} proves the formula. -/)
  (title := /-- Marginal deviation as a double-conditioning error -/)
  (latexEnv := "lemma")]
lemma conditioned_marginal_deviation_composition_local {d : ℕ}
    (X : partite_distribution d) (S : Finset (Fin d)) (z : X.Face)
    (i j : Fin d) (f : X.Face → ℝ) :
    conditioned_marginal_deviation X S z i j
        (partite_coordinate_fiber_average_local X S z j f) (X.coordinate z i) =
      partite_conditional_expectation X (insert i S)
          (partite_conditional_expectation X (insert j S) f) z -
        partite_conditional_expectation X S f z := by
  classical
  letI : Fintype X.Face := X.faceFintype
  let G := partite_coordinate_fiber_average_local X S z j f
  have heq_i (x : X.Face) :
      (partite_agree_on X S x z ∧ X.coordinate x i = X.coordinate z i) ↔
        partite_agree_on X (insert i S) x z := by
    constructor
    · rintro ⟨hxz, hi⟩ k hk
      rw [Finset.mem_insert] at hk
      rcases hk with rfl | hk
      · exact hi
      · exact hxz k hk
    · intro hxz
      exact ⟨fun k hk => hxz k (Finset.mem_insert_of_mem hk),
        hxz i (Finset.mem_insert_self i S)⟩
  have hmass_i : conditioned_coordinate_mass X S z i (X.coordinate z i) =
      partite_fiber_mass X (insert i S) z := by
    unfold conditioned_coordinate_mass partite_fiber_mass
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : partite_agree_on X S x z ∧ X.coordinate x i = X.coordinate z i
    · simp [h, (heq_i x).mp h]
    · have h' : ¬partite_agree_on X (insert i S) x z := fun h' => h ((heq_i x).mpr h')
      simp [h, h']
  have hmarginal :
      conditioned_marginal_average X S z i j G (X.coordinate z i) =
        partite_conditional_expectation X (insert i S)
          (partite_conditional_expectation X (insert j S) f) z := by
    unfold conditioned_marginal_average partite_conditional_expectation
    rw [hmass_i]
    by_cases hm : partite_fiber_mass X (insert i S) z = 0
    · simp [hm]
    simp only [hm, if_false]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : partite_agree_on X S x z ∧ X.coordinate x i = X.coordinate z i
    · have hbridge := coordinate_fiber_average_eq_conditional_local X S z x j f h.1
      simp only [h, (heq_i x).mp h, if_true]
      change X.weight x * G (X.coordinate x j) =
        X.weight x * partite_conditional_expectation X (insert j S) f x
      dsimp [G]
      rw [hbridge]
    · have h' : ¬partite_agree_on X (insert i S) x z := fun h' => h ((heq_i x).mpr h')
      simp [h, h']
  have hstationary : conditioned_stationary_average X S z j G =
      partite_conditional_expectation X S f z := by
    have havg : partite_conditional_expectation X S
        (fun x => G (X.coordinate x j)) z =
        partite_conditional_expectation X S
          (partite_conditional_expectation X (insert j S) f) z := by
      unfold partite_conditional_expectation
      by_cases hm : partite_fiber_mass X S z = 0
      · simp [hm]
      simp only [hm, if_false]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxz : partite_agree_on X S x z
      · have hbridge := coordinate_fiber_average_eq_conditional_local X S z x j f hxz
        simp only [hxz, if_true]
        change X.weight x * G (X.coordinate x j) =
          X.weight x * partite_conditional_expectation X (insert j S) f x
        dsimp [G]
        rw [hbridge]
      · simp [hxz]
    unfold conditioned_stationary_average
    rw [havg]
    exact congrFun (conditional_expectation_tower_local X S (insert j S)
      (Finset.subset_insert j S) f) z
  unfold conditioned_marginal_deviation
  rw [hmarginal, hstationary]

@[blueprint "lem:conditioned-marginal-deviation-constant-local"
  (statement := /-- If $z$ and $z'$ lie in the same $S$-fiber, then the conditioned $(i,j)$ marginal-deviation functions associated with the coordinate-fiber averages of a fixed face function $f$ are equal. -/)
  (proof := /-- By \cref{lem:coordinate-fiber-average-constant-local}, the two input functions on the $j$th coordinate coincide. Expanding \cref{def:conditioned-marginal-deviation, def:conditioned-marginal-average, def:conditioned-stationary-average}, agreement on $S$ also makes every conditioning predicate, fiber mass, and weighted numerator identical. Thus both the marginal and stationary terms agree for every value of the $i$th coordinate. -/)
  (title := /-- Marginal deviations are constant on base fibers -/)
  (latexEnv := "lemma")]
lemma conditioned_marginal_deviation_constant_local {d : ℕ}
    (X : partite_distribution d) (S : Finset (Fin d)) (z z' : X.Face)
    (i j : Fin d) (f : X.Face → ℝ) (hzz' : partite_agree_on X S z z') :
    conditioned_marginal_deviation X S z i j
        (partite_coordinate_fiber_average_local X S z j f) =
      conditioned_marginal_deviation X S z' i j
        (partite_coordinate_fiber_average_local X S z' j f) := by
  classical
  letI : Fintype X.Face := X.faceFintype
  have heq (x : X.Face) :
      partite_agree_on X S x z ↔ partite_agree_on X S x z' := by
    constructor
    · intro hx k hk
      exact (hx k hk).trans (hzz' k hk)
    · intro hx k hk
      exact (hx k hk).trans (hzz' k hk).symm
  have hG := coordinate_fiber_average_constant_local X S z z' j f hzz'
  have hcoord_mass (a : X.Coord i) : conditioned_coordinate_mass X S z i a =
      conditioned_coordinate_mass X S z' i a := by
    unfold conditioned_coordinate_mass
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : partite_agree_on X S x z
    · simp [h, (heq x).mp h]
    · have h' : ¬partite_agree_on X S x z' := fun h' => h ((heq x).mpr h')
      simp [h, h']
  have hmarginal (a : X.Coord i) :
      conditioned_marginal_average X S z i j
          (partite_coordinate_fiber_average_local X S z j f) a =
        conditioned_marginal_average X S z' i j
          (partite_coordinate_fiber_average_local X S z' j f) a := by
    unfold conditioned_marginal_average
    rw [hcoord_mass, hG]
    by_cases hm : conditioned_coordinate_mass X S z' i a = 0
    · simp [hm]
    simp only [hm, if_false]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : partite_agree_on X S x z
    · simp [h, (heq x).mp h]
    · have h' : ¬partite_agree_on X S x z' := fun h' => h ((heq x).mpr h')
      simp [h, h']
  have hstationary :
      conditioned_stationary_average X S z j
          (partite_coordinate_fiber_average_local X S z j f) =
        conditioned_stationary_average X S z' j
          (partite_coordinate_fiber_average_local X S z' j f) := by
    unfold conditioned_stationary_average partite_conditional_expectation
    rw [hG]
    have hmass : partite_fiber_mass X S z = partite_fiber_mass X S z' := by
      unfold partite_fiber_mass
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : partite_agree_on X S x z
      · simp [h, (heq x).mp h]
      · have h' : ¬partite_agree_on X S x z' := fun h' => h ((heq x).mpr h')
        simp [h, h']
    rw [hmass]
    by_cases hm : partite_fiber_mass X S z' = 0
    · simp [hm]
    simp only [hm, if_false]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : partite_agree_on X S x z
    · simp [h, (heq x).mp h]
    · have h' : ¬partite_agree_on X S x z' := fun h' => h ((heq x).mpr h')
      simp [h, h']
  funext a
  unfold conditioned_marginal_deviation
  rw [hmarginal, hstationary]

@[blueprint "lem:conditioned-coordinate-qnorm-global-local"
  (statement := /-- Let $q\geq1$. Suppose that a family $G_z$ of real functions on the $i$th coordinate is constant as $z$ varies within each $S$-fiber. Then
  \[
    \bigl\|z\mapsto G_z(z_i)\bigr\|_{q,X}
      =\bigl\|z\mapsto\|G_z\|_{q,i\mid S,z}\bigr\|_{q,X}.
  \] -/)
  (proof := /-- Expand the conditioned coordinate norm using \cref{def:conditioned-coordinate-qnorm}. Group the weighted sum on each $S$-fiber by the value of the $i$th coordinate; constancy of $G_z$ on the fiber identifies the resulting expression with the conditional expectation of $|G_z(z_i)|^q$. Raising its nonnegative $1/q$ power to the $q$th power recovers this conditional moment. Finally \cref{lem:conditional-expectation-weighted-sum-local} shows that integrating the conditional moment gives the original global moment, and \cref{def:partite-qnorm} yields the identity. -/)
  (title := /-- Disintegration of a conditioned coordinate q-norm -/)
  (latexEnv := "lemma")]
lemma conditioned_coordinate_qnorm_global_local {d : ℕ}
    (X : partite_distribution d) (q : ℝ) (hq : 1 ≤ q)
    (S : Finset (Fin d)) (i : Fin d) (G : X.Face → X.Coord i → ℝ)
    (hG : ∀ x z, partite_agree_on X S x z → G x = G z) :
    partite_qnorm X q (fun z => G z (X.coordinate z i)) =
    partite_qnorm X q
        (fun z => conditioned_coordinate_qnorm X S z i q (G z)) := by
  classical
  letI : Fintype X.Face := X.faceFintype
  letI : Fintype (X.Coord i) := X.coordFintype i
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  let F : X.Face → ℝ := fun x => |G x (X.coordinate x i)| ^ q
  have hmass_nonneg (z : X.Face) : 0 ≤ partite_fiber_mass X S z := by
    unfold partite_fiber_mass
    exact Finset.sum_nonneg fun x _ => by
      split_ifs
      · exact X.weight_nonnegative x
      · exact le_rfl
  have hcoord_mass_nonneg (z : X.Face) (a : X.Coord i) :
      0 ≤ conditioned_coordinate_mass X S z i a := by
    unfold conditioned_coordinate_mass
    exact Finset.sum_nonneg fun x _ => by
      split_ifs
      · exact X.weight_nonnegative x
      · exact le_rfl
  have hgroup (z : X.Face) :
      (∑ x, if partite_agree_on X S x z then X.weight x * F x else 0) =
        ∑ a, conditioned_coordinate_mass X S z i a * |G z a| ^ q := by
    have hreplace :
        (∑ x, if partite_agree_on X S x z then X.weight x * F x else 0) =
          ∑ x, if partite_agree_on X S x z then
            X.weight x * |G z (X.coordinate x i)| ^ q else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxz : partite_agree_on X S x z
      · have hfun := hG x z hxz
        simp only [hxz, if_true, F]
        rw [hfun]
      · simp [hxz]
    rw [hreplace]
    unfold conditioned_coordinate_mass
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hxz : partite_agree_on X S x z
    · simp [hxz]
    · simp [hxz]
  have hmoment (z : X.Face) :
      partite_conditional_expectation X S F z =
        if partite_fiber_mass X S z = 0 then 0 else
          ∑ a, conditioned_coordinate_mass X S z i a /
            partite_fiber_mass X S z * |G z a| ^ q := by
    unfold partite_conditional_expectation
    by_cases hm : partite_fiber_mass X S z = 0
    · simp [hm]
    simp only [hm, if_false]
    rw [hgroup]
    simp_rw [div_eq_mul_inv]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hpower (z : X.Face) :
      |conditioned_coordinate_qnorm X S z i q (G z)| ^ q =
        partite_conditional_expectation X S F z := by
    rw [hmoment]
    unfold conditioned_coordinate_qnorm
    by_cases hm : partite_fiber_mass X S z = 0
    · simp [hm, Real.zero_rpow (ne_of_gt hqpos)]
    have hmpos : 0 < partite_fiber_mass X S z :=
      lt_of_le_of_ne (hmass_nonneg z) (Ne.symm hm)
    let M := ∑ a, conditioned_coordinate_mass X S z i a /
      partite_fiber_mass X S z * |G z a| ^ q
    have hM : 0 ≤ M := Finset.sum_nonneg fun a _ =>
      mul_nonneg (div_nonneg (hcoord_mass_nonneg z a) hmpos.le)
        (Real.rpow_nonneg (abs_nonneg _) q)
    simp only [hm, if_false]
    change |M ^ (1 / q)| ^ q = M
    rw [abs_of_nonneg (Real.rpow_nonneg hM (1 / q)), ← Real.rpow_mul hM]
    have hmul : 1 / q * q = 1 := by field_simp
    rw [hmul, Real.rpow_one]
  unfold partite_qnorm
  apply congrArg (fun t : ℝ => t ^ (1 / q))
  calc
    (∑ z, X.weight z * |G z (X.coordinate z i)| ^ q) =
        ∑ z, X.weight z * F z := by rfl
    _ = ∑ z, X.weight z * partite_conditional_expectation X S F z :=
      (conditional_expectation_weighted_sum_local X S F).symm
    _ = ∑ z, X.weight z *
        |conditioned_coordinate_qnorm X S z i q (G z)| ^ q := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hpower]

@[blueprint "lem:partite-qnorm-congr-positive-weight-local"
  (statement := /-- Let $X$ be a finite partite distribution and let $g,h$ be real-valued on its top faces. If $g(x)=h(x)$ at every face of positive weight, then
  \[
    \|g\|_{q,X}=\|h\|_{q,X}
  \]
  for every real $q$. -/)
  (proof := /-- Expand the norm using \cref{def:partite-qnorm}. At a face of nonzero weight the two summands agree by hypothesis, while at a face of zero weight both weighted summands vanish. Thus the finite sums inside the two real powers are equal. -/)
  (title := /-- Weighted q-norm congruence off null faces -/)
  (latexEnv := "lemma")]
lemma partite_qnorm_congr_positive_weight_local {d : ℕ} (X : partite_distribution d)
    (q : ℝ) (g h : X.Face → ℝ)
    (heq : ∀ x, X.weight x ≠ 0 → g x = h x) :
    partite_qnorm X q g = partite_qnorm X q h := by
  classical
  letI : Fintype X.Face := X.faceFintype
  unfold partite_qnorm
  apply congrArg (fun t : ℝ => t ^ (1 / q))
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hw : X.weight x = 0
  · simp [hw]
  · rw [heq x hw]

@[blueprint "lem:partite-qnorm-mono-local"
  (statement := /-- Let $q\geq1$. If $|g(x)|\leq|h(x)|$ for every top face of a finite partite distribution, then
  \[
    \|g\|_{q,X}\leq\|h\|_{q,X}.
  \] -/)
  (proof := /-- Expand both norms using \cref{def:partite-qnorm}. Monotonicity of the nonnegative $q$th power gives the pointwise moment inequality; multiplication by the nonnegative face weights and summation preserve it. Monotonicity of the nonnegative $1/q$ power then gives the result. -/)
  (title := /-- Monotonicity of the weighted q-norm -/)
  (latexEnv := "lemma")]
lemma partite_qnorm_mono_local {d : ℕ} (X : partite_distribution d)
    (q : ℝ) (hq : 1 ≤ q) (g h : X.Face → ℝ)
    (hgh : ∀ x, |g x| ≤ |h x|) :
    partite_qnorm X q g ≤ partite_qnorm X q h := by
  classical
  letI : Fintype X.Face := X.faceFintype
  unfold partite_qnorm
  apply Real.rpow_le_rpow
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (X.weight_nonnegative x)
      (Real.rpow_nonneg (abs_nonneg _) q)
  · apply Finset.sum_le_sum
    intro x hx
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) (hgh x) (le_trans zero_le_one hq))
      (X.weight_nonnegative x)
  · positivity

@[blueprint "lem:partite-qnorm-nonnegative-mul-local"
  (statement := /-- Let $q>0$, let $c\geq0$, and let $g$ be real-valued on a finite partite distribution. Then
  \[
    \|cg\|_{q,X}=c\|g\|_{q,X}.
  \] -/)
  (proof := /-- Expand the norm using \cref{def:partite-qnorm}. Since $c\geq0$, the identities $|cg|=c|g|$ and $(c|g|)^q=c^q|g|^q$ factor $c^q$ from the weighted moment. The laws for nonnegative real powers and $q>0$ give $(c^q)^{1/q}=c$, proving the formula. -/)
  (title := /-- Nonnegative homogeneity of the weighted q-norm -/)
  (latexEnv := "lemma")]
lemma partite_qnorm_nonnegative_mul_local {d : ℕ} (X : partite_distribution d)
    (q c : ℝ) (hq : 0 < q) (hc : 0 ≤ c) (g : X.Face → ℝ) :
    partite_qnorm X q (fun x => c * g x) = c * partite_qnorm X q g := by
  classical
  letI : Fintype X.Face := X.faceFintype
  have hsum : 0 ≤ ∑ x, X.weight x * |g x| ^ q :=
    Finset.sum_nonneg fun x _ => mul_nonneg (X.weight_nonnegative x)
      (Real.rpow_nonneg (abs_nonneg _) q)
  unfold partite_qnorm
  change (∑ x, X.weight x * |c * g x| ^ q) ^ (1 / q) =
    c * (∑ x, X.weight x * |g x| ^ q) ^ (1 / q)
  have hinside : (∑ x, X.weight x * |c * g x| ^ q) =
      c ^ q * ∑ x, X.weight x * |g x| ^ q := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [abs_mul, abs_of_nonneg hc, Real.mul_rpow hc (abs_nonneg (g x))]
    ring
  rw [hinside, Real.mul_rpow (Real.rpow_nonneg hc q) hsum]
  have hroot : (c ^ q) ^ (1 / q) = c := by
    rw [← Real.rpow_mul hc]
    have hmul : q * (1 / q) = 1 := by field_simp
    rw [hmul, Real.rpow_one]
  rw [hroot]

@[blueprint "lem:partite-qnorm-add-le-local"
  (statement := /-- Let $q\geq1$ and let $g,h$ be real-valued on a finite partite distribution. Then
  \[
    \|g+h\|_{q,X}\leq\|g\|_{q,X}+\|h\|_{q,X}.
  \] -/)
  (proof := /-- Write $a=\|g\|_{q,X}$ and $b=\|h\|_{q,X}$. If either norm is zero, its function vanishes on every positive-weight face; \cref{lem:partite-qnorm-congr-positive-weight-local} reduces the result to equality. Otherwise normalize $|g|$ and $|h|$ by $a$ and $b$. The pointwise triangle inequality followed by \cref{lem:efron-weighted-rpow-mean-le}, with weights $a/(a+b)$ and $b/(a+b)$, bounds the $q$th moment of $(g+h)/(a+b)$ by one. The definitions of $a$ and $b$ identify the two normalized moments with one, and taking the nonnegative $1/q$ power proves the inequality. -/)
  (title := /-- Triangle inequality for the weighted q-norm -/)
  (latexEnv := "lemma")]
lemma partite_qnorm_add_le_local {d : ℕ} (X : partite_distribution d)
    (q : ℝ) (hq : 1 ≤ q) (g h : X.Face → ℝ) :
    partite_qnorm X q (fun x => g x + h x) ≤
      partite_qnorm X q g + partite_qnorm X q h := by
  classical
  letI : Fintype X.Face := X.faceFintype
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  let a := partite_qnorm X q g
  let b := partite_qnorm X q h
  have ha0 : 0 ≤ a := by
    dsimp [a, partite_qnorm]
    exact Real.rpow_nonneg (Finset.sum_nonneg fun x _ =>
      mul_nonneg (X.weight_nonnegative x)
        (Real.rpow_nonneg (abs_nonneg _) q)) (1 / q)
  have hb0 : 0 ≤ b := by
    dsimp [b, partite_qnorm]
    exact Real.rpow_nonneg (Finset.sum_nonneg fun x _ =>
      mul_nonneg (X.weight_nonnegative x)
        (Real.rpow_nonneg (abs_nonneg _) q)) (1 / q)
  have hzero_of_norm (u : X.Face → ℝ) (hu : partite_qnorm X q u = 0) :
      ∀ x, X.weight x ≠ 0 → u x = 0 := by
    intro x hw
    by_contra hux
    have hwpos : 0 < X.weight x :=
      lt_of_le_of_ne (X.weight_nonnegative x) (Ne.symm hw)
    have hterm : 0 < X.weight x * |u x| ^ q :=
      mul_pos hwpos (Real.rpow_pos_of_pos (abs_pos.mpr hux) q)
    have hraw : 0 < ∑ y, X.weight y * |u y| ^ q := by
      refine lt_of_lt_of_le hterm (Finset.single_le_sum
        (s := Finset.univ) (f := fun y => X.weight y * |u y| ^ q) ?_
        (Finset.mem_univ x))
      intro y hy
      exact mul_nonneg (X.weight_nonnegative y)
        (Real.rpow_nonneg (abs_nonneg _) q)
    unfold partite_qnorm at hu
    have hroot : 0 < (∑ y, X.weight y * |u y| ^ q) ^ (1 / q) :=
      Real.rpow_pos_of_pos hraw (1 / q)
    exact (ne_of_gt hroot) hu
  rcases eq_or_lt_of_le ha0 with ha | ha
  · have hga : ∀ x, X.weight x ≠ 0 → g x = 0 :=
      hzero_of_norm g (by simpa [a] using ha.symm)
    have heq := partite_qnorm_congr_positive_weight_local X q
      (fun x => g x + h x) h (fun x hx => by simp [hga x hx])
    rw [heq]
    dsimp [a, b] at ha ⊢
    linarith
  rcases eq_or_lt_of_le hb0 with hb | hb
  · have hhb : ∀ x, X.weight x ≠ 0 → h x = 0 :=
      hzero_of_norm h (by simpa [b] using hb.symm)
    have heq := partite_qnorm_congr_positive_weight_local X q
      (fun x => g x + h x) g (fun x hx => by simp [hhb x hx])
    rw [heq]
    dsimp [a, b] at hb ⊢
    linarith
  let c := a + b
  have hc : 0 < c := add_pos ha hb
  have hc0 : 0 ≤ c := hc.le
  have hraw_g : (∑ x, X.weight x * |g x| ^ q) = a ^ q := by
    dsimp [a, partite_qnorm]
    have hs : 0 ≤ ∑ x, X.weight x * |g x| ^ q :=
      Finset.sum_nonneg fun x _ => mul_nonneg (X.weight_nonnegative x)
        (Real.rpow_nonneg (abs_nonneg _) q)
    rw [← Real.rpow_mul hs]
    have hmul : 1 / q * q = 1 := by field_simp
    rw [hmul, Real.rpow_one]
  have hraw_h : (∑ x, X.weight x * |h x| ^ q) = b ^ q := by
    dsimp [b, partite_qnorm]
    have hs : 0 ≤ ∑ x, X.weight x * |h x| ^ q :=
      Finset.sum_nonneg fun x _ => mul_nonneg (X.weight_nonnegative x)
        (Real.rpow_nonneg (abs_nonneg _) q)
    rw [← Real.rpow_mul hs]
    have hmul : 1 / q * q = 1 := by field_simp
    rw [hmul, Real.rpow_one]
  let w : Bool → ℝ := fun t => if t then a / c else b / c
  have hw0 (t : Bool) : 0 ≤ w t := by
    cases t <;> simp [w, div_nonneg ha0 hc0, div_nonneg hb0 hc0]
  have hwsum : ∑ t, w t = 1 := by
    simp [w]
    field_simp
    rfl
  have hpoint (x : X.Face) :
      (|g x + h x| / c) ^ q ≤
        a / c * (|g x| / a) ^ q + b / c * (|h x| / b) ^ q := by
    let v : Bool → ℝ := fun t => if t then |g x| / a else |h x| / b
    have hv0 (t : Bool) : 0 ≤ v t := by
      cases t <;> simp [v, div_nonneg (abs_nonneg _) ha.le,
        div_nonneg (abs_nonneg _) hb.le]
    have hj := efron_weighted_rpow_mean_le q hq w v hw0 hv0 hwsum
    have habs : |g x + h x| / c ≤ ∑ t, w t * v t := by
      calc
        |g x + h x| / c ≤ (|g x| + |h x|) / c :=
          div_le_div_of_nonneg_right (abs_add_le (g x) (h x)) hc0
        _ = ∑ t, w t * v t := by
          simp [w, v]
          field_simp
    have hp := Real.rpow_le_rpow (by positivity) habs (le_trans zero_le_one hq)
    exact hp.trans (by simpa [w, v] using hj)
  have hnormalized :
      (∑ x, X.weight x * (|g x + h x| / c) ^ q) =
        (∑ x, X.weight x * |g x + h x| ^ q) / c ^ q := by
    simp_rw [Real.div_rpow (abs_nonneg _) hc0]
    simp_rw [div_eq_mul_inv, ← mul_assoc]
    rw [Finset.sum_mul]
  have htotal :
      (∑ x, X.weight x * (|g x + h x| / c) ^ q) ≤ 1 := by
    calc
      (∑ x, X.weight x * (|g x + h x| / c) ^ q) ≤
          ∑ x, X.weight x *
            (a / c * (|g x| / a) ^ q + b / c * (|h x| / b) ^ q) :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (hpoint x) (X.weight_nonnegative x)
      _ = a / c * ((∑ x, X.weight x * |g x| ^ q) / a ^ q) +
          b / c * ((∑ x, X.weight x * |h x| ^ q) / b ^ q) := by
        simp_rw [Real.div_rpow (abs_nonneg _) ha.le,
          Real.div_rpow (abs_nonneg _) hb.le]
        simp_rw [div_eq_mul_inv]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        apply congrArg₂ (· + ·)
        · calc
            (∑ x, X.weight x * (a * c⁻¹ * (|g x| ^ q * (a ^ q)⁻¹))) =
                ∑ x, (a * c⁻¹) * (X.weight x * |g x| ^ q) * (a ^ q)⁻¹ := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
            _ = (a * c⁻¹) * (∑ x, X.weight x * |g x| ^ q) * (a ^ q)⁻¹ := by
              rw [← Finset.sum_mul, ← Finset.mul_sum]
            _ = a * c⁻¹ * ((∑ x, X.weight x * |g x| ^ q) * (a ^ q)⁻¹) := by
              ring
        · calc
            (∑ x, X.weight x * (b * c⁻¹ * (|h x| ^ q * (b ^ q)⁻¹))) =
                ∑ x, (b * c⁻¹) * (X.weight x * |h x| ^ q) * (b ^ q)⁻¹ := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
            _ = (b * c⁻¹) * (∑ x, X.weight x * |h x| ^ q) * (b ^ q)⁻¹ := by
              rw [← Finset.sum_mul, ← Finset.mul_sum]
            _ = b * c⁻¹ * ((∑ x, X.weight x * |h x| ^ q) * (b ^ q)⁻¹) := by
              ring
      _ = 1 := by
        rw [hraw_g, hraw_h]
        field_simp
        ring
  rw [hnormalized] at htotal
  have hcq : 0 < c ^ q := Real.rpow_pos_of_pos hc q
  have hraw : (∑ x, X.weight x * |g x + h x| ^ q) ≤ c ^ q := by
    calc
      (∑ x, X.weight x * |g x + h x| ^ q) =
          c ^ q * ((∑ x, X.weight x * |g x + h x| ^ q) / c ^ q) := by
        field_simp [ne_of_gt hcq]
      _ ≤ c ^ q * 1 := mul_le_mul_of_nonneg_left htotal hcq.le
      _ = c ^ q := mul_one _
  unfold partite_qnorm
  have hroot := Real.rpow_le_rpow
    (Finset.sum_nonneg fun x _ => mul_nonneg (X.weight_nonnegative x)
      (Real.rpow_nonneg (abs_nonneg _) q)) hraw (by positivity : 0 ≤ 1 / q)
  have hcroot : (c ^ q) ^ (1 / q) = c := by
    rw [← Real.rpow_mul hc0]
    have hmul : q * (1 / q) = 1 := by field_simp
    rw [hmul, Real.rpow_one]
  rw [hcroot] at hroot
  simpa [c, a, b, partite_qnorm] using hroot

@[blueprint "lem:conditional-expectation-pair-qnorm-le-local"
  (statement := /-- Let $q\geq1$, let $\gamma\geq0$, and let $X$ be a finite $d$-partite $(q,\gamma)$-product. If $i\neq j$ and $i,j\notin S$, then every real function $f$ satisfies
  \[
    \bigl\|E_{S\cup\{i\}}E_{S\cup\{j\}}f-E_Sf\bigr\|_q
      \leq\gamma\|f\|_q.
  \] -/)
  (proof := /-- On each $S$-fiber let $G_z$ be the coordinate-fiber average from \cref{def:partite-coordinate-fiber-average-local} and let $H_z$ be its conditioned $(i,j)$ marginal deviation. The families $G_z$ and $H_z$ are constant on base fibers by \cref{lem:coordinate-fiber-average-constant-local, lem:conditioned-marginal-deviation-constant-local}. Hence \cref{lem:conditioned-coordinate-qnorm-global-local} identifies their diagonal global norms with the global norms of their conditioned coordinate norms. The defining inequality in \cref{def:is-q-gamma-product} bounds the latter for $H_z$ by $\gamma$ times those for $G_z$ on every positive-mass fiber; zero-mass fibers contribute zero. Apply \cref{lem:partite-qnorm-mono-local, lem:partite-qnorm-nonnegative-mul-local} to integrate this pointwise inequality. Finally \cref{lem:conditioned-marginal-deviation-composition-local} identifies the diagonal of $H_z$ with the displayed double-conditioning error, \cref{lem:coordinate-fiber-average-eq-conditional-local} identifies the diagonal of $G_z$ with $E_{S\cup\{j\}}f$, and \cref{lem:efron-conditional-qnorm-le} contracts the latter norm. -/)
  (title := /-- Two-coordinate conditional-expectation error -/)
  (latexEnv := "lemma")]
lemma conditional_expectation_pair_qnorm_le_local {d : ℕ}
    (X : partite_distribution d) (q γ : ℝ) (hq : 1 ≤ q) (hγ : 0 ≤ γ)
    (hproduct : is_q_gamma_product X q γ) (S : Finset (Fin d))
    (i j : Fin d) (hi : i ∉ S) (hj : j ∉ S) (hij : i ≠ j)
    (f : X.Face → ℝ) :
    partite_qnorm X q (fun z =>
      partite_conditional_expectation X (insert i S)
          (partite_conditional_expectation X (insert j S) f) z -
        partite_conditional_expectation X S f z) ≤
      γ * partite_qnorm X q f := by
  classical
  let G : X.Face → X.Coord j → ℝ := fun z =>
    partite_coordinate_fiber_average_local X S z j f
  let H : X.Face → X.Coord i → ℝ := fun z =>
    conditioned_marginal_deviation X S z i j (G z)
  have hG (x z : X.Face) (hxz : partite_agree_on X S x z) : G x = G z := by
    exact coordinate_fiber_average_constant_local X S x z j f hxz
  have hH (x z : X.Face) (hxz : partite_agree_on X S x z) : H x = H z := by
    exact conditioned_marginal_deviation_constant_local X S x z i j f hxz
  have hmass_nonneg (z : X.Face) : 0 ≤ partite_fiber_mass X S z := by
    unfold partite_fiber_mass
    letI : Fintype X.Face := X.faceFintype
    exact Finset.sum_nonneg fun x _ => by
      split_ifs
      · exact X.weight_nonnegative x
      · exact le_rfl
  have hcoord_nonneg (z : X.Face) (k : Fin d) (u : X.Coord k → ℝ) :
      0 ≤ conditioned_coordinate_qnorm X S z k q u := by
    by_cases hm : partite_fiber_mass X S z = 0
    · simp [conditioned_coordinate_qnorm, hm]
    have hmpos : 0 < partite_fiber_mass X S z :=
      lt_of_le_of_ne (hmass_nonneg z) (Ne.symm hm)
    simp only [conditioned_coordinate_qnorm, hm, if_false]
    apply Real.rpow_nonneg
    apply Finset.sum_nonneg
    intro a ha
    have hcm : 0 ≤ conditioned_coordinate_mass X S z k a := by
      unfold conditioned_coordinate_mass
      letI : Fintype X.Face := X.faceFintype
      exact Finset.sum_nonneg fun x _ => by
        split_ifs
        · exact X.weight_nonnegative x
        · exact le_rfl
    exact mul_nonneg (div_nonneg hcm hmpos.le)
      (Real.rpow_nonneg (abs_nonneg _) q)
  have hfiber (z : X.Face) :
      conditioned_coordinate_qnorm X S z i q (H z) ≤
        γ * conditioned_coordinate_qnorm X S z j q (G z) := by
    by_cases hm : partite_fiber_mass X S z = 0
    · simp [conditioned_coordinate_qnorm, hm, hγ]
    · exact hproduct S z i j hi hj hij
        (lt_of_le_of_ne (hmass_nonneg z) (Ne.symm hm)) (G z)
  have habs (z : X.Face) :
      |conditioned_coordinate_qnorm X S z i q (H z)| ≤
        |γ * conditioned_coordinate_qnorm X S z j q (G z)| := by
    rw [abs_of_nonneg (hcoord_nonneg z i (H z)),
      abs_of_nonneg (mul_nonneg hγ (hcoord_nonneg z j (G z)))]
    exact hfiber z
  have hGdiag : (fun z => G z (X.coordinate z j)) =
      partite_conditional_expectation X (insert j S) f := by
    funext z
    dsimp [G]
    exact coordinate_fiber_average_eq_conditional_local X S z z j f (by
      intro k hk
      rfl)
  have hHdiag : (fun z => H z (X.coordinate z i)) = fun z =>
      partite_conditional_expectation X (insert i S)
          (partite_conditional_expectation X (insert j S) f) z -
        partite_conditional_expectation X S f z := by
    funext z
    dsimp [H, G]
    exact conditioned_marginal_deviation_composition_local X S z i j f
  calc
    partite_qnorm X q (fun z =>
        partite_conditional_expectation X (insert i S)
            (partite_conditional_expectation X (insert j S) f) z -
          partite_conditional_expectation X S f z) =
        partite_qnorm X q (fun z => H z (X.coordinate z i)) := by rw [hHdiag]
    _ = partite_qnorm X q
        (fun z => conditioned_coordinate_qnorm X S z i q (H z)) :=
      conditioned_coordinate_qnorm_global_local X q hq S i H hH
    _ ≤ partite_qnorm X q (fun z =>
        γ * conditioned_coordinate_qnorm X S z j q (G z)) :=
      partite_qnorm_mono_local X q hq _ _ habs
    _ = γ * partite_qnorm X q
        (fun z => conditioned_coordinate_qnorm X S z j q (G z)) :=
      partite_qnorm_nonnegative_mul_local X q γ
        (lt_of_lt_of_le zero_lt_one hq) hγ _
    _ = γ * partite_qnorm X q (fun z => G z (X.coordinate z j)) := by
      rw [conditioned_coordinate_qnorm_global_local X q hq S j G hG]
    _ = γ * partite_qnorm X q (partite_conditional_expectation X (insert j S) f) := by
      rw [hGdiag]
    _ ≤ γ * partite_qnorm X q f :=
      mul_le_mul_of_nonneg_left
        (efron_conditional_qnorm_le X q hq (insert j S) f) hγ

@[blueprint "lem:conditional-expectation-one-coordinate-qnorm-le-local"
  (statement := /-- Let $q\geq1$, let $\gamma\geq0$, and let $X$ be a finite $(q,\gamma)$-product. Let $C$ be disjoint from $S$, let $i\notin S\cup C$, and suppose that $g$ is measurable with respect to $S\cup C$ on all positive-weight faces. Then
  \[
    \bigl\|E_{S\cup\{i\}}g-E_Sg\bigr\|_q
      \leq |C|\gamma\|g\|_q.
  \] -/)
  (proof := /-- Induct on $C$. For $C=\varnothing$, measurability and \cref{lem:conditional-expectation-reverse-tower-positive-local, lem:conditional-expectation-congr-positive-weight-local} show that both conditional expectations agree off null faces, so \cref{lem:partite-qnorm-congr-positive-weight-local} gives zero norm. For $C=C'\cup\{j\}$, put $U=S\cup C'$ and $g_0=E_Ug$. The difference for $g$ is the sum of the inductive difference for $g_0$ and the $E_{S\cup\{i\}}$-average of the $(i,j)$ error over $U$. This identity uses \cref{lem:conditional-expectation-sub-local, lem:conditional-expectation-tower-local} and null-face congruence. The latter error is bounded by \cref{lem:conditional-expectation-pair-qnorm-le-local} followed by \cref{lem:efron-conditional-qnorm-le}; the same contraction bounds $\|g_0\|_q$ by $\|g\|_q$. Apply the triangle inequality from \cref{lem:partite-qnorm-add-le-local} and the inductive hypothesis to obtain $(|C'|+1)\gamma\|g\|_q$. -/)
  (title := /-- One-coordinate conditioning against a measurable coordinate set -/)
  (latexEnv := "lemma")]
lemma conditional_expectation_one_coordinate_qnorm_le_local {d : ℕ}
    (X : partite_distribution d) (q γ : ℝ) (hq : 1 ≤ q) (hγ : 0 ≤ γ)
    (hproduct : is_q_gamma_product X q γ) (S C : Finset (Fin d))
    (i : Fin d) (hiS : i ∉ S) (hiC : i ∉ C) (hCS : Disjoint C S)
    (g : X.Face → ℝ)
    (hmeas : ∀ z, X.weight z ≠ 0 →
      partite_conditional_expectation X (S ∪ C) g z = g z) :
    partite_qnorm X q (fun z =>
      partite_conditional_expectation X (insert i S) g z -
        partite_conditional_expectation X S g z) ≤
      (C.card : ℝ) * γ * partite_qnorm X q g := by
  classical
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  induction C using Finset.induction_on generalizing g with
  | empty =>
      have hmeasS : ∀ z, X.weight z ≠ 0 →
          partite_conditional_expectation X S g z = g z := by
        simpa using hmeas
      have houter : partite_conditional_expectation X (insert i S) g =
          partite_conditional_expectation X (insert i S)
            (partite_conditional_expectation X S g) :=
        conditional_expectation_congr_positive_weight_local X (insert i S) g
          (partite_conditional_expectation X S g)
          (fun z hz => (hmeasS z hz).symm)
      have hzero (z : X.Face) (hz : X.weight z ≠ 0) :
          partite_conditional_expectation X (insert i S) g z -
            partite_conditional_expectation X S g z = 0 := by
        rw [congrFun houter z,
          conditional_expectation_reverse_tower_positive_local X S (insert i S)
            (Finset.subset_insert i S) g z hz]
        ring
      have hnorm := partite_qnorm_congr_positive_weight_local X q
        (fun z => partite_conditional_expectation X (insert i S) g z -
          partite_conditional_expectation X S g z) (fun _ => 0) hzero
      rw [hnorm]
      unfold partite_qnorm
      simp [Real.zero_rpow (ne_of_gt hqpos)]
      rw [Real.zero_rpow (inv_ne_zero (ne_of_gt hqpos))]
  | @insert j C hjC ih =>
      have hiC' : i ∉ C := fun hi => hiC (Finset.mem_insert_of_mem hi)
      have hij : i ≠ j := by
        intro hij
        subst j
        exact hiC (Finset.mem_insert_self i C)
      have hjS : j ∉ S := by
        intro hj
        exact (Finset.disjoint_left.mp hCS) (Finset.mem_insert_self j C) hj
      have hCS' : Disjoint C S := by
        rw [Finset.disjoint_left]
        intro k hkC hkS
        exact (Finset.disjoint_left.mp hCS) (Finset.mem_insert_of_mem hkC) hkS
      let U := S ∪ C
      let g0 := partite_conditional_expectation X U g
      have hiU : i ∉ U := by simp [U, hiS, hiC']
      have hjU : j ∉ U := by simp [U, hjS, hjC]
      have hmeas0 : ∀ z, X.weight z ≠ 0 →
          partite_conditional_expectation X (S ∪ C) g0 z = g0 z := by
        intro z hz
        dsimp [g0, U]
        exact congrFun (conditional_expectation_tower_local X (S ∪ C) (S ∪ C)
          Finset.Subset.rfl g) z
      have hind := ih hiC' hCS' g0 hmeas0
      let P : X.Face → ℝ := fun z =>
        partite_conditional_expectation X (insert i U)
            (partite_conditional_expectation X (insert j U) g) z -
          partite_conditional_expectation X U g z
      have hmeas_top : ∀ z, X.weight z ≠ 0 →
          partite_conditional_expectation X (insert j U) g z = g z := by
        intro z hz
        simpa [U, Finset.union_insert] using hmeas z hz
      have htop : partite_conditional_expectation X (insert i S)
          (partite_conditional_expectation X (insert j U) g) =
          partite_conditional_expectation X (insert i S) g :=
        conditional_expectation_congr_positive_weight_local X (insert i S)
          (partite_conditional_expectation X (insert j U) g) g hmeas_top
      have hsubset : insert i S ⊆ insert i U :=
        Finset.insert_subset_insert i (Finset.subset_union_left)
      have hfirst : partite_conditional_expectation X (insert i S) P = fun z =>
          partite_conditional_expectation X (insert i S) g z -
            partite_conditional_expectation X (insert i S) g0 z := by
        rw [conditional_expectation_sub_local]
        change partite_conditional_expectation X (insert i S)
            (partite_conditional_expectation X (insert i U)
              (partite_conditional_expectation X (insert j U) g)) -
            partite_conditional_expectation X (insert i S)
              (partite_conditional_expectation X U g) = _
        rw [conditional_expectation_tower_local X (insert i S) (insert i U)
          hsubset (partite_conditional_expectation X (insert j U) g), htop]
        rfl
      have hpair : partite_qnorm X q P ≤ γ * partite_qnorm X q g := by
        exact conditional_expectation_pair_qnorm_le_local X q γ hq hγ hproduct U
          i j hiU hjU hij g
      have hfirst_bound : partite_qnorm X q (fun z =>
          partite_conditional_expectation X (insert i S) g z -
            partite_conditional_expectation X (insert i S) g0 z) ≤
          γ * partite_qnorm X q g := by
        rw [← hfirst]
        exact (efron_conditional_qnorm_le X q hq (insert i S) P).trans hpair
      have hg0 : partite_qnorm X q g0 ≤ partite_qnorm X q g := by
        exact efron_conditional_qnorm_le X q hq U g
      have hcoef : 0 ≤ (C.card : ℝ) * γ := mul_nonneg (by positivity) hγ
      have hind' : partite_qnorm X q (fun z =>
          partite_conditional_expectation X (insert i S) g0 z -
            partite_conditional_expectation X S g0 z) ≤
          (C.card : ℝ) * γ * partite_qnorm X q g :=
        hind.trans (mul_le_mul_of_nonneg_left hg0 hcoef)
      have hcoarse : partite_conditional_expectation X S g0 =
          partite_conditional_expectation X S g := by
        dsimp [g0, U]
        exact conditional_expectation_tower_local X S (S ∪ C)
          Finset.subset_union_left g
      have hdecomp : (fun z =>
          partite_conditional_expectation X (insert i S) g z -
            partite_conditional_expectation X S g z) = fun z =>
          (partite_conditional_expectation X (insert i S) g z -
            partite_conditional_expectation X (insert i S) g0 z) +
          (partite_conditional_expectation X (insert i S) g0 z -
            partite_conditional_expectation X S g0 z) := by
        funext z
        rw [congrFun hcoarse z]
        ring
      rw [hdecomp]
      calc
        partite_qnorm X q (fun z =>
            (partite_conditional_expectation X (insert i S) g z -
              partite_conditional_expectation X (insert i S) g0 z) +
            (partite_conditional_expectation X (insert i S) g0 z -
              partite_conditional_expectation X S g0 z)) ≤
            partite_qnorm X q (fun z =>
              partite_conditional_expectation X (insert i S) g z -
                partite_conditional_expectation X (insert i S) g0 z) +
            partite_qnorm X q (fun z =>
              partite_conditional_expectation X (insert i S) g0 z -
                partite_conditional_expectation X S g0 z) :=
          partite_qnorm_add_le_local X q hq _ _
        _ ≤ γ * partite_qnorm X q g +
            (C.card : ℝ) * γ * partite_qnorm X q g :=
          add_le_add hfirst_bound hind'
        _ = ((insert j C).card : ℝ) * γ * partite_qnorm X q g := by
          rw [Finset.card_insert_of_notMem hjC]
          push_cast
          ring

@[blueprint "lem:conditional-expectation-composition-qnorm-le"
  (statement := /-- Let $q\geq1$, let $\gamma\geq0$, and let $X$ be a finite $d$-partite $(q,\gamma)$-product. For all coordinate sets $A,B\subseteq[d]$ and every real-valued function $f$ on the top faces of $X$,
  \[
    \bigl\|E_AE_Bf-E_{A\cap B}f\bigr\|_q
      \leq |A|\,|B|\,\gamma\|f\|_q.
  \] -/)
  (proof := /-- Put $g=E_Bf$, $I=A\cap B$, and $C=A\setminus B$. We first prove by induction on a finite set $C'$ disjoint from a base set $S$ and from $B$ that
  \[
    \|E_{S\cup C'}g-E_Sg\|_q
      \leq |C'|\,|B|\,\gamma\|f\|_q.
  \]
  The empty case is zero by \cref{lem:partite-qnorm-congr-positive-weight-local}. For the induction step $C'=C''\cup\{i\}$, set $U=S\cup C''$ and $D=B\setminus U$. Since $g=E_Bf$ and $B\subseteq U\cup D$, \cref{lem:conditional-expectation-reverse-tower-positive-local} shows that $g$ is measurable with respect to $U\cup D$ on every positive-weight face. Therefore \cref{lem:conditional-expectation-one-coordinate-qnorm-le-local} gives
  \[
    \|E_{U\cup\{i\}}g-E_Ug\|_q
      \leq |D|\gamma\|g\|_q
      \leq |B|\gamma\|f\|_q,
  \]
  where the last inequality uses $D\subseteq B$ and the contraction \cref{lem:efron-conditional-qnorm-le}. Add the inductive difference using \cref{lem:partite-qnorm-add-le-local}; this proves the displayed induction claim.

  Apply the claim with $S=I$ and $C'=C$. The sets are disjoint, $I\cup C=A$, and $|C|\leq|A|$. Finally $I\subseteq B$, so \cref{lem:conditional-expectation-tower-local} gives $E_Ig=E_IE_Bf=E_If$. Substitution and the nonnegativity of $\gamma$ and the weighted norm yield the required $|A|\,|B|\gamma\|f\|_q$ bound. -/)
  (title := /-- Approximate composition of coordinate conditional expectations -/)
  (latexEnv := "lemma")]
lemma conditional_expectation_composition_qnorm_le {d : ℕ}
    (X : partite_distribution d) (q γ : ℝ) (hq : 1 ≤ q) (hγ : 0 ≤ γ)
    (hproduct : is_q_gamma_product X q γ) (A B : Finset (Fin d))
    (f : X.Face → ℝ) :
    partite_qnorm X q (fun z =>
      partite_conditional_expectation X A
          (partite_conditional_expectation X B f) z -
        partite_conditional_expectation X (A ∩ B) f z) ≤
      (A.card : ℝ) * (B.card : ℝ) * γ * partite_qnorm X q f := by
  classical
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hnorm_nonneg (u : X.Face → ℝ) : 0 ≤ partite_qnorm X q u := by
    unfold partite_qnorm
    letI : Fintype X.Face := X.faceFintype
    exact Real.rpow_nonneg (Finset.sum_nonneg fun x _ =>
      mul_nonneg (X.weight_nonnegative x)
        (Real.rpow_nonneg (abs_nonneg _) q)) (1 / q)
  let g := partite_conditional_expectation X B f
  have hg : partite_qnorm X q g ≤ partite_qnorm X q f := by
    exact efron_conditional_qnorm_le X q hq B f
  have htel : ∀ (S C : Finset (Fin d)), Disjoint C S → Disjoint C B →
      partite_qnorm X q (fun z =>
        partite_conditional_expectation X (S ∪ C) g z -
          partite_conditional_expectation X S g z) ≤
        (C.card : ℝ) * (B.card : ℝ) * γ * partite_qnorm X q f := by
    intro S C hCS hCB
    induction C using Finset.induction_on with
    | empty =>
        simp only [Finset.union_empty, Nat.cast_zero, zero_mul]
        have hzero := partite_qnorm_congr_positive_weight_local X q
          (fun z => partite_conditional_expectation X S g z -
            partite_conditional_expectation X S g z) (fun _ => 0)
          (fun z hz => by ring)
        rw [hzero]
        unfold partite_qnorm
        simp [Real.zero_rpow (ne_of_gt hqpos)]
        rw [Real.zero_rpow (inv_ne_zero (ne_of_gt hqpos))]
    | @insert i C hiC ih =>
        have hiS : i ∉ S := by
          intro hi
          exact (Finset.disjoint_left.mp hCS) (Finset.mem_insert_self i C) hi
        have hiB : i ∉ B := by
          intro hi
          exact (Finset.disjoint_left.mp hCB) (Finset.mem_insert_self i C) hi
        have hCS' : Disjoint C S := by
          rw [Finset.disjoint_left]
          intro k hkC hkS
          exact (Finset.disjoint_left.mp hCS) (Finset.mem_insert_of_mem hkC) hkS
        have hCB' : Disjoint C B := by
          rw [Finset.disjoint_left]
          intro k hkC hkB
          exact (Finset.disjoint_left.mp hCB) (Finset.mem_insert_of_mem hkC) hkB
        have hind := ih hCS' hCB'
        let U := S ∪ C
        let D := B \ U
        have hiU : i ∉ U := by
          simp [U, hiS, hiC]
        have hiD : i ∉ D := by
          intro hi
          exact hiB (Finset.mem_sdiff.mp hi).1
        have hDU : Disjoint D U := by
          rw [Finset.disjoint_left]
          intro k hkD hkU
          exact (Finset.mem_sdiff.mp hkD).2 hkU
        have hBsub : B ⊆ U ∪ D := by
          intro k hkB
          by_cases hkU : k ∈ U
          · exact Finset.mem_union_left D hkU
          · exact Finset.mem_union_right U (Finset.mem_sdiff.mpr ⟨hkB, hkU⟩)
        have hmeas : ∀ z, X.weight z ≠ 0 →
            partite_conditional_expectation X (U ∪ D) g z = g z := by
          intro z hz
          dsimp [g]
          exact conditional_expectation_reverse_tower_positive_local X B (U ∪ D)
            hBsub f z hz
        have hone := conditional_expectation_one_coordinate_qnorm_le_local
          X q γ hq hγ hproduct U D i hiU hiD hDU g hmeas
        have hDcard : (D.card : ℝ) ≤ (B.card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : B \ U ⊆ B)
        have hcoefD : 0 ≤ (D.card : ℝ) * γ := mul_nonneg (by positivity) hγ
        have hgamma_norm : 0 ≤ γ * partite_qnorm X q f :=
          mul_nonneg hγ (hnorm_nonneg f)
        have hone' : partite_qnorm X q (fun z =>
            partite_conditional_expectation X (insert i U) g z -
              partite_conditional_expectation X U g z) ≤
            (B.card : ℝ) * γ * partite_qnorm X q f := by
          calc
            partite_qnorm X q (fun z =>
                partite_conditional_expectation X (insert i U) g z -
                  partite_conditional_expectation X U g z) ≤
                (D.card : ℝ) * γ * partite_qnorm X q g := hone
            _ ≤ (D.card : ℝ) * γ * partite_qnorm X q f :=
              mul_le_mul_of_nonneg_left hg hcoefD
            _ ≤ (B.card : ℝ) * γ * partite_qnorm X q f := by
              nlinarith
        have hunion : S ∪ insert i C = insert i U := by
          ext k
          simp [U]
        have hdecomp : (fun z =>
            partite_conditional_expectation X (S ∪ insert i C) g z -
              partite_conditional_expectation X S g z) = fun z =>
            (partite_conditional_expectation X (insert i U) g z -
              partite_conditional_expectation X U g z) +
            (partite_conditional_expectation X U g z -
              partite_conditional_expectation X S g z) := by
          funext z
          rw [hunion]
          ring
        rw [hdecomp]
        calc
          partite_qnorm X q (fun z =>
              (partite_conditional_expectation X (insert i U) g z -
                partite_conditional_expectation X U g z) +
              (partite_conditional_expectation X U g z -
                partite_conditional_expectation X S g z)) ≤
              partite_qnorm X q (fun z =>
                partite_conditional_expectation X (insert i U) g z -
                  partite_conditional_expectation X U g z) +
              partite_qnorm X q (fun z =>
                partite_conditional_expectation X U g z -
                  partite_conditional_expectation X S g z) :=
            partite_qnorm_add_le_local X q hq _ _
          _ ≤ (B.card : ℝ) * γ * partite_qnorm X q f +
              (C.card : ℝ) * (B.card : ℝ) * γ * partite_qnorm X q f :=
            add_le_add hone' hind
          _ = ((insert i C).card : ℝ) * (B.card : ℝ) * γ *
              partite_qnorm X q f := by
            rw [Finset.card_insert_of_notMem hiC]
            push_cast
            ring
  let I := A ∩ B
  let C := A \ B
  have hCI : Disjoint C I := by
    rw [Finset.disjoint_left]
    intro k hkC hkI
    exact (Finset.mem_sdiff.mp hkC).2 (Finset.mem_inter.mp hkI).2
  have hCB : Disjoint C B := by
    rw [Finset.disjoint_left]
    intro k hkC hkB
    exact (Finset.mem_sdiff.mp hkC).2 hkB
  have hA : I ∪ C = A := by
    ext k
    simp [I, C]
    tauto
  have hI : I ⊆ B := by
    intro k hk
    exact (Finset.mem_inter.mp hk).2
  have hbase : partite_conditional_expectation X I g =
      partite_conditional_expectation X I f := by
    dsimp [g]
    exact conditional_expectation_tower_local X I B hI f
  have hmain := htel I C hCI hCB
  rw [hA, hbase] at hmain
  have hCcard : (C.card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : A \ B ⊆ A)
  have hright : 0 ≤ (B.card : ℝ) * γ * partite_qnorm X q f :=
    mul_nonneg (mul_nonneg (by positivity) hγ) (hnorm_nonneg f)
  refine hmain.trans ?_
  calc
    (C.card : ℝ) * (B.card : ℝ) * γ * partite_qnorm X q f =
        (C.card : ℝ) * ((B.card : ℝ) * γ * partite_qnorm X q f) := by ring
    _ ≤ (A.card : ℝ) * ((B.card : ℝ) * γ * partite_qnorm X q f) :=
      mul_le_mul_of_nonneg_right hCcard hright
    _ = (A.card : ℝ) * (B.card : ℝ) * γ * partite_qnorm X q f := by ring

@[blueprint "lem:scalar-noise-inverse-powerset-insert"
  (statement := /-- If $a\notin s$, then every sum over the subsets of $s\cup\{a\}$ splits into the sum over subsets of $s$ and the sum over those subsets with $a$ adjoined. -/)
  (proof := /-- The powerset of $s\cup\{a\}$ is the disjoint union of the powerset of $s$ and the image of that powerset under $t\mapsto t\cup\{a\}$. The image map is injective because no subset of $s$ contains $a$. Summing over this disjoint union gives the identity. -/)
  (title := /-- Splitting a powerset sum at one element -/)
  (latexEnv := "lemma")]
lemma scalar_noise_inverse_powerset_insert {α M : Type} [DecidableEq α]
    [AddCommMonoid M] (a : α) (s : Finset α) (ha : a ∉ s)
    (f : Finset α → M) :
    ∑ t ∈ (insert a s).powerset, f t =
      (∑ t ∈ s.powerset, f t) + ∑ t ∈ s.powerset, f (insert a t) := by
  rw [Finset.powerset_insert]
  have hd : Disjoint s.powerset (s.powerset.image (insert a)) := by
    rw [Finset.disjoint_left]
    intro u hu himage
    rw [Finset.mem_image] at himage
    obtain ⟨v, hv, rfl⟩ := himage
    exact ha ((Finset.mem_powerset.mp hu) (Finset.mem_insert_self a v))
  rw [Finset.sum_union hd, Finset.sum_image]
  intro u hu v hv huv
  have hau : a ∉ u := fun h => ha ((Finset.mem_powerset.mp hu) h)
  have hav : a ∉ v := fun h => ha ((Finset.mem_powerset.mp hv) h)
  calc
    u = (insert a u).erase a := by simp [hau]
    _ = (insert a v).erase a := congrArg (Finset.erase · a) huv
    _ = v := by simp [hav]

@[blueprint "lem:scalar-noise-inverse-mobius-insert"
  (statement := /-- If $a\notin s$, the signed Möbius transform on $s\cup\{a\}$ is
  \[
    \sum_{T\subseteq s\cup\{a\}}(-1)^{|s\cup\{a\}|-|T|}g(T)
      =\sum_{T\subseteq s}(-1)^{|s|-|T|}\bigl(g(T\cup\{a\})-g(T)\bigr).
  \] -/)
  (proof := /-- Apply \cref{lem:scalar-noise-inverse-powerset-insert}. For a subset not containing $a$, insertion of $a$ raises the outer cardinality by one and hence negates its coefficient. For a subset containing $a$, both cardinalities rise by one, so its coefficient is unchanged. Combining the two sums yields the displayed difference. -/)
  (title := /-- Möbius transform under insertion -/)
  (latexEnv := "lemma")]
lemma scalar_noise_inverse_mobius_insert {α : Type} [DecidableEq α]
    (a : α) (s : Finset α) (ha : a ∉ s) (g : Finset α → ℝ) :
    ∑ T ∈ (insert a s).powerset,
        (-1 : ℝ) ^ ((insert a s).card - T.card) * g T =
      ∑ T ∈ s.powerset,
        (-1 : ℝ) ^ (s.card - T.card) * (g (insert a T) - g T) := by
  rw [scalar_noise_inverse_powerset_insert a s ha]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hinsert :
      (∑ T ∈ s.powerset,
        (-1 : ℝ) ^ ((insert a s).card - (insert a T).card) *
          g (insert a T)) =
        ∑ T ∈ s.powerset,
          (-1 : ℝ) ^ (s.card - T.card) * g (insert a T) := by
    apply Finset.sum_congr rfl
    intro T hT
    have haT : a ∉ T := fun h => ha ((Finset.mem_powerset.mp hT) h)
    rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haT]
    congr 2
    omega
  have hplain :
      (∑ T ∈ s.powerset,
        (-1 : ℝ) ^ ((insert a s).card - T.card) * g T) =
        -(∑ T ∈ s.powerset,
          (-1 : ℝ) ^ (s.card - T.card) * g T) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro T hT
    have hle : T.card ≤ s.card :=
      Finset.card_le_card (Finset.mem_powerset.mp hT)
    rw [Finset.card_insert_of_notMem ha]
    have hsub : s.card + 1 - T.card = s.card - T.card + 1 := by omega
    rw [hsub, pow_succ]
    ring
  rw [hplain, hinsert]
  ring

@[blueprint "lem:scalar-noise-inverse-signed-mobius-expansion"
  (statement := /-- Let $s$ be finite, let $r:s\to\mathbb R$, and let $g$ be real-valued on subsets of $s$. Then
  \[
    \sum_{S\subseteq s}r_S\sum_{T\subseteq S}(-1)^{|S|-|T|}g(T)
      =\sum_{T\subseteq s}r_T\prod_{i\in s\setminus T}(1-r_i)g(T).
  \] -/)
  (proof := /-- Induct on $s$. Split both outer powerset sums using \cref{lem:scalar-noise-inverse-powerset-insert}, and rewrite the Möbius transform of every subset containing the new element using \cref{lem:scalar-noise-inverse-mobius-insert}. After separating the new coordinate, both sides are $(1-r_a)$ times the induction hypothesis for $g$ plus $r_a$ times the induction hypothesis for $T\mapsto g(T\cup\{a\})$. -/)
  (title := /-- Signed finite Möbius expansion -/)
  (latexEnv := "lemma")]
lemma scalar_noise_inverse_signed_mobius_expansion {α : Type} [DecidableEq α]
    (s : Finset α) (r : α → ℝ) (g : Finset α → ℝ) :
    ∑ S ∈ s.powerset, (∏ i ∈ S, r i) *
        (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * g T) =
      ∑ T ∈ s.powerset,
        (∏ i ∈ T, r i) * (∏ i ∈ s \ T, (1 - r i)) * g T := by
  induction s using Finset.induction_on generalizing g with
  | empty => simp
  | @insert a s ha ih =>
      rw [scalar_noise_inverse_powerset_insert a s ha]
      rw [scalar_noise_inverse_powerset_insert a s ha]
      have hleft :
          (∑ t ∈ s.powerset, (∏ i ∈ insert a t, r i) *
            (∑ T ∈ (insert a t).powerset,
              (-1 : ℝ) ^ ((insert a t).card - T.card) * g T)) =
            r a *
              ((∑ t ∈ s.powerset, (∏ i ∈ t, r i) *
                (∑ T ∈ t.powerset,
                  (-1 : ℝ) ^ (t.card - T.card) * g (insert a T))) -
              ∑ t ∈ s.powerset, (∏ i ∈ t, r i) *
                (∑ T ∈ t.powerset,
                  (-1 : ℝ) ^ (t.card - T.card) * g T)) := by
        calc
          _ = ∑ t ∈ s.powerset, r a * (∏ i ∈ t, r i) *
              ((∑ T ∈ t.powerset,
                (-1 : ℝ) ^ (t.card - T.card) * g (insert a T)) -
              ∑ T ∈ t.powerset,
                (-1 : ℝ) ^ (t.card - T.card) * g T) := by
                apply Finset.sum_congr rfl
                intro t ht
                have hat : a ∉ t := fun h =>
                  ha ((Finset.mem_powerset.mp ht) h)
                rw [Finset.prod_insert hat,
                  scalar_noise_inverse_mobius_insert a t hat]
                simp_rw [mul_sub]
                rw [Finset.sum_sub_distrib]
                ring
          _ = _ := by
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib]
            simp only [mul_assoc]
            rw [← Finset.mul_sum, ← Finset.mul_sum]
      have hright₁ :
          (∑ t ∈ s.powerset,
            (∏ i ∈ t, r i) * (∏ i ∈ insert a s \ t, (1 - r i)) * g t) =
            (1 - r a) *
              ∑ t ∈ s.powerset,
                (∏ i ∈ t, r i) * (∏ i ∈ s \ t, (1 - r i)) * g t := by
        calc
          _ = ∑ t ∈ s.powerset,
              (1 - r a) * ((∏ i ∈ t, r i) *
                (∏ i ∈ s \ t, (1 - r i)) * g t) := by
                apply Finset.sum_congr rfl
                intro t ht
                have hat : a ∉ t := fun h =>
                  ha ((Finset.mem_powerset.mp ht) h)
                have hdiff : insert a s \ t = insert a (s \ t) := by
                  ext i
                  simp only [Finset.mem_sdiff, Finset.mem_insert]
                  constructor
                  · rintro ⟨rfl | his, hit⟩
                    · exact Or.inl rfl
                    · exact Or.inr ⟨his, hit⟩
                  · rintro (rfl | ⟨his, hit⟩)
                    · exact ⟨Or.inl rfl, hat⟩
                    · exact ⟨Or.inr his, hit⟩
                rw [hdiff, Finset.prod_insert]
                · ring
                · simp [ha]
          _ = _ := by rw [Finset.mul_sum]
      have hright₂ :
          (∑ t ∈ s.powerset,
            (∏ i ∈ insert a t, r i) *
              (∏ i ∈ insert a s \ insert a t, (1 - r i)) * g (insert a t)) =
            r a *
              ∑ t ∈ s.powerset,
                (∏ i ∈ t, r i) * (∏ i ∈ s \ t, (1 - r i)) *
                  g (insert a t) := by
        calc
          _ = ∑ t ∈ s.powerset, r a *
              ((∏ i ∈ t, r i) * (∏ i ∈ s \ t, (1 - r i)) *
                g (insert a t)) := by
                apply Finset.sum_congr rfl
                intro t ht
                have hat : a ∉ t := fun h =>
                  ha ((Finset.mem_powerset.mp ht) h)
                have hdiff : insert a s \ insert a t = s \ t := by
                  ext i
                  simp only [Finset.mem_sdiff, Finset.mem_insert]
                  constructor
                  · rintro ⟨rfl | his, hnot⟩
                    · exact (hnot (Or.inl rfl)).elim
                    · exact ⟨his, fun hit => hnot (Or.inr hit)⟩
                  · rintro ⟨his, hit⟩
                    exact ⟨Or.inr his, fun h =>
                      h.elim (fun hia => ha (hia ▸ his)) hit⟩
                rw [Finset.prod_insert hat, hdiff]
                ring
          _ = _ := by rw [Finset.mul_sum]
      rw [hleft, hright₁, hright₂, ih g, ih (fun t => g (insert a t))]
      ring

@[blueprint "lem:scalar-noise-inverse-conditional-expectation-finset-sum"
  (statement := /-- Conditional expectation with respect to any coordinate set commutes with every finite real linear combination. -/)
  (proof := /-- Expand \cref{def:partite-conditional-expectation}. If the conditioning fiber has zero mass, both sides vanish. Otherwise, distribute the common weighted fiber sum and its denominator over the finite linear combination, interchange the finite sums, and collect the coefficient of each summand. -/)
  (title := /-- Finite linearity of conditional expectation -/)
  (latexEnv := "lemma")]
lemma scalar_noise_inverse_conditional_expectation_finset_sum {d : ℕ}
    (X : partite_distribution d) {ι : Type} [DecidableEq ι] (s : Finset ι)
    (A : Finset (Fin d)) (c : ι → ℝ) (g : ι → X.Face → ℝ) (z : X.Face) :
    partite_conditional_expectation X A
        (fun x => ∑ i ∈ s, c i * g i x) z =
      ∑ i ∈ s, c i * partite_conditional_expectation X A (g i) z := by
  classical
  letI : Fintype X.Face := X.faceFintype
  by_cases hm : partite_fiber_mass X A z = 0
  · simp [partite_conditional_expectation, hm]
  · simp only [partite_conditional_expectation, hm, if_false]
    simp_rw [Finset.mul_sum]
    have hite : ∀ x : X.Face,
        (if partite_agree_on X A x z then
          ∑ i ∈ s, X.weight x * (c i * g i x) else 0) =
        ∑ i ∈ s, if partite_agree_on X A x z then
          X.weight x * (c i * g i x) else 0 := by
      intro x
      by_cases h : partite_agree_on X A x z <;> simp [h]
    simp_rw [hite]
    rw [Finset.sum_comm]
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h : partite_agree_on X A y z <;> simp [h] <;> ring

@[blueprint "lem:scalar-noise-inverse-expansion"
  (statement := /-- Let $X$ be a finite $d$-partite distribution and let $f$ be real-valued on its top faces. For every top face $x$,
  \[
    T_{1/2}T_2f(x)=2^{-d}\sum_{A\subseteq[d]}\sum_{B\subseteq[d]}
      2^{|B|}(-1)^{d-|B|}E_AE_Bf(x).
  \] -/)
  (proof := /-- Expand the scalar noise operator and every Efron--Stein component using \cref{def:scalar-noise, def:efron-stein-component}, and apply \cref{lem:scalar-noise-inverse-signed-mobius-expansion} with the constant scalar function $i\mapsto\rho$. At $\rho=1/2$, the coefficient of every $E_Ag$ is
  \[
    (1/2)^{|A|}(1/2)^{d-|A|}=2^{-d},
  \]
  so $T_{1/2}g=2^{-d}\sum_A E_Ag$. At $\rho=2$, the coefficient of $E_Bf$ is
  \[
    2^{|B|}\prod_{i\in[d]\setminus B}(1-2)
      =2^{|B|}(-1)^{d-|B|}.
  \]
  Substitute this second expansion for $g=T_2f$ in the first. Then \cref{lem:scalar-noise-inverse-conditional-expectation-finset-sum} distributes each $E_A$ over the finite sum indexed by $B$, giving the displayed double sum pointwise. -/)
  (title := /-- Conditional-expectation expansion of the inverse-noise composition -/)
  (latexEnv := "lemma")]
lemma scalar_noise_inverse_expansion {d : ℕ} (X : partite_distribution d)
    (f : X.Face → ℝ) (x : X.Face) :
    scalar_noise X (1 / 2) (scalar_noise X 2 f) x =
      ((2 : ℝ) ^ d)⁻¹ *
        ∑ A ∈ (Finset.univ : Finset (Fin d)).powerset,
          ∑ B ∈ (Finset.univ : Finset (Fin d)).powerset,
            (2 : ℝ) ^ B.card * (-1 : ℝ) ^ (d - B.card) *
              partite_conditional_expectation X A
                (partite_conditional_expectation X B f) x := by
  classical
  have hnoise (ρ : ℝ) (g : X.Face → ℝ) (z : X.Face) :
      scalar_noise X ρ g z =
        ∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
          ρ ^ T.card *
            (1 - ρ) ^ ((Finset.univ : Finset (Fin d)) \ T).card *
            partite_conditional_expectation X T g z := by
    simpa [scalar_noise, efron_stein_component] using
      scalar_noise_inverse_signed_mobius_expansion
        (Finset.univ : Finset (Fin d)) (fun _ => ρ)
        (fun T => partite_conditional_expectation X T g z)
  have hhalf (g : X.Face → ℝ) (z : X.Face) :
      scalar_noise X (1 / 2) g z =
        ((2 : ℝ) ^ d)⁻¹ *
          ∑ A ∈ (Finset.univ : Finset (Fin d)).powerset,
            partite_conditional_expectation X A g z := by
    rw [hnoise]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A hA
    have hsub : A ⊆ (Finset.univ : Finset (Fin d)) :=
      Finset.mem_powerset.mp hA
    have hcard : A.card + ((Finset.univ : Finset (Fin d)) \ A).card = d := by
      have hle := Finset.card_le_card hsub
      rw [Finset.card_sdiff]
      simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      have hle' : A.card ≤ d := by simpa using hle
      omega
    rw [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num, ← pow_add, hcard]
    norm_num [div_pow]
  have htwo (g : X.Face → ℝ) (z : X.Face) :
      scalar_noise X 2 g z =
        ∑ B ∈ (Finset.univ : Finset (Fin d)).powerset,
          (2 : ℝ) ^ B.card * (-1 : ℝ) ^ (d - B.card) *
            partite_conditional_expectation X B g z := by
    rw [hnoise]
    apply Finset.sum_congr rfl
    intro B hB
    rw [Finset.card_sdiff]
    simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    norm_num
  rw [hhalf]
  have htwo_fun : scalar_noise X 2 f = fun z =>
      ∑ B ∈ (Finset.univ : Finset (Fin d)).powerset,
        (2 : ℝ) ^ B.card * (-1 : ℝ) ^ (d - B.card) *
          partite_conditional_expectation X B f z := by
    funext z
    exact htwo f z
  rw [htwo_fun]
  simp_rw [scalar_noise_inverse_conditional_expectation_finset_sum]

@[blueprint "lem:finset-noise-sum-powerset-insert"
  (statement := /-- Let $\alpha$ be a type with decidable equality, let $M$ be an additive commutative monoid, let $a\in\alpha$, let $s$ be a finite subset of $\alpha$ with $a\notin s$, and let $f$ map finite subsets of $\alpha$ to $M$. Then
  \[
    \sum_{t\subseteq s\cup\{a\}}f(t)
      =\sum_{t\subseteq s}f(t)+\sum_{t\subseteq s}f(t\cup\{a\}).
  \] -/)
  (proof := /-- The powerset of $s\cup\{a\}$ is the disjoint union of the powerset of $s$ and the image of that powerset under $t\mapsto t\cup\{a\}$. The two parts are disjoint because $a\notin s$. Moreover, adjoining $a$ is injective on subsets of $s$: erasing $a$ from an equality $t\cup\{a\}=u\cup\{a\}$ recovers $t=u$. Summing over the disjoint union and then over this injective image yields the claimed identity. -/)
  (title := /-- Splitting a powerset sum at a new element -/)
  (latexEnv := "lemma")]
lemma finset_noise_sum_powerset_insert {α M : Type} [DecidableEq α]
    [AddCommMonoid M] (a : α) (s : Finset α) (ha : a ∉ s)
    (f : Finset α → M) :
    ∑ t ∈ (insert a s).powerset, f t =
      (∑ t ∈ s.powerset, f t) + ∑ t ∈ s.powerset, f (insert a t) := by
  rw [Finset.powerset_insert]
  have hd : Disjoint s.powerset (s.powerset.image (insert a)) := by
    rw [Finset.disjoint_left]
    intro u hu himage
    rw [Finset.mem_image] at himage
    obtain ⟨v, hv, rfl⟩ := himage
    exact ha ((Finset.mem_powerset.mp hu) (Finset.mem_insert_self a v))
  rw [Finset.sum_union hd, Finset.sum_image]
  intro u hu v hv huv
  have hau : a ∉ u := fun h => ha ((Finset.mem_powerset.mp hu) h)
  have hav : a ∉ v := fun h => ha ((Finset.mem_powerset.mp hv) h)
  calc
    u = (insert a u).erase a := by simp [hau]
    _ = (insert a v).erase a := congrArg (Finset.erase · a) huv
    _ = v := by simp [hav]

@[blueprint "lem:finset-noise-inverse-coefficient-cancellation"
  (statement := /-- Let $\alpha$ be a type with decidable equality, let $s$ be a finite subset of $\alpha$, and let $g$ be a real-valued function on the finite subsets of $\alpha$. Then
  \[
    2^{-|s|}\sum_{A\subseteq s}\sum_{B\subseteq s}
      2^{|B|}(-1)^{|s|-|B|}g(A\cap B)=g(s).
  \] -/)
  (proof := /-- We induct on $s$. The identity for $s=\varnothing$ follows by evaluating its unique pair of subsets. For the induction step, write $s'=s\cup\{a\}$ with $a\notin s$, and use \cref{lem:finset-noise-sum-powerset-insert} to split each powerset sum according to whether its subset contains $a$. Denote the unnormalized double sum over $s$, with test function $h$, by $F_s(h)$, and set $g_a(C)=g(C\cup\{a\})$.

  The four resulting contributions correspond to whether $A$ and $B$ contain $a$. If neither does, increasing the exponent of $-1$ changes the contribution to $-F_s(g)$. If only $B$ does, the factor $2^{|B|}$ doubles while $A\cap B$ is unchanged, giving $2F_s(g)$. If only $A$ does, the contribution is again $-F_s(g)$. If both do, their intersection contains $a$, and the contribution is $2F_s(g_a)$. Thus the first three terms cancel and the unnormalized sum over $s'$ is $2F_s(g_a)$. Since $2^{-|s'|}\cdot2=2^{-|s|}$, the induction hypothesis gives $g_a(s)=g(s')$, as required. -/)
  (title := /-- Coefficient cancellation for half-noise after two-noise -/)
  (latexEnv := "lemma")]
lemma finset_noise_inverse_coefficient_cancellation {α : Type}
    [DecidableEq α] (s : Finset α) (g : Finset α → ℝ) :
    ((2 : ℝ) ^ s.card)⁻¹ *
        ∑ A ∈ s.powerset, ∑ B ∈ s.powerset,
          (2 : ℝ) ^ B.card * (-1 : ℝ) ^ (s.card - B.card) * g (A ∩ B) =
      g s := by
  induction s using Finset.induction_on generalizing g with
  | empty => norm_num
  | @insert a s ha ih =>
      let F (h : Finset α → ℝ) :=
        ∑ A ∈ s.powerset, ∑ B ∈ s.powerset,
          (2 : ℝ) ^ B.card * (-1 : ℝ) ^ (s.card - B.card) * h (A ∩ B)
      have hnn :
          (∑ A ∈ s.powerset, ∑ B ∈ s.powerset,
            (2 : ℝ) ^ B.card * (-1 : ℝ) ^ (s.card + 1 - B.card) *
              g (A ∩ B)) = -F g := by
        simp only [F]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro A hA
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro B hB
        have hle : B.card ≤ s.card :=
          Finset.card_le_card (Finset.mem_powerset.mp hB)
        have hd : s.card + 1 - B.card = (s.card - B.card) + 1 := by
          omega
        simp only [F, hd, pow_succ]
        ring
      have hny :
          (∑ A ∈ s.powerset, ∑ B ∈ s.powerset,
            (2 : ℝ) ^ (insert a B).card *
              (-1 : ℝ) ^ (s.card + 1 - (insert a B).card) *
              g (A ∩ insert a B)) = 2 * F g := by
        simp only [F]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro A hA
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro B hB
        have hAsub : A ⊆ s := Finset.mem_powerset.mp hA
        have hBsub : B ⊆ s := Finset.mem_powerset.mp hB
        have hna : a ∉ A := fun h => ha (hAsub h)
        have hnb : a ∉ B := fun h => ha (hBsub h)
        have hinter : A ∩ insert a B = A ∩ B := by
          ext x
          constructor
          · intro hx
            simp only [Finset.mem_inter, Finset.mem_insert] at hx ⊢
            rcases hx with ⟨hxA, hxa | hxB⟩
            · exact (hna (hxa ▸ hxA)).elim
            · exact ⟨hxA, hxB⟩
          · intro hx
            exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
              Finset.mem_insert_of_mem (Finset.mem_inter.mp hx).2⟩
        have hd : s.card + 1 - (B.card + 1) = s.card - B.card := by
          omega
        simp only [F, Finset.card_insert_of_notMem hnb, hd, hinter, pow_succ]
        ring
      have hyn :
          (∑ A ∈ s.powerset, ∑ B ∈ s.powerset,
            (2 : ℝ) ^ B.card * (-1 : ℝ) ^ (s.card + 1 - B.card) *
              g (insert a A ∩ B)) = -F g := by
        simp only [F]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro A hA
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro B hB
        have hBsub : B ⊆ s := Finset.mem_powerset.mp hB
        have hnb : a ∉ B := fun h => ha (hBsub h)
        have hinter : insert a A ∩ B = A ∩ B := by
          ext x
          constructor
          · intro hx
            simp only [Finset.mem_inter, Finset.mem_insert] at hx ⊢
            rcases hx with ⟨hxa | hxA, hxB⟩
            · exact (hnb (hxa ▸ hxB)).elim
            · exact ⟨hxA, hxB⟩
          · intro hx
            exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem
              (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
        have hle : B.card ≤ s.card := Finset.card_le_card hBsub
        have hd : s.card + 1 - B.card = (s.card - B.card) + 1 := by
          omega
        simp only [F, hd, hinter, pow_succ]
        ring
      have hyy :
          (∑ A ∈ s.powerset, ∑ B ∈ s.powerset,
            (2 : ℝ) ^ (insert a B).card *
              (-1 : ℝ) ^ (s.card + 1 - (insert a B).card) *
              g (insert a A ∩ insert a B)) =
            2 * F (fun C => g (insert a C)) := by
        simp only [F]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro A hA
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro B hB
        have hBsub : B ⊆ s := Finset.mem_powerset.mp hB
        have hnb : a ∉ B := fun h => ha (hBsub h)
        have hinter : insert a A ∩ insert a B = insert a (A ∩ B) := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_insert]
          aesop
        have hd : s.card + 1 - (B.card + 1) = s.card - B.card := by
          omega
        simp only [F, Finset.card_insert_of_notMem hnb, hd, hinter, pow_succ]
        ring
      simp only [Finset.card_insert_of_notMem ha,
        finset_noise_sum_powerset_insert a s ha]
      repeat' rw [Finset.sum_add_distrib]
      rw [hnn, hny, hyn, hyy]
      have ih' := ih (fun C => g (insert a C))
      rw [pow_succ]
      norm_num
      ring_nf
      simpa [F] using ih'

@[blueprint "lem:approximate-noise-closure"
  (statement := /-- For every real number $q>1$, there are rates $a,b>0$, depending only on $q$, such that, for every $d\in\mathbb N$, every finite $d$-partite distribution $X$, every $\gamma\geq0$ for which $X$ is a $(q,\gamma)$-product and $\gamma\leq2^{-ad}$, and every function $f:X\to\mathbb R$ on the top faces of $X$,
  \[
    \|f\|_q\leq
    \|T_{1/2}T_2f\|_q+2^{bd}\gamma\|f\|_q.
  \] -/)
  (proof := /-- Choose the decay rate to be $1$ and the growth rate to be $4$. By \cref{lem:scalar-noise-inverse-expansion},
  \[
    T_{1/2}T_2f
      =2^{-d}\sum_{A,B\subseteq[d]}2^{|B|}(-1)^{d-|B|}E_AE_Bf.
  \]
  For each pair $(A,B)$, write $E_AE_Bf=E_{A\cap B}f+D_{A,B}$. The product hypothesis and \cref{lem:conditional-expectation-composition-qnorm-le} give
  \[
    \|D_{A,B}\|_q\leq |A|\,|B|\,\gamma\|f\|_q.
  \]
  Apply \cref{lem:finset-noise-inverse-coefficient-cancellation} pointwise to $C\mapsto E_Cf$. The sum of all main terms is $E_{[d]}f$. Complete coordinate tuples determine top faces, so $E_{[d]}f=f$ on every positive-mass face; zero-mass faces make no contribution to \cref{def:partite-qnorm}. Hence \cref{lem:partite-qnorm-congr-positive-weight-local} identifies the $q$-norm of the main sum with that of $f$.

  It remains to bound the sum of the $D_{A,B}$. By \cref{lem:noise-qnorm-nonnegative-scale}, replacing a scalar coefficient by its absolute value extracts that absolute value from the norm. After the factor $2^{-d}$ is included, every such coefficient has absolute value at most one. There are $4^d$ ordered pairs $(A,B)$, and $|A|\,|B|\leq d^2$. Repeated application of the finite Minkowski estimate \cref{lem:efron-qnorm-finset-sum-le-card} therefore bounds the error by
  \[
    d^2\,4^d\gamma\|f\|_q\leq 2^{4d}\gamma\|f\|_q;
  \]
  for $d=0$ the error is identically zero, while for $d\geq1$ the last inequality follows from $d\leq2^d$. The triangle inequality \cref{lem:partite-qnorm-add-le-local} applied once more to
  $f=T_{1/2}T_2f-\mathrm{error}$ proves the required estimate. The exponential-smallness hypothesis is not needed for this intermediate bound. -/)
  (title := /-- Approximate closure of the noise inverse -/)
  (latexEnv := "lemma")]
lemma approximate_noise_closure (q : ℝ) (hq : 1 < q) :
    ∃ decay growth : ℝ, 0 < decay ∧ 0 < growth ∧
      ∀ (d : ℕ) (X : partite_distribution d) (γ : ℝ) (f : X.Face → ℝ),
        0 ≤ γ → is_q_gamma_product X q γ → exponentially_small decay d γ →
          partite_qnorm X q f ≤
            partite_qnorm X q (scalar_noise X (1 / 2)
              (scalar_noise X 2 f)) +
            exponential_error growth d γ * partite_qnorm X q f := by
  refine ⟨1, 4, by norm_num, by norm_num, ?_⟩
  intro d X γ f hγ hproduct hsmall
  classical
  letI : Fintype X.Face := X.faceFintype
  have hq' : 1 ≤ q := le_of_lt hq
  let U : Finset (Fin d) := Finset.univ
  let D (A B : Finset (Fin d)) (x : X.Face) :=
    partite_conditional_expectation X A
        (partite_conditional_expectation X B f) x -
      partite_conditional_expectation X (A ∩ B) f x
  let C := (d : ℝ) ^ 2 * γ * partite_qnorm X q f
  have hnorm_nonneg : 0 ≤ partite_qnorm X q f := by
    unfold partite_qnorm
    exact Real.rpow_nonneg (Finset.sum_nonneg fun x _ =>
      mul_nonneg (X.weight_nonnegative x)
        (Real.rpow_nonneg (abs_nonneg _) q)) (1 / q)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) hγ) hnorm_nonneg
  have hD (A B : Finset (Fin d)) (hA : A ∈ U.powerset)
      (hB : B ∈ U.powerset) :
      partite_qnorm X q (D A B) ≤ C := by
    have hAc : A.card ≤ d := by
      calc
        A.card ≤ U.card := Finset.card_le_card (Finset.mem_powerset.mp hA)
        _ = d := by simp [U]
    have hBc : B.card ≤ d := by
      calc
        B.card ≤ U.card := Finset.card_le_card (Finset.mem_powerset.mp hB)
        _ = d := by simp [U]
    have hAc' : (A.card : ℝ) ≤ (d : ℝ) := by exact_mod_cast hAc
    have hBc' : (B.card : ℝ) ≤ (d : ℝ) := by exact_mod_cast hBc
    have hab : (A.card : ℝ) * (B.card : ℝ) ≤ (d : ℝ) * (d : ℝ) :=
      mul_le_mul hAc' hBc' (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hbase := conditional_expectation_composition_qnorm_le
      X q γ hq' hγ hproduct A B f
    calc
      partite_qnorm X q (D A B) ≤
          (A.card : ℝ) * (B.card : ℝ) * γ * partite_qnorm X q f := by
        simpa [D] using hbase
      _ = ((A.card : ℝ) * (B.card : ℝ)) *
          (γ * partite_qnorm X q f) := by ring
      _ ≤ ((d : ℝ) * (d : ℝ)) *
          (γ * partite_qnorm X q f) :=
        mul_le_mul_of_nonneg_right hab (mul_nonneg hγ hnorm_nonneg)
      _ = C := by dsimp [C]; ring
  have hscale (a : ℝ) (g : X.Face → ℝ) :
      partite_qnorm X q (fun x => a * g x) =
        |a| * partite_qnorm X q g := by
    calc
      partite_qnorm X q (fun x => a * g x) =
          partite_qnorm X q (fun x => |a| * g x) := by
        unfold partite_qnorm
        apply congrArg (fun t : ℝ => t ^ (1 / q))
        apply Finset.sum_congr rfl
        intro x hx
        congr 1
        rw [abs_mul, abs_mul, abs_abs]
      _ = |a| * partite_qnorm X q g :=
        noise_qnorm_nonnegative_scale X q hq' |a| (abs_nonneg a) g
  let coeff (B : Finset (Fin d)) :=
    (2 : ℝ) ^ B.card * (-1 : ℝ) ^ (d - B.card)
  have hcoeff_abs (B : Finset (Fin d)) : |coeff B| = (2 : ℝ) ^ B.card := by
    simp [coeff, abs_mul]
  have hterm (A B : Finset (Fin d)) (hA : A ∈ U.powerset)
      (hB : B ∈ U.powerset) :
      partite_qnorm X q (fun x => coeff B * D A B x) ≤
        (2 : ℝ) ^ d * C := by
    have hBc : B.card ≤ d := by
      calc
        B.card ≤ U.card := Finset.card_le_card (Finset.mem_powerset.mp hB)
        _ = d := by simp [U]
    have hpow : (2 : ℝ) ^ B.card ≤ (2 : ℝ) ^ d := by
      exact pow_le_pow_right₀ (by norm_num) hBc
    calc
      partite_qnorm X q (fun x => coeff B * D A B x) =
          (2 : ℝ) ^ B.card * partite_qnorm X q (D A B) := by
        rw [hscale, hcoeff_abs]
      _ ≤ (2 : ℝ) ^ B.card * C :=
        mul_le_mul_of_nonneg_left (hD A B hA hB) (by positivity)
      _ ≤ (2 : ℝ) ^ d * C := mul_le_mul_of_nonneg_right hpow hC
  have hinner (A : Finset (Fin d)) (hA : A ∈ U.powerset) :
      partite_qnorm X q (fun x =>
        ∑ B ∈ U.powerset, coeff B * D A B x) ≤
        (U.powerset.card : ℝ) * ((2 : ℝ) ^ d * C) := by
    exact efron_qnorm_finset_sum_le_card X q hq' U.powerset
      (fun B x => coeff B * D A B x) ((2 : ℝ) ^ d * C)
      (by positivity) (fun B hB => hterm A B hA hB)
  have hsum :
      partite_qnorm X q (fun x =>
        ∑ A ∈ U.powerset, ∑ B ∈ U.powerset,
          coeff B * D A B x) ≤
        (U.powerset.card : ℝ) *
          ((U.powerset.card : ℝ) * ((2 : ℝ) ^ d * C)) := by
    exact efron_qnorm_finset_sum_le_card X q hq' U.powerset
      (fun A x => ∑ B ∈ U.powerset, coeff B * D A B x)
      ((U.powerset.card : ℝ) * ((2 : ℝ) ^ d * C))
      (by positivity) (fun A hA => hinner A hA)
  have hcard : (U.powerset.card : ℝ) = (2 : ℝ) ^ d := by
    simp [U, Finset.card_powerset]
  let err (x : X.Face) :=
    ((2 : ℝ) ^ d)⁻¹ *
      ∑ A ∈ U.powerset, ∑ B ∈ U.powerset, coeff B * D A B x
  have herr_raw :
      partite_qnorm X q err ≤ (2 : ℝ) ^ (2 * d) * C := by
    calc
      partite_qnorm X q err =
          ((2 : ℝ) ^ d)⁻¹ * partite_qnorm X q (fun x =>
            ∑ A ∈ U.powerset, ∑ B ∈ U.powerset,
              coeff B * D A B x) := by
        exact noise_qnorm_nonnegative_scale X q hq' ((2 : ℝ) ^ d)⁻¹
          (by positivity) _
      _ ≤ ((2 : ℝ) ^ d)⁻¹ *
          ((U.powerset.card : ℝ) *
            ((U.powerset.card : ℝ) * ((2 : ℝ) ^ d * C))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (2 : ℝ) ^ (2 * d) * C := by
        rw [hcard, show 2 * d = d + d by omega, pow_add]
        field_simp
  have hdecomp (x : X.Face) :
      scalar_noise X (1 / 2) (scalar_noise X 2 f) x =
        partite_conditional_expectation X U f x + err x := by
    rw [scalar_noise_inverse_expansion]
    change ((2 : ℝ) ^ d)⁻¹ *
        ∑ A ∈ U.powerset, ∑ B ∈ U.powerset,
          coeff B * partite_conditional_expectation X A
            (partite_conditional_expectation X B f) x =
      partite_conditional_expectation X U f x + err x
    have hcancel := finset_noise_inverse_coefficient_cancellation U
      (fun C => partite_conditional_expectation X C f x)
    have hcancel' :
        ((2 : ℝ) ^ d)⁻¹ *
            ∑ A ∈ U.powerset, ∑ B ∈ U.powerset,
              coeff B * partite_conditional_expectation X (A ∩ B) f x =
          partite_conditional_expectation X U f x := by
      simpa [U, coeff] using hcancel
    calc
      ((2 : ℝ) ^ d)⁻¹ *
          ∑ A ∈ U.powerset, ∑ B ∈ U.powerset,
            coeff B * partite_conditional_expectation X A
              (partite_conditional_expectation X B f) x =
        ((2 : ℝ) ^ d)⁻¹ *
          ∑ A ∈ U.powerset, ∑ B ∈ U.powerset,
            coeff B * (partite_conditional_expectation X (A ∩ B) f x +
              D A B x) := by
          apply congrArg (fun t : ℝ => ((2 : ℝ) ^ d)⁻¹ * t)
          apply Finset.sum_congr rfl
          intro A hA
          apply Finset.sum_congr rfl
          intro B hB
          dsimp [D]
          ring
      _ = ((2 : ℝ) ^ d)⁻¹ *
            ∑ A ∈ U.powerset, ∑ B ∈ U.powerset,
              coeff B * partite_conditional_expectation X (A ∩ B) f x +
          ((2 : ℝ) ^ d)⁻¹ *
            ∑ A ∈ U.powerset, ∑ B ∈ U.powerset,
              coeff B * D A B x := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        ring
      _ = partite_conditional_expectation X U f x + err x := by
        rw [hcancel']
  have hfull (x : X.Face) (hw : X.weight x ≠ 0) :
      partite_conditional_expectation X U f x = f x := by
    have hagree (y : X.Face) : partite_agree_on X U y x ↔ y = x := by
      constructor
      · intro hy
        apply X.coordinate_injective
        intro i
        exact hy i (by simp [U])
      · rintro rfl
        intro i hi
        rfl
    simp [partite_conditional_expectation, partite_fiber_mass, hagree, hw]
  have hd_two_all : ∀ n : ℕ, n ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        have hp : 0 < (2 : ℕ) ^ n := pow_pos (by norm_num) n
        omega
  have hd_two : d ≤ 2 ^ d := hd_two_all d
  have hdreal : (d : ℝ) ≤ (2 : ℝ) ^ d := by exact_mod_cast hd_two
  have hsq : (d : ℝ) ^ 2 ≤ ((2 : ℝ) ^ d) ^ 2 := by
    have hprod := mul_nonneg
      (sub_nonneg.mpr hdreal)
      (add_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ d) (Nat.cast_nonneg d))
    nlinarith
  have hlarge :
      (2 : ℝ) ^ (2 * d) * (d : ℝ) ^ 2 ≤ (2 : ℝ) ^ (4 * d) := by
    calc
      (2 : ℝ) ^ (2 * d) * (d : ℝ) ^ 2 =
          ((2 : ℝ) ^ d) ^ 2 * (d : ℝ) ^ 2 := by
        rw [show 2 * d = d + d by omega, pow_add]
        ring
      _ ≤ ((2 : ℝ) ^ d) ^ 2 * ((2 : ℝ) ^ d) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = (2 : ℝ) ^ (4 * d) := by
        rw [show 4 * d = (d + d) + (d + d) by omega, pow_add, pow_add]
        ring
  have herr :
      partite_qnorm X q err ≤
        exponential_error 4 d γ * partite_qnorm X q f := by
    calc
      partite_qnorm X q err ≤ (2 : ℝ) ^ (2 * d) * C := herr_raw
      _ = ((2 : ℝ) ^ (2 * d) * (d : ℝ) ^ 2) *
          (γ * partite_qnorm X q f) := by dsimp [C]; ring
      _ ≤ (2 : ℝ) ^ (4 * d) *
          (γ * partite_qnorm X q f) :=
        mul_le_mul_of_nonneg_right hlarge (mul_nonneg hγ hnorm_nonneg)
      _ = exponential_error 4 d γ * partite_qnorm X q f := by
        unfold exponential_error
        rw [show (4 : ℝ) * (d : ℝ) = ((4 * d : ℕ) : ℝ) by push_cast; ring]
        have hrpow : Real.rpow 2 ((4 * d : ℕ) : ℝ) = (2 : ℝ) ^ (4 * d) :=
          Real.rpow_natCast 2 (4 * d)
        rw [hrpow]
        ring
  have hneg :
      partite_qnorm X q (fun x => -err x) = partite_qnorm X q err := by
    unfold partite_qnorm
    apply congrArg (fun t : ℝ => t ^ (1 / q))
    apply Finset.sum_congr rfl
    intro x hx
    rw [abs_neg]
  calc
    partite_qnorm X q f = partite_qnorm X q (fun x =>
        scalar_noise X (1 / 2) (scalar_noise X 2 f) x + -err x) := by
      apply partite_qnorm_congr_positive_weight_local
      intro x hw
      rw [hdecomp x, hfull x hw]
      ring
    _ ≤ partite_qnorm X q (scalar_noise X (1 / 2) (scalar_noise X 2 f)) +
        partite_qnorm X q (fun x => -err x) :=
      partite_qnorm_add_le_local X q hq' _ _
    _ = partite_qnorm X q (scalar_noise X (1 / 2) (scalar_noise X 2 f)) +
        partite_qnorm X q err := by rw [hneg]
    _ ≤ partite_qnorm X q (scalar_noise X (1 / 2) (scalar_noise X 2 f)) +
        exponential_error 4 d γ * partite_qnorm X q f :=
      add_le_add_right herr _

@[blueprint "lem:finset-sum-powerset-insert"
  (statement := /-- If $a\notin s$, then a sum over the subsets of $s\cup\{a\}$ splits into the subsets not containing $a$ and those containing $a$:
  \[
    \sum_{t\subseteq s\cup\{a\}}f(t)
      =\sum_{t\subseteq s}f(t)+\sum_{t\subseteq s}f(t\cup\{a\}).
  \] -/)
  (proof := /-- The powerset of $s\cup\{a\}$ is the disjoint union of the powerset of $s$ and its image under $t\mapsto t\cup\{a\}$. The latter map is injective on subsets of $s$ because none contains $a$. Summing over this disjoint union gives the identity. -/)
  (title := /-- Splitting a powerset sum at an inserted element -/)
  (latexEnv := "lemma")]
lemma finset_sum_powerset_insert {α M : Type} [DecidableEq α] [AddCommMonoid M]
    (a : α) (s : Finset α) (ha : a ∉ s) (f : Finset α → M) :
    ∑ t ∈ (insert a s).powerset, f t =
      (∑ t ∈ s.powerset, f t) + ∑ t ∈ s.powerset, f (insert a t) := by
  rw [Finset.powerset_insert]
  have hd : Disjoint s.powerset (s.powerset.image (insert a)) := by
    rw [Finset.disjoint_left]
    intro u hu himage
    rw [Finset.mem_image] at himage
    obtain ⟨v, hv, rfl⟩ := himage
    exact ha ((Finset.mem_powerset.mp hu) (Finset.mem_insert_self a v))
  rw [Finset.sum_union hd, Finset.sum_image]
  intro u hu v hv huv
  have hau : a ∉ u := fun h => ha ((Finset.mem_powerset.mp hu) h)
  have hav : a ∉ v := fun h => ha ((Finset.mem_powerset.mp hv) h)
  calc
    u = (insert a u).erase a := by simp [hau]
    _ = (insert a v).erase a := congrArg (Finset.erase · a) huv
    _ = v := by simp [hav]

@[blueprint "lem:finset-half-mobius-average"
  (statement := /-- Let $s$ be a finite set and let $g$ be real-valued on its subsets. Then
  \[
    \sum_{S\subseteq s}2^{-|S|}\sum_{T\subseteq S}(-1)^{|S|-|T|}g(T)
      =2^{-|s|}\sum_{T\subseteq s}g(T).
  \] -/)
  (proof := /-- Induct on $s$. Apply \cref{lem:finset-sum-powerset-insert} to split both powerset sums according to whether they contain the newly adjoined element. The induction step then follows from the induction hypothesis and the identity $1-\frac12=\frac12$. -/)
  (title := /-- Averaging the finite Möbius transform -/)
  (latexEnv := "lemma")]
lemma finset_half_mobius_average {α : Type} [DecidableEq α]
    (s : Finset α) (g : Finset α → ℝ) :
    ∑ S ∈ s.powerset, (1 / 2 : ℝ) ^ S.card *
        (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * g T) =
      ((2 : ℝ) ^ s.card)⁻¹ * ∑ T ∈ s.powerset, g T := by
  induction s using Finset.induction_on generalizing g with
  | empty => norm_num
  | @insert a s ha ih =>
      rw [finset_sum_powerset_insert a s ha]
      rw [finset_sum_powerset_insert a s ha]
      simp only [Finset.card_insert_of_notMem ha, pow_succ]
      have hterm : ∀ t ∈ s.powerset,
          (1 / 2 : ℝ) ^ (insert a t).card *
              (∑ T ∈ (insert a t).powerset,
                (-1 : ℝ) ^ ((insert a t).card - T.card) * g T) =
            (1 / 2 : ℝ) *
              ((1 / 2 : ℝ) ^ t.card *
                  (∑ T ∈ t.powerset,
                    (-1 : ℝ) ^ (t.card - T.card) * g (insert a T)) -
                (1 / 2 : ℝ) ^ t.card *
                  (∑ T ∈ t.powerset,
                    (-1 : ℝ) ^ (t.card - T.card) * g T)) := by
        intro t ht
        have hat : a ∉ t := fun h => ha ((Finset.mem_powerset.mp ht) h)
        rw [finset_sum_powerset_insert a t hat]
        have hfirst :
            (∑ T ∈ t.powerset,
              (-1 : ℝ) ^ ((insert a t).card - T.card) * g T) =
              -(∑ T ∈ t.powerset,
                (-1 : ℝ) ^ (t.card - T.card) * g T) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro T hT
          have hle : T.card ≤ t.card :=
            Finset.card_le_card (Finset.mem_powerset.mp hT)
          rw [Finset.card_insert_of_notMem hat]
          have hsub : t.card + 1 - T.card = t.card - T.card + 1 := by omega
          rw [hsub, pow_succ]
          ring
        have hsecond :
            (∑ T ∈ t.powerset,
              (-1 : ℝ) ^ ((insert a t).card - (insert a T).card) *
                g (insert a T)) =
              ∑ T ∈ t.powerset,
                (-1 : ℝ) ^ (t.card - T.card) * g (insert a T) := by
          apply Finset.sum_congr rfl
          intro T hT
          have haT : a ∉ T := fun h =>
            hat ((Finset.mem_powerset.mp hT) h)
          rw [Finset.card_insert_of_notMem hat,
            Finset.card_insert_of_notMem haT]
          congr 2
          omega
        rw [hfirst, hsecond, Finset.card_insert_of_notMem hat, pow_succ]
        ring
      have hsum := Finset.sum_congr rfl hterm
      have hsum' :
          (∑ t ∈ s.powerset,
            (1 / 2 : ℝ) ^ (insert a t).card *
              (∑ T ∈ (insert a t).powerset,
                (-1 : ℝ) ^ ((insert a t).card - T.card) * g T)) =
            (1 / 2 : ℝ) *
              ((∑ t ∈ s.powerset, (1 / 2 : ℝ) ^ t.card *
                  (∑ T ∈ t.powerset,
                    (-1 : ℝ) ^ (t.card - T.card) * g (insert a T))) -
                ∑ t ∈ s.powerset, (1 / 2 : ℝ) ^ t.card *
                  (∑ T ∈ t.powerset,
                    (-1 : ℝ) ^ (t.card - T.card) * g T)) := by
        rw [hsum]
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hsum', ih g, ih (fun t => g (insert a t))]
      ring

@[blueprint "lem:finset-mobius-insert"
  (statement := /-- If $a\notin s$, the Möbius transform on $s\cup\{a\}$ satisfies
  \[
    \sum_{T\subseteq s\cup\{a\}}(-1)^{|s\cup\{a\}|-|T|}g(T)
      =\sum_{T\subseteq s}(-1)^{|s|-|T|}\bigl(g(T\cup\{a\})-g(T)\bigr).
  \] -/)
  (proof := /-- Apply \cref{lem:finset-sum-powerset-insert}. For subsets not containing $a$, adjoining $a$ increases the exponent by one and changes the sign; for subsets containing $a$, both cardinalities increase by one and the exponent is unchanged. -/)
  (title := /-- Möbius transform after inserting one element -/)
  (latexEnv := "lemma")]
lemma finset_mobius_insert {α : Type} [DecidableEq α]
    (a : α) (s : Finset α) (ha : a ∉ s) (g : Finset α → ℝ) :
    ∑ T ∈ (insert a s).powerset,
        (-1 : ℝ) ^ ((insert a s).card - T.card) * g T =
      ∑ T ∈ s.powerset,
        (-1 : ℝ) ^ (s.card - T.card) * (g (insert a T) - g T) := by
  rw [finset_sum_powerset_insert a s ha]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hinsert :
      (∑ T ∈ s.powerset,
        (-1 : ℝ) ^ ((insert a s).card - (insert a T).card) *
          g (insert a T)) =
        ∑ T ∈ s.powerset,
          (-1 : ℝ) ^ (s.card - T.card) * g (insert a T) := by
    apply Finset.sum_congr rfl
    intro T hT
    have haT : a ∉ T := fun h => ha ((Finset.mem_powerset.mp hT) h)
    rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haT]
    congr 2
    omega
  have hplain :
      (∑ T ∈ s.powerset,
        (-1 : ℝ) ^ ((insert a s).card - T.card) * g T) =
        -(∑ T ∈ s.powerset,
          (-1 : ℝ) ^ (s.card - T.card) * g T) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro T hT
    have hle : T.card ≤ s.card :=
      Finset.card_le_card (Finset.mem_powerset.mp hT)
    rw [Finset.card_insert_of_notMem ha]
    have hsub : s.card + 1 - T.card = s.card - T.card + 1 := by omega
    rw [hsub, pow_succ]
    ring
  rw [hplain, hinsert]
  ring

@[blueprint "lem:finset-signed-mobius-expansion"
  (statement := /-- Let $s$ be finite, let $r:s\to\mathbb R$, and let $g$ be real-valued on the subsets of $s$. Then
  \[
    \sum_{S\subseteq s}r_S\sum_{T\subseteq S}(-1)^{|S|-|T|}g(T)
      =\sum_{T\subseteq s}r_T\prod_{i\in s\setminus T}(1-r_i)g(T).
  \] -/)
  (proof := /-- Induct on $s$. Use \cref{lem:finset-sum-powerset-insert} to split the outer sums and \cref{lem:finset-mobius-insert} for the Möbius transform of a subset containing the new element. Both sides become $(1-r_a)$ times the induction hypothesis for $g$ plus $r_a$ times the induction hypothesis for $T\mapsto g(T\cup\{a\})$. -/)
  (title := /-- Signed expansion of a finite Möbius transform -/)
  (latexEnv := "lemma")]
lemma finset_signed_mobius_expansion {α : Type} [DecidableEq α]
    (s : Finset α) (r : α → ℝ) (g : Finset α → ℝ) :
    ∑ S ∈ s.powerset, (∏ i ∈ S, r i) *
        (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * g T) =
      ∑ T ∈ s.powerset,
        (∏ i ∈ T, r i) * (∏ i ∈ s \ T, (1 - r i)) * g T := by
  induction s using Finset.induction_on generalizing g with
  | empty => simp
  | @insert a s ha ih =>
      rw [finset_sum_powerset_insert a s ha]
      rw [finset_sum_powerset_insert a s ha]
      have hleft :
          (∑ t ∈ s.powerset, (∏ i ∈ insert a t, r i) *
            (∑ T ∈ (insert a t).powerset,
              (-1 : ℝ) ^ ((insert a t).card - T.card) * g T)) =
            r a *
              ((∑ t ∈ s.powerset, (∏ i ∈ t, r i) *
                (∑ T ∈ t.powerset,
                  (-1 : ℝ) ^ (t.card - T.card) * g (insert a T))) -
              ∑ t ∈ s.powerset, (∏ i ∈ t, r i) *
                (∑ T ∈ t.powerset,
                  (-1 : ℝ) ^ (t.card - T.card) * g T)) := by
        calc
          _ = ∑ t ∈ s.powerset, r a * (∏ i ∈ t, r i) *
              ((∑ T ∈ t.powerset,
                (-1 : ℝ) ^ (t.card - T.card) * g (insert a T)) -
              ∑ T ∈ t.powerset,
                (-1 : ℝ) ^ (t.card - T.card) * g T) := by
                apply Finset.sum_congr rfl
                intro t ht
                have hat : a ∉ t := fun h =>
                  ha ((Finset.mem_powerset.mp ht) h)
                rw [Finset.prod_insert hat, finset_mobius_insert a t hat]
                simp_rw [mul_sub]
                rw [Finset.sum_sub_distrib]
                ring
          _ = _ := by
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib]
            simp only [mul_assoc]
            rw [← Finset.mul_sum, ← Finset.mul_sum]
      have hright₁ :
          (∑ t ∈ s.powerset,
            (∏ i ∈ t, r i) * (∏ i ∈ insert a s \ t, (1 - r i)) * g t) =
            (1 - r a) *
              ∑ t ∈ s.powerset,
                (∏ i ∈ t, r i) * (∏ i ∈ s \ t, (1 - r i)) * g t := by
        calc
          _ = ∑ t ∈ s.powerset,
              (1 - r a) * ((∏ i ∈ t, r i) *
                (∏ i ∈ s \ t, (1 - r i)) * g t) := by
                apply Finset.sum_congr rfl
                intro t ht
                have hat : a ∉ t := fun h =>
                  ha ((Finset.mem_powerset.mp ht) h)
                have hdiff : insert a s \ t = insert a (s \ t) := by
                  ext i
                  simp only [Finset.mem_sdiff, Finset.mem_insert]
                  constructor
                  · rintro ⟨rfl | his, hit⟩
                    · exact Or.inl rfl
                    · exact Or.inr ⟨his, hit⟩
                  · rintro (rfl | ⟨his, hit⟩)
                    · exact ⟨Or.inl rfl, hat⟩
                    · exact ⟨Or.inr his, hit⟩
                rw [hdiff, Finset.prod_insert]
                · ring
                · simp [ha]
          _ = _ := by rw [Finset.mul_sum]
      have hright₂ :
          (∑ t ∈ s.powerset,
            (∏ i ∈ insert a t, r i) *
              (∏ i ∈ insert a s \ insert a t, (1 - r i)) * g (insert a t)) =
            r a *
              ∑ t ∈ s.powerset,
                (∏ i ∈ t, r i) * (∏ i ∈ s \ t, (1 - r i)) *
                  g (insert a t) := by
        calc
          _ = ∑ t ∈ s.powerset, r a *
              ((∏ i ∈ t, r i) * (∏ i ∈ s \ t, (1 - r i)) *
                g (insert a t)) := by
                apply Finset.sum_congr rfl
                intro t ht
                have hat : a ∉ t := fun h =>
                  ha ((Finset.mem_powerset.mp ht) h)
                have hdiff : insert a s \ insert a t = s \ t := by
                  ext i
                  simp only [Finset.mem_sdiff, Finset.mem_insert]
                  constructor
                  · rintro ⟨rfl | his, hnot⟩
                    · exact (hnot (Or.inl rfl)).elim
                    · exact ⟨his, fun hit => hnot (Or.inr hit)⟩
                  · rintro ⟨his, hit⟩
                    exact ⟨Or.inr his, fun h => h.elim (fun hia => ha (hia ▸ his)) hit⟩
                rw [Finset.prod_insert hat, hdiff]
                ring
          _ = _ := by rw [Finset.mul_sum]
      rw [hleft, hright₁, hright₂, ih g, ih (fun t => g (insert a t))]
      ring

@[blueprint "lem:scalar-noise-half-average"
  (statement := /-- For every finite $d$-partite distribution $X$, every real-valued function $f$ on its top faces, and every top face $x$, the half-noise operator is the uniform average of the conditional expectations:
  \[
    T_{1/2}f(x)=2^{-d}\sum_{A\subseteq[d]}E_Af(x).
  \] -/)
  (proof := /-- Expand the scalar noise operator and every Efron--Stein component using \cref{def:scalar-noise, def:efron-stein-component}, and apply \cref{lem:finset-half-mobius-average} to the function $A\mapsto E_Af(x)$. -/)
  (title := /-- Half-noise as an average of conditional expectations -/)
  (latexEnv := "lemma")]
lemma scalar_noise_half_average {d : ℕ} (X : partite_distribution d)
    (f : X.Face → ℝ) (x : X.Face) :
    scalar_noise X (1 / 2) f x =
      ((2 : ℝ) ^ d)⁻¹ *
        ∑ A ∈ (Finset.univ : Finset (Fin d)).powerset,
          partite_conditional_expectation X A f x := by
  classical
  simpa [scalar_noise, efron_stein_component] using
    finset_half_mobius_average (Finset.univ : Finset (Fin d))
      (fun A => partite_conditional_expectation X A f x)

@[blueprint "lem:partite-conditional-expectation-tower"
  (statement := /-- Let $A\subseteq B\subseteq[d]$. For every finite $d$-partite distribution $X$, every real-valued function $f$ on its top faces, and every top face $z$,
  \[
    E_A(E_Bf)(z)=E_Af(z).
  \] -/)
  (proof := /-- Expand both conditional expectations using \cref{def:partite-conditional-expectation}. If the $A$-fiber of $z$ has zero mass, both sides vanish. Otherwise, interchange the two finite sums. Since $A\subseteq B$, every $B$-fiber occurring inside the $A$-fiber is contained in that $A$-fiber; its normalizing mass therefore cancels against the total weight of the faces in that fiber. The remaining sum is precisely the numerator defining $E_Af(z)$. -/)
  (title := /-- Tower property for finite coordinate conditionings -/)
  (latexEnv := "lemma")]
lemma partite_conditional_expectation_tower {d : ℕ} (X : partite_distribution d)
    {A B : Finset (Fin d)} (hAB : A ⊆ B) (f : X.Face → ℝ) (z : X.Face) :
    partite_conditional_expectation X A
        (partite_conditional_expectation X B f) z =
      partite_conditional_expectation X A f z := by
  classical
  letI : Fintype X.Face := X.faceFintype
  by_cases hA : partite_fiber_mass X A z = 0
  · simp [partite_conditional_expectation, hA]
  · simp only [partite_conditional_expectation, hA, if_false]
    have hagree_refl (S : Finset (Fin d)) (x : X.Face) :
        partite_agree_on X S x x := by
      intro i hi
      rfl
    have hagree_symm {S : Finset (Fin d)} {x y : X.Face}
        (h : partite_agree_on X S x y) : partite_agree_on X S y x := by
      intro i hi
      exact (h i hi).symm
    have hagree_trans {S : Finset (Fin d)} {x y w : X.Face}
        (hxy : partite_agree_on X S x y)
        (hyw : partite_agree_on X S y w) : partite_agree_on X S x w := by
      intro i hi
      exact (hxy i hi).trans (hyw i hi)
    have hagree_mono {S T : Finset (Fin d)} (hST : S ⊆ T)
        {x y : X.Face} (h : partite_agree_on X T x y) :
        partite_agree_on X S x y := by
      intro i hi
      exact h i (hST hi)
    have hmass_eq {S : Finset (Fin d)} {x y : X.Face}
        (hxy : partite_agree_on X S x y) :
        partite_fiber_mass X S x = partite_fiber_mass X S y := by
      unfold partite_fiber_mass
      apply Finset.sum_congr rfl
      intro w hw
      have heq : partite_agree_on X S w x ↔ partite_agree_on X S w y := by
        constructor
        · intro h
          exact hagree_trans h hxy
        · intro h
          exact hagree_trans h (hagree_symm hxy)
      simp only [heq]
    have hweight_zero {S : Finset (Fin d)} (x : X.Face)
        (hm : partite_fiber_mass X S x = 0) : X.weight x = 0 := by
      have hle : X.weight x ≤ partite_fiber_mass X S x := by
        unfold partite_fiber_mass
        calc
          X.weight x = if partite_agree_on X S x x then X.weight x else 0 := by
            simp [hagree_refl]
          _ ≤ ∑ y, if partite_agree_on X S y x then X.weight y else 0 := by
            apply Finset.single_le_sum (s := Finset.univ)
              (f := fun y => if partite_agree_on X S y x then X.weight y else 0)
              (a := x)
            · intro y hy
              split_ifs
              · exact X.weight_nonnegative y
              · exact le_rfl
            · exact Finset.mem_univ x
      have hx := X.weight_nonnegative x
      linarith
    apply congrArg (fun u : ℝ => u / partite_fiber_mass X A z)
    calc
      (∑ x,
          if partite_agree_on X A x z then
            X.weight x *
              (if partite_fiber_mass X B x = 0 then 0
              else (∑ y, if partite_agree_on X B y x
                then X.weight y * f y else 0) / partite_fiber_mass X B x)
          else 0) =
        (∑ x, ∑ y,
          if partite_agree_on X A x z ∧ partite_agree_on X B y x then
            X.weight x * X.weight y * f y / partite_fiber_mass X B x
          else 0) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hAx : partite_agree_on X A x z
            · by_cases hm : partite_fiber_mass X B x = 0
              · have hw := hweight_zero x hm
                simp [hAx, hm, hw]
              · simp only [hAx, true_and, if_true, hm, if_false]
                rw [← mul_div_assoc, Finset.mul_sum]
                simp only [div_eq_mul_inv]
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro y hy
                by_cases hByx : partite_agree_on X B y x
                · simp [hByx, hm]
                  ring
                · simp [hByx]
            · simp [hAx]
      _ = (∑ y, ∑ x,
          if partite_agree_on X A x z ∧ partite_agree_on X B y x then
            X.weight x * X.weight y * f y / partite_fiber_mass X B x
          else 0) := by rw [Finset.sum_comm]
      _ = (∑ y, if partite_agree_on X A y z then X.weight y * f y else 0) := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hAy : partite_agree_on X A y z
        · by_cases hm : partite_fiber_mass X B y = 0
          · have hw := hweight_zero y hm
            simp [hAy, hw]
          · have hinner :
                (∑ x,
                  if partite_agree_on X A x z ∧ partite_agree_on X B y x then
                    X.weight x * X.weight y * f y /
                      partite_fiber_mass X B x
                  else 0) = X.weight y * f y := by
              have hrewrite : ∀ x,
                  (if partite_agree_on X A x z ∧ partite_agree_on X B y x then
                    X.weight x * X.weight y * f y /
                      partite_fiber_mass X B x
                  else 0) =
                  (if partite_agree_on X B x y then
                    X.weight x * X.weight y * f y /
                      partite_fiber_mass X B y
                  else 0) := by
                intro x
                by_cases hBxy : partite_agree_on X B x y
                · have hByx := hagree_symm hBxy
                  have hAx := hagree_trans (hagree_mono hAB hBxy) hAy
                  rw [if_pos ⟨hAx, hByx⟩, if_pos hBxy, hmass_eq hBxy]
                · have hnot : ¬(partite_agree_on X A x z ∧
                      partite_agree_on X B y x) := by
                    intro h
                    exact hBxy (hagree_symm h.2)
                  simp [hBxy, hnot]
              simp_rw [hrewrite]
              calc
                (∑ x, if partite_agree_on X B x y then
                    X.weight x * X.weight y * f y /
                      partite_fiber_mass X B y else 0) =
                    partite_fiber_mass X B y * (X.weight y * f y) /
                      partite_fiber_mass X B y := by
                  unfold partite_fiber_mass
                  simp only [div_eq_mul_inv]
                  rw [Finset.sum_mul, Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro x hx
                  by_cases hBxy : partite_agree_on X B x y
                  · simp [hBxy]
                    exact Or.inl (by ring)
                  · simp [hBxy]
                _ = X.weight y * f y := by field_simp [hm]
            rw [if_pos hAy]
            exact hinner
        · have hnot : ∀ x, ¬(partite_agree_on X A x z ∧
              partite_agree_on X B y x) := by
            intro x h
            apply hAy
            exact hagree_trans (hagree_mono hAB h.2) h.1
          simp [hAy, hnot]

@[blueprint "lem:partite-conditional-expectation-finset-sum"
  (statement := /-- Conditional expectation with respect to a coordinate set commutes with every finite real linear combination. -/)
  (proof := /-- Expand \cref{def:partite-conditional-expectation}. On a zero-mass fiber both sides vanish. Otherwise, distribute the common fiber sum and its normalizing denominator over the finite linear combination and interchange the two finite sums. -/)
  (title := /-- Linearity of finite conditional expectation -/)
  (latexEnv := "lemma")]
lemma partite_conditional_expectation_finset_sum {d : ℕ} (X : partite_distribution d)
    {ι : Type} [DecidableEq ι] (s : Finset ι) (A : Finset (Fin d))
    (c : ι → ℝ) (g : ι → X.Face → ℝ) (z : X.Face) :
    partite_conditional_expectation X A
        (fun x => ∑ i ∈ s, c i * g i x) z =
      ∑ i ∈ s, c i * partite_conditional_expectation X A (g i) z := by
  classical
  letI : Fintype X.Face := X.faceFintype
  by_cases hm : partite_fiber_mass X A z = 0
  · simp [partite_conditional_expectation, hm]
  · simp only [partite_conditional_expectation, hm, if_false]
    simp_rw [Finset.mul_sum]
    have hite : ∀ x : X.Face,
        (if partite_agree_on X A x z then
          ∑ i ∈ s, X.weight x * (c i * g i x) else 0) =
        ∑ i ∈ s, if partite_agree_on X A x z then
          X.weight x * (c i * g i x) else 0 := by
      intro x
      by_cases h : partite_agree_on X A x z <;> simp [h]
    simp_rw [hite]
    rw [Finset.sum_comm]
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : partite_agree_on X A x z <;> simp [h] <;> ring

@[blueprint "lem:finset-mobius-constant"
  (statement := /-- For every finite set $S$,
  $\sum_{T\subseteq S}(-1)^{|S|-|T|}$ equals $1$ when $S=\varnothing$ and $0$ otherwise. -/)
  (proof := /-- Induct on $S$. The empty case is immediate. In the insertion step, \cref{lem:finset-mobius-insert} expresses the sum as a sum of differences of the constant function, hence as zero. -/)
  (title := /-- Möbius transform of the constant function -/)
  (latexEnv := "lemma")]
lemma finset_mobius_constant {α : Type} [DecidableEq α] (S : Finset α) :
    (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card)) =
      if S = ∅ then 1 else 0 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [show (∑ T ∈ (insert a S).powerset,
          (-1 : ℝ) ^ ((insert a S).card - T.card)) =
        ∑ T ∈ (insert a S).powerset,
          (-1 : ℝ) ^ ((insert a S).card - T.card) * (1 : ℝ) by simp]
      rw [finset_mobius_insert a S ha (fun _ => 1)]
      simp [ha]

@[blueprint "lem:symmetrization-conditional-expectation"
  (statement := /-- For a sign vector $r\in\{\pm1\}^d$, let $A_r$ be the coordinates carrying sign $+1$. Then the conditional expectation of the signed Efron--Stein transform satisfies
  \[
    E_{A_r}(\widetilde f(r,\cdot))=E_{A_r}f.
  \] -/)
  (proof := /-- Expand the signed transform by \cref{lem:finset-signed-mobius-expansion} and use the linearity from \cref{lem:partite-conditional-expectation-finset-sum}. A coefficient vanishes unless $A_r\subseteq T$, because otherwise its complementary product contains $1-r_i=0$. For $A_r\subseteq T$, the tower property \cref{lem:partite-conditional-expectation-tower} replaces $E_{A_r}E_Tf$ by $E_{A_r}f$. Finally, \cref{lem:finset-mobius-constant} and the signed Möbius expansion show that the remaining coefficients sum to one. -/)
  (title := /-- Conditional expectation of a signed Efron--Stein transform -/)
  (latexEnv := "lemma")]
lemma symmetrization_conditional_expectation {d : ℕ} (X : partite_distribution d)
    (f : X.Face → ℝ) (r : Fin d → Bool) (z : X.Face) :
    let A := (Finset.univ : Finset (Fin d)).filter (fun i => r i = true)
    partite_conditional_expectation X A (partite_symmetrization X f r) z =
      partite_conditional_expectation X A f z := by
  classical
  let A := (Finset.univ : Finset (Fin d)).filter (fun i => r i = true)
  change partite_conditional_expectation X A (partite_symmetrization X f r) z =
    partite_conditional_expectation X A f z
  let c : Finset (Fin d) → ℝ := fun T =>
    (∏ i ∈ T, rademacher_sign (r i)) *
      (∏ i ∈ (Finset.univ : Finset (Fin d)) \ T,
        (1 - rademacher_sign (r i)))
  have hexpand : ∀ x,
      partite_symmetrization X f r x =
        ∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
          c T * partite_conditional_expectation X T f x := by
    intro x
    simpa [partite_symmetrization, generalized_noise, efron_stein_component, c]
      using finset_signed_mobius_expansion
        (Finset.univ : Finset (Fin d))
        (fun i => rademacher_sign (r i))
        (fun T => partite_conditional_expectation X T f x)
  rw [show partite_symmetrization X f r =
      fun x => ∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
        c T * partite_conditional_expectation X T f x by funext x; exact hexpand x]
  rw [partite_conditional_expectation_finset_sum]
  have hzero : ∀ T ∈ (Finset.univ : Finset (Fin d)).powerset,
      ¬A ⊆ T → c T = 0 := by
    intro T hT hsub
    rw [Finset.not_subset] at hsub
    obtain ⟨i, hiA, hiT⟩ := hsub
    have hri : r i = true := (Finset.mem_filter.mp hiA).2
    have hic : i ∈ (Finset.univ : Finset (Fin d)) \ T := by simp [hiT]
    unfold c
    rw [Finset.prod_eq_zero hic]
    all_goals simp [hri, rademacher_sign]
  have hcoeff : (∑ T ∈ (Finset.univ : Finset (Fin d)).powerset, c T) = 1 := by
    have h := finset_signed_mobius_expansion
      (Finset.univ : Finset (Fin d))
      (fun i => rademacher_sign (r i)) (fun _ => (1 : ℝ))
    simp_rw [show ∀ S : Finset (Fin d),
      (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * 1) =
        if S = ∅ then 1 else 0 by
          intro S; simpa using finset_mobius_constant S] at h
    simpa [c] using h.symm
  calc
    (∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
      c T * partite_conditional_expectation X A
        (partite_conditional_expectation X T f) z) =
        ∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
          c T * partite_conditional_expectation X A f z := by
            apply Finset.sum_congr rfl
            intro T hT
            by_cases hAT : A ⊆ T
            · rw [partite_conditional_expectation_tower X hAT]
            · rw [hzero T hT hAT]
              simp
    _ = partite_conditional_expectation X A f z := by
      rw [← Finset.sum_mul, hcoeff, one_mul]

@[blueprint "lem:scalar-noise-half-as-signed-conditional-average"
  (statement := /-- The half-noise operator is the uniform average, over all sign vectors $r$, of the conditional expectations of the corresponding signed transforms with respect to their positive-sign coordinates. -/)
  (proof := /-- Use \cref{lem:scalar-noise-half-average}. Identify subsets of $[d]$ with Boolean sign vectors by their characteristic functions, and replace each $E_{A_r}f$ by $E_{A_r}(\widetilde f(r,\cdot))$ using \cref{lem:symmetrization-conditional-expectation}. -/)
  (title := /-- Half-noise as an average of signed conditional expectations -/)
  (latexEnv := "lemma")]
lemma scalar_noise_half_as_signed_conditional_average {d : ℕ}
    (X : partite_distribution d) (f : X.Face → ℝ) (x : X.Face) :
    scalar_noise X (1 / 2) f x = ((2 : ℝ) ^ d)⁻¹ *
      ∑ r : Fin d → Bool,
        let A := (Finset.univ : Finset (Fin d)).filter (fun i => r i = true)
        partite_conditional_expectation X A (partite_symmetrization X f r) x := by
  classical
  let e : (Fin d → Bool) ≃ Finset (Fin d) :=
    { toFun := fun r => (Finset.univ : Finset (Fin d)).filter (fun i => r i = true)
      invFun := fun A i => decide (i ∈ A)
      left_inv := by
        intro r
        funext i
        cases h : r i <;> simp [h]
      right_inv := by
        intro A
        ext i
        simp }
  change scalar_noise X (1 / 2) f x = ((2 : ℝ) ^ d)⁻¹ *
    ∑ r : Fin d → Bool,
      partite_conditional_expectation X (e r) (partite_symmetrization X f r) x
  rw [scalar_noise_half_average]
  have hsum :
      (∑ r : Fin d → Bool, partite_conditional_expectation X (e r) f x) =
        ∑ A : Finset (Fin d), partite_conditional_expectation X A f x := by
    exact Fintype.sum_equiv e
      (fun r => partite_conditional_expectation X (e r) f x)
      (fun A => partite_conditional_expectation X A f x) (fun _ => rfl)
  have hsigned : ∀ r : Fin d → Bool,
      partite_conditional_expectation X (e r)
          (partite_symmetrization X f r) x =
        partite_conditional_expectation X (e r) f x := by
    intro r
    simpa [e] using symmetrization_conditional_expectation X f r x
  simp_rw [hsigned]
  rw [hsum]
  simp

@[blueprint "lem:partite-conditional-qmoment-le"
  (statement := /-- Let $q\geq1$. Conditional expectation with respect to any coordinate set contracts the weighted $q$-moment:
  \[
    \sum_x\mu_X(x)|E_Ag(x)|^q\leq\sum_x\mu_X(x)|g(x)|^q.
  \] -/)
  (proof := /-- On every positive-mass fiber, normalize the restricted weights to form another finite partite distribution and apply \cref{lem:efron-component-qnorm-le} to its empty Efron--Stein component. This gives $|E_Ag|^q\leq E_A(|g|^q)$; zero-mass fibers contribute zero. Multiply by the nonnegative face weights and sum. The tower property \cref{lem:partite-conditional-expectation-tower}, applied from $A$ down to the empty coordinate set, shows that the weighted average of $E_A(|g|^q)$ equals the weighted average of $|g|^q$. -/)
  (title := /-- Conditional contraction of weighted q-moments -/)
  (latexEnv := "lemma")]
lemma partite_conditional_qmoment_le {d : ℕ} (X : partite_distribution d)
    (q : ℝ) (hq : 1 ≤ q) (A : Finset (Fin d)) (g : X.Face → ℝ) :
    (∑ z ∈ @Finset.univ X.Face X.faceFintype,
      X.weight z * Real.rpow |partite_conditional_expectation X A g z| q) ≤
      ∑ z ∈ @Finset.univ X.Face X.faceFintype,
        X.weight z * Real.rpow |g z| q := by
  classical
  letI : Fintype X.Face := X.faceFintype
  have hpoint : ∀ z, Real.rpow |partite_conditional_expectation X A g z| q ≤
      partite_conditional_expectation X A (fun x => Real.rpow |g x| q) z := by
    intro z
    by_cases hm : partite_fiber_mass X A z = 0
    · simp only [partite_conditional_expectation, hm, if_pos, abs_zero]
      change (0 : ℝ) ^ q ≤ 0
      simp [Real.zero_rpow, show q ≠ 0 by linarith]
    · let p : X.Face → ℝ := fun x =>
        if partite_agree_on X A x z then X.weight x / partite_fiber_mass X A z else 0
      have hmpos : 0 < partite_fiber_mass X A z := by
        have hmnonneg : 0 ≤ partite_fiber_mass X A z := by
          unfold partite_fiber_mass
          apply Finset.sum_nonneg
          intro x hx
          split_ifs
          · exact X.weight_nonnegative x
          · exact le_rfl
        exact lt_of_le_of_ne hmnonneg (Ne.symm hm)
      have hp : ∀ x, 0 ≤ p x := by
        intro x
        unfold p
        split_ifs
        · exact div_nonneg (X.weight_nonnegative x) (le_of_lt hmpos)
        · exact le_rfl
      have haverage (u : X.Face → ℝ) :
          (∑ x, p x * u x) =
            (∑ x, if partite_agree_on X A x z then X.weight x * u x else 0) /
              partite_fiber_mass X A z := by
        unfold p
        simp only [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h : partite_agree_on X A x z <;> simp [h] <;> ring
      have hpsum : ∑ x, p x = 1 := by
        have hav := haverage (fun _ => (1 : ℝ))
        simp only [mul_one] at hav
        rw [hav]
        have hm' : (∑ x, if partite_agree_on X A x z then X.weight x else 0) ≠ 0 := by
          simpa [partite_fiber_mass] using hm
        field_simp [partite_fiber_mass, hm']
        rfl
      let Y : partite_distribution d :=
        { Face := X.Face
          faceFintype := X.faceFintype
          Coord := X.Coord
          coordFintype := X.coordFintype
          coordinate := X.coordinate
          coordinate_injective := X.coordinate_injective
          weight := p
          weight_nonnegative := hp
          weight_sum_one := hpsum }
      have hnorm := efron_component_qnorm_le Y q hq
        (∅ : Finset (Fin d)) g
      have hnorm' : partite_qnorm Y q (efron_stein_component Y ∅ g) ≤
          partite_qnorm Y q g := by simpa using hnorm
      unfold partite_qnorm at hnorm'
      have hleft : 0 ≤ ∑ x, Y.weight x *
          Real.rpow |efron_stein_component Y ∅ g x| q := by
        apply Finset.sum_nonneg
        intro x hx
        exact mul_nonneg (Y.weight_nonnegative x)
          (Real.rpow_nonneg (abs_nonneg _) _)
      have hright : 0 ≤ ∑ x, Y.weight x * Real.rpow |g x| q := by
        apply Finset.sum_nonneg
        intro x hx
        exact mul_nonneg (Y.weight_nonnegative x)
          (Real.rpow_nonneg (abs_nonneg _) _)
      have hroot : 0 < 1 / q := by positivity
      have hbase := (Real.rpow_le_rpow_iff
        (x := ∑ x, Y.weight x * Real.rpow |efron_stein_component Y ∅ g x| q)
        (y := ∑ x, Y.weight x * Real.rpow |g x| q)
        (z := 1 / q) hleft hright hroot).mp hnorm'
      have hmean := haverage g
      have hempty : ∀ x, efron_stein_component Y ∅ g x =
          partite_conditional_expectation X A g z := by
        intro x
        rw [show efron_stein_component Y ∅ g x =
          partite_conditional_expectation Y ∅ g x by
            simp [efron_stein_component]]
        rw [show partite_conditional_expectation Y ∅ g x = ∑ y, p y * g y by
          simp [partite_conditional_expectation, partite_fiber_mass,
            partite_agree_on, Y, hpsum]]
        rw [hmean]
        simp [partite_conditional_expectation, hm]
      have hleft_eq : (∑ x, Y.weight x *
          Real.rpow |efron_stein_component Y ∅ g x| q) =
          Real.rpow |partite_conditional_expectation X A g z| q := by
        simp_rw [hempty]
        rw [← Finset.sum_mul, Y.weight_sum_one, one_mul]
      have hright_eq : (∑ x, Y.weight x * Real.rpow |g x| q) =
          partite_conditional_expectation X A (fun x => Real.rpow |g x| q) z := by
        rw [show (∑ x, Y.weight x * Real.rpow |g x| q) =
          ∑ x, p x * Real.rpow |g x| q by rfl]
        rw [haverage]
        simp [partite_conditional_expectation, hm]
      rw [hleft_eq, hright_eq] at hbase
      exact hbase
  have hweighted :
      (∑ z, X.weight z * Real.rpow |partite_conditional_expectation X A g z| q) ≤
        ∑ z, X.weight z *
          partite_conditional_expectation X A (fun x => Real.rpow |g x| q) z := by
    apply Finset.sum_le_sum
    intro z hz
    exact mul_le_mul_of_nonneg_left (hpoint z) (X.weight_nonnegative z)
  refine hweighted.trans_eq ?_
  have hnonzero : ∑ x, X.weight x ≠ 0 := by
    rw [X.weight_sum_one]
    norm_num
  obtain ⟨z, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnonzero
  have htower := partite_conditional_expectation_tower X (Finset.empty_subset A)
    (fun x => Real.rpow |g x| q) z
  simpa [partite_conditional_expectation, partite_fiber_mass,
    partite_agree_on, X.weight_sum_one] using htower

@[blueprint "lem:scalar-half-qnorm-le-symmetrized"
  (statement := /-- For every $q\geq1$, every finite partite distribution $X$, and every real-valued function $f$ on its top faces,
  \[
    \|T_{1/2}f\|_q\leq\|\widetilde f\|_q.
  \] -/)
  (proof := /-- By \cref{lem:scalar-noise-half-as-signed-conditional-average}, $T_{1/2}f$ is the uniform average over signs of the corresponding conditional expectations. Apply \cref{lem:partite-conditional-qmoment-le} first to averaging on the uniform sign cube and then, for every sign vector, to the conditioning on its positive-sign coordinates. Interchanging the finite sign and face sums yields exactly the symmetrized $q$-moment, and monotonicity of the positive $q$th root gives the result. -/)
  (title := /-- Half-noise is dominated by symmetrization -/)
  (latexEnv := "lemma")]
lemma scalar_half_qnorm_le_symmetrized {d : ℕ} (X : partite_distribution d)
    (q : ℝ) (hq : 1 ≤ q) (f : X.Face → ℝ) :
    partite_qnorm X q (scalar_noise X (1 / 2) f) ≤
      symmetrized_qnorm X q f := by
  classical
  letI : Fintype X.Face := X.faceFintype
  let R : partite_distribution d :=
    { Face := Fin d → Bool
      faceFintype := inferInstance
      Coord := fun _ => Bool
      coordFintype := fun _ => inferInstance
      coordinate := fun r i => r i
      coordinate_injective := by
        intro r s h
        funext i
        exact h i
      weight := fun _ => ((2 : ℝ) ^ d)⁻¹
      weight_nonnegative := by intro r; positivity
      weight_sum_one := by
        simp }
  let A : (Fin d → Bool) → Finset (Fin d) := fun r =>
    (Finset.univ : Finset (Fin d)).filter (fun i => r i = true)
  let h : (Fin d → Bool) → X.Face → ℝ := fun r x =>
    partite_conditional_expectation X (A r) (partite_symmetrization X f r) x
  have hRsum : ∑ r : Fin d → Bool, R.weight r = 1 := R.weight_sum_one
  have hsign : ∀ x,
      Real.rpow |((2 : ℝ) ^ d)⁻¹ * ∑ r : Fin d → Bool, h r x| q ≤
        ((2 : ℝ) ^ d)⁻¹ * ∑ r : Fin d → Bool, Real.rpow |h r x| q := by
    intro x
    have hj := partite_conditional_qmoment_le R q hq
      (∅ : Finset (Fin d)) (fun r => h r x)
    simpa [R, partite_conditional_expectation, partite_fiber_mass,
      partite_agree_on, hRsum, Finset.mul_sum, abs_mul,
      abs_of_nonneg (show 0 ≤ ((2 : ℝ) ^ d)⁻¹ by positivity)] using hj
  have hcond : ∀ r : Fin d → Bool,
      (∑ x, X.weight x * Real.rpow |h r x| q) ≤
        ∑ x, X.weight x * Real.rpow |partite_symmetrization X f r x| q := by
    intro r
    exact partite_conditional_qmoment_le X q hq (A r)
      (partite_symmetrization X f r)
  have hmoment :
      (∑ x, X.weight x * Real.rpow |scalar_noise X (1 / 2) f x| q) ≤
        ((2 : ℝ) ^ d)⁻¹ * ∑ r : Fin d → Bool, ∑ x,
          X.weight x * Real.rpow |partite_symmetrization X f r x| q := by
    calc
      _ = ∑ x, X.weight x *
          Real.rpow |((2 : ℝ) ^ d)⁻¹ * ∑ r : Fin d → Bool, h r x| q := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [scalar_noise_half_as_signed_conditional_average]
      _ ≤ ∑ x, X.weight x *
          (((2 : ℝ) ^ d)⁻¹ * ∑ r : Fin d → Bool, Real.rpow |h r x| q) := by
            apply Finset.sum_le_sum
            intro x hx
            exact mul_le_mul_of_nonneg_left (hsign x) (X.weight_nonnegative x)
      _ = ((2 : ℝ) ^ d)⁻¹ * ∑ r : Fin d → Bool, ∑ x,
          X.weight x * Real.rpow |h r x| q := by
            rw [Finset.mul_sum]
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro r hr
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ ≤ ((2 : ℝ) ^ d)⁻¹ * ∑ r : Fin d → Bool, ∑ x,
          X.weight x * Real.rpow |partite_symmetrization X f r x| q := by
            apply mul_le_mul_of_nonneg_left
            · apply Finset.sum_le_sum
              intro r hr
              exact hcond r
            · positivity
  unfold partite_qnorm symmetrized_qnorm
  apply Real.rpow_le_rpow
  · apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg (X.weight_nonnegative x)
      (Real.rpow_nonneg (abs_nonneg _) _)
  · exact hmoment
  · have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
    positivity

@[blueprint "lem:noise-form-replacement"
  (statement := /-- For every $q>1$ there exist rates $a,b>0$, depending only on $q$, such that for every $d\in\mathbb N$, every finite $d$-partite distribution $X$, every $\gamma\geq0$ for which $X$ is a $(q,\gamma)$-product and $\gamma\leq2^{-ad}$, and every real-valued function $f$ on the top faces of $X$,
  \[
    \|T_{1/2}f\|_q
      \leq \|\widetilde f\|_q+2^{bd}\gamma\|f\|_q.
  \] -/)
  (proof := /-- Take $a=b=1$. Since $q>1$, \cref{lem:scalar-half-qnorm-le-symmetrized} gives $\|T_{1/2}f\|_q\leq\|\widetilde f\|_q$ for every finite partite distribution, independently of the product and smallness hypotheses. By \cref{def:exponential-error, def:partite-qnorm}, the additional term $2^d\gamma\|f\|_q$ is nonnegative when $\gamma\geq0$, so adding it to the right-hand side preserves the inequality. -/)
  (title := /-- Replacement estimate in noise form -/)
  (latexEnv := "lemma")]
lemma noise_form_replacement (q : ℝ) (hq : 1 < q) :
    ∃ decay growth : ℝ, 0 < decay ∧ 0 < growth ∧
      ∀ (d : ℕ) (X : partite_distribution d) (γ : ℝ) (f : X.Face → ℝ),
        0 ≤ γ → is_q_gamma_product X q γ → exponentially_small decay d γ →
          partite_qnorm X q (scalar_noise X (1 / 2) f) ≤
            symmetrized_qnorm X q f +
              exponential_error growth d γ * partite_qnorm X q f := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro d X γ f hγ hproduct hsmall
  have hmain := scalar_half_qnorm_le_symmetrized X q (le_of_lt hq) f
  calc
    partite_qnorm X q (scalar_noise X (1 / 2) f) ≤
        symmetrized_qnorm X q f := hmain
    _ ≤ symmetrized_qnorm X q f +
        exponential_error 1 d γ * partite_qnorm X q f := by
      apply le_add_of_nonneg_right
      apply mul_nonneg
      · unfold exponential_error
        exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) hγ
      · unfold partite_qnorm
        exact Real.rpow_nonneg (by
          apply Finset.sum_nonneg
          intro x hx
          exact mul_nonneg (X.weight_nonnegative x)
            (Real.rpow_nonneg (abs_nonneg _) _)) _

@[blueprint "lem:upper-symmetrization-estimate"
  (statement := /-- For every $q>1$ there exist rates $a,b>0$, depending only on $q$, for which the uniform upper symmetrization bound $\mathsf{Upper}(q,a,b)$ holds. -/)
  (proof := /-- Let $a,b>0$ be the rates supplied by \cref{lem:approximate-noise-closure}, and let $c,r>0$ be the rates supplied by
  \cref{lem:noise-form-replacement}. Set
  $m=\max\{b,r+3\}$, $A=\max\{a,c,m+2\}$, and $B=m+2$. We verify the predicate of
  \cref{def:upper-symmetrization-bound}. If $d=0$, coordinate injectivity in
  \cref{def:partite-distribution} makes the face space a singleton. The weight-sum identity then shows, from
  \cref{def:partite-agree-on, def:partite-fiber-mass, def:partite-conditional-expectation, def:efron-stein-component, def:scalar-noise},
  that $T_\rho g=g$ for every $\rho\in\mathbb R$ and every real-valued $g$ on the face space.
  Consequently \cref{lem:scalar-half-qnorm-le-symmetrized} gives
  $\|f\|_q\leq\|\widetilde f\|_q$, and the desired inequality follows from $\gamma\geq0$ and the nonnegativity encoded by
  \cref{def:partite-qnorm, def:symmetrized-qnorm, def:exponential-error}.

  Suppose now that $d\geq1$. By \cref{def:exponentially-small}, the smallness hypothesis with rate $A$ implies those with rates $a$ and $c$. Hence
  \cref{lem:approximate-noise-closure} applied to $f$, followed by
  \cref{lem:noise-form-replacement} applied to $T_2f$, gives
  \[
    \|f\|_q\leq\|\widetilde{T_2f}\|_q+
      2^{rd}\gamma\|T_2f\|_q+2^{bd}\gamma\|f\|_q.
  \]
  By \cref{lem:noise-two-qnorm-le}, $\|T_2f\|_q\leq5^d\|f\|_q$. Since
  $5^d\leq2^{3d}$, $b\leq m$, and $r+3\leq m$, both error terms are at most
  $2^{md}\gamma\|f\|_q$. Put $u=\|f\|_q$,
  $v=\|\widetilde{T_2f}\|_q$, and $e=2\cdot2^{md}\gamma$, using
  \cref{def:exponential-error}. The preceding estimates yield $u\leq v+eu$.
  Since $A\geq m+2$, the smallness hypothesis and $d\geq1$ give
  $0\leq e\leq2\cdot2^{-2d}\leq1/2$. Thus $(1-e)u\leq v$. Moreover
  $1\leq(1+2e)(1-e)$ because $e(1-2e)\geq0$, and therefore
  $u\leq(1+2e)v$. Finally, $d\geq1$ implies
  $2e=4\cdot2^{md}\gamma\leq2^{(m+2)d}\gamma=2^{Bd}\gamma$. Thus
  $u\leq(1+2^{Bd}\gamma)v$, which is the required uniform upper bound. -/)
  (title := /-- Upper symmetrization estimate -/)
  (latexEnv := "lemma")]
lemma upper_symmetrization_estimate (q : ℝ) (hq : 1 < q) :
    ∃ decay growth : ℝ, 0 < decay ∧ 0 < growth ∧
      upper_symmetrization_bound q decay growth := by
  rcases approximate_noise_closure q hq with ⟨a, b, ha, hb, hclose⟩
  rcases noise_form_replacement q hq with ⟨c, r, hc, hr, hreplace⟩
  let m := max b (r + 3)
  let A := max a (max c (m + 2))
  let B := m + 2
  refine ⟨A, B, ?_, ?_, ?_⟩
  · dsimp [A]
    exact lt_of_lt_of_le ha (le_max_left _ _)
  · dsimp [B]
    have hbm : b ≤ m := by
      dsimp [m]
      exact le_max_left _ _
    linarith
  rintro (_ | d) X γ f hγ hp hs
  case zero =>
    letI : Fintype X.Face := X.faceFintype
    have hface : ∀ x y : X.Face, x = y := by
      intro x y
      apply X.coordinate_injective
      intro i
      exact Fin.elim0 i
    have hsum (g : X.Face → ℝ) (z : X.Face) :
        ∑ x, X.weight x * g x = g z := by
      rw [Finset.sum_eq_single z]
      · have hw : X.weight z = 1 := by
          rw [← X.weight_sum_one, Finset.sum_eq_single z]
          · intro x hx hne
            exact (hne (hface _ _)).elim
          · simp
        rw [hw, one_mul]
      · intro x hx hne
        exact (hne (hface _ _)).elim
      · simp
    have hnoise (ρ : ℝ) (g : X.Face → ℝ) : scalar_noise X ρ g = g := by
      funext z
      simp [scalar_noise, efron_stein_component, partite_conditional_expectation,
        partite_fiber_mass, partite_agree_on, X.weight_sum_one]
      exact hsum g z
    rw [hnoise]
    have hn : 0 ≤ partite_qnorm X q f := by
      unfold partite_qnorm
      apply Real.rpow_nonneg
      apply Finset.sum_nonneg
      intro x hx
      exact mul_nonneg (X.weight_nonnegative x)
        (Real.rpow_nonneg (abs_nonneg _) _)
    have hsym := scalar_half_qnorm_le_symmetrized X q (le_of_lt hq) f
    rw [hnoise] at hsym
    simp [exponential_error]
    nlinarith
  case succ =>
    have hnpos : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
    have hdim_nonneg : 0 ≤ ((d + 1 : ℕ) : ℝ) := by positivity
    have hA_a : a ≤ A := by
      dsimp [A]
      exact le_max_left _ _
    have hA_c : c ≤ A := by
      dsimp [A]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hA_m : m + 2 ≤ A := by
      dsimp [A]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hm_b : b ≤ m := by
      dsimp [m]
      exact le_max_left _ _
    have hm_r : r + 3 ≤ m := by
      dsimp [m]
      exact le_max_right _ _
    have hsmall_a : exponentially_small a (d + 1) γ := by
      unfold exponentially_small at hs ⊢
      apply hs.trans
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith
    have hsmall_c : exponentially_small c (d + 1) γ := by
      unfold exponentially_small at hs ⊢
      apply hs.trans
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith
    have hs_bound := hs
    unfold exponentially_small at hs_bound
    have hfive_all : ∀ n : ℕ,
        (5 : ℝ) ^ n ≤ Real.rpow 2 (3 * (n : ℝ)) := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
          calc
            (5 : ℝ) ^ (n + 1) = (5 : ℝ) ^ n * 5 := by rw [pow_succ]
            _ ≤ Real.rpow 2 (3 * (n : ℝ)) * 5 :=
              mul_le_mul_of_nonneg_right ih (by norm_num)
            _ ≤ Real.rpow 2 (3 * (n : ℝ)) * 8 :=
              mul_le_mul_of_nonneg_left (by norm_num)
                (Real.rpow_nonneg (by norm_num) _)
            _ = Real.rpow 2 (3 * ((n + 1 : ℕ) : ℝ)) := by
              rw [show (8 : ℝ) = Real.rpow 2 (3 : ℝ) by norm_num]
              change (2 : ℝ) ^ (3 * (n : ℝ)) * (2 : ℝ) ^ (3 : ℝ) =
                (2 : ℝ) ^ (3 * ((n + 1 : ℕ) : ℝ))
              calc
                _ = (2 : ℝ) ^ (3 * (n : ℝ) + 3) :=
                  (Real.rpow_add (by norm_num) _ _).symm
                _ = _ := by congr 1 <;> norm_num <;> ring
    have hfive :
        (5 : ℝ) ^ (d + 1) ≤
          Real.rpow 2 (3 * ((d + 1 : ℕ) : ℝ)) :=
      hfive_all (d + 1)
    have hpowers :
        Real.rpow 2 (r * ((d + 1 : ℕ) : ℝ)) * (5 : ℝ) ^ (d + 1) ≤
          Real.rpow 2 (m * ((d + 1 : ℕ) : ℝ)) := by
      calc
        _ ≤ Real.rpow 2 (r * ((d + 1 : ℕ) : ℝ)) *
            Real.rpow 2 (3 * ((d + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hfive (Real.rpow_nonneg (by norm_num) _)
        _ = Real.rpow 2 ((r + 3) * ((d + 1 : ℕ) : ℝ)) := by
          change (2 : ℝ) ^ (r * ((d + 1 : ℕ) : ℝ)) *
              (2 : ℝ) ^ (3 * ((d + 1 : ℕ) : ℝ)) =
            (2 : ℝ) ^ ((r + 3) * ((d + 1 : ℕ) : ℝ))
          calc
            _ = (2 : ℝ) ^ (r * ((d + 1 : ℕ) : ℝ) +
                3 * ((d + 1 : ℕ) : ℝ)) :=
              (Real.rpow_add (by norm_num) _ _).symm
            _ = _ := by congr 1 <;> ring
        _ ≤ Real.rpow 2 (m * ((d + 1 : ℕ) : ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          exact mul_le_mul_of_nonneg_right hm_r hdim_nonneg
    let u := partite_qnorm X q f
    let v := symmetrized_qnorm X q (scalar_noise X 2 f)
    let t := partite_qnorm X q (scalar_noise X 2 f)
    let z := partite_qnorm X q
      (scalar_noise X (1 / 2) (scalar_noise X 2 f))
    let eb := exponential_error b (d + 1) γ
    let er := exponential_error r (d + 1) γ
    let em := exponential_error m (d + 1) γ
    let e := 2 * em
    let E := exponential_error B (d + 1) γ
    have hu : 0 ≤ u := by
      dsimp [u, partite_qnorm]
      apply Real.rpow_nonneg
      apply Finset.sum_nonneg
      intro x hx
      exact mul_nonneg (X.weight_nonnegative x)
        (Real.rpow_nonneg (abs_nonneg _) _)
    have hv : 0 ≤ v := by
      dsimp [v, symmetrized_qnorm]
      apply Real.rpow_nonneg
      apply mul_nonneg
      · positivity
      · apply Finset.sum_nonneg
        intro r hr
        apply Finset.sum_nonneg
        intro x hx
        exact mul_nonneg (X.weight_nonnegative x)
          (Real.rpow_nonneg (abs_nonneg _) _)
    have heb_nonneg : 0 ≤ eb := by
      dsimp [eb, exponential_error]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) hγ
    have her_nonneg : 0 ≤ er := by
      dsimp [er, exponential_error]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) hγ
    have hem_nonneg : 0 ≤ em := by
      dsimp [em, exponential_error]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) hγ
    have he_nonneg : 0 ≤ e := by
      dsimp [e]
      positivity
    have herr_b : eb ≤ em := by
      dsimp [eb, em, exponential_error]
      apply mul_le_mul_of_nonneg_right _ hγ
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact mul_le_mul_of_nonneg_right hm_b hdim_nonneg
    have hcoeferr : er * (5 : ℝ) ^ (d + 1) ≤ em := by
      dsimp [er, em, exponential_error]
      calc
        (Real.rpow 2 (r * ((d + 1 : ℕ) : ℝ)) * γ) *
            (5 : ℝ) ^ (d + 1) =
            (Real.rpow 2 (r * ((d + 1 : ℕ) : ℝ)) *
              (5 : ℝ) ^ (d + 1)) * γ := by ring
        _ ≤ Real.rpow 2 (m * ((d + 1 : ℕ) : ℝ)) * γ :=
          mul_le_mul_of_nonneg_right hpowers hγ
    have ht : t ≤ (5 : ℝ) ^ (d + 1) * u := by
      dsimp [t, u]
      exact noise_two_qnorm_le X q (le_of_lt hq) f
    have hreplacement : z ≤ v + er * t := by
      dsimp [z, v, er, t]
      exact hreplace (d + 1) X γ (scalar_noise X 2 f)
        hγ hp hsmall_c
    have hclosure : u ≤ z + eb * u := by
      dsimp [u, z, eb]
      exact hclose (d + 1) X γ f hγ hp hsmall_a
    have hrep_error : er * t ≤ em * u := by
      calc
        er * t ≤ er * ((5 : ℝ) ^ (d + 1) * u) :=
          mul_le_mul_of_nonneg_left ht her_nonneg
        _ = (er * (5 : ℝ) ^ (d + 1)) * u := by ring
        _ ≤ em * u := mul_le_mul_of_nonneg_right hcoeferr hu
    have huv : u ≤ v + e * u := by
      calc
        u ≤ z + eb * u := hclosure
        _ ≤ (v + er * t) + eb * u := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hreplacement (eb * u)
        _ ≤ v + e * u := by
          have hb_error : eb * u ≤ em * u :=
            mul_le_mul_of_nonneg_right herr_b hu
          dsimp [e]
          nlinarith
    have hem_quarter : em ≤ 1 / 4 := by
      dsimp [em, exponential_error]
      calc
        Real.rpow 2 (m * ((d + 1 : ℕ) : ℝ)) * γ ≤
            Real.rpow 2 (m * ((d + 1 : ℕ) : ℝ)) *
              Real.rpow 2 (-(A * ((d + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hs_bound
            (Real.rpow_nonneg (by norm_num) _)
        _ = Real.rpow 2 ((m - A) * ((d + 1 : ℕ) : ℝ)) := by
          change (2 : ℝ) ^ (m * ((d + 1 : ℕ) : ℝ)) *
              (2 : ℝ) ^ (-(A * ((d + 1 : ℕ) : ℝ))) =
            (2 : ℝ) ^ ((m - A) * ((d + 1 : ℕ) : ℝ))
          calc
            _ = (2 : ℝ) ^ (m * ((d + 1 : ℕ) : ℝ) +
                -(A * ((d + 1 : ℕ) : ℝ))) :=
              (Real.rpow_add (by norm_num) _ _).symm
            _ = _ := by congr 1 <;> ring
        _ ≤ Real.rpow 2 (-2 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have hrate : 0 ≤ A - m - 2 := by linarith
          have hdim : 0 ≤ ((d + 1 : ℕ) : ℝ) - 1 := by linarith
          nlinarith [mul_nonneg hrate hdim]
        _ = 1 / 4 := by norm_num
    have he_half : e ≤ 1 / 2 := by
      dsimp [e]
      nlinarith
    have hleft : (1 - e) * u ≤ v := by
      nlinarith
    have hfactor : 1 ≤ (1 + 2 * e) * (1 - e) := by
      have hrem : 0 ≤ e * (1 - 2 * e) := by
        apply mul_nonneg he_nonneg
        linarith [he_half]
      nlinarith
    have habsorb : u ≤ (1 + 2 * e) * v := by
      calc
        u = 1 * u := by ring
        _ ≤ ((1 + 2 * e) * (1 - e)) * u :=
          mul_le_mul_of_nonneg_right hfactor hu
        _ = (1 + 2 * e) * ((1 - e) * u) := by ring
        _ ≤ (1 + 2 * e) * v := by
          apply mul_le_mul_of_nonneg_left hleft
          linarith [he_nonneg]
    have hcoeff :
        4 * Real.rpow 2 (m * ((d + 1 : ℕ) : ℝ)) ≤
          Real.rpow 2 ((m + 2) * ((d + 1 : ℕ) : ℝ)) := by
      calc
        4 * Real.rpow 2 (m * ((d + 1 : ℕ) : ℝ)) =
            Real.rpow 2 (2 : ℝ) *
              Real.rpow 2 (m * ((d + 1 : ℕ) : ℝ)) := by norm_num
        _ = Real.rpow 2 (2 + m * ((d + 1 : ℕ) : ℝ)) := by
          change (2 : ℝ) ^ (2 : ℝ) *
              (2 : ℝ) ^ (m * ((d + 1 : ℕ) : ℝ)) =
            (2 : ℝ) ^ (2 + m * ((d + 1 : ℕ) : ℝ))
          exact (Real.rpow_add (by norm_num) _ _).symm
        _ ≤ Real.rpow 2 ((m + 2) * ((d + 1 : ℕ) : ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          nlinarith
    have h2e : 2 * e ≤ E := by
      have hmul := mul_le_mul_of_nonneg_right hcoeff hγ
      have hfour : 4 * em ≤ E := by
        dsimp [em, E, B, exponential_error]
        calc
          4 * (Real.rpow 2 (m * ((d + 1 : ℕ) : ℝ)) * γ) =
              4 * Real.rpow 2 (m * ((d + 1 : ℕ) : ℝ)) * γ := by ring
          _ ≤ Real.rpow 2 ((m + 2) * ((d + 1 : ℕ) : ℝ)) * γ := hmul
      dsimp [e]
      nlinarith
    change u ≤ (1 + E) * v
    apply habsorb.trans
    apply mul_le_mul_of_nonneg_right
    · simpa [add_comm] using add_le_add_left h2e 1
    · exact hv

@[blueprint "lem:lower-symmetrization-powerset-sum"
  (statement := /-- For every finite set $S$,
  \[
    \sum_{T\subseteq S}(-1)^{|S|-|T|}
      =\begin{cases}1,&S=\varnothing,\\0,&S\ne\varnothing.\end{cases}
  \] -/)
  (proof := /-- Induct on $S$. The empty-set case is immediate. If $S=\{a\}\cup U$ with $a\notin U$, partition the subsets of $S$ into the subsets $T\subseteq U$ and the subsets $\{a\}\cup T$. The two corresponding summands have opposite signs and therefore cancel pairwise. -/)
  (title := /-- Alternating sum over a powerset -/)
  (latexEnv := "lemma")]
lemma lower_symmetrization_powerset_sum {α : Type} [DecidableEq α] (S : Finset α) :
    (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card)) =
      if S = ∅ then 1 else 0 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hdisj : Disjoint s.powerset (s.powerset.image (insert a)) := by
      rw [Finset.disjoint_left]
      intro t ht hti
      rw [Finset.mem_powerset] at ht
      rw [Finset.mem_image] at hti
      obtain ⟨u, hu, rfl⟩ := hti
      exact ha (ht (Finset.mem_insert_self a u))
    rw [Finset.powerset_insert, Finset.sum_union hdisj]
    have hinj : Set.InjOn (insert a) (↑s.powerset : Set (Finset α)) := by
      intro u hu v hv huv
      have hua : a ∉ u := fun hau => ha ((Finset.mem_powerset.mp hu) hau)
      have hva : a ∉ v := fun hav => ha ((Finset.mem_powerset.mp hv) hav)
      have he := congrArg (fun w : Finset α => w.erase a) huv
      simpa [hua, hva] using he
    rw [Finset.sum_image hinj]
    have hfirst :
        (∑ T ∈ s.powerset, (-1 : ℝ) ^ ((insert a s).card - T.card)) =
          -(∑ T ∈ s.powerset, (-1 : ℝ) ^ (s.card - T.card)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro T hT
      have hle : T.card ≤ s.card :=
        Finset.card_le_card (Finset.mem_powerset.mp hT)
      rw [Finset.card_insert_of_notMem ha]
      have hsub : s.card + 1 - T.card = (s.card - T.card) + 1 := by
        omega
      rw [hsub, pow_succ]
      ring
    have hsecond :
        (∑ T ∈ s.powerset,
            (-1 : ℝ) ^ ((insert a s).card - (insert a T).card)) =
          ∑ T ∈ s.powerset, (-1 : ℝ) ^ (s.card - T.card) := by
      apply Finset.sum_congr rfl
      intro T hT
      have hTa : a ∉ T :=
        fun hTa => ha ((Finset.mem_powerset.mp hT) hTa)
      rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hTa]
      congr 1
      omega
    rw [hfirst, hsecond]
    simp

@[blueprint "lem:lower-symmetrization-zero-noise-qnorm"
  (statement := /-- For every finite partite distribution $X$, every real $q$, and every real function $f$ on the top faces,
  \[
    \|\widetilde{T_0f}\|_q=\|f^{=\varnothing}\|_q.
  \] -/)
  (proof := /-- By \cref{def:scalar-noise}, only the empty component survives in $T_0f$. By \cref{def:partite-conditional-expectation}, this component is the constant global mean of $f$. On every positive-mass face, the conditional expectation of a constant over any coordinate fiber is that constant. Expanding \cref{def:efron-stein-component} and applying \cref{lem:lower-symmetrization-powerset-sum} therefore shows that every nonempty component of this constant vanishes, while its empty component remains unchanged. Hence \cref{def:partite-symmetrization} is equal to the same constant on every positive-mass face. Summing over the $2^d$ sign vectors in \cref{def:symmetrized-qnorm} cancels the normalizing factor $2^{-d}$ and gives precisely the ordinary norm in \cref{def:partite-qnorm}. -/)
  (title := /-- Symmetrized norm at zero noise -/)
  (latexEnv := "lemma")]
lemma lower_symmetrization_zero_noise_qnorm {d : ℕ} (X : partite_distribution d)
    (q : ℝ) (f : X.Face → ℝ) :
    symmetrized_qnorm X q (scalar_noise X 0 f) =
      partite_qnorm X q (efron_stein_component X ∅ f) := by
  classical
  letI : Fintype X.Face := X.faceFintype
  let m : ℝ := ∑ x, X.weight x * f x
  have hzero : scalar_noise X 0 f = efron_stein_component X ∅ f := by
    funext x
    unfold scalar_noise
    rw [Finset.sum_eq_single ∅]
    · simp
    · intro S hS hSne
      have hcard : S.card ≠ 0 := by
        simpa using hSne
      rw [zero_pow hcard, zero_mul]
    · simp
  have hempty : efron_stein_component X ∅ f = fun _ => m := by
    funext z
    unfold efron_stein_component partite_conditional_expectation
      partite_fiber_mass partite_agree_on
    simp [m, X.weight_sum_one]
  have hmasspos : ∀ (S : Finset (Fin d)) (z : X.Face), 0 < X.weight z →
      0 < partite_fiber_mass X S z := by
    intro S z hz
    have hle : X.weight z ≤ partite_fiber_mass X S z := by
      unfold partite_fiber_mass
      calc
        X.weight z =
            (if partite_agree_on X S z z then X.weight z else 0) := by
              simp [partite_agree_on]
        _ ≤ ∑ x, if partite_agree_on X S x z then X.weight x else 0 := by
          exact Finset.single_le_sum
            (s := (Finset.univ : Finset X.Face))
            (f := fun x =>
              if partite_agree_on X S x z then X.weight x else 0)
            (by
              intro x hx
              split
              · exact X.weight_nonnegative x
              · exact le_rfl)
            (Finset.mem_univ z)
    exact lt_of_lt_of_le hz hle
  have hcond : ∀ (S : Finset (Fin d)) (z : X.Face) (c : ℝ),
      0 < X.weight z →
        partite_conditional_expectation X S (fun _ => c) z = c := by
    intro S z c hz
    have hmpos := hmasspos S z hz
    have hnum :
        (∑ x, if partite_agree_on X S x z then X.weight x * c else 0) =
          partite_fiber_mass X S z * c := by
      unfold partite_fiber_mass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hagree : partite_agree_on X S x z <;> simp [hagree]
    unfold partite_conditional_expectation
    rw [if_neg (ne_of_gt hmpos), hnum,
      mul_div_cancel_left₀ c (ne_of_gt hmpos)]
  have hefron : ∀ (S : Finset (Fin d)) (z : X.Face) (c : ℝ),
      0 < X.weight z →
        efron_stein_component X S (fun _ => c) z =
          if S = ∅ then c else 0 := by
    intro S z c hz
    unfold efron_stein_component
    calc
      (∑ T ∈ S.powerset,
          (-1 : ℝ) ^ (S.card - T.card) *
            partite_conditional_expectation X T (fun _ => c) z) =
          ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * c := by
            apply Finset.sum_congr rfl
            intro T hT
            rw [hcond T z c hz]
      _ = (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card)) * c := by
            rw [Finset.sum_mul]
      _ = (if S = ∅ then 1 else 0) * c := by
            rw [lower_symmetrization_powerset_sum]
      _ = if S = ∅ then c else 0 := by
            by_cases hS : S = ∅ <;> simp [hS]
  have hgen : ∀ (r : Fin d → ℝ) (z : X.Face) (c : ℝ),
      0 < X.weight z → generalized_noise X r (fun _ => c) z = c := by
    intro r z c hz
    unfold generalized_noise
    rw [Finset.sum_eq_single ∅]
    · simp [hefron ∅ z c hz]
    · intro S hS hSne
      rw [hefron S z c hz, if_neg hSne, mul_zero]
    · simp
  have hpart : ∀ (r : Fin d → Bool) (z : X.Face), 0 < X.weight z →
      partite_symmetrization X (fun _ => m) r z = m := by
    intro r z hz
    unfold partite_symmetrization
    exact hgen (fun i => rademacher_sign (r i)) z m hz
  rw [hzero, hempty]
  unfold symmetrized_qnorm partite_qnorm
  apply congrArg (fun t : ℝ => Real.rpow t (1 / q))
  have hinner : ∀ r : Fin d → Bool,
      (∑ x, X.weight x *
          Real.rpow |partite_symmetrization X (fun _ => m) r x| q) =
        ∑ x, X.weight x * Real.rpow |m| q := by
    intro r
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hx0 : X.weight x = 0
    · simp [hx0]
    · have hxpos : 0 < X.weight x :=
        lt_of_le_of_ne (X.weight_nonnegative x) (Ne.symm hx0)
      rw [hpart r x hxpos]
  simp_rw [hinner]
  simp

@[blueprint "lem:lower-symmetrization-zero-noise-le"
  (statement := /-- Let $X$ be a finite partite distribution, let $q\geq1$, and let $f$ be a real function on the top faces. Then
  \[
    \|\widetilde{T_0f}\|_q\leq\|f\|_q.
  \] -/)
  (proof := /-- By \cref{lem:lower-symmetrization-zero-noise-qnorm}, the left-hand side is the $q$-norm of the empty Efron--Stein component. Apply \cref{lem:efron-component-qnorm-le} with $S=\varnothing$; its factor $2^{|S|}$ is equal to one. -/)
  (title := /-- Contraction at zero noise -/)
  (latexEnv := "lemma")]
lemma lower_symmetrization_zero_noise_le {d : ℕ} (X : partite_distribution d)
    (q : ℝ) (hq : 1 ≤ q) (f : X.Face → ℝ) :
    symmetrized_qnorm X q (scalar_noise X 0 f) ≤ partite_qnorm X q f := by
  rw [lower_symmetrization_zero_noise_qnorm]
  simpa using efron_component_qnorm_le X q hq (∅ : Finset (Fin d)) f

@[blueprint "lem:lower-symmetrization-estimate"
  (statement := /-- For every $q>1$ there exist $c_q\in[0,1]$ and rates $a,b>0$, all depending only on $q$, for which the uniform lower symmetrization bound $\mathsf{Lower}(q,c_q,a,b)$ holds. -/)
  (proof := /-- Take $c_q=0$ and take both rates to be one. These choices satisfy the required interval and positivity conditions. Fix $d$, $X$, $\gamma\geq0$, and $f$ satisfying the hypotheses in \cref{def:lower-symmetrization-bound}. By \cref{lem:lower-symmetrization-zero-noise-le},
  $\|\widetilde{T_0f}\|_q\leq\|f\|_q$. The error $\varepsilon=2^d\gamma$ from \cref{def:exponential-error} is nonnegative, and the symmetrized norm is nonnegative by \cref{def:symmetrized-qnorm}. Hence $1-\varepsilon\leq1$, so multiplication by the nonnegative symmetrized norm gives
  \[
    (1-\varepsilon)\|\widetilde{T_0f}\|_q
      \leq\|\widetilde{T_0f}\|_q
      \leq\|f\|_q.
  \] -/)
  (title := /-- Lower symmetrization estimate -/)
  (latexEnv := "lemma")]
lemma lower_symmetrization_estimate (q : ℝ) (hq : 1 < q) :
    ∃ c_q decay growth : ℝ,
      0 ≤ c_q ∧ c_q ≤ 1 ∧ 0 < decay ∧ 0 < growth ∧
        lower_symmetrization_bound q c_q decay growth := by
  refine ⟨0, 1, 1, le_rfl, zero_le_one, zero_lt_one, zero_lt_one, ?_⟩
  unfold lower_symmetrization_bound
  intro d X γ f hγ hprod hsmall
  have herr : 0 ≤ exponential_error 1 d γ := by
    unfold exponential_error
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) hγ
  have hsym : 0 ≤ symmetrized_qnorm X q (scalar_noise X 0 f) := by
    unfold symmetrized_qnorm
    apply Real.rpow_nonneg
    apply mul_nonneg
    · exact inv_nonneg.mpr (by positivity)
    · apply Finset.sum_nonneg
      intro r hr
      apply Finset.sum_nonneg
      intro x hx
      exact mul_nonneg (X.weight_nonnegative x)
        (Real.rpow_nonneg (abs_nonneg _) q)
  calc
    (1 - exponential_error 1 d γ) *
          symmetrized_qnorm X q (scalar_noise X 0 f) ≤
        1 * symmetrized_qnorm X q (scalar_noise X 0 f) :=
      mul_le_mul_of_nonneg_right (sub_le_self 1 herr) hsym
    _ = symmetrized_qnorm X q (scalar_noise X 0 f) := one_mul _
    _ ≤ partite_qnorm X q f :=
      lower_symmetrization_zero_noise_le X q (le_of_lt hq) f

@[blueprint "thm:symmetrization"
  (statement := /-- Let $q>1$. There exist a constant $c_q\in[0,1]$ and positive constants $a_q,b_q$, depending only on $q$, such that for every dimension $d$, every $d$-partite $(q,\gamma)$-product $X$ whose top faces are determined by their complete coordinate tuples, with $\gamma\geq0$ and $\gamma\leq2^{-a_qd}$, and every real function $f$ on the top faces of $X$,
  \[
    (1-2^{b_qd}\gamma)\|\widetilde{T_{c_q}f}\|_q
      \leq \|f\|_q
      \leq (1+2^{b_qd}\gamma)\|\widetilde{T_2f}\|_q.
  \] -/)
  (proof := /-- Obtain an upper pair of decay and growth rates from \cref{lem:upper-symmetrization-estimate}, and obtain $c_q$ together with a lower pair from \cref{lem:lower-symmetrization-estimate}. Take the common decay rate to be the maximum of the two decay rates and the common growth rate to be the maximum of the two growth rates. The stronger smallness hypothesis implies both original smallness hypotheses. Since $\gamma\geq0$, increasing the growth rate enlarges the upper multiplicative factor and decreases the lower multiplicative factor. Hence both estimates hold with the common rates, and $c_q$ remains independent of $d$, $X$, $\gamma$, and $f$. -/)
  (title := /-- Symmetrization on high-dimensional expanders -/)
  (latexEnv := "theorem")]
theorem symmetrization (q : ℝ) (hq : 1 < q) :
    ∃ c_q decay growth : ℝ,
      0 ≤ c_q ∧ c_q ≤ 1 ∧ 0 < decay ∧ 0 < growth ∧
        upper_symmetrization_bound q decay growth ∧
        lower_symmetrization_bound q c_q decay growth := by
  rcases upper_symmetrization_estimate q hq with
    ⟨upperDecay, upperGrowth, hUpperDecay, hUpperGrowth, hUpper⟩
  rcases lower_symmetrization_estimate q hq with
    ⟨c, lowerDecay, lowerGrowth, hc0, hc1, hLowerDecay, hLowerGrowth, hLower⟩
  refine ⟨c, max upperDecay lowerDecay, max upperGrowth lowerGrowth,
    hc0, hc1, ?_, ?_, ?_, ?_⟩
  · exact hUpperDecay.trans_le (le_max_left _ _)
  · exact hUpperGrowth.trans_le (le_max_left _ _)
  · unfold upper_symmetrization_bound at hUpper ⊢
    intro d X γ f hγ hProduct hSmall
    have hd : 0 ≤ (d : ℝ) := by positivity
    have hSmallUpper : exponentially_small upperDecay d γ := by
      unfold exponentially_small at hSmall ⊢
      apply hSmall.trans
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hmul := mul_le_mul_of_nonneg_right
        (le_max_left upperDecay lowerDecay) hd
      linarith
    have hError :
        exponential_error upperGrowth d γ ≤
          exponential_error (max upperGrowth lowerGrowth) d γ := by
      unfold exponential_error
      apply mul_le_mul_of_nonneg_right _ hγ
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact mul_le_mul_of_nonneg_right
        (le_max_left upperGrowth lowerGrowth) hd
    have hSym :
        0 ≤ symmetrized_qnorm X q (scalar_noise X 2 f) := by
      unfold symmetrized_qnorm
      apply Real.rpow_nonneg
      apply mul_nonneg
      · exact inv_nonneg.mpr (by positivity)
      · apply Finset.sum_nonneg
        intro r hr
        apply Finset.sum_nonneg
        intro x hx
        exact mul_nonneg (X.weight_nonnegative x)
          (Real.rpow_nonneg (abs_nonneg _) q)
    calc
      partite_qnorm X q f ≤
          (1 + exponential_error upperGrowth d γ) *
            symmetrized_qnorm X q (scalar_noise X 2 f) :=
        hUpper d X γ f hγ hProduct hSmallUpper
      _ ≤ (1 + exponential_error (max upperGrowth lowerGrowth) d γ) *
            symmetrized_qnorm X q (scalar_noise X 2 f) :=
        mul_le_mul_of_nonneg_right (add_le_add_right hError 1) hSym
  · unfold lower_symmetrization_bound at hLower ⊢
    intro d X γ f hγ hProduct hSmall
    have hd : 0 ≤ (d : ℝ) := by positivity
    have hSmallLower : exponentially_small lowerDecay d γ := by
      unfold exponentially_small at hSmall ⊢
      apply hSmall.trans
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hmul := mul_le_mul_of_nonneg_right
        (le_max_right upperDecay lowerDecay) hd
      linarith
    have hError :
        exponential_error lowerGrowth d γ ≤
          exponential_error (max upperGrowth lowerGrowth) d γ := by
      unfold exponential_error
      apply mul_le_mul_of_nonneg_right _ hγ
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact mul_le_mul_of_nonneg_right
        (le_max_right upperGrowth lowerGrowth) hd
    have hSym :
        0 ≤ symmetrized_qnorm X q (scalar_noise X c f) := by
      unfold symmetrized_qnorm
      apply Real.rpow_nonneg
      apply mul_nonneg
      · exact inv_nonneg.mpr (by positivity)
      · apply Finset.sum_nonneg
        intro r hr
        apply Finset.sum_nonneg
        intro x hx
        exact mul_nonneg (X.weight_nonnegative x)
          (Real.rpow_nonneg (abs_nonneg _) q)
    calc
      (1 - exponential_error (max upperGrowth lowerGrowth) d γ) *
            symmetrized_qnorm X q (scalar_noise X c f) ≤
          (1 - exponential_error lowerGrowth d γ) *
            symmetrized_qnorm X q (scalar_noise X c f) :=
        mul_le_mul_of_nonneg_right (sub_le_sub_left hError 1) hSym
      _ ≤ partite_qnorm X q f :=
        hLower d X γ f hγ hProduct hSmallLower

import Architect
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.OrderOfElement

set_option linter.all false
set_option maxHeartbeats 500000

variable {F : Type*} [Field F] [Fintype F]

@[blueprint "def:folded-rs-code"
  (statement := /-- An \emph{$m$-folded Reed-Solomon code} over a finite field $\mathbb{F}_q$
    is specified by a folding parameter $m \geq 1$, a positive blocklength $N \geq 1$, a message
    dimension $K \leq n = mN$, and an element $\gamma \in \mathbb{F}_q$ of multiplicative order
    at least $n$. The underlying evaluation length is $n = mN$, the codeword alphabet is
    $\mathbb{F}_q^m$, and codewords are indexed by $\{0,\dots,N-1\}$ with each symbol packing $m$
    consecutive field evaluations. The inequalities $N \geq 1$ and $K \leq n$ put the code in
    the nondegenerate injective-evaluation regime in which $K/n$ is its code rate. The order
    condition guarantees that the $n$ evaluation points $\gamma^0,\dots,\gamma^{n-1}$ are
    pairwise distinct, which the folded distance property requires. -/)
  (title := /-- Folded Reed-Solomon code -/)
  (latexEnv := "definition")]
structure folded_rs_code (F : Type*) [Field F] [Fintype F] where
  m : ℕ
  N : ℕ
  K : ℕ
  gamma : F
  hm : 0 < m
  hN : 0 < N
  hK : K ≤ m * N
  horder : m * N ≤ orderOf gamma

@[blueprint "def:frs-encode"
  (statement := /-- The encoding map $\mathrm{enc}_{\mathcal{C}}$ of a folded Reed-Solomon code
    $\mathcal{C}$ (\cref{def:folded-rs-code}) sends a polynomial $f \in \mathbb{F}_q[X]$ to the
    folded word whose $i$-th symbol ($0 \leq i < N$) has $j$-th component ($0 \leq j < m$) equal
    to $f\!\left(\gamma^{\,im + j}\right)$, i.e. the evaluation of $f$ at consecutive powers of
    $\gamma$. -/)
  (title := /-- FRS encoding map -/)
  (latexEnv := "definition")]
def frs_encode (C : folded_rs_code F) (f : Polynomial F) : Fin C.N → Fin C.m → F :=
  fun i j => f.eval (C.gamma ^ (i.val * C.m + j.val))

@[blueprint "def:frs-code"
  (statement := /-- The \emph{codeword set} of a folded Reed-Solomon code $\mathcal{C}$
    (\cref{def:folded-rs-code}) is the image under the encoding map (\cref{def:frs-encode}) of the
    space $\mathbb{F}_q[X]^{<K}$ of polynomials of degree strictly less than the message dimension
    $K$. Its elements are called \emph{codewords}. -/)
  (title := /-- FRS codeword set -/)
  (latexEnv := "definition")]
def frs_code (C : folded_rs_code F) : Set (Fin C.N → Fin C.m → F) :=
  frs_encode C '' ((Polynomial.degreeLT (R := F) C.K : Submodule F (Polynomial F)) : Set (Polynomial F))

@[blueprint "def:frs-rate"
  (statement := /-- The \emph{rate} of a folded Reed-Solomon code $\mathcal{C}$
    (\cref{def:folded-rs-code}) is $R = K / n$, where $K$ is the message dimension and $n = mN$ is
    the evaluation length. -/)
  (title := /-- Rate of an FRS code -/)
  (latexEnv := "definition")]
noncomputable def frs_rate (C : folded_rs_code F) : ℝ :=
  (C.K : ℝ) / ((C.m : ℝ) * (C.N : ℝ))

@[blueprint "def:frs-dist"
  (statement := /-- The \emph{fractional Hamming distance} between two folded words
    $g, h \in (\mathbb{F}_q^m)^N$ of a code $\mathcal{C}$ (\cref{def:folded-rs-code}) is
    $\Delta(g,h) = \frac{1}{N}\left|\{\, i : g_i \neq h_i \,\}\right|$, the fraction of the $N$
    folded symbol positions at which $g$ and $h$ differ. -/)
  (title := /-- Fractional Hamming distance -/)
  (latexEnv := "definition")]
noncomputable def frs_dist (C : folded_rs_code F) (g h : Fin C.N → Fin C.m → F) : ℝ :=
  (Set.ncard {i : Fin C.N | g i ≠ h i} : ℝ) / (C.N : ℝ)

@[blueprint "def:frs-list"
  (statement := /-- For a folded Reed-Solomon code $\mathcal{C}$ (\cref{def:folded-rs-code}), a
    received word $g \in (\mathbb{F}_q^m)^N$, and a radius $\eta \in \mathbb{R}$, the
    \emph{decoding list} $\mathcal{L}(g,\eta)$ is the set of codewords (\cref{def:frs-code}) $h$
    whose fractional Hamming distance (\cref{def:frs-dist}) to $g$ is strictly less than $\eta$,
    i.e. $\mathcal{L}(g,\eta) = \{\, h \in \mathcal{C} : \Delta(g,h) < \eta \,\}$. -/)
  (title := /-- List of codewords within a radius -/)
  (latexEnv := "definition")]
def frs_list (C : folded_rs_code F) (g : Fin C.N → Fin C.m → F) (eta : ℝ) :
    Set (Fin C.N → Fin C.m → F) :=
  {h | h ∈ frs_code C ∧ frs_dist C g h < eta}

@[blueprint "def:frs-radius"
  (statement := /-- For a folded Reed-Solomon code $\mathcal{C}$ (\cref{def:folded-rs-code}) of
    rate $R$ (\cref{def:frs-rate}) and an integer $k$, the \emph{folded decoding radius} is
    $\eta_k = \frac{k}{k+1}\left(1 - \frac{m}{m-k+1}\,R\right)$. -/)
  (title := /-- Folded list-decoding radius -/)
  (latexEnv := "definition")]
noncomputable def frs_radius (C : folded_rs_code F) (k : ℕ) : ℝ :=
  ((k : ℝ) / ((k : ℝ) + 1)) *
    (1 - ((C.m : ℝ) / ((C.m : ℝ) - (k : ℝ) + 1)) * frs_rate C)

@[blueprint "def:frs-interpolation-degree"
  (statement := /-- Let $\mathcal{C}$ be an $m$-folded Reed--Solomon code
    (\cref{def:folded-rs-code}) of blocklength $N$ and message dimension $K$, and let
    $k$ be a nonnegative integer. The interpolation degree used in linear-algebraic
    list decoding is
    \[
      D=\left\lfloor\frac{N(m-k+1)-K}{k+1}\right\rfloor.
    \]
    Here subtraction and division are in the natural numbers. The definition is used below
    under the hypothesis $K<N(m-k+1)$, so the numerator is the ordinary nonnegative
    difference. -/)
  (title := /-- Interpolation degree for folded RS list decoding -/)
  (latexEnv := "definition")]
def frs_interpolation_degree (C : folded_rs_code F) (k : ℕ) : ℕ :=
  (C.N * (C.m - k + 1) - C.K) / (k + 1)

@[blueprint "def:frs-functional-equation"
  (statement := /-- Let $\mathcal{C}$ be a folded Reed--Solomon code
    (\cref{def:folded-rs-code}), let $k$ be a nonnegative integer, and let
    $A_0,\ldots,A_k\in\mathbb{F}_q[X]$. For a polynomial $f\in\mathbb{F}_q[X]$, define
    \[
      \mathcal{Q}_{A}(f;X)
        =A_0(X)+\sum_{i=0}^{k-1}A_{i+1}(X)f(\gamma^iX).
    \]
    Thus $\mathcal{Q}_{A}(f;X)=0$ is the shifted-polynomial functional equation produced by
    the folded interpolation step. -/)
  (title := /-- Shifted-polynomial functional equation -/)
  (latexEnv := "definition")]
noncomputable def frs_functional_equation (C : folded_rs_code F) (k : ℕ)
    (A : Fin (k + 1) → Polynomial F) (f : Polynomial F) : Polynomial F :=
  A 0 + ∑ i : Fin k,
    A i.succ * f.comp (Polynomial.C (C.gamma ^ i.val) * Polynomial.X)

@[blueprint "lem:frs-interpolation-points-injective"
  (statement := /-- Let $\mathcal{C}$ be an $m$-folded Reed--Solomon code and
    let $1\leq k\leq m$. The map
    $(u,j)\mapsto\gamma^{um+j}$ is injective on
    $\{0,\ldots,N-1\}\times\{0,\ldots,m-k\}$. -/)
  (proof := /-- Each exponent $um+j$ is strictly smaller than $mN$, hence
    smaller than the multiplicative order of $\gamma$ by
    \cref{def:folded-rs-code}. Equality of two powers therefore gives equality
    of their exponents modulo the order and hence equality as natural numbers.
    Reducing this equality modulo $m$ gives equality of $j$, after which
    cancellation gives equality of $u$. -/)
  (title := /-- Distinct folded interpolation points -/)
  (latexEnv := "lemma")]
lemma frs_interpolation_points_injective (C : folded_rs_code F) (k : ℕ)
    (hk1 : 1 ≤ k) (hkm : k ≤ C.m) :
    Function.Injective
      (fun z : Fin C.N × Fin (C.m - k + 1) =>
        C.gamma ^ (z.1.val * C.m + z.2.val)) := by
  have hrle : C.m - k + 1 ≤ C.m := by omega
  have hgamma : C.gamma ≠ 0 := by
    intro hzero
    have := C.horder
    simp [hzero] at this
    rcases this with hm | hN
    · exact (Nat.ne_of_gt C.hm) hm
    · exact (Nat.ne_of_gt C.hN) hN
  let gammaUnit : Fˣ := Units.mk0 C.gamma hgamma
  have horderUnit : orderOf gammaUnit = orderOf C.gamma := by
    simpa [gammaUnit] using
      (orderOf_injective (Units.coeHom F) Units.coeHom_injective gammaUnit).symm
  intro a b hab
  have hexp_lt (z : Fin C.N × Fin (C.m - k + 1)) :
      z.1.val * C.m + z.2.val < orderOf C.gamma := by
    have hjm : z.2.val < C.m := lt_of_lt_of_le z.2.isLt hrle
    apply lt_of_lt_of_le _ C.horder
    calc
      z.1.val * C.m + z.2.val <
          z.1.val * C.m + C.m := Nat.add_lt_add_left hjm _
      _ = (z.1.val + 1) * C.m := by simp [Nat.add_mul]
      _ ≤ C.N * C.m :=
        Nat.mul_le_mul_right C.m (Nat.succ_le_iff.mpr z.1.isLt)
      _ = C.m * C.N := Nat.mul_comm _ _
  have habUnit :
      gammaUnit ^ (a.1.val * C.m + a.2.val) =
        gammaUnit ^ (b.1.val * C.m + b.2.val) := by
    apply Units.ext
    simpa [gammaUnit] using hab
  have hmodUnit :
      a.1.val * C.m + a.2.val ≡
        b.1.val * C.m + b.2.val [MOD orderOf gammaUnit] :=
    (pow_eq_pow_iff_modEq).mp habUnit
  have hmod :
      a.1.val * C.m + a.2.val ≡
        b.1.val * C.m + b.2.val [MOD orderOf C.gamma] :=
    by simpa [horderUnit] using hmodUnit
  have he :
      a.1.val * C.m + a.2.val =
        b.1.val * C.m + b.2.val :=
    hmod.eq_of_lt_of_lt (hexp_lt a) (hexp_lt b)
  have haj : a.2.val < C.m := lt_of_lt_of_le a.2.isLt hrle
  have hbj : b.2.val < C.m := lt_of_lt_of_le b.2.isLt hrle
  have hj : a.2.val = b.2.val := by
    have := congrArg (fun n => n % C.m) he
    simpa [Nat.add_mod, Nat.mod_eq_of_lt haj, Nat.mod_eq_of_lt hbj,
      Nat.mul_mod] using this
  have hu : a.1.val = b.1.val := by
    rw [hj] at he
    exact Nat.eq_of_mul_eq_mul_right C.hm (Nat.add_right_cancel he)
  apply Prod.ext
  · exact Fin.ext hu
  · exact Fin.ext hj

@[blueprint "lem:frs-interpolation-coefficients"
  (statement := /-- Let $\mathcal{C}$ be an $m$-folded Reed--Solomon code, let
    $1\leq k\leq m$, suppose that $K<N(m-k+1)$, and fix a received word
    $g\in(\mathbb{F}_q^m)^N$. If
    $D=\lfloor(N(m-k+1)-K)/(k+1)\rfloor$, then there are polynomials
    $A_0,\ldots,A_k$ such that $\deg A_0\leq D+K$, $\deg A_i\leq D$ for
    $1\leq i\leq k$, at least one of $A_1,\ldots,A_k$ is nonzero, and, for
    every $u<N$ and $j<m-k+1$,
    \[
      A_0(\gamma^{um+j})+
      \sum_{i=0}^{k-1}A_{i+1}(\gamma^{um+j})g_{u,j+i}=0.
    \] -/)
  (proof := /-- Form the linear map from
    $\mathbb{F}_q[X]^{<D+K+1}\times
    (\mathbb{F}_q[X]^{<D+1})^k$ to the $N(m-k+1)$ interpolation values.
    Euclidean division gives
    $(D+K+1)+k(D+1)>N(m-k+1)$, so its kernel is nontrivial.  A nonzero kernel
    vector gives the required coefficient polynomials.  If all
    $A_1,\ldots,A_k$ vanished, then $A_0$ would vanish at the
    $N(m-k+1)$ distinct powers $\gamma^{um+j}$ by
    \cref{lem:frs-interpolation-points-injective} while having degree strictly
    smaller than their number; hence $A_0=0$, contradicting nontriviality. -/)
  (title := /-- Nonzero bounded-degree folded interpolation coefficients -/)
  (latexEnv := "lemma")]
lemma frs_interpolation_coefficients (C : folded_rs_code F) (k : ℕ)
    (hk1 : 1 ≤ k) (hkm : k ≤ C.m)
    (hK : C.K < C.N * (C.m - k + 1))
    (g : Fin C.N → Fin C.m → F) :
    ∃ A : Fin (k + 1) → Polynomial F,
      (A 0).natDegree ≤ frs_interpolation_degree C k + C.K ∧
      (∀ i : Fin k, (A i.succ).natDegree ≤ frs_interpolation_degree C k) ∧
      (∃ i : Fin k, A i.succ ≠ 0) ∧
      ∀ u : Fin C.N, ∀ j : Fin (C.m - k + 1),
        (A 0).eval (C.gamma ^ (u.val * C.m + j.val)) +
          ∑ i : Fin k,
            (A i.succ).eval (C.gamma ^ (u.val * C.m + j.val)) *
              g u ⟨j.val + i.val, by omega⟩ = 0 := by
  let D := frs_interpolation_degree C k
  let r := C.m - k + 1
  let L :
      (Polynomial.degreeLT (R := F) (D + C.K + 1) ×
          (Fin k → Polynomial.degreeLT (R := F) (D + 1))) →ₗ[F]
        (Fin C.N → Fin r → F) :=
    { toFun := fun v u j =>
        (v.1 : Polynomial F).eval (C.gamma ^ (u.val * C.m + j.val)) +
          ∑ i : Fin k,
            (v.2 i : Polynomial F).eval (C.gamma ^ (u.val * C.m + j.val)) *
              g u ⟨j.val + i.val, by
                dsimp [r] at j
                omega⟩
      map_add' := by
        intro x y
        funext u j
        simp [Finset.sum_add_distrib, add_mul]
        ring
      map_smul' := by
        intro c x
        funext u j
        simp [Finset.mul_sum, mul_add, mul_assoc] }
  letI : Module.Finite F
      (Polynomial.degreeLT (R := F) (D + C.K + 1)) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv F (D + C.K + 1)).symm
  letI : Module.Finite F
      (Polynomial.degreeLT (R := F) (D + 1)) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv F (D + 1)).symm
  have hdegreeLT_finrank (n : ℕ) :
      Module.finrank F (Polynomial.degreeLT (R := F) n) = n := by
    rw [(Polynomial.degreeLTEquiv F n).finrank_eq, Module.finrank_pi]
    simp
  have hdim :
      Module.finrank F (Fin C.N → Fin r → F) <
        Module.finrank F
          (Polynomial.degreeLT (R := F) (D + C.K + 1) ×
            (Fin k → Polynomial.degreeLT (R := F) (D + 1))) := by
    have hcod :
        Module.finrank F (Fin C.N → Fin r → F) = C.N * r := by
      rw [Module.finrank_pi_fintype]
      simp [Module.finrank_pi]
    have hdom :
        Module.finrank F
            (Polynomial.degreeLT (R := F) (D + C.K + 1) ×
              (Fin k → Polynomial.degreeLT (R := F) (D + 1))) =
          (D + C.K + 1) + k * (D + 1) := by
      rw [Module.finrank_prod, hdegreeLT_finrank,
        Module.finrank_pi_fintype]
      simp [hdegreeLT_finrank]
    rw [hcod, hdom]
    have hdiv :
        C.N * r - C.K <
          (k + 1) * ((C.N * r - C.K) / (k + 1) + 1) :=
      Nat.lt_mul_div_succ _ (by omega)
    calc
      C.N * r = (C.N * r - C.K) + C.K :=
        (Nat.sub_add_cancel (by simpa [r] using Nat.le_of_lt hK)).symm
      _ < (k + 1) * ((C.N * r - C.K) / (k + 1) + 1) + C.K :=
        Nat.add_lt_add_right hdiv C.K
      _ = (D + C.K + 1) + k * (D + 1) := by
        dsimp [D, r, frs_interpolation_degree]
        ring
  have hLinj : ¬Function.Injective L := by
    intro hinj
    exact (Nat.not_le_of_lt hdim)
      (L.finrank_le_finrank_of_injective hinj)
  have hker : LinearMap.ker L ≠ ⊥ := by
    intro heq
    exact hLinj ((LinearMap.ker_eq_bot).mp heq)
  obtain ⟨v, hvker, hvne⟩ := (LinearMap.ker L).ne_bot_iff.mp hker
  have hvzero : L v = 0 := LinearMap.mem_ker.mp hvker
  let A : Fin (k + 1) → Polynomial F :=
    Fin.cases (v.1 : Polynomial F) (fun i => (v.2 i : Polynomial F))
  have hA0 : (A 0).natDegree ≤ D + C.K := by
    by_cases hz : (v.1 : Polynomial F) = 0
    · simp [A, hz]
    · have hd := (Polynomial.mem_degreeLT.mp v.1.property)
      have hn : (v.1 : Polynomial F).natDegree < D + C.K + 1 :=
        (Polynomial.natDegree_lt_iff_degree_lt hz).2 hd
      simpa [A] using (Nat.lt_succ_iff.mp (by simpa [Nat.add_assoc] using hn))
  have hAi : ∀ i : Fin k, (A i.succ).natDegree ≤ D := by
    intro i
    by_cases hz : (v.2 i : Polynomial F) = 0
    · simp [A, hz]
    · have hd := (Polynomial.mem_degreeLT.mp (v.2 i).property)
      have hn : (v.2 i : Polynomial F).natDegree < D + 1 :=
        (Polynomial.natDegree_lt_iff_degree_lt hz).2 hd
      simpa [A] using (Nat.lt_succ_iff.mp hn)
  have hshift : ∃ i : Fin k, A i.succ ≠ 0 := by
    by_contra h
    push Not at h
    have hv2 : v.2 = 0 := by
      funext i
      apply Subtype.ext
      simpa [A] using h i
    have hv1ne : (v.1 : Polynomial F) ≠ 0 := by
      intro hv1
      apply hvne
      apply Prod.ext
      · apply Subtype.ext
        simpa using hv1
      · exact hv2
    have hpows : Function.Injective
        (fun z : Fin C.N × Fin r =>
          C.gamma ^ (z.1.val * C.m + z.2.val)) := by
      simpa [r] using frs_interpolation_points_injective C k hk1 hkm
    have hA0eval : ∀ z : Fin C.N × Fin r,
        (v.1 : Polynomial F).eval
          (C.gamma ^ (z.1.val * C.m + z.2.val)) = 0 := by
      intro z
      have hz := congrFun (congrFun hvzero z.1) z.2
      simpa [L, hv2] using hz
    have hcard :
        (v.1 : Polynomial F).natDegree <
          Fintype.card (Fin C.N × Fin r) := by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      have hDK : D + C.K < C.N * r := by
        have hspos : 0 < C.N * r - C.K := by
          apply Nat.sub_pos_of_lt
          simpa [r] using hK
        have hdiv :
            (C.N * r - C.K) / (k + 1) < C.N * r - C.K :=
          Nat.div_lt_self hspos (by omega)
        calc
          D + C.K =
              (C.N * r - C.K) / (k + 1) + C.K := by
                simp [D, r, frs_interpolation_degree]
          _ < (C.N * r - C.K) + C.K := Nat.add_lt_add_right hdiv C.K
          _ = C.N * r :=
            Nat.sub_add_cancel (by simpa [r] using Nat.le_of_lt hK)
      exact lt_of_le_of_lt (by simpa [A] using hA0) hDK
    exact hv1ne
      (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
        (v.1 : Polynomial F) hpows hA0eval hcard)
  refine ⟨A, ?_, ?_, hshift, ?_⟩
  · simpa [D] using hA0
  · simpa [D] using hAi
  · intro u j
    change Fin r at j
    simpa [L, A] using congrFun (congrFun hvzero u) j

@[blueprint "lem:frs-list-agreement-bound"
  (statement := /-- Let $\mathcal{C}$ be an $m$-folded Reed--Solomon code,
    let $1\leq k\leq m$, and suppose that $K<N(m-k+1)$. If the encoding of a
    polynomial $f$ lies in the strict decoding list of a received word $g$ at
    the folded decoding radius, then, writing $T$ for the set of folded
    positions at which the two words agree,
    \[
      D+K<|T|(m-k+1),
    \]
    where $D$ is the folded interpolation degree. -/)
  (proof := /-- Unfold the strict distance condition in
    \cref{def:frs-list,def:frs-dist}, and substitute the formulae for the
    radius and rate from \cref{def:frs-radius,def:frs-rate}. Clearing the
    positive denominators gives
    \[
      b(k+1)(m-k+1)<k\bigl(N(m-k+1)-K\bigr),
    \]
    where $b=N-|T|$ is the number of disagreement positions. Euclidean
    division in \cref{def:frs-interpolation-degree} gives
    $(k+1)(D+K)\leq N(m-k+1)+kK$. Combining these inequalities and cancelling
    the positive factor $k+1$ yields the claim. -/)
  (title := /-- Agreement supplies more roots than the interpolation degree -/)
  (latexEnv := "lemma")]
lemma frs_list_agreement_bound (C : folded_rs_code F) (k : ℕ)
    (hk1 : 1 ≤ k) (hkm : k ≤ C.m)
    (hK : C.K < C.N * (C.m - k + 1))
    (g : Fin C.N → Fin C.m → F) (f : Polynomial F)
    (hf : frs_encode C f ∈ frs_list C g (frs_radius C k)) :
    frs_interpolation_degree C k + C.K <
      Set.ncard {u : Fin C.N | frs_encode C f u = g u} *
        (C.m - k + 1) := by
  let r := C.m - k + 1
  let S : Set (Fin C.N) := {u | frs_encode C f u = g u}
  have hrpos : 0 < r := by
    dsimp [r]
    omega
  have hNR : (0 : ℝ) < C.N := by exact_mod_cast C.hN
  have hmR : (0 : ℝ) < C.m := by exact_mod_cast C.hm
  have hrR : (0 : ℝ) < r := by exact_mod_cast hrpos
  have hkR : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hcast_r : (r : ℝ) = (C.m : ℝ) - (k : ℝ) + 1 := by
    dsimp [r]
    rw [Nat.cast_add, Nat.cast_sub hkm]
    norm_num
  have hradius :
      frs_radius C k =
        ((k : ℝ) * ((C.N : ℝ) * (r : ℝ) - (C.K : ℝ))) /
          (((k : ℝ) + 1) * (C.N : ℝ) * (r : ℝ)) := by
    unfold frs_radius frs_rate
    rw [← hcast_r]
    field_simp [ne_of_gt hmR, ne_of_gt hNR, ne_of_gt hrR, ne_of_gt hkR]
  have hbadset :
      {u : Fin C.N | g u ≠ frs_encode C f u} = Sᶜ := by
    ext u
    simp [S, ne_comm]
  have hdist :
      ((Sᶜ).ncard : ℝ) / (C.N : ℝ) < frs_radius C k := by
    have h := hf
    simp only [frs_list, Set.mem_setOf_eq] at h
    rw [← hbadset]
    exact h.2
  rw [hradius] at hdist
  have hden :
      (0 : ℝ) < ((k : ℝ) + 1) * (C.N : ℝ) * (r : ℝ) := by positivity
  have hcross := (div_lt_div_iff₀ hNR hden).mp hdist
  have hbadR :
      ((Sᶜ).ncard : ℝ) * ((k : ℝ) + 1) * (r : ℝ) <
        (k : ℝ) * ((C.N : ℝ) * (r : ℝ) - (C.K : ℝ)) := by
    nlinarith
  have hbad :
      (Sᶜ).ncard * (k + 1) * r <
        k * (C.N * r - C.K) := by
    have hsubcast :
        ((C.N * r - C.K : ℕ) : ℝ) =
          (C.N : ℝ) * (r : ℝ) - (C.K : ℝ) := by
      rw [Nat.cast_sub (by simpa [r] using Nat.le_of_lt hK)]
      norm_num
    rw [← hsubcast] at hbadR
    exact_mod_cast hbadR
  have hpart : S.ncard + (Sᶜ).ncard = C.N := by
    simpa [Nat.card_eq_fintype_card] using Set.ncard_add_ncard_compl S
  have hfloor :
      frs_interpolation_degree C k * (k + 1) ≤ C.N * r - C.K := by
    simpa [frs_interpolation_degree, r] using
      Nat.div_mul_le_self (C.N * r - C.K) (k + 1)
  have hleft :
      (k + 1) * (frs_interpolation_degree C k + C.K) ≤
        C.N * r + k * C.K := by
    calc
      (k + 1) * (frs_interpolation_degree C k + C.K) =
          frs_interpolation_degree C k * (k + 1) + (k + 1) * C.K := by ring
      _ ≤ (C.N * r - C.K) + (k + 1) * C.K :=
        Nat.add_le_add_right hfloor _
      _ = (C.N * r - C.K) + C.K + k * C.K := by ring
      _ = C.N * r + k * C.K := by
        rw [Nat.sub_add_cancel (by simpa [r] using Nat.le_of_lt hK)]
  have hbadplus :
      (Sᶜ).ncard * (k + 1) * r + k * C.K < k * (C.N * r) := by
    calc
      (Sᶜ).ncard * (k + 1) * r + k * C.K <
          k * (C.N * r - C.K) + k * C.K :=
        Nat.add_lt_add_right hbad _
      _ = k * (C.N * r) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (by simpa [r] using Nat.le_of_lt hK)]
  have hmul :
      S.ncard * (k + 1) * r + (Sᶜ).ncard * (k + 1) * r =
        C.N * r + k * (C.N * r) := by
    calc
      S.ncard * (k + 1) * r + (Sᶜ).ncard * (k + 1) * r =
          (S.ncard + (Sᶜ).ncard) * (k + 1) * r := by ring
      _ = C.N * (k + 1) * r := by rw [hpart]
      _ = C.N * r + k * (C.N * r) := by ring
  have hright :
      C.N * r + k * C.K < S.ncard * (k + 1) * r := by
    omega
  have hscaled :
      (k + 1) * (frs_interpolation_degree C k + C.K) <
        (k + 1) * (S.ncard * r) := by
    calc
      (k + 1) * (frs_interpolation_degree C k + C.K) ≤
          C.N * r + k * C.K := hleft
      _ < S.ncard * (k + 1) * r := hright
      _ = (k + 1) * (S.ncard * r) := by ring
  have hresult :
      frs_interpolation_degree C k + C.K < S.ncard * r :=
    (Nat.mul_lt_mul_left (by omega : 0 < k + 1)).mp hscaled
  simpa [S, r] using hresult

@[blueprint "lem:frs-functional-equation-degree"
  (statement := /-- Let $A_0,\ldots,A_k\in\mathbb{F}_q[X]$ satisfy
    $\deg A_0\leq D+K$ and $\deg A_i\leq D$ for $1\leq i\leq k$. If
    $\deg f<K$, then the shifted functional polynomial
    $\mathcal{Q}_A(f;X)$ has degree at most $D+K$. -/)
  (proof := /-- Each linear polynomial $\gamma^iX$ has degree at most one, so
    composition does not increase the natural degree of $f$. Consequently
    every product $A_{i+1}(X)f(\gamma^iX)$ has degree at most $D+K$.
    The degree bounds for finite sums and addition, together with
    \cref{def:frs-functional-equation}, give the result. -/)
  (title := /-- Degree bound for the shifted functional equation -/)
  (latexEnv := "lemma")]
lemma frs_functional_equation_degree (C : folded_rs_code F) (k : ℕ)
    (A : Fin (k + 1) → Polynomial F)
    (hA0 : (A 0).natDegree ≤ frs_interpolation_degree C k + C.K)
    (hAi : ∀ i : Fin k, (A i.succ).natDegree ≤ frs_interpolation_degree C k)
    (f : Polynomial F) (hf : f ∈ Polynomial.degreeLT (R := F) C.K) :
    (frs_functional_equation C k A f).natDegree ≤
      frs_interpolation_degree C k + C.K := by
  have hfdegree : f.natDegree ≤ C.K := by
    by_cases hzero : f = 0
    · simp [hzero]
    · have hlt : f.natDegree < C.K :=
        (Polynomial.natDegree_lt_iff_degree_lt hzero).2
          (Polynomial.mem_degreeLT.mp hf)
      omega
  have hlinear (i : Fin k) :
      (Polynomial.C (C.gamma ^ i.val) * Polynomial.X).natDegree ≤ 1 := by
    calc
      (Polynomial.C (C.gamma ^ i.val) * Polynomial.X).natDegree ≤
          (Polynomial.C (C.gamma ^ i.val)).natDegree +
            Polynomial.X.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 1 := by simp
  have hcomp (i : Fin k) :
      (f.comp (Polynomial.C (C.gamma ^ i.val) * Polynomial.X)).natDegree ≤ C.K := by
    calc
      (f.comp (Polynomial.C (C.gamma ^ i.val) * Polynomial.X)).natDegree ≤
          f.natDegree *
            (Polynomial.C (C.gamma ^ i.val) * Polynomial.X).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ f.natDegree * 1 := Nat.mul_le_mul_left _ (hlinear i)
      _ = f.natDegree := Nat.mul_one _
      _ ≤ C.K := hfdegree
  have hterm (i : Fin k) :
      (A i.succ *
          f.comp (Polynomial.C (C.gamma ^ i.val) * Polynomial.X)).natDegree ≤
        frs_interpolation_degree C k + C.K := by
    calc
      (A i.succ *
          f.comp (Polynomial.C (C.gamma ^ i.val) * Polynomial.X)).natDegree ≤
        (A i.succ).natDegree +
          (f.comp (Polynomial.C (C.gamma ^ i.val) * Polynomial.X)).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ frs_interpolation_degree C k + C.K :=
        Nat.add_le_add (hAi i) (hcomp i)
  have hsum :
      (∑ i : Fin k,
        A i.succ *
          f.comp (Polynomial.C (C.gamma ^ i.val) * Polynomial.X)).natDegree ≤
        frs_interpolation_degree C k + C.K := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact hterm i
  unfold frs_functional_equation
  exact (Polynomial.natDegree_add_le _ _).trans (max_le hA0 hsum)

@[blueprint "lem:frs-interpolation-vanishing"
  (statement := /-- Let $\mathcal{C}$ be an $m$-folded Reed--Solomon code and
    let $1\leq k\leq m$ with $K<N(m-k+1)$. Suppose that
    $A_0,\ldots,A_k$ have the interpolation degree bounds and satisfy every
    folded interpolation equation for a received word $g$. Then every
    polynomial $f$ of degree less than $K$ whose folded encoding lies at
    distance strictly less than the folded decoding radius from $g$ satisfies
    $\mathcal{Q}_A(f;X)=0$. -/)
  (proof := /-- For such an $f$, unfold the strict list-radius inequality and
    count the folded positions at which its encoding agrees with $g$.
    By \cref{lem:frs-list-agreement-bound}, the number of resulting
    interpolation roots is strictly larger than $D+K$. At every agreeing
    position, each interpolation equation is the evaluation of
    $\mathcal{Q}_A(f;X)$ at the corresponding power of $\gamma$. These powers
    are pairwise distinct by
    \cref{lem:frs-interpolation-points-injective}. By
    \cref{lem:frs-functional-equation-degree}, the polynomial has degree at
    most $D+K$. Thus it has more distinct roots than its degree and is zero. -/)
  (title := /-- Folded interpolation equations force functional vanishing -/)
  (latexEnv := "lemma")]
lemma frs_interpolation_vanishing (C : folded_rs_code F) (k : ℕ)
    (hk1 : 1 ≤ k) (hkm : k ≤ C.m)
    (hK : C.K < C.N * (C.m - k + 1))
    (g : Fin C.N → Fin C.m → F)
    (A : Fin (k + 1) → Polynomial F)
    (hA0 : (A 0).natDegree ≤ frs_interpolation_degree C k + C.K)
    (hAi : ∀ i : Fin k, (A i.succ).natDegree ≤ frs_interpolation_degree C k)
    (hinterp : ∀ u : Fin C.N, ∀ j : Fin (C.m - k + 1),
      (A 0).eval (C.gamma ^ (u.val * C.m + j.val)) +
        ∑ i : Fin k,
          (A i.succ).eval (C.gamma ^ (u.val * C.m + j.val)) *
            g u ⟨j.val + i.val, by omega⟩ = 0) :
    ∀ f : Polynomial F,
      f ∈ Polynomial.degreeLT (R := F) C.K →
      frs_encode C f ∈ frs_list C g (frs_radius C k) →
      frs_functional_equation C k A f = 0 := by
  intro f hf hlist
  let r := C.m - k + 1
  let S : Set (Fin C.N) := {u | frs_encode C f u = g u}
  letI : Fintype S := Fintype.ofFinite S
  let Q := frs_functional_equation C k A f
  have hrootcount :
      frs_interpolation_degree C k + C.K < S.ncard * r := by
    simpa [S, r] using
      frs_list_agreement_bound C k hk1 hkm hK g f hlist
  have hQdegree :
      Q.natDegree ≤ frs_interpolation_degree C k + C.K := by
    simpa [Q] using frs_functional_equation_degree C k A hA0 hAi f hf
  let rootPoint : S × Fin r → F := fun z =>
    C.gamma ^ (z.1.val.val * C.m + z.2.val)
  have hrootPoint : Function.Injective rootPoint := by
    intro a b hab
    have hpairs :
        (a.1.val, a.2) = (b.1.val, b.2) := by
      apply frs_interpolation_points_injective C k hk1 hkm
      simpa [rootPoint, r] using hab
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hpairs
    · exact congrArg (fun p : Fin C.N × Fin r => p.2) hpairs
  have hQeval : ∀ z : S × Fin r, Q.eval (rootPoint z) = 0 := by
    intro z
    have hinterp_z := hinterp z.1.val
      ⟨z.2.val, by simpa [r] using z.2.isLt⟩
    have hagree (i : Fin k) :
        f.eval
            ((C.gamma ^ i.val) *
              C.gamma ^ (z.1.val.val * C.m + z.2.val)) =
          g z.1.val ⟨z.2.val + i.val, by
            dsimp [r] at z
            omega⟩ := by
      let ji : Fin C.m := ⟨z.2.val + i.val, by
        dsimp [r] at z
        omega⟩
      have hpoint :
          (C.gamma ^ i.val) *
              C.gamma ^ (z.1.val.val * C.m + z.2.val) =
            C.gamma ^ (z.1.val.val * C.m + ji.val) := by
        rw [← pow_add]
        congr 1
        dsimp [ji]
        omega
      rw [hpoint]
      exact congrFun z.1.property ji
    simp only [Q, rootPoint, frs_functional_equation,
      Polynomial.eval_add, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_comp, Polynomial.eval_C, Polynomial.eval_X]
    simp_rw [hagree]
    simpa [r] using hinterp_z
  have hcard :
      Q.natDegree < Fintype.card (S × Fin r) := by
    rw [Fintype.card_prod, Set.fintypeCard_eq_ncard, Fintype.card_fin]
    exact lt_of_le_of_lt hQdegree hrootcount
  exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    Q hrootPoint hQeval hcard

@[blueprint "lem:frs-interpolation-equation"
  (statement := /-- Let $\mathcal{C}$ be an $m$-folded Reed--Solomon code
    (\cref{def:folded-rs-code}) of blocklength $N$ and message dimension $K$. Fix an integer
    $k$ with $1\leq k\leq m$, assume $K<N(m-k+1)$, and let
    $g\in(\mathbb{F}_q^m)^N$. Put $D$ equal to the interpolation degree
    (\cref{def:frs-interpolation-degree}). Then there are polynomials
    $A_0,\ldots,A_k\in\mathbb{F}_q[X]$ such that
    \[
      \deg A_0\leq D+K,\qquad \deg A_i\leq D\quad(1\leq i\leq k),
    \]
    at least one of $A_1,\ldots,A_k$ is nonzero, and every
    $f\in\mathbb{F}_q[X]^{<K}$ whose folded encoding (\cref{def:frs-encode}) belongs to
    $\mathcal{L}(g,\eta_k)$ (\cref{def:frs-list, def:frs-radius}) satisfies
    $\mathcal{Q}_{A}(f;X)=0$ (\cref{def:frs-functional-equation}). -/)
  (proof := /-- By \cref{lem:frs-interpolation-coefficients}, choose
    $A_0,\ldots,A_k$ with the required degree bounds and nonvanishing
    condition, satisfying all folded interpolation equations for $g$.
    The hypotheses of \cref{lem:frs-interpolation-vanishing} are therefore
    satisfied, so every degree-$<K$ polynomial whose encoding belongs to the
    strict decoding list satisfies $\mathcal{Q}_A(f;X)=0$. These same
    coefficients have all the properties asserted in the statement. -/)
  (title := /-- Interpolation equation for nearby folded RS words -/)
  (latexEnv := "lemma")]
lemma frs_interpolation_equation (C : folded_rs_code F) (k : ℕ)
    (hk1 : 1 ≤ k) (hkm : k ≤ C.m)
    (hK : C.K < C.N * (C.m - k + 1))
    (g : Fin C.N → Fin C.m → F) :
    ∃ A : Fin (k + 1) → Polynomial F,
      (A 0).natDegree ≤ frs_interpolation_degree C k + C.K ∧
      (∀ i : Fin k, (A i.succ).natDegree ≤ frs_interpolation_degree C k) ∧
      (∃ i : Fin k, A i.succ ≠ 0) ∧
      ∀ f : Polynomial F,
        f ∈ Polynomial.degreeLT (R := F) C.K →
        frs_encode C f ∈ frs_list C g (frs_radius C k) →
        frs_functional_equation C k A f = 0 := by
  obtain ⟨A, hA0, hAi, hne, hinterp⟩ :=
    frs_interpolation_coefficients C k hk1 hkm hK g
  refine ⟨A, hA0, hAi, hne, ?_⟩
  exact frs_interpolation_vanishing C k hk1 hkm hK g A hA0 hAi hinterp

@[blueprint "lem:frs-coeff-mul-at-first-support"
  (statement := /-- Let (p,qinmathbb{F}_q[X]), and let (r,sinmathbb{N}).
    If every coefficient of (p) below (r) and every coefficient of (q) below (s)
    vanishes, then
    ([X^{r+s}](pq)=([X^r]p)([X^s]q)). -/)
  (proof := /-- Expand the coefficient of the product as the sum over pairs
    ((a,b)) with (a+b=r+s).  The pair ((r,s)) contributes the asserted product.
    For every other pair, either (a<r), in which case the corresponding coefficient
    of (p) vanishes, or (a>r) and hence (b<s), in which case the corresponding
    coefficient of (q) vanishes. -/)
  (title := /-- Product coefficient at the first possible support index -/)
  (latexEnv := "lemma")]
lemma frs_coeff_mul_at_first_support (p q : Polynomial F) (r s : ℕ)
    (hp : ∀ n < r, p.coeff n = 0) (hq : ∀ n < s, q.coeff n = 0) :
    (p * q).coeff (r + s) = p.coeff r * q.coeff s := by
  rw [Polynomial.coeff_mul]
  rw [Finset.sum_eq_single (r, s)]
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.mem_antidiagonal] at hab
    by_cases ha : a < r
    · simp [hp a ha]
    · have hb : b < s := by
        have hra : r ≤ a := Nat.le_of_not_gt ha
        have har : a ≠ r := by
          intro har
          have hbs : b = s := by omega
          exact hne (by simp [har, hbs])
        omega
      simp [hq b hb]
  · simp

@[blueprint "lem:frs-shifted-equation-dimension"
  (statement := /-- Let $\mathcal{C}$ be an $m$-folded Reed--Solomon code
    (\cref{def:folded-rs-code}), let $k\geq1$, and let
    $A_0,\ldots,A_k\in\mathbb{F}_q[X]$, with at least one of
    $A_1,\ldots,A_k$ nonzero. The set of polynomials
    $f\in\mathbb{F}_q[X]^{<K}$ satisfying
    $\mathcal{Q}_{A}(f;X)=0$ (\cref{def:frs-functional-equation}) is contained in an
    affine subspace of $\mathbb{F}_q[X]^{<K}$ whose dimension is at most $k-1$. -/)
  (proof := /-- Choose the least exponent $r$ for which the coefficients
    $a_i=[X^r]A_{i+1}$, $0\leq i<k$, are not all zero, and set
    \[
      B(T)=\sum_{i=0}^{k-1}a_iT^i.
    \]
    Then $B$ is nonzero and has degree at most $k-1$. Write
    $f(X)=\sum_{j=0}^{K-1}f_jX^j$. By
    \cref{lem:frs-coeff-mul-at-first-support}, in the coefficient of $X^{r+j}$ in
    $\mathcal{Q}_{A}(f;X)$ (\cref{def:frs-functional-equation}), the coefficient of the
    as-yet undetermined variable $f_j$ is precisely $B(\gamma^j)$; every other occurrence
    of a coefficient of $f$ involves some $f_{j'}$ with $j'<j$, by the minimality of $r$.
    Thus the functional equation determines $f_j$ affinely from
    $f_0,\ldots,f_{j-1}$ whenever $B(\gamma^j)\neq0$.

    By \cref{def:folded-rs-code}, the order of $\gamma$ is at least $mN$, while
    $K\leq mN$. Hence $\gamma^0,\ldots,\gamma^{K-1}$ are pairwise distinct. Since the
    nonzero polynomial $B$ has degree at most $k-1$, at most $k-1$ of these powers are
    roots of $B$. Taking the coefficients $f_j$ at those exceptional indices as free
    parameters and applying the preceding recurrence at all remaining indices expresses
    the entire solution set as either the empty set or an affine family with at most
    $k-1$ parameters. In either case it is contained in an affine subspace of
    $\mathbb{F}_q[X]^{<K}$ of dimension at most $k-1$. -/)
  (title := /-- Dimension bound for the shifted-polynomial solution space -/)
  (latexEnv := "lemma")]
lemma frs_shifted_equation_dimension (C : folded_rs_code F) (k : ℕ)
    (hk1 : 1 ≤ k) (A : Fin (k + 1) → Polynomial F)
    (hA : ∃ i : Fin k, A i.succ ≠ 0) :
    ∃ S : AffineSubspace F (Polynomial.degreeLT (R := F) C.K),
      Module.finrank F S.direction ≤ k - 1 ∧
      ∀ f : Polynomial.degreeLT (R := F) C.K,
        frs_functional_equation C k A (f : Polynomial F) = 0 →
        f ∈ S := by
  classical
  have hex : ∃ r : ℕ, ∃ i : Fin k, (A i.succ).coeff r ≠ 0 := by
    obtain ⟨i, hi⟩ := hA
    by_contra h
    simp only [not_exists, not_not] at h
    apply hi
    ext n
    simpa using h n i
  let r := Nat.find hex
  have hr : ∃ i : Fin k, (A i.succ).coeff r ≠ 0 := by
    simpa [r] using Nat.find_spec hex
  have hAr : ∀ i : Fin k, ∀ n < r, (A i.succ).coeff n = 0 := by
    intro i n hn
    by_contra h
    exact Nat.find_min hex hn ⟨i, h⟩
  let B : Polynomial F :=
    ∑ i : Fin k, Polynomial.monomial i.val ((A i.succ).coeff r)
  have hBcoeff (i : Fin k) : B.coeff i.val = (A i.succ).coeff r := by
    simp only [B, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b hb hbi
      rw [Polynomial.coeff_monomial]
      split_ifs with hval
      · exact (hbi (Fin.ext hval)).elim
      · rfl
    · simp
  have hB : B ≠ 0 := by
    intro h
    obtain ⟨i, hi⟩ := hr
    apply hi
    have hc := congrArg (fun p : Polynomial F => p.coeff i.val) h
    simpa [hBcoeff i] using hc
  have hBdeg : B.natDegree < k := by
    have hle : B.natDegree ≤ k - 1 := by
      dsimp [B]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      exact (Polynomial.natDegree_monomial_le _).trans (by omega)
    omega
  let E : Finset (Fin C.K) :=
    Finset.univ.filter (fun j => Polynomial.eval (C.gamma ^ j.val) B = 0)
  have hpow : Function.Injective (fun j : Fin C.K => C.gamma ^ j.val) := by
    have hgamma : IsOfFinOrder C.gamma :=
      orderOf_pos_iff.1 (lt_of_lt_of_le (Nat.mul_pos C.hm C.hN) C.horder)
    intro a b hab
    apply Fin.ext
    exact (hgamma.pow_eq_pow_iff_modEq.1 hab).eq_of_lt_of_lt
      (lt_of_lt_of_le a.isLt (C.hK.trans C.horder))
      (lt_of_lt_of_le b.isLt (C.hK.trans C.horder))
  let P : Finset F := E.image (fun j => C.gamma ^ j.val)
  have hPE : P.card = E.card := by
    simpa [P] using Finset.card_image_of_injective E hpow
  have hProots : P.card ≤ B.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    have hxP : x ∈ P := by simpa using hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hxP
    apply (Polynomial.mem_roots hB).2
    simpa [Polynomial.IsRoot] using (Finset.mem_filter.mp hj).2
  have hEcard : E.card ≤ k - 1 := by
    calc
      E.card = P.card := hPE.symm
      _ ≤ B.natDegree := hProots
      _ ≤ k - 1 := by omega
  let L : Polynomial.degreeLT (R := F) C.K →ₗ[F] Polynomial F :=
    { toFun := fun f => ∑ i : Fin k,
          A i.succ * (f : Polynomial F).comp
            (Polynomial.C (C.gamma ^ i.val) * Polynomial.X)
      map_add' := by
        intro f g
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        simp [Finset.smul_sum] }
  let R : L.ker →ₗ[F] (E → F) :=
    { toFun := fun f e =>
          (((f : L.ker).1 : Polynomial.degreeLT (R := F) C.K) : Polynomial F).coeff
            ((e : E).1 : Fin C.K).val
      map_add' := by
        intro f g
        funext e
        simp
      map_smul' := by
        intro c f
        funext e
        simp }
  have hRinj : Function.Injective R := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply Subtype.ext
    apply Subtype.ext
    let p : Polynomial F :=
      ((((x - y : L.ker).1 : Polynomial.degreeLT (R := F) C.K)) : Polynomial F)
    by_contra hp
    have hpmem : p ∈ Polynomial.degreeLT (R := F) C.K := (x - y : L.ker).1.2
    have hLp : L (x - y : L.ker).1 = 0 :=
      LinearMap.mem_ker.mp (x - y : L.ker).2
    have hjdeg : p.natTrailingDegree < C.K := by
      exact lt_of_le_of_lt (Polynomial.natTrailingDegree_le_natDegree p)
        ((Polynomial.natDegree_lt_iff_degree_lt hp).2
          (Polynomial.mem_degreeLT.mp hpmem))
    let j : Fin C.K := ⟨p.natTrailingDegree, hjdeg⟩
    have hjcoeff : p.coeff p.natTrailingDegree ≠ 0 :=
      Polynomial.coeff_natTrailingDegree_ne_zero.2 hp
    have hjnot : j ∉ E := by
      intro hjE
      have heq := congrFun hxy ⟨j, hjE⟩
      change
        ((((x : L.ker).1 : Polynomial.degreeLT (R := F) C.K) : Polynomial F).coeff
          p.natTrailingDegree) =
        ((((y : L.ker).1 : Polynomial.degreeLT (R := F) C.K) : Polynomial F).coeff
          p.natTrailingDegree) at heq
      apply hjcoeff
      simpa [p] using sub_eq_zero.mpr heq
    have hBj : Polynomial.eval (C.gamma ^ p.natTrailingDegree) B ≠ 0 := by
      simpa [E, j] using hjnot
    have hEval :
        Polynomial.eval (C.gamma ^ p.natTrailingDegree) B =
          ∑ i : Fin k, (A i.succ).coeff r *
            (C.gamma ^ p.natTrailingDegree) ^ i.val := by
      rw [Polynomial.eval_eq_sum_range' hBdeg]
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hBcoeff i]
    have hci (i : Fin k) :
        (A i.succ *
          p.comp (Polynomial.C (C.gamma ^ i.val) * Polynomial.X)).coeff
            (r + p.natTrailingDegree) =
          (A i.succ).coeff r *
            (p.coeff p.natTrailingDegree * (C.gamma ^ i.val) ^ p.natTrailingDegree) := by
      rw [frs_coeff_mul_at_first_support]
      · rw [Polynomial.comp_C_mul_X_coeff]
      · exact hAr i
      · intro n hn
        rw [Polynomial.comp_C_mul_X_coeff,
          Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hn, zero_mul]
    have hz :
        (∑ i : Fin k,
          A i.succ * p.comp
            (Polynomial.C (C.gamma ^ i.val) * Polynomial.X)).coeff
              (r + p.natTrailingDegree) = 0 := by
      simpa [L, p] using
        congrArg (fun q : Polynomial F => q.coeff (r + p.natTrailingDegree)) hLp
    have hprod :
        Polynomial.eval (C.gamma ^ p.natTrailingDegree) B *
          p.coeff p.natTrailingDegree = 0 := by
      rw [hEval, Finset.sum_mul]
      calc
        (∑ i : Fin k,
            ((A i.succ).coeff r *
              (C.gamma ^ p.natTrailingDegree) ^ i.val) *
                p.coeff p.natTrailingDegree) =
            ∑ i : Fin k,
              (A i.succ *
                p.comp (Polynomial.C (C.gamma ^ i.val) * Polynomial.X)).coeff
                  (r + p.natTrailingDegree) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [hci i, ← pow_mul, ← pow_mul, Nat.mul_comm i.val]
                    ring
        _ = (∑ i : Fin k,
              A i.succ *
                p.comp (Polynomial.C (C.gamma ^ i.val) * Polynomial.X)).coeff
                  (r + p.natTrailingDegree) := by simp
        _ = 0 := hz
    exact (mul_ne_zero hBj hjcoeff) hprod
  have hdim : Module.finrank F L.ker ≤ k - 1 := by
    exact (LinearMap.finrank_le_finrank_of_injective hRinj).trans (by
      simpa using hEcard)
  by_cases hs :
      ∃ f : Polynomial.degreeLT (R := F) C.K,
        frs_functional_equation C k A (f : Polynomial F) = 0
  · obtain ⟨f₀, hf₀⟩ := hs
    refine ⟨AffineSubspace.mk' f₀ L.ker, ?_, ?_⟩
    · rw [AffineSubspace.direction_mk']
      exact hdim
    · intro f hf
      rw [AffineSubspace.mem_mk']
      rw [LinearMap.mem_ker]
      change L (f - f₀) = 0
      rw [map_sub, sub_eq_zero]
      apply add_left_cancel (a := A 0)
      simpa [frs_functional_equation, L] using hf.trans hf₀.symm
  · refine ⟨AffineSubspace.mk' 0 ⊥, ?_, ?_⟩
    · rw [AffineSubspace.direction_mk']
      simp
    · intro f hf
      exact False.elim (hs ⟨f, hf⟩)

@[blueprint "lem:lin-alg-rs"
  (statement := /-- Let $\mathcal{C}$ be an $m$-folded Reed-Solomon code (\cref{def:folded-rs-code})
    of blocklength $N$, message dimension $K$, and rate $R$ (\cref{def:frs-rate}). Let $k$ be an
    integer satisfying $1 \leq k \leq m$, $k - 1 \leq K$, and $k - 1 \leq mN$, and let
    $g \in (\mathbb{F}_q^m)^N$ be any received word. Then there exists an affine subspace
    $\mathcal{H}$ of the ambient folded-word space $(\mathbb{F}_q^m)^N$ such that every element of
    $\mathcal{H}$ is a codeword (\cref{def:frs-code}), the direction of $\mathcal{H}$ has
    $\mathbb{F}_q$-dimension exactly $k-1$, and the strict decoding list (\cref{def:frs-list}) at
    the folded radius $\eta_k$ (\cref{def:frs-radius}) is contained in $\mathcal{H}$:
    $\mathcal{L}(g,\eta_k) \subseteq \mathcal{H}$. -/)
  (proof := /-- Put $M=N(m-k+1)$. First suppose that $K<M$. By
    \cref{lem:frs-interpolation-equation}, there are coefficient polynomials
    $A_0,\ldots,A_k$, not all zero after $A_0$, such that every message polynomial whose
    encoding (\cref{def:frs-encode}) belongs to the decoding list
    (\cref{def:frs-list}) satisfies the associated shifted functional equation
    (\cref{def:frs-functional-equation}). By
    \cref{lem:frs-shifted-equation-dimension}, all solutions of that equation in
    $\mathbb{F}_q[X]^{<K}$ lie in an affine subspace $S$ of dimension at most $k-1$.
    Since $k-1\leq K$, extend $S$ inside $\mathbb{F}_q[X]^{<K}$ to an affine subspace
    $S'$ of dimension exactly $k-1$; if the solution set is empty, choose any affine
    subspace of that dimension.

    The restriction of the encoding map to $\mathbb{F}_q[X]^{<K}$ is linear and injective.
    Indeed, the $mN$ evaluation points are pairwise distinct by the order condition in
    \cref{def:folded-rs-code}, and a nonzero polynomial of degree less than
    $K\leq mN$ cannot vanish at all of them. Therefore the image $\mathcal{H}$ of $S'$
    under the encoding map is an affine subspace of the codeword space of dimension
    exactly $k-1$. Its points belong to the code (\cref{def:frs-code}), and the preceding
    containment gives $\mathcal{L}(g,\eta_k)\subseteq\mathcal{H}$.

    It remains to consider $M\leq K$. Since $N>0$ and $m-k+1>0$, the definition of the rate
    (\cref{def:frs-rate}) gives
    \[
      \frac{m}{m-k+1}R=\frac{K}{N(m-k+1)}\geq1.
    \]
    Hence the radius $\eta_k$ (\cref{def:frs-radius}) is nonpositive. Fractional distance
    (\cref{def:frs-dist}) is nonnegative, so the strict decoding list is empty. Choose any
    $(k-1)$-dimensional affine subspace of $\mathbb{F}_q[X]^{<K}$, which exists because
    $k-1\leq K$, and transport it through the same injective encoding map. Its image is an
    affine subspace $\mathcal{H}$ of codewords of dimension exactly $k-1$, and it contains
    the empty decoding list. -/)
  (title := /-- Linear-algebraic list decoding of folded RS codes -/)
  (latexEnv := "lemma")]
lemma lin_alg_rs (C : folded_rs_code F) (k : ℕ) (hk1 : 1 ≤ k) (hkm : k ≤ C.m)
    (hkK : k - 1 ≤ C.K)
    (hkN : k - 1 ≤ C.m * C.N)
    (g : Fin C.N → Fin C.m → F) :
      ∃ H : AffineSubspace F (Fin C.N → Fin C.m → F),
      (H : Set (Fin C.N → Fin C.m → F)) ⊆ frs_code C ∧
      Module.finrank F H.direction = k - 1 ∧
      frs_list C g (frs_radius C k) ⊆ (H : Set (Fin C.N → Fin C.m → F)) := by
  classical
  let V := Polynomial.degreeLT (R := F) C.K
  let E : V →ₗ[F] (Fin C.N → Fin C.m → F) :=
    { toFun := fun f => frs_encode C (f : Polynomial F)
      map_add' := by
        intro f h
        funext i j
        simp [frs_encode]
      map_smul' := by
        intro c f
        funext i j
        simp [frs_encode] }
  letI : Module.Finite F V :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv F C.K).symm
  have hVdim : Module.finrank F V = C.K := by
    rw [(Polynomial.degreeLTEquiv F C.K).finrank_eq, Module.finrank_pi]
    simp [V]
  have hEinj : Function.Injective E := by
    intro f h heq
    change frs_encode C (f : Polynomial F) = frs_encode C (h : Polynomial F) at heq
    let p : Polynomial F := (f : Polynomial F) - (h : Polynomial F)
    have hpdeg : p ∈ Polynomial.degreeLT (R := F) C.K :=
      Submodule.sub_mem V f.property h.property
    let rootPoint : Fin C.N × Fin C.m → F := fun z =>
      C.gamma ^ (z.1.val * C.m + z.2.val)
    have hrootPoint : Function.Injective rootPoint := by
      have hgamma : IsOfFinOrder C.gamma :=
        orderOf_pos_iff.1 (lt_of_lt_of_le (Nat.mul_pos C.hm C.hN) C.horder)
      intro a b hab
      have hexp_lt (z : Fin C.N × Fin C.m) :
          z.1.val * C.m + z.2.val < orderOf C.gamma := by
        apply lt_of_lt_of_le _ C.horder
        calc
          z.1.val * C.m + z.2.val < z.1.val * C.m + C.m :=
            Nat.add_lt_add_left z.2.isLt _
          _ = (z.1.val + 1) * C.m := by ring
          _ ≤ C.N * C.m := Nat.mul_le_mul_right C.m z.1.isLt
          _ = C.m * C.N := Nat.mul_comm _ _
      have hexp : a.1.val * C.m + a.2.val = b.1.val * C.m + b.2.val :=
        (hgamma.pow_eq_pow_iff_modEq.1 hab).eq_of_lt_of_lt (hexp_lt a) (hexp_lt b)
      have hj : a.2.val = b.2.val := by
        have hmod := congrArg (fun n : ℕ => n % C.m) hexp
        simpa [Nat.add_mod, Nat.mod_eq_of_lt a.2.isLt,
          Nat.mod_eq_of_lt b.2.isLt] using hmod
      rw [hj] at hexp
      apply Prod.ext
      · apply Fin.ext
        exact Nat.mul_right_cancel C.hm (Nat.add_right_cancel hexp)
      · exact Fin.ext hj
    have hpeval : ∀ z : Fin C.N × Fin C.m, p.eval (rootPoint z) = 0 := by
      intro z
      have hz := congrFun (congrFun heq z.1) z.2
      simpa [p, rootPoint, frs_encode] using sub_eq_zero.mpr hz
    have hpzero : p = 0 := by
      by_cases hp : p = 0
      · exact hp
      · have hpK : p.natDegree < C.K :=
          (Polynomial.natDegree_lt_iff_degree_lt hp).2
            (Polynomial.mem_degreeLT.mp hpdeg)
        have hpcard : p.natDegree < Fintype.card (Fin C.N × Fin C.m) := by
          rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
          exact lt_of_lt_of_le hpK (by simpa [Nat.mul_comm] using C.hK)
        exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
          p hrootPoint hpeval hpcard
    apply Subtype.ext
    exact sub_eq_zero.mp hpzero
  have hfamily :
      ∃ S : AffineSubspace F V,
        Module.finrank F S.direction ≤ k - 1 ∧
        ∀ f : V,
          frs_encode C (f : Polynomial F) ∈ frs_list C g (frs_radius C k) → f ∈ S := by
    by_cases hsmall : C.K < C.N * (C.m - k + 1)
    · obtain ⟨A, hA0, hAi, hAne, hA⟩ :=
        frs_interpolation_equation C k hk1 hkm hsmall g
      obtain ⟨S, hSdim, hS⟩ :=
        frs_shifted_equation_dimension C k hk1 A hAne
      refine ⟨S, hSdim, ?_⟩
      intro f hf
      exact hS f (hA (f : Polynomial F) f.property hf)
    · refine ⟨AffineSubspace.mk' 0 ⊥, ?_, ?_⟩
      · rw [AffineSubspace.direction_mk']
        simp
      intro f hf
      have hlarge : C.N * (C.m - k + 1) ≤ C.K := Nat.le_of_not_gt hsmall
      have hmpos : (0 : ℝ) < C.m := by exact_mod_cast C.hm
      have hNpos : (0 : ℝ) < C.N := by exact_mod_cast C.hN
      have htpos : (0 : ℝ) < (C.m : ℝ) - k + 1 := by
        exact_mod_cast (show 0 < C.m - k + 1 by omega)
      have hlargeR :
          (C.N : ℝ) * ((C.m : ℝ) - k + 1) ≤ (C.K : ℝ) := by
        exact_mod_cast hlarge
      have hratio :
          ((C.m : ℝ) / ((C.m : ℝ) - k + 1)) *
              ((C.K : ℝ) / ((C.m : ℝ) * (C.N : ℝ))) =
            (C.K : ℝ) / ((C.N : ℝ) * ((C.m : ℝ) - k + 1)) := by
        field_simp [ne_of_gt hmpos, ne_of_gt hNpos, ne_of_gt htpos]
        <;> ring
      have hone :
          (1 : ℝ) ≤ (C.K : ℝ) / ((C.N : ℝ) * ((C.m : ℝ) - k + 1)) := by
        apply (le_div_iff₀ (mul_pos hNpos htpos)).2
        simpa [one_mul] using hlargeR
      have hradius : frs_radius C k ≤ 0 := by
        rw [frs_radius, frs_rate, hratio]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hone)
      have hdist : 0 ≤ frs_dist C g (frs_encode C (f : Polynomial F)) := by
        unfold frs_dist
        positivity
      exact False.elim ((not_lt_of_ge hdist) (lt_of_lt_of_le hf.2 hradius))
  obtain ⟨S, hSdim, hSlist⟩ := hfamily
  have extend_by :
      ∀ n : ℕ, ∀ P : Submodule F V,
        Module.finrank F P + n ≤ Module.finrank F V →
        ∃ Q : Submodule F V,
          P ≤ Q ∧ Module.finrank F Q = Module.finrank F P + n := by
    intro n
    induction n with
    | zero =>
        intro P hP
        exact ⟨P, le_rfl, by simp⟩
    | succ n ih =>
        intro P hP
        have hlt : Module.finrank F P < Module.finrank F V := by omega
        obtain ⟨v, hv⟩ := P.exists_of_finrank_lt hlt
        have hvP : v ∉ P := by simpa using hv 1 one_ne_zero
        let P' := P ⊔ Submodule.span F {v}
        have hP'dim : Module.finrank F P' = Module.finrank F P + 1 := by
          simpa [P'] using Submodule.finrank_sup_span_singleton hvP
        have hP' : Module.finrank F P' + n ≤ Module.finrank F V := by
          rw [hP'dim]
          omega
        obtain ⟨Q, hP'Q, hQdim⟩ := ih P' hP'
        refine ⟨Q, le_sup_left.trans hP'Q, ?_⟩
        rw [hQdim, hP'dim]
        omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hSdim
  have hSn : Module.finrank F S.direction + n ≤ Module.finrank F V := by
    rw [← hn, hVdim]
    exact hkK
  obtain ⟨Q, hSQ, hQdim'⟩ := extend_by n S.direction hSn
  have hQdim : Module.finrank F Q = k - 1 := hQdim'.trans hn.symm
  let s₀ : V :=
    if hSne : (S : Set V).Nonempty then Classical.choose hSne else 0
  let S' : AffineSubspace F V := AffineSubspace.mk' s₀ Q
  have hSS' : S ≤ S' := by
    intro f hf
    have hSne : (S : Set V).Nonempty := ⟨f, hf⟩
    have hs₀ : s₀ ∈ S := by
      simp only [s₀, dif_pos hSne]
      exact Classical.choose_spec hSne
    rw [AffineSubspace.mem_mk']
    exact hSQ (S.vsub_mem_direction hf hs₀)
  let H : AffineSubspace F (Fin C.N → Fin C.m → F) :=
    AffineSubspace.mk' (E s₀) (Q.map E)
  have hHcode :
      (H : Set (Fin C.N → Fin C.m → F)) ⊆ frs_code C := by
    intro h hh
    dsimp [H] at hh
    change h - E s₀ ∈ Q.map E at hh
    obtain ⟨v, hv, hEv⟩ := hh
    let f : V := v + s₀
    refine ⟨(f : Polynomial F), f.property, ?_⟩
    change E f = h
    dsimp [f]
    rw [map_add, hEv]
    abel
  have hErestrict : Function.Injective (E.domRestrict Q) := by
    intro f h heq
    apply Subtype.ext
    exact hEinj heq
  have hHdim : Module.finrank F H.direction = k - 1 := by
    calc
      Module.finrank F H.direction = Module.finrank F (Q.map E) := by
        dsimp [H]
        rw [AffineSubspace.direction_mk']
      _ = Module.finrank F (LinearMap.range (E.domRestrict Q)) := by
        rw [LinearMap.range_domRestrict]
      _ = Module.finrank F Q := LinearMap.finrank_range_of_inj hErestrict
      _ = k - 1 := hQdim
  refine ⟨H, hHcode, hHdim, ?_⟩
  intro h hh
  obtain ⟨f, hf, rfl⟩ := hh.1
  have hfS' : (⟨f, hf⟩ : V) ∈ S' := hSS' (hSlist ⟨f, hf⟩ hh)
  rw [AffineSubspace.mem_mk'] at hfS'
  dsimp [H]
  change E (⟨f, hf⟩ : V) - E s₀ ∈ Q.map E
  rw [← map_sub]
  exact Submodule.mem_map_of_mem hfS'

@[blueprint "def:frs-symbol-proj"
  (statement := /-- For an $m$-folded Reed-Solomon code $\mathcal{C}$ (\cref{def:folded-rs-code})
    and a folded symbol index $i \in \{0,\dots,N-1\}$, the \emph{$i$-th symbol projection} is the
    $\mathbb{F}_q$-linear map $\mathrm{proj}_i \colon \mathbb{F}_q[X] \to \mathbb{F}_q^m$ sending a
    polynomial $f$ to its vector of evaluations
    $\left(f(\gamma^{\,im}),\, f(\gamma^{\,im+1}),\, \dots,\, f(\gamma^{\,im+m-1})\right)$ at the
    $m$ consecutive powers of $\gamma$ packed into symbol $i$. This is precisely the $i$-th folded
    coordinate of the encoding map (\cref{def:frs-encode}), viewed as a linear map on the whole
    polynomial ring. -/)
  (title := /-- Projection onto a folded symbol -/)
  (latexEnv := "definition")]
noncomputable def frs_symbol_proj (C : folded_rs_code F) (i : Fin C.N) :
    Polynomial F →ₗ[F] (Fin C.m → F) :=
  LinearMap.pi (fun j : Fin C.m => Polynomial.leval (C.gamma ^ (i.val * C.m + j.val)))

@[blueprint "lem:frd-det-row-dvd"
  (statement := /-- Let $R$ be a commutative ring, $M$ an $n \times n$ matrix over $R$, and
    $s$ a set of row indices such that a fixed element $g \in R$ divides every entry of every
    row in $s$. Then $g^{|s|}$ divides $\det M$. -/)
  (proof := /-- Using the axiom of choice, for each row $a \in s$ and each column $j$ write
    $M_{a,j} = g\,q_{a,j}$. Define the diagonal vector $c_a = g$ for $a \in s$ and $c_a = 1$
    otherwise, and the matrix $Q$ with $Q_{a,j} = q_{a,j}$ for $a \in s$ and $Q_{a,j} = M_{a,j}$
    otherwise. Then $M = \operatorname{diag}(c)\,Q$, so by multiplicativity of the determinant
    $\det M = \left(\prod_a c_a\right)\det Q = g^{|s|}\det Q$, whence $g^{|s|} \mid \det M$. -/)
  (title := /-- Determinant divisibility from divisible rows -/)
  (latexEnv := "lemma")]
lemma frd_det_row_dvd {n : ℕ} {R : Type*} [CommRing R] (g : R)
    (M : Matrix (Fin n) (Fin n) R) (s : Finset (Fin n))
    (h : ∀ a ∈ s, ∀ j, g ∣ M a j) :
    g ^ s.card ∣ M.det := by
  classical
  choose q hq using h
  set c : Fin n → R := fun a => if a ∈ s then g else 1 with hc
  set Q : Matrix (Fin n) (Fin n) R :=
    Matrix.of (fun a j => if ha : a ∈ s then q a ha j else M a j) with hQ
  have hMeq : M = Matrix.diagonal c * Q := by
    ext a j
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single a]
    · by_cases ha : a ∈ s
      · simp [Matrix.diagonal, hc, hQ, ha, hq a ha j]
      · simp [Matrix.diagonal, hc, hQ, ha]
    · intro b _ hba
      simp [Matrix.diagonal_apply, hba.symm]
    · intro hna
      exact absurd (Finset.mem_univ a) hna
  have hprod : (∏ a, c a) = g ^ s.card := by
    rw [hc]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    congr 1
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hMeq, Matrix.det_mul, Matrix.det_diagonal, hprod]
  exact Dvd.intro _ rfl

@[blueprint "def:frd-wron"
  (statement := /-- For an element $\gamma$ of a field, a dimension $d$, and a family of
    polynomials $f_0,\dots,f_{d-1}$, the \emph{multiplicative (folded) Wronskian} is the
    determinant of the $d \times d$ matrix whose $(a,j)$ entry is the polynomial
    $f_a(\gamma^{\,j} X)$, i.e. $f_a$ with its variable scaled by $\gamma^{\,j}$. -/)
  (title := /-- Multiplicative Wronskian -/)
  (latexEnv := "definition")]
noncomputable def frd_wron (gamma : F) (d : ℕ) (f : Fin d → Polynomial F) : Polynomial F :=
  (Matrix.of fun a j : Fin d =>
    Polynomial.aeval (Polynomial.C (gamma ^ (j : ℕ)) * Polynomial.X) (f a)).det

@[blueprint "lem:frd-wron-smul"
  (statement := /-- Let $\gamma$ be an element of a field, $d$ a dimension, $M$ a $d \times d$
    scalar matrix, and $f_0,\dots,f_{d-1}$ a family of polynomials. If $g_a = \sum_b M_{a,b} f_b$
    for each $a$, then the multiplicative Wronskian (\cref{def:frd-wron}) transforms as
    $\mathrm{Wron}(\gamma, g) = (\det M)\,\mathrm{Wron}(\gamma, f)$. -/)
  (proof := /-- Since the map $p \mapsto p(\gamma^{\,j}X)$ is the algebra homomorphism
    $\mathrm{aeval}(\gamma^{\,j}X)$, it is $F$-linear, so the $(a,j)$ entry of the matrix for $g$
    equals $\sum_b M_{a,b}\,f_b(\gamma^{\,j}X)$. Hence the matrix for $g$ is the product
    $(\mathrm{C}\,M)\cdot A_f$, where $A_f$ is the matrix for $f$ and $\mathrm{C}\,M$ is the
    entrywise image of $M$ under the constant-polynomial embedding. Taking determinants and using
    multiplicativity together with $\det(\mathrm{C}\,M) = \mathrm{C}(\det M)$ gives the claim. -/)
  (title := /-- Change of basis for the multiplicative Wronskian -/)
  (latexEnv := "lemma")]
lemma frd_wron_smul (gamma : F) (d : ℕ) (M : Matrix (Fin d) (Fin d) F)
    (f : Fin d → Polynomial F) (g : Fin d → Polynomial F)
    (hg : ∀ a, g a = ∑ b, M a b • f b) :
    frd_wron gamma d g = Polynomial.C M.det * frd_wron gamma d f := by
  unfold frd_wron
  have hEq : (Matrix.of fun a j : Fin d =>
        Polynomial.aeval (Polynomial.C (gamma ^ (j : ℕ)) * Polynomial.X) (g a))
      = (M.map Polynomial.C) *
        (Matrix.of fun a j : Fin d =>
          Polynomial.aeval (Polynomial.C (gamma ^ (j : ℕ)) * Polynomial.X) (f a)) := by
    apply Matrix.ext
    intro a j
    rw [Matrix.mul_apply, Matrix.of_apply, hg a, map_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [map_smul, Matrix.map_apply, Matrix.of_apply, Polynomial.smul_eq_C_mul]
  rw [hEq, Matrix.det_mul]
  congr 1
  exact (RingHom.map_det Polynomial.C M).symm

@[blueprint "lem:frd-wron-dvd"
  (statement := /-- Let $\gamma$ be an element of a field, $d$ a dimension, $f_0,\dots,f_{d-1}$
    a family of polynomials, $c$ a field element, and $s$ a set of row indices. Suppose that for
    every $a \in s$ and every $j \in \{0,\dots,d-1\}$ we have $f_a(\gamma^{\,j} c) = 0$. Then
    $(X - c)^{|s|}$ divides the multiplicative Wronskian (\cref{def:frd-wron})
    $\mathrm{Wron}(\gamma, f)$. -/)
  (proof := /-- For $a \in s$ and any column $j$, the polynomial $f_a(\gamma^{\,j}X)$ evaluated at
    $c$ equals $f_a(\gamma^{\,j}c) = 0$, so $(X - c)$ divides that entry. Thus every entry of the
    rows indexed by $s$ in the Wronskian matrix is divisible by $X - c$, and by the
    determinant divisibility bound (\cref{lem:frd-det-row-dvd}) with divisor $X - c$, the power
    $(X - c)^{|s|}$ divides the determinant, which is $\mathrm{Wron}(\gamma, f)$. -/)
  (title := /-- Divisibility of the multiplicative Wronskian by window factors -/)
  (latexEnv := "lemma")]
lemma frd_wron_dvd (gamma : F) (d : ℕ) (f : Fin d → Polynomial F) (c : F)
    (s : Finset (Fin d))
    (h : ∀ a ∈ s, ∀ j : Fin d, (f a).eval (gamma ^ (j : ℕ) * c) = 0) :
    (Polynomial.X - Polynomial.C c) ^ s.card ∣ frd_wron gamma d f := by
  unfold frd_wron
  apply frd_det_row_dvd
  intro a ha j
  rw [Matrix.of_apply, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
  have hcomp : Polynomial.aeval (Polynomial.C (gamma ^ (j : ℕ)) * Polynomial.X) (f a)
      = (f a).comp (Polynomial.C (gamma ^ (j : ℕ)) * Polynomial.X) := by
    rw [Polynomial.aeval_def, Polynomial.algebraMap_eq]
    rfl
  rw [hcomp, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  exact h a ha j

@[blueprint "lem:frd-coeff-prod"
  (statement := /-- Let $s$ be a finite index set, $g_i$ a family of polynomials over a field,
    and $n_i$ a family of natural numbers such that $\deg g_i \leq n_i$ for every $i \in s$.
    Then the coefficient of $X^{\sum_{i \in s} n_i}$ in the product $\prod_{i \in s} g_i$ equals
    $\prod_{i \in s} \bigl(\text{coefficient of } X^{n_i} \text{ in } g_i\bigr)$. -/)
  (proof := /-- We argue by induction on the finite set $s$. If $s$ is empty, both sides equal
    the coefficient of $X^0$ in the constant polynomial $1$, which is $1$. For the inductive
    step $s = \{a\} \cup s'$ with $a \notin s'$, the product factors as
    $g_a \cdot \prod_{i \in s'} g_i$ and the exponent as $n_a + \sum_{i \in s'} n_i$. Since
    $\deg g_a \leq n_a$ and, by the degree bound for products of polynomials,
    $\deg \prod_{i \in s'} g_i \leq \sum_{i \in s'} \deg g_i \leq \sum_{i \in s'} n_i$,
    the coefficient of the product at the sum of the two degree bounds is the product of the two
    coefficients; the inductive hypothesis rewrites the second factor as
    $\prod_{i \in s'}(\text{coeff of } X^{n_i} \text{ in } g_i)$, completing the step. -/)
  (title := /-- Product coefficient at the sum of degree bounds -/)
  (latexEnv := "lemma")]
lemma frd_coeff_prod {ι : Type*} (s : Finset ι) (g : ι → Polynomial F) (n : ι → ℕ)
    (h : ∀ i ∈ s, (g i).natDegree ≤ n i) :
    (∏ i ∈ s, g i).coeff (∑ i ∈ s, n i) = ∏ i ∈ s, (g i).coeff (n i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le
        (h a (Finset.mem_insert_self a s))
        ((Polynomial.natDegree_prod_le s g).trans
          (Finset.sum_le_sum (fun i hi => h i (Finset.mem_insert_of_mem hi))))]
    rw [ih (fun i hi => h i (Finset.mem_insert_of_mem hi))]

@[blueprint "lem:frd-wron-natDegree"
  (statement := /-- Let $\gamma$ be an element of a field, $d$ a dimension, and $f_0,\dots,f_{d-1}$
    a family of polynomials with $\deg f_a \leq n_a$ for each $a$. Then the multiplicative
    Wronskian (\cref{def:frd-wron}) has degree at most $\sum_a n_a$. -/)
  (proof := /-- By the Leibniz formula the Wronskian is a signed sum over permutations $\sigma$
    of the products $\prod_a f_{\sigma(a)}(\gamma^{\,a}X)$. Each factor is a composition of
    $f_{\sigma(a)}$ with the linear polynomial $\gamma^{\,a}X$, so its degree is at most
    $\deg f_{\sigma(a)} \leq n_{\sigma(a)}$; hence each product has degree at most
    $\sum_a n_{\sigma(a)} = \sum_a n_a$, and each signed summand has the same degree bound.
    The degree of the sum is therefore at most $\sum_a n_a$. -/)
  (title := /-- Degree bound for the multiplicative Wronskian -/)
  (latexEnv := "lemma")]
lemma frd_wron_natDegree (gamma : F) (d : ℕ) (f : Fin d → Polynomial F) (n : Fin d → ℕ)
    (hdeg : ∀ a, (f a).natDegree ≤ n a) :
    (frd_wron gamma d f).natDegree ≤ ∑ a, n a := by
  classical
  unfold frd_wron
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  rw [← Equiv.sum_comp σ n]
  apply Finset.sum_le_sum
  intro a _
  rw [Matrix.of_apply]
  have hcomp : Polynomial.aeval (Polynomial.C (gamma ^ (a : ℕ)) * Polynomial.X) (f (σ a))
      = (f (σ a)).comp (Polynomial.C (gamma ^ (a : ℕ)) * Polynomial.X) := by
    rw [Polynomial.aeval_def, Polynomial.algebraMap_eq]; rfl
  rw [hcomp]
  refine (Polynomial.natDegree_comp_le).trans ?_
  calc (f (σ a)).natDegree * (Polynomial.C (gamma ^ (a : ℕ)) * Polynomial.X).natDegree
      ≤ (f (σ a)).natDegree * 1 := by
        apply Nat.mul_le_mul_left
        exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    _ = (f (σ a)).natDegree := by rw [mul_one]
    _ ≤ n (σ a) := hdeg (σ a)

@[blueprint "lem:frd-wron-top"
  (statement := /-- Let $\gamma$ be an element of a field, $d$ a dimension, $f_0,\dots,f_{d-1}$
    a family of polynomials, and $n_a$ natural numbers with $\deg f_a \leq n_a$ for each $a$.
    Then the coefficient of $X^{\sum_a n_a}$ in the multiplicative Wronskian
    (\cref{def:frd-wron}) equals
    $\left(\prod_a (f_a)_{n_a}\right)\cdot \det V$, where $(f_a)_{n_a}$ is the $n_a$-th coefficient
    of $f_a$ and $V$ is the Vandermonde matrix with nodes $\gamma^{\,n_a}$. -/)
  (proof := /-- By the Leibniz formula the Wronskian is
    $\sum_\sigma \operatorname{sgn}(\sigma)\prod_i f_{\sigma(i)}(\gamma^{\,i}X)$, so taking the
    coefficient of $X^{\sum_a n_a}$ and using additivity of coefficients over sums and scalar
    multiples gives
    $\sum_\sigma \operatorname{sgn}(\sigma)\cdot\bigl[\prod_i f_{\sigma(i)}(\gamma^{\,i}X)\bigr]
    _{\sum_a n_a}$. Reindexing the exponent as $\sum_i n_{\sigma(i)}$ and applying the
    product-coefficient identity (\cref{lem:frd-coeff-prod}) with the degree bounds
    $\deg f_{\sigma(i)}(\gamma^{\,i}X) \leq n_{\sigma(i)}$, each summand becomes
    $\prod_i \bigl[f_{\sigma(i)}(\gamma^{\,i}X)\bigr]_{n_{\sigma(i)}}
    = \prod_i (f_{\sigma(i)})_{n_{\sigma(i)}}\,(\gamma^{\,i})^{n_{\sigma(i)}}$, using the
    scaled-composition coefficient formula. Splitting the product and reindexing the
    coefficient factor by the permutation, the constant $\prod_a (f_a)_{n_a}$ factors out of the
    signed sum, leaving $\sum_\sigma \operatorname{sgn}(\sigma)\prod_i
    (\gamma^{\,n_{\sigma(i)}})^{i}$, which is exactly $\det V$ by the Leibniz formula for the
    Vandermonde matrix with nodes $\gamma^{\,n_a}$. -/)
  (title := /-- Top coefficient of the multiplicative Wronskian -/)
  (latexEnv := "lemma")]
lemma frd_wron_top (gamma : F) (d : ℕ) (f : Fin d → Polynomial F) (n : Fin d → ℕ)
    (hdeg : ∀ a, (f a).natDegree ≤ n a) :
    (frd_wron gamma d f).coeff (∑ a, n a)
      = (∏ a, (f a).coeff (n a)) *
        (Matrix.vandermonde (fun a => gamma ^ n a)).det := by
  classical
  unfold frd_wron
  rw [Matrix.det_apply, Polynomial.finsetSum_coeff]
  rw [Matrix.det_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Polynomial.coeff_smul]
  have hsum : (∑ a, n a) = ∑ i, n (σ i) := (Equiv.sum_comp σ n).symm
  have hcoeff : (∏ i, Matrix.of (fun a j : Fin d =>
        Polynomial.aeval (Polynomial.C (gamma ^ (j : ℕ)) * Polynomial.X) (f a)) (σ i) i).coeff
        (∑ a, n a)
      = (∏ a, (f a).coeff (n a)) * ∏ i, (gamma ^ n (σ i)) ^ (i : ℕ) := by
    rw [hsum]
    rw [frd_coeff_prod Finset.univ
        (fun i => Matrix.of (fun a j : Fin d =>
          Polynomial.aeval (Polynomial.C (gamma ^ (j : ℕ)) * Polynomial.X) (f a)) (σ i) i)
        (fun i => n (σ i)) ?_]
    · have hstep : ∀ i : Fin d,
          (Matrix.of (fun a j : Fin d =>
            Polynomial.aeval (Polynomial.C (gamma ^ (j : ℕ)) * Polynomial.X) (f a)) (σ i) i).coeff
            (n (σ i))
          = (f (σ i)).coeff (n (σ i)) * (gamma ^ n (σ i)) ^ (i : ℕ) := by
        intro i
        rw [Matrix.of_apply]
        have hcomp : Polynomial.aeval (Polynomial.C (gamma ^ (i : ℕ)) * Polynomial.X) (f (σ i))
            = (f (σ i)).comp (Polynomial.C (gamma ^ (i : ℕ)) * Polynomial.X) := by
          rw [Polynomial.aeval_def, Polynomial.algebraMap_eq]; rfl
        rw [hcomp, Polynomial.comp_C_mul_X_coeff, ← pow_mul, ← pow_mul, mul_comm (i : ℕ)]
      rw [Finset.prod_congr rfl (fun i _ => hstep i), Finset.prod_mul_distrib]
      congr 1
      exact Equiv.prod_comp σ (fun a => (f a).coeff (n a))
    · intro i _
      rw [Matrix.of_apply]
      have hcomp : Polynomial.aeval (Polynomial.C (gamma ^ (i : ℕ)) * Polynomial.X) (f (σ i))
          = (f (σ i)).comp (Polynomial.C (gamma ^ (i : ℕ)) * Polynomial.X) := by
        rw [Polynomial.aeval_def, Polynomial.algebraMap_eq]; rfl
      rw [hcomp]
      refine (Polynomial.natDegree_comp_le).trans ?_
      calc (f (σ i)).natDegree * (Polynomial.C (gamma ^ (i : ℕ)) * Polynomial.X).natDegree
          ≤ (f (σ i)).natDegree * 1 :=
            Nat.mul_le_mul_left _ ((Polynomial.natDegree_C_mul_le _ _).trans (by simp))
        _ = (f (σ i)).natDegree := by rw [mul_one]
        _ ≤ n (σ i) := hdeg (σ i)
  rw [hcoeff]
  have hvander : ∀ i : Fin d,
      Matrix.vandermonde (fun a => gamma ^ n a) (σ i) i = (gamma ^ n (σ i)) ^ (i : ℕ) := by
    intro i; rw [Matrix.vandermonde_apply]
  rw [Finset.prod_congr rfl (fun i _ => hvander i)]
  exact (mul_smul_comm _ _ _).symm

@[blueprint "lem:frd-wron-ne-zero"
  (statement := /-- Let $\gamma$ be an element of a field, $d$ a dimension, $f_0,\dots,f_{d-1}$
    a family of polynomials, and $n_a$ degree bounds. Suppose that the coefficient of $X^{n_a}$
    in $f_a$ is nonzero for every $a$, that $\deg f_a \leq n_a$, and that the field elements
    $\gamma^{n_a}$ are pairwise distinct. Then the multiplicative Wronskian
    (\cref{def:frd-wron}) of the family $f$ is nonzero. -/)
  (proof := /-- By the top-coefficient formula (\cref{lem:frd-wron-top}), the coefficient of
    $X^{\sum_a n_a}$ in the Wronskian is the product of the nonzero coefficients
    $[X^{n_a}]f_a$ and the determinant of the Vandermonde matrix on the nodes $\gamma^{n_a}$.
    The coefficient product is nonzero by hypothesis, and the Vandermonde determinant is nonzero
    because its nodes are pairwise distinct. Hence this coefficient of the Wronskian is nonzero,
    so the Wronskian itself is nonzero. -/)
  (title := /-- Nonvanishing of a multiplicative Wronskian -/)
  (latexEnv := "lemma")]
lemma frd_wron_ne_zero (gamma : F) (d : ℕ) (f : Fin d → Polynomial F) (n : Fin d → ℕ)
    (hdeg : ∀ a, (f a).natDegree ≤ n a)
    (hcoeff : ∀ a, (f a).coeff (n a) ≠ 0)
    (hpow : Function.Injective (fun a => gamma ^ n a)) :
    frd_wron gamma d f ≠ 0 := by
  intro hzero
  have htop := frd_wron_top gamma d f n hdeg
  rw [hzero, Polynomial.coeff_zero] at htop
  have hprod : (∏ a, (f a).coeff (n a)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hcoeff a
  have hvander : (Matrix.vandermonde (fun a => gamma ^ n a)).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hpow
  exact (mul_ne_zero hprod hvander) htop.symm

@[blueprint "lem:frd-degree-basis"
  (statement := /-- Let $K$ be a natural number and let $D$ be an $F$-linear subspace of
    $F[X]^{<K}$. Then there are a natural number $r$ and a basis $b_0,\dots,b_{r-1}$ of $D$
    whose polynomial degrees are pairwise distinct and all strictly less than $K$. -/)
  (proof := /-- We induct on $K$. For $K=0$, the space $F[X]^{<0}$ is zero, so the empty basis
    suffices. Suppose the claim holds for $K$, and let $D \subseteq F[X]^{<K+1}$. If
    $D \subseteq F[X]^{<K}$, apply the induction hypothesis. Otherwise choose $p \in D$ with
    $p \notin F[X]^{<K}$. The bound $\deg p<K+1$ forces $\deg p=K$, so its $K$-th coefficient is
    nonzero. Put $E=D\cap F[X]^{<K}$ and choose, by induction, a basis of $E$ with distinct
    degrees below $K$. Prepending $p$ gives a linearly independent family, because the span of the
    remaining vectors is contained in $E$ whereas $p\notin E$. It spans $D$: for $q\in D$, set
    $a=[X^K]q/[X^K]p$; then $q-a p$ lies in $E$, since its $K$-th coefficient vanishes and both
    $q$ and $p$ have degree below $K+1$. Thus $q$ is in the span of $p$ and the chosen basis of
    $E$. The new vector has degree exactly $K$, while all old vectors have degree below $K$, so
    all degrees remain pairwise distinct and below $K+1$. -/)
  (title := /-- Basis of a polynomial subspace with distinct degrees -/)
  (latexEnv := "lemma")]
lemma frd_degree_basis (K : ℕ) (D : Submodule F (Polynomial F))
    (hDK : D ≤ (Polynomial.degreeLT (R := F) K : Submodule F (Polynomial F))) :
    ∃ r : ℕ, ∃ b : Module.Basis (Fin r) F D,
      Function.Injective (fun a => ((b a : D) : Polynomial F).natDegree) ∧
      ∀ a, ((b a : D) : Polynomial F).natDegree < K := by
  induction K generalizing D with
  | zero =>
      have hDbot : D = ⊥ := by
        apply le_antisymm
        · intro p hp
          have hp0 : (p : Polynomial F) = 0 := by
            apply Polynomial.ext
            intro n
            rw [Polynomial.coeff_zero]
            exact (Polynomial.degree_lt_iff_coeff_zero (p : Polynomial F) 0).mp
              (Polynomial.mem_degreeLT.mp (hDK hp)) n (Nat.zero_le n)
          exact hp0
        · exact bot_le
      subst D
      let b : Module.Basis (Fin 0) F (⊥ : Submodule F (Polynomial F)) :=
        Module.Basis.empty (⊥ : Submodule F (Polynomial F))
      exact ⟨0, b, fun a => Fin.elim0 a, fun a => Fin.elim0 a⟩
  | succ K ih =>
      by_cases hsmall : D ≤ (Polynomial.degreeLT (R := F) K : Submodule F (Polynomial F))
      · obtain ⟨r, b, hbinj, hbdeg⟩ := ih D hsmall
        exact ⟨r, b, hbinj, fun a => (hbdeg a).trans (Nat.lt_succ_self K)⟩
      · obtain ⟨p, hpD, hpnot⟩ := SetLike.not_le_iff_exists.mp hsmall
        have hpne : p ≠ 0 := by
          intro hp
          subst p
          exact hpnot (Submodule.zero_mem _)
        have hpdeg_lt : p.natDegree < K + 1 :=
          (Polynomial.natDegree_lt_iff_degree_lt hpne).mpr
            (Polynomial.mem_degreeLT.mp (hDK hpD))
        have hpdeg : p.natDegree = K := by
          have hpge : ¬p.natDegree < K := by
            intro hlt
            exact hpnot (Polynomial.mem_degreeLT.mpr
              ((Polynomial.natDegree_lt_iff_degree_lt hpne).mp hlt))
          omega
        have hpcoeff : p.coeff K ≠ 0 := by
          rw [← hpdeg]
          exact Polynomial.coeff_ne_zero_of_eq_degree (Polynomial.degree_eq_natDegree hpne)
        let E : Submodule F (Polynomial F) := D ⊓ Polynomial.degreeLT F K
        obtain ⟨r, b, hbinj, hbdeg⟩ := ih E inf_le_right
        let pD : D := ⟨p, hpD⟩
        let inc : E →ₗ[F] D :=
          { toFun := fun x => ⟨x, x.property.1⟩
            map_add' := by intro x y; rfl
            map_smul' := by intro c x; rfl }
        let tail : Fin r → D := fun i => inc (b i)
        have hinc_ker : LinearMap.ker inc = ⊥ := by
          apply LinearMap.ker_eq_bot.mpr
          intro x y hxy
          apply Subtype.ext
          exact congrArg (fun z : D => (z : Polynomial F)) hxy
        have htailLI : LinearIndependent F tail := by
          exact b.linearIndependent.map' inc hinc_ker
        have htail_deg : ∀ i, ((tail i : D) : Polynomial F).natDegree < K := by
          intro i
          simpa [tail, inc] using hbdeg i
        have hp_not_span : pD ∉ Submodule.span F (Set.range tail) := by
          intro hpSpan
          have hspan_small : Submodule.span F (Set.range tail) ≤
              (Polynomial.degreeLT F K).comap D.subtype := by
            apply Submodule.span_le.mpr
            rintro x ⟨i, rfl⟩
            exact (b i).property.2
          exact hpnot (hspan_small hpSpan)
        let fam : Fin (r + 1) → D := Fin.cons pD tail
        have hfamLI : LinearIndependent F fam := by
          exact htailLI.finCons hp_not_span
        have hfam_span : ⊤ ≤ Submodule.span F (Set.range fam) := by
          intro q _
          let a : F := (q : Polynomial F).coeff K / p.coeff K
          let z : Polynomial F := (q : Polynomial F) - a • p
          have hzD : z ∈ D := D.sub_mem q.property (D.smul_mem a hpD)
          have hzdeg : z ∈ Polynomial.degreeLT F K := by
            rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
            intro m hm
            by_cases hmk : m = K
            · subst m
              simp [z, a, hpcoeff]
            · have hKm : K + 1 ≤ m := by omega
              have hqzero : (q : Polynomial F).coeff m = 0 :=
                (Polynomial.degree_lt_iff_coeff_zero (q : Polynomial F) (K + 1)).mp
                  (Polynomial.mem_degreeLT.mp (hDK q.property)) m hKm
              have hpzero : p.coeff m = 0 :=
                (Polynomial.degree_lt_iff_coeff_zero p (K + 1)).mp
                  (Polynomial.mem_degreeLT.mp (hDK hpD)) m hKm
              simp [z, hqzero, hpzero]
          let zE : E := ⟨z, hzD, hzdeg⟩
          have hp_mem : pD ∈ Submodule.span F (Set.range fam) := by
            apply Submodule.subset_span
            exact ⟨0, by simp [fam]⟩
          have htail_mem : ∀ i, tail i ∈ Submodule.span F (Set.range fam) := by
            intro i
            apply Submodule.subset_span
            exact ⟨Fin.succ i, by simp [fam]⟩
          have hz_mem : (⟨z, hzD⟩ : D) ∈ Submodule.span F (Set.range fam) := by
            have hrepr : zE = ∑ i, (b.repr zE i) • b i := (b.sum_repr zE).symm
            have hreprD : (⟨z, hzD⟩ : D) = ∑ i, (b.repr zE i) • tail i := by
              apply Subtype.ext
              have hrepr' : inc zE = ∑ i, (b.repr zE i) • inc (b i) := by
                simpa only [map_sum, map_smul] using congrArg inc hrepr
              change z = ((∑ i, (b.repr zE i) • tail i : D) : Polynomial F)
              calc
                z = (inc zE : Polynomial F) := rfl
                _ = ((∑ i, (b.repr zE i) • inc (b i) : D) : Polynomial F) :=
                  congrArg (fun x : D => (x : Polynomial F)) hrepr'
                _ = ((∑ i, (b.repr zE i) • tail i : D) : Polynomial F) := rfl
            rw [hreprD]
            exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (htail_mem i)
          have hqeq : q = a • pD + (⟨z, hzD⟩ : D) := by
            apply Subtype.ext
            change (q : Polynomial F) = a • p + z
            simp only [z]
            abel
          rw [hqeq]
          exact Submodule.add_mem _ (Submodule.smul_mem _ _ hp_mem) hz_mem
        let bnew : Module.Basis (Fin (r + 1)) F D := Module.Basis.mk hfamLI hfam_span
        have hbnew_apply : ∀ i, bnew i = fam i := by
          intro i
          exact Module.Basis.mk_apply hfamLI hfam_span i
        refine ⟨r + 1, bnew, ?_, ?_⟩
        · intro i j hij
          change ((bnew i : D) : Polynomial F).natDegree =
            ((bnew j : D) : Polynomial F).natDegree at hij
          rw [hbnew_apply i, hbnew_apply j] at hij
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
          · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
            · rfl
            · change p.natDegree = ((tail j : D) : Polynomial F).natDegree at hij
              rw [hpdeg] at hij
              exact (Nat.ne_of_lt (htail_deg j) hij.symm).elim
          · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
            · change ((tail i : D) : Polynomial F).natDegree = p.natDegree at hij
              rw [hpdeg] at hij
              exact (Nat.ne_of_lt (htail_deg i) hij).elim
            · change ((tail i : D) : Polynomial F).natDegree =
                ((tail j : D) : Polynomial F).natDegree at hij
              have hij' : ((b i : E) : Polynomial F).natDegree =
                  ((b j : E) : Polynomial F).natDegree := by
                simpa [tail, inc] using hij
              exact congrArg Fin.succ (hbinj hij')
        · intro i
          rw [hbnew_apply i]
          refine Fin.cases ?_ (fun j => ?_) i
          · change p.natDegree < K + 1
            exact hpdeg_lt
          · change ((tail j : D) : Polynomial F).natDegree < K + 1
            exact (htail_deg j).trans (Nat.lt_succ_self K)

@[blueprint "lem:frd-wron-dvd-ker"
  (statement := /-- Let $D$ be a $d$-dimensional polynomial space with basis $b$, let
    $L:D\to F^d$ be a linear map, and suppose that the $j$-th coordinate of $L(f)$ is
    $f(\gamma^{\,j}c)$. Then $(X-c)^{\dim\ker L}$ divides the multiplicative Wronskian
    (\cref{def:frd-wron}) of the polynomial family underlying $b$. -/)
  (proof := /-- Choose a basis of $\ker L$ and a basis of the quotient $D/\ker L$. The combined
    submodule--quotient basis has its first $\dim\ker L$ vectors in $\ker L$; reindex it by the
    original $d$ indices. For each of those kernel vectors and each $j<d$, the hypothesis on $L$
    gives $f(\gamma^{\,j}c)=0$. Therefore the Wronskian of the adapted basis is divisible by
    $(X-c)^{\dim\ker L}$ by \cref{lem:frd-wron-dvd}. Express each original basis vector in the
    adapted basis. The change-of-basis formula \cref{lem:frd-wron-smul} writes the original
    Wronskian as a constant polynomial times the adapted Wronskian, so the same power of $X-c$
    divides it. -/)
  (title := /-- Wronskian divisibility from kernel dimension -/)
  (latexEnv := "lemma")]
lemma frd_wron_dvd_ker (gamma : F) (d : ℕ) (D : Submodule F (Polynomial F))
    (b : Module.Basis (Fin d) F D) (c : F) (L : D →ₗ[F] (Fin d → F))
    (hL : ∀ x j, L x j = (x : Polynomial F).eval (gamma ^ (j : ℕ) * c)) :
    (Polynomial.X - Polynomial.C c) ^ Module.finrank F (LinearMap.ker L) ∣
      frd_wron gamma d (fun a => ((b a : D) : Polynomial F)) := by
  classical
  letI : FiniteDimensional F D := b.finiteDimensional_of_finite
  let bk := Module.Basis.ofVectorSpace F (LinearMap.ker L)
  letI : Fintype (Module.Basis.ofVectorSpaceIndex F (LinearMap.ker L)) :=
    FiniteDimensional.fintypeBasisIndex (K := F) (V := LinearMap.ker L) bk
  let v : Module.Basis.ofVectorSpaceIndex F (LinearMap.ker L) → D :=
    fun i => (bk i : LinearMap.ker L)
  have hvLI : LinearIndependent F v := by
    exact bk.linearIndependent.map' (LinearMap.ker L).subtype
      (Submodule.ker_subtype (LinearMap.ker L))
  let hs := hvLI.linearIndepOn_id
  let bs := Module.Basis.extend hs
  let vi : Module.Basis.ofVectorSpaceIndex F (LinearMap.ker L) →
      hs.extend (Set.subset_univ (Set.range v)) := fun i =>
    ⟨v i, Module.Basis.subset_extend hs ⟨i, rfl⟩⟩
  let e := bs.indexEquiv b
  let g : Module.Basis (Fin d) F D := bs.reindex e
  let s : Finset (Fin d) := Finset.univ.image
    (fun i : Module.Basis.ofVectorSpaceIndex F (LinearMap.ker L) => e (vi i))
  have hscard : s.card = Module.finrank F (LinearMap.ker L) := by
    change (Finset.univ.image
      (fun i : Module.Basis.ofVectorSpaceIndex F (LinearMap.ker L) => e (vi i))).card = _
    rw [Finset.card_image_of_injective]
    · exact (Module.finrank_eq_card_basis bk).symm
    · intro i j hij
      apply hvLI.injective
      simpa only [vi] using congrArg Subtype.val (e.injective hij)
  have hgdvd : (Polynomial.X - Polynomial.C c) ^ s.card ∣
      frd_wron gamma d (fun a => ((g a : D) : Polynomial F)) := by
    apply frd_wron_dvd
    intro a ha j
    change a ∈ Finset.univ.image
      (fun i : Module.Basis.ofVectorSpaceIndex F (LinearMap.ker L) => e (vi i)) at ha
    rw [Finset.mem_image] at ha
    obtain ⟨i, _, rfl⟩ := ha
    have hgeq : g (e (vi i)) = v i := by
      simp [g, bs, vi]
    have hgker : g (e (vi i)) ∈ LinearMap.ker L := by
      rw [hgeq]
      exact (bk i).property
    have hzero : L (g (e (vi i))) j = 0 := by
      exact congrFun (LinearMap.mem_ker.mp hgker) j
    rw [hL] at hzero
    exact hzero
  rw [hscard] at hgdvd
  let M : Matrix (Fin d) (Fin d) F := Matrix.of fun a j => g.repr (b a) j
  have hchange : frd_wron gamma d (fun a => ((b a : D) : Polynomial F)) =
      Polynomial.C M.det * frd_wron gamma d (fun a => ((g a : D) : Polynomial F)) := by
    apply frd_wron_smul gamma d M
    intro a
    have hrepr : b a = ∑ j, (g.repr (b a) j) • g j := (g.sum_repr (b a)).symm
    change ((b a : D) : Polynomial F) =
      ∑ j, (Matrix.of fun a j => g.repr (b a) j) a j • ((g j : D) : Polynomial F)
    calc
      ((b a : D) : Polynomial F) = D.subtype (b a) := rfl
      _ = D.subtype (∑ j, (g.repr (b a) j) • g j) := congrArg D.subtype hrepr
      _ = ∑ j, (g.repr (b a) j) • ((g j : D) : Polynomial F) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [map_smul]
        rfl
  rw [hchange]
  exact dvd_mul_of_dvd_right hgdvd _

@[blueprint "lem:frd-distinct-root-budget"
  (statement := /-- Let $p\in F[X]$ be nonzero, let $I$ be a finite type, let $c:I\to F$ be
    injective, and let $e:I\to\mathbb{N}$. If $(X-c_i)^{e_i}$ divides $p$ for every $i$, then
    $\sum_i e_i\leq\deg p$. -/)
  (proof := /-- Divisibility by $(X-c_i)^{e_i}$ implies
    $e_i\leq\operatorname{mult}_{c_i}(p)$. By injectivity, summing these multiplicities is the sum
    of the multiplicities of a finite set of distinct roots. Using the multiset of roots of $p$,
    this sum is at most the cardinality of the entire root multiset: roots outside the selected
    image contribute nonnegative multiplicity, while selected field elements that are not roots
    contribute zero. The cardinality of the root multiset is at most the natural degree of $p$,
    giving the asserted inequality. -/)
  (title := /-- Degree budget for distinct roots with multiplicity -/)
  (latexEnv := "lemma")]
lemma frd_distinct_root_budget {ι : Type*} [Fintype ι] (p : Polynomial F) (hp : p ≠ 0)
    (c : ι → F) (hc : Function.Injective c) (e : ι → ℕ)
    (hdvd : ∀ i, (Polynomial.X - Polynomial.C (c i)) ^ e i ∣ p) :
    ∑ i, e i ≤ p.natDegree := by
  classical
  let S : Finset F := Finset.univ.image c
  let R : Finset F := p.roots.toFinset
  calc
    ∑ i, e i ≤ ∑ i, p.roots.count (c i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [Polynomial.count_roots]
      exact (Polynomial.le_rootMultiplicity_iff hp).mpr (hdvd i)
    _ = ∑ x ∈ S, p.roots.count x := by
      change (∑ i, p.roots.count (c i)) =
        ∑ x ∈ Finset.univ.image c, p.roots.count x
      rw [Finset.sum_image]
      exact fun i _ j _ hij => hc hij
    _ = ∑ x ∈ S ∩ R, p.roots.count x := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro x hxS hxnot
      have hxnotR : x ∉ R := by
        intro hxR
        exact hxnot (Finset.mem_inter.mpr ⟨hxS, hxR⟩)
      rw [Multiset.count_eq_zero]
      simpa [R] using hxnotR
    _ ≤ ∑ x ∈ R, p.roots.count x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      intro x _ _
      exact Nat.zero_le _
    _ = p.roots.card := by
      exact Multiset.toFinset_sum_count_eq p.roots
    _ ≤ p.natDegree := Polynomial.card_roots' p

@[blueprint "lem:folded-rank-defect"
  (statement := /-- Let $\mathcal{C}$ be an $m$-folded Reed-Solomon code
    (\cref{def:folded-rs-code}) of message dimension $K$, and let $d$ be an integer with
    $1 \leq d \leq m$. Let $D \subseteq \mathbb{F}_q[X]^{<K}$ be a $d$-dimensional
    $\mathbb{F}_q$-linear space of polynomials of degree strictly less than $K$. For each folded
    symbol $i \in \{0,\dots,N-1\}$ let $r_i$ be the $\mathbb{F}_q$-rank of the image of $D$ under
    the $i$-th symbol projection (\cref{def:frs-symbol-proj}), i.e. the dimension of the space of
    evaluation vectors $\left(f(\gamma^{\,im}),\dots,f(\gamma^{\,im+m-1})\right)$ as $f$ ranges over
    $D$. Then the total \emph{rank defect} over the $N$ folded symbols satisfies
    \[
      \sum_{i=0}^{N-1} \left(d - r_i\right) \;\leq\; \frac{d\,(K-1)}{m - d + 1}.
    \] -/)
  (proof := /-- Put $s=m-d+1$ and $e_i=d-r_i$. By
    \cref{lem:frd-degree-basis}, choose a basis $f_0,\ldots,f_{d-1}$ of $D$ whose degrees
    $n_a$ are pairwise distinct and satisfy $n_a<K$. Rank--nullity identifies $e_i$ with the
    dimension of the kernel of the $i$-th symbol projection restricted to $D$. If $sN\leq K-1$,
    then $e_i\leq d$ for every $i$, and hence
    $s\sum_i e_i\leq sdN\leq d(K-1)$.

    Suppose instead that $sN>K-1$. Then $K\leq sN\leq mN\leq\operatorname{ord}(\gamma)$.
    Consequently the elements $\gamma^{n_a}$ are pairwise distinct. Form the multiplicative
    Wronskian $W$ of the chosen basis as in \cref{def:frd-wron}. Its leading coefficients are
    nonzero, so \cref{lem:frd-wron-ne-zero} shows that $W\neq0$, while
    \cref{lem:frd-wron-natDegree} gives
    $\deg W\leq\sum_a n_a\leq d(K-1)$.

    For each $i<N$ and $t<s$, set $c_{i,t}=\gamma^{im+t}$ and let
    $L_{i,t}:D\to F^d$ send $f$ to
    $(f(c_{i,t}),f(\gamma c_{i,t}),\ldots,f(\gamma^{d-1}c_{i,t}))$.
    Since $t+j<m$ whenever $t<s$ and $j<d$, the kernel of the $i$-th symbol projection is
    contained in $\ker L_{i,t}$. Thus \cref{lem:frd-wron-dvd-ker} implies
    $(X-c_{i,t})^{e_i}\mid W$. The exponents $im+t$ are pairwise distinct and all below $mN$;
    hence the points $c_{i,t}$ are pairwise distinct because $mN$ does not exceed the order of
    $\gamma$. Applying \cref{lem:frd-distinct-root-budget} to these $sN$ points yields
    $s\sum_i e_i\leq\deg W\leq d(K-1)$. In either case, casting this natural-number inequality to
    $\mathbb{R}$ and dividing by the positive number $s=m-d+1$ proves the stated bound. -/)
  (title := /-- Folded Wronskian rank-defect bound -/)
  (latexEnv := "lemma")]
lemma folded_rank_defect (C : folded_rs_code F) (d : ℕ) (hd : 0 < d) (hdm : d ≤ C.m)
    (D : Submodule F (Polynomial F))
    (hDK : D ≤ (Polynomial.degreeLT (R := F) C.K : Submodule F (Polynomial F)))
    (hDdim : Module.finrank F D = d) :
    (∑ i : Fin C.N,
        ((d : ℝ) - (Module.finrank F (D.map (frs_symbol_proj C i)) : ℝ)))
      ≤ (d : ℝ) * ((C.K : ℝ) - 1) / ((C.m : ℝ) - (d : ℝ) + 1) := by
  classical
  obtain ⟨r, b, hbdeg_inj, hbdeg_lt⟩ := frd_degree_basis C.K D hDK
  have hr : r = d := by
    have hcard := Module.finrank_eq_card_basis b
    simp only [Fintype.card_fin] at hcard
    omega
  subst r
  letI : FiniteDimensional F D := b.finiteDimensional_of_finite
  let f : Fin d → Polynomial F := fun a => ((b a : D) : Polynomial F)
  let n : Fin d → ℕ := fun a => (f a).natDegree
  have hninj : Function.Injective n := hbdeg_inj
  have hnlt : ∀ a, n a < C.K := hbdeg_lt
  have hKpos : 0 < C.K := by
    let a : Fin d := ⟨0, hd⟩
    exact Nat.zero_lt_of_lt (hnlt a)
  let den : ℕ := C.m - d + 1
  have hdenpos : 0 < den := by
    dsimp [den]
    omega
  let P : Fin C.N → D →ₗ[F] (Fin C.m → F) :=
    fun i => (frs_symbol_proj C i).domRestrict D
  have hrank_le : ∀ i, Module.finrank F (D.map (frs_symbol_proj C i)) ≤ d := by
    intro i
    rw [← LinearMap.range_domRestrict]
    exact (LinearMap.finrank_range_le (P i)).trans_eq hDdim
  have hdefect_ker : ∀ i,
      d - Module.finrank F (D.map (frs_symbol_proj C i)) =
        Module.finrank F (LinearMap.ker (P i)) := by
    intro i
    have hnull := LinearMap.finrank_range_add_finrank_ker (P i)
    rw [LinearMap.range_domRestrict, hDdim] at hnull
    omega
  have hNat : den * (∑ i : Fin C.N,
      (d - Module.finrank F (D.map (frs_symbol_proj C i)))) ≤ d * (C.K - 1) := by
    by_cases hshort : den * C.N ≤ C.K - 1
    · have hsum : (∑ i : Fin C.N,
          (d - Module.finrank F (D.map (frs_symbol_proj C i)))) ≤ C.N * d := by
        calc
          (∑ i : Fin C.N, (d - Module.finrank F (D.map (frs_symbol_proj C i))))
              ≤ ∑ _i : Fin C.N, d := Finset.sum_le_sum fun i _ => Nat.sub_le _ _
          _ = C.N * d := by simp [Nat.mul_comm]
      nlinarith
    · have hKorder : C.K ≤ orderOf C.gamma := by
        have hdenm : den ≤ C.m := by
          dsimp [den]
          omega
        have hKN : C.K ≤ den * C.N := by omega
        exact hKN.trans ((Nat.mul_le_mul_right C.N hdenm).trans C.horder)
      have hpowinj : Function.Injective (fun a : Fin d => C.gamma ^ n a) := by
        intro a a' haa'
        apply hninj
        apply pow_injOn_Iio_orderOf (x := C.gamma)
        · exact (hnlt a).trans_le hKorder
        · exact (hnlt a').trans_le hKorder
        · exact haa'
      have hcoeff : ∀ a, (f a).coeff (n a) ≠ 0 := by
        intro a
        have hfa : f a ≠ 0 := by
          intro hzero
          have hbzero : b a = 0 := by
            apply Subtype.ext
            exact hzero
          exact b.ne_zero a hbzero
        exact Polynomial.coeff_ne_zero_of_eq_degree (Polynomial.degree_eq_natDegree hfa)
      let W := frd_wron C.gamma d f
      have hWne : W ≠ 0 := frd_wron_ne_zero C.gamma d f n (fun _ => le_rfl) hcoeff hpowinj
      have hWdeg : W.natDegree ≤ d * (C.K - 1) := by
        calc
          W.natDegree ≤ ∑ a, n a := frd_wron_natDegree C.gamma d f n (fun _ => le_rfl)
          _ ≤ ∑ _a : Fin d, (C.K - 1) :=
            Finset.sum_le_sum fun a _ => Nat.le_pred_of_lt (hnlt a)
          _ = d * (C.K - 1) := by simp
      let I := Fin C.N × Fin den
      let point : I → F := fun x => C.gamma ^ (x.1.val * C.m + x.2.val)
      let defect : I → ℕ := fun x =>
        d - Module.finrank F (D.map (frs_symbol_proj C x.1))
      have hpointinj : Function.Injective point := by
        rintro ⟨i, t⟩ ⟨i', t'⟩ hxy
        have hxexp : i.val * C.m + t.val < orderOf C.gamma := by
          refine lt_of_lt_of_le ?_ C.horder
          have ht : t.val < C.m := t.isLt.trans_le (by dsimp [den]; omega)
          nlinarith [i.isLt]
        have hyexp : i'.val * C.m + t'.val < orderOf C.gamma := by
          refine lt_of_lt_of_le ?_ C.horder
          have ht' : t'.val < C.m := t'.isLt.trans_le (by dsimp [den]; omega)
          nlinarith [i'.isLt]
        have hexp := pow_injOn_Iio_orderOf (x := C.gamma) hxexp hyexp hxy
        have hi : i.val = i'.val := by
          have ht : t.val < C.m := t.isLt.trans_le (by dsimp [den]; omega)
          have ht' : t'.val < C.m := t'.isLt.trans_le (by dsimp [den]; omega)
          nlinarith [C.hm]
        have hii : i = i' := Fin.ext hi
        subst i'
        have htt : t = t' := by
          apply Fin.ext
          omega
        subst t'
        rfl
      have hdvd : ∀ x : I,
          (Polynomial.X - Polynomial.C (point x)) ^ defect x ∣ W := by
        intro x
        let L : D →ₗ[F] (Fin d → F) :=
          LinearMap.pi (fun j : Fin d =>
            (Polynomial.leval
              (C.gamma ^ (x.1.val * C.m + x.2.val + j.val))).comp D.subtype)
        have hL : ∀ q j, L q j =
            (q : Polynomial F).eval (C.gamma ^ (j : ℕ) * point x) := by
          intro q j
          change (q : Polynomial F).eval
              (C.gamma ^ (x.1.val * C.m + x.2.val + j.val)) =
            (q : Polynomial F).eval
              (C.gamma ^ (j : ℕ) * C.gamma ^ (x.1.val * C.m + x.2.val))
          rw [← pow_add]
          congr 2
          omega
        have hker : LinearMap.ker (P x.1) ≤ LinearMap.ker L := by
          intro q hq
          rw [LinearMap.mem_ker]
          funext j
          have htj : x.2.val + j.val < C.m := by
            have ht := x.2.isLt
            have hj := j.isLt
            dsimp [den] at ht
            omega
          let k : Fin C.m := ⟨x.2.val + j.val, htj⟩
          have hqk : P x.1 q k = 0 := congrFun (LinearMap.mem_ker.mp hq) k
          simpa [P, L, frs_symbol_proj, k, add_assoc] using hqk
        have hkerfin : defect x ≤ Module.finrank F (LinearMap.ker L) := by
          change d - Module.finrank F (D.map (frs_symbol_proj C x.1)) ≤ _
          rw [hdefect_ker]
          exact Submodule.finrank_mono hker
        have hlarge := frd_wron_dvd_ker C.gamma d D b (point x) L hL
        exact (pow_dvd_pow _ hkerfin).trans hlarge
      have hbudget := frd_distinct_root_budget W hWne point hpointinj defect hdvd
      have hsumI : (∑ x : I, defect x) = den *
          (∑ i : Fin C.N, (d - Module.finrank F (D.map (frs_symbol_proj C i)))) := by
        change (∑ x : Fin C.N × Fin den,
          (d - Module.finrank F (D.map (frs_symbol_proj C x.1)))) = _
        rw [Fintype.sum_prod_type]
        simp only [Prod.fst]
        change (Finset.univ.sum fun x : Fin C.N =>
          Finset.univ.sum fun _y : Fin den =>
            d - Module.finrank F (D.map (frs_symbol_proj C x))) = _
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          Nat.nsmul_eq_mul, Finset.mul_sum]
      rw [hsumI] at hbudget
      exact hbudget.trans hWdeg
  have hdenR : (0 : ℝ) < (den : ℝ) := by positivity
  have hden_cast : (den : ℝ) = (C.m : ℝ) - (d : ℝ) + 1 := by
    dsimp [den]
    rw [Nat.cast_add, Nat.cast_sub hdm]
    norm_num
  have hK_cast : ((C.K - 1 : ℕ) : ℝ) = (C.K : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr hKpos)]
    norm_num
  let S : ℕ := ∑ i : Fin C.N,
    (d - Module.finrank F (D.map (frs_symbol_proj C i)))
  have hsum_cast :
      (∑ i : Fin C.N,
          ((d : ℝ) - (Module.finrank F (D.map (frs_symbol_proj C i)) : ℝ))) =
        (S : ℝ) := by
    dsimp only [S]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (Nat.cast_sub (hrank_le i)).symm
  rw [hsum_cast, ← hden_cast, ← hK_cast]
  apply (le_div_iff₀ hdenR).2
  norm_num only [Nat.cast_mul]
  have hNat' := hNat
  rw [Nat.mul_comm den] at hNat'
  exact_mod_cast hNat'

@[blueprint "lem:folded-main-gap-algebra"
  (statement := /-- Let $m,N,K,d,k$ be nonnegative integers satisfying $N>0$,
    $d<k\leq m$, and $K\leq mN$. Then
    \[
      \frac{K}{m-d+1}<\frac{N}{k+1}+\frac{kK}{(k+1)(m-k+1)}.
    \] -/)
  (proof := /-- Put $a=k+1$, $c=m-k+1$, and $e=m-d+1$. Clearing the positive
    denominator $ace$ reduces the claim to positivity of $Nce+K(ke-ac)$. This expression is
    affine in $K$. If $ke-ac\geq0$, its first summand is already positive. Otherwise the upper
    bound $K\leq mN$ reduces the claim to $K=mN$. With $u=k-d-1\geq0$ and $y=m-k\geq0$, the
    resulting endpoint $ce+m(ke-ac)$ is a sum of nonnegative terms with a positive constant
    term. Hence the cleared numerator is positive, and division by $ace>0$ proves the claim. -/)
  (title := /-- Positivity gap for the folded agreement coefficient -/)
  (latexEnv := "lemma")]
lemma folded_main_gap_algebra (m N K d k : ℕ) (hN : 0 < N) (hdk : d < k)
    (hkm : k ≤ m) (hKN : K ≤ m * N) :
    (K : ℝ) / ((m : ℝ) - (d : ℝ) + 1) <
      (N : ℝ) / ((k : ℝ) + 1) +
        (k : ℝ) * (K : ℝ) / (((k : ℝ) + 1) * ((m : ℝ) - (k : ℝ) + 1)) := by
  let a : ℝ := (k : ℝ) + 1
  let c : ℝ := (m : ℝ) - (k : ℝ) + 1
  let e : ℝ := (m : ℝ) - (d : ℝ) + 1
  let u : ℝ := (k : ℝ) - (d : ℝ) - 1
  let y : ℝ := (m : ℝ) - (k : ℝ)
  let slope : ℝ := (k : ℝ) * e - a * c
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hkmR : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
  have hKNR : (K : ℝ) ≤ (m : ℝ) * (N : ℝ) := by exact_mod_cast hKN
  have hdk1R : (d : ℝ) + 1 ≤ (k : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hdk)
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c]; nlinarith only [hkmR]
  have he : 0 < e := by dsimp [e]; nlinarith only [hdk1R, hkmR]
  have hu : 0 ≤ u := by dsimp [u]; nlinarith only [hdk1R]
  have hy : 0 ≤ y := by dsimp [y]; nlinarith only [hkmR]
  have hend : 0 < c * e + (m : ℝ) * slope := by
    have hid : c * e + (m : ℝ) * slope =
        (d : ℝ) ^ 2 * (u + 1) +
        (d : ℝ) * (2 * u ^ 2 + u * y + 4 * u + 1) +
        (u ^ 3 + u ^ 2 * y + 3 * u ^ 2 + 2 * u * y + 3 * u + 2 * y + 2) := by
      dsimp [a, c, e, u, y, slope]
      ring
    rw [hid]
    have h1 : 0 ≤ (d : ℝ) ^ 2 * (u + 1) := by positivity
    have h2 : 0 ≤ (d : ℝ) * (2 * u ^ 2 + u * y + 4 * u + 1) := by positivity
    have h3 : 0 < u ^ 3 + u ^ 2 * y + 3 * u ^ 2 + 2 * u * y +
        3 * u + 2 * y + 2 := by positivity
    linarith only [h1, h2, h3]
  have hnum : 0 < (N : ℝ) * c * e + (K : ℝ) * slope := by
    by_cases hslope : 0 ≤ slope
    · have hfirst : 0 < (N : ℝ) * c * e := by positivity
      have hsecond : 0 ≤ (K : ℝ) * slope := by positivity
      linarith only [hfirst, hsecond]
    · have hslope' : slope < 0 := lt_of_not_ge hslope
      have hmul := mul_le_mul_of_nonpos_right hKNR (le_of_lt hslope')
      have hend' : 0 < (N : ℝ) * (c * e + (m : ℝ) * slope) := mul_pos hNR hend
      nlinarith only [hmul, hend']
  have hdiff :
      (N : ℝ) / a + (k : ℝ) * (K : ℝ) / (a * c) - (K : ℝ) / e =
        ((N : ℝ) * c * e + (K : ℝ) * slope) / (a * c * e) := by
    dsimp only [slope]
    field_simp [ne_of_gt ha, ne_of_gt hc, ne_of_gt he]
    ring
  have hden : 0 < a * c * e := by positivity
  have hpos := div_pos hnum hden
  rw [← hdiff] at hpos
  change (K : ℝ) / e < (N : ℝ) / a + (k : ℝ) * (K : ℝ) / (a * c)
  linarith only [hpos]

@[blueprint "lem:folded-main-master-algebra"
  (statement := /-- Let $m,N,K,d,k$ be nonnegative integers satisfying $N>0$, $K>0$,
    $d>0$, $d<k\leq m$, and $K\leq mN$. Then
    \[
      N-\frac{K}{m-d+1}
      <\bigl((k-1)d+2\bigr)\left(
        \frac{N}{k+1}+\frac{kK}{(k+1)(m-k+1)}-\frac{K}{m-d+1}\right).
    \] -/)
  (proof := /-- Put $a=k+1$, $c=m-k+1$, $e=m-d+1$, and
    $L=(k-1)d+2$. All three denominators are positive. After multiplication by $ace$, the
    desired strict inequality becomes positivity of
    $Nc e(L-a)+K\bigl(Lke-(L-1)ac\bigr)$. This expression is affine in $K$. If its coefficient
    of $K$ is nonnegative, positivity follows directly; when $d=1$ that coefficient equals
    $ak(k-1)>0$, and when $d\geq2$ the constant term is positive because
    $L-a=(k-1)(d-1)>0$. If the coefficient of $K$ is negative, the hypothesis $K\leq mN$
    reduces the claim to the endpoint $K=mN$. Writing $u=k-d-1\geq0$ and $y=m-k\geq0$,
    the endpoint is a sum of nonnegative monomials with positive constant term, so it is
    strictly positive. Dividing by the positive product $ace$ gives the result. -/)
  (title := /-- Numerical endpoint inequality for the folded subspace bound -/)
  (latexEnv := "lemma")]
lemma folded_main_master_algebra (m N K d k : ℕ) (hN : 0 < N) (hK : 0 < K)
    (hd : 0 < d) (hdk : d < k) (hkm : k ≤ m) (hKN : K ≤ m * N) :
    (N : ℝ) - (K : ℝ) / ((m : ℝ) - (d : ℝ) + 1) <
      (((k : ℝ) - 1) * (d : ℝ) + 2) *
        ((N : ℝ) / ((k : ℝ) + 1) +
          (k : ℝ) * (K : ℝ) / (((k : ℝ) + 1) * ((m : ℝ) - (k : ℝ) + 1)) -
          (K : ℝ) / ((m : ℝ) - (d : ℝ) + 1)) := by
  let a : ℝ := (k : ℝ) + 1
  let c : ℝ := (m : ℝ) - (k : ℝ) + 1
  let e : ℝ := (m : ℝ) - (d : ℝ) + 1
  let u : ℝ := (k : ℝ) - (d : ℝ) - 1
  let y : ℝ := (m : ℝ) - (k : ℝ)
  let L : ℝ := ((k : ℝ) - 1) * (d : ℝ) + 2
  let Qc : ℝ := L - 1
  let slope : ℝ := L * (k : ℝ) * e - Qc * a * c
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdkR : (d : ℝ) < (k : ℝ) := by exact_mod_cast hdk
  have hkmR : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
  have hKNR : (K : ℝ) ≤ (m : ℝ) * (N : ℝ) := by exact_mod_cast hKN
  have hdk1R : (d : ℝ) + 1 ≤ (k : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hdk)
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c]; nlinarith only [hkmR]
  have he : 0 < e := by dsimp [e]; nlinarith only [hdk1R, hkmR]
  have hu : 0 ≤ u := by dsimp [u]; nlinarith only [hdk1R]
  have hy : 0 ≤ y := by dsimp [y]; nlinarith only [hkmR]
  have hkend : 0 < c * e * (L - a) + (m : ℝ) * slope := by
    have hid : c * e * (L - a) + (m : ℝ) * slope =
        (d : ℝ) ^ 4 * (u + 1) +
        (d : ℝ) ^ 3 * (3 * u ^ 2 + u * y + 5 * u + 1) +
        (d : ℝ) ^ 2 *
          (3 * u ^ 3 + 2 * u ^ 2 * y + 7 * u ^ 2 + 2 * u * y +
            6 * u + 3 * y + 5) +
        (d : ℝ) *
          (u ^ 4 + u ^ 3 * y + 3 * u ^ 3 + 2 * u ^ 2 * y +
            7 * u ^ 2 + 5 * u * y + 11 * u + y + 3) +
        (2 * u ^ 3 + 2 * u ^ 2 * y + 6 * u ^ 2 + 3 * u * y +
          5 * u + 2 * y + 2) := by
      dsimp [a, c, e, u, y, L, Qc, slope]
      ring
    rw [hid]
    have ht1 : 0 ≤ (d : ℝ) ^ 4 * (u + 1) := by positivity
    have ht2 : 0 ≤ (d : ℝ) ^ 3 * (3 * u ^ 2 + u * y + 5 * u + 1) := by
      positivity
    have ht3 : 0 ≤ (d : ℝ) ^ 2 *
        (3 * u ^ 3 + 2 * u ^ 2 * y + 7 * u ^ 2 + 2 * u * y +
          6 * u + 3 * y + 5) := by
      positivity
    have ht4 : 0 ≤ (d : ℝ) *
        (u ^ 4 + u ^ 3 * y + 3 * u ^ 3 + 2 * u ^ 2 * y +
          7 * u ^ 2 + 5 * u * y + 11 * u + y + 3) := by
      positivity
    have ht5 : 0 < 2 * u ^ 3 + 2 * u ^ 2 * y + 6 * u ^ 2 +
        3 * u * y + 5 * u + 2 * y + 2 := by
      positivity
    linarith only [ht1, ht2, ht3, ht4, ht5]
  have hnum : 0 < (N : ℝ) * c * e * (L - a) + (K : ℝ) * slope := by
    by_cases hslope : 0 ≤ slope
    · by_cases hd1 : d = 1
      · have hd1R : (d : ℝ) = 1 := by exact_mod_cast hd1
        have hslopepos : 0 < slope := by
          have hid : slope = a * (k : ℝ) * ((k : ℝ) - 1) := by
            dsimp [a, c, e, L, Qc, slope]
            rw [hd1R]
            ring
          rw [hid]
          have hk2R : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 2 ≤ k by omega)
          have hkpos : (0 : ℝ) < (k : ℝ) := by linarith only [hk2R]
          have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith only [hk2R]
          exact mul_pos (mul_pos ha hkpos) hkm1
        have hsecond : 0 < (K : ℝ) * slope := mul_pos hKR hslopepos
        have hLa : 0 ≤ L - a := by
          dsimp [L, a]
          rw [hd1R]
          ring_nf
          positivity
        have hfirst : 0 ≤ (N : ℝ) * c * e * (L - a) := by positivity
        linarith only [hfirst, hsecond]
      · have hd2R : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 2 ≤ d by omega)
        have hLa : 0 < L - a := by
          have hid : L - a = ((k : ℝ) - 1) * ((d : ℝ) - 1) := by
            dsimp [L, a]
            ring
          rw [hid]
          have hk1R : (1 : ℝ) < (k : ℝ) := by nlinarith only [hdkR, hd2R]
          have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith only [hk1R]
          have hdm1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith only [hd2R]
          exact mul_pos hkm1 hdm1
        have hfirst : 0 < (N : ℝ) * c * e * (L - a) := by positivity
        have hsecond : 0 ≤ (K : ℝ) * slope := by positivity
        linarith only [hfirst, hsecond]
    · have hslope' : slope < 0 := lt_of_not_ge hslope
      have hmul := mul_le_mul_of_nonpos_right hKNR (le_of_lt hslope')
      have hend' : 0 < (N : ℝ) * (c * e * (L - a) + (m : ℝ) * slope) :=
        mul_pos hNR hkend
      nlinarith only [hmul, hend']
  have hdiff :
      L * ((N : ℝ) / a + (k : ℝ) * (K : ℝ) / (a * c) - (K : ℝ) / e) -
          ((N : ℝ) - (K : ℝ) / e) =
        ((N : ℝ) * c * e * (L - a) + (K : ℝ) * slope) / (a * c * e) := by
    dsimp only [Qc, slope]
    field_simp [ne_of_gt ha, ne_of_gt hc, ne_of_gt he]
    ring
  have hden : 0 < a * c * e := by positivity
  have hpos := div_pos hnum hden
  rw [← hdiff] at hpos
  change (N : ℝ) - (K : ℝ) / e <
    L * ((N : ℝ) / a + (k : ℝ) * (K : ℝ) / (a * c) - (K : ℝ) / e)
  linarith only [hpos]

@[blueprint "lem:folded-main"
  (statement := /-- Let $\mathcal{C}$ be an $m$-folded Reed-Solomon code (\cref{def:folded-rs-code})
    of blocklength $N$ and rate $R$ (\cref{def:frs-rate}). Let $d$ and $k$ be nonnegative integers
    satisfying $d < k \leq m$, let $g \in (\mathbb{F}_q^m)^N$ be any received word, and let
    $\mathcal{H} \subseteq (\mathbb{F}_q^m)^N$ be an affine subspace whose direction has dimension
    exactly $d$ and all of whose points are codewords (\cref{def:frs-code}). Then the intersection
    of $\mathcal{H}$ with the
    decoding list (\cref{def:frs-list}) at the folded radius $\eta_k$ (\cref{def:frs-radius})
    satisfies $\left|\mathcal{H} \cap \mathcal{L}(g,\eta_k)\right| \leq (k-1)\,d + 1$. -/)
  (proof := /-- We argue by strong induction on $d$. If $d=0$, then
    $\mathcal H.\mathrm{direction}=\{0\}$, so any two points of $\mathcal H$ are equal and the
    asserted intersection has cardinality at most one. We may therefore assume $d>0$ and that
    \[
      S:=\mathcal H\cap\mathcal L(g,\eta_k)
    \]
    is nonempty, since the empty case is immediate.

    Let $E\colon\mathbb F_q[X]\to(\mathbb F_q^m)^N$ be the linear encoding map
    (\cref{def:frs-encode}), let $P_{<K}=\mathbb F_q[X]^{<K}$, and put
    \[
      D=P_{<K}\cap E^{-1}(\mathcal H.\mathrm{direction}).
    \]
    Choose $h_0\in S$. Every $v\in\mathcal H.\mathrm{direction}$ satisfies
    $v+h_0\in\mathcal H$; since both $h_0$ and $v+h_0$ belong to the code
    (\cref{def:frs-code}), subtracting polynomial representatives shows that $E(D)$ is exactly
    $\mathcal H.\mathrm{direction}$. Moreover, $E$ is injective on $P_{<K}$. Indeed, if a nonzero
    difference polynomial $p\in P_{<K}$ encoded to zero, it would vanish at all $mN$ pairwise
    distinct powers of $\gamma$. Applying \cref{lem:frd-distinct-root-budget} with multiplicity
    one at each evaluation point would give $mN\leq\deg p$, contradicting
    $\deg p<K\leq mN$. Consequently $\dim D=d$.

    For $i\in\{0,\ldots,N-1\}$, let $Q_i$ be the $i$th folded-coordinate projection and set
    \[
      r_i=\dim Q_i(\mathcal H.\mathrm{direction}).
    \]
    The identity $Q_i\circ E=\mathrm{proj}_i$ from \cref{def:frs-symbol-proj} identifies this
    image with the image of $D$ under the polynomial symbol projection. Thus
    \cref{lem:folded-rank-defect} gives
    \[
      \sum_i(d-r_i)\leq\frac{d(K-1)}{m-d+1}
      \leq\frac{dK}{m-d+1}.                                      \tag{1}
    \]
    Let $K_i$ be the image in the ambient word space of the kernel of
    $Q_i|_{\mathcal H.\mathrm{direction}}$. Rank--nullity gives
    $\dim K_i=d-r_i$. If $r_i>0$, the fiber
    $\mathcal H\cap\{x:x_i=g_i\}$ is either empty or, after choosing a point $a$ in it, is the
    affine subspace $a+K_i$. It is contained in the code, has dimension $d-r_i<d$, and
    $d-r_i<k$. The induction hypothesis therefore yields
    \[
      \bigl|S\cap\{x:x_i=g_i\}\bigr|\leq(k-1)(d-r_i)+1.            \tag{2}
    \]

    For $x\in S$, write $A_x=\{i:x_i=g_i\}$. From the definitions of the list, distance, and
    radius (\cref{def:frs-list,def:frs-dist,def:frs-radius}), the strict distance inequality
    implies
    \[
      (1-\eta_k)N\leq |A_x|.
    \]
    Summing over $x\in S$ and interchanging the two finite sums gives
    \[
      (1-\eta_k)N|S|
      \leq\sum_i\bigl|S\cap\{x:x_i=g_i\}\bigr|.                   \tag{3}
    \]
    Let $B=\{i:r_i=0\}$ and $G=\{i:r_i\ne0\}$. On $B$ we use the trivial upper bound $|S|$,
    while on $G$ we use (2). Since
    \[
      |B|+|G|=N,\qquad
      d|B|+\sum_{i\in G}(d-r_i)=\sum_i(d-r_i),
    \]
    equations (1)--(3) imply
    \[
      \bigl((1-\eta_k)N-|B|\bigr)|S|
      \leq N-|B|+(k-1)\left(\frac{dK}{m-d+1}-d|B|\right).         \tag{4}
    \]
    Because $d>0$, (1) also gives $|B|\leq K/(m-d+1)$. The inequality
    \cref{lem:folded-main-gap-algebra}, together with the formula for $\eta_k$, shows that
    $K/(m-d+1)<(1-\eta_k)N$; hence the coefficient on the left of (4) is positive.

    Suppose that $|S|>(k-1)d+1$. Integrality then gives $(k-1)d+2\leq|S|$. By
    \cref{lem:folded-main-master-algebra},
    \[
      N-\frac{K}{m-d+1}
      <\bigl((k-1)d+2\bigr)
        \left((1-\eta_k)N-\frac{K}{m-d+1}\right).
    \]
    Since $|B|\leq K/(m-d+1)$, expanding both sides and adding the nonnegative difference
    $K/(m-d+1)-|B|$ yields
    \[
      N-|B|+(k-1)\left(\frac{dK}{m-d+1}-d|B|\right)
      <\bigl((k-1)d+2\bigr)\bigl((1-\eta_k)N-|B|\bigr).
    \]
    Positivity of the last factor and $(k-1)d+2\leq|S|$ contradict (4). Therefore
    $|S|\leq(k-1)d+1$, as required. -/)
  (title := /-- Subspace-intersection list bound for folded RS codes -/)
  (latexEnv := "lemma")]
lemma folded_main (C : folded_rs_code F) (d k : ℕ) (hdk : d < k) (hkm : k ≤ C.m)
    (g : Fin C.N → Fin C.m → F)
    (H : AffineSubspace F (Fin C.N → Fin C.m → F))
    (hHC : (H : Set (Fin C.N → Fin C.m → F)) ⊆ frs_code C)
    (hdim : Module.finrank F H.direction = d) :
    ((H : Set (Fin C.N → Fin C.m → F)) ∩ frs_list C g (frs_radius C k)).ncard
      ≤ (k - 1) * d + 1 := by
  classical
  induction d using Nat.strong_induction_on generalizing H with
  | h d ih =>
    by_cases hd0 : d = 0
    · rw [hd0] at hdim ⊢
      have hdir : H.direction = ⊥ := Submodule.finrank_eq_zero.mp hdim
      have hsingle : ((H : Set (Fin C.N → Fin C.m → F)) ∩
          frs_list C g (frs_radius C k)).Subsingleton := by
        intro x hx y hy
        have hxy := H.vsub_mem_direction hx.1 hy.1
        rw [hdir] at hxy
        exact sub_eq_zero.mp (by simpa using hxy)
      simpa using Set.ncard_le_one_iff_subsingleton.mpr hsingle
    · have hd : 0 < d := Nat.pos_of_ne_zero hd0
      have hdm : d ≤ C.m := (Nat.le_of_lt hdk).trans hkm
      let S : Set (Fin C.N → Fin C.m → F) :=
        (H : Set (Fin C.N → Fin C.m → F)) ∩ frs_list C g (frs_radius C k)
      change S.ncard ≤ (k - 1) * d + 1
      by_cases hSne : S.Nonempty
      · obtain ⟨h₀, hh₀H, hh₀L⟩ := hSne
        let E : Polynomial F →ₗ[F] (Fin C.N → Fin C.m → F) :=
          { toFun := frs_encode C
            map_add' := by
              intro p q
              funext i j
              simp [frs_encode]
            map_smul' := by
              intro a p
              funext i j
              simp [frs_encode] }
        let P₀ : Submodule F (Polynomial F) := Polynomial.degreeLT (R := F) C.K
        let D : Submodule F (Polynomial F) := P₀ ⊓ H.direction.comap E
        have hDle : D ≤ P₀ := inf_le_left
        have hDmap : D.map E = H.direction := by
          apply le_antisymm
          · rintro v ⟨p, hp, rfl⟩
            exact hp.2
          · intro v hv
            have hvh₀ : v + h₀ ∈ H := H.vadd_mem_of_mem_direction hv hh₀H
            obtain ⟨p₀, hp₀, hep₀⟩ := hHC hh₀H
            obtain ⟨p₁, hp₁, hep₁⟩ := hHC hvh₀
            refine ⟨p₁ - p₀, ⟨P₀.sub_mem hp₁ hp₀, ?_⟩, ?_⟩
            · change E (p₁ - p₀) ∈ H.direction
              have heq : E (p₁ - p₀) = v := by
                rw [map_sub]
                change frs_encode C p₁ - frs_encode C p₀ = v
                rw [hep₁, hep₀]
                simp
              exact heq.symm ▸ hv
            · change E (p₁ - p₀) = v
              rw [map_sub]
              change frs_encode C p₁ - frs_encode C p₀ = v
              rw [hep₁, hep₀]
              simp
        have hEinj : Function.Injective (E.domRestrict P₀) := by
          intro p q hpq
          apply Subtype.ext
          let r : Polynomial F := (p : Polynomial F) - (q : Polynomial F)
          have hrP₀ : r ∈ P₀ := P₀.sub_mem p.property q.property
          have hEr : E r = 0 := by
            dsimp [r]
            rw [map_sub]
            have hpqE : E (p : Polynomial F) = E (q : Polynomial F) := hpq
            rw [hpqE, sub_self]
          by_contra hneq
          have hrne : r ≠ 0 := sub_ne_zero.mpr hneq
          let point : Fin C.N × Fin C.m → F :=
            fun x => C.gamma ^ (x.1.val * C.m + x.2.val)
          have hpointinj : Function.Injective point := by
            rintro ⟨i, j⟩ ⟨i', j'⟩ hxy
            have hxexp : i.val * C.m + j.val < orderOf C.gamma := by
              refine lt_of_lt_of_le ?_ C.horder
              nlinarith [i.isLt, j.isLt, C.hm]
            have hyexp : i'.val * C.m + j'.val < orderOf C.gamma := by
              refine lt_of_lt_of_le ?_ C.horder
              nlinarith [i'.isLt, j'.isLt, C.hm]
            have hexp := pow_injOn_Iio_orderOf (x := C.gamma) hxexp hyexp hxy
            have hi : i.val = i'.val := by
              nlinarith [j.isLt, j'.isLt, C.hm]
            have hii : i = i' := Fin.ext hi
            subst i'
            have hj : j = j' := by
              apply Fin.ext
              omega
            subst j'
            rfl
          have hdvd : ∀ x : Fin C.N × Fin C.m,
              (Polynomial.X - Polynomial.C (point x)) ^ (1 : ℕ) ∣ r := by
            intro x
            have heval : r.eval (point x) = 0 := by
              have hx := congrFun (congrFun hEr x.1) x.2
              simpa [E, frs_encode, point] using hx
            simpa [heval] using
              (Polynomial.X_sub_C_dvd_sub_C_eval (p := r) (a := point x))
          have hbudget := frd_distinct_root_budget r hrne point hpointinj
            (fun _ => 1) hdvd
          have hrdeg : r.natDegree < C.K :=
            (Polynomial.natDegree_lt_iff_degree_lt hrne).2
              (Polynomial.mem_degreeLT.mp hrP₀)
          have hcard : C.N * C.m ≤ r.natDegree := by
            simpa [Fintype.sum_prod_type, Nat.mul_comm] using hbudget
          have : C.K ≤ r.natDegree := by
            exact C.hK.trans (by simpa [Nat.mul_comm] using hcard)
          omega
        have hEDinj : Function.Injective (E.domRestrict D) := by
          intro p q hpq
          have hpq' : (⟨p.1, hDle p.2⟩ : P₀) = ⟨q.1, hDle q.2⟩ := by
            apply hEinj
            exact hpq
          apply Subtype.eq
          exact congrArg (fun z : P₀ => (z : Polynomial F)) hpq'
        have hDdim : Module.finrank F D = d := by
          calc
            Module.finrank F D = Module.finrank F (LinearMap.range (E.domRestrict D)) :=
              (LinearMap.finrank_range_of_inj hEDinj).symm
            _ = Module.finrank F (D.map E) := by rw [LinearMap.range_domRestrict]
            _ = Module.finrank F H.direction := by rw [hDmap]
            _ = d := hdim
        let Q : Fin C.N → (Fin C.N → Fin C.m → F) →ₗ[F] (Fin C.m → F) :=
          fun i => LinearMap.proj i
        have hproj : ∀ i, D.map (frs_symbol_proj C i) = H.direction.map (Q i) := by
          intro i
          apply le_antisymm
          · rintro y ⟨p, hp, hpy⟩
            have hEp : E p ∈ H.direction := by
              rw [← hDmap]
              exact ⟨p, hp, rfl⟩
            refine ⟨E p, hEp, ?_⟩
            rw [← hpy]
            rfl
          · rintro y ⟨v, hv, hvy⟩
            have hvD : v ∈ D.map E := by
              rw [hDmap]
              exact hv
            rcases hvD with ⟨p, hp, hpv⟩
            refine ⟨p, hp, ?_⟩
            calc
              frs_symbol_proj C i p = Q i (E p) := by rfl
              _ = Q i v := congrArg (Q i) hpv
              _ = y := hvy
        let r : Fin C.N → ℕ := fun i => Module.finrank F (H.direction.map (Q i))
        have hrle : ∀ i, r i ≤ d := by
          intro i
          dsimp [r]
          rw [← LinearMap.range_domRestrict]
          exact (LinearMap.finrank_range_le ((Q i).domRestrict H.direction)).trans_eq hdim
        have hdefect :
            (∑ i : Fin C.N, ((d : ℝ) - (r i : ℝ))) ≤
              (d : ℝ) * ((C.K : ℝ) - 1) / ((C.m : ℝ) - (d : ℝ) + 1) := by
          have hf := folded_rank_defect C d hd hdm D (by simpa [P₀] using hDle) hDdim
          have hfin : ∀ i, Module.finrank F (D.map (frs_symbol_proj C i)) = r i := by
            intro i
            rw [hproj i]
          simpa only [hfin] using hf
        have hdefectK :
            (∑ i : Fin C.N, ((d : ℝ) - (r i : ℝ))) ≤
              (d : ℝ) * (C.K : ℝ) / ((C.m : ℝ) - (d : ℝ) + 1) := by
          calc
            _ ≤ (d : ℝ) * ((C.K : ℝ) - 1) /
                ((C.m : ℝ) - (d : ℝ) + 1) := hdefect
            _ ≤ (d : ℝ) * (C.K : ℝ) /
                ((C.m : ℝ) - (d : ℝ) + 1) := by
              have hden : (0 : ℝ) < (C.m : ℝ) - (d : ℝ) + 1 := by
                exact_mod_cast (show 0 < C.m - d + 1 by omega)
              gcongr
              norm_num
        let P : Fin C.N → H.direction →ₗ[F] (Fin C.m → F) :=
          fun i => (Q i).domRestrict H.direction
        let Kdir : Fin C.N → Submodule F (Fin C.N → Fin C.m → F) :=
          fun i => (LinearMap.ker (P i)).map H.direction.subtype
        have hKdim : ∀ i, Module.finrank F (Kdir i) = d - r i := by
          intro i
          have hnull := LinearMap.finrank_range_add_finrank_ker (P i)
          have hrange : LinearMap.range (P i) = H.direction.map (Q i) := by
            simpa [P] using (LinearMap.range_domRestrict H.direction (Q i))
          rw [hrange, hdim] at hnull
          change r i + Module.finrank F (LinearMap.ker (P i)) = d at hnull
          dsimp [Kdir]
          rw [Submodule.finrank_map_subtype_eq]
          omega
        have hKleH : ∀ i, Kdir i ≤ H.direction := by
          intro i v hv
          rcases hv with ⟨u, hu, rfl⟩
          exact u.property
        have hKker : ∀ i v, v ∈ Kdir i → Q i v = 0 := by
          intro i v hv
          rcases hv with ⟨u, hu, rfl⟩
          exact LinearMap.mem_ker.mp hu
        have hgood : ∀ i, 0 < r i →
            (S ∩ {x | x i = g i}).ncard ≤ (k - 1) * (d - r i) + 1 := by
          intro i hri
          by_cases hfiber : (S ∩ {x | x i = g i}).Nonempty
          · obtain ⟨a, haS, hai⟩ := hfiber
            let Hi : AffineSubspace F (Fin C.N → Fin C.m → F) :=
              AffineSubspace.mk' a (Kdir i)
            have hHi_eq : (Hi : Set (Fin C.N → Fin C.m → F)) =
                (H : Set (Fin C.N → Fin C.m → F)) ∩ {x | x i = g i} := by
              ext x
              constructor
              · intro hx
                have hxK : x - a ∈ Kdir i := by simpa [Hi] using hx
                have hxH : x ∈ H := by
                  have := H.vadd_mem_of_mem_direction (hKleH i hxK) haS.1
                  simpa using this
                have hxQ := hKker i (x - a) hxK
                have hxia : x i = a i := by
                  apply sub_eq_zero.mp
                  simpa [Q] using hxQ
                exact ⟨hxH, hxia.trans hai⟩
              · rintro ⟨hxH, hxg⟩
                have hxaH : x - a ∈ H.direction := H.vsub_mem_direction hxH haS.1
                let u : H.direction := ⟨x - a, hxaH⟩
                have hu : u ∈ LinearMap.ker (P i) := by
                  rw [LinearMap.mem_ker]
                  change Q i (x - a) = 0
                  apply sub_eq_zero.mpr
                  simpa [Q] using hxg.trans hai.symm
                have hxaK : x - a ∈ Kdir i := by
                  exact ⟨u, hu, rfl⟩
                simpa [Hi] using hxaK
            have hHiC : (Hi : Set (Fin C.N → Fin C.m → F)) ⊆ frs_code C := by
              intro x hx
              exact hHC ((Set.ext_iff.mp hHi_eq x).mp hx).1
            have hHidim : Module.finrank F Hi.direction = d - r i := by
              rw [show Hi.direction = Kdir i by simp [Hi]]
              exact hKdim i
            have hsmall : d - r i < d := Nat.sub_lt hd hri
            have hsmallk : d - r i < k := (Nat.sub_le d (r i)).trans_lt hdk
            have hih := ih (d - r i) hsmall hsmallk Hi hHiC hHidim
            have hset : S ∩ {x | x i = g i} =
                (Hi : Set (Fin C.N → Fin C.m → F)) ∩
                  frs_list C g (frs_radius C k) := by
              rw [hHi_eq]
              simp only [S]
              ext x
              simp [and_left_comm, and_assoc, and_comm]
            simpa [hset] using hih
          · have hempty : S ∩ {x | x i = g i} = ∅ :=
              Set.not_nonempty_iff_eq_empty.mp hfiber
            simp [hempty]
        let A : Finset (Fin C.N → Fin C.m → F) := S.toFinset
        let Agree : (Fin C.N → Fin C.m → F) → Set (Fin C.N) :=
          fun x => {i | x i = g i}
        have hAcard : A.card = S.ncard := by
          simpa [A] using (Set.ncard_eq_toFinset_card S).symm
        have hlower_point : ∀ x ∈ A,
            (1 - frs_radius C k) * (C.N : ℝ) ≤ ((Agree x).ncard : ℝ) := by
          intro x hxA
          have hxS : x ∈ S := by simpa [A] using hxA
          have hxl := hxS.2.2
          have hcomp : {i : Fin C.N | g i ≠ x i} = (Agree x)ᶜ := by
            ext i
            simp [Agree, ne_comm]
          rw [frs_dist, hcomp, Set.ncard_compl] at hxl
          simp only [Nat.card_fin] at hxl
          have hAgreeLe : (Agree x).ncard ≤ C.N := by
            simpa using Set.ncard_le_card (Agree x)
          rw [Nat.cast_sub hAgreeLe] at hxl
          have hNpos : (0 : ℝ) < (C.N : ℝ) := by exact_mod_cast C.hN
          have hmul := (div_lt_iff₀ hNpos).mp hxl
          nlinarith
        have hlower :
            (1 - frs_radius C k) * (C.N : ℝ) * (S.ncard : ℝ) ≤
              ∑ x ∈ A, ((Agree x).ncard : ℝ) := by
          calc
            _ = ∑ _x ∈ A, ((1 - frs_radius C k) * (C.N : ℝ)) := by
              simp [hAcard, mul_comm]
            _ ≤ ∑ x ∈ A, ((Agree x).ncard : ℝ) := by
              exact Finset.sum_le_sum fun x hx => hlower_point x hx
        have hdouble_nat :
            (∑ x ∈ A, (Agree x).ncard) =
              ∑ i : Fin C.N, (S ∩ {x | x i = g i}).ncard := by
          calc
            _ = ∑ x ∈ A, ∑ i : Fin C.N, if x i = g i then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [Set.ncard_eq_toFinset_card]
              simp [Agree]
            _ = ∑ i : Fin C.N, ∑ x ∈ A, if x i = g i then 1 else 0 := by
              rw [Finset.sum_comm]
            _ = ∑ i : Fin C.N, (S ∩ {x | x i = g i}).ncard := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Set.ncard_eq_toFinset_card]
              calc
                _ = (A.filter fun x => x i = g i).card := by simp
                _ = _ := by
                  apply congrArg Finset.card
                  ext x
                  simp [A]
        have hdouble :
            (∑ x ∈ A, ((Agree x).ncard : ℝ)) =
              ∑ i : Fin C.N, ((S ∩ {x | x i = g i}).ncard : ℝ) := by
          exact_mod_cast hdouble_nat
        let B : Finset (Fin C.N) := Finset.univ.filter fun i => r i = 0
        let G : Finset (Fin C.N) := Finset.univ.filter fun i => r i ≠ 0
        have hupper_partition :
            (∑ i : Fin C.N, (S ∩ {x | x i = g i}).ncard) ≤
              (∑ _i ∈ B, S.ncard) +
                ∑ i ∈ G, ((k - 1) * (d - r i) + 1) := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun i => r i = 0) (fun i => (S ∩ {x | x i = g i}).ncard)]
          apply Nat.add_le_add
          · apply Finset.sum_le_sum
            intro i hi
            exact Set.ncard_le_ncard Set.inter_subset_left
          · apply Finset.sum_le_sum
            intro i hi
            apply hgood i
            have hir : r i ≠ 0 := by simpa [G] using hi
            omega
        have hupper_nat :
            (∑ i : Fin C.N, (S ∩ {x | x i = g i}).ncard) ≤
              B.card * S.ncard + G.card +
                (k - 1) * (∑ i ∈ G, (d - r i)) := by
          calc
            _ ≤ (∑ _i ∈ B, S.ncard) +
                ∑ i ∈ G, ((k - 1) * (d - r i) + 1) := hupper_partition
            _ = B.card * S.ncard + G.card +
                (k - 1) * (∑ i ∈ G, (d - r i)) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
              simp [Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        have hBGcard : B.card + G.card = C.N := by
          simpa [B, G] using Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin C.N))) (p := fun i => r i = 0)
        have hdefect_partition :
            B.card * d + (∑ i ∈ G, (d - r i)) =
              ∑ i : Fin C.N, (d - r i) := by
          have hp := Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun i => r i = 0) (fun i => d - r i)
          have hbad : (∑ i ∈ B, (d - r i)) = B.card * d := by
            apply Finset.sum_eq_card_nsmul
            intro i hi
            have hir : r i = 0 := by simpa [B] using hi
            simp [hir]
          simpa [B, G, hbad] using hp
        rw [hdouble] at hlower
        have hupper_real :
            (∑ i : Fin C.N, ((S ∩ {x | x i = g i}).ncard : ℝ)) ≤
              (B.card : ℝ) * (S.ncard : ℝ) + (G.card : ℝ) +
                (k - 1 : ℕ) * ((∑ i ∈ G, (d - r i) : ℕ) : ℝ) := by
          exact_mod_cast hupper_nat
        have hBGreal : (B.card : ℝ) + (G.card : ℝ) = (C.N : ℝ) := by
          exact_mod_cast hBGcard
        have hpartreal :
            (B.card : ℝ) * (d : ℝ) + ((∑ i ∈ G, (d - r i) : ℕ) : ℝ) =
              ((∑ i : Fin C.N, (d - r i) : ℕ) : ℝ) := by
          exact_mod_cast hdefect_partition
        have hsumcast :
            ((∑ i : Fin C.N, (d - r i) : ℕ) : ℝ) =
              ∑ i : Fin C.N, ((d : ℝ) - (r i : ℝ)) := by
          rw [Nat.cast_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Nat.cast_sub (hrle i)]
        have htotaldefect :
            ((∑ i : Fin C.N, (d - r i) : ℕ) : ℝ) ≤
              (d : ℝ) * (C.K : ℝ) / ((C.m : ℝ) - (d : ℝ) + 1) := by
          rw [hsumcast]
          exact hdefectK
        have hmR : (0 : ℝ) < (C.m : ℝ) := by exact_mod_cast C.hm
        have hNR : (0 : ℝ) < (C.N : ℝ) := by exact_mod_cast C.hN
        have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
        have hkplus : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have hkden : (0 : ℝ) < (C.m : ℝ) - (k : ℝ) + 1 := by
          exact_mod_cast (show 0 < C.m - k + 1 by omega)
        have hdden : (0 : ℝ) < (C.m : ℝ) - (d : ℝ) + 1 := by
          exact_mod_cast (show 0 < C.m - d + 1 by omega)
        have halpha :
            (1 - frs_radius C k) * (C.N : ℝ) =
              (C.N : ℝ) / ((k : ℝ) + 1) +
                (k : ℝ) * (C.K : ℝ) /
                  (((k : ℝ) + 1) * ((C.m : ℝ) - (k : ℝ) + 1)) := by
          rw [frs_radius, frs_rate]
          field_simp
          ring
        have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
        have hdkR : (d : ℝ) < (k : ℝ) := by exact_mod_cast hdk
        have hkmR : (k : ℝ) ≤ (C.m : ℝ) := by exact_mod_cast hkm
        have hKR : (C.K : ℝ) ≤ (C.m : ℝ) * (C.N : ℝ) := by
          exact_mod_cast C.hK
        have hKpos : 0 < C.K := by
          by_contra hK
          have hK0 : C.K = 0 := Nat.eq_zero_of_not_pos hK
          have hPbot : P₀ = ⊥ := by
            ext p
            simp [P₀, hK0, Polynomial.mem_degreeLT]
          have hDbot : D = ⊥ := by
            apply le_antisymm
            · rw [← hPbot]
              exact hDle
            · exact bot_le
          rw [hDbot] at hDdim
          simp at hDdim
          omega
        have hKposR : (0 : ℝ) < (C.K : ℝ) := by exact_mod_cast hKpos
        have hGnonneg : (0 : ℝ) ≤ ((∑ i ∈ G, (d - r i) : ℕ) : ℝ) := by positivity
        have hbdefect :
            (B.card : ℝ) * (d : ℝ) ≤
              (d : ℝ) * (C.K : ℝ) / ((C.m : ℝ) - (d : ℝ) + 1) := by
          nlinarith [hpartreal, htotaldefect]
        have hb :
            (B.card : ℝ) ≤ (C.K : ℝ) / ((C.m : ℝ) - (d : ℝ) + 1) := by
          apply le_of_mul_le_mul_left (a := (d : ℝ))
          · calc
              (d : ℝ) * (B.card : ℝ) = (B.card : ℝ) * (d : ℝ) := by ring
              _ ≤ (d : ℝ) * (C.K : ℝ) / ((C.m : ℝ) - (d : ℝ) + 1) := hbdefect
              _ = (d : ℝ) * ((C.K : ℝ) / ((C.m : ℝ) - (d : ℝ) + 1)) := by ring
          · exact hdR
        have hgap := folded_main_gap_algebra C.m C.N C.K d k C.hN hdk hkm C.hK
        rw [← halpha] at hgap
        have hApos :
            (0 : ℝ) < (1 - frs_radius C k) * (C.N : ℝ) - (B.card : ℝ) := by
          nlinarith only [hb, hgap]
        have hgd :
            ((∑ i ∈ G, (d - r i) : ℕ) : ℝ) ≤
              (d : ℝ) * (C.K : ℝ) / ((C.m : ℝ) - (d : ℝ) + 1) -
                (B.card : ℝ) * (d : ℝ) := by
          nlinarith only [hpartreal, htotaldefect]
        have hkminus : (0 : ℝ) ≤ (k : ℝ) - 1 := by
          have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
          linarith
        have hgd_mul := mul_le_mul_of_nonneg_left hgd hkminus
        have hchain :
            ((1 - frs_radius C k) * (C.N : ℝ) - (B.card : ℝ)) *
                (S.ncard : ℝ) ≤
              (C.N : ℝ) - (B.card : ℝ) + ((k : ℝ) - 1) *
                ((d : ℝ) * (C.K : ℝ) / ((C.m : ℝ) - (d : ℝ) + 1) -
                  (B.card : ℝ) * (d : ℝ)) := by
          have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
            rw [Nat.cast_sub (show 1 ≤ k by omega)]
            norm_num
          rw [hkcast] at hupper_real
          have hlowup := hlower.trans hupper_real
          have hgcard : (G.card : ℝ) = (C.N : ℝ) - (B.card : ℝ) := by
            linarith only [hBGreal]
          nlinarith only [hlowup, hgcard, hgd_mul]
        by_contra hbound
        have hslarge : (k - 1) * d + 2 ≤ S.ncard := by omega
        have hslargeR :
            ((k : ℝ) - 1) * (d : ℝ) + 2 ≤ (S.ncard : ℝ) := by
          have hslargeR' : (((k - 1) * d + 2 : ℕ) : ℝ) ≤ (S.ncard : ℝ) :=
            Nat.cast_le.mpr hslarge
          norm_num [Nat.cast_sub (show 1 ≤ k by omega)] at hslargeR'
          exact hslargeR'
        have hmaster := folded_main_master_algebra C.m C.N C.K d k C.hN hKpos hd hdk hkm C.hK
        rw [← halpha] at hmaster
        have halgebra :
            (C.N : ℝ) - (B.card : ℝ) + ((k : ℝ) - 1) *
                ((d : ℝ) * (C.K : ℝ) / ((C.m : ℝ) - (d : ℝ) + 1) -
                  (B.card : ℝ) * (d : ℝ)) <
              (((k : ℝ) - 1) * (d : ℝ) + 2) *
                ((1 - frs_radius C k) * (C.N : ℝ) - (B.card : ℝ)) := by
          have hx : 0 ≤ (C.K : ℝ) / ((C.m : ℝ) - (d : ℝ) + 1) -
              (B.card : ℝ) := by linarith only [hb]
          have hid :
              ((((k : ℝ) - 1) * (d : ℝ) + 2) *
                  ((1 - frs_radius C k) * (C.N : ℝ) - (B.card : ℝ))) -
                ((C.N : ℝ) - (B.card : ℝ) + ((k : ℝ) - 1) *
                  ((d : ℝ) * (C.K : ℝ) / ((C.m : ℝ) - (d : ℝ) + 1) -
                    (B.card : ℝ) * (d : ℝ))) =
              (((((k : ℝ) - 1) * (d : ℝ) + 2) *
                  ((1 - frs_radius C k) * (C.N : ℝ) -
                    (C.K : ℝ) / ((C.m : ℝ) - (d : ℝ) + 1))) -
                ((C.N : ℝ) - (C.K : ℝ) / ((C.m : ℝ) - (d : ℝ) + 1))) +
                ((C.K : ℝ) / ((C.m : ℝ) - (d : ℝ) + 1) - (B.card : ℝ)) := by
            ring
          rw [← sub_pos, hid]
          have hmpos := sub_pos.mpr hmaster
          nlinarith only [hmpos, hx]
        have hscale := mul_le_mul_of_nonneg_right hslargeR (le_of_lt hApos)
        have hlt := hchain.trans_lt (halgebra.trans_le hscale)
        nlinarith only [hlt]
      · have hSe : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
        simp [hSe]

@[blueprint "thm:frs-list-size"
  (statement := /-- Let $\mathcal{C}$ be an $m$-folded Reed-Solomon code (\cref{def:folded-rs-code})
    of blocklength $N$ and rate $R$ (\cref{def:frs-rate}). For every integer $k$ with
    $1 \leq k \leq m$ and every received word $g \in (\mathbb{F}_q^m)^N$, the decoding list
    (\cref{def:frs-list}) at the folded radius $\eta_k = \frac{k}{k+1}\left(1 -
    \frac{m}{m-k+1}R\right)$ (\cref{def:frs-radius}) has size at most $(k-1)^2 + 1$:
    $\left|\mathcal{L}\!\left(g, \eta_k\right)\right| \leq (k-1)^2 + 1$. -/)
  (proof := /-- We distinguish two cases according to whether the codeword space is large enough to
    host a $(k-1)$-dimensional affine family.

    \emph{Nondegenerate case: $k - 1 \leq K$ and $k - 1 \leq mN$.} Here both hypotheses of
    \cref{lem:lin-alg-rs} are met, so — applied with the given $k$ (which satisfies
    $1 \leq k \leq m$) — there is an affine subspace $\mathcal{H}$ of the codeword space of
    dimension exactly $k-1$, all of whose points are codewords, such that
    $\mathcal{L}(g,\eta_k) \subseteq \mathcal{H}$. Since the decoding list is contained in
    $\mathcal{H}$, we have $\mathcal{H} \cap \mathcal{L}(g,\eta_k) = \mathcal{L}(g,\eta_k)$, hence
    $\left|\mathcal{L}(g,\eta_k)\right| = \left|\mathcal{H} \cap \mathcal{L}(g,\eta_k)\right|$.
    Applying \cref{lem:folded-main} with dimension parameter $d = k-1$ (so that $d < k$ and
    $k \leq m$) yields $\left|\mathcal{H} \cap \mathcal{L}(g,\eta_k)\right| \leq (k-1)(k-1) + 1
    = (k-1)^2 + 1$, and combining gives $\left|\mathcal{L}(g,\eta_k)\right| \leq (k-1)^2 + 1$.

    \emph{Degenerate case: $k - 1 > K$ or $k - 1 > mN$.} The codeword space (\cref{def:frs-code})
    is the image of $\mathbb{F}_q[X]^{<K}$ under the linear encoding map (\cref{def:frs-encode})
    inside the ambient space $(\mathbb{F}_q^m)^N$, so it is a linear subspace whose dimension
    $d_0$ satisfies both $d_0 \leq K$ (the domain has dimension $K$) and $d_0 \leq mN$ (the
    codomain has dimension $mN$). In the present case $\min(K, mN) \leq k - 2$, hence
    $d_0 \leq k - 2 < k$. Take $\mathcal{H}$ to be this codeword space itself: a $d_0$-dimensional
    linear subspace, all of whose points are codewords, which contains the entire list
    $\mathcal{L}(g,\eta_k)$, so that $\mathcal{H} \cap \mathcal{L}(g,\eta_k) =
    \mathcal{L}(g,\eta_k)$. Applying \cref{lem:folded-main} with dimension parameter $d = d_0$
    (so that $d_0 < k$ and $k \leq m$) gives
    $\left|\mathcal{L}(g,\eta_k)\right| = \left|\mathcal{H} \cap \mathcal{L}(g,\eta_k)\right|
    \leq (k-1)d_0 + 1 \leq (k-1)(k-2) + 1 \leq (k-1)^2 + 1$. -/)
  (title := /-- FRS list-size bound $(k-1)^2 + 1$ -/)
  (latexEnv := "theorem")]
theorem frs_list_size (C : folded_rs_code F) (k : ℕ) (hk1 : 1 ≤ k) (hkm : k ≤ C.m)
    (g : Fin C.N → Fin C.m → F) :
    (frs_list C g (frs_radius C k)).ncard ≤ (k - 1) ^ 2 + 1 := by
  classical
  have hdegenerate :
      (¬ k - 1 ≤ C.K ∨ ¬ k - 1 ≤ C.m * C.N) →
        (frs_list C g (frs_radius C k)).ncard ≤ (k - 1) ^ 2 + 1 := by
    intro hsmall
    let V := Polynomial.degreeLT (R := F) C.K
    let E : V →ₗ[F] (Fin C.N → Fin C.m → F) :=
      { toFun := fun f => frs_encode C (f : Polynomial F)
        map_add' := by
          intro f h
          funext i j
          simp [frs_encode]
        map_smul' := by
          intro c f
          funext i j
          simp [frs_encode] }
    letI : Module.Finite F V :=
      Module.Finite.equiv (Polynomial.degreeLTEquiv F C.K).symm
    have hVdim : Module.finrank F V = C.K := by
      rw [(Polynomial.degreeLTEquiv F C.K).finrank_eq, Module.finrank_pi]
      simp [V]
    let H : AffineSubspace F (Fin C.N → Fin C.m → F) :=
      (LinearMap.range E).toAffineSubspace
    let d := Module.finrank F H.direction
    have hdir : H.direction = LinearMap.range E := by
      simp [H]
    have hdK : d ≤ C.K := by
      calc
        d = Module.finrank F (LinearMap.range E) := by
          change Module.finrank F H.direction = _
          rw [hdir]
        _ ≤ Module.finrank F V := LinearMap.finrank_range_le E
        _ = C.K := hVdim
    have hdN : d ≤ C.m * C.N := by
      calc
        d = Module.finrank F (LinearMap.range E) := by
          change Module.finrank F H.direction = _
          rw [hdir]
        _ ≤ Module.finrank F (Fin C.N → Fin C.m → F) :=
          Submodule.finrank_le (LinearMap.range E)
        _ = C.N * C.m := by
          simp [Module.finrank_pi_fintype, Module.finrank_pi]
        _ = C.m * C.N := Nat.mul_comm _ _
    have hd : d < k := by
      rcases hsmall with hsmall | hsmall
      · omega
      · omega
    have hHcode :
        (H : Set (Fin C.N → Fin C.m → F)) ⊆ frs_code C := by
      intro h hh
      change h ∈ LinearMap.range E at hh
      obtain ⟨f, rfl⟩ := hh
      exact ⟨(f : Polynomial F), f.property, rfl⟩
    have hlistH :
        frs_list C g (frs_radius C k) ⊆
          (H : Set (Fin C.N → Fin C.m → F)) := by
      intro h hh
      obtain ⟨f, hf, rfl⟩ := hh.1
      change frs_encode C f ∈ LinearMap.range E
      exact ⟨⟨f, hf⟩, rfl⟩
    have hbound := folded_main C d k hd hkm g H hHcode rfl
    rw [Set.inter_eq_right.mpr hlistH] at hbound
    have hdle : d ≤ k - 2 := by
      rcases hsmall with hsmall | hsmall
      · omega
      · omega
    calc
      (frs_list C g (frs_radius C k)).ncard ≤ (k - 1) * d + 1 := hbound
      _ ≤ (k - 1) * (k - 2) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left (k - 1) hdle) 1
      _ ≤ (k - 1) * (k - 1) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left (k - 1) (by omega)) 1
      _ = (k - 1) ^ 2 + 1 := by rw [pow_two]
  by_cases hkK : k - 1 ≤ C.K
  · by_cases hkN : k - 1 ≤ C.m * C.N
    · obtain ⟨H, hHcode, hHdim, hlistH⟩ := lin_alg_rs C k hk1 hkm hkK hkN g
      have hbound := folded_main C (k - 1) k (by omega) hkm g H hHcode hHdim
      rw [Set.inter_eq_right.mpr hlistH] at hbound
      simpa [pow_two] using hbound
    · exact hdegenerate (Or.inr hkN)
  · exact hdegenerate (Or.inl hkK)

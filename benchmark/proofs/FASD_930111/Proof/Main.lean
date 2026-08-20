import Architect
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.ENNReal.Holder

set_option linter.all false
set_option maxHeartbeats 500000

open scoped Gradient

@[blueprint "def:finite-lp-norm"
  (statement := /-- For $p\in[0,\infty]$ and $z\in\mathbb R^d$, define $\lVert z\rVert_p$ by transporting the coordinate function underlying the Euclidean vector $z$ to Mathlib's finite `PiLp` space of exponent $p$ and taking its norm. -/)
  (title := /-- The finite $\ell_p$ norm -/)
  (latexEnv := "definition")]
noncomputable def finite_lp_norm (p : ENNReal) {d : ℕ}
    (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ‖WithLp.toLp p (WithLp.ofLp z)‖

@[blueprint "def:l-smooth-with-respect-to-lp"
  (statement := /-- Let $p,q\in[0,\infty]$, let $L\in\mathbb R$, and let $f:\mathbb R^d\to\mathbb R$ be differentiable.  We say that $f$ is $L$-smooth with respect to $\lVert\cdot\rVert_p$, with dual norm represented by $\lVert\cdot\rVert_q$, if
  \[
    \lVert\nabla f(y)-\nabla f(x)\rVert_q
      \le L\lVert y-x\rVert_p
  \]
  for every $x,y\in\mathbb R^d$. -/)
  (title := /-- Smoothness with respect to a finite $\ell_p$ norm -/)
  (latexEnv := "definition")]
def l_smooth_with_respect_to_lp {d : ℕ} (p q : ENNReal) (L : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ x y,
    finite_lp_norm q (gradient f y - gradient f x) ≤
      L * finite_lp_norm p (y - x)

@[blueprint "def:hasd-data"
  (statement := /-- A HASD data set in $\mathbb R^d$ consists of sequences $(x_t)$, $(y_t)$, and $(v_t)$ of points, scalar sequences $(A_t)$, $(a_t)$, and $(\rho_t)$, and estimate functions $(\psi_t)$. -/)
  (title := /-- Data carried by a HASD trajectory -/)
  (latexEnv := "definition")]
structure hasd_data (d : ℕ) where
  x : ℕ → EuclideanSpace ℝ (Fin d)
  y : ℕ → EuclideanSpace ℝ (Fin d)
  v : ℕ → EuclideanSpace ℝ (Fin d)
  A : ℕ → ℝ
  a : ℕ → ℝ
  rho : ℕ → ℝ
  psi : ℕ → EuclideanSpace ℝ (Fin d) → ℝ

@[blueprint "def:is-hasd-run"
  (statement := /-- Let $f:\mathbb R^d\to\mathbb R$, let $L>0$, let $p$ and $q$ be the primal and dual norm exponents, let $T\in\mathbb N$, and let $x_0\in\mathbb R^d$.  A data set is a HASD run through time $T$ if it has $x_0$ as its initial point, $A_0=0$, and $\psi_0(z)=\frac12\lVert z-x_0\rVert_2^2$; if $v_t$ minimizes $\psi_t$; and if, for every $0\le t<T$, the parameters and iterates satisfy the update rules
  \[
  A_{t+1}=A_t+a_{t+1},\qquad
  a_{t+1}^2=\frac{A_t+A_{t+1}}{18L\rho_t},\qquad
  y_t=\left(1-\frac{a_{t+1}}{A_{t+1}}\right)x_t+
       \frac{a_{t+1}}{A_{t+1}}v_t,
  \]
  with $a_{t+1},\rho_t>0$.  The point $x_{t+1}$ minimizes the prescribed steepest-descent model at $y_t$; $\rho_t$ lies between one half and twice the squared ratio $\lVert\nabla f(x_{t+1})\rVert_2^2/\lVert\nabla f(x_{t+1})\rVert_q^2$; and $\psi_{t+1}$ is obtained by adding the affine first-order model of $f$ at $x_{t+1}$ with weight $a_{t+1}$. -/)
  (title := /-- The HASD update interface -/)
  (latexEnv := "definition")]
def is_hasd_run {d : ℕ} (run : hasd_data d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (p q : ENNReal)
    (T : ℕ) (x0 : EuclideanSpace ℝ (Fin d)) : Prop :=
  run.x 0 = x0 ∧
  run.A 0 = 0 ∧
  (∀ z, run.psi 0 z = (1 / 2 : ℝ) * ‖z - x0‖ ^ 2) ∧
  (∀ t, t ≤ T → IsMinOn (run.psi t) Set.univ (run.v t)) ∧
  ∀ t, t < T →
    0 < run.a (t + 1) ∧
    0 < run.rho t ∧
    run.A (t + 1) = run.A t + run.a (t + 1) ∧
    run.a (t + 1) ^ 2 =
      (run.A t + run.A (t + 1)) / (18 * L * run.rho t) ∧
    run.y t =
      (1 - run.a (t + 1) / run.A (t + 1)) • run.x t +
        (run.a (t + 1) / run.A (t + 1)) • run.v t ∧
    IsMinOn
      (fun z => inner ℝ (gradient f (run.y t)) (z - run.y t) +
        L * finite_lp_norm p (z - run.y t) ^ 2)
      Set.univ (run.x (t + 1)) ∧
    (1 / 2 : ℝ) *
        (‖gradient f (run.x (t + 1))‖ ^ 2 /
          finite_lp_norm q (gradient f (run.x (t + 1))) ^ 2) ≤ run.rho t ∧
    run.rho t ≤ 2 *
        (‖gradient f (run.x (t + 1))‖ ^ 2 /
          finite_lp_norm q (gradient f (run.x (t + 1))) ^ 2) ∧
    ∀ z,
      run.psi (t + 1) z = run.psi t z + run.a (t + 1) *
        (f (run.x (t + 1)) +
          inner ℝ (gradient f (run.x (t + 1))) (z - run.x (t + 1)))

@[blueprint "def:hasd-recurrence-bonus"
  (statement := /-- For a HASD data set, define
  \[
    B_t=\frac1{18L}\sum_{i=0}^{t-1}a_{i+1}
       \lVert\nabla f(x_{i+1})\rVert_q^2.
  \] -/)
  (title := /-- The HASD recurrence bonus -/)
  (latexEnv := "definition")]
noncomputable def hasd_recurrence_bonus {d : ℕ} (run : hasd_data d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (q : ENNReal)
    (t : ℕ) : ℝ :=
  (1 / (18 * L)) * ∑ i ∈ Finset.range t,
    run.a (i + 1) * finite_lp_norm q (gradient f (run.x (i + 1))) ^ 2

@[blueprint "def:average-gradient-ratio"
  (statement := /-- For $T>0$, define the average gradient-norm ratio along a HASD trajectory by
  \[
    \mathcal G_T=\frac1T\sum_{t=0}^{T-1}
       \frac{\lVert\nabla f(x_{t+1})\rVert_q}
            {\lVert\nabla f(x_{t+1})\rVert_2}.
  \]  Lean's division on $\mathbb R$ is total; the run conditions are responsible for excluding a zero denominator whenever the algorithm performs a step. -/)
  (title := /-- The average gradient-norm ratio -/)
  (latexEnv := "definition")]
noncomputable def average_gradient_ratio {d : ℕ} (run : hasd_data d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (q : ENNReal) (T : ℕ) : ℝ :=
  (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
    finite_lp_norm q (gradient f (run.x (t + 1))) /
      ‖gradient f (run.x (t + 1))‖

@[blueprint "lem:convex-first-order-lower-bound"
  (statement := /-- Let $f:\mathbb R^d\to\mathbb R$ be convex and differentiable.  Then, for all $x,z\in\mathbb R^d$,
  \[
    f(x)+\langle\nabla f(x),z-x\rangle\le f(z).
  \] -/)
  (proof := /-- Set $v=z-x$ and
  \[
    R(h)=f(x+h)-f(x)-\langle\nabla f(x),h\rangle.
  \]
  Differentiability at $x$ gives $R(h)=o(\lVert h\rVert)$ as $h\to0$.  Restricting this estimate to $h=tv$ yields $R(tv)=o(t)$ and consequently $R(tv)/t\to0$ as $t\to0$.  For every $t$ with $0<t<1$, convexity gives
  \[
    f(x+tv)\le (1-t)f(x)+tf(z).
  \]
  After subtracting $f(x)+t\langle\nabla f(x),v\rangle$ and dividing by $t>0$, this becomes
  \[
    \frac{R(tv)}{t}\le f(z)-f(x)-\langle\nabla f(x),v\rangle.
  \]
  Passing to the right-hand limit at $0$ proves that the right-hand side is nonnegative, which is the asserted inequality. -/)
  (title := /-- The first-order lower bound for a convex function -/)
  (latexEnv := "lemma")]
lemma convex_first_order_lower_bound {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hconv : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (x z : EuclideanSpace ℝ (Fin d)) :
    f x + inner ℝ (gradient f x) (z - x) ≤ f z := by
  let v := z - x
  let r : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun h => f (x + h) - f x - inner ℝ (gradient f x) h
  have hr : r =o[nhds 0] (fun h : EuclideanSpace ℝ (Fin d) => h) := by
    simpa [r] using
      (hasGradientAt_iff_isLittleO_nhds_zero.mp (hdiff x).hasGradientAt)
  have htv : Filter.Tendsto (fun t : ℝ => t • v) (nhds 0) (nhds 0) := by
    have hid : Filter.Tendsto (fun t : ℝ => t) (nhds 0) (nhds 0) :=
      Filter.tendsto_id
    simpa using (Filter.Tendsto.smul_const hid v)
  have hray : (fun t : ℝ => r (t • v)) =o[nhds 0] (fun t : ℝ => t • v) := by
    have hcomp := hr.comp_tendsto htv
    change (fun t : ℝ => r (t • v)) =o[nhds 0] (fun t : ℝ => t • v) at hcomp
    exact hcomp
  have hvbig : (fun t : ℝ => t • v) =O[nhds 0] (fun t : ℝ => t) := by
    refine Asymptotics.IsBigO.of_bound ‖v‖ (Filter.Eventually.of_forall ?_)
    intro t
    simp [norm_smul, mul_comm]
  have hratio : (fun t : ℝ => r (t • v)) =o[nhds 0] (fun t : ℝ => t) :=
    hray.trans_isBigO hvbig
  have htend : Filter.Tendsto (fun t : ℝ => r (t • v) / t)
      (nhds 0) (nhds 0) :=
    (Asymptotics.isLittleO_iff_tendsto (by
      intro t ht
      subst t
      simp [r])).mp hratio
  have hevent :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        r (t • v) / t ≤ f z - f x - inner ℝ (gradient f x) v := by
    filter_upwards [eventually_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)]
      with t htpos htlt
    have hc := hconv.2 (Set.mem_univ x) (Set.mem_univ z)
      (sub_nonneg.mpr htlt.le) htpos.le (by ring)
    have harg : (1 - t) • x + t • z = x + t • v := by
      dsimp [v]
      module
    rw [harg] at hc
    simp only [smul_eq_mul] at hc
    rw [div_le_iff₀ htpos]
    dsimp [r]
    simp only [inner_smul_right]
    nlinarith
  have hnonneg : 0 ≤ f z - f x - inner ℝ (gradient f x) v :=
    le_of_tendsto (hx := nhdsWithin_Ioi_neBot le_rfl)
      (htend.mono_left inf_le_left) hevent
  dsimp [v] at hnonneg
  linarith

@[blueprint "lem:hasd-progress-bound"
  (statement := /-- Let $d,T\in\mathbb N$, let $L\in\mathbb R$, let $p,q\in[0,\infty]$ be Hölder-conjugate exponents with $p\ge2$, and let $x_0\in\mathbb R^d$.  Suppose that $f:\mathbb R^d\to\mathbb R$ satisfies
  \[
    \lVert\nabla f(y)-\nabla f(x)\rVert_q
      \le L\lVert y-x\rVert_p
      \qquad\text{for all }x,y\in\mathbb R^d,
  \]
  and that the data form a HASD run through time $T$ initialized at $x_0$.  Then, for every $t\in\mathbb N$ with $t<T$,
  \[
  \langle\nabla f(x_{t+1}),y_t-x_{t+1}\rangle
     \ge L\lVert x_{t+1}-y_t\rVert_p^2
     \ge \frac1{9L}\lVert\nabla f(x_{t+1})\rVert_q^2.
  \] -/)
  (proof := /-- Put $s=x_{t+1}-y_t$, $g_0=\nabla f(y_t)$,
  $g_1=\nabla f(x_{t+1})$, and $S=\lVert s\rVert_p$.  First,
  the positivity and recurrence clauses in \cref{def:is-hasd-run}, together
  with $A_0=0$, imply inductively that $A_u\ge0$ for $u\le T$ and then
  imply $L>0$ from the positive weight identity at time $t$.

  By \cref{def:finite-lp-norm} and Hölder conjugacy, finite-dimensional
  Hölder's inequality gives
  $\langle u,v\rangle\le\lVert u\rVert_q\lVert v\rVert_p$.
  The minimization clause in \cref{def:is-hasd-run}, evaluated at
  $y_t+c s$ for arbitrary $c\in\mathbb R$, says
  \[
    \langle g_0,s\rangle+LS^2
      \le c\langle g_0,s\rangle+Lc^2S^2.
  \]
  Minimizing this scalar quadratic, with the case $S=0$ treated separately,
  yields $\langle g_0,s\rangle=-2LS^2$.

  For completeness, the dual-norm attainment used below is obtained
  coordinatewise.  For $w\ne0$, set $G=\lVert w\rVert_q$ and
  \[
    v_i=\operatorname{sign}(w_i)
      \left(\frac{|w_i|}{G}\right)^{q-1}.
  \]
  The relation $(q-1)p=q$ and the finite-sum formula in
  \cref{def:finite-lp-norm} give
  $\lVert v\rVert_p=1$ and $\langle w,v\rangle=G$; for $w=0$, take
  $v=0$.  Applying this construction to $g_0$, perturbing the minimizer by
  $-\varepsilon v$, and using the triangle inequality shows
  $\lVert g_0\rVert_q\le2LS$: otherwise the positive choice
  $\varepsilon=(\lVert g_0\rVert_q-2LS)/(2L)$ would strictly decrease
  the model.

  The smoothness inequality in
  \cref{def:l-smooth-with-respect-to-lp} now gives
  $\lVert g_1-g_0\rVert_q\le LS$.  Hence the triangle inequality yields
  $\lVert g_1\rVert_q\le3LS$, and squaring and dividing by $9L>0$
  gives
  $LS^2\ge(9L)^{-1}\lVert g_1\rVert_q^2$.  Finally, Hölder's inequality,
  the bound on $g_1-g_0$, and
  $\langle g_0,s\rangle=-2LS^2$ give
  $\langle g_1,s\rangle\le-LS^2$, which is the first asserted
  inequality after replacing $s$ by $x_{t+1}-y_t$. -/)
  (title := /-- Progress of one HASD steepest-descent step -/)
  (latexEnv := "lemma")]
lemma hasd_progress_bound {d : ℕ} {run : hasd_data d}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} {p q : ENNReal}
    [hpq : ENNReal.HolderConjugate p q]
    {T : ℕ} {x0 : EuclideanSpace ℝ (Fin d)} (hp : (2 : ℝ) ≤ p.toReal)
    (hsmooth : l_smooth_with_respect_to_lp p q L f)
    (hrun : is_hasd_run run f L p q T x0) {t : ℕ} (ht : t < T) :
    inner ℝ (gradient f (run.x (t + 1))) (run.y t - run.x (t + 1)) ≥
        L * finite_lp_norm p (run.x (t + 1) - run.y t) ^ 2 ∧
      L * finite_lp_norm p (run.x (t + 1) - run.y t) ^ 2 ≥
        (1 / (9 * L)) * finite_lp_norm q (gradient f (run.x (t + 1))) ^ 2 := by
  classical
  have hp1 : 1 < p.toReal := lt_of_lt_of_le one_lt_two hp
  have hpqR : p.toReal.HolderConjugate q.toReal :=
    ENNReal.HolderConjugate.toReal hp1
  letI : Fact (1 ≤ p) := ⟨hpq.one_le⟩
  letI : Fact (1 ≤ q) := ⟨hpq.symm.one_le⟩
  rcases hrun.2.2.2.2 t ht with
    ⟨ha, hrho, hA, hweight, hy, hmin, hrholow, hrhohigh, hpsi⟩
  have hA_nonneg : ∀ u, u ≤ T → 0 ≤ run.A u := by
    intro u hu
    induction u with
    | zero => simpa [hrun.2.1]
    | succ u ih =>
        have huT : u < T := Nat.lt_of_succ_le hu
        have hu := hrun.2.2.2.2 u huT
        rw [hu.2.2.1]
        exact add_nonneg (ih (Nat.le_of_lt huT)) hu.1.le
  have hnum : 0 < run.A t + run.A (t + 1) := by
    rw [hA]
    have hAt := hA_nonneg t (Nat.le_of_lt ht)
    nlinarith
  have hquot : 0 < (run.A t + run.A (t + 1)) / (18 * L * run.rho t) := by
    rw [← hweight]
    positivity
  have hden : 0 < 18 * L * run.rho t := by
    rcases (div_pos_iff.mp hquot) with h | h
    · exact h.2
    · nlinarith [hnum, h.1]
  have hL : 0 < L := by nlinarith
  have hholder (u v : EuclideanSpace ℝ (Fin d)) :
      inner ℝ u v ≤ finite_lp_norm q u * finite_lp_norm p v := by
    simpa [PiLp.inner_apply, finite_lp_norm,
      PiLp.norm_eq_sum hpqR.symm.pos, PiLp.norm_eq_sum hpqR.pos, mul_comm]
      using (Real.inner_le_Lp_mul_Lq (s := Finset.univ)
        (f := fun i : Fin d => u i) (g := fun i : Fin d => v i) hpqR.symm)
  set s := run.x (t + 1) - run.y t
  set g0 := gradient f (run.y t)
  set g1 := gradient f (run.x (t + 1))
  set S := finite_lp_norm p s
  have hscale (c : ℝ) :
      inner ℝ g0 s + L * S ^ 2 ≤
        c * inner ℝ g0 s + L * c ^ 2 * S ^ 2 := by
    have hc := hmin (Set.mem_univ (run.y t + c • s))
    simp only [Set.mem_setOf_eq] at hc
    have hc' : inner ℝ g0 s + L * S ^ 2 ≤
        inner ℝ g0 (c • s) + L * finite_lp_norm p (c • s) ^ 2 := by
      simpa [s, S] using hc
    have hnorm_smul : finite_lp_norm p (c • s) = |c| * S := by
      change ‖c • WithLp.toLp p (WithLp.ofLp s)‖ =
        |c| * ‖WithLp.toLp p (WithLp.ofLp s)‖
      simpa only [Real.norm_eq_abs] using
        (norm_smul c (WithLp.toLp p (WithLp.ofLp s)))
    rw [inner_smul_right, hnorm_smul, mul_pow, sq_abs] at hc'
    simpa [mul_assoc] using hc'
  have hSnonneg : 0 ≤ S := by exact norm_nonneg _
  have hinner : inner ℝ g0 s = -2 * L * S ^ 2 := by
    by_cases hS0 : S = 0
    · have h0 := hscale 0
      have h2 := hscale 2
      rw [hS0] at h0 h2 ⊢
      norm_num at h0 h2 ⊢
      linarith
    · have hSpos : 0 < S := lt_of_le_of_ne hSnonneg (Ne.symm hS0)
      let a := inner ℝ g0 s
      let D := L * S ^ 2
      have hD : 0 < D := by dsimp [D]; positivity
      have hc := hscale (-a / (2 * D))
      have hmul := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4 * D by positivity)
      dsimp [a, D] at hmul ⊢
      field_simp [hD.ne'] at hmul
      nlinarith
  have hExp : (q.toReal - 1) * p.toReal = q.toReal := by
    rw [hpqR.conjugate_eq]
    field_simp [ne_of_gt (sub_pos.mpr hp1)]
    ring
  have hdual_exists (w : EuclideanSpace ℝ (Fin d)) :
      ∃ v : EuclideanSpace ℝ (Fin d),
        finite_lp_norm p v ≤ 1 ∧ inner ℝ w v = finite_lp_norm q w := by
    by_cases hw : w = 0
    · refine ⟨0, ?_, ?_⟩
      · simp [finite_lp_norm]
      · simp [hw, finite_lp_norm]
    · let G := finite_lp_norm q w
      have hGpos : 0 < G := by
        simpa [G, finite_lp_norm] using hw
      let v : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
        (fun i : Fin d => (SignType.sign (w i) : ℝ) *
          (|w i| / G) ^ (q.toReal - 1))
      refine ⟨v, ?_, ?_⟩
      · unfold finite_lp_norm
        rw [PiLp.norm_eq_sum hpqR.pos]
        simp only [v, WithLp.toLp_ofLp, Real.norm_eq_abs]
        have hterm (i : Fin d) :
            |(SignType.sign (w i) : ℝ) *
                (|w i| / G) ^ (q.toReal - 1)| ^ p.toReal =
              (|w i| / G) ^ q.toReal := by
          by_cases hi : w i = 0
          · simp [hi, SignType.sign, hpqR.pos.ne', hpqR.symm.pos.ne']
          · have hr : 0 ≤ |w i| / G := (div_pos (abs_pos.mpr hi) hGpos).le
            have hsign : |(SignType.sign (w i) : ℝ)| = 1 := by
              rcases lt_or_gt_of_ne hi with hi | hi
              · simp [SignType.sign, hi, not_lt.mpr hi.le]
              · simp [SignType.sign, hi, not_lt.mpr hi.le]
            rw [abs_mul, hsign, one_mul, abs_of_nonneg (Real.rpow_nonneg hr _),
              ← Real.rpow_mul hr, hExp]
        simp_rw [hterm]
        let R := ∑ i : Fin d, |w i| ^ q.toReal
        have hRnonneg : 0 ≤ R := Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
        have hG_eq : G = R ^ (1 / q.toReal) := by
          simp [G, R, finite_lp_norm, PiLp.norm_eq_sum hpqR.symm.pos]
        have hGpow : G ^ q.toReal = R := by
          have hq0 : q.toReal ≠ 0 := ne_of_gt hpqR.symm.pos
          rw [hG_eq, ← Real.rpow_mul hRnonneg,
            show (1 / q.toReal) * q.toReal = 1 by field_simp [hq0], Real.rpow_one]
        have hratio : ∑ i : Fin d, (|w i| / G) ^ q.toReal = 1 := by
          simp_rw [Real.div_rpow (abs_nonneg _) hGpos.le]
          rw [← Finset.sum_div, show (∑ i : Fin d, |w i| ^ q.toReal) = R by rfl,
            ← hGpow, div_self]
          exact (Real.rpow_pos_of_pos hGpos _).ne'
        rw [hratio]
        norm_num
      · change inner ℝ w v = G
        rw [PiLp.inner_apply]
        simp only [v, WithLp.toLp_ofLp, RCLike.inner_apply, conj_trivial]
        have hsignterm (i : Fin d) :
            (SignType.sign (w i) : ℝ) * (|w i| / G) ^ (q.toReal - 1) * w i =
              |w i| * (|w i| / G) ^ (q.toReal - 1) := by
          rcases lt_trichotomy (w i) 0 with hi | hi | hi
          · simp [SignType.sign, hi, not_lt.mpr hi.le, abs_of_neg hi]
            ring
          · simp [hi, SignType.sign]
          · simp [SignType.sign, hi, not_lt.mpr hi.le, abs_of_pos hi]
            ring
        simp_rw [hsignterm]
        have hratio_term (i : Fin d) :
            |w i| * (|w i| / G) ^ (q.toReal - 1) =
              G * (|w i| / G) ^ q.toReal := by
          by_cases hi : w i = 0
          · simp [hi, hpqR.symm.pos.ne']
          · have hrpos : 0 < |w i| / G := div_pos (abs_pos.mpr hi) hGpos
            have habs : |w i| = G * (|w i| / G) := by field_simp
            calc
              |w i| * (|w i| / G) ^ (q.toReal - 1) =
                  G * (|w i| / G) * (|w i| / G) ^ (q.toReal - 1) := by
                    exact congrArg
                      (fun z : ℝ => z * (|w i| / G) ^ (q.toReal - 1)) habs
              _ = G * ((|w i| / G) ^ (1 : ℝ) *
                    (|w i| / G) ^ (q.toReal - 1)) := by
                    simp only [Real.rpow_one]
                    ring
              _ = G * (|w i| / G) ^ (1 + (q.toReal - 1)) := by
                    exact congrArg (fun z : ℝ => G * z)
                      (Real.rpow_add hrpos 1 (q.toReal - 1)).symm
              _ = G * (|w i| / G) ^ q.toReal := by ring_nf
        simp_rw [hratio_term]
        let R := ∑ i : Fin d, |w i| ^ q.toReal
        have hRnonneg : 0 ≤ R :=
          Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
        have hG_eq : G = R ^ (1 / q.toReal) := by
          simp [G, R, finite_lp_norm, PiLp.norm_eq_sum hpqR.symm.pos]
        have hGpow : G ^ q.toReal = R := by
          have hq0 : q.toReal ≠ 0 := ne_of_gt hpqR.symm.pos
          rw [hG_eq, ← Real.rpow_mul hRnonneg,
            show (1 / q.toReal) * q.toReal = 1 by field_simp [hq0], Real.rpow_one]
        have hratio : ∑ i : Fin d, (|w i| / G) ^ q.toReal = 1 := by
          simp_rw [Real.div_rpow (abs_nonneg _) hGpos.le]
          rw [← Finset.sum_div, show (∑ i : Fin d, |w i| ^ q.toReal) = R by rfl,
            ← hGpow, div_self]
          exact (Real.rpow_pos_of_pos hGpos _).ne'
        rw [← Finset.mul_sum, hratio, mul_one]
  have hnorm_sub (u v : EuclideanSpace ℝ (Fin d)) :
      finite_lp_norm p (u - v) ≤ finite_lp_norm p u + finite_lp_norm p v := by
    simpa [finite_lp_norm] using
      (norm_sub_le (WithLp.toLp p (WithLp.ofLp u))
        (WithLp.toLp p (WithLp.ofLp v)))
  have hnorm_smul (c : ℝ) (u : EuclideanSpace ℝ (Fin d)) :
      finite_lp_norm p (c • u) = |c| * finite_lp_norm p u := by
    change ‖c • WithLp.toLp p (WithLp.ofLp u)‖ =
      |c| * ‖WithLp.toLp p (WithLp.ofLp u)‖
    simpa only [Real.norm_eq_abs] using
      (norm_smul c (WithLp.toLp p (WithLp.ofLp u)))
  have hg0bound : finite_lp_norm q g0 ≤ 2 * L * S := by
    obtain ⟨v, hvnorm, hvpair⟩ := hdual_exists g0
    by_contra hbound
    have hgt : 2 * L * S < finite_lp_norm q g0 := lt_of_not_ge hbound
    let e := (finite_lp_norm q g0 - 2 * L * S) / (2 * L)
    have he : 0 < e := div_pos (sub_pos.mpr hgt) (by positivity)
    have heq : 2 * L * e = finite_lp_norm q g0 - 2 * L * S := by
      dsimp [e]
      field_simp [hL.ne']
    have hstepnorm :
        finite_lp_norm p (s - e • v) ≤ S + e := by
      calc
        finite_lp_norm p (s - e • v) ≤
            finite_lp_norm p s + finite_lp_norm p (e • v) := hnorm_sub s (e • v)
        _ = S + e * finite_lp_norm p v := by
          rw [hnorm_smul, abs_of_pos he]
        _ ≤ S + e := by nlinarith
    have hstepnorm_nonneg : 0 ≤ finite_lp_norm p (s - e • v) := norm_nonneg _
    have hsum_nonneg : 0 ≤ S + e := by positivity
    have hstepsq :
        finite_lp_norm p (s - e • v) ^ 2 ≤ (S + e) ^ 2 := by
      nlinarith [sq_nonneg
        (finite_lp_norm p (s - e • v) - (S + e))]
    have hc := hmin (Set.mem_univ (run.y t + (s - e • v)))
    simp only [Set.mem_setOf_eq] at hc
    have hc' : inner ℝ g0 s + L * S ^ 2 ≤
        inner ℝ g0 (s - e • v) +
          L * finite_lp_norm p (s - e • v) ^ 2 := by
      simpa [s, S] using hc
    change inner ℝ g0 s + L * S ^ 2 ≤
      inner ℝ g0 (s - e • v) +
        L * finite_lp_norm p (s - e • v) ^ 2 at hc'
    simp only [inner_sub_right, inner_smul_right] at hc'
    rw [hinner, hvpair] at hc'
    nlinarith
  have hsmooth_step : finite_lp_norm q (g1 - g0) ≤ L * S := by
    simpa [l_smooth_with_respect_to_lp, s, g0, g1, S] using
      hsmooth (run.y t) (run.x (t + 1))
  have hnorm_add_q (u v : EuclideanSpace ℝ (Fin d)) :
      finite_lp_norm q (u + v) ≤ finite_lp_norm q u + finite_lp_norm q v := by
    simpa [finite_lp_norm] using
      (norm_add_le (WithLp.toLp q (WithLp.ofLp u))
        (WithLp.toLp q (WithLp.ofLp v)))
  have hg1bound : finite_lp_norm q g1 ≤ 3 * L * S := by
    calc
      finite_lp_norm q g1 =
          finite_lp_norm q ((g1 - g0) + g0) := by congr 2; abel
      _ ≤ finite_lp_norm q (g1 - g0) + finite_lp_norm q g0 :=
        hnorm_add_q (g1 - g0) g0
      _ ≤ L * S + 2 * L * S := add_le_add hsmooth_step hg0bound
      _ = 3 * L * S := by ring
  have hdiffinner : inner ℝ (g1 - g0) s ≤ L * S ^ 2 := by
    exact (hholder (g1 - g0) s).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hsmooth_step hSnonneg])
  have hfirst : inner ℝ g1 s ≤ -L * S ^ 2 := by
    have hdecomp : inner ℝ g1 s =
        inner ℝ g0 s + inner ℝ (g1 - g0) s := by
      calc
        inner ℝ g1 s = inner ℝ (g0 + (g1 - g0)) s := by
          congr 2
          abel
        _ = inner ℝ g0 s + inner ℝ (g1 - g0) s := inner_add_left _ _ _
    rw [hdecomp, hinner]
    linarith
  have hg1nonneg : 0 ≤ finite_lp_norm q g1 := norm_nonneg _
  have hthree_nonneg : 0 ≤ 3 * L * S := by positivity
  have hg1sq : finite_lp_norm q g1 ^ 2 ≤ (3 * L * S) ^ 2 := by
    nlinarith [sq_nonneg (finite_lp_norm q g1 - 3 * L * S)]
  constructor
  · have hyx : run.y t - run.x (t + 1) = -s := by simp [s]
    rw [hyx, inner_neg_right]
    linarith
  · calc
      (1 / (9 * L)) * finite_lp_norm q g1 ^ 2 ≤
          (1 / (9 * L)) * (3 * L * S) ^ 2 :=
        mul_le_mul_of_nonneg_left hg1sq (by positivity)
      _ = L * S ^ 2 := by field_simp [hL.ne']; ring

@[blueprint "lem:hasd-estimate-upper-bound"
  (statement := /-- Let $d,T\in\mathbb N$, let $L\in\mathbb R$ and $p,q\in[0,\infty]$, let $x_0\in\mathbb R^d$, and let $f:\mathbb R^d\to\mathbb R$ be convex and differentiable.  If the data form a HASD run for $f,L,p,q$ through time $T$, initialized at $x_0$, then, for every $t\in\mathbb N$ with $t\le T$ and every $z\in\mathbb R^d$,
  \[
    \psi_t(z)\le \frac12\lVert z-x_0\rVert_2^2+A_tf(z).
  \] -/)
  (proof := /-- We argue by induction on $t$.  At $t=0$, the initialization clauses in \cref{def:is-hasd-run} give $\psi_0(z)=\frac12\lVert z-x_0\rVert_2^2$ and $A_0=0$.  Suppose that $t+1\le T$.  Then $t<T$, and the update clauses in \cref{def:is-hasd-run} give $a_{t+1}>0$, $A_{t+1}=A_t+a_{t+1}$, and
  \[
    \psi_{t+1}(z)=\psi_t(z)+a_{t+1}\bigl(f(x_{t+1})+\langle\nabla f(x_{t+1}),z-x_{t+1}\rangle\bigr).
  \]
  By \cref{lem:convex-first-order-lower-bound}, the affine model in parentheses is at most $f(z)$.  Its multiplication by the positive number $a_{t+1}$ preserves this inequality.  Combining it with the induction hypothesis yields
  \[
    \psi_{t+1}(z)\le \frac12\lVert z-x_0\rVert_2^2+
      \bigl(A_t+a_{t+1}\bigr)f(z)
    =\frac12\lVert z-x_0\rVert_2^2+A_{t+1}f(z),
  \]
  as required. -/)
  (title := /-- Upper estimate-sequence bound -/)
  (latexEnv := "lemma")]
lemma hasd_estimate_upper_bound {d : ℕ} {run : hasd_data d}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} {p q : ENNReal}
    {T : ℕ} {x0 : EuclideanSpace ℝ (Fin d)}
    (hconv : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hrun : is_hasd_run run f L p q T x0) {t : ℕ} (ht : t ≤ T)
    (z : EuclideanSpace ℝ (Fin d)) :
    run.psi t z ≤ (1 / 2 : ℝ) * ‖z - x0‖ ^ 2 + run.A t * f z := by
  induction t with
  | zero =>
      simp [hrun.2.2.1 z, hrun.2.1]
  | succ t ih =>
      have htlt : t < T := Nat.lt_of_succ_le ht
      obtain ⟨ha, _, hA, _, _, _, _, _, hpsi⟩ := hrun.2.2.2.2 t htlt
      have hf :=
        convex_first_order_lower_bound f hconv hdiff (run.x (t + 1)) z
      rw [hpsi z, hA]
      have hi := ih (Nat.le_of_lt htlt)
      nlinarith

@[blueprint "lem:hasd-accumulated-weight-nonnegative"
  (statement := /-- If the data form a HASD run through time $T\in\mathbb N$, then $A_t\ge0$ for every $t\in\mathbb N$ with $t\le T$. -/)
  (proof := /-- We argue by induction on $t$ under the assumption $t\le T$.  For $t=0$, the initialization clause in \cref{def:is-hasd-run} gives $A_0=0$.  Suppose that $t+1\le T$.  Then $t<T$, so the update clauses in \cref{def:is-hasd-run} give $a_{t+1}>0$ and $A_{t+1}=A_t+a_{t+1}$.  Since $t\le T$, the induction hypothesis yields $A_t\ge0$; hence $A_{t+1}\ge0$. -/)
  (title := /-- Nonnegativity of accumulated HASD weights -/)
  (latexEnv := "lemma")]
lemma hasd_accumulated_weight_nonnegative {d : ℕ} {run : hasd_data d}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} {p q : ENNReal}
    {T : ℕ} {x0 : EuclideanSpace ℝ (Fin d)}
    (hrun : is_hasd_run run f L p q T x0) {t : ℕ} (ht : t ≤ T) :
    0 ≤ run.A t := by
  induction t with
  | zero =>
      exact hrun.2.1.symm ▸ le_refl 0
  | succ t ih =>
      have h := hrun.2.2.2.2 t (Nat.lt_of_succ_le ht)
      rw [h.2.2.1]
      exact add_nonneg (ih (Nat.le_of_lt (Nat.lt_of_succ_le ht))) (le_of_lt h.1)

@[blueprint "lem:hasd-accumulated-weight-positive"
  (statement := /-- Let $d,T,t\in\mathbb N$, let $f:\mathbb R^d\to\mathbb R$, let
  $L\in\mathbb R$, let $p,q\in[0,\infty]$, and let $x_0\in\mathbb R^d$.
  If the data form a HASD run for $f,L,p,q$ through time $T$, initialized at
  $x_0$, and $0<t\le T$, then $A_t>0$. -/)
  (proof := /-- Since $t>0$, write $t=s+1$.  The inequality $t\le T$ gives
  $s<T$, and \cref{lem:hasd-accumulated-weight-nonnegative} gives $A_s\ge0$.
  The update clauses in \cref{def:is-hasd-run} give
  $A_{s+1}=A_s+a_{s+1}$ and $a_{s+1}>0$.  Hence $A_t=A_s+a_{s+1}>0$. -/)
  (title := /-- Positivity of accumulated HASD weights -/)
  (latexEnv := "lemma")]
lemma hasd_accumulated_weight_positive {d : ℕ} {run : hasd_data d}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} {p q : ENNReal}
    {T : ℕ} {x0 : EuclideanSpace ℝ (Fin d)}
    (hrun : is_hasd_run run f L p q T x0) {t : ℕ}
    (ht0 : 0 < t) (htT : t ≤ T) : 0 < run.A t := by
  cases t with
  | zero => omega
  | succ s =>
      have hsT : s < T := Nat.lt_of_succ_le htT
      rw [(hrun.2.2.2.2 s hsT).2.2.1]
      exact add_pos_of_nonneg_of_pos
        (hasd_accumulated_weight_nonnegative hrun (Nat.le_of_lt hsT))
        (hrun.2.2.2.2 s hsT).1

@[blueprint "lem:hasd-recurrence-bonus-nonnegative"
  (statement := /-- Let $d,T\in\mathbb N$, let $f:\mathbb R^d\to\mathbb R$, let $L\in\mathbb R$, let $p,q\in[0,\infty]$, and let $x_0\in\mathbb R^d$.  If $L>0$ and the data form a HASD run for $f,L,p,q$ through time $T$, initialized at $x_0$, then $B_t\ge0$ for every $t\in\mathbb N$ with $t\le T$. -/)
  (proof := /-- By \cref{def:hasd-recurrence-bonus}, $B_t$ is $(18L)^{-1}$ times a sum indexed by the integers $i$ with $0\le i<t$.  For every such $i$, the inequality $i<t\le T$ permits the update clause in \cref{def:is-hasd-run} to be applied at time $i$, and that clause gives $a_{i+1}>0$.  Since $\lVert\nabla f(x_{i+1})\rVert_q^2\ge0$, every summand is nonnegative.  The finite sum is therefore nonnegative, and $L>0$ implies $(18L)^{-1}>0$.  Consequently $B_t\ge0$. -/)
  (title := /-- Nonnegativity of the recurrence bonus -/)
  (latexEnv := "lemma")]
lemma hasd_recurrence_bonus_nonnegative {d : ℕ} {run : hasd_data d}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} {p q : ENNReal}
    {T : ℕ} {x0 : EuclideanSpace ℝ (Fin d)} (hL : 0 < L)
    (hrun : is_hasd_run run f L p q T x0) {t : ℕ} (ht : t ≤ T) :
    0 ≤ hasd_recurrence_bonus run f L q t := by
  unfold hasd_recurrence_bonus
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (le_of_lt (hrun.2.2.2.2 i
      (lt_of_lt_of_le (Finset.mem_range.mp hi) ht)).1)
    (sq_nonneg _)

@[blueprint "lem:hasd-estimate-quadratic-form"
  (statement := /-- Let the data form a HASD run for $f,L,p,q$ through time $T$, initialized at $x_0$.  Then for every $t\in\mathbb N$ with $t\le T$ there exist $b\in\mathbb R^d$ and $c\in\mathbb R$ such that $\psi_t(z)=\frac12\lVert z\rVert_2^2+\langle b,z\rangle+c$ for all $z\in\mathbb R^d$. -/)
  (proof := /-- We induct on $t$.  For $t=0$, \cref{def:is-hasd-run} gives $\psi_0(z)=\frac12\lVert z-x_0\rVert_2^2$; expanding the square yields the claim with $b=-x_0$ and $c=\frac12\lVert x_0\rVert_2^2$.  For the induction step at $t<T$, the update clause of \cref{def:is-hasd-run} adds the affine function $z\mapsto a_{t+1}(f(x_{t+1})+\langle\nabla f(x_{t+1}),z-x_{t+1}\rangle)$ to $\psi_t$, so the quadratic part $\frac12\lVert z\rVert_2^2$ is preserved while $b$ and $c$ are shifted by an affine amount. -/)
  (title := /-- HASD estimate functions are quadratics -/)
  (latexEnv := "lemma")]
lemma hasd_estimate_quadratic_form {d : ℕ} {run : hasd_data d}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} {p q : ENNReal}
    {T : ℕ} {x0 : EuclideanSpace ℝ (Fin d)}
    (hrun : is_hasd_run run f L p q T x0) :
    ∀ t, t ≤ T → ∃ b : EuclideanSpace ℝ (Fin d), ∃ c : ℝ,
      ∀ z, run.psi t z = (1 / 2 : ℝ) * ‖z‖ ^ 2 + inner ℝ b z + c := by
  intro t
  induction t with
  | zero =>
      intro _
      refine ⟨-x0, (1 / 2 : ℝ) * ‖x0‖ ^ 2, ?_⟩
      intro z
      rw [hrun.2.2.1 z, norm_sub_sq_real, inner_neg_left, real_inner_comm x0 z]
      ring
  | succ t ih =>
      intro ht
      obtain ⟨b, c, hbc⟩ := ih (le_of_lt (Nat.lt_of_succ_le ht))
      obtain ⟨_, _, _, _, _, _, _, _, hpsi⟩ := hrun.2.2.2.2 t (Nat.lt_of_succ_le ht)
      refine ⟨b + run.a (t + 1) • gradient f (run.x (t + 1)),
        c + run.a (t + 1) * (f (run.x (t + 1)) -
          inner ℝ (gradient f (run.x (t + 1))) (run.x (t + 1))), ?_⟩
      intro z
      rw [hpsi z, hbc z, inner_add_left, real_inner_smul_left, inner_sub_right]
      ring

@[blueprint "lem:hasd-estimate-completing-square"
  (statement := /-- Let the data form a HASD run for $f,L,p,q$ through time $T$, initialized at $x_0$.  Then for every $t\in\mathbb N$ with $t\le T$ and every $z\in\mathbb R^d$, $\psi_t(z)=\psi_t(v_t)+\frac12\lVert z-v_t\rVert_2^2$. -/)
  (proof := /-- By \cref{lem:hasd-estimate-quadratic-form}, $\psi_t(z)=\frac12\lVert z\rVert_2^2+\langle b,z\rangle+c$ for some $b,c$.  Because $v_t$ minimizes $\psi_t$ over $\mathbb R^d$ by \cref{def:is-hasd-run}, evaluating this minimality at $z=-b$ gives $\frac12\lVert v_t+b\rVert_2^2\le0$, hence $b=-v_t$.  Substituting $b=-v_t$ into the quadratic form and expanding $\frac12\lVert z-v_t\rVert_2^2$ yields the completed-square identity. -/)
  (title := /-- Completed-square form of a HASD estimate function -/)
  (latexEnv := "lemma")]
lemma hasd_estimate_completing_square {d : ℕ} {run : hasd_data d}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} {p q : ENNReal}
    {T : ℕ} {x0 : EuclideanSpace ℝ (Fin d)}
    (hrun : is_hasd_run run f L p q T x0) {t : ℕ} (ht : t ≤ T) :
    ∀ z, run.psi t z
      = run.psi t (run.v t) + (1 / 2 : ℝ) * ‖z - run.v t‖ ^ 2 := by
  obtain ⟨b, c, hbc⟩ := hasd_estimate_quadratic_form hrun t ht
  have hmin : IsMinOn (run.psi t) Set.univ (run.v t) := hrun.2.2.2.1 t ht
  have hle := isMinOn_iff.mp hmin (-b) (Set.mem_univ _)
  rw [hbc (-b), hbc (run.v t), inner_neg_right, real_inner_self_eq_norm_sq,
    norm_neg] at hle
  have hsq : ‖run.v t + b‖ ^ 2 ≤ 0 := by
    rw [norm_add_sq_real]
    nlinarith [hle, real_inner_comm b (run.v t)]
  have hb0 : run.v t + b = 0 := by
    have h2 : ‖run.v t + b‖ ^ 2 = 0 := le_antisymm hsq (by positivity)
    have h3 : ‖run.v t + b‖ = 0 := (pow_eq_zero_iff (by norm_num)).mp h2
    exact norm_eq_zero.mp h3
  have hb : b = -run.v t := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hb0
  intro z
  rw [hbc z, hbc (run.v t), hb, inner_neg_left, inner_neg_left, norm_sub_sq_real,
    real_inner_self_eq_norm_sq, real_inner_comm (run.v t) z]
  ring

@[blueprint "lem:hasd-estimate-recurrence-lower-bound"
  (statement := /-- Let $d,T\in\mathbb N$, let $x_0\in\mathbb R^d$, and let $L\in\mathbb R$ satisfy $L>0$.  Let $p,q\in[0,\infty]$ be Hölder-conjugate exponents, with $p$ finite and $p\ge2$.  Suppose that $f:\mathbb R^d\to\mathbb R$ is convex and differentiable and satisfies
  \[
    \lVert\nabla f(y)-\nabla f(x)\rVert_q
      \le L\lVert y-x\rVert_p
      \qquad\text{for all }x,y\in\mathbb R^d.
  \]
  If the data form a HASD run through time $T$, initialized at $x_0$, then, for every $t\in\mathbb N$ with $t\le T$,
  \[
    A_tf(x_t)+B_t\le\psi_t(v_t).
  \] -/)
  (proof := /-- We argue by induction on $t$.  At $t=0$, the initialization in \cref{def:is-hasd-run} gives $A_0=0$ and $\psi_0(v_0)=\frac12\lVert v_0-x_0\rVert_2^2\ge0$, while \cref{def:hasd-recurrence-bonus} gives $B_0=0$.

  Assume the assertion at time $t<T$.  Write $a=a_{t+1}$, $A=A_t$, $A'=A_{t+1}$, $g=\nabla f(x_{t+1})$, and $B=B_t$.  By \cref{lem:hasd-accumulated-weight-nonnegative} we have $A\ge0$, and by \cref{lem:hasd-accumulated-weight-positive} we have $A'>0$.  By \cref{lem:hasd-estimate-completing-square}, applied at time $t$,
  \[
    \psi_t(z)=\psi_t(v_t)+\frac12\lVert z-v_t\rVert_2^2
    \qquad(z\in\mathbb R^d).
  \]
  The induction hypothesis and \cref{lem:convex-first-order-lower-bound} give
  \[
  f(x_{t+1})+\langle\nabla f(x_{t+1}),x_t-x_{t+1}\rangle\le f(x_t).
  \]
  Consequently, evaluating the update of $\psi$ from \cref{def:is-hasd-run} at $v_{t+1}$ and using the completed-square identity at time $t$ together with the affine-combination formula $A'y_t=Ax_t+av_t$ (which follows from the update formulas $A'=A+a$ and the definition of $y_t$), we obtain
  \[
  \psi_{t+1}(z)\ge A'f(x_{t+1})+B
    +\frac12\lVert z-v_t\rVert_2^2
    +a\langle g,z-v_t\rangle
    +A'\langle g,y_t-x_{t+1}\rangle.
  \]
  Completing the square in the free variable $z$ shows that the sum of the quadratic and the term with coefficient $a$ is at least $-\frac12a^2\lVert g\rVert_2^2$.  The weight identity in \cref{def:is-hasd-run} therefore identifies this penalty as
  \[
    -\frac{A+A'}{36L\rho_t}\lVert g\rVert_2^2.
  \]
  By \cref{lem:hasd-progress-bound}, the last inner product contributes at least $A'\lVert g\rVert_q^2/(9L)$.  The positivity of $\rho_t$ and its upper ratio bound in \cref{def:is-hasd-run} exclude $\lVert g\rVert_q=0$ and $\lVert g\rVert_2=0$.  We may therefore multiply the lower ratio bound
  $\rho_t\ge\frac12\lVert g\rVert_2^2/\lVert g\rVert_q^2$ by the positive denominators to obtain
  $\lVert g\rVert_2^2/\rho_t\le2\lVert g\rVert_q^2$.  Hence
  \[
  \begin{aligned}
    \psi_{t+1}(v_{t+1})
    &\ge A'f(x_{t+1})+B
      -\frac{A+A'}{18L}\lVert g\rVert_q^2
      +\frac{2A'}{18L}\lVert g\rVert_q^2\\
    &=A'f(x_{t+1})+B
      +\frac{A'-A}{18L}\lVert g\rVert_q^2\\
    &=A'f(x_{t+1})+B
      +\frac{a}{18L}\lVert g\rVert_q^2.
  \end{aligned}
  \]
  By \cref{def:hasd-recurrence-bonus}, the last two terms are $B_{t+1}$.  This proves the induction step and the assertion for every $t\le T$. -/)
  (title := /-- Lower estimate-sequence recurrence -/)
  (latexEnv := "lemma")]
lemma hasd_estimate_recurrence_lower_bound {d : ℕ} {run : hasd_data d}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} {p q : ENNReal}
    [hpq : ENNReal.HolderConjugate p q]
    {T : ℕ} {x0 : EuclideanSpace ℝ (Fin d)} (hp : (2 : ℝ) ≤ p.toReal)
    (hL : 0 < L)
    (hconv : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hsmooth : l_smooth_with_respect_to_lp p q L f)
    (hrun : is_hasd_run run f L p q T x0) {t : ℕ} (ht : t ≤ T) :
    run.A t * f (run.x t) + hasd_recurrence_bonus run f L q t ≤
      run.psi t (run.v t) := by
  letI : Fact (1 ≤ p) := ⟨hpq.one_le⟩
  letI : Fact (1 ≤ q) := ⟨hpq.symm.one_le⟩
  suffices h : ∀ s, s ≤ T →
      run.A s * f (run.x s) + hasd_recurrence_bonus run f L q s
        ≤ run.psi s (run.v s) by
    exact h t ht
  intro s
  induction s with
  | zero =>
      intro _
      have hA0 : run.A 0 = 0 := hrun.2.1
      have hB0 : hasd_recurrence_bonus run f L q 0 = 0 := by
        unfold hasd_recurrence_bonus
        simp
      have hpsi0 : run.psi 0 (run.v 0) = (1 / 2 : ℝ) * ‖run.v 0 - x0‖ ^ 2 :=
        hrun.2.2.1 (run.v 0)
      rw [hA0, hB0, hpsi0]
      have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) * ‖run.v 0 - x0‖ ^ 2 := by positivity
      linarith [hnn]
  | succ s ih =>
      intro hs
      have hsT : s < T := Nat.lt_of_succ_le hs
      have hIH := ih (le_of_lt hsT)
      have hAnn : 0 ≤ run.A s :=
        hasd_accumulated_weight_nonnegative hrun (le_of_lt hsT)
      have hA'pos : 0 < run.A (s + 1) :=
        hasd_accumulated_weight_positive hrun (Nat.succ_pos s) hs
      have hA'nn : 0 ≤ run.A (s + 1) := le_of_lt hA'pos
      have hLne : L ≠ 0 := ne_of_gt hL
      obtain ⟨ha, hrho, hA, hweight, hy, hxmin, hrholow, hrhohigh, hpsi⟩ :=
        hrun.2.2.2.2 s hsT
      have hconvb :=
        convex_first_order_lower_bound f hconv hdiff (run.x (s + 1)) (run.x s)
      have hprog := hasd_progress_bound hp hsmooth hrun hsT
      set g := gradient f (run.x (s + 1)) with hgdef
      set c18 := (1 / (18 * L)) * finite_lp_norm q g ^ 2 with hc18def
      have hQnn : 0 ≤ finite_lp_norm q g :=
        norm_nonneg (WithLp.toLp q (WithLp.ofLp g))
      have hQpos : 0 < finite_lp_norm q g := by
        by_contra hcon
        have hQ0 : finite_lp_norm q g = 0 := le_antisymm (not_lt.mp hcon) hQnn
        rw [hQ0] at hrhohigh
        rw [show ((0 : ℝ) ^ 2) = 0 by norm_num, div_zero, mul_zero] at hrhohigh
        linarith [hrho]
      have hQsq : 0 < finite_lp_norm q g ^ 2 := pow_pos hQpos 2
      have hNbound : ‖g‖ ^ 2 ≤ 2 * run.rho s * finite_lp_norm q g ^ 2 := by
        have h1 : ‖g‖ ^ 2 / finite_lp_norm q g ^ 2 ≤ 2 * run.rho s := by
          linarith [hrholow]
        exact (div_le_iff₀ hQsq).mp h1
      have hdenpos : 0 < 18 * L * run.rho s := by
        have h18 : (0 : ℝ) < 18 := by norm_num
        exact mul_pos (mul_pos h18 hL) hrho
      have hden_ne : (18 * L * run.rho s) ≠ 0 := ne_of_gt hdenpos
      have hw2 : run.a (s + 1) ^ 2 * (18 * L * run.rho s)
          = run.A s + run.A (s + 1) := by
        rw [hweight, div_mul_cancel₀ _ hden_ne]
      have hRHS : run.A s * c18 + run.A (s + 1) * c18
          = run.a (s + 1) ^ 2 * run.rho s * finite_lp_norm q g ^ 2 := by
        have hcomb : run.A s * c18 + run.A (s + 1) * c18
            = (run.A s + run.A (s + 1)) * c18 := by ring
        rw [hcomb, ← hw2, hc18def]
        field_simp
      have H6 : (1 / 2 : ℝ) * (run.a (s + 1) ^ 2 * ‖g‖ ^ 2)
          ≤ run.A s * c18 + run.A (s + 1) * c18 := by
        rw [hRHS]
        nlinarith [mul_le_mul_of_nonneg_left hNbound (sq_nonneg (run.a (s + 1)))]
      have hcompsq : -(1 / 2 : ℝ) * (run.a (s + 1) ^ 2 * ‖g‖ ^ 2)
          ≤ (1 / 2 : ℝ) * ‖run.v (s + 1) - run.v s‖ ^ 2
            + run.a (s + 1) * inner ℝ g (run.v (s + 1) - run.v s) := by
        have hpos : (0 : ℝ)
            ≤ ‖(run.v (s + 1) - run.v s) + run.a (s + 1) • g‖ ^ 2 := sq_nonneg _
        rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow,
            Real.norm_eq_abs, sq_abs, real_inner_comm] at hpos
        linarith [hpos]
      have hYrel : run.A (s + 1) * inner ℝ g (run.y s)
          = run.A s * inner ℝ g (run.x s)
            + run.a (s + 1) * inner ℝ g (run.v s) := by
        have hAa_pos : 0 < run.A s + run.a (s + 1) := by rw [← hA]; exact hA'pos
        have hAa_ne : run.A s + run.a (s + 1) ≠ 0 := ne_of_gt hAa_pos
        rw [hy, inner_add_right, real_inner_smul_right, real_inner_smul_right, hA]
        field_simp
        ring
      have H4 : run.A s * inner ℝ g (run.x s - run.x (s + 1))
            + run.a (s + 1) * inner ℝ g (run.v (s + 1) - run.x (s + 1))
          = run.A (s + 1) * inner ℝ g (run.y s - run.x (s + 1))
            + run.a (s + 1) * inner ℝ g (run.v (s + 1) - run.v s) := by
        simp only [inner_sub_right]
        linear_combination (-1 : ℝ) * hYrel + (inner ℝ g (run.x (s + 1))) * hA
      have H3 : run.A s * f (run.x (s + 1))
            + run.A s * inner ℝ g (run.x s - run.x (s + 1))
          ≤ run.A s * f (run.x s) := by
        have h := mul_le_mul_of_nonneg_left hconvb hAnn
        rw [mul_add] at h
        exact h
      have hc9 : (1 / (9 * L)) * finite_lp_norm q g ^ 2 = 2 * c18 := by
        rw [hc18def]; field_simp; ring
      have h2c18P3 : 2 * c18 ≤ inner ℝ g (run.y s - run.x (s + 1)) := by
        rw [← hc9]
        exact ge_trans hprog.1 hprog.2
      have H7 : 2 * (run.A (s + 1) * c18)
          ≤ run.A (s + 1) * inner ℝ g (run.y s - run.x (s + 1)) := by
        have h := mul_le_mul_of_nonneg_left h2c18P3 hA'nn
        have heq : run.A (s + 1) * (2 * c18) = 2 * (run.A (s + 1) * c18) := by ring
        linarith [h, heq]
      have H8 : run.A (s + 1) * f (run.x (s + 1))
          = run.A s * f (run.x (s + 1)) + run.a (s + 1) * f (run.x (s + 1)) := by
        rw [hA]; ring
      have H9 : run.A (s + 1) * c18
          = run.A s * c18 + run.a (s + 1) * c18 := by
        rw [hA]; ring
      have H10 : hasd_recurrence_bonus run f L q (s + 1)
          = hasd_recurrence_bonus run f L q s + run.a (s + 1) * c18 := by
        unfold hasd_recurrence_bonus
        rw [Finset.sum_range_succ, hc18def, hgdef]
        ring
      have H1 : run.psi (s + 1) (run.v (s + 1))
          = run.psi s (run.v s) + (1 / 2 : ℝ) * ‖run.v (s + 1) - run.v s‖ ^ 2
            + run.a (s + 1) * f (run.x (s + 1))
            + run.a (s + 1) * inner ℝ g (run.v (s + 1) - run.x (s + 1)) := by
        rw [hpsi (run.v (s + 1)),
          hasd_estimate_completing_square hrun (le_of_lt hsT) (run.v (s + 1))]
        ring
      linarith [H1, hIH, H3, H4, hcompsq, H6, H7, H8, H9, H10]

@[blueprint "lem:hasd-objective-gap-bound"
  (statement := /-- Let $p$ and $q$ be Hölder-conjugate exponents with $p\ge2$.  Let $x^*$ minimize the convex differentiable objective $f$, assume $L>0$, and let the data form a HASD run through a positive time $T$.  If $f$ is $L$-smooth with respect to $\lVert\cdot\rVert_p$, with dual norm $\lVert\cdot\rVert_q$, then
  \[
    f(x_T)-f(x^*)\le\frac{\lVert x_0-x^*\rVert_2^2}{2A_T}.
  \] -/)
  (proof := /-- Apply \cref{lem:hasd-estimate-recurrence-lower-bound} with the assumed convexity and differentiability of $f$.  Together with \cref{lem:hasd-recurrence-bonus-nonnegative}, this gives
  $A_Tf(x_T)\le\psi_T(v_T)$.  Since $v_T$ minimizes $\psi_T$, evaluation at $x^*$ gives $\psi_T(v_T)\le\psi_T(x^*)$.  By \cref{lem:hasd-estimate-upper-bound},
  $\psi_T(x^*)\le\frac12\lVert x^*-x_0\rVert_2^2+A_Tf(x^*)$.
  Finally, \cref{lem:hasd-accumulated-weight-positive} permits division by $A_T>0$, yielding the claim. -/)
  (title := /-- Objective gap in terms of the accumulated weight -/)
  (latexEnv := "lemma")]
lemma hasd_objective_gap_bound {d : ℕ} {run : hasd_data d}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} {p q : ENNReal}
    [hpq : ENNReal.HolderConjugate p q]
    {T : ℕ} {x0 xstar : EuclideanSpace ℝ (Fin d)}
    (hp : (2 : ℝ) ≤ p.toReal)
    (hL : 0 < L) (hT : 0 < T) (hconv : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f) (hsmooth : l_smooth_with_respect_to_lp p q L f)
    (hrun : is_hasd_run run f L p q T x0) (hmin : ∀ z, f xstar ≤ f z) :
    f (run.x T) - f xstar ≤ ‖x0 - xstar‖ ^ 2 / (2 * run.A T) := by
  have hAT_pos : 0 < run.A T :=
    hasd_accumulated_weight_positive hrun hT (le_refl T)
  have hlower :
      run.A T * f (run.x T) + hasd_recurrence_bonus run f L q T ≤
        run.psi T (run.v T) :=
    hasd_estimate_recurrence_lower_bound hp hL hconv hdiff hsmooth hrun
      (le_refl T)
  have hbonus : 0 ≤ hasd_recurrence_bonus run f L q T :=
    hasd_recurrence_bonus_nonnegative hL hrun (le_refl T)
  have hvmin : IsMinOn (run.psi T) Set.univ (run.v T) :=
    hrun.2.2.2.1 T (le_refl T)
  have hpsi_le : run.psi T (run.v T) ≤ run.psi T xstar :=
    (isMinOn_iff.mp hvmin) xstar (Set.mem_univ xstar)
  have hupper :
      run.psi T xstar ≤ (1 / 2 : ℝ) * ‖xstar - x0‖ ^ 2 + run.A T * f xstar :=
    hasd_estimate_upper_bound hconv hdiff hrun (le_refl T) xstar
  have hnorm : ‖xstar - x0‖ ^ 2 = ‖x0 - xstar‖ ^ 2 := by
    rw [norm_sub_rev]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hlower, hbonus, hpsi_le, hupper, hnorm]

@[blueprint "lem:hasd-growth-sum-bound"
  (statement := /-- Let $d,T\in\mathbb N$, let $f:\mathbb R^d\to\mathbb R$, let $L\in\mathbb R$ satisfy $L>0$, let $p,q\in[0,\infty]$, and let $x_0\in\mathbb R^d$.  If the data form a HASD run for $f,L,p,q$ through time $T$, initialized at $x_0$, then, for every $t\in\mathbb N$ with $t\le T$,
  \[
    \sqrt{A_t}\ge \frac1{18\sqrt L}\sum_{i=0}^{t-1}
       \frac{\lVert\nabla f(x_{i+1})\rVert_q}
            {\lVert\nabla f(x_{i+1})\rVert_2}.
  \] -/)
  (proof := /-- First, induction on $u\le T$, using $A_0=0$, the positivity of $a_{u+1}$, and the identity $A_{u+1}=A_u+a_{u+1}$ from \cref{def:is-hasd-run}, shows that $A_u\ge0$.

  We now prove the asserted inequality by induction on $t$.  The case $t=0$ follows from $A_0=0$.  For the induction step, write
  \[
    A=A_t,\quad B=A_{t+1},\quad a=a_{t+1},\quad
    \rho=\rho_t,\quad
    Q=\lVert\nabla f(x_{t+1})\rVert_q,\quad
    N=\lVert\nabla f(x_{t+1})\rVert_2.
  \]
  By \cref{def:is-hasd-run},
  \[
    B=A+a,\qquad
    a^2=\frac{A+B}{18L\rho},\qquad
    0<\rho\le 2\frac{N^2}{Q^2}.
  \]
  The last inequalities imply $Q\ne0$ and $N>0$.  Clearing the positive denominators gives
  \[
    A+B=18L\rho a^2
    \quad\text{and}\quad
    \rho Q^2\le2N^2.
  \]
  Since $A,B\ge0$, the square-root identities and
  $(\sqrt B-\sqrt A)^2\ge0$ yield
  \[
    (\sqrt B+\sqrt A)^2\le2(A+B).
  \]
  Consequently,
  \[
    \bigl(Q(\sqrt B+\sqrt A)\bigr)^2
      \le36L\rho Q^2a^2
      \le72LN^2a^2
      \le\bigl(18\sqrt L\,Na\bigr)^2.
  \]
  If the left-hand product is negative, its unsquared upper bound is immediate; otherwise, nonnegativity of both sides permits taking square roots.  Thus
  \[
    Q(\sqrt B+\sqrt A)\le18\sqrt L\,Na.
  \]
  Moreover,
  $(\sqrt B+\sqrt A)(\sqrt B-\sqrt A)=B-A=a$, and the first factor is positive.  Cancelling it and then dividing by $18\sqrt L\,N>0$ proves
  \[
    \sqrt{A_{t+1}}-\sqrt{A_t}\ge
      \frac1{18\sqrt L}\frac{Q}{N}.
  \]
  Adding this estimate to the induction hypothesis and expanding the sum over
  $\{0,\ldots,t\}$ completes the induction. -/)
  (title := /-- Growth of the accumulated HASD weight -/)
  (latexEnv := "lemma")]
lemma hasd_growth_sum_bound {d : ℕ} {run : hasd_data d}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} {p q : ENNReal}
    {T : ℕ} {x0 : EuclideanSpace ℝ (Fin d)} (hL : 0 < L)
    (hrun : is_hasd_run run f L p q T x0) {t : ℕ} (ht : t ≤ T) :
    Real.sqrt (run.A t) ≥
      (1 / (18 * Real.sqrt L)) * ∑ i ∈ Finset.range t,
        finite_lp_norm q (gradient f (run.x (i + 1))) /
          ‖gradient f (run.x (i + 1))‖ := by
  have hA_nonneg : ∀ u, u ≤ T → 0 ≤ run.A u := by
    intro u
    induction u with
    | zero =>
        intro hu
        rw [hrun.2.1]
    | succ u ih =>
        intro hu
        have huT : u < T := Nat.lt_of_succ_le hu
        obtain ⟨ha_pos, hrho_pos, hAstep, hweight, hy, hmin, hrho_lower,
          hrho_upper, hpsi⟩ := hrun.2.2.2.2 u huT
        have hprev : 0 ≤ run.A u := ih (Nat.le_trans (Nat.le_succ u) hu)
        linarith
  have hmain : ∀ u, u ≤ T →
      Real.sqrt (run.A u) ≥
        (1 / (18 * Real.sqrt L)) * ∑ i ∈ Finset.range u,
          finite_lp_norm q (gradient f (run.x (i + 1))) /
            ‖gradient f (run.x (i + 1))‖ := by
    intro u
    induction u with
    | zero =>
        intro hu
        simp [hrun.2.1]
    | succ u ih =>
        intro hu
        have huT : u < T := Nat.lt_of_succ_le hu
        have hu_le : u ≤ T := Nat.le_trans (Nat.le_succ u) hu
        obtain ⟨ha_pos, hrho_pos, hAstep, hweight, hy, hmin, hrho_lower,
          hrho_upper, hpsi⟩ := hrun.2.2.2.2 u huT
        have hA0 : 0 ≤ run.A u := hA_nonneg u hu_le
        have hA1 : 0 ≤ run.A (u + 1) := hA_nonneg (u + 1) hu
        have hA_lt : run.A u < run.A (u + 1) := by
          linarith
        have hsqrt0_sq : Real.sqrt (run.A u) ^ 2 = run.A u :=
          Real.sq_sqrt hA0
        have hsqrt1_sq : Real.sqrt (run.A (u + 1)) ^ 2 = run.A (u + 1) :=
          Real.sq_sqrt hA1
        have hn_nonneg :
            0 ≤ ‖gradient f (run.x (u + 1))‖ := norm_nonneg _
        have hq_ne :
            finite_lp_norm q (gradient f (run.x (u + 1))) ≠ 0 := by
          intro hq
          rw [hq] at hrho_upper
          norm_num at hrho_upper
          linarith
        have hn_ne : ‖gradient f (run.x (u + 1))‖ ≠ 0 := by
          intro hn
          rw [hn] at hrho_upper
          norm_num at hrho_upper
          linarith
        have hn_pos : 0 < ‖gradient f (run.x (u + 1))‖ :=
          lt_of_le_of_ne hn_nonneg (Ne.symm hn_ne)
        have hrho_mul :
            run.rho u * finite_lp_norm q (gradient f (run.x (u + 1))) ^ 2 ≤
              2 * ‖gradient f (run.x (u + 1))‖ ^ 2 := by
          calc
            run.rho u *
                  finite_lp_norm q (gradient f (run.x (u + 1))) ^ 2 ≤
                (2 * (‖gradient f (run.x (u + 1))‖ ^ 2 /
                  finite_lp_norm q (gradient f (run.x (u + 1))) ^ 2)) *
                    finite_lp_norm q (gradient f (run.x (u + 1))) ^ 2 :=
              mul_le_mul_of_nonneg_right hrho_upper
                (sq_nonneg (finite_lp_norm q (gradient f (run.x (u + 1)))))
            _ = 2 * ‖gradient f (run.x (u + 1))‖ ^ 2 := by
              field_simp
        have hweight_mul :
            run.A u + run.A (u + 1) =
              18 * L * run.rho u * run.a (u + 1) ^ 2 := by
          have hden : 18 * L * run.rho u ≠ 0 := by positivity
          have hm := (eq_div_iff hden).mp hweight
          nlinarith
        have hDsq :
            (Real.sqrt (run.A (u + 1)) + Real.sqrt (run.A u)) ^ 2 ≤
              2 * (run.A u + run.A (u + 1)) := by
          nlinarith [sq_nonneg
            (Real.sqrt (run.A (u + 1)) - Real.sqrt (run.A u))]
        have hQDsq :
            finite_lp_norm q (gradient f (run.x (u + 1))) ^ 2 *
                (Real.sqrt (run.A (u + 1)) + Real.sqrt (run.A u)) ^ 2 ≤
              36 * L * run.rho u *
                finite_lp_norm q (gradient f (run.x (u + 1))) ^ 2 *
                  run.a (u + 1) ^ 2 := by
          have hm := mul_le_mul_of_nonneg_left hDsq
            (sq_nonneg (finite_lp_norm q (gradient f (run.x (u + 1)))))
          rw [hweight_mul] at hm
          nlinarith
        have hscaled_rho :
            36 * L * run.a (u + 1) ^ 2 *
                (run.rho u *
                  finite_lp_norm q (gradient f (run.x (u + 1))) ^ 2) ≤
              36 * L * run.a (u + 1) ^ 2 *
                (2 * ‖gradient f (run.x (u + 1))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hrho_mul (by positivity)
        have hsqrtL_sq : Real.sqrt L ^ 2 = L := Real.sq_sqrt (le_of_lt hL)
        have hsquare_bound :
            (finite_lp_norm q (gradient f (run.x (u + 1))) *
                (Real.sqrt (run.A (u + 1)) + Real.sqrt (run.A u))) ^ 2 ≤
              (18 * Real.sqrt L * ‖gradient f (run.x (u + 1))‖ *
                run.a (u + 1)) ^ 2 := by
          nlinarith
        have hproduct_bound :
            finite_lp_norm q (gradient f (run.x (u + 1))) *
                (Real.sqrt (run.A (u + 1)) + Real.sqrt (run.A u)) ≤
              18 * Real.sqrt L * ‖gradient f (run.x (u + 1))‖ *
                run.a (u + 1) := by
          have hright : 0 ≤
              18 * Real.sqrt L * ‖gradient f (run.x (u + 1))‖ *
                run.a (u + 1) := by
            positivity
          by_cases hleft : 0 ≤
              finite_lp_norm q (gradient f (run.x (u + 1))) *
                (Real.sqrt (run.A (u + 1)) + Real.sqrt (run.A u))
          · nlinarith
          · exact le_trans (le_of_not_ge hleft) hright
        have hdiffmul :
            (Real.sqrt (run.A (u + 1)) + Real.sqrt (run.A u)) *
                (Real.sqrt (run.A (u + 1)) - Real.sqrt (run.A u)) =
              run.a (u + 1) := by
          nlinarith
        have hDpos :
            0 < Real.sqrt (run.A (u + 1)) + Real.sqrt (run.A u) := by
          have hA1_pos : 0 < run.A (u + 1) := by
            linarith
          have hsqrt1_pos : 0 < Real.sqrt (run.A (u + 1)) :=
            Real.sqrt_pos.2 hA1_pos
          positivity
        have hcancel :
            finite_lp_norm q (gradient f (run.x (u + 1))) ≤
              18 * Real.sqrt L * ‖gradient f (run.x (u + 1))‖ *
                (Real.sqrt (run.A (u + 1)) - Real.sqrt (run.A u)) := by
          apply le_of_mul_le_mul_right _ hDpos
          calc
            finite_lp_norm q (gradient f (run.x (u + 1))) *
                  (Real.sqrt (run.A (u + 1)) + Real.sqrt (run.A u)) ≤
                18 * Real.sqrt L * ‖gradient f (run.x (u + 1))‖ *
                  run.a (u + 1) := hproduct_bound
            _ = (18 * Real.sqrt L * ‖gradient f (run.x (u + 1))‖ *
                  (Real.sqrt (run.A (u + 1)) - Real.sqrt (run.A u))) *
                (Real.sqrt (run.A (u + 1)) + Real.sqrt (run.A u)) := by
              rw [← hdiffmul]
              ring
        have hone_step :
            finite_lp_norm q (gradient f (run.x (u + 1))) /
                  ‖gradient f (run.x (u + 1))‖ /
                (18 * Real.sqrt L) ≤
              Real.sqrt (run.A (u + 1)) - Real.sqrt (run.A u) := by
          apply (div_le_iff₀ (by positivity : 0 < 18 * Real.sqrt L)).2
          apply (div_le_iff₀ hn_pos).2
          nlinarith
        have ih_bound := ih hu_le
        rw [Finset.sum_range_succ]
        have hfactor :
            1 / (18 * Real.sqrt L) *
                (finite_lp_norm q (gradient f (run.x (u + 1))) /
                  ‖gradient f (run.x (u + 1))‖) =
              finite_lp_norm q (gradient f (run.x (u + 1))) /
                ‖gradient f (run.x (u + 1))‖ /
                  (18 * Real.sqrt L) := by
          ring
        rw [mul_add, hfactor]
        nlinarith
  exact hmain t ht

@[blueprint "lem:hasd-growth-average-bound"
  (statement := /-- Let $d,T\in\mathbb N$, let $f:\mathbb R^d\to\mathbb R$, let $L\in\mathbb R$ satisfy $L>0$, let $p,q\in[0,\infty]$, and let $x_0\in\mathbb R^d$.  If $T>0$ and the data form a HASD run for $f,L,p,q$ through time $T$, initialized at $x_0$, then
  \[
    \sqrt{A_T}\ge\frac{\mathcal G_TT}{18\sqrt L}.
  \] -/)
  (proof := /-- Apply \cref{lem:hasd-growth-sum-bound} with $t=T$.  By \cref{def:average-gradient-ratio} and the hypothesis $T>0$, multiplication by $T$ cancels the factor $1/T$, so the finite sum is $T\mathcal G_T$.  Reassociating the remaining real factors yields the asserted inequality. -/)
  (title := /-- Growth expressed through the average gradient ratio -/)
  (latexEnv := "lemma")]
lemma hasd_growth_average_bound {d : ℕ} {run : hasd_data d}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} {p q : ENNReal}
    {T : ℕ} {x0 : EuclideanSpace ℝ (Fin d)} (hL : 0 < L) (hT : 0 < T)
    (hrun : is_hasd_run run f L p q T x0) :
    Real.sqrt (run.A T) ≥
      average_gradient_ratio run f q T * (T : ℝ) / (18 * Real.sqrt L) := by
  rw [average_gradient_ratio]
  convert hasd_growth_sum_bound hL hrun (t := T) le_rfl using 1 <;>
    field_simp [Nat.ne_of_gt hT] <;>
    ring

@[blueprint "lem:average-gradient-ratio-positive"
  (statement := /-- Let $d,T\in\mathbb N$, let $p,q\in[0,\infty]$ be Hölder-conjugate exponents with $2\le p<\infty$, let $L\in\mathbb R$, let $f:\mathbb R^d\to\mathbb R$, and let $x_0\in\mathbb R^d$.  Suppose $T>0$ and a HASD data set is a valid run for $f,L,p,q$ through time $T$, initialized at $x_0$, in the sense of \cref{def:is-hasd-run}.  Then its average gradient ratio from \cref{def:average-gradient-ratio} satisfies
  \[
    \frac1T\sum_{t=0}^{T-1}
      \frac{\lVert\nabla f(x_{t+1})\rVert_q}
           {\lVert\nabla f(x_{t+1})\rVert_2}>0.
  \] -/)
  (proof := /-- Hölder conjugacy implies $1\le q$, so the finite $\ell_q$ norm in \cref{def:finite-lp-norm} is a genuine norm.  Fix $t<T$.  By \cref{def:is-hasd-run}, one has $\rho_t>0$ and
  \[
    \rho_t\le 2\frac{\lVert\nabla f(x_{t+1})\rVert_2^2}
                         {\lVert\nabla f(x_{t+1})\rVert_q^2}.
  \]
  If $\nabla f(x_{t+1})=0$, then Lean's total division makes the right-hand side zero, contradicting $\rho_t>0$.  Thus the gradient is nonzero, both norms in the quotient are strictly positive, and the quotient is strictly positive.  Since $T>0$, the summation range in \cref{def:average-gradient-ratio} is nonempty and $1/T>0$.  The finite sum, and hence the average gradient ratio, is therefore strictly positive. -/)
  (title := /-- Positivity of the average gradient ratio -/)
  (latexEnv := "lemma")]
lemma average_gradient_ratio_positive {d : ℕ} {run : hasd_data d}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} {p q : ENNReal}
    [hpq : ENNReal.HolderConjugate p q]
    {T : ℕ} {x0 : EuclideanSpace ℝ (Fin d)}
    (hp : (2 : ℝ) ≤ p.toReal) (hT : 0 < T)
    (hrun : is_hasd_run run f L p q T x0) :
    0 < average_gradient_ratio run f q T := by
  letI : Fact (1 ≤ q) := ⟨hpq.symm.one_le⟩
  unfold average_gradient_ratio
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  apply mul_pos (one_div_pos.mpr hTreal)
  apply Finset.sum_pos
  · intro t ht
    have htt : t < T := Finset.mem_range.mp ht
    rcases hrun.2.2.2.2 t htt with
      ⟨_, hrho, _, _, _, _, _, hupper, _⟩
    have hg_ne : gradient f (run.x (t + 1)) ≠ 0 := by
      intro hg
      have hrho_nonpos : run.rho t ≤ 0 := by
        simpa [hg, finite_lp_norm] using hupper
      linarith
    have hg2pos : 0 < ‖gradient f (run.x (t + 1))‖ :=
      norm_pos_iff.mpr hg_ne
    have hgqpos : 0 < finite_lp_norm q (gradient f (run.x (t + 1))) := by
      unfold finite_lp_norm
      exact norm_pos_iff.mpr (by simpa using hg_ne)
    exact div_pos hgqpos hg2pos
  · exact Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hT)

@[blueprint "lem:hasd-rate-from-weight-bounds"
  (statement := /-- Let $L,A,G,D,\delta\in\mathbb R$ and $T\in\mathbb N$.  Suppose $L,A,G,T$ are positive, $D\ge0$, $\delta\le D^2/(2A)$, and
  \[
    \sqrt A\ge\frac{GT}{18\sqrt L}.
  \]
  Then
  \[
    \delta\le\frac{324LD^2}{G^2T^2}.
  \] -/)
  (proof := /-- Since $L>0$, the quantity $18\sqrt L$ is positive, so the growth hypothesis gives
  $GT\le18\sqrt L\sqrt A$.  Both sides are nonnegative.  Monotonicity of squaring, together with $(\sqrt A)^2=A$ and $(\sqrt L)^2=L$, therefore yields
  $G^2T^2\le324LA$.  Multiplying by the nonnegative quantity $D^2$ gives
  $D^2G^2T^2\le324LAD^2\le648LAD^2$.  Because $2A>0$ and $G^2T^2>0$, cross-multiplication now shows
  $D^2/(2A)\le324LD^2/(G^2T^2)$.  The conclusion follows from the assumed bound on $\delta$. -/)
  (title := /-- Scalar assembly of the accelerated rate -/)
  (latexEnv := "lemma")]
lemma hasd_rate_from_weight_bounds {L A G D delta : ℝ} {T : ℕ}
    (hL : 0 < L) (hA : 0 < A) (hG : 0 < G) (hT : 0 < T) (hD : 0 ≤ D)
    (hgap : delta ≤ D ^ 2 / (2 * A))
    (hgrowth : Real.sqrt A ≥ G * (T : ℝ) / (18 * Real.sqrt L)) :
    delta ≤ 324 * L * D ^ 2 / (G ^ 2 * (T : ℝ) ^ 2) := by
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hsqrtL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hdenGrowth : 0 < 18 * Real.sqrt L := by positivity
  have hmul : G * (T : ℝ) ≤ Real.sqrt A * (18 * Real.sqrt L) :=
    (div_le_iff₀ hdenGrowth).mp hgrowth
  have hsqL : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt (le_of_lt hL)
  have hsqA : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt (le_of_lt hA)
  have hpoly : G ^ 2 * (T : ℝ) ^ 2 ≤ 324 * L * A := by
    have hsquared := mul_self_le_mul_self (le_of_lt (mul_pos hG hTreal)) hmul
    nlinarith
  calc
    delta ≤ D ^ 2 / (2 * A) := hgap
    _ ≤ 324 * L * D ^ 2 / (G ^ 2 * (T : ℝ) ^ 2) := by
      have hdenLeft : 0 < 2 * A := by positivity
      have hdenRight : 0 < G ^ 2 * (T : ℝ) ^ 2 := by positivity
      rw [div_le_div_iff₀ hdenLeft hdenRight]
      have hmulD := mul_le_mul_of_nonneg_left hpoly (sq_nonneg D)
      nlinarith

@[blueprint "thm:main"
  (statement := /-- Let $d,T\in\mathbb N$ with $T>0$, let $p,q\in[0,\infty]$ be Hölder-conjugate exponents with $p\ge2$, and let $L>0$.  Let $f:\mathbb R^d\to\mathbb R$ be differentiable, convex, and $L$-smooth with respect to $\lVert\cdot\rVert_p$.  Suppose $x^*$ is a global minimizer of $f$, and suppose HASD initialized at $x_0$, $A_0=0$, and $\psi_0(x)=\frac12\lVert x-x_0\rVert_2^2$ produces the run $(x_t)$ through time $T$.  With
  \[
    \mathcal G=\frac1T\sum_{t=0}^{T-1}
       \frac{\lVert\nabla f(x_{t+1})\rVert_q}
            {\lVert\nabla f(x_{t+1})\rVert_2},
  \]
  the output $x_T$ satisfies
  \[
    f(x_T)-f(x^*)\le
      \frac{324L\lVert x_0-x^*\rVert_2^2}{\mathcal G^2T^2}.
  \] -/)
  (proof := /-- By \cref{lem:hasd-objective-gap-bound}, the estimate-sequence argument gives
  \[
    f(x_T)-f(x^*)\le\frac{\lVert x_0-x^*\rVert_2^2}{2A_T}.
  \]
  By \cref{lem:hasd-growth-average-bound},
  $\sqrt{A_T}\ge\mathcal G T/(18\sqrt L)$.  The iteration hypotheses and \cref{lem:hasd-accumulated-weight-positive,lem:average-gradient-ratio-positive} give $A_T>0$ and $\mathcal G>0$, respectively.  Apply \cref{lem:hasd-rate-from-weight-bounds} with $D=\lVert x_0-x^*\rVert_2$ and $\delta=f(x_T)-f(x^*)$ to obtain the claimed inequality. -/)
  (title := /-- Faster acceleration for steepest descent -/)
  (latexEnv := "theorem")]
theorem main {d T : ℕ} (hT : 0 < T) {p q : ENNReal}
    [hpq : ENNReal.HolderConjugate p q] (hp : (2 : ℝ) ≤ p.toReal)
    {L : ℝ} (hL : 0 < L) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hconv : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hsmooth : l_smooth_with_respect_to_lp p q L f)
    (run : hasd_data d) (x0 xstar : EuclideanSpace ℝ (Fin d))
    (hrun : is_hasd_run run f L p q T x0) (hmin : ∀ z, f xstar ≤ f z) :
    f (run.x T) - f xstar ≤
      324 * L * ‖x0 - xstar‖ ^ 2 /
        (average_gradient_ratio run f q T ^ 2 * (T : ℝ) ^ 2) := by
  have hgap : f (run.x T) - f xstar ≤ ‖x0 - xstar‖ ^ 2 / (2 * run.A T) :=
    hasd_objective_gap_bound hp hL hT hconv hdiff hsmooth hrun hmin
  have hgrowth : Real.sqrt (run.A T) ≥
      average_gradient_ratio run f q T * (T : ℝ) / (18 * Real.sqrt L) :=
    hasd_growth_average_bound hL hT hrun
  have hA : 0 < run.A T := hasd_accumulated_weight_positive hrun hT (le_refl T)
  have hG : 0 < average_gradient_ratio run f q T :=
    average_gradient_ratio_positive hp hT hrun
  exact hasd_rate_from_weight_bounds hL hA hG hT (norm_nonneg _) hgap hgrowth

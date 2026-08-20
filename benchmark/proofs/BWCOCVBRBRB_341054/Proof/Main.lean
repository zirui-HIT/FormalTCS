import Architect
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Nat.Choose.Basic

set_option linter.all false
set_option maxHeartbeats 500000

variable {X : Type*} [MetricSpace X] {Y : Type*}

@[blueprint "def:is-gamma-cover"
  (statement := /-- Let $(\mathcal{X},\rho)$ be a metric space and let $\gamma > 0$. A finite set
  $Z \subseteq \mathcal{X}$ together with a map $\varphi : \mathcal{X} \to \mathcal{X}$ is a
  \emph{$\gamma$-cover with selection map} if for every $x \in \mathcal{X}$ one has both
  $\varphi(x) \in Z$ and $\varphi(x) \in B(x,\gamma)$, where $B(x,\gamma) = \{z \in \mathcal{X} :
  \rho(x,z) \le \gamma\}$ is the closed ball of radius $\gamma$ about $x$. In particular $Z$ is a
  $\gamma$-cover of $\mathcal{X}$ (every point of $\mathcal{X}$ has a point of $Z$ within distance
  $\gamma$), and $\varphi$ selects, for each $x$, a definite representative $\varphi(x) \in Z \cap
  B(x,\gamma)$, acting as a tie-breaker when several such representatives exist. -/)
  (title := /-- $\gamma$-cover with selection map -/)
  (latexEnv := "definition")]
def is_gamma_cover (γ : ℝ) (Z : Finset X) (φ : X → X) : Prop :=
  ∀ x : X, φ x ∈ Z ∧ φ x ∈ Metric.closedBall x γ

@[blueprint "def:perturbed-loss"
  (statement := /-- Fix a metric space $(\mathcal{X},\rho)$, a label space $\mathcal{Y}$ (in the
  paper $\mathcal{Y} = \{\pm 1\}$), and $\gamma > 0$. For a classifier $h : \mathcal{X} \to
  \mathcal{Y}$ and a labeled point $(x,y) \in \mathcal{X} \times \mathcal{Y}$, the
  \emph{$\gamma$-perturbed loss} is the worst-case indicator over the ball $B(x,\gamma)$,
  \[ \ell^{\gamma}_{\mathrm{pert}}(h,x,y) \;=\; \max_{z \in B(x,\gamma)} \mathbf{1}[h(z) \ne y]
  \;=\; \begin{cases} 0, & \text{if } h(z) = y \text{ for all } z \in B(x,\gamma),\\ 1, &
  \text{otherwise.}\end{cases} \]
  Equivalently, it equals $0$ precisely when $h$ is constant equal to $y$ on the closed ball
  $B(x,\gamma) = \{z : \rho(x,z) \le \gamma\}$, and $1$ otherwise. -/)
  (title := /-- $\gamma$-perturbed $0/1$ loss -/)
  (latexEnv := "definition")]
noncomputable def perturbed_loss (γ : ℝ) (h : X → Y) (x : X) (y : Y) : ℝ := by
  classical
  exact if ∀ z ∈ Metric.closedBall x γ, h z = y then 0 else 1

@[blueprint "def:perturbed-opt"
  (statement := /-- Fix $\gamma > 0$, a hypothesis class $\mathcal{H} \subseteq \mathcal{Y}^{
  \mathcal{X}}$, a horizon $T \in \mathbb{N}$, and a sequence of instances $x_1,\dots,x_T \in
  \mathcal{X}$ with labels $y_1,\dots,y_T \in \mathcal{Y}$. The \emph{relaxed benchmark under
  input perturbations} is
  \[ \mathsf{OPT}^{\gamma}_{\mathrm{pert}} \;=\; \inf_{h \in \mathcal{H}} \sum_{t=1}^{T}
  \ell^{\gamma}_{\mathrm{pert}}(h, x_t, y_t) \;=\; \inf_{h \in \mathcal{H}} \sum_{t=1}^{T}
  \max_{z \in B(x_t,\gamma)} \mathbf{1}[h(z) \ne y_t], \]
  the smallest cumulative error achievable by a fixed hypothesis of $\mathcal{H}$ against the
  worst-case perturbation of each input to distance at most $\gamma$, using the $\gamma$-perturbed
  loss of \cref{def:perturbed-loss}. -/)
  (title := /-- Relaxed benchmark $\mathsf{OPT}^{\gamma}_{\mathrm{pert}}$ -/)
  (latexEnv := "definition")]
noncomputable def perturbed_opt (γ : ℝ) (H : Set (X → Y)) (T : ℕ)
    (xs : Fin T → X) (ys : Fin T → Y) : ℝ :=
  ⨅ h ∈ H, ∑ t, perturbed_loss γ h (xs t) (ys t)

@[blueprint "def:projected-empirical-opt"
  (statement := /-- Fix a hypothesis class $\mathcal{H} \subseteq \mathcal{Y}^{\mathcal{X}}$, a
  selection map $\varphi : \mathcal{X} \to \mathcal{X}$, a horizon $T \in \mathbb{N}$, and a
  labeled sequence $(x_t, y_t)_{t=1}^{T}$. The \emph{projected empirical optimum} is
  \[ \widehat{\mathsf{OPT}}_{\mathcal{Z}} \;=\; \inf_{h \in \mathcal{H}} \sum_{t=1}^{T}
  \mathbf{1}[h(\varphi(x_t)) \ne y_t]. \]
  Since $h(\varphi(x))$ depends on $h$ only through its restriction $h|_{\mathcal{Z}}$ to the range
  of $\varphi$, this quantity coincides with $\min_{h \in \mathcal{H}|_{\mathcal{Z}}} \sum_{t=1}^{T}
  \mathbf{1}[h(\varphi(x_t)) \ne y_t]$, the empirical optimum of the projected class
  $\mathcal{H}|_{\mathcal{Z}}$ evaluated on the cover representatives $\varphi(x_t)$. -/)
  (title := /-- Projected empirical optimum $\widehat{\mathsf{OPT}}_{\mathcal{Z}}$ -/)
  (latexEnv := "definition")]
noncomputable def projected_empirical_opt (H : Set (X → Y)) (φ : X → X) (T : ℕ)
    (xs : Fin T → X) (ys : Fin T → Y) : ℝ := by
  classical
  exact ⨅ h ∈ H, ∑ t, if h (φ (xs t)) = ys t then (0 : ℝ) else 1

@[blueprint "lem:covering-property"
  (statement := /-- Let $(\mathcal{X},\rho)$ be a metric space, $\gamma > 0$, and let $(Z,\varphi)$
  be a $\gamma$-cover with selection map in the sense of \cref{def:is-gamma-cover}. Then for every
  classifier $h : \mathcal{X} \to \mathcal{Y}$, every instance $x \in \mathcal{X}$, and every label
  $y \in \mathcal{Y}$, if $h(z) = y$ for all $z \in B(x,\gamma)$, then $h(\varphi(x)) = y$. -/)
  (proof := /-- Fix $h$, $x$, and $y$, and assume $h(z) = y$ for every $z \in B(x,\gamma)$. By
  \cref{def:is-gamma-cover}, the selection map satisfies $\varphi(x) \in B(x,\gamma)$. Applying the
  hypothesis to $z = \varphi(x)$ yields $h(\varphi(x)) = y$. -/)
  (title := /-- Covering property of the selection map -/)
  (latexEnv := "lemma")]
lemma covering_property {γ : ℝ} {Z : Finset X} {φ : X → X}
    (hcover : is_gamma_cover γ Z φ) (h : X → Y) (x : X) (y : Y)
    (hagree : ∀ z ∈ Metric.closedBall x γ, h z = y) : h (φ x) = y := by
  exact hagree (φ x) (hcover x).2

@[blueprint "lem:cover-opt-bound"
  (statement := /-- Let $(\mathcal{X},\rho)$ be a metric space, $\gamma \in \mathbb{R}$, $(Z,\varphi)$ a
  $\gamma$-cover with selection map (\cref{def:is-gamma-cover}), $\mathcal{H} \subseteq
  \mathcal{Y}^{\mathcal{X}}$ a hypothesis class, and $(x_t,y_t)_{t=1}^{T}$ a labeled sequence. Then
  \[ \widehat{\mathsf{OPT}}_{\mathcal{Z}} \;\le\; \mathsf{OPT}^{\gamma}_{\mathrm{pert}}, \]
  i.e. the projected empirical optimum of \cref{def:projected-empirical-opt} is at most the relaxed
  benchmark of \cref{def:perturbed-opt}. -/)
  (proof := /-- Fix an arbitrary $h \in \mathcal{H}$. For each round $t$, if
  $\ell^{\gamma}_{\mathrm{pert}}(h,x_t,y_t) = 0$ then, by \cref{def:perturbed-loss}, $h(z) = y_t$
  for all $z \in B(x_t,\gamma)$; hence \cref{lem:covering-property} gives $h(\varphi(x_t)) = y_t$,
  so $\mathbf{1}[h(\varphi(x_t)) \ne y_t] = 0 = \ell^{\gamma}_{\mathrm{pert}}(h,x_t,y_t)$. If instead
  $\ell^{\gamma}_{\mathrm{pert}}(h,x_t,y_t) = 1$, then $\mathbf{1}[h(\varphi(x_t)) \ne y_t] \le 1 =
  \ell^{\gamma}_{\mathrm{pert}}(h,x_t,y_t)$. Summing over $t = 1,\dots,T$ yields
  $\sum_{t} \mathbf{1}[h(\varphi(x_t)) \ne y_t] \le \sum_{t} \ell^{\gamma}_{\mathrm{pert}}(h,x_t,y_t)$.
  Taking the infimum over $h \in \mathcal{H}$ on both sides, and using that the left-hand side is,
  by \cref{def:projected-empirical-opt}, at most its value for each fixed $h$, we obtain
  $\widehat{\mathsf{OPT}}_{\mathcal{Z}} \le \mathsf{OPT}^{\gamma}_{\mathrm{pert}}$ as in
  \cref{def:perturbed-opt}. -/)
  (title := /-- Projected optimum dominated by the relaxed benchmark -/)
  (latexEnv := "lemma")]
lemma cover_opt_bound {γ : ℝ} {Z : Finset X} {φ : X → X}
    (hcover : is_gamma_cover γ Z φ) (H : Set (X → Y)) (T : ℕ)
    (xs : Fin T → X) (ys : Fin T → Y) :
    projected_empirical_opt H φ T xs ys ≤ perturbed_opt γ H T xs ys := by
  classical
  unfold projected_empirical_opt perturbed_opt
  have hterm : ∀ h : X → Y,
      (∑ t, if h (φ (xs t)) = ys t then (0 : ℝ) else 1)
        ≤ ∑ t, perturbed_loss γ h (xs t) (ys t) := by
    intro h
    apply Finset.sum_le_sum
    intro t _
    unfold perturbed_loss
    by_cases hz : ∀ z ∈ Metric.closedBall (xs t) γ, h z = ys t
    · have hval : h (φ (xs t)) = ys t := covering_property hcover h (xs t) (ys t) hz
      rw [if_pos hval]
      split <;> norm_num
    · simp only [hz, if_false]
      split <;> norm_num
  have hsum_nonneg : ∀ h : X → Y,
      (0 : ℝ) ≤ ∑ t, if h (φ (xs t)) = ys t then (0 : ℝ) else 1 := by
    intro h
    apply Finset.sum_nonneg
    intro t _
    split <;> norm_num
  apply ciInf_mono
  · refine ⟨0, ?_⟩
    rintro x ⟨h, rfl⟩
    exact Real.iInf_nonneg (fun _ => hsum_nonneg h)
  · intro h
    apply ciInf_mono
    · exact ⟨0, by rintro x ⟨hh, rfl⟩; exact hsum_nonneg h⟩
    · intro _
      exact hterm h

@[blueprint "lem:sauer-shelah-sum-pow-bound"
  (statement := /-- Let $n, d \in \mathbb{N}$ with $0 < d \le n$. Then the partial sum of binomial
  coefficients is bounded by
  \[ \sum_{k=0}^{d} \binom{n}{k} \;\le\; \left(\frac{e\, n}{d}\right)^{d}. \] -/)
  (proof := /-- Write $t = d/n$, so that $0 < t \le 1$. For every index $k$ in the sum we have
  $k \le d$, and since $0 < t \le 1$ this gives $t^{d} \le t^{k}$. Multiplying the sum by the
  nonnegative factor $t^{d}$ and using $\binom{n}{k} \ge 0$ therefore yields
  \[ \left(\sum_{k=0}^{d}\binom{n}{k}\right) t^{d} = \sum_{k=0}^{d}\binom{n}{k}\,t^{d}
  \le \sum_{k=0}^{d}\binom{n}{k}\,t^{k} \le \sum_{k=0}^{n}\binom{n}{k}\,t^{k} = (1+t)^{n}, \]
  where the middle inequality adds the nonnegative terms with $k = d+1,\dots,n$ and the last
  equality is the binomial theorem. From $1 + t \le e^{t}$ and $n\,t = d$ we obtain $(1+t)^{n} \le
  (e^{t})^{n} = e^{n t} = e^{d}$, hence $\left(\sum_{k=0}^{d}\binom{n}{k}\right) t^{d} \le e^{d}$.
  Since $\left(\frac{e\,n}{d}\right)^{d} t^{d} = \big(\tfrac{e\,n}{d}\cdot\tfrac{d}{n}\big)^{d} =
  e^{d}$ and $t^{d} > 0$, cancelling the factor $t^{d}$ gives $\sum_{k=0}^{d}\binom{n}{k} \le
  \left(\frac{e\,n}{d}\right)^{d}$. -/)
  (title := /-- Binomial partial-sum bound $\sum_{k\le d}\binom{n}{k}\le (en/d)^d$ -/)
  (latexEnv := "lemma")]
lemma sauer_shelah_sum_pow_bound (n d : ℕ) (hd : 0 < d) (hdn : d ≤ n) :
    (∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ))
      ≤ (Real.exp 1 * (n : ℝ) / (d : ℝ)) ^ d := by
  have hn : 0 < n := hd.trans_le hdn
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hd' : (d : ℝ) ≠ 0 := ne_of_gt hd0
  have hn' : (n : ℝ) ≠ 0 := ne_of_gt hn0
  set t : ℝ := (d : ℝ) / (n : ℝ) with ht_def
  have ht0 : 0 < t := by rw [ht_def]; exact div_pos hd0 hn0
  have ht1 : t ≤ 1 := by
    rw [ht_def, div_le_one hn0]; exact_mod_cast hdn
  have hnt : (n : ℝ) * t = (d : ℝ) := by
    rw [ht_def]; field_simp
  have hclaim4 : (t + 1) ^ n ≤ Real.exp (d : ℝ) := by
    have h1 : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
    have h2 : (t + 1) ^ n ≤ (Real.exp t) ^ n :=
      pow_le_pow_left₀ (by linarith) h1 n
    have h3 : (Real.exp t) ^ n = Real.exp (d : ℝ) := by
      rw [← Real.exp_nat_mul, hnt]
    exact h2.trans_eq h3
  have hS : (∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ)) * t ^ d ≤ Real.exp (d : ℝ) := by
    calc (∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ)) * t ^ d
        = ∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ) * t ^ d := by rw [Finset.sum_mul]
      _ ≤ ∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ) * t ^ k := by
            apply Finset.sum_le_sum
            intro k hk
            have hkd : k ≤ d := by have := Finset.mem_range.mp hk; omega
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_of_le_one ht0.le ht1 hkd) (by positivity)
      _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * t ^ k := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              rw [Finset.mem_range] at hx ⊢
              omega
            · intro k _ _; exact mul_nonneg (by positivity) (pow_nonneg ht0.le k)
      _ = (t + 1) ^ n := by
            rw [add_pow]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [one_pow, mul_one]; ring
      _ ≤ Real.exp (d : ℝ) := hclaim4
  have hkey : (Real.exp 1 * (n : ℝ) / (d : ℝ)) ^ d * t ^ d = Real.exp (d : ℝ) := by
    rw [← mul_pow]
    have hmul : Real.exp 1 * (n : ℝ) / (d : ℝ) * t = Real.exp 1 := by
      rw [ht_def]; field_simp
    rw [hmul, ← Real.exp_nat_mul, mul_one]
  have htdpos : 0 < t ^ d := pow_pos ht0 d
  have hcombined : (∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ)) * t ^ d
      ≤ (Real.exp 1 * (n : ℝ) / (d : ℝ)) ^ d * t ^ d := by
    rw [hkey]; exact hS
  exact le_of_mul_le_mul_right hcombined htdpos

@[blueprint "lem:sauer-shelah-cover-bound"
  (statement := /-- Let $n, d, m \in \mathbb{N}$ with $0 < d \le n$, and suppose that
  $m \le \sum_{k=0}^{d} \binom{n}{k}$. Then
  \[ \ln m \;\le\; d \, \ln\!\left(\frac{e\, n}{d}\right). \]
  In the application, $n = |Z| = |\mathsf{C}(\mathcal{X},\rho,\gamma)|$ is the size of the
  $\gamma$-cover, $d = \mathsf{vc}(\mathcal{H})$ is the VC dimension of $\mathcal{H}$, and $m =
  |\mathcal{H}|_{\mathcal{Z}}|$ is the cardinality of the projected class; the hypothesis
  $m \le \sum_{k=0}^{d} \binom{n}{k}$ is the Sauer--Shelah--Perles bound applied to
  $\mathcal{H}|_{\mathcal{Z}}$, whose VC dimension is at most $\mathsf{vc}(\mathcal{H}) = d$. -/)
  (proof := /-- By the Sauer--Shelah--Perles growth-function estimate assumed in the hypothesis,
  $m \le \sum_{k=0}^{d} \binom{n}{k}$. Since $0 < d \le n$, the elementary binomial estimate gives
  $\sum_{k=0}^{d} \binom{n}{k} \le \left(\frac{e\,n}{d}\right)^{d}$ by
  \cref{lem:sauer-shelah-sum-pow-bound}. Chaining these two inequalities gives $m \le
  \left(\frac{e\,n}{d}\right)^{d}$ as an inequality of nonnegative reals. If $m = 0$ then $\ln m =
  0$, while $\frac{e\,n}{d} \ge 1$ forces $\ln\!\left(\frac{e\,n}{d}\right) \ge 0$ and hence
  $d\,\ln\!\left(\frac{e\,n}{d}\right) \ge 0$, so the bound holds. Otherwise $m \ge 1$, so both
  sides of $m \le \left(\frac{e\,n}{d}\right)^{d}$ are positive; applying the monotone logarithm
  and using $\ln\!\left(x^{d}\right) = d\,\ln x$ yields $\ln m \le d\,\ln\!\left(\frac{e\,n}{d}
  \right)$. -/)
  (title := /-- Logarithmic Sauer--Shelah bound for the projected class -/)
  (latexEnv := "lemma")]
lemma sauer_shelah_cover_bound (n d m : ℕ) (hd : 0 < d) (hdn : d ≤ n)
    (hcount : m ≤ ∑ k ∈ Finset.range (d + 1), n.choose k) :
    Real.log (m : ℝ) ≤ (d : ℝ) * Real.log (Real.exp 1 * (n : ℝ) / (d : ℝ)) := by
  have hn : 0 < n := hd.trans_le hdn
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set B : ℝ := Real.exp 1 * (n : ℝ) / (d : ℝ) with hB_def
  have hB1 : 1 ≤ B := by
    rw [hB_def, le_div_iff₀ hd0, one_mul]
    have he : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
    calc (d : ℝ) ≤ (n : ℝ) := he
      _ = 1 * (n : ℝ) := by ring
      _ ≤ Real.exp 1 * (n : ℝ) :=
          mul_le_mul_of_nonneg_right (Real.one_le_exp (by norm_num)) hn0.le
  have hB0 : 0 < B := lt_of_lt_of_le one_pos hB1
  have hmcount : (m : ℝ) ≤ (∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ)) := by
    have := hcount
    have hcast : (m : ℝ) ≤ ((∑ k ∈ Finset.range (d + 1), n.choose k : ℕ) : ℝ) := by
      exact_mod_cast this
    rw [Nat.cast_sum] at hcast
    exact hcast
  have hsum : (∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ)) ≤ B ^ d :=
    sauer_shelah_sum_pow_bound n d hd hdn
  have hmB : (m : ℝ) ≤ B ^ d := hmcount.trans hsum
  have hlogB : Real.log (B ^ d) = (d : ℝ) * Real.log B := by
    rw [Real.log_pow]
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    simp only [Nat.cast_zero, Real.log_zero]
    have hlogBnn : 0 ≤ Real.log B := Real.log_nonneg hB1
    positivity
  · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
    have hlog : Real.log (m : ℝ) ≤ Real.log (B ^ d) :=
      Real.log_le_log (by linarith) hmB
    rw [hlogB] at hlog
    exact hlog

@[blueprint "lem:eta-optimization"
  (statement := /-- Let $T \in \mathbb{N}$ and let $\mathrm{opt}, L, M \in \mathbb{R}$ satisfy
  $0 \le \mathrm{opt} \le T$ and $0 \le L$. Suppose that for every step size $\eta > 0$,
  \[ M \;\le\; \frac{\eta}{1 - e^{-\eta}}\,\mathrm{opt} \;+\; \frac{1}{1 - e^{-\eta}}\,L. \]
  Then
  \[ M - \mathrm{opt} \;\le\; \sqrt{2\,\mathrm{opt}\,L} \;+\; L. \] -/)
  (proof := /-- If $\mathrm{opt} = 0$, the hypothesis gives $M \le \frac{1}{1 - e^{-\eta}}\,L$ for
  every $\eta > 0$; since $\frac{1}{1 - e^{-\eta}} \downarrow 1$ as $\eta \to \infty$ and $L \ge 0$,
  passing to the limit yields $M \le L = \sqrt{2 \cdot 0 \cdot L} + L$. If $L = 0$, the hypothesis
  gives $M \le \frac{\eta}{1 - e^{-\eta}}\,\mathrm{opt}$ for every $\eta > 0$; since
  $\frac{\eta}{1 - e^{-\eta}} \downarrow 1$ as $\eta \to 0^{+}$ and $\mathrm{opt} \ge 0$, passing to
  the limit gives $M \le \mathrm{opt}$, i.e. $M - \mathrm{opt} \le 0 = \sqrt{2\,\mathrm{opt}\cdot 0}
  + 0$.

  Now assume $\mathrm{opt} > 0$ and $L > 0$, and set $u \doteq \sqrt{2L/\mathrm{opt}} > 0$ and
  $\eta \doteq \ln(1 + u) > 0$. Then $e^{-\eta} = (1 + u)^{-1}$, hence $1 - e^{-\eta} =
  \frac{u}{1 + u}$. By the elementary inequality $(1 + u)\ln(1 + u) \le u + \tfrac{u^{2}}{2}$, valid
  for all $u \ge 0$, we obtain
  \[ \frac{\eta}{1 - e^{-\eta}} = \frac{(1 + u)\ln(1 + u)}{u} \le \frac{u + u^{2}/2}{u} = 1 +
  \frac{u}{2}, \qquad \frac{1}{1 - e^{-\eta}} = \frac{1 + u}{u} = 1 + \frac{1}{u}. \]
  Substituting these two bounds into the hypothesis at this $\eta$ and using $\mathrm{opt}, L \ge 0$,
  \[ M \le \Big(1 + \tfrac{u}{2}\Big)\mathrm{opt} + \Big(1 + \tfrac{1}{u}\Big)L = \mathrm{opt} + L +
  \Big(\tfrac{u\,\mathrm{opt}}{2} + \tfrac{L}{u}\Big). \]
  Since $u = \sqrt{2L/\mathrm{opt}}$, both $\tfrac{u\,\mathrm{opt}}{2}$ and $\tfrac{L}{u}$ equal
  $\tfrac{1}{2}\sqrt{2\,\mathrm{opt}\,L}$, so their sum is $\sqrt{2\,\mathrm{opt}\,L}$. Therefore
  $M \le \mathrm{opt} + L + \sqrt{2\,\mathrm{opt}\,L}$, that is, $M - \mathrm{opt} \le
  \sqrt{2\,\mathrm{opt}\,L} + L$. -/)
  (title := /-- Step-size tuning of the multiplicative-weights bound -/)
  (latexEnv := "lemma")]
lemma eta_optimization (T : ℕ) (opt L M : ℝ) (hopt0 : 0 ≤ opt) (hoptT : opt ≤ (T : ℝ))
    (hL0 : 0 ≤ L)
    (hreg : ∀ η : ℝ, 0 < η →
      M ≤ (η / (1 - Real.exp (-η))) * opt + (1 / (1 - Real.exp (-η))) * L) :
    M - opt ≤ Real.sqrt (2 * opt * L) + L := by
  have key : ∀ u : ℝ, 0 ≤ u → (1 + u) * Real.log (1 + u) ≤ u + u ^ 2 / 2 := by
    intro u hu
    have h1u : (0 : ℝ) < 1 + u := by linarith
    have hs0 : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
    have hes : Real.exp (Real.log (1 + u)) = 1 + u := Real.exp_log h1u
    have hq := Real.quadratic_le_exp_of_nonneg hs0
    have hab : Real.exp (Real.log (1 + u)) * Real.exp (-Real.log (1 + u)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hbpos := Real.exp_pos (-Real.log (1 + u))
    have hapos := Real.exp_pos (Real.log (1 + u))
    have hL1 : 2 * Real.log (1 + u)
        ≤ Real.exp (Real.log (1 + u)) - Real.exp (-Real.log (1 + u)) := by
      nlinarith [hq, hab, hbpos, hapos, mul_nonneg (sub_nonneg.2 hq) hbpos.le]
    have hmul := mul_le_mul_of_nonneg_right hL1 h1u.le
    rw [hes] at hmul
    nlinarith [hmul, hab, hes]
  have hmain : ∀ u : ℝ, 0 < u → M ≤ opt + L + (u * opt / 2 + L / u) := by
    intro u hu
    have h1u : (0 : ℝ) < 1 + u := by linarith
    have hηpos : 0 < Real.log (1 + u) := Real.log_pos (by linarith)
    have hes : Real.exp (Real.log (1 + u)) = 1 + u := Real.exp_log h1u
    have hden : 1 - Real.exp (-Real.log (1 + u)) = u / (1 + u) := by
      rw [Real.exp_neg, hes]
      field_simp
      ring
    have hkey := key u hu.le
    have hreg' := hreg (Real.log (1 + u)) hηpos
    rw [hden] at hreg'
    have hclear : M * u ≤ Real.log (1 + u) * (1 + u) * opt + (1 + u) * L := by
      have e1 : Real.log (1 + u) / (u / (1 + u)) * opt + 1 / (u / (1 + u)) * L
          = (Real.log (1 + u) * (1 + u) * opt + (1 + u) * L) / u := by
        field_simp
      rw [e1] at hreg'
      exact (le_div_iff₀ hu).mp hreg'
    have hb2 : Real.log (1 + u) * (1 + u) * opt ≤ (u + u ^ 2 / 2) * opt :=
      mul_le_mul_of_nonneg_right (by nlinarith [hkey]) hopt0
    rw [show opt + L + (u * opt / 2 + L / u)
          = (opt * u + L * u + u ^ 2 * opt / 2 + L) / u by field_simp; ring,
       le_div_iff₀ hu]
    nlinarith [hclear, hb2]
  rcases eq_or_lt_of_le hL0 with rfl | hLpos
  · rcases eq_or_lt_of_le hopt0 with rfl | hoptpos
    · have h := hmain 1 one_pos
      norm_num at h ⊢
      linarith
    · simp only [mul_zero, Real.sqrt_zero, add_zero]
      rw [sub_nonpos]
      apply le_of_forall_pos_le_add
      intro ε hε
      have hu : (0 : ℝ) < 2 * ε / (opt + 1) := by positivity
      have h := hmain _ hu
      have hb : 2 * ε / (opt + 1) * opt / 2 + (0 : ℝ) / (2 * ε / (opt + 1)) ≤ ε := by
        rw [zero_div, add_zero, div_le_iff₀ (by norm_num : (0 : ℝ) < 2),
          div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < opt + 1)]
        nlinarith [hε, hoptpos]
      simp only [add_zero] at h
      linarith [h, hb]
  · rcases eq_or_lt_of_le hopt0 with rfl | hoptpos
    · simp only [mul_zero, zero_mul, Real.sqrt_zero, zero_add, sub_zero]
      apply le_of_forall_pos_le_add
      intro ε hε
      have hu : (0 : ℝ) < L / ε := by positivity
      have h := hmain _ hu
      have hb : L / ε * 0 / 2 + L / (L / ε) = ε := by
        rw [mul_zero, zero_div, zero_add, div_div_eq_mul_div, mul_comm, mul_div_assoc,
          div_self (ne_of_gt hLpos), mul_one]
      linarith [h, hb]
    · have hu : (0 : ℝ) < Real.sqrt (2 * L / opt) := Real.sqrt_pos.2 (by positivity)
      have h := hmain _ hu
      have hu2 : Real.sqrt (2 * L / opt) ^ 2 = 2 * L / opt := Real.sq_sqrt (by positivity)
      have hterm : L / Real.sqrt (2 * L / opt) = Real.sqrt (2 * L / opt) * opt / 2 := by
        rw [div_eq_iff (ne_of_gt hu)]
        have hxx : Real.sqrt (2 * L / opt) * opt / 2 * Real.sqrt (2 * L / opt)
            = Real.sqrt (2 * L / opt) ^ 2 * opt / 2 := by ring
        rw [hxx, hu2]
        field_simp
      have huopt : Real.sqrt (2 * L / opt) * opt = Real.sqrt (2 * opt * L) := by
        have h1 : 0 ≤ Real.sqrt (2 * L / opt) * opt := by positivity
        rw [← Real.sqrt_sq h1, mul_pow, hu2]
        congr 1
        field_simp
      have hsum : Real.sqrt (2 * L / opt) * opt / 2 + L / Real.sqrt (2 * L / opt)
          = Real.sqrt (2 * opt * L) := by
        rw [hterm, ← huopt]; ring
      rw [hsum] at h
      linarith [h]

@[blueprint "thm:input-margin-upperbnd"
  (statement := /-- Let $(\mathcal{X},\rho)$ be a metric space and let $\gamma > 0$. Let $Z$ be a
  finite $\gamma$-cover of $\mathcal{X}$ with selection map $\varphi$ in the sense of
  \cref{def:is-gamma-cover}, and let $\mathcal{H} \subseteq \mathcal{Y}^{\mathcal{X}}$ be a
  hypothesis class of $\{\pm 1\}$-valued classifiers. Fix a horizon $T \in \mathbb{N}$ and an
  arbitrary labeled sequence $(x_1,y_1),\dots,(x_T,y_T)$ with $x_t \in \mathcal{X}$ and $y_t \in
  \mathcal{Y}$. Let $d \in \mathbb{N}$ with $0 < d \le |Z|$ be the VC dimension $\mathsf{vc}(
  \mathcal{H})$, and let $m \in \mathbb{N}$ be the cardinality $|\mathcal{H}|_{\mathcal{Z}}|$ of the
  projected class, which by Sauer--Shelah--Perles satisfies $m \le \sum_{k=0}^{d}\binom{|Z|}{k}$.
  Let $E$ denote the expected number of mistakes $\sum_{t=1}^{T}\mathbb{E}\,\mathbf{1}[\hat{y}_t \ne
  y_t]$ produced by \textup{Algorithm (input-margin)}, and assume the multiplicative-weights regret
  guarantee: for every step size $\eta > 0$,
  \[ E \;\le\; \frac{\eta}{1 - e^{-\eta}}\,\widehat{\mathsf{OPT}}_{\mathcal{Z}} \;+\;
  \frac{1}{1 - e^{-\eta}}\,\ln m, \]
  with $\widehat{\mathsf{OPT}}_{\mathcal{Z}}$ as in \cref{def:projected-empirical-opt}. Then
  \[ E - \mathsf{OPT}^{\gamma}_{\mathrm{pert}} \;\le\; \sqrt{2\,T \cdot \mathsf{vc}(\mathcal{H})\,\ln
  \!\left(\frac{e\,|\mathsf{C}(\mathcal{X},\rho,\gamma)|}{\mathsf{vc}(\mathcal{H})}\right)} \;+\;
  \mathsf{vc}(\mathcal{H})\,\ln\!\left(\frac{e\,|\mathsf{C}(\mathcal{X},\rho,\gamma)|}{\mathsf{vc}(
  \mathcal{H})}\right), \]
  where $\mathsf{OPT}^{\gamma}_{\mathrm{pert}}$ is the relaxed benchmark of
  \cref{def:perturbed-opt} and $|\mathsf{C}(\mathcal{X},\rho,\gamma)| = |Z|$. -/)
  (proof := /-- By \cref{lem:cover-opt-bound}, the projected empirical optimum is dominated by the
  relaxed benchmark: $\widehat{\mathsf{OPT}}_{\mathcal{Z}} \le \mathsf{OPT}^{\gamma}_{\mathrm{pert}}$.
  By \cref{lem:sauer-shelah-cover-bound} applied with $n = |Z|$, the projected class cardinality
  satisfies $\ln m \le d\,\ln\!\left(\frac{e\,|Z|}{d}\right)$. Substituting these two inequalities
  into the multiplicative-weights regret guarantee (whose coefficients $\frac{\eta}{1-e^{-\eta}}$
  and $\frac{1}{1-e^{-\eta}}$ are nonnegative for $\eta > 0$) shows that for every $\eta > 0$,
  \[ E \;\le\; \frac{\eta}{1-e^{-\eta}}\,\mathsf{OPT}^{\gamma}_{\mathrm{pert}} +
  \frac{1}{1-e^{-\eta}}\,\Big(d\,\ln\tfrac{e\,|Z|}{d}\Big). \]
  Finally, $\mathsf{OPT}^{\gamma}_{\mathrm{pert}} \ge 0$ and $\mathsf{OPT}^{\gamma}_{\mathrm{pert}}
  \le T$ (each round contributes a loss in $\{0,1\}$), and $d\,\ln\tfrac{e\,|Z|}{d} \ge 0$; hence
  \cref{lem:eta-optimization}, applied with $\mathrm{opt} = \mathsf{OPT}^{\gamma}_{\mathrm{pert}}$
  and $L = d\,\ln\tfrac{e\,|Z|}{d}$, yields $E - \mathsf{OPT}^{\gamma}_{\mathrm{pert}} \le
  \sqrt{2\,\mathsf{OPT}^{\gamma}_{\mathrm{pert}}\cdot d\,\ln\tfrac{e\,|Z|}{d}} + d\,\ln\tfrac{e\,|Z|}{d}$.
  Using $\mathsf{OPT}^{\gamma}_{\mathrm{pert}} \le T$ and $d\,\ln\tfrac{e\,|Z|}{d} \ge 0$ to bound the
  square-root term by $\sqrt{2\,T \cdot d\,\ln\tfrac{e\,|Z|}{d}}$ gives
  $E - \mathsf{OPT}^{\gamma}_{\mathrm{pert}} \le \sqrt{2\,T \cdot d\,\ln\tfrac{e\,|Z|}{d}} +
  d\,\ln\tfrac{e\,|Z|}{d}$, which is the claimed bound since $d = \mathsf{vc}(
  \mathcal{H})$ and $|Z| = |\mathsf{C}(\mathcal{X},\rho,\gamma)|$. -/)
  (title := /-- Input-margin regret bound against the relaxed benchmark -/)
  (latexEnv := "theorem")]
theorem input_margin_upperbnd {γ : ℝ} (hγ : 0 < γ) {Z : Finset X} {φ : X → X}
    (hcover : is_gamma_cover γ Z φ) (H : Set (X → Y)) (T : ℕ)
    (xs : Fin T → X) (ys : Fin T → Y) (d : ℕ) (hd : 0 < d) (hdn : d ≤ Z.card)
    (m : ℕ) (hcount : m ≤ ∑ k ∈ Finset.range (d + 1), (Z.card).choose k)
    (expectedMistakes : ℝ)
    (hMW : ∀ η : ℝ, 0 < η →
      expectedMistakes ≤ (η / (1 - Real.exp (-η))) * projected_empirical_opt H φ T xs ys
        + (1 / (1 - Real.exp (-η))) * Real.log (m : ℝ)) :
    expectedMistakes - perturbed_opt γ H T xs ys
      ≤ Real.sqrt (2 * (T : ℝ) * ((d : ℝ) * Real.log (Real.exp 1 * (Z.card : ℝ) / (d : ℝ))))
        + (d : ℝ) * Real.log (Real.exp 1 * (Z.card : ℝ) / (d : ℝ)) := by
  classical
  set L : ℝ := (d : ℝ) * Real.log (Real.exp 1 * (Z.card : ℝ) / (d : ℝ)) with hL_def
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hB1 : (1 : ℝ) ≤ Real.exp 1 * (Z.card : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hd0, one_mul]
    have hZcard0 : (0 : ℝ) ≤ (Z.card : ℝ) := by positivity
    have he : (d : ℝ) ≤ (Z.card : ℝ) := by exact_mod_cast hdn
    calc (d : ℝ) ≤ (Z.card : ℝ) := he
      _ = 1 * (Z.card : ℝ) := by ring
      _ ≤ Real.exp 1 * (Z.card : ℝ) :=
          mul_le_mul_of_nonneg_right (Real.one_le_exp (by norm_num)) hZcard0
  have hlogB0 : 0 ≤ Real.log (Real.exp 1 * (Z.card : ℝ) / (d : ℝ)) := Real.log_nonneg hB1
  have hL0 : 0 ≤ L := by rw [hL_def]; positivity
  have hlogm : Real.log (m : ℝ) ≤ L :=
    sauer_shelah_cover_bound Z.card d m hd hdn hcount
  have hcov : projected_empirical_opt H φ T xs ys ≤ perturbed_opt γ H T xs ys :=
    cover_opt_bound hcover H T xs ys
  have hopt0 : 0 ≤ perturbed_opt γ H T xs ys := by
    unfold perturbed_opt
    apply Real.iInf_nonneg
    intro h
    apply Real.iInf_nonneg
    intro _
    apply Finset.sum_nonneg
    intro t _
    unfold perturbed_loss
    split <;> norm_num
  have hTnn : (0 : ℝ) ≤ (T : ℝ) := by positivity
  have hsum_le : ∀ h : X → Y,
      (∑ t, perturbed_loss γ h (xs t) (ys t)) ≤ (T : ℝ) := by
    intro h
    calc (∑ t, perturbed_loss γ h (xs t) (ys t))
        ≤ ∑ _t : Fin T, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro t _
          unfold perturbed_loss
          split <;> norm_num
      _ = (T : ℝ) := by simp
  have hsum_nonneg : ∀ h : X → Y,
      (0 : ℝ) ≤ ∑ t, perturbed_loss γ h (xs t) (ys t) := by
    intro h
    apply Finset.sum_nonneg
    intro t _
    unfold perturbed_loss
    split <;> norm_num
  have hoptT : perturbed_opt γ H T xs ys ≤ (T : ℝ) := by
    have hg_le : ∀ h : X → Y,
        (⨅ _ : h ∈ H, ∑ t, perturbed_loss γ h (xs t) (ys t)) ≤ (T : ℝ) := by
      intro h
      by_cases hh : h ∈ H
      · haveI : Nonempty (h ∈ H) := ⟨hh⟩
        rw [ciInf_const]
        exact hsum_le h
      · haveI : IsEmpty (h ∈ H) := ⟨hh⟩
        rw [Real.iInf_of_isEmpty]
        exact hTnn
    have hg_nonneg : ∀ h : X → Y,
        (0 : ℝ) ≤ (⨅ _ : h ∈ H, ∑ t, perturbed_loss γ h (xs t) (ys t)) := by
      intro h
      exact Real.iInf_nonneg (fun _ => hsum_nonneg h)
    unfold perturbed_opt
    rcases isEmpty_or_nonempty (X → Y) with hE | hNE
    · haveI := hE
      rw [Real.iInf_of_isEmpty]
      exact hTnn
    · obtain ⟨h0⟩ := hNE
      exact ciInf_le_of_le ⟨0, by rintro x ⟨h, rfl⟩; exact hg_nonneg h⟩ h0 (hg_le h0)
  have hreg : ∀ η : ℝ, 0 < η →
      expectedMistakes ≤ (η / (1 - Real.exp (-η))) * perturbed_opt γ H T xs ys
        + (1 / (1 - Real.exp (-η))) * L := by
    intro η hη
    have hexp : Real.exp (-η) < 1 := by
      have := Real.exp_lt_exp.mpr (show -η < 0 by linarith)
      rwa [Real.exp_zero] at this
    have hden : 0 < 1 - Real.exp (-η) := by linarith
    have hc1 : 0 ≤ η / (1 - Real.exp (-η)) := by positivity
    have hc2 : 0 ≤ 1 / (1 - Real.exp (-η)) := by positivity
    have h1 : (η / (1 - Real.exp (-η))) * projected_empirical_opt H φ T xs ys
        ≤ (η / (1 - Real.exp (-η))) * perturbed_opt γ H T xs ys :=
      mul_le_mul_of_nonneg_left hcov hc1
    have h2 : (1 / (1 - Real.exp (-η))) * Real.log (m : ℝ)
        ≤ (1 / (1 - Real.exp (-η))) * L :=
      mul_le_mul_of_nonneg_left hlogm hc2
    linarith [hMW η hη, h1, h2]
  have hfinal := eta_optimization T (perturbed_opt γ H T xs ys) L expectedMistakes
    hopt0 hoptT hL0 hreg
  have hsqrt : Real.sqrt (2 * perturbed_opt γ H T xs ys * L) ≤ Real.sqrt (2 * (T : ℝ) * L) := by
    apply Real.sqrt_le_sqrt
    nlinarith [hopt0, hoptT, hL0]
  calc expectedMistakes - perturbed_opt γ H T xs ys
      ≤ Real.sqrt (2 * perturbed_opt γ H T xs ys * L) + L := hfinal
    _ ≤ Real.sqrt (2 * (T : ℝ) * L) + L := by linarith [hsqrt]

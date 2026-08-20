import Architect
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Int.Interval

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:rnn-eigenvalue"
  (statement := /-- Let $\alpha \in \mathbb{R}$ and let $K \in \mathbb{N}$. For an index
    $s \in \mathbb{Z}$ we define the \emph{eigenvalue} of the linear recurrent neural network
    associated with the stability parameter $\alpha$, the recall horizon $K$ and the index $s$ by
    \[
      a_s \;=\; \exp\!\left(-\frac{\alpha}{K}\right)\exp\!\left(\frac{i\pi s}{K}\right)
            \;=\; \exp\!\left(-\frac{\alpha}{K} + \frac{i\pi s}{K}\right)
            \;\in\; \mathbb{C}.
    \]
    This is the parametrisation of the recurrent state-transition eigenvalues used throughout the
    upper-bound analysis. -/)
  (title := /-- Eigenvalues of the linear recurrent neural network -/)
  (latexEnv := "definition")]
noncomputable def rnn_eigenvalue (α : ℝ) (K : ℕ) (s : ℤ) : ℂ :=
  Complex.exp (((-α / K : ℝ) : ℂ) + ((Real.pi * s / K : ℝ) : ℂ) * Complex.I)

@[blueprint "def:rnn-coefficient-scale"
  (statement := /-- Let $\alpha \in \mathbb{R}$ and let $K \in \mathbb{N}$. We define the common
    real scale of the output coefficients of the filter by
    \[
      \beta \;=\; \frac{e^{-\alpha}\left(e^{2\alpha} - e^{-2\alpha}\right)}{2K} \;\in\; \mathbb{R}.
    \]
    This is the modulus common to all the coefficients $b_s$, isolated so that the alternating sign
    is the only part of $b_s$ that depends on the index $s$. -/)
  (title := /-- Common scale of the output coefficients -/)
  (latexEnv := "definition")]
noncomputable def rnn_coefficient_scale (α : ℝ) (K : ℕ) : ℝ :=
  Real.exp (-α) * (Real.exp (2 * α) - Real.exp (-(2 * α))) / (2 * K)

@[blueprint "def:rnn-coefficient"
  (statement := /-- Let $\alpha \in \mathbb{R}$, let $K \in \mathbb{N}$, and let $\beta$ be the
    scale of \cref{def:rnn-coefficient-scale}. For an index $s \in \mathbb{Z}$ we define the
    \emph{output coefficient}
    \[
      b_s \;=\; \beta \, (-1)^s
            \;=\; \frac{e^{-\alpha}\left(e^{2\alpha} - e^{-2\alpha}\right)}{2K}\,(-1)^s
            \;\in\; \mathbb{C},
    \]
    where $(-1)^s$ is the integer power of $-1$ in $\mathbb{C}$. These are the asymptotically
    optimal coefficients of the source's Lemma on the parametrisation of the $b_s$. -/)
  (title := /-- Output coefficients of the linear recurrent neural network -/)
  (latexEnv := "definition")]
noncomputable def rnn_coefficient (α : ℝ) (K : ℕ) (s : ℤ) : ℂ :=
  ((rnn_coefficient_scale α K : ℝ) : ℂ) * (-1 : ℂ) ^ s

@[blueprint "def:rnn-filter"
  (statement := /-- Let $\alpha \in \mathbb{R}$ and let $T, K \in \mathbb{N}$; the hidden state
    size is $S = 2T + 1$. With the eigenvalues $a_s$ of \cref{def:rnn-eigenvalue} and the
    coefficients $b_s$ of \cref{def:rnn-coefficient}, the \emph{convolution filter} of the linear
    recurrent neural network is the sequence $(c_k)_{k \in \mathbb{N}}$ given by
    \[
      c_k \;=\; \sum_{s = -T}^{T} b_s \, a_s^{\,k} \;\in\; \mathbb{C}, \qquad k \in \mathbb{N},
    \]
    the sum being taken over the $S = 2T+1$ integers $s$ with $-T \le s \le T$. The output of the
    network on an input $u$ is the convolution $y_n = (c * u)_n$. -/)
  (title := /-- Convolution filter of the linear recurrent neural network -/)
  (latexEnv := "definition")]
noncomputable def rnn_filter (α : ℝ) (T K : ℕ) (k : ℕ) : ℂ :=
  ∑ s ∈ Finset.Icc (-(T : ℤ)) (T : ℤ), rnn_coefficient α K s * rnn_eigenvalue α K s ^ k

@[blueprint "def:shift-filter"
  (statement := /-- Let $K \in \mathbb{N}$. The \emph{shift-$K$ filter} is the sequence
    $(d_k)_{k \in \mathbb{N}}$ defined by
    \[
      d_k \;=\; \mathbf{1}_{k = K} \;=\;
        \begin{cases} 1, & k = K, \\ 0, & k \neq K, \end{cases}
    \]
    that is, the Dirac impulse at position $K$. Convolution with $d$ is exactly the operation of
    copying the input from $K$ time steps in the past. -/)
  (title := /-- The shift-$K$ target filter -/)
  (latexEnv := "definition")]
noncomputable def shift_filter (K : ℕ) (k : ℕ) : ℂ :=
  if k = K then 1 else 0

@[blueprint "def:white-noise-time-loss"
  (statement := /-- Let $c, d : \mathbb{N} \to \mathbb{C}$ be two filters. Under a white-noise
    input, whose autocorrelation is $\gamma(k) = \mathbf{1}_{k = 0}$, the double sum
    $\sum_{k, k'} (c_k - d_k)\overline{(c_{k'} - d_{k'})}\,\gamma(k - k')$ defining the
    time-domain expected mean-square approximation error collapses to its diagonal, and we
    therefore define
    \[
      \mathcal{L}_{\mathrm{time}}(c, d) \;=\; \sum_{k = 0}^{\infty} \left|c_k - d_k\right|^2
      \;\in\; \mathbb{R}.
    \]
    The sum is the unconditional sum of a family of nonnegative reals; it is the true value of the
    series whenever the family is summable, which is established for the filters of interest in
    \cref{lem:squared-norm-summable}. -/)
  (title := /-- Time-domain approximation error under white-noise input -/)
  (latexEnv := "definition")]
noncomputable def white_noise_time_loss (c d : ℕ → ℂ) : ℝ :=
  ∑' k : ℕ, ‖c k - d k‖ ^ 2

@[blueprint "def:rnn-denominator"
  (statement := /-- Let $\alpha \in \mathbb{R}$ and let $K \in \mathbb{N}$. For $m \in \mathbb{Z}$
    we define
    \[
      D_m \;=\; 1 - \exp\!\left(-\frac{2\alpha}{K} + \frac{i \pi m}{K}\right) \;\in\; \mathbb{C}.
    \]
    By \cref{lem:eigenvalue-product} the quantity $D_{s - s'}$ is exactly the resolvent denominator
    $1 - a_s \overline{a_{s'}}$ produced by summing a geometric series over the time index; it
    depends on the pair $(s, s')$ only through the difference $m = s - s'$. -/)
  (title := /-- Resolvent denominator of the filter -/)
  (latexEnv := "definition")]
noncomputable def rnn_denominator (α : ℝ) (K : ℕ) (m : ℤ) : ℂ :=
  1 - Complex.exp (((-(2 * α) / K : ℝ) : ℂ) + ((Real.pi * m / K : ℝ) : ℂ) * Complex.I)

@[blueprint "def:fourier-kernel"
  (statement := /-- Let $\alpha \in \mathbb{R}$. We define the $2\pi$-periodic kernel
    $f_\alpha : \mathbb{R} \to \mathbb{C}$ on the fundamental domain by
    \[
      f_\alpha(\omega) \;=\;
        \frac{2\,e^{\frac{2\alpha}{\pi}(\omega - \pi)}}{e^{2\alpha} - e^{-2\alpha}}.
    \]
    We record a discrepancy in the source, which displays this kernel with the exponent
    $-\frac{2\alpha}{\pi}(\omega - \pi)$ but then evaluates its Fourier coefficients using the
    exponent $+\frac{2\alpha}{\pi}(\omega - \pi)$; only the latter sign is compatible with the
    value $\frac{1}{2\alpha - i\pi s}$ asserted in \cref{lem:fourier-coefficient-kernel}. Since the
    two kernels agree at $\omega = \pi$, which is the only point at which the kernel is evaluated
    in \cref{lem:alternating-inverse-series}, the conclusion of the source is unaffected. -/)
  (title := /-- The Fourier kernel $f_\alpha$ -/)
  (latexEnv := "definition")]
noncomputable def fourier_kernel (α : ℝ) (ω : ℝ) : ℂ :=
  ((2 * Real.exp (2 * α / Real.pi * (ω - Real.pi))
      / (Real.exp (2 * α) - Real.exp (-(2 * α))) : ℝ) : ℂ)

@[blueprint "lem:eigenvalue-norm"
  (statement := /-- Let $\alpha \in \mathbb{R}$ with $\alpha > 0$, let $K \in \mathbb{N}$ with
    $K \ge 1$, and let $s \in \mathbb{Z}$. Then the eigenvalue $a_s$ of
    \cref{def:rnn-eigenvalue} satisfies
    \[
      \left|a_s\right| \;=\; e^{-\alpha/K}
      \qquad\text{and}\qquad
      \left|a_s\right| \;<\; 1 .
    \]
    In particular the modulus does not depend on $s$, and the recurrence is stable for every
    positive $\alpha$. -/)
  (proof := /-- By \cref{def:rnn-eigenvalue} we have
    $a_s = \exp\left(-\frac{\alpha}{K} + \frac{i\pi s}{K}\right)$, and the real part of the
    argument is $-\alpha/K$ because $-\alpha/K$ is real and $\frac{\pi s}{K}$ is real, so that
    $\frac{i \pi s}{K}$ is purely imaginary. Since the modulus of the complex exponential is the
    real exponential of the real part of its argument, we obtain
    $\left|a_s\right| = e^{-\alpha/K}$, which is the first assertion.

    For the second assertion, $K \ge 1$ gives $K > 0$, and $\alpha > 0$, so $\alpha / K > 0$ and
    hence $-\alpha/K < 0$. The real exponential is strictly increasing and satisfies
    $e^0 = 1$, so $e^{-\alpha/K} < 1$. Combining with the first assertion yields
    $\left|a_s\right| < 1$. -/)
  (title := /-- Modulus of the eigenvalues -/)
  (latexEnv := "lemma")]
lemma eigenvalue_norm (α : ℝ) (hα : 0 < α) (K : ℕ) (hK : 1 ≤ K) (s : ℤ) :
    ‖rnn_eigenvalue α K s‖ = Real.exp (-α / K) ∧ ‖rnn_eigenvalue α K s‖ < 1 := by
  have hnorm : ‖rnn_eigenvalue α K s‖ = Real.exp (-α / K) := by
    rw [rnn_eigenvalue, Complex.norm_exp]
    congr 1
    simp
  refine ⟨hnorm, ?_⟩
  rw [hnorm]
  have hK0 : (0 : ℝ) < K := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hK
  have hneg : -α / (K : ℝ) < 0 := div_neg_of_neg_of_pos (by linarith) hK0
  calc Real.exp (-α / K) < Real.exp 0 := Real.exp_lt_exp.mpr hneg
    _ = 1 := Real.exp_zero

@[blueprint "lem:eigenvalue-pow-horizon"
  (statement := /-- Let $\alpha \in \mathbb{R}$, let $K \in \mathbb{N}$ with $K \ge 1$, and let
    $s \in \mathbb{Z}$. Then the eigenvalue $a_s$ of \cref{def:rnn-eigenvalue} raised to the recall
    horizon $K$ satisfies
    \[
      a_s^{\,K} \;=\; e^{-\alpha}\,(-1)^s .
    \]
    Thus at the target delay $k = K$ every eigenvalue collapses to the same real modulus
    $e^{-\alpha}$ times the alternating sign $(-1)^s$. -/)
  (proof := /-- By \cref{def:rnn-eigenvalue} and the multiplicativity of the complex exponential,
    \[
      a_s^{\,K}
        = \exp\!\left(K\left(-\frac{\alpha}{K} + \frac{i \pi s}{K}\right)\right)
        = \exp\!\left(-\alpha + i \pi s\right)
        = e^{-\alpha}\exp(i\pi s),
    \]
    where the second equality uses $K \ge 1$, so that $K \neq 0$ and
    $K \cdot \frac{\alpha}{K} = \alpha$, $K \cdot \frac{\pi s}{K} = \pi s$.

    It remains to identify $\exp(i \pi s)$ for $s \in \mathbb{Z}$. Euler's identity gives
    $\exp(i\pi) = -1$, and the exponential is a homomorphism from the additive group
    $\mathbb{C}$ to the multiplicative group $\mathbb{C}^{\times}$, so
    $\exp(i \pi s) = \left(\exp(i\pi)\right)^{s} = (-1)^{s}$ as an integer power. Substituting
    gives $a_s^{\,K} = e^{-\alpha}(-1)^s$. -/)
  (title := /-- The eigenvalues at the recall horizon -/)
  (latexEnv := "lemma")]
lemma eigenvalue_pow_horizon (α : ℝ) (K : ℕ) (hK : 1 ≤ K) (s : ℤ) :
    rnn_eigenvalue α K s ^ K = ((Real.exp (-α) : ℝ) : ℂ) * (-1 : ℂ) ^ s := by
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hK
  rw [rnn_eigenvalue, ← Complex.exp_nat_mul]
  have harg : (K : ℂ) * (((-α / K : ℝ) : ℂ) + ((Real.pi * s / K : ℝ) : ℂ) * Complex.I)
      = ((-α : ℝ) : ℂ) + (s : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp
  rw [harg, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I, ← Complex.ofReal_exp]

@[blueprint "lem:eigenvalue-product"
  (statement := /-- Let $\alpha \in \mathbb{R}$, let $K \in \mathbb{N}$, and let
    $s, s' \in \mathbb{Z}$. With the eigenvalues $a_s$ of \cref{def:rnn-eigenvalue} and the
    resolvent denominator $D_m$ of \cref{def:rnn-denominator} we have
    \[
      1 - a_s \overline{a_{s'}} \;=\; D_{s - s'} .
    \]
    In particular $1 - a_s \overline{a_{s'}}$ depends on the pair $(s, s')$ only through the
    difference $m = s - s'$. -/)
  (proof := /-- By \cref{def:rnn-eigenvalue},
    $a_s = \exp\left(-\frac{\alpha}{K} + \frac{i \pi s}{K}\right)$ and
    $a_{s'} = \exp\left(-\frac{\alpha}{K} + \frac{i \pi s'}{K}\right)$. The complex conjugate of
    an exponential is the exponential of the conjugate argument, and the argument of $a_{s'}$ has
    real part $-\frac{\alpha}{K}$ and imaginary part $\frac{\pi s'}{K}$, whence
    \[
      \overline{a_{s'}} = \exp\!\left(-\frac{\alpha}{K} - \frac{i \pi s'}{K}\right).
    \]
    Multiplying and using that the exponential turns sums into products,
    \[
      a_s \overline{a_{s'}}
        = \exp\!\left(-\frac{2\alpha}{K} + \frac{i\pi (s - s')}{K}\right).
    \]
    Subtracting from $1$ and comparing with \cref{def:rnn-denominator} evaluated at
    $m = s - s'$ gives the claimed identity. -/)
  (title := /-- The resolvent denominator depends only on the index difference -/)
  (latexEnv := "lemma")]
lemma eigenvalue_product (α : ℝ) (K : ℕ) (s s' : ℤ) :
    1 - rnn_eigenvalue α K s * (starRingEnd ℂ) (rnn_eigenvalue α K s')
      = rnn_denominator α K (s - s') := by
  rw [rnn_eigenvalue, rnn_eigenvalue, rnn_denominator, ← Complex.exp_conj, ← Complex.exp_add]
  congr 2
  simp only [map_add, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast,
    map_natCast, map_inv₀]
  push_cast
  ring

@[blueprint "lem:squared-norm-summable"
  (statement := /-- Let $\alpha \in \mathbb{R}$ with $\alpha > 0$ and let $T, K \in \mathbb{N}$
    with $K \ge 1$. Then the family of nonnegative reals
    $\left(\left|c_k\right|^2\right)_{k \in \mathbb{N}}$, where $c$ is the filter of
    \cref{def:rnn-filter}, is summable:
    \[
      \sum_{k = 0}^{\infty} \left|c_k\right|^2 \;<\; \infty .
    \]
    Equivalently, the filter $c$ lies in $\ell^2(\mathbb{N})$. -/)
  (proof := /-- Write $q = e^{-\alpha/K}$. By \cref{lem:eigenvalue-norm} we have
    $\left|a_s\right| = q$ for every $s$ and $q < 1$.

    Let $B = \sum_{s = -T}^{T} \left|b_s\right|$, a finite sum of nonnegative reals, hence a finite
    nonnegative real. By \cref{def:rnn-filter} and the triangle inequality together with
    multiplicativity of the modulus,
    \[
      \left|c_k\right|
        \;\le\; \sum_{s = -T}^{T} \left|b_s\right| \left|a_s\right|^{k}
        \;=\; B \, q^{k}
        \qquad \text{for every } k \in \mathbb{N}.
    \]
    Squaring, and using that both sides are nonnegative,
    $\left|c_k\right|^2 \le B^2 \left(q^2\right)^{k}$ for every $k$.

    Since $0 \le q < 1$ we have $0 \le q^2 < 1$, so the geometric series
    $\sum_{k} \left(q^2\right)^{k}$ converges, and therefore so does
    $\sum_{k} B^2 \left(q^2\right)^{k}$. By comparison of a nonnegative family with a summable
    dominating family, $\left(\left|c_k\right|^2\right)_{k}$ is summable. -/)
  (title := /-- Square summability of the filter -/)
  (latexEnv := "lemma")]
lemma squared_norm_summable (α : ℝ) (hα : 0 < α) (T K : ℕ) (hK : 1 ≤ K) :
    Summable (fun k : ℕ => ‖rnn_filter α T K k‖ ^ 2) := by
  set q : ℝ := Real.exp (-α / K) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hqlt : q < 1 := by
    have h := (eigenvalue_norm α hα K hK 0).2
    rw [(eigenvalue_norm α hα K hK 0).1] at h
    rw [hq]; exact h
  set B : ℝ := ∑ s ∈ Finset.Icc (-(T : ℤ)) (T : ℤ), ‖rnn_coefficient α K s‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun s _ => norm_nonneg _)
  have hsum : Summable (fun k : ℕ => B ^ 2 * (q ^ 2) ^ k) := by
    apply Summable.mul_left
    exact summable_geometric_of_lt_one (by positivity) (by nlinarith [hq0, hqlt])
  refine Summable.of_nonneg_of_le (fun k => by positivity) ?_ hsum
  intro k
  have hnorm_le : ‖rnn_filter α T K k‖ ≤ B * q ^ k := by
    calc ‖rnn_filter α T K k‖
        = ‖∑ s ∈ Finset.Icc (-(T : ℤ)) (T : ℤ),
              rnn_coefficient α K s * rnn_eigenvalue α K s ^ k‖ := by rw [rnn_filter]
      _ ≤ ∑ s ∈ Finset.Icc (-(T : ℤ)) (T : ℤ),
              ‖rnn_coefficient α K s * rnn_eigenvalue α K s ^ k‖ := norm_sum_le _ _
      _ = ∑ s ∈ Finset.Icc (-(T : ℤ)) (T : ℤ), ‖rnn_coefficient α K s‖ * q ^ k := by
          refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [norm_mul, norm_pow, (eigenvalue_norm α hα K hK s).1]
      _ = (∑ s ∈ Finset.Icc (-(T : ℤ)) (T : ℤ), ‖rnn_coefficient α K s‖) * q ^ k := by
          rw [Finset.sum_mul]
      _ = B * q ^ k := by rw [hB]
  calc ‖rnn_filter α T K k‖ ^ 2
      ≤ (B * q ^ k) ^ 2 := by
        gcongr
    _ = B ^ 2 * (q ^ 2) ^ k := by ring

@[blueprint "lem:filter-sq-double-sum"
  (statement := /-- Let $\alpha \in \mathbb{R}$ with $\alpha > 0$ and let $T, K \in \mathbb{N}$
    with $K \ge 1$. With the coefficients $b_s$ of \cref{def:rnn-coefficient}, the filter $c$ of
    \cref{def:rnn-filter} and the resolvent denominator $D_m$ of \cref{def:rnn-denominator}, the
    energy of the filter is given by the finite double sum
    \[
      \sum_{k = 0}^{\infty} \left|c_k\right|^2
        \;=\; \sum_{s = -T}^{T} \sum_{s' = -T}^{T}
                \frac{b_s \overline{b_{s'}}}{D_{s - s'}} ,
    \]
    an identity between the real number on the left, viewed as a complex number, and the complex
    number on the right. -/)
  (proof := /-- Fix $k \in \mathbb{N}$. By \cref{def:rnn-filter} and the identity
    $\left|z\right|^2 = z \overline{z}$, expanding the product of the two finite sums gives
    \[
      \left|c_k\right|^2
        = \left(\sum_{s = -T}^{T} b_s a_s^{\,k}\right)
          \overline{\left(\sum_{s' = -T}^{T} b_{s'} a_{s'}^{\,k}\right)}
        = \sum_{s = -T}^{T} \sum_{s' = -T}^{T}
            b_s \overline{b_{s'}} \left(a_s \overline{a_{s'}}\right)^{k},
    \]
    where we used that conjugation is additive and multiplicative.

    Summing the previous display over $k$ shows that the energy $\sum_{k} \left|c_k\right|^2$,
    viewed as a complex number, equals
    $\sum_{k = 0}^{\infty} \sum_{s} \sum_{s'} b_s \overline{b_{s'}} \left(a_s \overline{a_{s'}}\right)^{k}$.
    For each of the finitely many pairs $(s, s')$ we have, by \cref{lem:eigenvalue-norm},
    \[
      \left| a_s \overline{a_{s'}} \right|
        = \left|a_s\right| \left|a_{s'}\right| = e^{-2\alpha/K} < 1 ,
    \]
    so each geometric family $\left(\left(a_s \overline{a_{s'}}\right)^{k}\right)_k$ is summable;
    consequently the finite sum over the pairs $(s, s')$ may be exchanged with the sum over $k$,
    giving
    \[
      \sum_{k = 0}^{\infty} \left|c_k\right|^2
        = \sum_{s = -T}^{T} \sum_{s' = -T}^{T} b_s \overline{b_{s'}}
            \sum_{k = 0}^{\infty} \left(a_s \overline{a_{s'}}\right)^{k} .
    \]
    Summing each geometric series, again legitimate because
    $\left|a_s \overline{a_{s'}}\right| < 1$, yields
    $\sum_{k = 0}^{\infty} \left(a_s \overline{a_{s'}}\right)^{k} = \left(1 - a_s \overline{a_{s'}}\right)^{-1}$.
    Finally \cref{lem:eigenvalue-product} identifies $1 - a_s \overline{a_{s'}}$ with
    $D_{s - s'}$, which gives the asserted formula. -/)
  (title := /-- The energy of the filter as a finite double sum -/)
  (latexEnv := "lemma")]
lemma filter_sq_double_sum (α : ℝ) (hα : 0 < α) (T K : ℕ) (hK : 1 ≤ K) :
    ((∑' k : ℕ, ‖rnn_filter α T K k‖ ^ 2 : ℝ) : ℂ)
      = ∑ s ∈ Finset.Icc (-(T : ℤ)) (T : ℤ), ∑ s' ∈ Finset.Icc (-(T : ℤ)) (T : ℤ),
          rnn_coefficient α K s * (starRingEnd ℂ) (rnn_coefficient α K s')
            / rnn_denominator α K (s - s') := by
  have hqnorm : ∀ s s' : ℤ,
      ‖rnn_eigenvalue α K s * (starRingEnd ℂ) (rnn_eigenvalue α K s')‖ < 1 := by
    intro s s'
    rw [norm_mul, Complex.norm_conj, (eigenvalue_norm α hα K hK s).1,
        (eigenvalue_norm α hα K hK s').1]
    have h1 := (eigenvalue_norm α hα K hK s).2
    rw [(eigenvalue_norm α hα K hK s).1] at h1
    have h0 : (0 : ℝ) ≤ Real.exp (-α / K) := (Real.exp_pos _).le
    nlinarith [h0, h1]
  have hgsum : ∀ s s' : ℤ, Summable (fun k : ℕ =>
      rnn_coefficient α K s * (starRingEnd ℂ) (rnn_coefficient α K s')
        * (rnn_eigenvalue α K s * (starRingEnd ℂ) (rnn_eigenvalue α K s')) ^ k) :=
    fun s s' => (summable_geometric_of_norm_lt_one (hqnorm s s')).mul_left _
  have hpt : ∀ k : ℕ, ((‖rnn_filter α T K k‖ ^ 2 : ℝ) : ℂ)
      = ∑ s ∈ Finset.Icc (-(T : ℤ)) (T : ℤ), ∑ s' ∈ Finset.Icc (-(T : ℤ)) (T : ℤ),
          rnn_coefficient α K s * (starRingEnd ℂ) (rnn_coefficient α K s')
            * (rnn_eigenvalue α K s * (starRingEnd ℂ) (rnn_eigenvalue α K s')) ^ k := by
    intro k
    rw [Complex.sq_norm, ← Complex.mul_conj, rnn_filter, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun s' _ => ?_))
    rw [map_mul, map_pow]
    ring
  rw [Complex.ofReal_tsum]
  simp_rw [hpt]
  rw [Summable.tsum_finsetSum (fun s _ => summable_sum (fun s' _ => hgsum s s'))]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Summable.tsum_finsetSum (fun s' _ => hgsum s s')]
  refine Finset.sum_congr rfl (fun s' _ => ?_)
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (hqnorm s s'), eigenvalue_product,
      div_eq_mul_inv]

@[blueprint "lem:cross-term"
  (statement := /-- Let $\alpha \in \mathbb{R}$, let $K \in \mathbb{N}$ with $K \ge 1$, and let
    $T \in \mathbb{N}$; put $S = 2T + 1$. Then the filter $c$ of \cref{def:rnn-filter} takes at the
    recall horizon $k = K$ the real value
    \[
      c_K \;=\; S \cdot \frac{e^{-2\alpha}\left(e^{2\alpha} - e^{-2\alpha}\right)}{2K} .
    \]
    In particular $c_K$ is real and positive when $\alpha > 0$, and it is exactly linear in
    $S / K$ with no error term. -/)
  (proof := /-- By \cref{def:rnn-filter} we have $c_K = \sum_{s = -T}^{T} b_s a_s^{\,K}$. Fix
    $s$ with $-T \le s \le T$. By \cref{lem:eigenvalue-pow-horizon},
    $a_s^{\,K} = e^{-\alpha}(-1)^s$, and by \cref{def:rnn-coefficient} together with
    \cref{def:rnn-coefficient-scale},
    $b_s = \frac{e^{-\alpha}\left(e^{2\alpha} - e^{-2\alpha}\right)}{2K}(-1)^s$. Hence
    \[
      b_s a_s^{\,K}
        = \frac{e^{-\alpha}\left(e^{2\alpha} - e^{-2\alpha}\right)}{2K}
          \, e^{-\alpha} \, (-1)^s (-1)^s
        = \frac{e^{-2\alpha}\left(e^{2\alpha} - e^{-2\alpha}\right)}{2K},
    \]
    where we used $(-1)^s(-1)^s = (-1)^{2s} = 1$ for every $s \in \mathbb{Z}$ and
    $e^{-\alpha}e^{-\alpha} = e^{-2\alpha}$.

    The summand is therefore the same real constant for every $s$, independent of $s$. The index
    set consists of the integers $s$ with $-T \le s \le T$, of which there are exactly
    $2T + 1 = S$. Summing the constant over the index set multiplies it by $S$, which gives the
    asserted value of $c_K$. -/)
  (title := /-- Exact value of the filter at the recall horizon -/)
  (latexEnv := "lemma")]
lemma cross_term (α : ℝ) (K : ℕ) (hK : 1 ≤ K) (T : ℕ) :
    rnn_filter α T K K
      = (((2 * (T : ℝ) + 1)
            * (Real.exp (-(2 * α)) * (Real.exp (2 * α) - Real.exp (-(2 * α))) / (2 * K)) : ℝ) : ℂ) := by
  have hconst : ∀ s ∈ Finset.Icc (-(T : ℤ)) (T : ℤ),
      rnn_coefficient α K s * rnn_eigenvalue α K s ^ K
        = ((Real.exp (-(2 * α)) * (Real.exp (2 * α) - Real.exp (-(2 * α))) / (2 * K) : ℝ) : ℂ) := by
    intro s _
    rw [rnn_coefficient, eigenvalue_pow_horizon α K hK s, rnn_coefficient_scale]
    have h1 : (-1 : ℂ) ^ s * (-1 : ℂ) ^ s = 1 := by
      rw [← mul_zpow]; norm_num
    rw [mul_mul_mul_comm, h1, mul_one, ← Complex.ofReal_mul]
    congr 1
    have h2 : Real.exp (-α) * Real.exp (-α) = Real.exp (-(2 * α)) := by
      rw [← Real.exp_add]; ring_nf
    linear_combination (Real.exp (2 * α) - Real.exp (-(2 * α))) / (2 * (K : ℝ)) * h2
  rw [rnn_filter, Finset.sum_congr rfl hconst, Finset.sum_const]
  have hcard : (Finset.Icc (-(T : ℤ)) (T : ℤ)).card = 2 * T + 1 := by
    rw [Int.card_Icc]; omega
  rw [hcard, nsmul_eq_mul]
  push_cast
  ring

@[blueprint "lem:loss-expansion"
  (statement := /-- Let $\alpha \in \mathbb{R}$ with $\alpha > 0$ and let $T, K \in \mathbb{N}$
    with $K \ge 1$. Let $c$ be the filter of \cref{def:rnn-filter} and $d$ the shift-$K$ filter of
    \cref{def:shift-filter}. Then the white-noise time-domain loss of
    \cref{def:white-noise-time-loss} decomposes as
    \[
      \mathcal{L}_{\mathrm{time}}(c, d)
        \;=\; 1 \;-\; 2\,\operatorname{Re}(c_K) \;+\; \sum_{k = 0}^{\infty}\left|c_k\right|^2 .
    \]
    The three terms are, respectively, the energy of the target, the cross term, and the energy of
    the filter. -/)
  (proof := /-- By \cref{def:shift-filter} the family $\left(\left|d_k\right|^2\right)_k$ is
    supported on the single index $k = K$, where it takes the value $1$; hence it is summable with
    $\sum_{k} \left|d_k\right|^2 = 1$. Likewise
    $\left(\operatorname{Re}\left(c_k \overline{d_k}\right)\right)_k$ is supported on $k = K$,
    where it equals $\operatorname{Re}(c_K)$, so it is summable with sum
    $\operatorname{Re}(c_K)$. By \cref{lem:squared-norm-summable} the family
    $\left(\left|c_k\right|^2\right)_k$ is summable as well.

    For each $k \in \mathbb{N}$, expanding the square of the modulus of a difference of complex
    numbers gives the pointwise identity
    \[
      \left|c_k - d_k\right|^2
        = \left|c_k\right|^2 - 2 \operatorname{Re}\left(c_k \overline{d_k}\right)
          + \left|d_k\right|^2 .
    \]
    All three families on the right-hand side have been shown to be summable, so the family on the
    left is summable and its sum is the corresponding combination of the three sums. Therefore
    \[
      \mathcal{L}_{\mathrm{time}}(c, d)
        = \sum_{k}\left|c_k\right|^2 - 2 \operatorname{Re}(c_K) + 1 ,
    \]
    which is the asserted identity after reordering the terms. -/)
  (title := /-- Exact expansion of the white-noise loss -/)
  (latexEnv := "lemma")]
lemma loss_expansion (α : ℝ) (hα : 0 < α) (T K : ℕ) (hK : 1 ≤ K) :
    white_noise_time_loss (rnn_filter α T K) (shift_filter K)
      = 1 - 2 * (rnn_filter α T K K).re + ∑' k : ℕ, ‖rnn_filter α T K k‖ ^ 2 := by
  have hc : Summable (fun k : ℕ => ‖rnn_filter α T K k‖ ^ 2) :=
    squared_norm_summable α hα T K hK
  have hg : Summable (fun k : ℕ =>
      ‖shift_filter K k‖ ^ 2
        - 2 * (rnn_filter α T K k * (starRingEnd ℂ) (shift_filter K k)).re) := by
    apply summable_of_ne_finset_zero (s := {K})
    intro b hb
    have hbK : b ≠ K := by simpa using hb
    simp [shift_filter, hbK]
  have hpoint : ∀ k : ℕ,
      ‖rnn_filter α T K k - shift_filter K k‖ ^ 2
        = ‖rnn_filter α T K k‖ ^ 2
          + (‖shift_filter K k‖ ^ 2
              - 2 * (rnn_filter α T K k * (starRingEnd ℂ) (shift_filter K k)).re) := by
    intro k
    rw [Complex.sq_norm, Complex.normSq_sub, ← Complex.sq_norm, ← Complex.sq_norm]
    ring
  have hgsum : (∑' k : ℕ, (‖shift_filter K k‖ ^ 2
        - 2 * (rnn_filter α T K k * (starRingEnd ℂ) (shift_filter K k)).re))
      = 1 - 2 * (rnn_filter α T K K).re := by
    rw [tsum_eq_single K (fun b hb => by simp [shift_filter, hb])]
    simp [shift_filter]
  unfold white_noise_time_loss
  rw [tsum_congr hpoint, hc.tsum_add hg, hgsum]
  ring

@[blueprint "lem:fourier-coefficient-kernel"
  (statement := /-- Let $\alpha \in \mathbb{R}$ with $\alpha > 0$ and let $s \in \mathbb{Z}$. Then
    the $s$-th Fourier coefficient of the kernel $f_\alpha$ of \cref{def:fourier-kernel} is
    \[
      c_s(f_\alpha) \;=\; \frac{1}{2\pi}\int_{0}^{2\pi} f_\alpha(\omega)\, e^{-i s \omega}
      \, d\omega \;=\; \frac{1}{2\alpha - i \pi s} .
    \]
    -/)
  (proof := /-- Set $\lambda = \frac{2\alpha}{\pi}$ and
    $D = e^{2\alpha} - e^{-2\alpha}$; since $\alpha > 0$ we have $\lambda > 0$ and $D > 0$, so
    $D \neq 0$. By \cref{def:fourier-kernel},
    $f_\alpha(\omega) = \frac{2}{D} e^{\lambda(\omega - \pi)}$, hence
    \[
      \frac{1}{2\pi}\int_{0}^{2\pi} f_\alpha(\omega) e^{-i s \omega} \, d\omega
        = \frac{e^{-\lambda \pi}}{\pi D}
          \int_{0}^{2\pi} e^{(\lambda - i s)\omega} \, d\omega .
    \]
    The exponent satisfies $\lambda - i s \neq 0$, because its real part is $\lambda > 0$. The
    integral of $\omega \mapsto e^{z\omega}$ over $[0, 2\pi]$ for $z \neq 0$ equals
    $\frac{e^{2 \pi z} - 1}{z}$, since $\omega \mapsto e^{z \omega}/z$ is an antiderivative of the
    integrand on all of $\mathbb{R}$ and the integrand is continuous, so the fundamental theorem of
    calculus applies. Therefore
    \[
      \frac{1}{2\pi}\int_{0}^{2\pi} f_\alpha(\omega) e^{-i s \omega} \, d\omega
        = \frac{e^{-\lambda\pi}}{\pi D} \cdot
          \frac{e^{2\pi(\lambda - i s)} - 1}{\lambda - i s} .
    \]
    Now $e^{-\lambda \pi} = e^{-2\alpha}$ by the definition of $\lambda$, and
    $e^{2\pi(\lambda - is)} = e^{2\pi\lambda} e^{-2\pi i s} = e^{4\alpha}$, because $s$ is an
    integer and the complex exponential is $2\pi i$-periodic, so $e^{-2\pi i s} = 1$. Hence the
    numerator becomes $e^{-2\alpha}\left(e^{4\alpha} - 1\right) = e^{2\alpha} - e^{-2\alpha} = D$,
    and
    \[
      \frac{1}{2\pi}\int_{0}^{2\pi} f_\alpha(\omega) e^{-i s \omega} \, d\omega
        = \frac{1}{\pi}\cdot\frac{1}{\lambda - i s}
        = \frac{1}{\pi \lambda - i \pi s}
        = \frac{1}{2\alpha - i \pi s},
    \]
    using $\pi \lambda = 2\alpha$ in the last step. -/)
  (title := /-- Fourier coefficients of the kernel $f_\alpha$ -/)
  (latexEnv := "lemma")]
lemma fourier_coefficient_kernel (α : ℝ) (hα : 0 < α) (s : ℤ) :
    (1 / (2 * (Real.pi : ℂ)))
        * ∫ ω in (0 : ℝ)..(2 * Real.pi),
            fourier_kernel α ω * Complex.exp (-((s : ℂ) * ((ω : ℝ) : ℂ)) * Complex.I)
      = 1 / (2 * (α : ℂ) - (Real.pi : ℂ) * (s : ℂ) * Complex.I) := by
  have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hπc : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hπ
  set D : ℝ := Real.exp (2 * α) - Real.exp (-(2 * α)) with hDdef
  have hDpos : 0 < D := by
    have h1 : Real.exp (-(2 * α)) < Real.exp (2 * α) := Real.exp_lt_exp.mpr (by linarith)
    rw [hDdef]; linarith
  have hDne : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hDpos.ne'
  have hDc : (D : ℂ) = Complex.exp (2 * (α : ℂ)) - Complex.exp (-(2 * (α : ℂ))) := by
    rw [hDdef]; push_cast [Complex.ofReal_exp]; ring
  set c : ℂ := ((2 * α / Real.pi : ℝ) : ℂ) - (s : ℂ) * Complex.I with hcdef
  have hcne : c ≠ 0 := by
    have hpos : (0 : ℝ) < 2 * α / Real.pi := div_pos (by linarith) Real.pi_pos
    have hre : c.re = 2 * α / Real.pi := by
      rw [hcdef]
      simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im]
    intro h
    rw [h, Complex.zero_re] at hre
    linarith
  have hπc2 : (Real.pi : ℂ) * c = 2 * (α : ℂ) - (Real.pi : ℂ) * (s : ℂ) * Complex.I := by
    rw [hcdef]; push_cast; field_simp
  set C : ℂ := 2 / (D : ℂ) * Complex.exp (-(2 * (α : ℂ))) with hCdef
  have hnum : Complex.exp (-(2 * (α : ℂ))) * (Complex.exp (4 * (α : ℂ)) - 1) = (D : ℂ) := by
    rw [hDc, mul_sub, mul_one, ← Complex.exp_add,
      show -(2 * (α : ℂ)) + 4 * (α : ℂ) = 2 * (α : ℂ) from by ring]
  have hcombine :
      (2 / (D : ℂ) * Complex.exp (-(2 * (α : ℂ))))
          * ((Complex.exp (4 * (α : ℂ)) - 1) / c) = 2 / c := by
    rw [show (2 / (D : ℂ) * Complex.exp (-(2 * (α : ℂ))))
            * ((Complex.exp (4 * (α : ℂ)) - 1) / c)
          = Complex.exp (-(2 * (α : ℂ))) * (Complex.exp (4 * (α : ℂ)) - 1) / (D : ℂ)
              * (2 / c) from by ring,
      hnum, div_self hDne, one_mul]
  have h0 : Complex.exp (c * ((0 : ℝ) : ℂ)) = 1 := by
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have h2π : Complex.exp (c * ((2 * Real.pi : ℝ) : ℂ)) = Complex.exp (4 * (α : ℂ)) := by
    have hcc : c * ((2 * Real.pi : ℝ) : ℂ)
        = 4 * (α : ℂ) + ((-s : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hcdef]; push_cast; field_simp; ring
    rw [hcc, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hpt : ∀ ω : ℝ,
      fourier_kernel α ω * Complex.exp (-((s : ℂ) * ((ω : ℝ) : ℂ)) * Complex.I)
        = C * Complex.exp (c * ((ω : ℝ) : ℂ)) := by
    intro ω
    have hE : Complex.exp ((2 * α / Real.pi * (ω - Real.pi) : ℝ) : ℂ)
          * Complex.exp (-((s : ℂ) * ((ω : ℝ) : ℂ)) * Complex.I)
        = Complex.exp (-(2 * (α : ℂ)))
          * Complex.exp ((((2 * α / Real.pi : ℝ) : ℂ) - (s : ℂ) * Complex.I) * ((ω : ℝ) : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    simp only [fourier_kernel]
    rw [← hDdef, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_exp,
      Complex.ofReal_ofNat, hCdef, hcdef]
    rw [show (2 : ℂ) * Complex.exp ((2 * α / Real.pi * (ω - Real.pi) : ℝ) : ℂ) / (D : ℂ)
            * Complex.exp (-((s : ℂ) * ((ω : ℝ) : ℂ)) * Complex.I)
          = (2 : ℂ) / (D : ℂ)
            * (Complex.exp ((2 * α / Real.pi * (ω - Real.pi) : ℝ) : ℂ)
                * Complex.exp (-((s : ℂ) * ((ω : ℝ) : ℂ)) * Complex.I)) from by ring,
      hE]
    ring
  simp only [hpt]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hcne, h0, h2π,
    hCdef, hcombine, ← hπc2]
  field_simp

@[blueprint "lem:alternating-inverse-series"
  (statement := /-- Let $\alpha \in \mathbb{R}$ with $\alpha > 0$. Then the symmetric partial sums
    of the alternating series $\sum_{m \in \mathbb{Z}} \frac{(-1)^m}{2\alpha - i \pi m}$ converge,
    as $N \to \infty$, to $\frac{2}{e^{2\alpha} - e^{-2\alpha}}$; that is,
    \[
      \lim_{N \to \infty} \sum_{m = -N}^{N} \frac{(-1)^m}{2\alpha - i \pi m}
        \;=\; \frac{2}{e^{2\alpha} - e^{-2\alpha}} .
    \] -/)
  (proof := /-- Put $z=-2\alpha i/\pi$. Since $\alpha>0$, the imaginary parts of $z$ and
    $z/2$ are nonzero, so neither number is an integer. For $n\geq 0$, set
    \[
      t_n(w)=\frac{1}{w-(n+1)}+\frac{1}{w+(n+1)}
      \quad\text{and}\quad
      a_n=(-1)^{n+1}t_n(z).
    \]
    The case $s=0$ of \cref{lem:fourier-coefficient-kernel} identifies the central coefficient
    with $1/(2\alpha)$.
    The cotangent partial-fraction expansion, applied at $z$ and $z/2$, gives absolutely
    convergent series
    \[
      \pi\cot(\pi w)-\frac1w=\sum_{n=0}^{\infty}t_n(w).
    \]
    Split the series for $a_n$ into its even and odd subsequences. The parity identities for
    $(-1)^{n+1}$ and the relation
    \[
      t_{2k+1}(z)=\frac12t_k(z/2)
    \]
    show that
    \[
      \sum_{n=0}^{\infty}a_n
        =\pi\bigl(\cot(\pi z/2)-\cot(\pi z)\bigr)-\frac1z.
    \]

    For every $N\in\mathbb N$, the identity
    $2\alpha-i\pi m=\pi i(z-m)$ and pairing the terms indexed by
    $m=n+1$ and $m=-(n+1)$ yield
    \[
      \sum_{m=-N}^{N}\frac{(-1)^m}{2\alpha-i\pi m}
        =\frac1{2\alpha}+\frac1{\pi i}\sum_{n=0}^{N-1}a_n.
    \]
    Absolute convergence of $(a_n)$ therefore permits passage to the limit. Finally, substituting
    $z=-2\alpha i/\pi$ into the preceding cotangent formula and using
    \[
      \cot w=\frac{e^{2iw}+1}{i(1-e^{2iw})}
    \]
    reduces the limit by field arithmetic to
    $2/(e^{2\alpha}-e^{-2\alpha})$. The required denominators are nonzero because
    $\alpha>0$ and the real exponential is strictly increasing. -/)
  (title := /-- Summation of the alternating series of inverse linear terms -/)
  (latexEnv := "lemma")]
lemma alternating_inverse_series (α : ℝ) (hα : 0 < α) :
    Filter.Tendsto
      (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (-1 : ℂ) ^ m / (2 * (α : ℂ) - (Real.pi : ℂ) * (m : ℂ) * Complex.I))
      Filter.atTop
      (nhds (2 / (((Real.exp (2 * α) - Real.exp (-(2 * α))) : ℝ) : ℂ))) := by
  set x : ℂ := -((2 * α / Real.pi : ℝ) : ℂ) * Complex.I with hxdef
  have hπc : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hx : x ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    apply hα.ne'
    have hi := congrArg Complex.im hn
    simp [hxdef] at hi
    linarith [Real.pi_pos]
  have hx2 : x / 2 ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff] at hx ⊢
    rintro ⟨n, hn⟩
    apply hx
    refine ⟨2 * n, ?_⟩
    push_cast
    linear_combination 2 * hn
  let a : ℕ → ℂ := fun n => (-1 : ℂ) ^ (n + 1) * cotTerm x n
  have hcot : Summable (fun n : ℕ => cotTerm x n) := summable_cotTerm hx
  have ha : Summable a := by
    apply Summable.of_norm_bounded hcot.norm
    intro n
    simp [a]
  have hae : Summable (fun k => a (2 * k)) := by
    exact ha.comp_injective (by
      intro i j h
      exact Nat.mul_left_cancel (by omega) h)
  have hao : Summable (fun k => a (2 * k + 1)) := by
    exact ha.comp_injective (by
      intro i j h
      exact Nat.mul_left_cancel (by omega) (Nat.add_right_cancel h))
  have hce : Summable (fun k => cotTerm x (2 * k)) := by
    exact hcot.comp_injective (by
      intro i j h
      exact Nat.mul_left_cancel (by omega) h)
  have hco : Summable (fun k => cotTerm x (2 * k + 1)) := by
    exact hcot.comp_injective (by
      intro i j h
      exact Nat.mul_left_cancel (by omega) (Nat.add_right_cancel h))
  have he (k : ℕ) : a (2 * k) = -cotTerm x (2 * k) := by
    simp [a, pow_add, pow_mul]
  have ho (k : ℕ) : a (2 * k + 1) = cotTerm x (2 * k + 1) := by
    rw [show a (2 * k + 1) =
      (-1 : ℂ) ^ (2 * (k + 1)) * cotTerm x (2 * k + 1) by congr 2 <;> omega,
      pow_mul]
    norm_num
  have hA : (∑' n, a n) =
      2 * (∑' k, cotTerm x (2 * k + 1)) - ∑' n, cotTerm x n := by
    rw [← tsum_even_add_odd hae hao, ← tsum_even_add_odd hce hco]
    rw [show (∑' k, a (2 * k)) = -(∑' k, cotTerm x (2 * k)) by
      rw [← tsum_neg]
      exact tsum_congr he]
    rw [show (∑' k, a (2 * k + 1)) = ∑' k, cotTerm x (2 * k + 1) by
      exact tsum_congr ho]
    ring
  have hs (k : ℕ) :
      cotTerm x (2 * k + 1) = (1 / 2 : ℂ) * cotTerm (x / 2) k := by
    unfold cotTerm
    push_cast
    rw [show x - (2 * (k : ℂ) + 1 + 1) =
      2 * (x / 2 - ((k : ℂ) + 1)) by ring]
    rw [show x + (2 * (k : ℂ) + 1 + 1) =
      2 * (x / 2 + ((k : ℂ) + 1)) by ring]
    simp only [one_div, mul_inv_rev]
    norm_num
    ring
  have hO : (∑' k, cotTerm x (2 * k + 1)) =
      (1 / 2 : ℂ) * ∑' k, cotTerm (x / 2) k := by
    rw [← tsum_mul_left]
    exact tsum_congr hs
  have htsum : (∑' n, a n) =
      (Real.pi : ℂ) * (Complex.cot ((Real.pi : ℂ) * (x / 2)) -
        Complex.cot ((Real.pi : ℂ) * x)) - 1 / x := by
    rw [hA, hO]
    rw [← cot_series_rep' hx, ← cot_series_rep' hx2]
    ring
  have hpos (n : ℕ) :
      (-1 : ℂ) ^ (n : ℤ) /
        (2 * (α : ℂ) - (Real.pi : ℂ) * (n : ℂ) * Complex.I) =
      1 / ((Real.pi : ℂ) * Complex.I) *
        ((-1 : ℂ) ^ n / (x - (n : ℂ))) := by
    have hd : 2 * (α : ℂ) - (Real.pi : ℂ) * (n : ℂ) * Complex.I =
        (Real.pi : ℂ) * Complex.I * (x - (n : ℂ)) := by
      rw [hxdef]
      push_cast
      field_simp [hπc]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hd]
    simp only [zpow_natCast, div_eq_mul_inv, mul_inv_rev]
    ring
  have hneg (n : ℕ) :
      (-1 : ℂ) ^ (-(n : ℤ)) /
        (2 * (α : ℂ) - (Real.pi : ℂ) * (-(n : ℂ)) * Complex.I) =
      1 / ((Real.pi : ℂ) * Complex.I) *
        ((-1 : ℂ) ^ n / (x + (n : ℂ))) := by
    have hd : 2 * (α : ℂ) - (Real.pi : ℂ) * (-(n : ℂ)) * Complex.I =
        (Real.pi : ℂ) * Complex.I * (x + (n : ℂ)) := by
      rw [hxdef]
      push_cast
      field_simp [hπc]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hd]
    have hz : (-1 : ℂ) ^ (-(n : ℤ)) = (-1 : ℂ) ^ n := by
      simp only [zpow_neg, zpow_natCast]
      rw [← inv_pow]
      norm_num
    rw [hz]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hfinite : ∀ N : ℕ,
      (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (-1 : ℂ) ^ m /
          (2 * (α : ℂ) - (Real.pi : ℂ) * (m : ℂ) * Complex.I)) =
      1 / (2 * (α : ℂ)) + 1 / ((Real.pi : ℂ) * Complex.I) *
        ∑ n ∈ Finset.range N, a n := by
    intro N
    induction N with
    | zero =>
        simp
    | succ N ih =>
        have htop : ((N : ℤ) + 1) ∉
            Finset.Icc (-(N : ℤ) - 1) (N : ℤ) := by
          simp
        have hbot : (-(N : ℤ) - 1) ∉
            Finset.Icc (-(N : ℤ)) (N : ℤ) := by
          simp
        have hlo : -((N + 1 : ℕ) : ℤ) = -(N : ℤ) - 1 := by
          push_cast
          ring
        have hhi : ((N + 1 : ℕ) : ℤ) = (N : ℤ) + 1 := by
          norm_num
        rw [hlo, hhi]
        rw [← Finset.insert_Icc_right_eq_Icc_add_one
          (a := -(N : ℤ) - 1) (b := (N : ℤ)) (by omega)]
        rw [Finset.sum_insert htop]
        rw [← Finset.insert_Icc_left_eq_Icc_sub_one
          (a := -(N : ℤ)) (b := (N : ℤ)) (by omega)]
        rw [Finset.sum_insert hbot, ih, Finset.sum_range_succ]
        rw [← hhi, ← hlo]
        simp only [Int.cast_natCast, Int.cast_neg]
        rw [hpos (N + 1), hneg (N + 1)]
        simp only [a, cotTerm, Nat.cast_add, Nat.cast_one]
        ring
  let c0 : ℂ := (1 / (2 * (Real.pi : ℂ))) *
    ∫ ω in (0 : ℝ)..(2 * Real.pi),
      fourier_kernel α ω *
        Complex.exp (-(((0 : ℤ) : ℂ) * ((ω : ℝ) : ℂ)) * Complex.I)
  have hc0 : c0 = 1 / (2 * (α : ℂ)) := by
    dsimp [c0]
    simpa using fourier_coefficient_kernel α hα 0
  have hlim : Filter.Tendsto
      (fun N : ℕ => 1 / (2 * (α : ℂ)) +
        1 / ((Real.pi : ℂ) * Complex.I) * ∑ n ∈ Finset.range N, a n)
      Filter.atTop
      (nhds (1 / (2 * (α : ℂ)) +
        1 / ((Real.pi : ℂ) * Complex.I) * ∑' n, a n)) := by
    rw [← hc0]
    exact tendsto_const_nhds.add
      (tendsto_const_nhds.mul ha.hasSum.tendsto_sum_nat)
  rw [show (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (-1 : ℂ) ^ m /
        (2 * (α : ℂ) - (Real.pi : ℂ) * (m : ℂ) * Complex.I)) =
      (fun N : ℕ => 1 / (2 * (α : ℂ)) +
        1 / ((Real.pi : ℂ) * Complex.I) * ∑ n ∈ Finset.range N, a n) by
      funext N
      exact hfinite N]
  convert hlim using 1
  have harg1 : 2 * Complex.I * ((Real.pi : ℂ) * (x / 2)) =
      (α : ℂ) * 2 := by
    rw [hxdef]
    push_cast
    field_simp [hπc]
    ring_nf
    rw [Complex.I_sq]
    ring
  have harg2 : 2 * Complex.I * ((Real.pi : ℂ) * x) =
      (α : ℂ) * 4 := by
    rw [hxdef]
    push_cast
    field_simp [hπc]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [htsum, Complex.cot_eq_exp_ratio, Complex.cot_eq_exp_ratio, harg1, harg2,
    hxdef]
  have hE2 : Real.exp (2 * α) ≠ 1 := by
    apply ne_of_gt
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hE4 : Real.exp (4 * α) ≠ 1 := by
    apply ne_of_gt
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hD : Real.exp (2 * α) - Real.exp (-(2 * α)) ≠ 0 := by
    have h := Real.exp_lt_exp.mpr (show -(2 * α) < 2 * α by linarith)
    linarith
  have hec2 : Complex.exp ((α : ℂ) * 2) =
      ((Real.exp (2 * α) : ℝ) : ℂ) := by
    rw [show (α : ℂ) * 2 = ((2 * α : ℝ) : ℂ) by
      push_cast
      ring]
    exact (Complex.ofReal_exp _).symm
  have hec4 : Complex.exp ((α : ℂ) * 4) =
      ((Real.exp (4 * α) : ℝ) : ℂ) := by
    rw [show (α : ℂ) * 4 = ((4 * α : ℝ) : ℂ) by
      push_cast
      ring]
    exact (Complex.ofReal_exp _).symm
  have hq : Complex.exp ((α : ℂ) * 2) ≠ 1 := by
    rw [hec2]
    exact_mod_cast hE2
  have hE2sq : Real.exp (2 * α) ^ 2 ≠ 1 := by
    have hp : 1 < Real.exp (2 * α) := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    nlinarith
  have hq2 : Complex.exp ((α : ℂ) * 2) ^ 2 ≠ 1 := by
    rw [hec2]
    exact_mod_cast hE2sq
  have h1q : 1 - Complex.exp ((α : ℂ) * 2) ≠ 0 :=
    sub_ne_zero.mpr hq.symm
  have h1q2 : 1 - Complex.exp ((α : ℂ) * 2) ^ 2 ≠ 0 :=
    sub_ne_zero.mpr hq2.symm
  have hq21 : -1 + Complex.exp ((α : ℂ) * 2) ^ 2 ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr hq2
  rw [hec2, hec4, Real.exp_neg]
  rw [show 4 * α = 2 * α + 2 * α by ring, Real.exp_add]
  norm_num [Complex.inv_I, Complex.I_sq]
  field_simp [hπc, hE2, hE4, hD, hq, hq2, h1q, h1q2, hq21]
  ring_nf
  rw [Complex.I_sq]
  field_simp [h1q, h1q2, hq21] <;> ring

@[blueprint "lem:double-sum-diagonal-reindex"
  (statement := /-- Let $T \in \mathbb{N}$ and let $f : \mathbb{Z} \to \mathbb{C}$ be any function.
    Then
    \[
      \sum_{s = -T}^{T} \sum_{s' = -T}^{T} f(s - s')
        \;=\; \sum_{m = -2T}^{2T} \left(2T + 1 - \left|m\right|\right) f(m) .
    \]
    That is, in the double sum over the square $\{-T, \dots, T\}^2$ the difference $m = s - s'$
    ranges over $\{-2T, \dots, 2T\}$ and each value $m$ is attained exactly
    $2T + 1 - \left|m\right|$ times. -/)
  (proof := /-- Both sides are finite sums, so it suffices to compare, for each fixed
    $m \in \mathbb{Z}$, the total coefficient of $f(m)$.

    Partition the index square $\{-T, \dots, T\}^2$ according to the value of the difference
    $s - s'$. A pair $(s, s')$ in the square contributes to the fibre over $m$ precisely when
    $s = s' + m$ with $-T \le s' \le T$ and $-T \le s' + m \le T$, i.e. when $s'$ lies in
    $\{-T, \dots, T\} \cap \{-T - m, \dots, T - m\}$. This intersection is the set of integers
    $s'$ with $\max(-T, -T - m) \le s' \le \min(T, T - m)$, and it is nonempty exactly when
    $\left|m\right| \le 2T$.

    Assume $\left|m\right| \le 2T$. If $m \ge 0$ the constraints read
    $-T \le s' \le T - m$, giving $2T + 1 - m$ integers; if $m \le 0$ they read
    $-T - m \le s' \le T$, giving $2T + 1 + m$ integers. In both cases the fibre has exactly
    $2T + 1 - \left|m\right|$ elements. If $\left|m\right| > 2T$ the fibre is empty, and
    correspondingly $m$ does not occur in the range of summation on the right-hand side.

    Summing $f(s - s')$ over each fibre therefore contributes
    $\left(2T + 1 - \left|m\right|\right) f(m)$, and summing over the fibres, indexed by
    $m \in \{-2T, \dots, 2T\}$, gives the right-hand side. -/)
  (title := /-- Reindexing a double sum by the index difference -/)
  (latexEnv := "lemma")]
lemma double_sum_diagonal_reindex (T : ℕ) (f : ℤ → ℂ) :
    ∑ s ∈ Finset.Icc (-(T : ℤ)) (T : ℤ), ∑ s' ∈ Finset.Icc (-(T : ℤ)) (T : ℤ), f (s - s')
      = ∑ m ∈ Finset.Icc (-(2 * (T : ℤ))) (2 * (T : ℤ)),
          (((2 * (T : ℤ) + 1 - |m| : ℤ) : ℂ)) * f m := by
  rw [← Finset.sum_product']
  have hmaps : ∀ x ∈ Finset.Icc (-(T : ℤ)) (T : ℤ) ×ˢ Finset.Icc (-(T : ℤ)) (T : ℤ),
      x.1 - x.2 ∈ Finset.Icc (-(2 * (T : ℤ))) (2 * (T : ℤ)) := by
    intro x hx
    simp only [Finset.mem_product, Finset.mem_Icc] at hx ⊢
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => f (x.1 - x.2))]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hfib : ∀ x ∈ (Finset.Icc (-(T : ℤ)) (T : ℤ) ×ˢ Finset.Icc (-(T : ℤ)) (T : ℤ)).filter
        (fun x => x.1 - x.2 = m), f (x.1 - x.2) = f m := by
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const]
  have hcard : ((Finset.Icc (-(T : ℤ)) (T : ℤ) ×ˢ Finset.Icc (-(T : ℤ)) (T : ℤ)).filter
        (fun x => x.1 - x.2 = m)).card
      = (Finset.Icc (max (-(T : ℤ)) (-(T : ℤ) - m)) (min (T : ℤ) ((T : ℤ) - m))).card := by
    apply Finset.card_nbij' (fun x => x.2) (fun s' => (s' + m, s'))
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_Icc, Set.mem_setOf_eq] at hx
      simp only [Finset.coe_Icc, Set.mem_Icc]
      omega
    · intro s' hs
      simp only [Finset.coe_Icc, Set.mem_Icc] at hs
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_Icc, Set.mem_setOf_eq]
      omega
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_Icc, Set.mem_setOf_eq] at hx
      obtain ⟨_, h⟩ := hx
      have hx1 : x.2 + m = x.1 := by omega
      exact Prod.ext hx1 rfl
    · intro s' hs
      rfl
  have key : ((min (T : ℤ) ((T : ℤ) - m) + 1 - max (-(T : ℤ)) (-(T : ℤ) - m)).toNat : ℤ)
      = 2 * (T : ℤ) + 1 - |m| := by
    have hm' := Finset.mem_Icc.mp hm
    rw [Int.abs_eq_natAbs]
    omega
  rw [hcard, Int.card_Icc, nsmul_eq_mul]
  congr 1
  rw [← Int.cast_natCast, key]

@[blueprint "lem:triangular-sum-eq-cesaro"
  (statement := /-- Let $M\in\mathbb N$ and let $f:\mathbb Z\to\mathbb C$. Then the triangularly
    weighted symmetric sum of $f$ is the sum of its first $M+1$ symmetric partial sums:
    \[
      \sum_{m=-M}^{M}(M+1-|m|)f(m)
        =\sum_{j=0}^{M}\sum_{m=-j}^{j}f(m).
    \] -/)
  (proof := /-- Induct on $M$. The assertion for $M=0$ is immediate. On passing from $M$ to
    $M+1$, the weight of every old term increases by one and the two new endpoint terms have
    weight one. Thus the increment is exactly the symmetric partial sum over
    $\{-M-1,\ldots,M+1\}$, which is also the final summand on the right-hand side. -/)
  (title := /-- Triangular sums as Cesàro sums -/)
  (latexEnv := "lemma")]
lemma triangular_sum_eq_cesaro (M : ℕ) (f : ℤ → ℂ) :
    ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ((((M : ℤ) + 1 - |m| : ℤ) : ℂ)) * f m
      = ∑ j ∈ Finset.range (M + 1),
          ∑ m ∈ Finset.Icc (-(j : ℤ)) (j : ℤ), f m := by
  induction M with
  | zero => simp
  | succ M ih =>
      have hsplit : Finset.Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ) =
          insert ((M + 1 : ℕ) : ℤ)
            (insert (-((M + 1 : ℕ) : ℤ)) (Finset.Icc (-(M : ℤ)) (M : ℤ))) := by
        ext m
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hweight : ∀ m : ℤ,
          (((((M + 1 : ℕ) : ℤ) + 1 - |m| : ℤ) : ℂ)) * f m
            = (((((M : ℕ) : ℤ) + 1 - |m| : ℤ) : ℂ)) * f m + f m := by
        intro m
        push_cast
        ring
      have hold :
          (∑ m ∈ Finset.Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ),
              (((((M : ℕ) : ℤ) + 1 - |m| : ℤ) : ℂ)) * f m)
            = ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
                (((((M : ℕ) : ℤ) + 1 - |m| : ℤ) : ℂ)) * f m := by
        rw [hsplit]
        rw [Finset.sum_insert (by simp [Finset.mem_Icc]; omega),
          Finset.sum_insert (by simp [Finset.mem_Icc])]
        have hp : |((M + 1 : ℕ) : ℤ)| = ((M + 1 : ℕ) : ℤ) := abs_of_nonneg (by omega)
        have hn : |-((M + 1 : ℕ) : ℤ)| = ((M + 1 : ℕ) : ℤ) := by rw [abs_neg, hp]
        rw [hp, hn]
        push_cast
        ring
      simp_rw [hweight]
      rw [Finset.sum_add_distrib, hold, Finset.sum_range_succ, ih]

@[blueprint "lem:triangular-inverse-series"
  (statement := /-- Let $\alpha>0$. The triangular means of the symmetric alternating inverse
    series converge to the same value as its symmetric partial sums:
    \[
      \frac1{M+1}\sum_{m=-M}^{M}(M+1-|m|)
        \frac{(-1)^m}{2\alpha-i\pi m}
      \longrightarrow \frac{2}{e^{2\alpha}-e^{-2\alpha}}.
    \] -/)
  (proof := /-- By \cref{lem:triangular-sum-eq-cesaro}, the triangular sum is the sum of the first
    $M+1$ symmetric partial sums. Those partial sums converge by
    \cref{lem:alternating-inverse-series}. Cesàro's theorem therefore gives the asserted limit;
    composing with the shift $M\mapsto M+1$ supplies the normalization by $M+1$. -/)
  (title := /-- Triangular means of the alternating inverse series -/)
  (latexEnv := "lemma")]
lemma triangular_inverse_series (α : ℝ) (hα : 0 < α) :
    Filter.Tendsto
      (fun M : ℕ => ((M + 1 : ℕ) : ℝ)⁻¹ •
        ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          ((((M : ℤ) + 1 - |m| : ℤ) : ℂ)) *
            ((-1 : ℂ) ^ m /
              (2 * (α : ℂ) - (Real.pi : ℂ) * (m : ℂ) * Complex.I)))
      Filter.atTop
      (nhds (2 / (((Real.exp (2 * α) - Real.exp (-(2 * α))) : ℝ) : ℂ))) := by
  have h := (alternating_inverse_series α hα).cesaro_smul
  have hc := h.comp (Filter.tendsto_add_atTop_nat 1)
  refine hc.congr' ?_
  filter_upwards with M
  simp only [Function.comp_apply]
  rw [triangular_sum_eq_cesaro]

@[blueprint "lem:rnn-denominator-inverse-bound"
  (statement := /-- Let $\alpha>0$, let $K\geq1$, and let $m\in\mathbb Z$. Put
    $w_m=2\alpha-i\pi m$. If $|w_m/K|\leq1/2$, then
    \[
      \left|\frac1{K D_m}-\frac1{w_m}\right|\leq\frac2K,
    \]
    where $D_m$ is the resolvent denominator of \cref{def:rnn-denominator}. -/)
  (proof := /-- Set $z=-w_m/K$ and
    $e=e^z-1-z$. The quadratic exponential remainder bound gives $|e|\leq|z|^2$.
    Since $|z|\leq1/2$, the identity $D_m=-z-e$ and the reverse triangle inequality imply
    $|D_m|\geq |z|/2$. Moreover $w_m\neq0$ because its real part is $2\alpha>0$.
    The exact algebraic identity
    \[
      \frac1{K D_m}-\frac1{w_m}=\frac{e}{D_mw_m}
    \]
    now yields the bound after using $|w_m|=K|z|$. -/)
  (title := /-- Uniform linearization bound for the resolvent denominator -/)
  (latexEnv := "lemma")]
lemma rnn_denominator_inverse_bound (α : ℝ) (hα : 0 < α) (K : ℕ) (hK : 1 ≤ K)
    (m : ℤ)
    (hsmall : ‖(2 * (α : ℂ) - (Real.pi : ℂ) * (m : ℂ) * Complex.I) /
      (K : ℂ)‖ ≤ (1 / 2 : ℝ)) :
    ‖1 / ((K : ℂ) * rnn_denominator α K m) -
        1 / (2 * (α : ℂ) - (Real.pi : ℂ) * (m : ℂ) * Complex.I)‖
      ≤ 2 / (K : ℝ) := by
  let w : ℂ := 2 * (α : ℂ) - (Real.pi : ℂ) * (m : ℂ) * Complex.I
  let z : ℂ := -w / (K : ℂ)
  let e : ℂ := Complex.exp z - 1 - z
  have hKn : K ≠ 0 := Nat.ne_of_gt hK
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hKn
  have hKc : (K : ℂ) ≠ 0 := by exact_mod_cast hKn
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hw : w ≠ 0 := by
    intro hw
    have hre := congrArg Complex.re hw
    simp [w] at hre
    linarith
  have hzpos : 0 < ‖z‖ := by
    rw [norm_pos_iff]
    simp [z, hw, hKn]
  have hzsmall : ‖z‖ ≤ (1 / 2 : ℝ) := by
    calc
      ‖z‖ = ‖w / (K : ℂ)‖ := by simp [z]
      _ ≤ (1 / 2 : ℝ) := by simpa [w] using hsmall
  have hzone : ‖z‖ ≤ 1 := by linarith
  have he : ‖e‖ ≤ ‖z‖ ^ 2 := by
    simpa [e] using Complex.norm_exp_sub_one_sub_id_le hzone
  have hD : rnn_denominator α K m = -z - e := by
    simp only [rnn_denominator, e]
    have hexp :
        (((-(2 * α) / K : ℝ) : ℂ) + ((Real.pi * m / K : ℝ) : ℂ) * Complex.I)
          = z := by
      simp [z, w]
      field_simp
      ring
    rw [hexp]
    ring
  have hDlower : ‖z‖ / 2 ≤ ‖rnn_denominator α K m‖ := by
    rw [hD]
    calc
      ‖z‖ / 2 ≤ ‖-z‖ - ‖e‖ := by
        rw [norm_neg]
        nlinarith [norm_nonneg z]
      _ ≤ ‖-z - e‖ := norm_sub_norm_le (-z) e
  have hDpos : 0 < ‖rnn_denominator α K m‖ := lt_of_lt_of_le (half_pos hzpos) hDlower
  have hDne : rnn_denominator α K m ≠ 0 := norm_pos_iff.mp hDpos
  have hw_norm : ‖w‖ = (K : ℝ) * ‖z‖ := by
    simp [z, norm_div, hK0]
    field_simp
  have hKD : (K : ℂ) * rnn_denominator α K m = w - (K : ℂ) * e := by
    rw [hD]
    simp only [z]
    field_simp [hKc]
  have hsub : w - (K : ℂ) * e ≠ 0 := by
    rw [← hKD]
    exact mul_ne_zero hKc hDne
  have halg :
      1 / ((K : ℂ) * rnn_denominator α K m) - 1 / w =
        e / (rnn_denominator α K m * w) := by
    rw [hKD]
    field_simp [hw, hDne, hsub]
    linear_combination e * hKD
  change ‖1 / ((K : ℂ) * rnn_denominator α K m) - 1 / w‖ ≤ _
  rw [halg, norm_div, norm_mul, div_le_iff₀ (mul_pos hDpos (norm_pos_iff.mpr hw))]
  calc
    ‖e‖ ≤ ‖z‖ ^ 2 := he
    _ = (2 / (K : ℝ)) * (‖z‖ / 2) * ((K : ℝ) * ‖z‖) := by
      field_simp
    _ ≤ (2 / (K : ℝ)) * ‖rnn_denominator α K m‖ * ‖w‖ := by
      rw [hw_norm]
      gcongr
    _ = (2 / (K : ℝ)) *
        (‖rnn_denominator α K m‖ * ‖w‖) := by ring

@[blueprint "lem:triangular-sum-norm-bound"
  (statement := /-- Let $M\in\mathbb N$, let $C\geq0$, and let $g:\mathbb Z\to\mathbb C$ satisfy
    $|g(m)|\leq C$ for every $|m|\leq M$. Then
    \[
      \left|\sum_{m=-M}^{M}(M+1-|m|)g(m)\right|
        \leq 2(M+1)^2C.
    \] -/)
  (proof := /-- On the interval $[-M,M]$, every triangular weight is nonnegative and at most
    $M+1$. Hence every summand has norm at most $(M+1)C$. The interval has $2M+1\leq2(M+1)$
    elements, so the triangle inequality gives the stated bound. -/)
  (title := /-- Norm bound for a triangularly weighted sum -/)
  (latexEnv := "lemma")]
lemma triangular_sum_norm_bound (M : ℕ) (g : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ‖g m‖ ≤ C) :
    ‖∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ((((M : ℤ) + 1 - |m| : ℤ) : ℂ)) * g m‖
      ≤ 2 * ((M + 1 : ℕ) : ℝ) ^ 2 * C := by
  have hcard : (Finset.Icc (-(M : ℤ)) (M : ℤ)).card = 2 * M + 1 := by
    rw [Int.card_Icc]
    omega
  calc
    ‖∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ((((M : ℤ) + 1 - |m| : ℤ) : ℂ)) * g m‖
        ≤ ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            ‖((((M : ℤ) + 1 - |m| : ℤ) : ℂ)) * g m‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ((M + 1 : ℕ) : ℝ) * C := by
      refine Finset.sum_le_sum fun m hm => ?_
      rw [norm_mul]
      have hm' := Finset.mem_Icc.mp hm
      have habs : |m| ≤ (M : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
      have habs0 : 0 ≤ |m| := abs_nonneg m
      have hw0 : 0 ≤ (M : ℤ) + 1 - |m| := by omega
      have hwle : (M : ℤ) + 1 - |m| ≤ (M : ℤ) + 1 := by omega
      have hn : ‖((((M : ℤ) + 1 - |m| : ℤ) : ℂ))‖ ≤ ((M + 1 : ℕ) : ℝ) := by
        rw [Complex.norm_intCast, abs_of_nonneg (by exact_mod_cast hw0)]
        exact_mod_cast hwle
      exact mul_le_mul hn (hg m hm) (norm_nonneg _) (by positivity)
    _ = ((2 * M + 1 : ℕ) : ℝ) * (((M + 1 : ℕ) : ℝ) * C) := by
      rw [← hcard]
      simp
    _ ≤ 2 * ((M + 1 : ℕ) : ℝ) ^ 2 * C := by
      push_cast
      nlinarith

@[blueprint "lem:rnn-denominator-triangular-limit"
  (statement := /-- Let $\alpha>0$, and let $T(n),K(n)\to\infty$ with $K(n)\geq1$ and
    $(2T(n)+1)/K(n)\to0$. Then
    \[
      \frac1{2T(n)+1}\sum_{m=-2T(n)}^{2T(n)}(2T(n)+1-|m|)
      \frac{(-1)^m}{K(n)D_m}
      \longrightarrow\frac2{e^{2\alpha}-e^{-2\alpha}}.
    \] -/)
  (proof := /-- The triangular sum with $1/(2\alpha-i\pi m)$ in place of $1/(K D_m)$
    converges by \cref{lem:triangular-inverse-series}, after composition with $2T(n)\to\infty$.
    Since $(2T(n)+1)/K(n)\to0$ and $K(n)\to\infty$, the scaled frequencies satisfy
    $|(2\alpha-i\pi m)/K(n)|\leq1/2$ eventually, uniformly for $|m|\leq2T(n)$.
    The pointwise difference is then at most $2/K(n)$ by
    \cref{lem:rnn-denominator-inverse-bound}. Applying
    \cref{lem:triangular-sum-norm-bound} and dividing by $2T(n)+1$ bounds the normalized error by
    $4(2T(n)+1)/K(n)$, which tends to zero. -/)
  (title := /-- Limit of the triangular resolvent sum -/)
  (latexEnv := "lemma")]
lemma rnn_denominator_triangular_limit (α : ℝ) (hα : 0 < α) (T K : ℕ → ℕ)
    (hK1 : ∀ n, 1 ≤ K n)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop)
    (hK : Filter.Tendsto K Filter.atTop Filter.atTop)
    (hSK : Filter.Tendsto (fun n => (2 * (T n : ℝ) + 1) / (K n : ℝ))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ((2 * T n + 1 : ℕ) : ℝ)⁻¹ •
        ∑ m ∈ Finset.Icc (-(2 * (T n : ℤ))) (2 * (T n : ℤ)),
          (((2 * (T n : ℤ) + 1 - |m| : ℤ) : ℂ)) *
            ((-1 : ℂ) ^ m /
              ((K n : ℂ) * rnn_denominator α (K n) m)))
      Filter.atTop
      (nhds (2 / (((Real.exp (2 * α) - Real.exp (-(2 * α))) : ℝ) : ℂ))) := by
  let M : ℕ → ℕ := fun n => 2 * T n
  let A : ℕ → ℂ := fun n => ((M n + 1 : ℕ) : ℝ)⁻¹ •
    ∑ m ∈ Finset.Icc (-(M n : ℤ)) (M n : ℤ),
      ((((M n : ℤ) + 1 - |m| : ℤ) : ℂ)) *
        ((-1 : ℂ) ^ m / (2 * (α : ℂ) - (Real.pi : ℂ) * (m : ℂ) * Complex.I))
  let B : ℕ → ℂ := fun n => ((M n + 1 : ℕ) : ℝ)⁻¹ •
    ∑ m ∈ Finset.Icc (-(M n : ℤ)) (M n : ℤ),
      ((((M n : ℤ) + 1 - |m| : ℤ) : ℂ)) *
        ((-1 : ℂ) ^ m / ((K n : ℂ) * rnn_denominator α (K n) m))
  have hM : Filter.Tendsto M Filter.atTop Filter.atTop := by
    simpa [M] using hT.const_mul_atTop' (show (0 : ℕ) < 2 by norm_num)
  have hA : Filter.Tendsto A Filter.atTop
      (nhds (2 / (((Real.exp (2 * α) - Real.exp (-(2 * α))) : ℝ) : ℂ))) := by
    have hc := (triangular_inverse_series α hα).comp hM
    refine hc.congr' ?_
    filter_upwards with n
    rfl
  have hKreal : Filter.Tendsto (fun n => (K n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hK
  have hKinv : Filter.Tendsto (fun n => ((K n : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
    hKreal.inv_tendsto_atTop
  have hratio : Filter.Tendsto
      (fun n => (2 * (T n : ℝ) + 1) / (K n : ℝ) - (K n : ℝ)⁻¹)
      Filter.atTop (nhds 0) := by simpa using hSK.sub hKinv
  have hcα : Filter.Tendsto (fun _n : ℕ => 2 * α) Filter.atTop (nhds (2 * α)) :=
    tendsto_const_nhds
  have hcπ : Filter.Tendsto (fun _n : ℕ => Real.pi) Filter.atTop (nhds Real.pi) :=
    tendsto_const_nhds
  have hfreq : Filter.Tendsto
      (fun n => 2 * α * (K n : ℝ)⁻¹ + Real.pi *
        ((2 * (T n : ℝ) + 1) / (K n : ℝ) - (K n : ℝ)⁻¹))
      Filter.atTop (nhds 0) :=
    by simpa using (hcα.mul hKinv).add (hcπ.mul hratio)
  have hfreq_small : ∀ᶠ n in Filter.atTop,
      2 * α * (K n : ℝ)⁻¹ + Real.pi *
        ((2 * (T n : ℝ) + 1) / (K n : ℝ) - (K n : ℝ)⁻¹) < 1 / 2 :=
    hfreq.eventually (Iio_mem_nhds (by norm_num))
  have herr_bound : ∀ᶠ n in Filter.atTop,
      ‖B n - A n‖ ≤ 4 * ((M n + 1 : ℕ) : ℝ) / (K n : ℝ) := by
    filter_upwards [hfreq_small] with n hn
    have hKn := hK1 n
    have hKn0 : (K n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hKn)
    have hKnpos : (0 : ℝ) < K n := by exact_mod_cast hKn
    have hpoint : ∀ m ∈ Finset.Icc (-(M n : ℤ)) (M n : ℤ),
        ‖(-1 : ℂ) ^ m *
          (1 / ((K n : ℂ) * rnn_denominator α (K n) m) -
            1 / (2 * (α : ℂ) - (Real.pi : ℂ) * (m : ℂ) * Complex.I))‖
          ≤ 2 / (K n : ℝ) := by
      intro m hm
      have hm' := Finset.mem_Icc.mp hm
      have habs : |m| ≤ (M n : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
      have hsmall : ‖(2 * (α : ℂ) - (Real.pi : ℂ) * (m : ℂ) * Complex.I) /
          (K n : ℂ)‖ ≤ (1 / 2 : ℝ) := by
        rw [norm_div, Complex.norm_natCast]
        calc
          ‖2 * (α : ℂ) - (Real.pi : ℂ) * (m : ℂ) * Complex.I‖ / (K n : ℝ)
              ≤ (2 * α + Real.pi * |m|) / (K n : ℝ) := by
            gcongr
            calc
              ‖2 * (α : ℂ) - (Real.pi : ℂ) * (m : ℂ) * Complex.I‖
                  ≤ ‖2 * (α : ℂ)‖ + ‖(Real.pi : ℂ) * (m : ℂ) * Complex.I‖ := norm_sub_le _ _
              _ = 2 * α + Real.pi * |m| := by
                simp [norm_mul, abs_of_pos hα, abs_of_pos Real.pi_pos]
          _ ≤ (2 * α + Real.pi * (M n : ℝ)) / (K n : ℝ) := by
            gcongr
            exact_mod_cast habs
          _ = 2 * α * (K n : ℝ)⁻¹ + Real.pi *
              ((2 * (T n : ℝ) + 1) / (K n : ℝ) - (K n : ℝ)⁻¹) := by
            simp [M]
            field_simp
            ring
          _ ≤ 1 / 2 := le_of_lt hn
      have hd := rnn_denominator_inverse_bound α hα (K n) hKn m hsmall
      simpa [norm_mul] using hd
    have hraw := triangular_sum_norm_bound (M n)
      (fun m => (-1 : ℂ) ^ m *
        (1 / ((K n : ℂ) * rnn_denominator α (K n) m) -
          1 / (2 * (α : ℂ) - (Real.pi : ℂ) * (m : ℂ) * Complex.I)))
      (2 / (K n : ℝ)) (by positivity) hpoint
    have hSpos : (0 : ℝ) < ((M n + 1 : ℕ) : ℝ) := by positivity
    calc
      ‖B n - A n‖ = ‖((M n + 1 : ℕ) : ℝ)⁻¹ •
          ∑ m ∈ Finset.Icc (-(M n : ℤ)) (M n : ℤ),
            ((((M n : ℤ) + 1 - |m| : ℤ) : ℂ)) *
              ((-1 : ℂ) ^ m *
                (1 / ((K n : ℂ) * rnn_denominator α (K n) m) -
                  1 / (2 * (α : ℂ) - (Real.pi : ℂ) * (m : ℂ) * Complex.I)))‖ := by
        simp only [A, B]
        rw [← smul_sub, ← Finset.sum_sub_distrib]
        apply congrArg norm
        apply congrArg (fun z : ℂ => ((M n + 1 : ℕ) : ℝ)⁻¹ • z)
        apply Finset.sum_congr rfl
        intro m hm
        ring
      _ ≤ ((M n + 1 : ℕ) : ℝ)⁻¹ *
          (2 * ((M n + 1 : ℕ) : ℝ) ^ 2 * (2 / (K n : ℝ))) := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hSpos]
        exact mul_le_mul_of_nonneg_left hraw (by positivity)
      _ = 4 * ((M n + 1 : ℕ) : ℝ) / (K n : ℝ) := by
        field_simp
        ring
  have hbound_zero : Filter.Tendsto
      (fun n => 4 * ((M n + 1 : ℕ) : ℝ) / (K n : ℝ)) Filter.atTop (nhds 0) := by
    have hc4 : Filter.Tendsto (fun _n : ℕ => (4 : ℝ)) Filter.atTop (nhds 4) :=
      tendsto_const_nhds
    have hc := hc4.mul hSK
    simpa only [mul_zero] using hc.congr' (by
      filter_upwards with n
      simp [M]
      ring)
  have herr : Filter.Tendsto (fun n => B n - A n) Filter.atTop (nhds 0) :=
    squeeze_zero_norm' herr_bound hbound_zero
  have hB := herr.add hA
  simpa [A, B, M] using hB

@[blueprint "lem:filter-energy-diagonal-sum"
  (statement := /-- Let $\alpha>0$, $T\in\mathbb N$, and $K\geq1$. With
    $\beta=e^{-\alpha}(e^{2\alpha}-e^{-2\alpha})/(2K)$, the energy of the filter satisfies
    \[
      \left(\sum_{k=0}^{\infty}|c_k|^2:\mathbb C\right)
      =\beta^2\sum_{m=-2T}^{2T}(2T+1-|m|)\frac{(-1)^m}{D_m}.
    \] -/)
  (proof := /-- Apply \cref{lem:filter-sq-double-sum}. By \cref{def:rnn-coefficient} and
    \cref{def:rnn-coefficient-scale}, the product $b_s\overline{b_{s'}}$ is
    $\beta^2(-1)^{s-s'}$; the equality of the two sign exponents follows because their difference
    is the even integer $2s'$. The summand therefore depends only on $m=s-s'$, so
    \cref{lem:double-sum-diagonal-reindex} gives the displayed triangular sum. -/)
  (title := /-- Diagonal form of the filter energy -/)
  (latexEnv := "lemma")]
lemma filter_energy_diagonal_sum (α : ℝ) (hα : 0 < α) (T K : ℕ) (hK : 1 ≤ K) :
    ((∑' k : ℕ, ‖rnn_filter α T K k‖ ^ 2 : ℝ) : ℂ) =
      ((rnn_coefficient_scale α K : ℝ) : ℂ) ^ 2 *
        ∑ m ∈ Finset.Icc (-(2 * (T : ℤ))) (2 * (T : ℤ)),
          (((2 * (T : ℤ) + 1 - |m| : ℤ) : ℂ)) *
            ((-1 : ℂ) ^ m / rnn_denominator α K m) := by
  have hsign : ∀ s s' : ℤ, (-1 : ℂ) ^ s * (-1 : ℂ) ^ s' = (-1 : ℂ) ^ (s - s') := by
    intro s s'
    calc
      (-1 : ℂ) ^ s * (-1 : ℂ) ^ s' = (-1 : ℂ) ^ (s + s') :=
        (zpow_add₀ (by norm_num) s s').symm
      _ = (-1 : ℂ) ^ ((s - s') + 2 * s') := by congr 1 <;> omega
      _ = (-1 : ℂ) ^ (s - s') * (-1 : ℂ) ^ (2 * s') :=
        zpow_add₀ (by norm_num) (s - s') (2 * s')
      _ = (-1 : ℂ) ^ (s - s') := by
        rw [zpow_mul]
        norm_num
  rw [filter_sq_double_sum α hα T K hK]
  calc
    (∑ s ∈ Finset.Icc (-(T : ℤ)) (T : ℤ),
        ∑ s' ∈ Finset.Icc (-(T : ℤ)) (T : ℤ),
          rnn_coefficient α K s * (starRingEnd ℂ) (rnn_coefficient α K s') /
            rnn_denominator α K (s - s')) =
      ∑ s ∈ Finset.Icc (-(T : ℤ)) (T : ℤ),
        ∑ s' ∈ Finset.Icc (-(T : ℤ)) (T : ℤ),
          (((rnn_coefficient_scale α K : ℝ) : ℂ) ^ 2 *
            ((-1 : ℂ) ^ (s - s') / rnn_denominator α K (s - s'))) := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro s' hs'
      simp only [rnn_coefficient, map_mul]
      have hscale : (starRingEnd ℂ) (((rnn_coefficient_scale α K : ℝ) : ℂ)) =
          ((rnn_coefficient_scale α K : ℝ) : ℂ) := by simp
      have hpow : (starRingEnd ℂ) ((-1 : ℂ) ^ s') = (-1 : ℂ) ^ s' := by
        change star ((-1 : ℂ) ^ s') = (-1 : ℂ) ^ s'
        rw [star_zpow₀]
        norm_num
      rw [hscale, hpow]
      calc
        ((rnn_coefficient_scale α K : ℂ) * (-1 : ℂ) ^ s) *
              ((rnn_coefficient_scale α K : ℂ) * (-1 : ℂ) ^ s') /
            rnn_denominator α K (s - s') =
          (rnn_coefficient_scale α K : ℂ) ^ 2 *
            (((-1 : ℂ) ^ s * (-1 : ℂ) ^ s') / rnn_denominator α K (s - s')) := by ring
        _ = (rnn_coefficient_scale α K : ℂ) ^ 2 *
            ((-1 : ℂ) ^ (s - s') / rnn_denominator α K (s - s')) := by rw [hsign]
    _ = ∑ m ∈ Finset.Icc (-(2 * (T : ℤ))) (2 * (T : ℤ)),
        (((2 * (T : ℤ) + 1 - |m| : ℤ) : ℂ)) *
          ((((rnn_coefficient_scale α K : ℝ) : ℂ) ^ 2 *
            ((-1 : ℂ) ^ m / rnn_denominator α K m))) :=
      double_sum_diagonal_reindex T (fun m =>
        ((rnn_coefficient_scale α K : ℝ) : ℂ) ^ 2 *
          ((-1 : ℂ) ^ m / rnn_denominator α K m))
    _ = ((rnn_coefficient_scale α K : ℝ) : ℂ) ^ 2 *
        ∑ m ∈ Finset.Icc (-(2 * (T : ℤ))) (2 * (T : ℤ)),
          (((2 * (T : ℤ) + 1 - |m| : ℤ) : ℂ)) *
            ((-1 : ℂ) ^ m / rnn_denominator α K m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring

@[blueprint "lem:quadratic-term-asymptotics"
  (statement := /-- Let $\alpha \in \mathbb{R}$ with $\alpha > 0$. Let
    $T, K : \mathbb{N} \to \mathbb{N}$ be sequences with $K(n) \ge 1$ for every $n$, with
    $T(n) \to \infty$ and $K(n) \to \infty$, and with
    $S(n) / K(n) \to 0$, where $S(n) = 2 T(n) + 1$. Then, with $c$ the filter of
    \cref{def:rnn-filter},
    \[
      \sum_{k = 0}^{\infty} \left|c_k\right|^2
        \;\sim\; \frac{e^{-2\alpha}\left(e^{2\alpha} - e^{-2\alpha}\right)}{2}
                 \cdot \frac{S(n)}{K(n)}
      \qquad (n \to \infty),
    \]
    the filter being taken with parameters $\left(\alpha, T(n), K(n)\right)$, and $\sim$ denoting
    asymptotic equivalence along the filter of large $n$. -/)
  (proof := /-- Put $S(n)=2T(n)+1$, $\Delta=e^{2\alpha}-e^{-2\alpha}$, let
    $\beta(n)=e^{-\alpha}\Delta/(2K(n))$ be the scale of
    \cref{def:rnn-coefficient-scale}, and set
    $L=2/\Delta$. Since $\alpha>0$, both $\Delta$ and
    $\kappa=e^{-2\alpha}\Delta/2$ are strictly positive.

    By \cref{lem:filter-energy-diagonal-sum}, for every $n$,
    \[
      \sum_k |c_k|^2
        =\beta(n)^2\sum_{m=-2T(n)}^{2T(n)}
          \bigl(S(n)-|m|\bigr)\frac{(-1)^m}{D_m}.
    \]
    Define the normalized triangular sum
    \[
      Q_n=\frac1{S(n)}\sum_{m=-2T(n)}^{2T(n)}
        \bigl(S(n)-|m|\bigr)\frac{(-1)^m}{K(n)D_m}.
    \]
    The hypotheses $T(n),K(n)\to\infty$ and $S(n)/K(n)\to0$ allow
    \cref{lem:rnn-denominator-triangular-limit} to be applied, and it gives $Q_n\to L$.

    The preceding exact energy identity and the definitions of $\beta$, $\kappa$, and $L$ give,
    for every $n$,
    \[
      \frac{\sum_k|c_k|^2}{\kappa S(n)/K(n)}=\frac{Q_n}{L}.
    \]
    Here $K(n)\geq1$, $S(n)>0$, and $\Delta>0$, so every denominator is nonzero. Since
    $Q_n\to L$ and $L\neq0$, the right-hand side tends to $1$. The ratio characterization of
    asymptotic equivalence therefore yields
    $\sum_k|c_k|^2\sim\kappa S(n)/K(n)$, which is the asserted formula. -/)
  (title := /-- Asymptotics of the energy of the filter -/)
  (latexEnv := "lemma")]
lemma quadratic_term_asymptotics (α : ℝ) (hα : 0 < α) (T K : ℕ → ℕ)
    (hK1 : ∀ n, 1 ≤ K n)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop)
    (hK : Filter.Tendsto K Filter.atTop Filter.atTop)
    (hSK : Filter.Tendsto (fun n => (2 * (T n : ℝ) + 1) / (K n : ℝ)) Filter.atTop (nhds 0)) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n => ∑' k : ℕ, ‖rnn_filter α (T n) (K n) k‖ ^ 2)
      (fun n => Real.exp (-(2 * α)) * (Real.exp (2 * α) - Real.exp (-(2 * α))) / 2
                  * ((2 * (T n : ℝ) + 1) / (K n : ℝ))) := by
  let Δ : ℝ := Real.exp (2 * α) - Real.exp (-(2 * α))
  let κ : ℝ := Real.exp (-(2 * α)) * Δ / 2
  let L : ℂ := 2 / (Δ : ℂ)
  let Q : ℕ → ℂ := fun n => ((2 * T n + 1 : ℕ) : ℝ)⁻¹ •
    ∑ m ∈ Finset.Icc (-(2 * (T n : ℤ))) (2 * (T n : ℤ)),
      (((2 * (T n : ℤ) + 1 - |m| : ℤ) : ℂ)) *
        ((-1 : ℂ) ^ m / ((K n : ℂ) * rnn_denominator α (K n) m))
  have hΔ : 0 < Δ := by
    dsimp [Δ]
    rw [sub_pos]
    apply Real.exp_lt_exp.mpr
    linarith
  have hκ : 0 < κ := by
    dsimp [κ]
    positivity
  have hQ : Filter.Tendsto Q Filter.atTop (nhds L) := by
    simpa only [Q, L, Δ] using
      rnn_denominator_triangular_limit α hα T K hK1 hT hK hSK
  have hQone : Filter.Tendsto (fun n => Q n / L) Filter.atTop (nhds 1) := by
    have hc := hQ.div_const L
    simpa [L, hΔ.ne'] using hc
  have hcomplex : ∀ n,
      (((∑' k : ℕ, ‖rnn_filter α (T n) (K n) k‖ ^ 2) /
        (κ * ((2 * (T n : ℝ) + 1) / (K n : ℝ))) : ℝ) : ℂ) = Q n / L := by
    intro n
    have hKn := hK1 n
    have hKnN : K n ≠ 0 := Nat.ne_of_gt hKn
    have hKnR : (K n : ℝ) ≠ 0 := by exact_mod_cast hKnN
    have hKnC : (K n : ℂ) ≠ 0 := by exact_mod_cast hKnN
    have hSnR : (2 * (T n : ℝ) + 1) ≠ 0 := by positivity
    have hSnN : 2 * T n + 1 ≠ 0 := by omega
    have hcastK : (((K n : ℝ) : ℂ)) = (K n : ℂ) := by norm_num
    have hexpR : Real.exp (-α) ^ 2 = Real.exp (-(2 * α)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hexpC : ((Real.exp (-α) : ℝ) : ℂ) ^ 2 =
        ((Real.exp (-(2 * α)) : ℝ) : ℂ) := by exact_mod_cast hexpR
    have hsum :
        (∑ m ∈ Finset.Icc (-(2 * (T n : ℤ))) (2 * (T n : ℤ)),
          (((2 * (T n : ℤ) + 1 - |m| : ℤ) : ℂ)) *
            ((-1 : ℂ) ^ m / ((K n : ℂ) * rnn_denominator α (K n) m))) =
          1 / (K n : ℂ) *
            ∑ m ∈ Finset.Icc (-(2 * (T n : ℤ))) (2 * (T n : ℤ)),
              (((2 * (T n : ℤ) + 1 - |m| : ℤ) : ℂ)) *
                ((-1 : ℂ) ^ m / rnn_denominator α (K n) m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      field_simp [hKnC]
    have hscaleC :
        (((Real.exp (-α) : ℝ) : ℂ) * (Δ : ℂ) / (2 * (K n : ℂ))) ^ 2 =
          ((Real.exp (-(2 * α)) : ℝ) : ℂ) * (Δ : ℂ) ^ 2 /
            (4 * (K n : ℂ) ^ 2) := by
      calc
        (((Real.exp (-α) : ℝ) : ℂ) * (Δ : ℂ) / (2 * (K n : ℂ))) ^ 2 =
            (((Real.exp (-α) : ℝ) : ℂ) ^ 2 * (Δ : ℂ) ^ 2) /
              (4 * (K n : ℂ) ^ 2) := by ring
        _ = ((Real.exp (-(2 * α)) : ℝ) : ℂ) * (Δ : ℂ) ^ 2 /
              (4 * (K n : ℂ) ^ 2) := by rw [hexpC]
    rw [Complex.ofReal_div, filter_energy_diagonal_sum α hα (T n) (K n) hKn]
    simp only [Q, L, κ, rnn_coefficient_scale, Complex.ofReal_div,
      Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.real_smul]
    rw [show Real.exp (2 * α) - Real.exp (-(2 * α)) = Δ by rfl]
    rw [hcastK]
    rw [hsum, hscaleC]
    field_simp [hKnR, hKnC, hSnR, hSnN, hΔ.ne']
    norm_num
    ring
  have hv : ∀ᶠ n in Filter.atTop,
      κ * ((2 * (T n : ℝ) + 1) / (K n : ℝ)) ≠ 0 := by
    filter_upwards with n
    have hKn : (0 : ℝ) < K n := by exact_mod_cast hK1 n
    exact mul_ne_zero hκ.ne' (div_ne_zero (by positivity) hKn.ne')
  rw [Asymptotics.isEquivalent_iff_tendsto_one hv]
  have hc : Filter.Tendsto
      (fun n => ((((∑' k : ℕ, ‖rnn_filter α (T n) (K n) k‖ ^ 2) /
        (κ * ((2 * (T n : ℝ) + 1) / (K n : ℝ))) : ℝ) : ℂ)))
      Filter.atTop (nhds 1) :=
    hQone.congr' (Filter.Eventually.of_forall fun n => (hcomplex n).symm)
  have hr := (Complex.continuous_re.tendsto 1).comp hc
  have hr' : Filter.Tendsto
      (fun n => (∑' k : ℕ, ‖rnn_filter α (T n) (K n) k‖ ^ 2) /
        (κ * ((2 * (T n : ℝ) + 1) / (K n : ℝ)))) Filter.atTop (nhds 1) := by
    simpa only [Function.comp_def, Complex.ofReal_re, Complex.one_re] using hr
  change Filter.Tendsto
    (fun n => (∑' k : ℕ, ‖rnn_filter α (T n) (K n) k‖ ^ 2) /
      (Real.exp (-(2 * α)) * (Real.exp (2 * α) - Real.exp (-(2 * α))) / 2 *
        ((2 * (T n : ℝ) + 1) / (K n : ℝ)))) Filter.atTop (nhds 1)
  simpa only [κ, Δ] using hr'

@[blueprint "thm:upper-bound-of-the-error"
  (statement := /-- \emph{(Upper bound of the error.)} Let $\alpha \in \mathbb{R}$ with
    $\alpha > 0$. Let $T, K : \mathbb{N} \to \mathbb{N}$ be sequences with $K(n) \ge 1$ for every
    $n$, with $T(n) \to \infty$ and $K(n) \to \infty$, and with $S(n)/K(n) \to 0$, where
    $S(n) = 2 T(n) + 1$ is the hidden state size. For each $n$, let $c^{(n)}$ be the
    linear-recurrent-network filter of \cref{def:rnn-filter} with parameters
    $\left(\alpha, T(n), K(n)\right)$, and let $d^{(n)}$ be the shift-$K(n)$ filter of
    \cref{def:shift-filter}. Then, for the white-noise time-domain loss of
    \cref{def:white-noise-time-loss},
    \[
      \mathcal{L}_{\mathrm{time}}\left(c^{(n)}, d^{(n)}\right) - 1
        \;\sim\; -\,\frac{e^{-2\alpha}\left(e^{2\alpha} - e^{-2\alpha}\right)}{2}
                 \cdot \frac{S(n)}{K(n)}
      \qquad (n \to \infty),
    \]
    equivalently
    $\mathcal{L}_{\mathrm{time}}\left(c^{(n)}, d^{(n)}\right) = 1 - \frac{e^{-2\alpha}\left(e^{2\alpha} - e^{-2\alpha}\right)}{2}\frac{S(n)}{K(n)} + o\!\left(\frac{S(n)}{K(n)}\right)$. -/)
  (proof := /-- Set
    $\kappa=e^{-2\alpha}\left(e^{2\alpha}-e^{-2\alpha}\right)/2$ and
    $S(n)=2T(n)+1$. By \cref{lem:quadratic-term-asymptotics},
    \[
      \sum_{k=0}^{\infty}\left|c_k^{(n)}\right|^2-\kappa\frac{S(n)}{K(n)}
        =o\!\left(\kappa\frac{S(n)}{K(n)}\right).
    \]
    Little-$o$ is unchanged when the comparison function is negated, so the same difference is
    $o\!\left(-\kappa S(n)/K(n)\right)$.

    For every $n$, \cref{lem:loss-expansion} and the hypothesis $K(n)\geq1$ give
    \[
      \mathcal{L}_{\mathrm{time}}\left(c^{(n)},d^{(n)}\right)-1
        =-2\operatorname{Re}\left(c_{K(n)}^{(n)}\right)
          +\sum_{k=0}^{\infty}\left|c_k^{(n)}\right|^2.
    \]
    By \cref{lem:cross-term},
    $\operatorname{Re}\left(c_{K(n)}^{(n)}\right)=\kappa S(n)/K(n)$. Since $K(n)\geq1$,
    its real cast is nonzero, and the preceding identities yield
    \[
      \bigl(\mathcal{L}_{\mathrm{time}}(c^{(n)},d^{(n)})-1\bigr)
        -\left(-\kappa\frac{S(n)}{K(n)}\right)
      =\sum_{k=0}^{\infty}\left|c_k^{(n)}\right|^2-\kappa\frac{S(n)}{K(n)}.
    \]
    Eventual equality of these remainders, together with the little-$o$ estimate above, is exactly
    the asserted asymptotic equivalence. -/)
  (title := /-- Upper bound of the error -/)
  (latexEnv := "theorem")]
theorem upper_bound_of_the_error (α : ℝ) (hα : 0 < α) (T K : ℕ → ℕ)
    (hK1 : ∀ n, 1 ≤ K n)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop)
    (hK : Filter.Tendsto K Filter.atTop Filter.atTop)
    (hSK : Filter.Tendsto (fun n => (2 * (T n : ℝ) + 1) / (K n : ℝ)) Filter.atTop (nhds 0)) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n => white_noise_time_loss (rnn_filter α (T n) (K n)) (shift_filter (K n)) - 1)
      (fun n => -(Real.exp (-(2 * α)) * (Real.exp (2 * α) - Real.exp (-(2 * α))) / 2)
                  * ((2 * (T n : ℝ) + 1) / (K n : ℝ))) := by
  have hQ := quadratic_term_asymptotics α hα T K hK1 hT hK hSK
  unfold Asymptotics.IsEquivalent at hQ ⊢
  refine hQ.neg_right.congr' ?_ (Filter.Eventually.of_forall fun n => by dsimp; ring)
  filter_upwards with n
  rw [Pi.sub_apply, Pi.sub_apply, loss_expansion α hα (T n) (K n) (hK1 n),
    cross_term α (K n) (hK1 n) (T n)]
  simp only [Complex.ofReal_re]
  have hKn : (K n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hK1 n))
  field_simp
  ring

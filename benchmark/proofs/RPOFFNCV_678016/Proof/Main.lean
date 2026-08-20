import Architect
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.Real.Sqrt
import Mathlib.InformationTheory.Hamming

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:char-word"
  (statement := /-- Let $\F_q$ be a finite field of odd order $q$, and let
  $\chi : \F_q \to \{0, \pm 1\} \subseteq \mathbb{Z}$ denote the quadratic residue
  character, which sends $0$ to $0$, every nonzero square to $+1$, and every
  nonsquare to $-1$. For a polynomial $g(X) \in \F_q[X]$, the \emph{character word}
  $\chi \circ g$ is the function $\F_q \to \mathbb{Z}$ defined by
  $(\chi \circ g)(\alpha) = \chi(g(\alpha))$ for every $\alpha \in \F_q$. -/)
  (title := /-- The character word $\chi \circ g$ -/)
  (latexEnv := "definition")]
def char_word {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : Polynomial F) : F → ℤ :=
  fun α => quadraticChar F (Polynomial.eval α g)

@[blueprint "def:algorithm-a"
  (statement := /-- Let $\F_q$ be a finite field of odd order $q$, and let
  $\chi : \F_q \to \{0, \pm 1\}$ be the quadratic residue character. We model
  \emph{Algorithm A} as the recovery function
  $A : \mathbb{N} \times \mathbb{N} \times (\F_q \to \mathbb{Z}) \to \F_q[X]$ specified by
  its output: given a degree bound $d \in \mathbb{N}$, an error bound $e \in \mathbb{N}$,
  and a received word $r : \F_q \to \mathbb{Z}$, if there exists a monic squarefree
  polynomial $p(X) \in \F_q[X]$ with $\deg(p) \leq d$ whose character word
  $\chi \circ p$ (see \cref{def:char-word}) satisfies $\Delta(\chi \circ p, r) \leq e$,
  then $A(d, e, r)$ is some such polynomial, chosen via the axiom of choice; otherwise
  $A(d, e, r)$ is the zero polynomial. This captures exactly the input–output
  specification of the $\poly(q)$-time procedure of Section \ref{sec:chi} (solve the
  designed $\F_q$-linear system, factor the resulting polynomial, select the irreducible
  factors whose multiplicity lies in $[\tfrac{3}{8}q, \tfrac{7}{8}q] \bmod q$, and return
  their product), whose output is precisely a monic squarefree polynomial of degree at
  most $d$ lying within Hamming distance $e$ of $r$. -/)
  (title := /-- Algorithm A as a recovery function -/)
  (latexEnv := "definition")]
noncomputable def algorithm_a {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (d e : ℕ) (r : F → ℤ) : Polynomial F :=
  letI := Classical.propDecidable
  if h : ∃ p : Polynomial F,
      p.Monic ∧ Squarefree p ∧ p.natDegree ≤ d ∧ hammingDist (char_word p) r ≤ e then
    h.choose
  else 0

@[blueprint "def:weil-char-sum-bound"
  (statement := /-- Let $\F_q$ be a finite field with $q = \#\F_q$, and let
  $\chi : \F_q \to \{0, \pm 1\}$ be the quadratic residue character. We say that $\F_q$
  \emph{satisfies the Weil character-sum bound} if for every squarefree polynomial
  $f(X) \in \F_q[X]$ of degree $m = \deg(f) \geq 1$ the incomplete character sum
  $\sum_{\alpha \in \F_q}\chi(f(\alpha))$ (whose summands are the values of the character
  word $\chi \circ f$ of \cref{def:char-word}) obeys
  \[ \left| \sum_{\alpha \in \F_q} \chi(f(\alpha)) \right| \leq (m - 1)\sqrt{q}. \]

  This condition is a theorem of the literature for every finite field of odd order: it is
  the character-sum form of the Riemann Hypothesis for curves over finite fields, proved by
  A.~Weil (\emph{Sur les courbes alg\'ebriques et les vari\'et\'es qui s'en d\'eduisent},
  Hermann, 1948), and in exactly the form stated here — for every finite field $\F_q$ of odd
  order $q$ and every squarefree $f(X) \in \F_q[X]$ with $\deg(f) \geq 1$ — it is
  W.~M.~Schmidt, \emph{Equations over Finite Fields: An Elementary Approach}, Lecture Notes
  in Mathematics 536, Springer, 1976, Ch.~II, Thm.~2C. It is isolated here as a named
  hypothesis, rather than derived, because the argument being formalized uses it as a black
  box and no self-contained derivation is available: every known proof requires either the
  theory of zeta functions of curves over finite fields, as in Weil (loc.~cit.), or
  Stepanov's method, as in Schmidt (loc.~cit.). Accordingly, every result below that needs
  the estimate carries this condition as an explicit assumption on $\F_q$.

  For orientation on the quantity so estimated, write
  $S = \sum_{\alpha \in \F_q}\chi(f(\alpha))$ and note that $S$ measures an affine point
  count. For each $\alpha \in \F_q$ the number of $y \in \F_q$ with $y^2 = f(\alpha)$ equals
  $1 + \chi(f(\alpha))$: it is $2$ when $f(\alpha)$ is a nonzero square, in which case
  $\chi(f(\alpha)) = 1$; it is $0$ when $f(\alpha)$ is a nonsquare, in which case
  $\chi(f(\alpha)) = -1$; and it is $1$ when $f(\alpha) = 0$, in which case
  $\chi(f(\alpha)) = 0$. Summing over all $\alpha \in \F_q$, the number $N$ of affine
  $\F_q$-points of the curve $y^2 = f(x)$ satisfies
  $N = \sum_{\alpha \in \F_q}\bigl(1 + \chi(f(\alpha))\bigr) = q + S$, so that $S = N - q$
  and the condition asserts exactly that this point count deviates from $q$ by at most
  $(m - 1)\sqrt{q}$. -/)
  (title := /-- The Weil character-sum bound as a hypothesis on $\F_q$ -/)
  (latexEnv := "definition")]
def weil_char_sum_bound (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∀ f : Polynomial F, Squarefree f → 1 ≤ f.natDegree →
    |((∑ α : F, char_word f α : ℤ) : ℝ)|
      ≤ ((f.natDegree : ℝ) - 1) * Real.sqrt (Fintype.card F)

@[blueprint "lem:char-word-values"
  (statement := /-- Let $\F_q$ be a finite field and let $\chi : \F_q \to \{0, \pm 1\}$ be the
  quadratic residue character. For every polynomial $h(X) \in \F_q[X]$ and every
  $\alpha \in \F_q$, the value $(\chi \circ h)(\alpha) = \chi(h(\alpha))$ of the character word
  of \cref{def:char-word} satisfies $(\chi \circ h)(\alpha) \in \{0, 1, -1\}$; that is,
  $(\chi \circ h)(\alpha) = 0$ or $(\chi \circ h)(\alpha) = 1$ or
  $(\chi \circ h)(\alpha) = -1$. -/)
  (proof := /-- Fix $h(X) \in \F_q[X]$ and $\alpha \in \F_q$, and distinguish two cases according
  to whether $h(\alpha)$ vanishes. If $h(\alpha) = 0$, then $\chi(h(\alpha)) = \chi(0) = 0$,
  since the quadratic character takes the value $0$ at $0$, and the first alternative holds.
  If $h(\alpha) \neq 0$, then the quadratic character of a nonzero argument is $1$ or $-1$,
  so $\chi(h(\alpha)) = 1$ or $\chi(h(\alpha)) = -1$, and the second or third alternative
  holds. In either case one of the three alternatives is satisfied. -/)
  (title := /-- The character word takes values in $\{0, \pm 1\}$ -/)
  (latexEnv := "lemma")]
lemma char_word_values {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h : Polynomial F) (α : F) :
    char_word h α = 0 ∨ char_word h α = 1 ∨ char_word h α = -1 := by
  rcases eq_or_ne (Polynomial.eval α h) 0 with hz | hz
  · exact Or.inl (by simp [char_word, hz])
  · exact Or.inr (quadraticChar_dichotomy hz)

@[blueprint "lem:char-word-mul-eq"
  (statement := /-- Let $\F_q$ be a finite field and let $\chi : \F_q \to \{0, \pm 1\}$ be the
  quadratic residue character. For all polynomials $u(X), v(X) \in \F_q[X]$ and every
  $\alpha \in \F_q$, the character word of \cref{def:char-word} is multiplicative:
  \[ (\chi \circ (uv))(\alpha) = (\chi \circ u)(\alpha)\,(\chi \circ v)(\alpha). \] -/)
  (proof := /-- Fix $u(X), v(X) \in \F_q[X]$ and $\alpha \in \F_q$. Evaluation at $\alpha$ is a
  ring homomorphism $\F_q[X] \to \F_q$, so $(uv)(\alpha) = u(\alpha)\,v(\alpha)$. The quadratic
  residue character is a multiplicative character, hence
  $\chi\bigl(u(\alpha)v(\alpha)\bigr) = \chi(u(\alpha))\,\chi(v(\alpha))$. Combining the two
  identities gives
  $(\chi \circ (uv))(\alpha) = \chi\bigl((uv)(\alpha)\bigr) = \chi(u(\alpha))\,\chi(v(\alpha))
  = (\chi \circ u)(\alpha)\,(\chi \circ v)(\alpha)$. -/)
  (title := /-- Multiplicativity of the character word -/)
  (latexEnv := "lemma")]
lemma char_word_mul_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (u v : Polynomial F) (α : F) :
    char_word (u * v) α = char_word u α * char_word v α := by
  simp only [char_word, Polynomial.eval_mul, map_mul]

@[blueprint "lem:char-word-zero-count-le"
  (statement := /-- Let $\F_q$ be a finite field and let $\chi : \F_q \to \{0, \pm 1\}$ be the
  quadratic residue character. Let $h(X) \in \F_q[X]$ be a nonzero polynomial. Then the number
  of points at which the character word of \cref{def:char-word} vanishes is at most the degree
  of $h$:
  \[ \sum_{\alpha \in \F_q} \bigl[(\chi \circ h)(\alpha) = 0\bigr] \leq \deg(h), \]
  where $[\,\cdot\,]$ denotes the indicator taking the value $1$ when the condition holds and
  $0$ otherwise. -/)
  (proof := /-- Since the quadratic residue character vanishes exactly at $0$, for every
  $\alpha \in \F_q$ we have $(\chi \circ h)(\alpha) = \chi(h(\alpha)) = 0$ if and only if
  $h(\alpha) = 0$. Hence the set $\{\alpha \in \F_q : (\chi \circ h)(\alpha) = 0\}$ coincides
  with the set $Z = \{\alpha \in \F_q : h(\alpha) = 0\}$ of roots of $h$ in $\F_q$, and the
  displayed sum of indicators equals $\#Z$. Every $\alpha \in Z$ is a root of $h$, so $Z$,
  viewed as a multiset without repetition, is contained in the multiset of roots of $h$; as
  $h \neq 0$, the number of roots of $h$ counted with multiplicity is at most $\deg(h)$.
  Therefore $\#Z \leq \deg(h)$, which is the claim. -/)
  (title := /-- The character word vanishes at few points -/)
  (latexEnv := "lemma")]
lemma char_word_zero_count_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h : Polynomial F) (hh : h ≠ 0) :
    (∑ α : F, if char_word h α = 0 then (1 : ℤ) else 0) ≤ (h.natDegree : ℤ) := by
  have hfil : (Finset.univ.filter (fun α : F => char_word h α = 0))
      = Finset.univ.filter (fun α : F => Polynomial.eval α h = 0) := by
    apply Finset.filter_congr
    intro α _
    constructor
    · intro hx
      exact quadraticChar_eq_zero_iff.mp hx
    · intro hx
      exact quadraticChar_eq_zero_iff.mpr hx
  have hcard : (Finset.univ.filter (fun α : F => Polynomial.eval α h = 0)).card
      ≤ h.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro a ha
    simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [Polynomial.mem_roots hh]
    simpa [Polynomial.IsRoot] using ha
  rw [Finset.sum_boole, hfil]
  exact_mod_cast hcard

@[blueprint "lem:char-word-gcd-decomp"
  (statement := /-- Let $\F_q$ be a finite field and let $p(X), g(X) \in \F_q[X]$ be distinct
  monic squarefree polynomials. Then there exist polynomials $t(X), f(X) \in \F_q[X]$ such that
  \[ p(X)\,g(X) = t(X)^2 f(X), \]
  with $f$ squarefree, $1 \leq \deg(f)$, $\deg(f) \leq \deg(p) + \deg(g)$, and
  $\deg(t) \leq \deg(p)$. -/)
  (proof := /-- Set $t = \gcd(p, g)$, $u = p / t$ and $v = g / t$, and put $f = uv$. Since $p$
  and $g$ are monic they are nonzero, hence $t \neq 0$ and the exact divisions $tu = p$ and
  $tv = g$ hold. Multiplying these gives $pg = (tu)(tv) = t^2 (uv) = t^2 f$, which is the
  displayed factorisation.

  We check the four asserted properties of $t$ and $f$. First, $u \mid p$ and $p$ is
  squarefree, so $u$ is squarefree; likewise $v \mid g$ and $g$ is squarefree, so $v$ is
  squarefree. Moreover $u = p/\gcd(p,g)$ and $v = g/\gcd(p,g)$ are coprime, hence relatively
  prime, and a product of two relatively prime squarefree polynomials is squarefree; therefore
  $f = uv$ is squarefree.

  Second, we show $\deg(f) \geq 1$. Since $p, g \neq 0$ we have $pg \neq 0$, and from
  $pg = t^2 f$ it follows that $f \neq 0$. Suppose, for contradiction, that $\deg(f) = 0$.
  A nonzero polynomial of degree $0$ is a unit, so $f = uv$ is a unit, and therefore both $u$
  and $v$ are units. From $tu = p$ with $u$ a unit we get that $t$ and $p$ are associates, and
  from $tv = g$ with $v$ a unit that $t$ and $g$ are associates; hence $p$ and $g$ are
  associates. Two associated monic polynomials are equal, so $p = g$, contradicting the
  hypothesis $p \neq g$. Therefore $\deg(f) \geq 1$.

  Third, $f$ divides $pg$ because $pg = t^2 f$, and $pg \neq 0$, so
  $\deg(f) \leq \deg(pg) = \deg(p) + \deg(g)$, the last equality because $p$ and $g$ are
  nonzero. Finally $t = \gcd(p,g)$ divides $p$ and $p \neq 0$, so
  $\deg(t) \leq \deg(p)$. -/)
  (title := /-- Squarefree kernel of the product of two distinct monic squarefree polynomials -/)
  (latexEnv := "lemma")]
lemma char_word_gcd_decomp {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (p g : Polynomial F) (hpm : p.Monic) (hps : Squarefree p)
    (hgm : g.Monic) (hgs : Squarefree g) (hpg : p ≠ g) :
    ∃ t f : Polynomial F, p * g = t ^ 2 * f ∧ Squarefree f ∧ 1 ≤ f.natDegree ∧
      f.natDegree ≤ p.natDegree + g.natDegree ∧ t.natDegree ≤ p.natDegree := by
  have hp0 : p ≠ 0 := hpm.ne_zero
  have hg0 : g ≠ 0 := hgm.ne_zero
  have ht0 : gcd p g ≠ 0 := gcd_ne_zero_of_left hp0
  have hep : gcd p g * (p / gcd p g) = p :=
    EuclideanDomain.mul_div_cancel' ht0 (gcd_dvd_left p g)
  have heg : gcd p g * (g / gcd p g) = g :=
    EuclideanDomain.mul_div_cancel' ht0 (gcd_dvd_right p g)
  have hcop : IsCoprime (p / gcd p g) (g / gcd p g) := isCoprime_div_gcd_div_gcd hg0
  have hsp : Squarefree (p / gcd p g) := hps.squarefree_of_dvd (Dvd.intro_left _ hep)
  have hsg : Squarefree (g / gcd p g) := hgs.squarefree_of_dvd (Dvd.intro_left _ heg)
  have hprod : p * g = gcd p g ^ 2 * ((p / gcd p g) * (g / gcd p g)) := by
    calc p * g = (gcd p g * (p / gcd p g)) * (gcd p g * (g / gcd p g)) := by rw [hep, heg]
      _ = gcd p g ^ 2 * ((p / gcd p g) * (g / gcd p g)) := by ring
  have hpg0 : p * g ≠ 0 := mul_ne_zero hp0 hg0
  have hf0 : (p / gcd p g) * (g / gcd p g) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hprod
    exact hpg0 hprod
  refine ⟨gcd p g, (p / gcd p g) * (g / gcd p g), hprod,
    squarefree_mul_iff.mpr ⟨hcop.isRelPrime, hsp, hsg⟩, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos ((p / gcd p g) * (g / gcd p g)).natDegree with h0 | h0
    · exfalso
      have hu : IsUnit ((p / gcd p g) * (g / gcd p g)) := by
        rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hf0, h0]
        rfl
      have hup : IsUnit (p / gcd p g) := isUnit_of_mul_isUnit_left hu
      have hug : IsUnit (g / gcd p g) := isUnit_of_mul_isUnit_right hu
      have hap : Associated (gcd p g) p := ⟨hup.unit, by rw [IsUnit.unit_spec]; exact hep⟩
      have hag : Associated (gcd p g) g := ⟨hug.unit, by rw [IsUnit.unit_spec]; exact heg⟩
      exact hpg (Polynomial.eq_of_monic_of_associated hpm hgm (hap.symm.trans hag))
    · exact h0
  · have hdvd : (p / gcd p g) * (g / gcd p g) ∣ p * g := Dvd.intro_left _ hprod.symm
    calc ((p / gcd p g) * (g / gcd p g)).natDegree ≤ (p * g).natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd hpg0
      _ = p.natDegree + g.natDegree := Polynomial.natDegree_mul hp0 hg0
  · exact Polynomial.natDegree_le_of_dvd (gcd_dvd_left p g) hp0

@[blueprint "lem:char-word-sum-abs-bound"
  (statement := /-- Let $\F_q$ be a finite field with $q = \#\F_q$, let
  $\chi : \F_q \to \{0, \pm 1\}$ be the quadratic residue character, and assume that $\F_q$
  satisfies the Weil character-sum bound of \cref{def:weil-char-sum-bound}. Let $d \in \mathbb{N}$
  and let $p(X), g(X) \in \F_q[X]$ be distinct monic squarefree polynomials with
  $\deg(p) \leq d$ and $\deg(g) \leq d$. Then the complete character sum of the product $pg$
  obeys
  \[ \Bigl| \sum_{\alpha \in \F_q} \chi\bigl((pg)(\alpha)\bigr) \Bigr|
     \leq 2d\sqrt{q} + d, \]
  the summands being the values of the character word $\chi \circ (pg)$ of
  \cref{def:char-word}. -/)
  (proof := /-- By \cref{lem:char-word-gcd-decomp} there are $t(X), f(X) \in \F_q[X]$ with
  $pg = t^2 f$, with $f$ squarefree, $1 \leq \deg(f) \leq \deg(p) + \deg(g)$ and
  $\deg(t) \leq \deg(p)$. Since $p$ and $g$ are monic they are nonzero, so $pg \neq 0$, and
  from $pg = t^2f$ we get $t \neq 0$. Write $S = \sum_{\alpha}\chi\bigl((pg)(\alpha)\bigr)$ and
  $T = \sum_{\alpha}\chi(f(\alpha))$.

  We first compare $S$ with $T$ pointwise. Fix $\alpha \in \F_q$; evaluating $pg = t^2f$ at
  $\alpha$ gives $(pg)(\alpha) = t(\alpha)^2 f(\alpha)$. If $t(\alpha) \neq 0$, then
  $t(\alpha)^2$ is a nonzero square, so $\chi\bigl(t(\alpha)^2\bigr) = 1$, and by
  multiplicativity of $\chi$ we obtain
  $\chi\bigl((pg)(\alpha)\bigr) = \chi\bigl(t(\alpha)^2\bigr)\chi(f(\alpha)) = \chi(f(\alpha))$,
  so the two summands agree and their difference is $0$. If $t(\alpha) = 0$, then
  $(pg)(\alpha) = 0$, hence $\chi\bigl((pg)(\alpha)\bigr) = 0$, while
  $|\chi(f(\alpha))| \leq 1$ because $\chi(f(\alpha)) \in \{0, \pm 1\}$ by
  \cref{lem:char-word-values}; so the difference has absolute value at most $1$. In both cases
  \[ \bigl|\chi\bigl((pg)(\alpha)\bigr) - \chi(f(\alpha))\bigr|
     \leq \bigl[\chi(t(\alpha)) = 0\bigr], \]
  using that $\chi(t(\alpha)) = 0$ if and only if $t(\alpha) = 0$. Summing over
  $\alpha \in \F_q$ and applying the triangle inequality,
  $|S - T| \leq \sum_{\alpha}\bigl[\chi(t(\alpha)) = 0\bigr] \leq \deg(t) \leq \deg(p) \leq d$,
  where the second inequality is \cref{lem:char-word-zero-count-le} applied to the nonzero
  polynomial $t$.

  We next bound $T$. The polynomial $f$ is squarefree with $\deg(f) \geq 1$, so the assumed
  Weil character-sum bound of \cref{def:weil-char-sum-bound} applies and yields
  $|T| \leq (\deg(f) - 1)\sqrt{q}$. Since $\deg(f) \leq \deg(p) + \deg(g) \leq 2d$ and
  $\sqrt{q} \geq 0$, we get $|T| \leq (2d - 1)\sqrt{q} \leq 2d\sqrt{q}$.

  Combining the two estimates by the triangle inequality,
  $|S| \leq |T| + |S - T| \leq 2d\sqrt{q} + d$, as asserted. -/)
  (title := /-- Character-sum bound for the product of two admissible polynomials -/)
  (latexEnv := "lemma")]
lemma char_word_sum_abs_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hweil : weil_char_sum_bound F)
    (d : ℕ) (p g : Polynomial F)
    (hpm : p.Monic) (hps : Squarefree p) (hpd : p.natDegree ≤ d)
    (hgm : g.Monic) (hgs : Squarefree g) (hgd : g.natDegree ≤ d)
    (hpg : p ≠ g) :
    |((∑ α : F, char_word (p * g) α : ℤ) : ℝ)|
      ≤ 2 * (d : ℝ) * Real.sqrt (Fintype.card F) + (d : ℝ) := by
  obtain ⟨t, f, hprod, hsf, hf1, hfd, htd⟩ := char_word_gcd_decomp p g hpm hps hgm hgs hpg
  have hpg0 : p * g ≠ 0 := mul_ne_zero hpm.ne_zero hgm.ne_zero
  have ht0 : t ≠ 0 := by
    intro hz
    apply hpg0
    rw [hprod, hz]
    simp
  have hbound : ∀ α : F, |char_word (p * g) α - char_word f α|
      ≤ (if char_word t α = 0 then (1 : ℤ) else 0) := by
    intro α
    have hev : Polynomial.eval α (p * g)
        = Polynomial.eval α t ^ 2 * Polynomial.eval α f := by
      rw [hprod]
      simp
    rcases eq_or_ne (Polynomial.eval α t) 0 with hz | hz
    · rw [if_pos (show char_word t α = 0 from quadraticChar_eq_zero_iff.mpr hz)]
      have h1 : char_word (p * g) α = 0 := by
        simp [char_word, hev, hz]
      rw [h1, zero_sub, abs_neg]
      rcases char_word_values f α with hv | hv | hv <;> rw [hv] <;> norm_num
    · rw [if_neg (show ¬ char_word t α = 0 from fun hc => hz (quadraticChar_eq_zero_iff.mp hc))]
      have h1 : char_word (p * g) α = char_word f α := by
        simp only [char_word, hev, map_mul, quadraticChar_sq_one' hz, one_mul]
      rw [h1, sub_self, abs_zero]
  have hdiff : |(∑ α : F, char_word (p * g) α) - ∑ α : F, char_word f α| ≤ (d : ℤ) := by
    calc |(∑ α : F, char_word (p * g) α) - ∑ α : F, char_word f α|
        = |∑ α : F, (char_word (p * g) α - char_word f α)| := by
          rw [Finset.sum_sub_distrib]
      _ ≤ ∑ α : F, |char_word (p * g) α - char_word f α| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ α : F, (if char_word t α = 0 then (1 : ℤ) else 0) :=
          Finset.sum_le_sum (fun α _ => hbound α)
      _ ≤ (t.natDegree : ℤ) := char_word_zero_count_le t ht0
      _ ≤ (d : ℤ) := by exact_mod_cast le_trans htd hpd
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (Fintype.card F) := Real.sqrt_nonneg _
  have hfd2 : (f.natDegree : ℝ) ≤ 2 * (d : ℝ) := by
    have : f.natDegree ≤ 2 * d := by omega
    exact_mod_cast this
  have hT : |((∑ α : F, char_word f α : ℤ) : ℝ)| ≤ 2 * (d : ℝ) * Real.sqrt (Fintype.card F) := by
    have hw := hweil f hsf hf1
    nlinarith [hw, hsqrt0, hfd2]
  have hdiffR : |((∑ α : F, char_word (p * g) α : ℤ) : ℝ)
      - ((∑ α : F, char_word f α : ℤ) : ℝ)| ≤ (d : ℝ) := by
    have := hdiff
    push_cast [← Int.cast_abs]
    exact_mod_cast this
  calc |((∑ α : F, char_word (p * g) α : ℤ) : ℝ)|
      ≤ |((∑ α : F, char_word (p * g) α : ℤ) : ℝ) - ((∑ α : F, char_word f α : ℤ) : ℝ)|
        + |((∑ α : F, char_word f α : ℤ) : ℝ)| := by
        simpa using abs_sub_abs_le_abs_sub
          (((∑ α : F, char_word (p * g) α : ℤ) : ℝ)) (((∑ α : F, char_word f α : ℤ) : ℝ))
    _ ≤ (d : ℝ) + 2 * (d : ℝ) * Real.sqrt (Fintype.card F) := add_le_add hdiffR hT
    _ = 2 * (d : ℝ) * Real.sqrt (Fintype.card F) + (d : ℝ) := by ring

@[blueprint "lem:char-word-dist-count"
  (statement := /-- Let $\F_q$ be a finite field with $q = \#\F_q$, and let
  $\chi : \F_q \to \{0, \pm 1\}$ be the quadratic residue character. Let $d \in \mathbb{N}$ and
  let $p(X), g(X) \in \F_q[X]$ be monic polynomials with $\deg(p) \leq d$ and
  $\deg(g) \leq d$. Then, with $\Delta$ denoting Hamming distance and $\chi \circ p$,
  $\chi \circ g$, $\chi \circ (pg)$ the character words of \cref{def:char-word},
  \[ q - \sum_{\alpha \in \F_q} \chi\bigl((pg)(\alpha)\bigr)
     \leq 2\,\Delta(\chi \circ p, \chi \circ g) + 2d. \] -/)
  (proof := /-- We argue pointwise and then sum. Fix $\alpha \in \F_q$ and write
  $a = \chi(p(\alpha))$ and $b = \chi(g(\alpha))$. By \cref{lem:char-word-values} each of $a$
  and $b$ lies in $\{0, 1, -1\}$, and we claim that
  \[ 1 - ab \leq 2\,[a \neq b] + [a = 0] + [b = 0], \]
  where $[\,\cdot\,]$ is the indicator of the enclosed condition. This is verified by checking
  the nine possible pairs $(a,b)$. If $a = b = 1$ or $a = b = -1$ then $1 - ab = 0$ and the
  right-hand side is $0$. If $a = b = 0$ then $1 - ab = 1$ while the right-hand side is
  $0 + 1 + 1 = 2$. If exactly one of $a, b$ is $0$ and the other is $\pm 1$, then $1 - ab = 1$
  and the right-hand side is $2 + 1 + 0 = 3$ or $2 + 0 + 1 = 3$. If $\{a, b\} = \{1, -1\}$ then
  $1 - ab = 2$ and the right-hand side is $2 + 0 + 0 = 2$. In every case the inequality holds.

  Now sum the inequality over all $\alpha \in \F_q$. On the left, $\sum_{\alpha} 1 = q$, and by
  \cref{lem:char-word-mul-eq} we have
  $\chi(p(\alpha))\chi(g(\alpha)) = \chi\bigl((pg)(\alpha)\bigr)$ for every $\alpha$, so the
  left-hand side sums to $q - \sum_{\alpha}\chi\bigl((pg)(\alpha)\bigr)$. On the right, the
  first term sums to $2\,\Delta(\chi \circ p, \chi \circ g)$, since the Hamming distance is by
  definition the number of $\alpha$ at which the two character words differ. The second and
  third terms sum to $\sum_{\alpha}[\chi(p(\alpha)) = 0]$ and
  $\sum_{\alpha}[\chi(g(\alpha)) = 0]$ respectively; since $p$ and $g$ are monic they are
  nonzero, so \cref{lem:char-word-zero-count-le} bounds these by $\deg(p) \leq d$ and
  $\deg(g) \leq d$. Adding the three bounds gives
  $q - \sum_{\alpha}\chi\bigl((pg)(\alpha)\bigr) \leq
  2\,\Delta(\chi \circ p, \chi \circ g) + 2d$, as claimed. -/)
  (title := /-- Lower bound for the Hamming distance in terms of a character sum -/)
  (latexEnv := "lemma")]
lemma char_word_dist_count {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (d : ℕ) (p g : Polynomial F)
    (hpm : p.Monic) (hpd : p.natDegree ≤ d)
    (hgm : g.Monic) (hgd : g.natDegree ≤ d) :
    (Fintype.card F : ℤ) - (∑ α : F, char_word (p * g) α)
      ≤ 2 * (hammingDist (char_word p) (char_word g) : ℤ) + 2 * (d : ℤ) := by
  have hpt : ∀ α : F, 1 - char_word p α * char_word g α
      ≤ 2 * (if char_word p α ≠ char_word g α then (1 : ℤ) else 0)
        + (if char_word p α = 0 then (1 : ℤ) else 0)
        + (if char_word g α = 0 then (1 : ℤ) else 0) := by
    intro α
    rcases char_word_values p α with ha | ha | ha <;>
      rcases char_word_values g α with hb | hb | hb <;>
        rw [ha, hb] <;> norm_num
  have hleft : (Fintype.card F : ℤ) - (∑ α : F, char_word (p * g) α)
      = ∑ α : F, (1 - char_word p α * char_word g α) := by
    rw [Finset.sum_sub_distrib]
    simp only [char_word_mul_eq]
    simp [Finset.card_univ]
  have hright : (∑ α : F, (2 * (if char_word p α ≠ char_word g α then (1 : ℤ) else 0)
        + (if char_word p α = 0 then (1 : ℤ) else 0)
        + (if char_word g α = 0 then (1 : ℤ) else 0)))
      = 2 * (hammingDist (char_word p) (char_word g) : ℤ)
        + (∑ α : F, if char_word p α = 0 then (1 : ℤ) else 0)
        + (∑ α : F, if char_word g α = 0 then (1 : ℤ) else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole]
    norm_num [hammingDist]
  have hp := char_word_zero_count_le p hpm.ne_zero
  have hg := char_word_zero_count_le g hgm.ne_zero
  have hpd' : (p.natDegree : ℤ) ≤ (d : ℤ) := by exact_mod_cast hpd
  have hgd' : (g.natDegree : ℤ) ≤ (d : ℤ) := by exact_mod_cast hgd
  rw [hleft]
  calc ∑ α : F, (1 - char_word p α * char_word g α)
      ≤ ∑ α : F, (2 * (if char_word p α ≠ char_word g α then (1 : ℤ) else 0)
          + (if char_word p α = 0 then (1 : ℤ) else 0)
          + (if char_word g α = 0 then (1 : ℤ) else 0)) :=
        Finset.sum_le_sum (fun α _ => hpt α)
    _ = 2 * (hammingDist (char_word p) (char_word g) : ℤ)
        + (∑ α : F, if char_word p α = 0 then (1 : ℤ) else 0)
        + (∑ α : F, if char_word g α = 0 then (1 : ℤ) else 0) := hright
    _ ≤ 2 * (hammingDist (char_word p) (char_word g) : ℤ) + 2 * (d : ℤ) := by
        linarith [hp, hg, hpd', hgd']

@[blueprint "lem:char-word-min-dist"
  (statement := /-- Let $\F_q$ be a finite field of odd order $q = \#\F_q$, let
  $\chi : \F_q \to \{0, \pm 1\}$ be the quadratic residue character, and let
  $\varepsilon > 0$. Let $d, e \in \mathbb{N}$ satisfy $d \leq \tfrac{\varepsilon}{16}\sqrt{q}$
  and $e \leq \left(\tfrac{1}{8} - \varepsilon\right) q$. Assume that $\F_q$ satisfies the
  Weil character-sum bound of \cref{def:weil-char-sum-bound}, that is, that
  $\bigl|\sum_{\alpha \in \F_q}\chi(h(\alpha))\bigr| \leq (\deg(h) - 1)\sqrt{q}$ for every
  squarefree $h(X) \in \F_q[X]$ with $\deg(h) \geq 1$. Let $p(X), g(X) \in \F_q[X]$ be
  distinct monic squarefree polynomials, each of degree at most $d$. Then their character
  words (see \cref{def:char-word}) are far apart in Hamming distance:
  \[ \Delta(\chi \circ p, \chi \circ g) > 2e. \] -/)
  (proof := /-- Write $\Delta = \Delta(\chi \circ p, \chi \circ g)$ and
  $S = \sum_{\alpha \in \F_q}\chi\bigl((pg)(\alpha)\bigr)$. Since $q = \#\F_q \geq 1$ we have
  $q > 0$, and $\sqrt{q} \geq 1$ with $\sqrt{q}\sqrt{q} = q$; consequently
  $\sqrt{q} \leq q$. Also $e \geq 0$ and $d \geq 0$, being natural numbers.

  We first record that $\varepsilon \leq \tfrac{1}{8}$. Indeed, from
  $0 \leq e \leq \left(\tfrac{1}{8} - \varepsilon\right)q$ and $q > 0$ we get
  $\tfrac{1}{8} - \varepsilon \geq 0$.

  Next we combine two estimates. By \cref{lem:char-word-dist-count}, applied to the monic
  polynomials $p$ and $g$ of degree at most $d$,
  \[ q - S \leq 2\Delta + 2d. \]
  By \cref{lem:char-word-sum-abs-bound}, applied with the assumed Weil character-sum bound of
  \cref{def:weil-char-sum-bound} to the distinct monic squarefree polynomials $p$ and $g$ of
  degree at most $d$, we have $|S| \leq 2d\sqrt{q} + d$, and hence in particular
  $S \leq 2d\sqrt{q} + d$.

  We now bound the two error terms by multiples of $q$. From
  $d \leq \tfrac{\varepsilon}{16}\sqrt{q}$ and $\sqrt{q} \geq 0$ we get
  $d\sqrt{q} \leq \tfrac{\varepsilon}{16}\sqrt{q}\sqrt{q} = \tfrac{\varepsilon}{16}q$, so with
  $\varepsilon \leq \tfrac{1}{8}$ and $q > 0$ this gives
  $2d\sqrt{q} \leq \tfrac{\varepsilon}{8}q \leq \tfrac{q}{64}$. Similarly, from
  $d \leq \tfrac{\varepsilon}{16}\sqrt{q}$ together with $\varepsilon \leq \tfrac{1}{8}$,
  $\sqrt{q} \leq q$ and $\varepsilon > 0$ we obtain $d \leq \tfrac{q}{128}$. Finally, from
  $e \leq \left(\tfrac{1}{8} - \varepsilon\right)q$ with $\varepsilon > 0$ and $q > 0$ we get
  $4e \leq \tfrac{q}{2}$.

  Assembling these linear inequalities: $2\Delta \geq q - S - 2d \geq q - 2d\sqrt{q} - 3d
  \geq q - \tfrac{q}{64} - \tfrac{3q}{128} = \tfrac{123}{128}q$, while
  $4e \leq \tfrac{q}{2} < \tfrac{123}{128}q$ because $q > 0$. Therefore $2\Delta > 4e$, that
  is, $\Delta > 2e$. Since $\Delta$ and $e$ are natural numbers, the strict inequality
  $2e < \Delta$ of the statement follows. -/)
  (title := /-- Minimum distance between distinct admissible character words -/)
  (latexEnv := "lemma")]
lemma char_word_min_dist {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hodd : Odd (Fintype.card F))
    (hweil : weil_char_sum_bound F)
    (ε : ℝ) (hε : 0 < ε)
    (d e : ℕ)
    (hd : (d : ℝ) ≤ ε / 16 * Real.sqrt (Fintype.card F))
    (he : (e : ℝ) ≤ (1 / 8 - ε) * (Fintype.card F : ℝ))
    (p g : Polynomial F)
    (hpm : p.Monic) (hps : Squarefree p) (hpd : p.natDegree ≤ d)
    (hgm : g.Monic) (hgs : Squarefree g) (hgd : g.natDegree ≤ d)
    (hpg : p ≠ g) :
    2 * e < hammingDist (char_word p) (char_word g) := by
  have hq0 : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Fintype.card F) := Real.sqrt_nonneg _
  have hss : Real.sqrt (Fintype.card F) * Real.sqrt (Fintype.card F) = (Fintype.card F : ℝ) :=
    Real.mul_self_sqrt (le_of_lt hq0)
  have hs1 : (1 : ℝ) ≤ Real.sqrt (Fintype.card F) := Real.one_le_sqrt.mpr hq1
  have hsq : Real.sqrt (Fintype.card F) ≤ (Fintype.card F : ℝ) := by nlinarith [hss, hs1]
  have he0 : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg e
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hεle : ε ≤ 1 / 8 := by nlinarith [he, he0, hq0]
  have hcount := char_word_dist_count d p g hpm hpd hgm hgd
  have hsum := char_word_sum_abs_bound hweil d p g hpm hps hpd hgm hgs hgd hpg
  have hSle : ((∑ α : F, char_word (p * g) α : ℤ) : ℝ)
      ≤ 2 * (d : ℝ) * Real.sqrt (Fintype.card F) + (d : ℝ) :=
    le_trans (le_abs_self _) hsum
  have hcountR : (Fintype.card F : ℝ) - ((∑ α : F, char_word (p * g) α : ℤ) : ℝ)
      ≤ 2 * (hammingDist (char_word p) (char_word g) : ℝ) + 2 * (d : ℝ) := by
    exact_mod_cast hcount
  have hds : (d : ℝ) * Real.sqrt (Fintype.card F) ≤ ε / 16 * (Fintype.card F : ℝ) := by
    calc (d : ℝ) * Real.sqrt (Fintype.card F)
        ≤ (ε / 16 * Real.sqrt (Fintype.card F)) * Real.sqrt (Fintype.card F) :=
          mul_le_mul_of_nonneg_right hd hs0
      _ = ε / 16 * (Real.sqrt (Fintype.card F) * Real.sqrt (Fintype.card F)) := by ring
      _ = ε / 16 * (Fintype.card F : ℝ) := by rw [hss]
  have h2ds : 2 * (d : ℝ) * Real.sqrt (Fintype.card F) ≤ (Fintype.card F : ℝ) / 64 := by
    nlinarith [hds, hεle, hq0]
  have hd128 : (d : ℝ) ≤ (Fintype.card F : ℝ) / 128 := by
    nlinarith [hd, hs0, hεle, hsq, hε]
  have he4 : 4 * (e : ℝ) ≤ (Fintype.card F : ℝ) / 2 := by nlinarith [he, hε, hq0]
  have hlt : (2 * e : ℝ) < (hammingDist (char_word p) (char_word g) : ℝ) := by
    linarith [hcountR, hSle, h2ds, hd128, he4, hq0]
  exact_mod_cast hlt

@[blueprint "lem:admissible-unique"
  (statement := /-- Let $\F_q$ be a finite field of odd order $q = \#\F_q$, let
  $\chi : \F_q \to \{0, \pm 1\}$ be the quadratic residue character, and let
  $\varepsilon > 0$. Let $d, e \in \mathbb{N}$ satisfy $d \leq \tfrac{\varepsilon}{16}\sqrt{q}$
  and $e \leq \left(\tfrac{1}{8} - \varepsilon\right) q$, and let $r : \F_q \to \mathbb{Z}$
  be a received word. Assume that $\F_q$ satisfies the Weil character-sum bound of
  \cref{def:weil-char-sum-bound}. Suppose $g(X) \in \F_q[X]$ is monic and squarefree with
  $\deg(g) \leq d$ and $\Delta(\chi \circ g, r) \leq e$ (see \cref{def:char-word}). Then $g$
  is the unique such polynomial: every monic squarefree $p(X) \in \F_q[X]$ with
  $\deg(p) \leq d$ and $\Delta(\chi \circ p, r) \leq e$ satisfies $p = g$. -/)
  (proof := /-- Let $p(X) \in \F_q[X]$ be monic squarefree with $\deg(p) \leq d$ and
  $\Delta(\chi \circ p, r) \leq e$, and suppose for contradiction that $p \neq g$. By the
  triangle inequality for Hamming distance,
  \[ \Delta(\chi \circ p, \chi \circ g) \leq \Delta(\chi \circ p, r) + \Delta(r, \chi \circ g)
  \leq e + e = 2e, \] where the second inequality uses $\Delta(\chi \circ p, r) \leq e$
  together with $\Delta(r, \chi \circ g) = \Delta(\chi \circ g, r) \leq e$, the equality
  being the symmetry of the Hamming distance. But $p$ and $g$ are distinct monic
  squarefree polynomials of degree
  at most $d$, so \cref{lem:char-word-min-dist}, applied with the assumed Weil
  character-sum bound of \cref{def:weil-char-sum-bound}, gives
  $\Delta(\chi \circ p, \chi \circ g) > 2e$, contradicting the bound just derived, since no
  natural number is both at most $2e$ and greater than $2e$. Hence $p = g$. -/)
  (title := /-- Uniqueness of the admissible polynomial -/)
  (latexEnv := "lemma")]
lemma admissible_unique {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hodd : Odd (Fintype.card F))
    (hweil : weil_char_sum_bound F)
    (ε : ℝ) (hε : 0 < ε)
    (d e : ℕ)
    (hd : (d : ℝ) ≤ ε / 16 * Real.sqrt (Fintype.card F))
    (he : (e : ℝ) ≤ (1 / 8 - ε) * (Fintype.card F : ℝ))
    (r : F → ℤ)
    (g : Polynomial F) (hgm : g.Monic) (hgs : Squarefree g) (hgd : g.natDegree ≤ d)
    (hgr : hammingDist (char_word g) r ≤ e)
    (p : Polynomial F) (hpm : p.Monic) (hps : Squarefree p) (hpd : p.natDegree ≤ d)
    (hpr : hammingDist (char_word p) r ≤ e) :
    p = g := by
  by_contra hne
  have hmin := char_word_min_dist hodd hweil ε hε d e hd he p g hpm hps hpd hgm hgs hgd hne
  have htri : hammingDist (char_word p) (char_word g)
      ≤ hammingDist (char_word p) r + hammingDist r (char_word g) :=
    hammingDist_triangle _ _ _
  rw [hammingDist_comm r (char_word g)] at htri
  omega

@[blueprint "thm:algorithm-a-correct"
  (statement := /-- Let $\F_q$ be a finite field whose order $q = \#\F_q$ is odd,
  and let $\chi : \F_q \to \{0, \pm 1\}$ be the quadratic residue character. Let
  $\varepsilon > 0$ be a real number, and let $d, e \in \mathbb{N}$ satisfy
  $d \leq \tfrac{\varepsilon}{16}\sqrt{q}$ and $e \leq \left(\tfrac{1}{8} - \varepsilon\right) q$.
  Assume that $\F_q$ satisfies the Weil character-sum bound of
  \cref{def:weil-char-sum-bound}; this is a classical theorem for every finite field of odd
  order, recorded as an explicit hypothesis because it is used as a black box.
  Let $A$ denote Algorithm A (see \cref{def:algorithm-a}), the recovery function that,
  on parameters $d, e \in \mathbb{N}$ and a received word $r : \F_q \to \mathbb{Z}$,
  returns a polynomial $A(d, e, r) \in \F_q[X]$. Suppose $g(X) \in \F_q[X]$ is monic and
  squarefree with $\deg(g) \leq d$, and suppose the Hamming distance between the
  character word $\chi \circ g$ (see \cref{def:char-word}) and $r$ satisfies
  $\Delta(\chi \circ g, r) \leq e$. Then $A(d, e, r) = g(X)$. -/)
  (proof := /-- By hypothesis $g$ is monic and squarefree with $\deg(g) \leq d$ and
  $\Delta(\chi \circ g, r) \leq e$, so $g$ itself witnesses the existential predicate
  defining Algorithm A (see \cref{def:algorithm-a}): there exists a monic squarefree
  polynomial of degree at most $d$ whose character word lies within Hamming distance $e$
  of $r$. Here the character word $\chi \circ p$ of \cref{def:char-word} and the Hamming
  distance $\Delta$ are formed using the decidable-equality data supplied by the definition
  of $A$, which agrees with the ambient decidable equality of $\F_q$ because decidability
  of a proposition is a subsingleton; the witnessing property for $g$ therefore transfers
  verbatim. Consequently that existential holds, and by definition $A(d, e, r)$ is some
  polynomial $p := A(d, e, r)$ chosen to satisfy exactly those defining properties; that
  is, $p$ is monic and squarefree with $\deg(p) \leq d$ and $\Delta(\chi \circ p, r) \leq e$.
  Both $g$ and $p$ are therefore monic squarefree polynomials of degree at most $d$ whose
  character words lie within Hamming distance $e$ of $r$. By \cref{lem:admissible-unique},
  applied with the assumed Weil character-sum bound of \cref{def:weil-char-sum-bound},
  such a polynomial is unique, so $p = g$; that is, $A(d, e, r) = g(X)$, as claimed. -/)
  (title := /-- Correctness of Algorithm A -/)
  (latexEnv := "theorem")]
theorem algorithm_a_correct {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hodd : Odd (Fintype.card F))
    (hweil : weil_char_sum_bound F)
    (ε : ℝ) (hε : 0 < ε)
    (d e : ℕ)
    (hd : (d : ℝ) ≤ ε / 16 * Real.sqrt (Fintype.card F))
    (he : (e : ℝ) ≤ (1 / 8 - ε) * (Fintype.card F : ℝ))
    (g : Polynomial F) (hmonic : g.Monic) (hsquarefree : Squarefree g)
    (hdeg : g.natDegree ≤ d)
    (r : F → ℤ)
    (hdist : hammingDist (char_word g) r ≤ e) :
    algorithm_a d e r = g := by
  have hcw : ∀ p : Polynomial F,
      @char_word F _ _ (fun a b => Classical.propDecidable (a = b)) p = char_word p := by
    intro p
    congr 1
    exact Subsingleton.elim _ _
  have hhd : ∀ v w : F → ℤ,
      @hammingDist F (fun _ => ℤ) _ (fun _ a b => Classical.propDecidable (a = b)) v w =
        hammingDist v w := by
    intro v w
    congr 1
  have hex : ∃ p : Polynomial F, p.Monic ∧ Squarefree p ∧ p.natDegree ≤ d ∧
      @hammingDist F (fun _ => ℤ) _ (fun _ a b => Classical.propDecidable (a = b))
        (@char_word F _ _ (fun a b => Classical.propDecidable (a = b)) p) r ≤ e := by
    refine ⟨g, hmonic, hsquarefree, hdeg, ?_⟩
    rw [hhd, hcw]
    exact hdist
  obtain ⟨hpm, hps, hpd, hpr⟩ := hex.choose_spec
  rw [hhd, hcw] at hpr
  refine Eq.trans ?_ (admissible_unique hodd hweil ε hε d e hd he r g hmonic hsquarefree
    hdeg hdist hex.choose hpm hps hpd hpr)
  unfold algorithm_a
  exact dif_pos hex

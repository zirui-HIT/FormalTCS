import Architect
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.ZMod.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators
open Filter

universe u v

@[blueprint "def:canonical-set"
  (statement := /-- For a positive integer \(m\), the canonical set is the set of
  idempotent residue classes
  \[
    S_m^*=\{x\in \mathbb Z/m\mathbb Z:x^2=x\}.
  \] -/)
  (title := /-- Canonical set of residues -/)
  (latexEnv := "definition")]
def canonical_set (m : ℕ) : Set (ZMod m) :=
  {x | x ^ 2 = x}

@[blueprint "def:is-decoding-polynomial"
  (statement := /-- Let \(F\) be a field, let \(m\) be a positive integer, and let
  \(S\subseteq\mathbb Z/m\mathbb Z\).  A polynomial \(P\in F[X]\) is an
  \(S\)-decoding polynomial if there is a primitive \(m\)-th root of unity
  \(\zeta\in F\) such that \(P(1)=1\) and
  \(P(\zeta^{\operatorname{val}(s)})=0\) for every nonzero \(s\in S\). -/)
  (title := /-- Decoding polynomial -/)
  (latexEnv := "definition")]
def is_decoding_polynomial {F : Type u} [Field F]
    (m : ℕ) (S : Set (ZMod m)) (P : Polynomial F) : Prop :=
  ∃ ζ : F,
    IsPrimitiveRoot ζ m ∧
      Polynomial.eval 1 P = 1 ∧
      ∀ s : ZMod m, s ∈ S → s ≠ 0 →
        Polynomial.eval (ζ ^ s.val) P = 0

@[blueprint "def:has-sparse-canonical-decoder"
  (statement := /-- Let \(F\) be a field and let \(m,t\) be natural numbers.
  The canonical set modulo \(m\) has a decoding polynomial of sparsity at most
  \(t\) if there is a decoding polynomial whose support contains at most
  \(t\) exponents. -/)
  (title := /-- Sparse canonical decoder -/)
  (latexEnv := "definition")]
def has_sparse_canonical_decoder {F : Type u} [Field F]
    (m t : ℕ) : Prop :=
  ∃ P : Polynomial F,
    is_decoding_polynomial m (canonical_set m) P ∧ P.support.card ≤ t

@[blueprint "def:polynomial-supported-on-residues"
  (statement := /-- Let \(m\) be a natural number and let
  \(S\subseteq\mathbb Z/m\mathbb Z\).  A polynomial is canonically
  supported on \(S\) if every exponent \(i\) in its support satisfies
  \(i<m\) and the residue of \(i\) modulo \(m\) belongs to \(S\).
  Thus no two supported exponents represent the same residue class. -/)
  (title := /-- Polynomial support on canonical residue representatives -/)
  (latexEnv := "definition")]
def polynomial_supported_on_residues {F : Type u} [Semiring F]
    (m : ℕ) (S : Set (ZMod m)) (P : Polynomial F) : Prop :=
  ∀ i ∈ P.support, i < m ∧ (i : ZMod m) ∈ S

@[blueprint "def:is-zero-interpolating-set"
  (statement := /-- Let \(F\) be a field, \(m\) a natural number,
  \(S\subseteq\mathbb Z/m\mathbb Z\), and \(B\subseteq F\) finite.  The set
  \(B\) is zero-interpolating for \(S\) if every element of \(B\) is an
  \(m\)-th root of unity and, for any two polynomials canonically supported
  on \(S\), equality of their evaluations on \(B\) forces equality of
  their constant coefficients. -/)
  (title := /-- Zero-interpolating set -/)
  (latexEnv := "definition")]
def is_zero_interpolating_set {F : Type u} [Field F]
    (m : ℕ) (S : Set (ZMod m)) (B : Finset F) : Prop :=
  (∀ b ∈ B, b ^ m = 1) ∧
    ∀ P Q : Polynomial F,
      polynomial_supported_on_residues m S P →
      polynomial_supported_on_residues m S Q →
      (∀ b ∈ B, Polynomial.eval b P = Polynomial.eval b Q) →
      P.coeff 0 = Q.coeff 0

@[blueprint "def:has-small-canonical-interpolation-set"
  (statement := /-- Let \(F\) be a field and let \(m,t\) be natural numbers.
  There is a small canonical zero-interpolation set if some finite
  \(B\subseteq F\), of cardinality at most \(t\), is zero-interpolating for
  canonically supported polynomials on \(S_m^*\). -/)
  (title := /-- Small canonical interpolation set -/)
  (latexEnv := "definition")]
def has_small_canonical_interpolation_set {F : Type u} [Field F]
    (m t : ℕ) : Prop :=
  ∃ B : Finset F,
    B.card ≤ t ∧ is_zero_interpolating_set m (canonical_set m) B

@[blueprint "def:is-zero-interpolating-with-multiplicity"
  (statement := /-- Let \(F\) be a field, \(M,e\) natural numbers,
  \(S\subseteq\mathbb Z/M\mathbb Z\), and \(B\subseteq F\) finite.  The set
  \(B\) is zero-interpolating with multiplicity \(e\) for \(S\) if its points
  are \(M\)-th roots of unity and equality on \(B\) of all Hasse derivatives
  of orders below \(e\), for two polynomials canonically supported on \(S\),
  forces equality of their constant coefficients. -/)
  (title := /-- Zero interpolation with multiplicity -/)
  (latexEnv := "definition")]
def is_zero_interpolating_with_multiplicity {F : Type u} [Field F]
    (M : ℕ) (S : Set (ZMod M)) (B : Finset F) (e : ℕ) : Prop :=
  (∀ b ∈ B, b ^ M = 1) ∧
    ∀ P Q : Polynomial F,
      polynomial_supported_on_residues M S P →
      polynomial_supported_on_residues M S Q →
      (∀ b ∈ B, ∀ j < e,
        Polynomial.eval b (Polynomial.hasseDeriv j P) =
          Polynomial.eval b (Polynomial.hasseDeriv j Q)) →
      P.coeff 0 = Q.coeff 0

@[blueprint "def:has-canonical-multiplicity-interpolation"
  (statement := /-- Let \(F\) be a field, let \(m,p,t\) be natural numbers,
  and put \(M=mp\).  Canonical multiplicity interpolation is available if
  there is a set of at most \(t\) field elements which is zero-interpolating
  with multiplicity \(2\) for canonically supported polynomials on
  \(S_M^*\). -/)
  (title := /-- Canonical multiplicity interpolation data -/)
  (latexEnv := "definition")]
def has_canonical_multiplicity_interpolation {F : Type u} [Field F]
    (m p t : ℕ) : Prop :=
  ∃ B : Finset F,
    B.card ≤ t ∧
      is_zero_interpolating_with_multiplicity
        (m * p) (canonical_set (m * p)) B 2

@[blueprint "def:canonical-matching-vector-family"
  (statement := /-- Let \(M,k,n\) be natural numbers.  A canonical matching
  vector family of size \(n\) in \((\mathbb Z/M\mathbb Z)^k\) consists of
  pairs \((u_i,v_i)\) such that
  \(\langle u_i,v_i\rangle=0\), whereas
  \(\langle u_i,v_j\rangle\) is a nonzero member of \(S_M^*\) whenever
  \(i\ne j\). -/)
  (title := /-- Canonical matching-vector family -/)
  (latexEnv := "definition")]
structure canonical_matching_vector_family (M k n : ℕ) where
  left : Fin n → Fin k → ZMod M
  right : Fin n → Fin k → ZMod M
  diagonal :
    ∀ i : Fin n, ∑ a : Fin k, left i a * right i a = 0
  offDiagonal :
    ∀ i j : Fin n, i ≠ j →
      (∑ a : Fin k, left i a * right j a) ∈ canonical_set M ∧
      (∑ a : Fin k, left i a * right j a) ≠ 0

@[blueprint "def:canonical-modular-intersection-family"
  (statement := /-- Let \(D,k,n\) be natural numbers.  A canonical modular
  intersection family of size \(n\) on a \(k\)-element ground set is a family
  \((A_i)_{i<n}\) such that
  \[
    |A_i|\equiv0\pmod D
  \]
  for every \(i\), whereas, for \(i\ne j\), the residue class of
  \(|A_i\cap A_j|\) is a nonzero member of the canonical set \(S_D^*\). -/)
  (title := /-- Canonical modular intersection family -/)
  (latexEnv := "definition")]
structure canonical_modular_intersection_family (D k n : ℕ) where
  blocks : Fin n → Finset (Fin k)
  diagonalCard :
    ∀ i : Fin n, ((blocks i).card : ZMod D) = 0
  offDiagonalCard :
    ∀ i j : Fin n, i ≠ j →
      ((blocks i ∩ blocks j).card : ZMod D) ∈ canonical_set D ∧
      ((blocks i ∩ blocks j).card : ZMod D) ≠ 0

@[blueprint "def:has-large-canonical-matching-vector-families"
  (statement := /-- Let \(M,R\) be natural numbers.  Large canonical
  matching-vector families exist at rank \(R\) if there is \(c>0\) such that,
  for all sufficiently large dimensions \(k\), there is a family of some size
  \(n\) satisfying
  \[
    \exp\!\left(c\,\frac{(\log k)^R}
      {(\log\log k)^{R-1}}\right)\le n.
  \] -/)
  (title := /-- Large matching-vector-family rate -/)
  (latexEnv := "definition")]
def has_large_canonical_matching_vector_families (M R : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ k : ℕ in atTop,
      ∃ n : ℕ, Nonempty (canonical_matching_vector_family M k n) ∧
        Real.exp
            (c * (Real.log (k : ℝ)) ^ R /
              (Real.log (Real.log (k : ℝ))) ^ (R - 1)) ≤
          (n : ℝ)

@[blueprint "def:one-round-pir-scheme"
  (statement := /-- A one-round \(t\)-server PIR scheme for \(n\)-bit
  databases consists of a joint query distribution, deterministic server
  responses, and a reconstruction map.  Perfect correctness means that the
  reconstructed bit has the Dirac distribution at the requested database
  bit.  Information-theoretic privacy means that each individual server's
  query marginal is independent of the requested index.  Finite injective
  encodings of queries and answers specify their bit lengths. -/)
  (title := /-- One-round private information retrieval scheme -/)
  (latexEnv := "definition")]
structure one_round_pir_scheme (servers databaseSize : ℕ) where
  Query : Type
  Answer : Type
  queryBits : ℕ
  answerBits : ℕ
  encodeQuery : Query ↪ (Fin queryBits → Bool)
  encodeAnswer : Answer ↪ (Fin answerBits → Bool)
  query : Fin databaseSize → PMF (Fin servers → Query)
  answer : (Fin databaseSize → Bool) → Fin servers → Query → Answer
  reconstruct : Fin databaseSize → (Fin servers → Answer) → Bool
  correctness :
    ∀ database index,
      PMF.map
          (fun queries =>
            reconstruct index
              (fun server => answer database server (queries server)))
          (query index) =
        PMF.pure (database index)
  privacy :
    ∀ server (i j : Fin databaseSize),
      PMF.map (fun queries => queries server) (query i) =
        PMF.map (fun queries => queries server) (query j)

@[blueprint "def:pir-communication"
  (statement := /-- The total communication of a one-round \(t\)-server
  scheme is \(t\) times the sum of the encoded query length and encoded answer
  length. -/)
  (title := /-- Total PIR communication -/)
  (latexEnv := "definition")]
def pir_communication {t n : ℕ}
    (scheme : one_round_pir_scheme t n) : ℕ :=
  t * (scheme.queryBits + scheme.answerBits)

@[blueprint "def:has-pir-at-matching-vector-cost"
  (statement := /-- Let \(t,M\) be natural numbers.  PIR schemes are available
  at matching-vector cost if there is a constant \(C>0\), independent of
  \(k\) and \(n\), such that every canonical matching-vector family of size
  \(n\) in dimension \(k\) yields a \(t\)-server PIR scheme for \(n\)-bit
  databases with communication at most \(C(k+1)\). -/)
  (title := /-- PIR construction at matching-vector cost -/)
  (latexEnv := "definition")]
def has_pir_at_matching_vector_cost (t M : ℕ) : Prop :=
  ∃ C : ℕ, 0 < C ∧
    ∀ {k n : ℕ}, canonical_matching_vector_family M k n →
      ∃ scheme : one_round_pir_scheme t n,
        pir_communication scheme ≤ C * (k + 1)

@[blueprint "def:has-target-communication-rate"
  (statement := /-- Let \(t,r\) be natural numbers.  A family of
  \(t\)-server PIR schemes has communication
  \(\exp(\widetilde O((\log n)^{1/(r+1)}))\) if the logarithm of its
  communication is, as \(n\to\infty\), bounded in Big-O by
  \[
    (\log n)^{1/(r+1)}(\log\log n)^d
  \]
  for some natural number \(d\). -/)
  (title := /-- Target soft-exponential communication rate -/)
  (latexEnv := "definition")]
def has_target_communication_rate (t r : ℕ) : Prop :=
  ∃ schemes : (n : ℕ) → one_round_pir_scheme t n,
    ∃ d : ℕ,
      Asymptotics.IsBigO atTop
        (fun n : ℕ => Real.log ((pir_communication (schemes n) : ℕ) : ℝ))
        (fun n : ℕ =>
          Real.rpow (Real.log (n : ℝ)) (1 / ((r + 1 : ℕ) : ℝ)) *
            (Real.log (Real.log (n : ℝ))) ^ d)

@[blueprint "lem:sparse-decoder-yields-small-zero-interpolation"
  (statement := /-- Let \(F\) be a field, let \(m>0\), and let \(t\) be a
  natural number.  If \(S_m^*\) has a decoding polynomial over \(F\) with at
  most \(t\) monomials, then \(S_m^*\) has a zero-interpolating set in \(F\)
  of cardinality at most \(t\) for polynomials supported on the canonical
  representatives of \(S_m^*\). -/)
  (proof := /-- Unpack
  \cref{def:has-sparse-canonical-decoder,def:is-decoding-polynomial} to obtain
  a polynomial \(P\), a primitive \(m\)-th root \(\zeta\), the identities
  \(P(1)=1\) and \(P(\zeta^{s})=0\) for every nonzero
  \(s\in S_m^*\), and the bound \(|\operatorname{supp}(P)|\le t\).  Let
  \[
    B=\{\zeta^d:d\in\operatorname{supp}(P)\}.
  \]
  Taking an image cannot increase cardinality, so \(|B|\le t\); moreover,
  every \(b\in B\) satisfies \(b^m=1\) because \(\zeta^m=1\).

  Let \(A\) satisfy the canonical-support condition of
  \cref{def:polynomial-supported-on-residues} for the set in
  \cref{def:canonical-set}.  Expanding both polynomial evaluations over their
  finite supports, interchanging the two sums, and using
  \((\zeta^d)^i=(\zeta^i)^d\) gives
  \[
    \sum_{d\in\operatorname{supp}(P)}[Y^d]P\,A(\zeta^d)
      =\sum_{i\in\operatorname{supp}(A)}[Z^i]A\,P(\zeta^i).
  \]
  If \(i\in\operatorname{supp}(A)\), then \(i<m\) and its residue belongs to
  \(S_m^*\).  For \(i\ne0\), the inequality \(i<m\) shows that this residue
  is nonzero and has canonical representative \(i\), so the corresponding
  value of \(P\) vanishes.  The term with \(i=0\) is \([Z^0]A\), since
  \(P(1)=1\); if zero is absent from the support, this coefficient is zero.
  Hence the displayed sum equals \([Z^0]A\).

  Apply this identity to two canonically supported polynomials having equal
  evaluations on \(B\).  Their weighted sums agree term by term, and therefore
  their constant coefficients agree.  Together with the root and cardinality
  properties of \(B\), this is exactly
  \cref{def:is-zero-interpolating-set,def:has-small-canonical-interpolation-set}.
  -/)
  (title := /-- Sparse decoding gives zero interpolation -/)
  (latexEnv := "lemma")]
lemma sparse_decoder_yields_small_zero_interpolation
    {F : Type u} [Field F] {m t : ℕ} (hm : 0 < m)
    (hdecoder : has_sparse_canonical_decoder (F := F) m t) :
    has_small_canonical_interpolation_set (F := F) m t := by
  classical
  rcases hdecoder with ⟨P, ⟨ζ, hζ, hP_one, hP_zero⟩, hP_card⟩
  let B : Finset F := P.support.image (fun d => ζ ^ d)
  refine ⟨B, ?_, ?_, ?_⟩
  · exact (Finset.card_image_le.trans hP_card)
  · intro b hb
    rcases Finset.mem_image.mp hb with ⟨d, hd, rfl⟩
    rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · intro R Q hR hQ heval
    have recover (A : Polynomial F)
        (hA : polynomial_supported_on_residues m (canonical_set m) A) :
        ∑ d ∈ P.support, P.coeff d * Polynomial.eval (ζ ^ d) A = A.coeff 0 := by
      calc
        ∑ d ∈ P.support, P.coeff d * Polynomial.eval (ζ ^ d) A =
            ∑ d ∈ P.support, ∑ i ∈ A.support,
              P.coeff d * (A.coeff i * (ζ ^ d) ^ i) := by
                simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
        _ = ∑ i ∈ A.support, ∑ d ∈ P.support,
              A.coeff i * (P.coeff d * (ζ ^ i) ^ d) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro i hi
                apply Finset.sum_congr rfl
                intro d hd
                rw [← pow_mul ζ d i, ← pow_mul ζ i d, Nat.mul_comm d i]
                ring
        _ = ∑ i ∈ A.support, A.coeff i * Polynomial.eval (ζ ^ i) P := by
              simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
        _ = A.coeff 0 := by
              rw [Finset.sum_eq_single 0]
              · simp [hP_one]
              · intro i hi hi_ne
                obtain ⟨hi_lt, hi_canonical⟩ := hA i hi
                have hi_cast_ne : (i : ZMod m) ≠ 0 := by
                  intro hi_zero
                  have hi_val := congrArg ZMod.val hi_zero
                  exact hi_ne (by simpa [ZMod.val_natCast_of_lt hi_lt] using hi_val)
                have hi_eval := hP_zero (i : ZMod m) hi_canonical hi_cast_ne
                rw [ZMod.val_natCast_of_lt hi_lt] at hi_eval
                rw [hi_eval, mul_zero]
              · intro h0
                have hc0 : A.coeff 0 = 0 := Polynomial.notMem_support_iff.mp h0
                simp [hc0]
    rw [← recover R hR, ← recover Q hQ]
    apply Finset.sum_congr rfl
    intro d hd
    rw [heval (ζ ^ d) (Finset.mem_image.mpr ⟨d, hd, rfl⟩)]

@[blueprint "lem:canonical-zero-interpolation-lifts-to-multiplicity"
  (statement := /-- Let \(p\) be prime, let \(p\nmid m\), let \(F\) be a
  field of characteristic \(p\), and let \(t\) be a natural number.  If the
  canonical set modulo \(m\) has a zero-interpolating set of size at most
  \(t\) for canonically supported polynomials, then the canonical set modulo
  \(mp\) has a zero-interpolating set of multiplicity \(2\) and size at
  most \(t\), again with canonical exponent representatives. -/)
  (proof := /-- Choose a set \(B\) witnessing
  \cref{def:has-small-canonical-interpolation-set}.  By
  \cref{def:is-zero-interpolating-set}, every \(b\in B\) satisfies
  \(b^m=1\), and hence \(b^{mp}=1\).

  For a polynomial \(R\) supported as in
  \cref{def:polynomial-supported-on-residues} on
  \(S_{mp}^*\), define
  \[
    L_R(Z)=\sum_{i\in\operatorname{supp}(R)}
      (1-\overline i)\,R_i Z^{i\bmod m},
  \]
  where \(\overline i\) denotes the image of \(i\) in \(F\).
  The idempotence condition from \cref{def:canonical-set}, mapped to the
  field \(F\) of characteristic \(p\), gives
  \(\overline i^2=\overline i\), so
  \(\overline i\in\{0,1\}\).  Mapping the same condition to
  \(\mathbb Z/m\mathbb Z\) shows that \(L_R\) is canonically supported
  modulo \(m\).

  For \(b\in B\), the equality \(b^m=1\) gives
  \(b^{i\bmod m}=b^i\).  Expanding the first Hasse derivative therefore
  yields
  \[
    L_R(b)=R(b)-bR^{[1]}(b).
  \]
  Thus, if two canonically supported polynomials \(P,Q\) have equal
  derivatives of orders zero and one on \(B\), then
  \(L_P\) and \(L_Q\) have equal values on \(B\).

  It remains to identify their constant coefficients.  A contributing
  exponent satisfies \(m\mid i\).  If also \(\overline i=0\), then
  \(p\mid i\); since \(m\) and \(p\) are coprime and \(i<mp\), this
  forces \(i=0\).  Every nonzero exponent divisible by \(m\) therefore has
  \(\overline i=1\) and is killed by the factor
  \(1-\overline i\).  Consequently
  \(L_R(0)=R_0\).  Applying the zero-interpolation implication in
  \cref{def:is-zero-interpolating-set} to \(L_P,L_Q\) proves
  \(P_0=Q_0\).  Together with the unchanged cardinality bound and the
  root-of-unity observation, this is precisely
  \cref{def:is-zero-interpolating-with-multiplicity} with multiplicity
  \(2\), and hence
  \cref{def:has-canonical-multiplicity-interpolation}. -/)
  (title := /-- Canonical interpolation lifts to multiplicity two -/)
  (latexEnv := "lemma")]
lemma canonical_zero_interpolation_lifts_to_multiplicity
    {F : Type u} [Field F] {m p t : ℕ}
    [CharP F p] (hp : p.Prime) (hcoprime : ¬p ∣ m)
    (hinterpolation :
      has_small_canonical_interpolation_set (F := F) m t) :
    has_canonical_multiplicity_interpolation (F := F) m p t := by
  rcases hinterpolation with ⟨B, hcard, hroot, hinterp⟩
  refine ⟨B, hcard, ?_, ?_⟩
  · intro b hb
    rw [pow_mul, hroot b hb, one_pow]
  · intro P Q hP hQ hderiv
    have hmpos : 0 < m := by
      by_contra hm
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      exact hcoprime (hm0 ▸ dvd_zero p)
    let lower : Polynomial F → Polynomial F := fun R =>
      R.support.sum fun i =>
        Polynomial.monomial (i % m) ((1 - (i : F)) * R.coeff i)
    have cast_zero_or_one (R : Polynomial F)
        (hR : polynomial_supported_on_residues (m * p) (canonical_set (m * p)) R)
        (i : ℕ) (hi : i ∈ R.support) : (i : F) = 0 ∨ (i : F) = 1 := by
      have hc := (hR i hi).2
      have hpdiv : p ∣ m * p := Nat.dvd_mul_left p m
      have hmap := congrArg (ZMod.castHom hpdiv F) hc
      have hidem : (i : F) ^ 2 = (i : F) := by
        simpa [canonical_set] using hmap
      exact eq_zero_or_one_of_sq_eq_self hidem
    have lower_supported (R : Polynomial F)
        (hR : polynomial_supported_on_residues (m * p) (canonical_set (m * p)) R) :
        polynomial_supported_on_residues m (canonical_set m) (lower R) := by
      intro k hk
      have hkne : (lower R).coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk
      simp only [lower, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial] at hkne
      obtain ⟨i, hi, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hkne
      split at hterm
      next hik =>
        subst k
        refine ⟨Nat.mod_lt i hmpos, ?_⟩
        have hc := (hR i hi).2
        have hmap := congrArg
          (ZMod.castHom (Nat.dvd_mul_right m p) (ZMod m)) hc
        simpa [canonical_set] using hmap
      next hik =>
        exact (hterm rfl).elim
    have lower_eval (R : Polynomial F) (b : F) (hb : b ∈ B) :
        Polynomial.eval b (lower R) =
          Polynomial.eval b R -
            b * Polynomial.eval b (Polynomial.hasseDeriv 1 R) := by
      dsimp only [lower]
      rw [Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_monomial]
      rw [Polynomial.eval_eq_sum, Polynomial.hasseDeriv_one',
        Polynomial.derivative_eval]
      simp only [Polynomial.sum_def]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hpow : b ^ (i % m) = b ^ i := by
        nth_rewrite 2 [← Nat.mod_add_div i m]
        rw [pow_add, pow_mul, hroot b hb, one_pow, mul_one]
      rw [hpow]
      by_cases hi0 : i = 0
      · simp [hi0]
      · have hipos : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
        have hpow_succ : b ^ (i - 1) * b = b ^ i := by
          rw [← pow_succ, Nat.sub_add_cancel hipos]
        rw [← hpow_succ]
        ring
    have cast_eq_one_of_mod_eq_zero (R : Polynomial F)
        (hR : polynomial_supported_on_residues (m * p) (canonical_set (m * p)) R)
        (i : ℕ) (hi : i ∈ R.support) (himod : i % m = 0) (hi0 : i ≠ 0) :
        (i : F) = 1 := by
      rcases cast_zero_or_one R hR i hi with hz | ho
      · have hpdvd : p ∣ i := (CharP.cast_eq_zero_iff F p i).mp hz
        have hmdvd : m ∣ i := Nat.dvd_of_mod_eq_zero himod
        have hcop : Nat.Coprime m p :=
          (hp.coprime_iff_not_dvd.mpr hcoprime).symm
        have hmpdvd : m * p ∣ i :=
          hcop.mul_dvd_of_dvd_of_dvd hmdvd hpdvd
        exact (hi0 (Nat.eq_zero_of_dvd_of_lt hmpdvd (hR i hi).1)).elim
      · exact ho
    have lower_coeff_zero (R : Polynomial F)
        (hR : polynomial_supported_on_residues (m * p) (canonical_set (m * p)) R) :
        (lower R).coeff 0 = R.coeff 0 := by
      dsimp only [lower]
      rw [Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_monomial]
      calc
        (∑ i ∈ R.support,
            if i % m = 0 then (1 - (i : F)) * R.coeff i else 0) =
            ∑ i ∈ R.support, if i = 0 then R.coeff 0 else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases himod : i % m = 0
              · by_cases hi0 : i = 0
                · simp [hi0]
                · rw [if_pos himod, if_neg hi0,
                    cast_eq_one_of_mod_eq_zero R hR i hi himod hi0]
                  simp
              · have hi0 : i ≠ 0 := by
                  intro hi0
                  subst i
                  simp at himod
                simp [himod, hi0]
        _ = R.coeff 0 := by
          by_cases hzero : 0 ∈ R.support
          · simp [hzero]
          · rw [Polynomial.notMem_support_iff.mp hzero]
            simp [hzero]
    have hlower :
        ∀ b ∈ B, Polynomial.eval b (lower P) = Polynomial.eval b (lower Q) := by
      intro b hb
      rw [lower_eval P b hb, lower_eval Q b hb]
      have hvalue : Polynomial.eval b P = Polynomial.eval b Q := by
        simpa using hderiv b hb 0 (by omega)
      rw [hvalue, hderiv b hb 1 (by omega)]
    have hcoeff := hinterp (lower P) (lower Q)
      (lower_supported P hP) (lower_supported Q hQ) hlower
    rwa [lower_coeff_zero P hP, lower_coeff_zero Q hQ] at hcoeff

@[blueprint "def:bbr-separating-polynomial"
  (statement := /-- Let \(D,\ell,d\) be natural numbers.  A BBR separating
  polynomial of length \(\ell\) and binomial degree at most \(d\) modulo
  \(D\) is a tuple \(a_0,\ldots,a_d\in\mathbb Z/D\mathbb Z\).  Writing
  \[
    P(s)=\sum_{j=0}^{d}a_j\binom{s}{j},
  \]
  one requires \(P(0)=0\), while \(P(s)\) is a nonzero idempotent modulo
  \(D\) for every integer \(s\) with \(1\leq s\leq\ell\). -/)
  (title := /-- BBR separating polynomial in the binomial basis -/)
  (latexEnv := "definition")]
structure bbr_separating_polynomial
    (D length degree : ℕ) where
  coefficient : Fin (degree + 1) → ZMod D
  valueAtZero :
    (∑ j : Fin (degree + 1),
      coefficient j * (Nat.choose 0 (j : ℕ) : ZMod D)) = 0
  separates :
    ∀ s : ℕ, 0 < s → s ≤ length →
      (∑ j : Fin (degree + 1),
        coefficient j * (Nat.choose s (j : ℕ) : ZMod D)) ∈
          canonical_set D ∧
      (∑ j : Fin (degree + 1),
        coefficient j * (Nat.choose s (j : ℕ) : ZMod D)) ≠ 0

@[blueprint "lem:bbr-polynomial-construction"
  (statement := /-- Let \(D>0\) be squarefree with exactly \(R\geq2\)
  distinct prime factors.  There is a positive integer \(C\), depending
  only on \(D\), such that for every \(\ell\) there is a BBR separating
  polynomial modulo \(D\) of some binomial degree \(d\) satisfying
  \[
    d^R\leq C(\ell+1).
  \] -/)
  (proof := /-- Fix \(\ell\), and let \(M\) be the least natural number
  satisfying \(\ell+1\leq M^R\).  Minimality gives
  \[
    M^R\leq 2^R(\ell+1).
  \]
  For every prime divisor \(q\) of \(D\), let \(a_q\) be least with
  \(M\leq q^{a_q}\).  Then \(q^{a_q}\leq qM\leq DM\), while
  \[
    \prod_{q\mid D}q^{a_q}\geq M^R>\ell.
  \]

  Put \(d=DM\).  For each \(q\mid D\), the Chinese remainder theorem
  supplies a selector \(e_q\in\mathbb Z/D\mathbb Z\) whose reduction is
  \(1\) modulo \(q\) and \(0\) modulo every other prime divisor of \(D\).
  For \(0\leq j\leq d\), define
  \[
    c_j=\sum_{q\mid D}e_q\,\mathbf 1_{j<q^{a_q}}
      \bigl(\mathbf 1_{j=0}-(-1)^j\bigr).
  \]
  Thus \(c_0=0\).

  We verify the values componentwise.  In characteristic \(q\), the
  identity
  \[
    (X+1)^{q^{a_q}}=X^{q^{a_q}}+1
  \]
  shows by comparing coefficients that
  \(\binom{n+q^{a_q}}{k}=\binom nk\) whenever \(k<q^{a_q}\).
  Induction on \(s\) consequently gives
  \[
    \binom{s-1}{q^{a_q}-1}
      =\mathbf 1_{q^{a_q}\mid s}\quad\text{in }\mathbb Z/q\mathbb Z.
  \]
  The alternating binomial identity, together with
  \((-1)^{q^{a_q}-1}=1\) in \(\mathbb Z/q\mathbb Z\), now yields
  \[
    \sum_{j=0}^{d}c_j\binom sj
      =1-\mathbf 1_{q^{a_q}\mid s}
      \quad\text{modulo }q.
  \]
  Hence every component of this value is \(0\) or \(1\), so squarefreeness
  of \(D\) makes the value idempotent modulo \(D\).  If all components
  vanished for some \(1\leq s\leq\ell\), the pairwise coprime prime powers
  \(q^{a_q}\) would have product dividing \(s\), contrary to the strict
  inequality above.  The coefficients therefore form a separating
  polynomial in the sense of
  \cref{def:bbr-separating-polynomial}.

  Finally,
  \[
    d^R=D^RM^R\leq (2D)^R(\ell+1).
  \]
  Taking \(C=(2D)^R>0\) proves the assertion uniformly in \(\ell\). -/)
  (title := /-- BBR low-degree polynomial construction -/)
  (latexEnv := "lemma")]
lemma bbr_polynomial_construction
    {D R : ℕ} (hDpos : 0 < D)
    (hDsquarefree : ∏ q ∈ D.primeFactors, q = D)
    (hR : D.primeFactors.card = R) (hRtwo : 2 ≤ R) :
    ∃ C : ℕ, 0 < C ∧
      ∀ length : ℕ,
        ∃ degree : ℕ,
          Nonempty (bbr_separating_polynomial D length degree) ∧
          degree ^ R ≤ C * (length + 1) := by
  classical
  letI : NeZero D := ⟨Nat.ne_of_gt hDpos⟩
  have prime_mem_of_dvd_prod (p : ℕ) (S : Finset ℕ) (hpp : p.Prime)
      (hprime : ∀ q ∈ S, q.Prime) (hdvd : p ∣ ∏ q ∈ S, q) :
      p ∈ S := by
    induction S using Finset.induction_on with
    | empty =>
        simp at hdvd
        exact (hpp.ne_one hdvd).elim
    | @insert q S hqS ih =>
        rw [Finset.prod_insert hqS] at hdvd
        rcases hpp.dvd_mul.mp hdvd with hpq | hdvd
        · have hpqeq : p = q := by
            rcases (Nat.dvd_prime (hprime q (by simp))).mp hpq with hpone | hpqeq
            · exact (hpp.ne_one hpone).elim
            · exact hpqeq
          simp [hpqeq]
        · exact Finset.mem_insert_of_mem (ih (fun r hr => hprime r (by simp [hr])) hdvd)
  have modEq_prod_primes (S : Finset ℕ) (x y : ℕ)
      (hprime : ∀ p ∈ S, p.Prime)
      (hmod : ∀ p ∈ S, x ≡ y [MOD p]) :
      x ≡ y [MOD ∏ p ∈ S, p] := by
    induction S using Finset.induction_on with
    | empty =>
        exact Nat.modEq_one
    | @insert p S hpS ih =>
        have hpp : p.Prime := hprime p (by simp)
        have hcop : p.Coprime (∏ q ∈ S, q) := by
          rw [hpp.coprime_iff_not_dvd]
          intro hdvd
          exact hpS (prime_mem_of_dvd_prod p S hpp
            (fun q hq => hprime q (by simp [hq])) hdvd)
        rw [Finset.prod_insert hpS]
        refine (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨?_, ?_⟩
        · exact hmod p (by simp)
        · apply ih
          · intro q hq
            exact hprime q (by simp [hq])
          · intro q hq
            exact hmod q (by simp [hq])
  have zmod_ext (x y : ZMod D)
      (hxy : ∀ p (hp : p ∈ D.primeFactors),
        ZMod.castHom ((Nat.mem_primeFactors.mp hp).2.1) (ZMod p) x =
          ZMod.castHom ((Nat.mem_primeFactors.mp hp).2.1) (ZMod p) y) :
      x = y := by
    rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y]
    apply (ZMod.natCast_eq_natCast_iff x.val y.val D).mpr
    have hm : x.val ≡ y.val [MOD ∏ p ∈ D.primeFactors, p] := by
      apply modEq_prod_primes
      · intro p hp
        exact Nat.prime_of_mem_primeFactors hp
      · intro p hp
        have h := hxy p hp
        apply (ZMod.natCast_eq_natCast_iff x.val y.val p).mp
        have hcast : (ZMod.cast x : ZMod p) = ZMod.cast y := by
          simpa only [ZMod.castHom_apply] using h
        exact (ZMod.natCast_val x).trans
          (hcast.trans (ZMod.natCast_val y).symm)
    simpa only [hDsquarefree] using hm
  refine ⟨(2 * D) ^ R, by positivity, ?_⟩
  intro length
  have hRpos : 0 < R := by omega
  have hexM : ∃ m : ℕ, length + 1 ≤ m ^ R :=
    ⟨length + 1, Nat.le_pow hRpos⟩
  let M := Nat.find hexM
  have hMroot : length + 1 ≤ M ^ R := Nat.find_spec hexM
  have hMpos : 0 < M := by
    by_contra h
    have hMzero : M = 0 := Nat.eq_zero_of_not_pos h
    simp [hMzero, hRpos.ne'] at hMroot
  have hMbound : M ^ R ≤ 2 ^ R * (length + 1) := by
    by_cases hMone : M = 1
    · simp [hMone]
      have htwo : 0 < 2 ^ R := pow_pos (by omega) R
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero htwo.ne' (Nat.succ_ne_zero length))
    · have hMtwo : 2 ≤ M := by omega
      have hpredlt : M - 1 < M := by omega
      have hnot := Nat.find_min hexM hpredlt
      have hlt : (M - 1) ^ R < length + 1 := Nat.lt_of_not_ge hnot
      have hdouble : M ≤ 2 * (M - 1) := by omega
      calc
        M ^ R ≤ (2 * (M - 1)) ^ R := Nat.pow_le_pow_left hdouble R
        _ = 2 ^ R * (M - 1) ^ R := by rw [Nat.mul_pow]
        _ ≤ 2 ^ R * (length + 1) :=
          Nat.mul_le_mul_left _ (Nat.le_of_lt hlt)
  have two_pow_ge (n : ℕ) : n ≤ 2 ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.pow_succ]
        have hone : 1 ≤ 2 ^ n :=
          Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
        simpa [Nat.mul_succ] using Nat.add_le_add ih hone
  have hexponent (q : ↥D.primeFactors) :
      ∃ a : ℕ, M ≤ (q : ℕ) ^ a := by
    have hqprime : (q : ℕ).Prime :=
      Nat.prime_of_mem_primeFactors q.property
    refine ⟨M, (two_pow_ge M).trans ?_⟩
    exact Nat.pow_le_pow_left hqprime.two_le M
  let exponent : ↥D.primeFactors → ℕ :=
    fun q => Nat.find (hexponent q)
  have hexponent_lower (q : ↥D.primeFactors) :
      M ≤ (q : ℕ) ^ exponent q :=
    Nat.find_spec (hexponent q)
  have hexponent_upper (q : ↥D.primeFactors) :
      (q : ℕ) ^ exponent q ≤ (q : ℕ) * M := by
    by_cases ha : exponent q = 0
    · simp [ha, hMpos]
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero
          (Nat.prime_of_mem_primeFactors q.property).ne_zero hMpos.ne')
    · obtain ⟨a, haeq⟩ := Nat.exists_eq_succ_of_ne_zero ha
      have hminimal := Nat.find_min (hexponent q) (show a < exponent q by omega)
      have hpowlt : (q : ℕ) ^ a < M := Nat.lt_of_not_ge hminimal
      rw [haeq, Nat.pow_succ]
      simpa [Nat.mul_comm] using
        Nat.mul_le_mul_right (q : ℕ) (Nat.le_of_lt hpowlt)
  have hprime_power_le_degree (q : ↥D.primeFactors) :
      (q : ℕ) ^ exponent q ≤ D * M := by
    refine (hexponent_upper q).trans ?_
    exact Nat.mul_le_mul_right M
      (Nat.le_of_dvd hDpos (Nat.dvd_of_mem_primeFactors q.property))
  have hproduct_large :
      length < ∏ q : ↥D.primeFactors, (q : ℕ) ^ exponent q := by
    have hprod :
        M ^ D.primeFactors.card ≤
          ∏ q : ↥D.primeFactors, (q : ℕ) ^ exponent q := by
      simpa using
        (Finset.prod_le_prod (s := Finset.univ)
          (fun q _ => Nat.zero_le M)
          (fun q _ => hexponent_lower q))
    have : length < M ^ R := lt_of_lt_of_le (Nat.lt_succ_self length) hMroot
    rw [hR] at hprod
    exact this.trans_le hprod
  let complement (q : ↥D.primeFactors) : ℕ :=
    ∏ r ∈ D.primeFactors.erase (q : ℕ), r
  have hcomplement_coprime (q : ↥D.primeFactors) :
      (q : ℕ).Coprime (complement q) := by
    have hqprime : (q : ℕ).Prime :=
      Nat.prime_of_mem_primeFactors q.property
    rw [hqprime.coprime_iff_not_dvd]
    intro hdvd
    have hmem := prime_mem_of_dvd_prod (q : ℕ)
      (D.primeFactors.erase (q : ℕ)) hqprime
      (fun r hr => Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hr))
      hdvd
    exact (Finset.mem_erase.mp hmem).1 rfl
  let eNat (q : ↥D.primeFactors) : ℕ :=
    (Nat.chineseRemainder (hcomplement_coprime q) 1 0).val
  have eNat_mod_self (q : ↥D.primeFactors) :
      eNat q ≡ 1 [MOD (q : ℕ)] :=
    (Nat.chineseRemainder (hcomplement_coprime q) 1 0).property.1
  have eNat_mod_other (q r : ↥D.primeFactors) (hqr : q ≠ r) :
      eNat q ≡ 0 [MOD (r : ℕ)] := by
    apply (Nat.chineseRemainder
      (hcomplement_coprime q) 1 0).property.2.of_dvd
    change (r : ℕ) ∣ complement q
    dsimp only [complement]
    apply Finset.dvd_prod_of_mem id
    exact Finset.mem_erase.mpr
      ⟨fun h => hqr (Subtype.ext h.symm), r.property⟩
  have cast_eNat (q r : ↥D.primeFactors) :
      ZMod.castHom (Nat.dvd_of_mem_primeFactors r.property) (ZMod (r : ℕ))
          (eNat q : ZMod D) =
        if q = r then 1 else 0 := by
    rw [ZMod.castHom_apply,
      ZMod.cast_natCast (Nat.dvd_of_mem_primeFactors r.property)]
    split_ifs with hqr
    · subst r
      simpa using (ZMod.natCast_eq_natCast_iff _ _ (q : ℕ)).mpr
        (eNat_mod_self q)
    · simpa using (ZMod.natCast_eq_natCast_iff _ _ (r : ℕ)).mpr
        (eNat_mod_other q r hqr)
  have choose_periodic (p a n k : ℕ) (hp : p.Prime)
      (hk : k < p ^ a) :
      (Nat.choose (n + p ^ a) k : ZMod p) =
        (Nat.choose n k : ZMod p) := by
    letI : Fact p.Prime := ⟨hp⟩
    calc
      (Nat.choose (n + p ^ a) k : ZMod p) =
          (((Polynomial.X + 1) ^ (n + p ^ a) :
            Polynomial (ZMod p))).coeff k :=
        (Polynomial.coeff_X_add_one_pow (ZMod p) (n + p ^ a) k).symm
      _ = (((Polynomial.X + 1) ^ n *
          (Polynomial.X + 1) ^ (p ^ a) :
            Polynomial (ZMod p))).coeff k := by rw [pow_add]
      _ = (((Polynomial.X + 1) ^ n *
          (Polynomial.X ^ (p ^ a) + 1) :
            Polynomial (ZMod p))).coeff k := by
        rw [add_pow_char_pow]
        simp only [one_pow]
      _ = (((Polynomial.X + 1) ^ n :
            Polynomial (ZMod p))).coeff k := by
        rw [mul_add, mul_one, Polynomial.coeff_add,
          Polynomial.coeff_mul_X_pow']
        simp [Nat.not_le_of_lt hk]
      _ = (Nat.choose n k : ZMod p) :=
        Polynomial.coeff_X_add_one_pow (ZMod p) n k
  have choose_indicator (p a s : ℕ) (hp : p.Prime) (hs : 0 < s) :
      (Nat.choose (s - 1) (p ^ a - 1) : ZMod p) =
        if p ^ a ∣ s then 1 else 0 := by
    have hpowpos : 0 < p ^ a := pow_pos hp.pos a
    induction s using Nat.strong_induction_on with
    | h s ih =>
        by_cases hle : s ≤ p ^ a
        · by_cases heq : s = p ^ a
          · subst s
            simp
          · have hlt : s < p ^ a := lt_of_le_of_ne hle heq
            have hchoose :
                Nat.choose (s - 1) (p ^ a - 1) = 0 :=
              Nat.choose_eq_zero_of_lt (by omega)
            have hndvd : ¬p ^ a ∣ s := by
              intro hdvd
              have := Nat.le_of_dvd hs hdvd
              omega
            simp [hchoose, hndvd]
        · have hgt : p ^ a < s := Nat.lt_of_not_ge hle
          have hperiod := choose_periodic p a (s - p ^ a - 1)
            (p ^ a - 1) hp (by omega)
          have harg : s - p ^ a - 1 + p ^ a = s - 1 := by omega
          rw [harg] at hperiod
          have hih := ih (s - p ^ a) (by omega) (by omega)
          have hdvdiff : p ^ a ∣ s ↔ p ^ a ∣ s - p ^ a := by
            constructor
            · intro hdvd
              exact Nat.dvd_sub hdvd (dvd_refl (p ^ a))
            · intro hdvd
              rw [← Nat.sub_add_cancel hgt.le]
              exact dvd_add hdvd (dvd_refl (p ^ a))
          rw [hperiod, hih]
          by_cases hd : p ^ a ∣ s
          · simp [hd, hdvdiff.mp hd]
          · have hd' : ¬p ^ a ∣ s - p ^ a :=
              fun h => hd (hdvdiff.mpr h)
            simp [hd, hd']
  have alternating_choose (p s k : ℕ) (hs : 0 < s) :
      (∑ j ∈ Finset.range (k + 1),
          (-1 : ZMod p) ^ j * (Nat.choose s j : ZMod p)) =
        (-1 : ZMod p) ^ k * (Nat.choose (s - 1) k : ZMod p) := by
    induction k with
    | zero =>
        simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        have hchoose :
            Nat.choose s (k + 1) =
              Nat.choose (s - 1) k + Nat.choose (s - 1) (k + 1) := by
          simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel hs] using
            Nat.choose_succ_succ (s - 1) k
        rw [hchoose]
        push_cast
        ring
  have neg_one_pow_prime_power_sub_one (p a : ℕ) (hp : p.Prime) :
      (-1 : ZMod p) ^ (p ^ a - 1) = 1 := by
    rcases hp.eq_two_or_odd with hp2 | hpodd
    · subst p
      have hneg : (-1 : ZMod 2) = 1 := by decide
      simp [hneg]
    · have hpodd' : Odd p := Nat.odd_iff.mpr hpodd
      have hpowodd : Odd (p ^ a) := hpodd'.pow
      obtain ⟨t, ht⟩ := hpowodd
      have hpow : p ^ a - 1 = 2 * t := by omega
      rw [hpow, pow_mul]
      norm_num
  let degree := D * M
  let componentCoefficient (q : ↥D.primeFactors) (j : ℕ) : ZMod D :=
    if j < (q : ℕ) ^ exponent q then
      (if j = 0 then 1 else 0) - (-1) ^ j
    else 0
  let coefficient : Fin (degree + 1) → ZMod D :=
    fun j => ∑ q : ↥D.primeFactors,
      (eNat q : ZMod D) * componentCoefficient q j
  have coefficient_cast (r : ↥D.primeFactors) (j : Fin (degree + 1)) :
      ZMod.castHom (Nat.dvd_of_mem_primeFactors r.property) (ZMod (r : ℕ))
          (coefficient j) =
        if (j : ℕ) < (r : ℕ) ^ exponent r then
          (if (j : ℕ) = 0 then 1 else 0) - (-1) ^ (j : ℕ)
        else 0 := by
    simp only [coefficient, componentCoefficient, map_sum, map_mul, map_sub,
      map_pow, map_neg, map_one, map_zero, cast_eNat]
    simp
    by_cases hjlt : (j : ℕ) < (r : ℕ) ^ exponent r
    · rw [if_pos hjlt, if_pos hjlt,
        ZMod.cast_sub (Nat.dvd_of_mem_primeFactors r.property),
        ZMod.cast_pow (Nat.dvd_of_mem_primeFactors r.property),
        ZMod.cast_neg (Nat.dvd_of_mem_primeFactors r.property),
        ZMod.cast_one (Nat.dvd_of_mem_primeFactors r.property)]
      by_cases hjzero : j = 0
      · subst j
        simp only [Fin.val_zero, eq_self, if_true, pow_zero]
        rw [ZMod.cast_one (Nat.dvd_of_mem_primeFactors r.property)]
      · have hjval : (j : ℕ) ≠ 0 :=
          fun h => hjzero (Fin.eq_of_val_eq h)
        simp only [if_neg hjzero, if_neg hjval]
        rw [ZMod.cast_zero]
    · simp [hjlt, ZMod.cast_zero]
  let value (s : ℕ) : ZMod D :=
    ∑ j : Fin (degree + 1),
      coefficient j * (Nat.choose s (j : ℕ) : ZMod D)
  have value_cast (r : ↥D.primeFactors) (s : ℕ) (hs : 0 < s) :
      ZMod.castHom (Nat.dvd_of_mem_primeFactors r.property) (ZMod (r : ℕ))
          (value s) =
        if (r : ℕ) ^ exponent r ∣ s then 0 else 1 := by
    rw [show value s =
      ∑ j : Fin (degree + 1),
        coefficient j * (Nat.choose s (j : ℕ) : ZMod D) by rfl]
    simp only [map_sum, map_mul, coefficient_cast, map_natCast]
    rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ =>
        (if j < (r : ℕ) ^ exponent r then
          (if j = 0 then 1 else 0) - (-1 : ZMod (r : ℕ)) ^ j
        else 0) * (Nat.choose s j : ZMod (r : ℕ))) (degree + 1)]
    have hpowpos : 0 < (r : ℕ) ^ exponent r :=
      pow_pos (Nat.prime_of_mem_primeFactors r.property).pos _
    have hsubset :
        Finset.range ((r : ℕ) ^ exponent r) ⊆
          Finset.range (degree + 1) :=
      Finset.range_mono (by
        change (r : ℕ) ^ exponent r ≤ D * M + 1
        exact (hprime_power_le_degree r).trans (Nat.le_succ _))
    calc
      (∑ j ∈ Finset.range (degree + 1),
          (if j < (r : ℕ) ^ exponent r then
            (if j = 0 then 1 else 0) - (-1 : ZMod (r : ℕ)) ^ j
          else 0) * (Nat.choose s j : ZMod (r : ℕ))) =
          ∑ j ∈ Finset.range ((r : ℕ) ^ exponent r),
            (if j < (r : ℕ) ^ exponent r then
              (if j = 0 then 1 else 0) - (-1 : ZMod (r : ℕ)) ^ j
            else 0) * (Nat.choose s j : ZMod (r : ℕ)) := by
        symm
        apply Finset.sum_subset hsubset
        intro j hj hnot
        have hjge : ¬j < (r : ℕ) ^ exponent r := by
          simpa only [Finset.mem_range] using hnot
        simp [hjge]
      _ = ∑ j ∈ Finset.range ((r : ℕ) ^ exponent r),
            ((if j = 0 then 1 else 0) - (-1 : ZMod (r : ℕ)) ^ j) *
              (Nat.choose s j : ZMod (r : ℕ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [Finset.mem_range.mp hj]
      _ = 1 - ∑ j ∈ Finset.range ((r : ℕ) ^ exponent r),
            (-1 : ZMod (r : ℕ)) ^ j *
              (Nat.choose s j : ZMod (r : ℕ)) := by
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib]
        simp [hpowpos]
      _ = 1 - ((-1 : ZMod (r : ℕ)) ^
            ((r : ℕ) ^ exponent r - 1) *
          (Nat.choose (s - 1) ((r : ℕ) ^ exponent r - 1) :
            ZMod (r : ℕ))) := by
        have halt := alternating_choose (r : ℕ) s
          ((r : ℕ) ^ exponent r - 1) hs
        rw [Nat.sub_add_cancel hpowpos] at halt
        rw [halt]
      _ = if (r : ℕ) ^ exponent r ∣ s then 0 else 1 := by
        rw [neg_one_pow_prime_power_sub_one (r : ℕ) (exponent r)
          (Nat.prime_of_mem_primeFactors r.property)]
        rw [one_mul, choose_indicator (r : ℕ) (exponent r) s
          (Nat.prime_of_mem_primeFactors r.property) hs]
        split_ifs <;> ring
  have product_prime_powers_dvd (s : ℕ)
      (hdiv : ∀ q : ↥D.primeFactors, (q : ℕ) ^ exponent q ∣ s) :
      (∏ q : ↥D.primeFactors, (q : ℕ) ^ exponent q) ∣ s := by
    have aux (S : Finset ↥D.primeFactors)
        (hSdiv : ∀ q ∈ S, (q : ℕ) ^ exponent q ∣ s) :
        (∏ q ∈ S, (q : ℕ) ^ exponent q) ∣ s := by
      induction S using Finset.induction_on with
      | empty =>
          simp
      | @insert q S hqS ih =>
          rw [Finset.prod_insert hqS]
          have hcop :
              ((q : ℕ) ^ exponent q).Coprime
                (∏ r ∈ S, (r : ℕ) ^ exponent r) := by
            apply Nat.Coprime.prod_right
            intro r hr
            have hqr : (q : ℕ) ≠ (r : ℕ) := by
              intro h
              have hqr' : q = r := Subtype.ext h
              subst r
              exact hqS hr
            exact ((Nat.coprime_primes
              (Nat.prime_of_mem_primeFactors q.property)
              (Nat.prime_of_mem_primeFactors r.property)).mpr hqr).pow _ _
          exact hcop.mul_dvd_of_dvd_of_dvd
            (hSdiv q (by simp)) (ih (fun r hr => hSdiv r (by simp [hr])))
    simpa using aux Finset.univ (fun q _ => hdiv q)
  refine ⟨degree, ?_, ?_⟩
  · refine ⟨{
      coefficient := coefficient
      valueAtZero := ?_
      separates := ?_
    }⟩
    · change value 0 = 0
      change (∑ j : Fin (degree + 1),
        coefficient j * (Nat.choose 0 (j : ℕ) : ZMod D)) = 0
      rw [Fin.sum_univ_succ]
      simp [coefficient, componentCoefficient]
    · intro s hs hslen
      change value s ∈ canonical_set D ∧ value s ≠ 0
      constructor
      · change value s ^ 2 = value s
        apply zmod_ext
        intro p hp
        let r : ↥D.primeFactors := ⟨p, hp⟩
        have hv := value_cast r s hs
        simp only [map_pow]
        rw [hv]
        split_ifs <;> simp
      · intro hzero
        have hdiv : ∀ q : ↥D.primeFactors,
            (q : ℕ) ^ exponent q ∣ s := by
          intro q
          by_contra hnot
          have hv := value_cast q s hs
          rw [hzero, map_zero, if_neg hnot] at hv
          letI : Fact (q : ℕ).Prime :=
            ⟨Nat.prime_of_mem_primeFactors q.property⟩
          exact zero_ne_one hv
        have hbig_dvd :
            (∏ q : ↥D.primeFactors, (q : ℕ) ^ exponent q) ∣ s :=
          product_prime_powers_dvd s hdiv
        have hbig_le : (∏ q : ↥D.primeFactors,
            (q : ℕ) ^ exponent q) ≤ s :=
          Nat.le_of_dvd hs hbig_dvd
        omega
  · change (D * M) ^ R ≤ (2 * D) ^ R * (length + 1)
    rw [Nat.mul_pow, Nat.mul_pow]
    calc
      D ^ R * M ^ R ≤ D ^ R * (2 ^ R * (length + 1)) :=
        Nat.mul_le_mul_left _ hMbound
      _ = 2 ^ R * D ^ R * (length + 1) := by ring

@[blueprint "lem:bbr-coefficient-selection"
  (statement := /-- Let \(D>0\), and suppose that a BBR separating
  polynomial of length \(\ell\) and binomial degree at most \(d\) modulo
  \(D\) is given.  Then there is a canonical modular intersection family
  indexed by all \(\lfloor\ell/2\rfloor\)-element subsets of an
  \(\ell\)-element set.  Its ground-set size \(k\) satisfies
  \[
    k\leq D(d+1)(\ell+1)^d.
  \] -/)
  (proof := /-- Put \(w=\lfloor\ell/2\rfloor\), and write the polynomial
  from \cref{def:bbr-separating-polynomial} as
  \(P(s)=\sum_{j\leq d}a_j\binom{s}{j}\).  The polynomial
  \(z\mapsto P(w-z)\), restricted to \(0\leq z\leq w\), has a unique
  Newton expansion
  \[
    P(w-z)=\sum_{j\leq d}b_j\binom{z}{j}
      \quad\text{in }\mathbb Z/D\mathbb Z;
  \]
  translation does not increase its binomial degree.

  Choose the representative \(\bar b_j\in\{0,\ldots,D-1\}\) of each
  \(b_j\).  Form a ground set having \(\bar b_j\) labelled copies of every
  \(j\)-element subset of \(\operatorname{Fin}(\ell)\).  For every
  \(w\)-element subset \(X\), let \(A_X\) contain precisely the copies
  labelled by subsets of \(X\).  Since there are
  \(\binom{\ell}{j}\) labels of size \(j\), the ground-set cardinality is
  at most
  \[
    D\sum_{j\leq d}\binom{\ell}{j}
      \leq D(d+1)(\ell+1)^d.
  \]

  If \(X\) and \(Y\) have size \(w\), the copies common to \(A_X\) and
  \(A_Y\) are exactly those whose labels lie in \(X\cap Y\).  Hence
  \[
    |A_X\cap A_Y|
      \equiv\sum_{j\leq d}b_j
        \binom{|X\cap Y|}{j}
      =P\bigl(w-|X\cap Y|\bigr)\pmod D.
  \]
  For \(X=Y\), this is \(P(0)=0\).  For \(X\ne Y\), equal cardinalities
  imply \(1\leq w-|X\cap Y|\leq\ell\), so the last residue is a nonzero
  idempotent by the separation property.  Enumerating the \(w\)-element
  subsets, whose number is \(\binom{\ell}{w}\), gives the asserted
  canonical modular intersection family. -/)
  (title := /-- Coefficient selection for restricted intersections -/)
  (latexEnv := "lemma")]
lemma bbr_coefficient_selection
    {D length degree : ℕ} (hDpos : 0 < D)
    (P : bbr_separating_polynomial D length degree) :
    ∃ k : ℕ,
      k ≤ D * (degree + 1) * (length + 1) ^ degree ∧
      Nonempty
        (canonical_modular_intersection_family
          D k (Nat.choose length (length / 2))) := by
  classical
  letI : NeZero D := ⟨Nat.ne_of_gt hDpos⟩
  let w := length / 2
  let a : ℕ → ZMod D := fun i =>
    if hi : i < degree + 1 then P.coefficient ⟨i, hi⟩ else 0
  let S : ℕ → ℕ → ℕ → ZMod D := fun w' i r =>
    ∑ j ∈ Finset.range (i + 1), ((-1 : ZMod D) ^ j) *
      (Nat.choose (w' - j) (i - j) : ZMod D) *
      (Nat.choose r j : ZMod D)
  let b : ℕ → ZMod D := fun j =>
    (-1 : ZMod D) ^ j *
      ∑ i ∈ Finset.range (degree + 1),
        if j ≤ i then
          a i * (Nat.choose (w - j) (i - j) : ZMod D)
        else 0
  have hbase (w' i : ℕ) : S w' i 0 = (Nat.choose w' i : ZMod D) := by
    simp only [S]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro q hq hq0
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
      simp
    · simp
  have hsplit (w' i r : ℕ) :
      S w' (i + 1) (r + 1) = S w' (i + 1) r - S (w' - 1) i r := by
    simp only [S]
    conv_lhs => rw [Finset.sum_range_succ']
    conv_rhs => lhs; rw [Finset.sum_range_succ']
    simp only [Nat.choose_succ_succ]
    simp_rw [Nat.cast_add, mul_add]
    rw [Finset.sum_add_distrib]
    have hterm : ∀ j ∈ Finset.range (i + 1),
        (-1 : ZMod D) ^ (j + 1) *
            (Nat.choose (w' - (j + 1)) (i + 1 - (j + 1)) : ZMod D) *
            (Nat.choose r j : ZMod D) =
          -((-1 : ZMod D) ^ j *
            (Nat.choose (w' - 1 - j) (i - j) : ZMod D) *
            (Nat.choose r j : ZMod D)) := by
      intro j hj
      rw [show w' - (j + 1) = w' - 1 - j by omega]
      rw [show i + 1 - (j + 1) = i - j by omega]
      rw [pow_succ]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.add_comm]
    ring
  have hreflect : ∀ w' i r : ℕ, r ≤ w' →
      S w' i r = (Nat.choose (w' - r) i : ZMod D) := by
    intro w' i r hr
    induction r generalizing w' i with
    | zero => exact hbase w' i
    | succ r ih =>
        cases i with
        | zero => simp [S]
        | succ i =>
            rw [hsplit, ih w' (i + 1) (by omega), ih (w' - 1) i (by omega)]
            rw [show w' - r = (w' - r - 1) + 1 by omega]
            rw [Nat.choose_succ_succ]
            rw [show w' - 1 - r = w' - r - 1 by omega]
            rw [show w' - (r + 1) = w' - r - 1 by omega]
            push_cast
            ring
  have hswap (r : ℕ) :
      (∑ j ∈ Finset.range (degree + 1),
          b j * (Nat.choose r j : ZMod D)) =
        ∑ i ∈ Finset.range (degree + 1), a i * S w i r := by
    simp only [b, S]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < degree + 1 := Finset.mem_range.mp hi
    have hfilter :
        (Finset.range (degree + 1)).filter (fun j => j ≤ i) =
          Finset.range (i + 1) := by
      ext j
      simp
      omega
    rw [← hfilter]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs with hji
    · ring
    · simp
  have hpolyRange (r : ℕ) (hr : r ≤ w) :
      (∑ j ∈ Finset.range (degree + 1),
          b j * (Nat.choose r j : ZMod D)) =
        ∑ i : Fin (degree + 1),
          P.coefficient i * (Nat.choose (w - r) (i : ℕ) : ZMod D) := by
    rw [hswap]
    calc
      _ = ∑ i ∈ Finset.range (degree + 1),
          a i * (Nat.choose (w - r) i : ZMod D) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hreflect w i r hr]
      _ = _ := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [a]
        rw [dif_pos i.isLt]
  have hpoly (r : ℕ) (hr : r ≤ w) :
      (∑ j : Fin (degree + 1),
          b j * (Nat.choose r j : ZMod D)) =
        ∑ i : Fin (degree + 1),
          P.coefficient i * (Nat.choose (w - r) (i : ℕ) : ZMod D) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun j => b j * (Nat.choose r j : ZMod D)) (degree + 1)]
    exact hpolyRange r hr
  let Ground := Σ j : Fin (degree + 1),
    Σ _ : Fin (b j).val,
      ↥((Finset.univ : Finset (Fin length)).powersetCard j)
  let subsetEmbedding (X : Finset (Fin length)) (j : Fin (degree + 1)) :
      ↥(X.powersetCard j) ↪
        ↥((Finset.univ : Finset (Fin length)).powersetCard j) :=
    { toFun := fun T => ⟨T.1, by
        rcases Finset.mem_powersetCard.mp T.property with ⟨hsub, hcard⟩
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩⟩
      inj' := by
        rintro ⟨T, hT⟩ ⟨U, hU⟩ h
        simp_all }
  let sigmaBlock (X : Finset (Fin length)) : Finset Ground :=
    Finset.univ.sigma fun j =>
      Finset.univ.sigma fun _ =>
        (X.powersetCard j).attach.map (subsetEmbedding X j)
  have hsigma_mem (X : Finset (Fin length)) (g : Ground) :
      g ∈ sigmaBlock X ↔ g.2.2.1 ⊆ X := by
    rcases g with ⟨j, c, T⟩
    simp only [sigmaBlock, Ground]
    rw [Finset.mem_sigma, Finset.mem_sigma]
    simp only [Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · rintro ⟨U, hU, hUT⟩
      have hval : U.1 = T.1 := congrArg Subtype.val hUT
      rw [← hval]
      exact (Finset.mem_powersetCard.mp U.property).1
    · intro hsub
      let U : ↥(X.powersetCard j) := ⟨T.1,
        Finset.mem_powersetCard.mpr ⟨hsub,
          (Finset.mem_powersetCard.mp T.property).2⟩⟩
      refine ⟨U, by simp [U], ?_⟩
      apply Subtype.ext
      rfl
  let rawBlock (X : Finset (Fin length)) : Finset Ground :=
    Finset.univ.filter fun g => g.2.2.1 ⊆ X
  have hraw_eq_sigma (X : Finset (Fin length)) :
      rawBlock X = sigmaBlock X := by
    ext g
    simp [rawBlock, hsigma_mem]
  have hrawcard (X : Finset (Fin length)) :
      (rawBlock X).card = ∑ j : Fin (degree + 1),
        (b j).val * Nat.choose X.card j := by
    rw [hraw_eq_sigma]
    simp [sigmaBlock, Ground]
  have hrawcard_cast (X : Finset (Fin length)) :
      ((rawBlock X).card : ZMod D) =
        ∑ j : Fin (degree + 1),
          b j * (Nat.choose X.card j : ZMod D) := by
    rw [hrawcard]
    push_cast
    simp [ZMod.natCast_zmod_val]
  have hinter (X Y : Finset (Fin length)) :
      rawBlock X ∩ rawBlock Y = rawBlock (X ∩ Y) := by
    ext g
    simp [rawBlock, Finset.subset_inter_iff]
  have hGround :
      Fintype.card Ground = ∑ j : Fin (degree + 1),
        (b j).val * Nat.choose length j := by
    simp [Ground]
  have hbound :
      Fintype.card Ground ≤
        D * (degree + 1) * (length + 1) ^ degree := by
    rw [hGround]
    calc
      _ ≤ ∑ _j : Fin (degree + 1),
          D * (length + 1) ^ degree := by
        apply Finset.sum_le_sum
        intro j hj
        apply Nat.mul_le_mul
        · exact Nat.le_of_lt (ZMod.val_lt (b j))
        · exact (Nat.choose_le_pow length j).trans
            ((Nat.pow_le_pow_left (by omega) _).trans
              (Nat.pow_le_pow_right (by omega) (Fin.le_last j)))
      _ = _ := by
        simp
        ring
  let choices := (Finset.univ : Finset (Fin length)).powersetCard w
  let choiceEquiv : Fin (Nat.choose length w) ≃ ↥choices :=
    Fintype.equivOfCardEq (by simp [choices])
  let groundEquiv := Fintype.equivFin Ground
  let blocks (i : Fin (Nat.choose length w)) :
      Finset (Fin (Fintype.card Ground)) :=
    (rawBlock (choiceEquiv i).1).map groundEquiv.toEmbedding
  refine ⟨Fintype.card Ground, hbound, ⟨{
    blocks := blocks
    diagonalCard := ?_
    offDiagonalCard := ?_
  }⟩⟩
  · intro i
    have hXi : (choiceEquiv i).1.card = w :=
      (Finset.mem_powersetCard.mp (choiceEquiv i).property).2
    simp only [blocks, Finset.card_map]
    rw [hrawcard_cast, hpoly _ (by omega)]
    simpa [w, hXi] using P.valueAtZero
  · intro i j hij
    let X := (choiceEquiv i).1
    let Y := (choiceEquiv j).1
    have hXcard : X.card = w :=
      (Finset.mem_powersetCard.mp (choiceEquiv i).property).2
    have hYcard : Y.card = w :=
      (Finset.mem_powersetCard.mp (choiceEquiv j).property).2
    have hXY : X ≠ Y := by
      intro h
      apply hij
      exact choiceEquiv.injective (Subtype.ext h)
    have hinterlt : (X ∩ Y).card < w := by
      have hle : (X ∩ Y).card ≤ X.card :=
        Finset.card_le_card Finset.inter_subset_left
      rw [hXcard] at hle
      apply lt_of_le_of_ne hle
      intro heq
      have hIX : X ∩ Y = X := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_left (by omega)
      have hsub : X ⊆ Y := Finset.inter_eq_left.mp hIX
      have : X = Y := Finset.eq_of_subset_of_card_le hsub (by omega)
      exact hXY this
    have hspos : 0 < w - (X ∩ Y).card := by omega
    have hslen : w - (X ∩ Y).card ≤ length := by
      dsimp [w]
      omega
    have hsep := P.separates (w - (X ∩ Y).card) hspos hslen
    change
      (((rawBlock X).map groundEquiv.toEmbedding ∩
        (rawBlock Y).map groundEquiv.toEmbedding).card : ZMod D) ∈
          canonical_set D ∧
      (((rawBlock X).map groundEquiv.toEmbedding ∩
        (rawBlock Y).map groundEquiv.toEmbedding).card : ZMod D) ≠ 0
    rw [← Finset.map_inter, Finset.card_map, hinter, hrawcard_cast,
      hpoly (X ∩ Y).card (by omega)]
    simpa [X, Y, w] using hsep

@[blueprint "lem:bbr-word-coefficient-selection"
  (statement := /-- Let \(D>0\), and let a BBR separating polynomial of
  length \(\ell\) and binomial degree at most \(d\) modulo \(D\) be
  given.  There is a canonical modular intersection family indexed by all
  words of length \(\ell\) over an alphabet of size \(\ell+1\).  Its
  ground-set size \(k\) satisfies
  \[
    k\leq D(d+1)(\ell+1)^{2d}.
  \] -/)
  (proof := /-- When \(\ell=0\), the one-member family supplied by
  \cref{lem:bbr-coefficient-selection} has exactly the required size and
  bound.  For positive \(\ell\), rewrite the separating polynomial from
  \cref{def:bbr-separating-polynomial} in the binomial basis evaluated at
  the number of coordinates on which two words agree.  For every coefficient
  of index \(j\), use all \(j\)-element subsets of the set of
  coordinate--symbol pairs, repeated according to a natural representative
  of the coefficient modulo \(D\).  The block associated with a word
  retains precisely the graph subsets obtained by restricting that word.
  Thus the residue of the intersection of two blocks is the separating
  polynomial evaluated at their Hamming distance.  The diagonal residue is
  zero, and distinct words have a positive Hamming distance at most \(\ell\), so
  \cref{def:canonical-modular-intersection-family} supplies the required
  off-diagonal condition.  Counting coordinate sets and assignments gives
  the displayed ground-set bound. -/)
  (title := /-- Coefficient selection for word-indexed intersections -/)
  (latexEnv := "lemma")]
lemma bbr_word_coefficient_selection
    {D length degree : ℕ} (hDpos : 0 < D)
    (P : bbr_separating_polynomial D length degree) :
    ∃ k : ℕ,
      k ≤ D * (degree + 1) * (length + 1) ^ (2 * degree) ∧
      Nonempty
        (canonical_modular_intersection_family
          D k ((length + 1) ^ length)) := by
  classical
  by_cases hlength : length = 0
  · subst length
    rcases bbr_coefficient_selection hDpos P with ⟨k, hk, hfamily⟩
    refine ⟨k, ?_, ?_⟩
    · simpa using hk
    · simpa using hfamily
  letI : NeZero D := ⟨Nat.ne_of_gt hDpos⟩
  let a : ℕ → ZMod D := fun i =>
    if hi : i < degree + 1 then P.coefficient ⟨i, hi⟩ else 0
  let S : ℕ → ℕ → ℕ → ZMod D := fun w i r =>
    ∑ j ∈ Finset.range (i + 1), ((-1 : ZMod D) ^ j) *
      (Nat.choose (w - j) (i - j) : ZMod D) *
      (Nat.choose r j : ZMod D)
  let b : ℕ → ZMod D := fun j =>
    (-1 : ZMod D) ^ j *
      ∑ i ∈ Finset.range (degree + 1),
        if j ≤ i then
          a i * (Nat.choose (length - j) (i - j) : ZMod D)
        else 0
  have hbase (w i : ℕ) : S w i 0 = (Nat.choose w i : ZMod D) := by
    simp only [S]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro q hq hq0
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
      simp
    · simp
  have hsplit (w i r : ℕ) :
      S w (i + 1) (r + 1) = S w (i + 1) r - S (w - 1) i r := by
    simp only [S]
    conv_lhs => rw [Finset.sum_range_succ']
    conv_rhs => lhs; rw [Finset.sum_range_succ']
    simp only [Nat.choose_succ_succ]
    simp_rw [Nat.cast_add, mul_add]
    rw [Finset.sum_add_distrib]
    have hterm : ∀ j ∈ Finset.range (i + 1),
        (-1 : ZMod D) ^ (j + 1) *
            (Nat.choose (w - (j + 1)) (i + 1 - (j + 1)) : ZMod D) *
            (Nat.choose r j : ZMod D) =
          -((-1 : ZMod D) ^ j *
            (Nat.choose (w - 1 - j) (i - j) : ZMod D) *
            (Nat.choose r j : ZMod D)) := by
      intro j hj
      rw [show w - (j + 1) = w - 1 - j by omega]
      rw [show i + 1 - (j + 1) = i - j by omega]
      rw [pow_succ]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.add_comm]
    ring
  have hreflect : ∀ w i r : ℕ, r ≤ w →
      S w i r = (Nat.choose (w - r) i : ZMod D) := by
    intro w i r hr
    induction r generalizing w i with
    | zero => exact hbase w i
    | succ r ih =>
        cases i with
        | zero => simp [S]
        | succ i =>
            rw [hsplit, ih w (i + 1) (by omega), ih (w - 1) i (by omega)]
            rw [show w - r = (w - r - 1) + 1 by omega]
            rw [Nat.choose_succ_succ]
            rw [show w - 1 - r = w - r - 1 by omega]
            rw [show w - (r + 1) = w - r - 1 by omega]
            push_cast
            ring
  have hswap (r : ℕ) :
      (∑ j ∈ Finset.range (degree + 1),
          b j * (Nat.choose r j : ZMod D)) =
        ∑ i ∈ Finset.range (degree + 1), a i * S length i r := by
    simp only [b, S]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < degree + 1 := Finset.mem_range.mp hi
    have hfilter :
        (Finset.range (degree + 1)).filter (fun j => j ≤ i) =
          Finset.range (i + 1) := by
      ext j
      simp
      omega
    rw [← hfilter]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs with hji
    · ring
    · simp
  have hpolyRange (r : ℕ) (hr : r ≤ length) :
      (∑ j ∈ Finset.range (degree + 1),
          b j * (Nat.choose r j : ZMod D)) =
        ∑ i : Fin (degree + 1),
          P.coefficient i * (Nat.choose (length - r) (i : ℕ) : ZMod D) := by
    rw [hswap]
    calc
      _ = ∑ i ∈ Finset.range (degree + 1),
          a i * (Nat.choose (length - r) i : ZMod D) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hreflect length i r hr]
      _ = _ := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [a]
        rw [dif_pos i.isLt]
  have hpoly (r : ℕ) (hr : r ≤ length) :
      (∑ j : Fin (degree + 1),
          b j * (Nat.choose r j : ZMod D)) =
        ∑ i : Fin (degree + 1),
          P.coefficient i * (Nat.choose (length - r) (i : ℕ) : ZMod D) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun j => b j * (Nat.choose r j : ZMod D)) (degree + 1)]
    exact hpolyRange r hr
  let Symbols := Fin length × Fin (length + 1)
  let CoordinateSets (j : Fin (degree + 1)) :=
    ↥((Finset.univ : Finset Symbols).powersetCard j)
  let Ground := Σ j : Fin (degree + 1),
    Σ _ : Fin (b j).val, CoordinateSets j
  let graphEmbedding (x : Fin length → Fin (length + 1)) :
      Fin length ↪ Symbols :=
    { toFun := fun u => (u, x u)
      inj' := fun u v h => congrArg Prod.fst h }
  let wordEmbedding (x : Fin length → Fin (length + 1))
      (X : Finset (Fin length)) (j : Fin (degree + 1)) :
      ↥(X.powersetCard j) ↪ CoordinateSets j :=
    { toFun := fun T =>
        ⟨T.1.map (graphEmbedding x), Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ _, by
            rw [Finset.card_map]
            exact (Finset.mem_powersetCard.mp T.property).2⟩⟩
      inj' := by
        intro T U h
        apply Subtype.ext
        apply Finset.map_injective
        exact congrArg Subtype.val h }
  let sigmaBlock (X : Finset (Fin length))
      (x : Fin length → Fin (length + 1)) : Finset Ground :=
    Finset.univ.sigma fun j =>
      Finset.univ.sigma fun _ =>
        (X.powersetCard j).attach.map (wordEmbedding x X j)
  have hsigma_mem (X : Finset (Fin length))
      (x : Fin length → Fin (length + 1)) (g : Ground) :
      g ∈ sigmaBlock X x ↔
        ∃ T : ↥(X.powersetCard g.1),
          T.1.map (graphEmbedding x) = g.2.2.1 := by
    rcases g with ⟨j, c, V⟩
    simp only [sigmaBlock, Ground]
    rw [Finset.mem_sigma, Finset.mem_sigma]
    simp only [Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · rintro ⟨T, hT, h⟩
      exact ⟨T, congrArg Subtype.val h⟩
    · rintro ⟨T, h⟩
      exact ⟨T, by simp, Subtype.ext h⟩
  have graph_map_eq_iff (x y : Fin length → Fin (length + 1))
      (T U : Finset (Fin length)) :
      T.map (graphEmbedding x) = U.map (graphEmbedding y) ↔
        T = U ∧ ∀ u ∈ T, x u = y u := by
    constructor
    · intro h
      have hTU : T = U := by
        ext u
        constructor
        · intro hu
          have hm : (u, x u) ∈ U.map (graphEmbedding y) := by
            rw [← h]
            exact Finset.mem_map.mpr ⟨u, hu, rfl⟩
          rcases Finset.mem_map.mp hm with ⟨v, hv, heq⟩
          have hvu : v = u := congrArg Prod.fst heq
          simpa [hvu] using hv
        · intro hu
          have hm : (u, y u) ∈ T.map (graphEmbedding x) := by
            rw [h]
            exact Finset.mem_map.mpr ⟨u, hu, rfl⟩
          rcases Finset.mem_map.mp hm with ⟨v, hv, heq⟩
          have hvu : v = u := congrArg Prod.fst heq
          simpa [hvu] using hv
      refine ⟨hTU, ?_⟩
      intro u hu
      have hm : (u, x u) ∈ U.map (graphEmbedding y) := by
        rw [← h]
        exact Finset.mem_map.mpr ⟨u, hu, rfl⟩
      rcases Finset.mem_map.mp hm with ⟨v, hv, heq⟩
      have hvu : v = u := congrArg Prod.fst heq
      subst v
      exact (congrArg Prod.snd heq).symm
    · rintro ⟨rfl, hxy⟩
      ext z
      rcases z with ⟨u, s⟩
      simp only [Finset.mem_map]
      constructor
      · rintro ⟨v, hv, heq⟩
        refine ⟨v, hv, ?_⟩
        have hvu : v = u := congrArg Prod.fst heq
        subst v
        change (u, y u) = (u, s)
        rw [← hxy u hv]
        exact heq
      · rintro ⟨v, hv, heq⟩
        refine ⟨v, hv, ?_⟩
        have hvu : v = u := congrArg Prod.fst heq
        subst v
        change (u, x u) = (u, s)
        rw [hxy u hv]
        exact heq
  let agreement (x y : Fin length → Fin (length + 1)) :
      Finset (Fin length) :=
    Finset.univ.filter fun u => x u = y u
  have hinter (x y : Fin length → Fin (length + 1)) :
      sigmaBlock Finset.univ x ∩ sigmaBlock Finset.univ y =
        sigmaBlock (agreement x y) x := by
    ext g
    rw [Finset.mem_inter, hsigma_mem, hsigma_mem, hsigma_mem]
    constructor
    · rintro ⟨⟨T, hT⟩, ⟨U, hU⟩⟩
      have hmaps :
          T.1.map (graphEmbedding x) = U.1.map (graphEmbedding y) :=
        hT.trans hU.symm
      rcases (graph_map_eq_iff x y T.1 U.1).mp hmaps with ⟨hTU, hxy⟩
      let V : ↥((agreement x y).powersetCard g.1) :=
        ⟨T.1, Finset.mem_powersetCard.mpr
          ⟨by
            intro u hu
            simp [agreement, hxy u hu],
            (Finset.mem_powersetCard.mp T.property).2⟩⟩
      exact ⟨V, hT⟩
    · rintro ⟨T, hT⟩
      let U : ↥((Finset.univ : Finset (Fin length)).powersetCard g.1) :=
        ⟨T.1, Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp T.property).2⟩⟩
      have hxy : ∀ u ∈ T.1, x u = y u := by
        intro u hu
        have := (Finset.mem_powersetCard.mp T.property).1 hu
        simpa [agreement] using this
      refine ⟨⟨U, hT⟩, ⟨U, ?_⟩⟩
      exact ((graph_map_eq_iff x y U.1 U.1).mpr ⟨rfl, hxy⟩).symm.trans hT
  have hsigma_card (X : Finset (Fin length))
      (x : Fin length → Fin (length + 1)) :
      (sigmaBlock X x).card =
        ∑ j : Fin (degree + 1), (b j).val * Nat.choose X.card j := by
    simp [sigmaBlock, Ground]
  have hinter_card_cast (x y : Fin length → Fin (length + 1)) :
      (((sigmaBlock Finset.univ x ∩ sigmaBlock Finset.univ y).card : ℕ) :
          ZMod D) =
        ∑ j : Fin (degree + 1),
          b j * (Nat.choose (agreement x y).card j : ZMod D) := by
    rw [hinter, hsigma_card]
    push_cast
    simp [ZMod.natCast_zmod_val]
  have hGround :
      Fintype.card Ground =
        ∑ j : Fin (degree + 1),
          (b j).val * Nat.choose (length * (length + 1)) j := by
    simp [Ground, CoordinateSets, Symbols]
  have hbound :
      Fintype.card Ground ≤
        D * (degree + 1) * (length + 1) ^ (2 * degree) := by
    rw [hGround]
    calc
      _ ≤ ∑ _j : Fin (degree + 1),
          D * ((length + 1) ^ degree * (length + 1) ^ degree) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Nat.mul_le_mul
        · exact Nat.le_of_lt (ZMod.val_lt (b j))
        · calc
            Nat.choose (length * (length + 1)) j ≤
                (length * (length + 1)) ^ (j : ℕ) :=
              Nat.choose_le_pow _ _
            _ ≤ ((length + 1) ^ 2) ^ (j : ℕ) := by
              gcongr
              nlinarith
            _ ≤ ((length + 1) ^ 2) ^ degree := by
              exact Nat.pow_le_pow_right (by positivity) (by omega)
            _ = (length + 1) ^ degree * (length + 1) ^ degree := by
              calc
                ((length + 1) ^ 2) ^ degree =
                    (length + 1) ^ (2 * degree) :=
                  (pow_mul (length + 1) 2 degree).symm
                _ = (length + 1) ^ (degree + degree) := by
                  congr 2
                  omega
                _ = _ := pow_add _ _ _
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        have hpow :
            D * ((length + 1) ^ degree * (length + 1) ^ degree) =
              D * (length + 1) ^ (2 * degree) := by
          rw [show 2 * degree = degree + degree by omega, pow_add]
        rw [hpow]
        ac_rfl
  let Word := Fin length → Fin (length + 1)
  let wordEquiv : Fin ((length + 1) ^ length) ≃ Word :=
    Fintype.equivOfCardEq (by simp [Word])
  let groundEquiv := Fintype.equivFin Ground
  let blocks (i : Fin ((length + 1) ^ length)) :
      Finset (Fin (Fintype.card Ground)) :=
    (sigmaBlock Finset.univ (wordEquiv i)).map groundEquiv.toEmbedding
  refine ⟨Fintype.card Ground, hbound, ⟨{
    blocks := blocks
    diagonalCard := ?_
    offDiagonalCard := ?_
  }⟩⟩
  · intro i
    simp only [blocks, Finset.card_map]
    rw [← Finset.inter_self (sigmaBlock Finset.univ (wordEquiv i))]
    rw [hinter_card_cast]
    have hagree :
        (agreement (wordEquiv i) (wordEquiv i)).card = length := by
      simp [agreement]
    rw [hagree, hpoly length (le_refl length)]
    simpa using P.valueAtZero
  · intro i j hij
    let x := wordEquiv i
    let y := wordEquiv j
    have hxy : x ≠ y := by
      intro h
      exact hij (wordEquiv.injective h)
    have hagree_lt : (agreement x y).card < length := by
      calc
        (agreement x y).card <
            (Finset.univ : Finset (Fin length)).card := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨Finset.subset_univ _, ?_⟩
          intro heq
          apply hxy
          funext u
          have hu : u ∈ agreement x y := by rw [heq]; simp
          simpa [agreement] using hu
        _ = length := by simp
    have hspos : 0 < length - (agreement x y).card := by omega
    have hslen : length - (agreement x y).card ≤ length := by omega
    have hsep := P.separates
      (length - (agreement x y).card) hspos hslen
    change
      ((((sigmaBlock Finset.univ x).map groundEquiv.toEmbedding ∩
        (sigmaBlock Finset.univ y).map groundEquiv.toEmbedding).card : ℕ) :
          ZMod D) ∈ canonical_set D ∧
      ((((sigmaBlock Finset.univ x).map groundEquiv.toEmbedding ∩
        (sigmaBlock Finset.univ y).map groundEquiv.toEmbedding).card : ℕ) :
          ZMod D) ≠ 0
    rw [← Finset.map_inter, Finset.card_map, hinter_card_cast,
      hpoly (agreement x y).card (by
        simpa using Finset.card_le_univ (agreement x y))]
    simpa [x, y] using hsep

@[blueprint "lem:bbr-asymptotic-parameter-selection"
  (statement := /-- Let \(D,C>0\) and \(R\geq2\) be natural numbers.
  There is a real constant \(c>0\) such that, for every sufficiently large
  natural number \(k\), one can choose a length \(\ell\) with the following
  two properties.  Every natural number \(d\) satisfying
  \(d^R\leq C(\ell+1)\) also satisfies
  \[
    D(d+1)(\ell+1)^{2d}\leq k,
  \]
  and
  \[
    \exp\!\left(c\frac{(\log k)^R}
      {(\log\log k)^{R-1}}\right)
      \leq (\ell+1)^\ell .
  \] -/)
  (proof := /-- Put \(A=C+1\), choose a fixed sufficiently large constant
  \(K\) in terms of \(A\) and \(R\), and set
  \(\alpha=(4K)^{-1}\).  For a large \(k\), let
  \[
    q=\left\lceil\alpha\frac{\log k}{\log\log k}\right\rceil
    \quad\text{and}\quad \ell=q^R.
  \]
  The estimate \(d^R\leq C(q^R+1)\) implies
  \(d\leq A(q+1)\).  Consequently the proposed ground-set bound is at most
  \((q+1)^{4+2RA(q+1)}\), whose logarithm is at most \(\log k\) by the
  choice of \(\alpha\).  On the other hand, the logarithm of
  \((\ell+1)^\ell\) is at least \(q^R\log q\).  Standard eventual
  estimates \(\log q\geq\frac12\log\log k\) and
  \(q\geq\alpha\log k/\log\log k\) give the asserted lower bound after
  taking \(c=\alpha^R/4\). -/)
  (title := /-- Asymptotic parameter selection for the BBR construction -/)
  (latexEnv := "lemma")]
lemma bbr_asymptotic_parameter_selection
    {D C R : ℕ} (hDpos : 0 < D) (hCpos : 0 < C) (hRtwo : 2 ≤ R) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k : ℕ in atTop,
        ∃ length : ℕ,
          (∀ degree : ℕ,
            degree ^ R ≤ C * (length + 1) →
              D * (degree + 1) * (length + 1) ^ (2 * degree) ≤ k) ∧
          Real.exp
              (c * (Real.log (k : ℝ)) ^ R /
                (Real.log (Real.log (k : ℝ))) ^ (R - 1)) ≤
            (((length + 1) ^ length : ℕ) : ℝ) := by
  classical
  let A : ℕ := C + 1
  let K : ℕ := 4 + 2 * R * A
  let α : ℝ := 1 / (4 * (K : ℝ))
  let L : ℕ → ℝ := fun k => Real.log (k : ℝ)
  let LL : ℕ → ℝ := fun k => Real.log (L k)
  let x : ℕ → ℝ := fun k => α * L k / LL k
  let q : ℕ → ℕ := fun k => ⌈x k⌉₊
  have hKpos : 0 < K := by simp [K]
  have hαpos : 0 < α := by
    dsimp [α]
    positivity
  have hlog : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto LL atTop atTop := by
    exact Real.tendsto_log_atTop.comp hlog
  have hratioSmall :
      ∀ᶠ k : ℕ in atTop,
        ‖LL k‖ ≤ (α / ((D + C + 2 : ℕ) : ℝ)) * ‖L k‖ := by
    exact (Real.isLittleO_log_id_atTop.comp_tendsto hlog).bound (by positivity)
  have hthirdLogSmall :
      ∀ᶠ k : ℕ in atTop, ‖Real.log (LL k)‖ ≤ (1 / 4 : ℝ) * ‖LL k‖ := by
    exact (Real.isLittleO_log_id_atTop.comp_tendsto hloglog).bound (by norm_num)
  refine ⟨α ^ R / 4, by positivity, ?_⟩
  filter_upwards [
      hlog.eventually_ge_atTop 1,
      hloglog.eventually_ge_atTop
        (max 1 (max (2 * α) (-4 * Real.log α))),
      hratioSmall,
      hthirdLogSmall] with k hkL hkLL hsmall hthird
  let length := (q k) ^ R
  have hLpos : 0 < L k := lt_of_lt_of_le zero_lt_one hkL
  have hLLone : 1 ≤ LL k := le_trans (le_max_left _ _) hkLL
  have hLLpos : 0 < LL k := zero_lt_one.trans_le hLLone
  have hsmall' :
      LL k ≤ (α / ((D + C + 2 : ℕ) : ℝ)) * L k := by
    simpa [Real.norm_eq_abs, abs_of_pos hLLpos, abs_of_pos hLpos] using hsmall
  have hxlarge : ((D + C + 2 : ℕ) : ℝ) ≤ x k := by
    have hMpos : (0 : ℝ) < ((D + C + 2 : ℕ) : ℝ) := by positivity
    have hmul :
        ((D + C + 2 : ℕ) : ℝ) * LL k ≤ α * L k := by
      calc
        ((D + C + 2 : ℕ) : ℝ) * LL k ≤
            ((D + C + 2 : ℕ) : ℝ) *
              ((α / ((D + C + 2 : ℕ) : ℝ)) * L k) :=
          mul_le_mul_of_nonneg_left hsmall' hMpos.le
        _ = α * L k := by field_simp
    dsimp [x]
    exact (le_div_iff₀ hLLpos).2 (by nlinarith)
  have hxpos : 0 < x k := lt_of_lt_of_le (by positivity) hxlarge
  have hx_le_q : x k ≤ (q k : ℝ) := by
    exact Nat.le_ceil (x k)
  have hq_lt : (q k : ℝ) < x k + 1 := by
    exact Nat.ceil_lt_add_one hxpos.le
  have hqlarge : D + C + 2 ≤ q k := by
    exact_mod_cast hxlarge.trans hx_le_q
  have hB_bound : ((q k + 1 : ℕ) : ℝ) ≤ 2 * x k := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    have htwoM : (2 : ℝ) ≤ ((D + C + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 ≤ D + C + 2 by omega)
    have hxtwo : (2 : ℝ) ≤ x k := htwoM.trans hxlarge
    linarith
  have htwoα_le_LL : 2 * α ≤ LL k :=
    le_trans (le_max_left (2 * α) (-4 * Real.log α))
      (le_trans (le_max_right 1 _) hkLL)
  have hB_le_L : ((q k + 1 : ℕ) : ℝ) ≤ L k := by
    refine hB_bound.trans ?_
    dsimp [x]
    rw [show 2 * (α * L k / LL k) = (2 * α * L k) / LL k by ring]
    rw [div_le_iff₀ hLLpos]
    nlinarith
  have hqpos : 0 < q k := by omega
  have hBlog : Real.log ((q k + 1 : ℕ) : ℝ) ≤ LL k := by
    calc
      Real.log ((q k + 1 : ℕ) : ℝ) ≤ Real.log (L k) :=
        Real.log_le_log (by positivity) hB_le_L
      _ = LL k := rfl
  have hlogLL :
      Real.log (LL k) ≤ (1 / 4 : ℝ) * LL k := by
    have hlogLLnonneg : 0 ≤ Real.log (LL k) := Real.log_nonneg hLLone
    simpa [Real.norm_eq_abs, abs_of_nonneg hlogLLnonneg,
      abs_of_pos hLLpos] using hthird
  have hlogα : -LL k / 4 ≤ Real.log α := by
    have hbound :
        -4 * Real.log α ≤ LL k :=
      le_trans (le_max_right (2 * α) (-4 * Real.log α))
        (le_trans (le_max_right 1 _) hkLL)
    linarith
  have hlogq : LL k / 2 ≤ Real.log (q k : ℝ) := by
    have hlogx : LL k / 2 ≤ Real.log (x k) := by
      dsimp [x]
      rw [Real.log_div (mul_ne_zero hαpos.ne' hLpos.ne') hLLpos.ne',
        Real.log_mul hαpos.ne' hLpos.ne']
      dsimp [LL, L] at hlogLL ⊢
      nlinarith
    exact hlogx.trans (Real.log_le_log hxpos hx_le_q)
  have hqpowadd : (q k) ^ R + 1 ≤ (q k + 1) ^ R := by
    have hlt := Nat.pow_lt_pow_left (Nat.lt_succ_self (q k))
      (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hRtwo))
    exact hlt
  have hCR : C ≤ (C + 1) ^ R := by
    exact (Nat.le_succ C).trans (Nat.le_pow (by omega))
  refine ⟨length, ?_, ?_⟩
  · intro degree hdegreePow
    have hdegree : degree ≤ A * (q k + 1) := by
      apply (Nat.pow_le_pow_iff_left
        (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hRtwo))).mp
      exact
        calc
          degree ^ R ≤ C * (length + 1) := hdegreePow
          _ ≤ (C + 1) ^ R * (q k + 1) ^ R := by
            dsimp [length]
            exact Nat.mul_le_mul hCR hqpowadd
          _ = (A * (q k + 1)) ^ R := by
            dsimp [A]
            rw [Nat.mul_pow]
    have hDle : D ≤ q k + 1 := by omega
    have hAle : A ≤ q k + 1 := by
      dsimp [A]
      omega
    have hdegreeSquare : degree ≤ (q k + 1) ^ 2 := by
      exact hdegree.trans (by
        calc
          A * (q k + 1) ≤ (q k + 1) * (q k + 1) :=
            Nat.mul_le_mul_right _ hAle
          _ = (q k + 1) ^ 2 := by ring)
    have hdegreeCube : degree + 1 ≤ (q k + 1) ^ 3 := by
      calc
        degree + 1 ≤ (q k + 1) ^ 2 + 1 := Nat.add_le_add_right hdegreeSquare 1
        _ ≤ (q k + 1) ^ 2 + (q k + 1) ^ 2 := by
          gcongr
          exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
        _ = 2 * (q k + 1) ^ 2 := by omega
        _ ≤ (q k + 1) * (q k + 1) ^ 2 :=
          Nat.mul_le_mul_right _ (by omega)
        _ = (q k + 1) ^ 3 := by ring
    have hbase :
        length + 1 ≤ (q k + 1) ^ R := by
      simpa [length] using hqpowadd
    have hexponent : 2 * degree ≤ 2 * A * (q k + 1) := by
      calc
        2 * degree ≤ 2 * (A * (q k + 1)) :=
          Nat.mul_le_mul_left 2 hdegree
        _ = 2 * A * (q k + 1) := by ring
    have hgroundPower :
        D * (degree + 1) * (length + 1) ^ (2 * degree) ≤
          (q k + 1) ^ (4 + R * (2 * A * (q k + 1))) := by
      calc
        D * (degree + 1) * (length + 1) ^ (2 * degree) ≤
            (q k + 1) * (q k + 1) ^ 3 *
              ((q k + 1) ^ R) ^ (2 * A * (q k + 1)) := by
          apply Nat.mul_le_mul
          · exact Nat.mul_le_mul hDle hdegreeCube
          · exact
              (Nat.pow_le_pow_left hbase _).trans
                (Nat.pow_le_pow_right (by positivity) hexponent)
        _ = (q k + 1) ^ (4 + R * (2 * A * (q k + 1))) := by
          calc
            (q k + 1) * (q k + 1) ^ 3 *
                ((q k + 1) ^ R) ^ (2 * A * (q k + 1)) =
              (q k + 1) ^ 4 *
                (q k + 1) ^ (R * (2 * A * (q k + 1))) := by
                  rw [pow_mul]
                  ring
            _ = _ := (pow_add _ _ _).symm
    have hexponentK :
        4 + R * (2 * A * (q k + 1)) ≤ K * (q k + 1) := by
      calc
        4 + R * (2 * A * (q k + 1)) ≤
            4 * (q k + 1) + R * (2 * A * (q k + 1)) := by
          gcongr
          omega
        _ = K * (q k + 1) := by
          dsimp [K]
          ring
    have hlogPower :
        (((4 + R * (2 * A * (q k + 1)) : ℕ) : ℝ)) *
            Real.log ((q k + 1 : ℕ) : ℝ) ≤ L k := by
      calc
        (((4 + R * (2 * A * (q k + 1)) : ℕ) : ℝ)) *
              Real.log ((q k + 1 : ℕ) : ℝ) ≤
            ((K * (q k + 1) : ℕ) : ℝ) * LL k := by
          apply mul_le_mul
          · exact_mod_cast hexponentK
          · exact hBlog
          · exact Real.log_nonneg (by norm_num)
          · positivity
        _ ≤ (K : ℝ) * (2 * x k) * LL k := by
          norm_num only [Nat.cast_mul]
          gcongr
        _ = L k / 2 := by
          dsimp [x, α]
          field_simp
          ring
        _ ≤ L k := by linarith
    have hpower_le :
        (q k + 1) ^ (4 + R * (2 * A * (q k + 1))) ≤ k := by
      have hkposNat : 0 < k := by
        by_contra hk
        have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk
        subst k
        norm_num [L] at hkL
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkposNat
      have hreal :
          (((q k + 1 : ℕ) : ℝ)) ^
              (4 + R * (2 * A * (q k + 1))) ≤ (k : ℝ) := by
        apply (Real.pow_le_iff_le_log (x := ((q k + 1 : ℕ) : ℝ))
          (y := (k : ℝ)) (n := 4 + R * (2 * A * (q k + 1)))
          (by positivity) hkpos).2
        simpa [L] using hlogPower
      exact_mod_cast hreal
    exact hgroundPower.trans hpower_le
  · have hlengthCast :
        (length : ℝ) = (q k : ℝ) ^ R := by
      simp [length]
    have hq_le_length_succ : (q k : ℝ) ≤ (length + 1 : ℕ) := by
      exact_mod_cast
        (show q k ≤ length + 1 from
          (Nat.le_pow (by omega : 0 < R)).trans (Nat.le_succ _))
    have hlogLength :
        LL k / 2 ≤ Real.log ((length + 1 : ℕ) : ℝ) := by
      exact hlogq.trans
        (Real.log_le_log (by exact_mod_cast hqpos) hq_le_length_succ)
    have hxpow :
        (x k) ^ R ≤ (length : ℝ) := by
      rw [hlengthCast]
      gcongr
    have halgebra :
        (α ^ R / 4) * (L k) ^ R / (LL k) ^ (R - 1) ≤
          (x k) ^ R * (LL k / 2) := by
      have hxpowEq :
          (x k) ^ R = α ^ R * (L k) ^ R / (LL k) ^ R := by
        dsimp [x]
        rw [div_pow, mul_pow]
      let z := α ^ R * (L k) ^ R / (LL k) ^ (R - 1)
      have hleft :
          (α ^ R / 4) * (L k) ^ R / (LL k) ^ (R - 1) = z / 4 := by
        dsimp [z]
        ring
      have hright : (x k) ^ R * (LL k / 2) = z / 2 := by
        have hαpow : α ^ R = α ^ (R - 1) * α := by
          calc
            α ^ R = α ^ ((R - 1) + 1) := by congr 1 <;> omega
            _ = _ := by rw [pow_add, pow_one]
        have hLpow : (L k) ^ R = (L k) ^ (R - 1) * L k := by
          calc
            (L k) ^ R = (L k) ^ ((R - 1) + 1) := by congr 1 <;> omega
            _ = _ := by rw [pow_add, pow_one]
        have hLLpow : (LL k) ^ R = (LL k) ^ (R - 1) * LL k := by
          calc
            (LL k) ^ R = (LL k) ^ ((R - 1) + 1) := by congr 1 <;> omega
            _ = _ := by rw [pow_add, pow_one]
        rw [hxpowEq, hαpow, hLpow, hLLpow]
        dsimp [z]
        rw [hαpow, hLpow]
        field_simp [hLLpos.ne']
      rw [hleft, hright]
      have hz : 0 ≤ z := by
        dsimp [z]
        positivity
      linarith
    have hlogFamily :
        (α ^ R / 4) * (L k) ^ R / (LL k) ^ (R - 1) ≤
          Real.log ((((length + 1) ^ length : ℕ) : ℝ)) := by
      calc
        _ ≤ (x k) ^ R * (LL k / 2) := halgebra
        _ ≤ (length : ℝ) *
              Real.log ((length + 1 : ℕ) : ℝ) := by
          exact mul_le_mul hxpow hlogLength
            (div_nonneg hLLpos.le (by norm_num)) (by positivity)
        _ = Real.log ((((length + 1) ^ length : ℕ) : ℝ)) := by
          norm_num only [Nat.cast_pow]
          rw [Real.log_pow]
    calc
      Real.exp
          ((α ^ R / 4) * (Real.log (k : ℝ)) ^ R /
            (Real.log (Real.log (k : ℝ))) ^ (R - 1)) ≤
          Real.exp (Real.log ((((length + 1) ^ length : ℕ) : ℝ))) := by
        apply Real.exp_le_exp.mpr
        simpa [L, LL] using hlogFamily
      _ = (((length + 1) ^ length : ℕ) : ℝ) := by
        rw [Real.exp_log]
        positivity

@[blueprint "lem:bbr-restricted-intersection-construction"
  (statement := /-- Let \(D>0\) be squarefree with exactly \(R\geq2\)
  distinct prime factors.  There is \(c>0\) such that, for every
  sufficiently large \(k\), some \(k'\leq k\) supports a canonical modular
  intersection family of size \(n\) satisfying
  \[
    \exp\!\left(c\,\frac{(\log k)^R}
      {(\log\log k)^{R-1}}\right)\leq n.
  \] -/)
  (proof := /-- Apply \cref{lem:bbr-polynomial-construction} to obtain a
  positive constant \(C\) and separating polynomials of every length.
  The parameter choice in
  \cref{lem:bbr-asymptotic-parameter-selection} supplies a positive real
  constant \(c\) and, for every sufficiently large \(k\), a length
  \(\ell\) for which every degree satisfying
  \(d^R\leq C(\ell+1)\) yields a ground-set bound at most \(k\), while
  \[
    \exp\!\left(c\frac{(\log k)^R}
      {(\log\log k)^{R-1}}\right)\leq(\ell+1)^\ell.
  \]
  Choose the separating polynomial and its degree \(d\), and apply
  \cref{lem:bbr-word-coefficient-selection}.  This produces a canonical
  modular intersection family of size \((\ell+1)^\ell\) on a ground set
  of size at most \(D(d+1)(\ell+1)^{2d}\), which is at most \(k\) by the
  parameter choice.  These inequalities give the required witnesses. -/)
  (title := /-- Quantitative restricted-intersection construction -/)
  (latexEnv := "lemma")]
lemma bbr_restricted_intersection_construction
    {D R : ℕ} (hDpos : 0 < D)
    (hDsquarefree : ∏ q ∈ D.primeFactors, q = D)
    (hR : D.primeFactors.card = R) (hRtwo : 2 ≤ R) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k : ℕ in atTop,
        ∃ k' n : ℕ,
          k' ≤ k ∧
          Nonempty (canonical_modular_intersection_family D k' n) ∧
          Real.exp
              (c * (Real.log (k : ℝ)) ^ R /
                (Real.log (Real.log (k : ℝ))) ^ (R - 1)) ≤
            (n : ℝ) := by
  rcases bbr_polynomial_construction hDpos hDsquarefree hR hRtwo with
    ⟨C, hCpos, hpolynomials⟩
  rcases bbr_asymptotic_parameter_selection hDpos hCpos hRtwo with
    ⟨c, hcpos, hparameters⟩
  refine ⟨c, hcpos, ?_⟩
  filter_upwards [hparameters] with k hk
  rcases hk with ⟨length, hground, hsize⟩
  rcases hpolynomials length with ⟨degree, ⟨P⟩, hdegree⟩
  rcases bbr_word_coefficient_selection hDpos P with
    ⟨k', hk'bound, hfamily⟩
  refine ⟨k', (length + 1) ^ length, ?_, hfamily, hsize⟩
  exact hk'bound.trans (hground degree hdegree)

@[blueprint "thm:grolmusz-bbr-intersection-family"
  (statement := /-- Let \(D>0\) be squarefree and have exactly \(R\geq2\)
  distinct prime factors.  There is a constant \(c>0\) such that, for every
  sufficiently large \(k\), there are a natural number \(n\) and a canonical
  modular intersection family of size \(n\) on a \(k\)-element ground set
  satisfying
  \[
    \exp\!\left(c\,\frac{(\log k)^R}
      {(\log\log k)^{R-1}}\right)\leq n.
  \] -/)
  (proof := /-- Invoke
  \cref{lem:bbr-restricted-intersection-construction} with the given
  squarefree modulus.  It supplies \(c>0\) and, for every sufficiently large
  \(k\), a number \(k'\leq k\), a size \(n\), and a canonical modular
  intersection family \((A_i)_{i<n}\) on \(\operatorname{Fin}(k')\) with
  the required lower bound expressed in terms of \(k\).

  Embed \(\operatorname{Fin}(k')\) as the initial segment of
  \(\operatorname{Fin}(k)\), and replace each \(A_i\) by its image under
  this injection.  Injectivity preserves the cardinality of every block
  and every pairwise intersection.  The diagonal residues therefore remain
  zero, and every off-diagonal residue remains a nonzero member of the
  canonical set modulo \(D\).  The image blocks consequently form a family
  in the sense of \cref{def:canonical-modular-intersection-family} on the
  required \(k\)-element ground set.  Neither \(n\) nor its lower bound
  changes under this padding. -/)
  (title := /-- Grolmusz--BBR modular intersection construction -/)
  (latexEnv := "theorem")]
theorem grolmusz_bbr_intersection_family
    {D R : ℕ} (hDpos : 0 < D)
    (hDsquarefree : ∏ q ∈ D.primeFactors, q = D)
    (hR : D.primeFactors.card = R) (hRtwo : 2 ≤ R) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k : ℕ in atTop,
        ∃ n : ℕ,
          Nonempty (canonical_modular_intersection_family D k n) ∧
          Real.exp
              (c * (Real.log (k : ℝ)) ^ R /
                (Real.log (Real.log (k : ℝ))) ^ (R - 1)) ≤
            (n : ℝ) := by
  rcases bbr_restricted_intersection_construction hDpos hDsquarefree hR hRtwo with
    ⟨c, hc, hfamilies⟩
  refine ⟨c, hc, ?_⟩
  filter_upwards [hfamilies] with k hk
  rcases hk with ⟨k', n, hk'k, ⟨family⟩, hsize⟩
  let emb : Fin k' ↪ Fin k :=
    { toFun := (fun a => ⟨a.val, lt_of_lt_of_le a.isLt hk'k⟩)
      inj' := by
        intro a b hab
        apply Fin.ext
        exact congrArg (fun x : Fin k => x.val) hab }
  refine ⟨n, ?_, hsize⟩
  refine ⟨{ blocks := (fun i => (family.blocks i).map emb)
            diagonalCard := ?_
            offDiagonalCard := ?_ }⟩
  · intro i
    simpa using family.diagonalCard i
  · intro i j hij
    rw [← Finset.map_inter]
    simpa using family.offDiagonalCard i j hij

@[blueprint "lem:modular-intersection-family-gives-matching-vectors"
  (statement := /-- Let \(D,k,n\) be natural numbers.  Every canonical
  modular intersection family of size \(n\) on a \(k\)-element ground set
  determines a canonical matching-vector family of size \(n\) in
  \((\mathbb Z/D\mathbb Z)^k\). -/)
  (proof := /-- Let \((A_i)_{i<n}\) be the family supplied by
  \cref{def:canonical-modular-intersection-family}.  For \(i<n\), let both
  \(u_i\) and \(v_i\) be the incidence vector of \(A_i\), regarded as a
  vector over \(\mathbb Z/D\mathbb Z\).  Then
  \[
    \langle u_i,v_j\rangle
      =\sum_{a<k}\mathbf1_{A_i}(a)\mathbf1_{A_j}(a)
      =|A_i\cap A_j|\pmod D.
  \]
  When \(i=j\), this is \(|A_i|\), which is zero modulo \(D\).  When
  \(i\ne j\), the defining intersection condition says that it is a
  nonzero member of the canonical set.  These are exactly the diagonal and
  off-diagonal requirements in
  \cref{def:canonical-matching-vector-family}. -/)
  (title := /-- Incidence vectors from modular intersection families -/)
  (latexEnv := "lemma")]
lemma modular_intersection_family_gives_matching_vectors
    {D k n : ℕ} :
    Nonempty (canonical_modular_intersection_family D k n) →
      Nonempty (canonical_matching_vector_family D k n) := by
  classical
  rintro ⟨family⟩
  refine ⟨{ left := fun i a => if a ∈ family.blocks i then 1 else 0
            right := fun i a => if a ∈ family.blocks i then 1 else 0
            diagonal := ?_
            offDiagonal := ?_ }⟩
  · intro i
    simpa using family.diagonalCard i
  · intro i j hij
    simpa [Finset.mem_inter] using family.offDiagonalCard j i hij.symm

@[blueprint "thm:MVF"
  (statement := /-- Let \(D\) be a squarefree positive integer with exactly
  \(R\geq 2\) distinct prime factors.  Then there is a constant \(c>0\) such
  that, for every sufficiently large \(k\), there is a canonical matching-vector
  family modulo \(D\), of dimension \(k\) and some size \(n\), satisfying
  \[
    \exp\!\left(c\,\frac{(\log k)^R}{(\log\log k)^{R-1}}\right)\leq n.
  \] -/)
  (proof := /-- Apply
  \cref{thm:grolmusz-bbr-intersection-family} to \(D\) and \(R\).  It gives
  a constant \(c>0\) and, for every sufficiently large dimension \(k\), a
  canonical modular intersection family of some size \(n\) satisfying
  \[
    \exp\!\left(c\,\frac{(\log k)^R}{(\log\log k)^{R-1}}\right)\leq n.
  \]
  Convert each of these set families by
  \cref{lem:modular-intersection-family-gives-matching-vectors}.  The
  conversion preserves both the dimension \(k\) and the size \(n\), so it
  preserves the displayed lower bound.  The resulting eventual family is
  precisely the assertion of
  \cref{def:has-large-canonical-matching-vector-families}. -/)
  (title := /-- Large squarefree matching-vector families -/)
  (latexEnv := "theorem")]
theorem MVF {D R : ℕ} (hDpos : 0 < D)
    (hDsquarefree : ∏ q ∈ D.primeFactors, q = D)
    (hR : D.primeFactors.card = R) (hRtwo : 2 ≤ R) :
    has_large_canonical_matching_vector_families D R := by
  rcases grolmusz_bbr_intersection_family hDpos hDsquarefree hR hRtwo with
    ⟨c, hc, hfamilies⟩
  refine ⟨c, hc, ?_⟩
  filter_upwards [hfamilies] with k hk
  rcases hk with ⟨n, hfamily, hsize⟩
  refine ⟨n, ?_, hsize⟩
  exact modular_intersection_family_gives_matching_vectors hfamily

@[blueprint "lem:finite-commutative-monoid-common-idempotent-power"
  (statement := /-- Let \(A\) be a finite commutative monoid.  There is a
  positive natural number \(E\) such that \((x^E)^2=x^E\) for every
  \(x\in A\). -/)
  (proof := /-- Since the set of functions from \(A\) to itself is finite,
  two distinct power maps \(x\mapsto x^a\) and \(x\mapsto x^b\) coincide.
  Order the exponents so that \(a<b\) and put \(d=b-a\).  Multiplying the
  equality \(x^a=x^b\) by further powers shows that powers are periodic
  with period \(d\) from exponent \(a\) onward.  The positive exponent
  \(E=bd\) lies in this stable range and is divisible by \(d\), so
  \(x^{2E}=x^E\) for every \(x\in A\). -/)
  (title := /-- A common idempotent power in a finite commutative monoid -/)
  (latexEnv := "lemma")]
lemma finite_commutative_monoid_common_idempotent_power
    (A : Type*) [CommMonoid A] [Fintype A] :
    ∃ E : ℕ, 0 < E ∧ ∀ x : A, (x ^ E) ^ 2 = x ^ E := by
  classical
  have build :
      ∀ {a b : ℕ}, a < b →
        (fun x : A => x ^ a) = (fun x : A => x ^ b) →
        ∃ E : ℕ, 0 < E ∧ ∀ x : A, (x ^ E) ^ 2 = x ^ E := by
    intro a b hab hpow
    let d := b - a
    let E := b * d
    have hd : 0 < d := by dsimp [d]; omega
    have hb : 0 < b := by omega
    have hE : 0 < E := Nat.mul_pos hb hd
    refine ⟨E, hE, ?_⟩
    intro x
    have hx : x ^ a = x ^ b := congrFun hpow x
    have hperiod (n : ℕ) (han : a ≤ n) : x ^ n = x ^ (n + d) := by
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le han
      calc
        x ^ (a + c) = x ^ a * x ^ c := pow_add x a c
        _ = x ^ b * x ^ c := by rw [hx]
        _ = x ^ (b + c) := (pow_add x b c).symm
        _ = x ^ (a + c + d) := by
          congr 1
          dsimp [d]
          omega
    have haE : a ≤ E := by
      dsimp [E]
      nlinarith
    have hiter : ∀ t : ℕ, x ^ E = x ^ (E + t * d) := by
      intro t
      induction t with
      | zero => simp
      | succ t iht =>
          calc
            x ^ E = x ^ (E + t * d) := iht
            _ = x ^ (E + t * d + d) :=
              hperiod _ (haE.trans (Nat.le_add_right E (t * d)))
            _ = x ^ (E + (t + 1) * d) := by
              congr 1
              simp [Nat.succ_mul, Nat.add_assoc]
    calc
      (x ^ E) ^ 2 = x ^ (E * 2) := (pow_mul x E 2).symm
      _ = x ^ (E + b * d) := by
        congr 1
        dsimp [E]
        omega
      _ = x ^ E := (hiter b).symm
  obtain ⟨a, b, hab, hpow⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => fun x : A => x ^ n)
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · exact build hablt hpow
  · exact build hbalt hpow.symm

@[blueprint "lem:matching-vector-family-lift-from-radical"
  (statement := /-- Let \(M,k,n,E\) be natural numbers with \(M>0\) and
  \(E>0\).  Suppose that the \(E\)-th power of every residue modulo \(M\)
  is idempotent.  Every canonical matching-vector family modulo the radical
  of \(M\), of dimension \(k\) and size \(n\), then gives one modulo \(M\),
  of dimension \(k^E\) and the same size. -/)
  (proof := /-- Lift each source coordinate to its standard natural
  representative modulo \(M\), and index the new coordinates by
  \(E\)-tuples of old coordinates.  Define each new vector coordinate as
  the product over the corresponding tuple.  Distributivity shows that
  every new inner product is the \(E\)-th power of the lifted old inner
  product.  It is idempotent by hypothesis.  Reduction modulo the radical
  sends it to the positive power of the old idempotent, hence to the old
  idempotent itself.  Thus an off-diagonal product remains nonzero.  On the
  diagonal the new product is both idempotent and nilpotent: its reduction
  modulo the radical is zero, while the modulus divides a power of its
  radical.  An idempotent nilpotent element is zero. -/)
  (title := /-- Tensor-power lift from the radical modulus -/)
  (latexEnv := "lemma")]
lemma matching_vector_family_lift_from_radical
    {M k n E : ℕ} (hM : 0 < M) (hE : 0 < E)
    (hpower : ∀ x : ZMod M, (x ^ E) ^ 2 = x ^ E) :
    Nonempty
        (canonical_matching_vector_family
          (∏ q ∈ M.primeFactors, q) k n) →
      Nonempty (canonical_matching_vector_family M (k ^ E) n) := by
  classical
  letI : NeZero M := ⟨hM.ne'⟩
  let D : ℕ := ∏ q ∈ M.primeFactors, q
  have hDpos : 0 < D := by
    dsimp [D]
    exact Finset.prod_pos fun q hq => (Nat.prime_of_mem_primeFactors hq).pos
  letI : NeZero D := ⟨hDpos.ne'⟩
  have hDDvd : D ∣ M := by
    dsimp [D]
    exact Nat.prod_primeFactors_dvd M
  let reduce : ZMod M →+* ZMod D := ZMod.castHom hDDvd (ZMod D)
  change Nonempty (canonical_matching_vector_family D k n) →
    Nonempty (canonical_matching_vector_family M (k ^ E) n)
  rintro ⟨family⟩
  let coordinateEquiv : (Fin E → Fin k) ≃ Fin (k ^ E) :=
    Fintype.equivFinOfCardEq (by simp)
  let base (i j : Fin n) : ZMod M :=
    ∑ a : Fin k,
      ((family.left i a).val : ZMod M) * ((family.right j a).val : ZMod M)
  let newLeft (i : Fin n) (z : Fin (k ^ E)) : ZMod M :=
    ∏ e : Fin E, ((family.left i (coordinateEquiv.symm z e)).val : ZMod M)
  let newRight (j : Fin n) (z : Fin (k ^ E)) : ZMod M :=
    ∏ e : Fin E, ((family.right j (coordinateEquiv.symm z e)).val : ZMod M)
  have hdot (i j : Fin n) :
      (∑ z : Fin (k ^ E), newLeft i z * newRight j z) = (base i j) ^ E := by
    calc
      (∑ z : Fin (k ^ E), newLeft i z * newRight j z) =
          ∑ f : Fin E → Fin k,
            (∏ e : Fin E, ((family.left i (f e)).val : ZMod M)) *
              ∏ e : Fin E, ((family.right j (f e)).val : ZMod M) := by
        simpa [newLeft, newRight] using
          (coordinateEquiv.symm.sum_comp
            (fun f : Fin E → Fin k =>
              (∏ e : Fin E, ((family.left i (f e)).val : ZMod M)) *
                ∏ e : Fin E, ((family.right j (f e)).val : ZMod M)))
      _ = ∑ f : Fin E → Fin k,
            ∏ e : Fin E,
              ((family.left i (f e)).val : ZMod M) *
                ((family.right j (f e)).val : ZMod M) := by
        apply Finset.sum_congr rfl
        intro f hf
        exact Finset.prod_mul_distrib.symm
      _ = (base i j) ^ E := by
        dsimp [base]
        symm
        simpa using
          (Finset.sum_pow' (Finset.univ : Finset (Fin k))
            (fun a : Fin k =>
              ((family.left i a).val : ZMod M) *
                ((family.right j a).val : ZMod M)) E)
  have hreduce (i j : Fin n) :
      reduce (base i j) =
        ∑ a : Fin k, family.left i a * family.right j a := by
    dsimp only [base]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [map_mul, map_natCast, map_natCast]
    change
      ((family.left i a).val : ZMod D) *
          ((family.right j a).val : ZMod D) =
        family.left i a * family.right j a
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  refine ⟨{
    left := newLeft
    right := newRight
    diagonal := ?_
    offDiagonal := ?_ }⟩
  · intro i
    rw [hdot]
    let y : ZMod M := (base i i) ^ E
    have hyIdem : IsIdempotentElem y := by
      simpa [y, IsIdempotentElem, pow_two] using hpower (base i i)
    have hyReduce : reduce y = 0 := by
      dsimp [y]
      rw [map_pow, hreduce i i, family.diagonal i, zero_pow hE.ne']
    have hradicalDvdVal : D ∣ y.val := by
      apply (ZMod.natCast_eq_zero_iff y.val D).mp
      simpa [reduce, ZMod.castHom] using hyReduce
    have hyPow : y ^ M = 0 := by
      rw [← ZMod.natCast_zmod_val y, ← Nat.cast_pow]
      apply (ZMod.natCast_eq_zero_iff (y.val ^ M) M).2
      exact (Nat.dvd_prod_primeFactors_pow_self hM.ne').trans
        (pow_dvd_pow_of_dvd hradicalDvdVal M)
    have hyPowEq : y ^ M = y := by
      exact hyIdem.pow_eq hM.ne'
    exact hyPowEq.symm.trans hyPow
  · intro i j hij
    rw [hdot]
    refine ⟨hpower (base i j), ?_⟩
    intro hzero
    have hmapped := congrArg reduce hzero
    rw [map_pow, hreduce i j] at hmapped
    have hsourceIdem :
        IsIdempotentElem (∑ a : Fin k, family.left i a * family.right j a) := by
      simpa [canonical_set, IsIdempotentElem, pow_two] using
        (family.offDiagonal i j hij).1
    rw [hsourceIdem.pow_eq hE.ne'] at hmapped
    exact (family.offDiagonal i j hij).2 (by simpa using hmapped)

@[blueprint "lem:matching-vector-family-pad-dimension"
  (statement := /-- Let \(M,k,K,n\) be natural numbers with \(k\leq K\).
  Every canonical matching-vector family modulo \(M\), of dimension \(k\)
  and size \(n\), extends to one of dimension \(K\) and the same size. -/)
  (proof := /-- Append \(K-k\) zero coordinates to both vectors in every
  pair.  Splitting each inner product into its original and appended parts,
  the latter part is zero.  Thus the diagonal and off-diagonal conditions
  from \cref{def:canonical-matching-vector-family} are unchanged. -/)
  (title := /-- Padding a matching-vector family with zero coordinates -/)
  (latexEnv := "lemma")]
lemma matching_vector_family_pad_dimension
    {M k K n : ℕ} (hkK : k ≤ K) :
    Nonempty (canonical_matching_vector_family M k n) →
      Nonempty (canonical_matching_vector_family M K n) := by
  rintro ⟨family⟩
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hkK
  refine ⟨{
    left := fun i => Fin.addCases (family.left i) (fun _ => 0)
    right := fun i => Fin.addCases (family.right i) (fun _ => 0)
    diagonal := ?_
    offDiagonal := ?_ }⟩
  · intro i
    simpa [Fin.sum_univ_add] using family.diagonal i
  · intro i j hij
    simpa [Fin.sum_univ_add] using family.offDiagonal i j hij

@[blueprint "lem:large-matching-vector-families-lift-from-radical"
  (statement := /-- Let \(M,R\) be natural numbers with \(M>0\) and
  \(R\geq2\).  If canonical matching-vector families modulo the squarefree
  kernel \(\prod_{q\mid M}q\) have the large-family rate of rank \(R\),
  then families modulo \(M\) have the same rate. -/)
  (proof := /-- Choose a common positive exponent \(E\) whose powers are
  idempotent modulo \(M\) by
  \cref{lem:finite-commutative-monoid-common-idempotent-power}.  For a target
  dimension \(k\), put
  \(d=\lfloor\exp((\log k)/E)\rfloor\).  The source rate supplies a family
  of dimension \(d\).  Lift it by
  \cref{lem:matching-vector-family-lift-from-radical}, obtaining dimension
  \(d^E\leq k\), and pad it to dimension \(k\) using
  \cref{lem:matching-vector-family-pad-dimension}.

  For all sufficiently large \(k\), the floor bounds give
  \(d\geq \exp((\log k)/E)/2\).  Consequently
  \(\log d\geq (\log k)/(2E)\), while \(d\leq k\) gives
  \(\log\log d\leq\log\log k\).  Dividing the source growth constant by
  \((2E)^R\) therefore preserves the required rank-\(R\) lower bound. -/)
  (title := /-- Large matching-vector rates lift from the squarefree kernel -/)
  (latexEnv := "lemma")]
lemma large_matching_vector_families_lift_from_radical
    {M R : ℕ} (hM : 0 < M) (hR : 2 ≤ R)
    (hfamilies :
      has_large_canonical_matching_vector_families
        (∏ q ∈ M.primeFactors, q) R) :
    has_large_canonical_matching_vector_families M R := by
  classical
  letI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨E, hE, hpower⟩ :=
    finite_commutative_monoid_common_idempotent_power (ZMod M)
  rcases hfamilies with ⟨c, hc, hsource⟩
  let root : ℕ → ℝ := fun k =>
    Real.exp (Real.log (k : ℝ) / (E : ℝ))
  let sourceDimension : ℕ → ℕ := fun k => ⌊root k⌋₊
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hEreal : (0 : ℝ) < (E : ℝ) := by exact_mod_cast hE
  have hroot : Tendsto root atTop atTop := by
    exact Real.tendsto_exp_atTop.comp (hlog.atTop_div_const hEreal)
  have hdimension : Tendsto sourceDimension atTop atTop := by
    exact tendsto_nat_floor_atTop.comp hroot
  have hsourceAt :
      ∀ᶠ k : ℕ in atTop,
        ∃ n : ℕ,
          Nonempty
            (canonical_matching_vector_family
              (∏ q ∈ M.primeFactors, q) (sourceDimension k) n) ∧
          Real.exp
              (c * (Real.log (sourceDimension k : ℝ)) ^ R /
                (Real.log (Real.log (sourceDimension k : ℝ))) ^ (R - 1)) ≤
            (n : ℝ) := by
    exact hdimension.eventually hsource
  have hlogSource :
      Tendsto (fun k : ℕ => Real.log (sourceDimension k : ℝ)) atTop atTop :=
    hlog.comp hdimension
  let scale : ℝ := (2 * (E : ℝ)) ^ R
  have hscale : 0 < scale := by
    dsimp [scale]
    positivity
  refine ⟨c / scale, div_pos hc hscale, ?_⟩
  filter_upwards [hsourceAt, hroot.eventually_ge_atTop 2,
      hlog.eventually_ge_atTop (2 * (E : ℝ) * Real.log 2),
      hlog.eventually_ge_atTop 2,
      hlogSource.eventually_ge_atTop 2] with
      k hkSource hkRoot hkLogBound hkLogTwo hkSourceLogTwo
  rcases hkSource with ⟨n, hfamily, hn⟩
  have hkLogPos : 0 < Real.log (k : ℝ) := zero_lt_two.trans_le hkLogTwo
  have hkNe : k ≠ 0 := by
    intro hk
    subst k
    norm_num at hkLogPos
  have hkPosNat : 0 < k := Nat.pos_of_ne_zero hkNe
  have hkPos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkPosNat
  have hrootPos : 0 < root k := by
    dsimp [root]
    positivity
  have hdimensionUpper : (sourceDimension k : ℝ) ≤ root k := by
    exact Nat.floor_le hrootPos.le
  have hdimensionLower : root k / 2 ≤ (sourceDimension k : ℝ) := by
    have hlt := Nat.lt_floor_add_one (root k)
    linarith
  have hrootPower : (root k) ^ E = (k : ℝ) := by
    calc
      (root k) ^ E = Real.exp ((E : ℝ) *
          (Real.log (k : ℝ) / (E : ℝ))) := by
        dsimp [root]
        rw [← Real.exp_nat_mul]
      _ = Real.exp (Real.log (k : ℝ)) := by
        congr 1
        field_simp
      _ = (k : ℝ) := Real.exp_log hkPos
  have hdimensionPower : sourceDimension k ^ E ≤ k := by
    exact_mod_cast (show ((sourceDimension k : ℝ) ^ E) ≤ (k : ℝ) from
      calc
        (sourceDimension k : ℝ) ^ E ≤ (root k) ^ E := by gcongr
        _ = (k : ℝ) := hrootPower)
  have hrootLe : root k ≤ (k : ℝ) := by
    have hEle : (1 : ℝ) ≤ (E : ℝ) := by exact_mod_cast hE
    calc
      root k ≤ Real.exp (Real.log (k : ℝ)) := by
        apply Real.exp_le_exp.mpr
        exact div_le_self hkLogPos.le hEle
      _ = (k : ℝ) := Real.exp_log hkPos
  have hdimensionLe : (sourceDimension k : ℝ) ≤ (k : ℝ) :=
    hdimensionUpper.trans hrootLe
  have hsourceDimensionPos : (0 : ℝ) < (sourceDimension k : ℝ) := by
    have hne : sourceDimension k ≠ 0 := by
      intro hzero
      rw [hzero] at hkSourceLogTwo
      norm_num at hkSourceLogTwo
    exact_mod_cast Nat.pos_of_ne_zero hne
  have hlogLower :
      Real.log (k : ℝ) / (2 * (E : ℝ)) ≤
        Real.log (sourceDimension k : ℝ) := by
    calc
      Real.log (k : ℝ) / (2 * (E : ℝ)) ≤
          Real.log (k : ℝ) / (E : ℝ) - Real.log 2 := by
        field_simp
        nlinarith
      _ = Real.log (root k / 2) := by
        rw [Real.log_div (ne_of_gt hrootPos) (by norm_num : (2 : ℝ) ≠ 0)]
        dsimp [root]
        rw [Real.log_exp]
      _ ≤ Real.log (sourceDimension k : ℝ) :=
        Real.log_le_log (div_pos hrootPos (by norm_num)) hdimensionLower
  have hlogDimensionLe :
      Real.log (sourceDimension k : ℝ) ≤ Real.log (k : ℝ) :=
    Real.log_le_log hsourceDimensionPos hdimensionLe
  have hlogLogDimensionLe :
      Real.log (Real.log (sourceDimension k : ℝ)) ≤
        Real.log (Real.log (k : ℝ)) := by
    exact Real.log_le_log (zero_lt_two.trans_le hkSourceLogTwo) hlogDimensionLe
  have hsourceLogLogPos :
      0 < Real.log (Real.log (sourceDimension k : ℝ)) :=
    Real.log_pos (one_lt_two.trans_le hkSourceLogTwo)
  have hkLogLogPos : 0 < Real.log (Real.log (k : ℝ)) :=
    Real.log_pos (one_lt_two.trans_le hkLogTwo)
  have hnumerator :
      (c / scale) * (Real.log (k : ℝ)) ^ R ≤
        c * (Real.log (sourceDimension k : ℝ)) ^ R := by
    have hpow :
        (Real.log (k : ℝ) / (2 * (E : ℝ))) ^ R ≤
          (Real.log (sourceDimension k : ℝ)) ^ R := by
      gcongr
    calc
      (c / scale) * (Real.log (k : ℝ)) ^ R =
          c * (Real.log (k : ℝ) / (2 * (E : ℝ))) ^ R := by
        dsimp [scale]
        rw [div_pow]
        ring
      _ ≤ c * (Real.log (sourceDimension k : ℝ)) ^ R :=
        mul_le_mul_of_nonneg_left hpow hc.le
  have hdenominator :
      (Real.log (Real.log (sourceDimension k : ℝ))) ^ (R - 1) ≤
        (Real.log (Real.log (k : ℝ))) ^ (R - 1) := by
    gcongr
  have htargetNumeratorNonneg :
      0 ≤ (c / scale) * (Real.log (k : ℝ)) ^ R := by positivity
  have hexponent :
      (c / scale) * (Real.log (k : ℝ)) ^ R /
          (Real.log (Real.log (k : ℝ))) ^ (R - 1) ≤
        c * (Real.log (sourceDimension k : ℝ)) ^ R /
          (Real.log (Real.log (sourceDimension k : ℝ))) ^ (R - 1) := by
    calc
      (c / scale) * (Real.log (k : ℝ)) ^ R /
            (Real.log (Real.log (k : ℝ))) ^ (R - 1) ≤
          (c / scale) * (Real.log (k : ℝ)) ^ R /
            (Real.log (Real.log (sourceDimension k : ℝ))) ^ (R - 1) :=
        div_le_div_of_nonneg_left htargetNumeratorNonneg
          (pow_pos hsourceLogLogPos (R - 1)) hdenominator
      _ ≤ c * (Real.log (sourceDimension k : ℝ)) ^ R /
            (Real.log (Real.log (sourceDimension k : ℝ))) ^ (R - 1) :=
        div_le_div_of_nonneg_right hnumerator
          (pow_nonneg hsourceLogLogPos.le (R - 1))
  refine ⟨n, ?_, (Real.exp_le_exp.mpr hexponent).trans hn⟩
  exact matching_vector_family_pad_dimension hdimensionPower
    (matching_vector_family_lift_from_radical hM hE hpower hfamily)

@[blueprint "lem:prime-modulus-rank-one-matching-vectors"
  (statement := /-- Let \(p\) be a prime natural number.  Canonical
  matching-vector families modulo \(p\) have the large-family rate of
  rank one. -/)
  (proof := /-- For every positive dimension \(k\), index a family of size
  \(k\) by the standard basis.  Let \(u_i\) be the \(i\)-th basis vector
  and let \(v_i\) have value zero in coordinate \(i\) and value one in all
  other coordinates.  The diagonal inner products are zero and every
  off-diagonal inner product is one, which is a nonzero member of the
  canonical set modulo the prime \(p\) by
  \cref{def:canonical-matching-vector-family}.  With growth constant one,
  the required lower bound from
  \cref{def:has-large-canonical-matching-vector-families} is the identity
  \(\exp(\log k)=k\). -/)
  (title := /-- Rank-one matching vectors modulo a prime -/)
  (latexEnv := "lemma")]
lemma prime_modulus_rank_one_matching_vectors
    {p : ℕ} (hp : p.Prime) :
    has_large_canonical_matching_vector_families p 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨1, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with k hk
  refine ⟨k, ⟨{
    left := fun i a => if i = a then 1 else 0
    right := fun i a => if i = a then 0 else 1
    diagonal := ?_
    offDiagonal := ?_ }⟩, ?_⟩
  · intro i
    apply Finset.sum_eq_zero
    intro a ha
    by_cases hia : i = a <;> simp [hia]
  · intro i j hij
    have hsum :
        (∑ a : Fin k,
          (if i = a then (1 : ZMod p) else 0) *
            (if j = a then 0 else 1)) = 1 := by
      calc
        _ = ∑ a : Fin k, if i = a then (1 : ZMod p) else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          by_cases hia : i = a
          · have hja : j ≠ a := by
              intro hja
              exact hij (hia.trans hja.symm)
            simp [hia, hja]
          · simp [hia]
        _ = 1 := by simp
    rw [hsum]
    exact ⟨by simp [canonical_set], one_ne_zero⟩
  · have hkposNat : 0 < k := Nat.zero_lt_of_lt hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkposNat
    norm_num [Real.exp_log hkpos]

@[blueprint "lem:main-matching-vector-input-gap"
  (statement := /-- Let \(m,r,p\) be natural numbers.  Suppose that \(m>0\)
  has exactly \(r\) distinct prime factors and that \(p\) is prime with
  \(p\nmid m\).  Then canonical matching-vector families modulo \(mp\) have
  the large-family rate of rank \(r+1\). -/)
  (proof := /-- If \(r=0\), then the prime-factor set of the positive
  integer \(m\) is empty, so \(m=1\).  The conclusion is therefore exactly
  the rank-one prime-modulus construction from
  \cref{lem:prime-modulus-rank-one-matching-vectors}.

  Suppose now that \(r>0\), and put \(M=mp\) and
  \(D=\prod_{q\mid M}q\).  Since \(p\) is prime and does not divide \(m\),
  the prime-factor sets of \(m\) and \(p\) are disjoint.  Hence \(D>0\),
  its prime factors are precisely those of \(M\), and it is squarefree
  with exactly \(r+1\geq2\) prime factors.  Applying \cref{thm:MVF} to
  \(D\) gives the large-family rate of rank \(r+1\) modulo \(D\).
  Finally,
  \cref{lem:large-matching-vector-families-lift-from-radical} transfers
  that rate from the squarefree kernel \(D\) to \(M=mp\), proving the
  claim. -/)
  (title := /-- Matching-vector input for the main theorem -/)
  (latexEnv := "lemma")]
lemma main_matching_vector_input_gap
    {m r p : ℕ} (hm : 0 < m)
    (hr : m.primeFactors.card = r)
    (hp : p.Prime) (hcoprime : ¬p ∣ m) :
    has_large_canonical_matching_vector_families (m * p) (r + 1) := by
  classical
  by_cases hrzero : r = 0
  · have hprimeFactorsEmpty : m.primeFactors = ∅ := by
      apply Finset.card_eq_zero.mp
      exact hr.trans hrzero
    have hmOne : m = 1 := by
      rcases Nat.primeFactors_eq_empty.mp hprimeFactorsEmpty with hmZero | hmOne
      · exact (hm.ne' hmZero).elim
      · exact hmOne
    subst m
    subst r
    simpa using prime_modulus_rank_one_matching_vectors hp
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hrzero
    have hmpCoprime : Nat.Coprime m p :=
      (hp.coprime_iff_not_dvd.mpr hcoprime).symm
    have hmpPos : 0 < m * p := Nat.mul_pos hm hp.pos
    have hkernelPos :
        0 < ∏ q ∈ (m * p).primeFactors, q := by
      exact Finset.prod_pos fun q hq => (Nat.prime_of_mem_primeFactors hq).pos
    have hkernelFactors :
        (∏ q ∈ (m * p).primeFactors, q).primeFactors =
          (m * p).primeFactors := by
      ext q
      constructor
      · intro hq
        rcases Nat.mem_primeFactors.mp hq with ⟨hqPrime, hqDvd, hkernelNe⟩
        have hprimeDvdProd :
            ∀ s : Finset ℕ, q ∣ ∏ a ∈ s, a → ∃ a ∈ s, q ∣ a := by
          intro s
          induction s using Finset.induction_on with
          | empty => simpa [hqPrime.ne_one]
          | @insert a s ha ih =>
              rw [Finset.prod_insert ha]
              intro hqMul
              rcases hqPrime.dvd_mul.mp hqMul with hqA | hqS
              · exact ⟨a, Finset.mem_insert_self a s, hqA⟩
              · rcases ih hqS with ⟨b, hb, hqB⟩
                exact ⟨b, Finset.mem_insert_of_mem hb, hqB⟩
        rcases hprimeDvdProd (m * p).primeFactors hqDvd with
          ⟨a, ha, hqDvdA⟩
        have haPrime : a.Prime := Nat.prime_of_mem_primeFactors ha
        have hqa : q = a := ((haPrime.dvd_iff_eq hqPrime.ne_one).mp hqDvdA).symm
        simpa [hqa] using ha
      · intro hq
        apply Nat.mem_primeFactors.mpr
        refine ⟨Nat.prime_of_mem_primeFactors hq, ?_, hkernelPos.ne'⟩
        exact Finset.dvd_prod_of_mem (fun a : ℕ => a) hq
    have hkernelSquarefree :
        ∏ q ∈ (∏ q ∈ (m * p).primeFactors, q).primeFactors, q =
          ∏ q ∈ (m * p).primeFactors, q := by
      rw [hkernelFactors]
    have hkernelCard :
        (∏ q ∈ (m * p).primeFactors, q).primeFactors.card = r + 1 := by
      have hdisjoint : Disjoint m.primeFactors {p} := by
        simpa [hp.primeFactors] using hmpCoprime.disjoint_primeFactors
      rw [hkernelFactors, hmpCoprime.primeFactors_mul,
        hp.primeFactors,
        Finset.card_union_of_disjoint hdisjoint]
      simp [hr]
    apply large_matching_vector_families_lift_from_radical hmpPos (by omega)
    exact MVF hkernelPos hkernelSquarefree hkernelCard (by omega)

@[blueprint "lem:multiplicity-interpolation-gives-pir-cost"
  (statement := /-- Let \(F\) be a field of characteristic \(p\), and let
  \(m,p,t\) be natural numbers such that \(m>0\) and \(p\) is prime.  If
  canonical multiplicity-two interpolation modulo \(mp\) is available with
  at most \(t\) evaluation points for canonically supported response
  polynomials, then there is a positive integer \(C\) such that, for every
  pair of natural numbers \(k,n\), every canonical matching-vector family
  modulo \(mp\) of dimension \(k\) and size \(n\) yields a one-round
  \(t\)-server PIR scheme for \(n\)-bit databases whose total encoded
  communication is at most \(C(k+1)\). -/)
  (proof := /-- Unpack
  \cref{def:has-canonical-multiplicity-interpolation} as an interpolation set
  \(B\) of cardinality at most \(t\), with the root and multiplicity-two
  uniqueness properties in
  \cref{def:is-zero-interpolating-with-multiplicity}.  The set \(B\) is
  nonempty, since otherwise applying uniqueness to the canonically supported
  polynomials \(0\) and \(1\) would equate their constant coefficients.
  Consequently \(t>0\), and \(B\) embeds into the server set; use a fixed
  element of \(B\) to label any remaining servers.

  Fix a family from \cref{def:canonical-matching-vector-family}, write
  \(R\) for the finite group of \(mp\)-th roots of unity in \(F\), and put
  \(H=R\to\mathbb Z/p\mathbb Z\).  To retrieve index \(i\), choose a uniform
  mask \(z\in R^k\).  At the server labelled by \(b\in B\), send
  \[
    q_a=z_a b^{u_{i,a}}.
  \]
  For \(\mu_l(q)=\prod_a q_a^{v_{l,a}}\), the server returns the query itself
  together with one histogram in \(H\) counting the values \(\mu_l(q)\) for
  selected database positions and, for every coordinate \(a\), one histogram
  weighted by \(v_{l,a}\) modulo \(p\).  Decoding a histogram \(h\) as
  \(\sum_{x\in R}h(x)x\) in \(F\) gives the required finite answer alphabet
  even when \(F\) is infinite.

  Let \(d_{il}=\langle u_i,v_l\rangle\in\mathbb Z/(mp)\mathbb Z\) and form
  \[
    P_{D,i,z}(X)=\sum_{l:D_l=1}\mu_l(z)X^{\operatorname{val}(d_{il})}.
  \]
  The diagonal and off-diagonal conditions place every exponent in the set
  of \cref{def:canonical-set}, so \(P_{D,i,z}\) satisfies
  \cref{def:polynomial-supported-on-residues}.  The identity
  \(\mu_l(q)=\mu_l(z)b^{\operatorname{val}(d_{il})}\) identifies the first
  decoded histogram with \(P_{D,i,z}(b)\).  After casting the inner product
  through the characteristic-\(p\) field, the weighted histograms identify
  \(b^{-1}\sum_a u_{i,a}h_a\) with the first Hasse derivative of
  \(P_{D,i,z}\) at \(b\).

  If two complete transcripts agree, their echoed queries at one server
  agree; the corresponding multiplicative shift is a bijection, so their
  masks agree.  Their decoded values and first Hasse derivatives then agree
  at every point of \(B\).  Multiplicity-two uniqueness gives equality of
  constant coefficients.  That coefficient is \(D_i\mu_i(z)\), and
  \(\mu_i(z)\) is a unit, hence the two requested bits agree.  Define
  reconstruction by choosing any database and mask producing the received
  transcript; the preceding uniqueness proves perfect correctness.

  Multiplication by the fixed query shift is a permutation of \(R^k\), so
  the uniform mask makes every individual query marginal independent of
  \(i\).  Thus the correctness and privacy fields of
  \cref{def:one-round-pir-scheme} hold.  Coordinatewise one-hot encodings use
  \(k|R|\) query bits and \(k|R|+(k+1)|H|\) answer bits.  Hence
  \cref{def:pir-communication} is at most
  \[
    t\bigl(2k|R|+(k+1)|H|\bigr)
      \le \bigl(t(2|R|+|H|)+1\bigr)(k+1).
  \]
  The positive constant \(C=t(2|R|+|H|)+1\), independent of \(k,n\), proves
  \cref{def:has-pir-at-matching-vector-cost}. -/)
  (title := /-- Multiplicity interpolation yields a PIR construction -/)
  (latexEnv := "lemma")]
lemma multiplicity_interpolation_gives_pir_cost
    {F : Type u} [Field F] {m p t : ℕ} [CharP F p]
    (hm : 0 < m) (hp : p.Prime)
    (hinterpolation :
      has_canonical_multiplicity_interpolation (F := F) m p t) :
    has_pir_at_matching_vector_cost t (m * p) := by
  classical
  have hM : 0 < m * p := Nat.mul_pos hm hp.pos
  letI : NeZero (m * p) := ⟨Nat.ne_of_gt hM⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  rcases hinterpolation with ⟨B, hBt, hB⟩
  have hBne : B.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst B
    have hone :
        polynomial_supported_on_residues
          (m * p) (canonical_set (m * p)) (1 : Polynomial F) := by
      intro i hi
      by_cases hi0 : i = 0
      · subst i
        simp [canonical_set, hM]
      · simp [Polynomial.coeff_one, hi0] at hi
    have hc := hB.2 (0 : Polynomial F) 1
      (by simp [polynomial_supported_on_residues]) hone (by simp)
    simpa using hc
  have ht : 0 < t :=
    lt_of_lt_of_le (Finset.card_pos.mpr hBne) hBt
  let R := rootsOfUnity (m * p) F
  letI : Fintype R := Fintype.ofFinite R
  let H := R → ZMod p
  let rootOfB : B → R := fun b =>
    ⟨Units.mk0 b.1 (by
        intro hb0
        have hbpow := hB.1 b b.property
        rw [hb0, zero_pow (Nat.ne_of_gt hM)] at hbpow
        exact zero_ne_one hbpow),
      by
        apply Units.ext
        simpa using hB.1 b b.property⟩
  let serverOfB : B ↪ Fin t :=
    (B.equivFin.toEmbedding).trans
      ⟨Fin.castLE hBt, Fin.castLE_injective hBt⟩
  let bzero : B := ⟨hBne.choose, hBne.choose_spec⟩
  let point : Fin t → B := fun s =>
    if hs : s.val < B.card then B.equivFin.symm ⟨s.val, hs⟩ else bzero
  have point_server (b : B) : point (serverOfB b) = b := by
    simp [point, serverOfB]
  refine ⟨t * (2 * Fintype.card R + Fintype.card H) + 1, by omega, ?_⟩
  intro k n family
  let shift (i : Fin n) (b : B) : (Fin k → ↥R) ≃ (Fin k → ↥R) :=
    { toFun := fun z a => z a * rootOfB b ^ (family.left i a).val
      invFun := fun z a =>
        z a * (rootOfB b ^ (family.left i a).val)⁻¹
      left_inv := by
        intro z
        funext a
        simp
      right_inv := by
        intro z
        funext a
        simp }
  let queries (i : Fin n) (z : Fin k → ↥R) (s : Fin t) : Fin k → ↥R :=
    shift i (point s) z
  let monomial (q : Fin k → ↥R) (l : Fin n) : ↥R :=
    ∏ a : Fin k, q a ^ (family.right l a).val
  let dot (i l : Fin n) : ZMod (m * p) :=
    ∑ a : Fin k, family.left i a * family.right l a
  let hist0 (database : Fin n → Bool) (q : Fin k → ↥R) : H := fun x =>
    ∑ l : Fin n,
      if database l then if monomial q l = x then 1 else 0 else 0
  let histD (database : Fin n → Bool) (q : Fin k → ↥R)
      (a : Fin k) : H := fun x =>
    ∑ l : Fin n,
      if database l then
        if monomial q l = x then
          ((family.right l a).val : ZMod p)
        else 0
      else 0
  let response (database : Fin n → Bool) (q : Fin k → ↥R) :
      Fin (k + 1) → H :=
    Fin.cases (hist0 database q) (histD database q)
  let decode (h : H) : F :=
    ∑ x : ↥R, (ZMod.castHom (dvd_refl p) F) (h x) * ((x.1 : F))
  let poly (database : Fin n → Bool) (i : Fin n) (z : Fin k → ↥R) :
      Polynomial F :=
    ∑ l : Fin n,
      if database l then
        Polynomial.monomial (dot i l).val ((monomial z l).1 : F)
      else 0
  have monomial_shift (i l : Fin n) (b : B) (z : Fin k → ↥R) :
      monomial (shift i b z) l =
        monomial z l * rootOfB b ^ (dot i l).val := by
    simp only [monomial, shift, Equiv.coe_fn_mk, mul_pow]
    rw [Finset.prod_mul_distrib]
    congr 1
    simp_rw [← pow_mul]
    calc
      ∏ a : Fin k,
          rootOfB b ^
            ((family.left i a).val * (family.right l a).val) =
          rootOfB b ^
            (∑ a : Fin k,
              (family.left i a).val * (family.right l a).val) := by
        simpa using Finset.prod_pow_eq_pow_sum Finset.univ
          (fun a : Fin k =>
            (family.left i a).val * (family.right l a).val) (rootOfB b)
      _ = rootOfB b ^ (dot i l).val := by
        apply pow_eq_pow_of_modEq
        · apply (ZMod.natCast_eq_natCast_iff _ _ (m * p)).mp
          simp [dot]
        · apply Subtype.ext
          apply Units.ext
          simpa [rootOfB] using hB.1 b b.property
  have supported_monomial (e : ZMod (m * p)) (c : F)
      (he : e ∈ canonical_set (m * p)) :
      polynomial_supported_on_residues (m * p) (canonical_set (m * p))
        (Polynomial.monomial e.val c) := by
    intro j hj
    have hj' := Polynomial.support_monomial_subset e.val c hj
    simp only [Finset.mem_singleton] at hj'
    subst j
    exact ⟨ZMod.val_lt _, by simpa using he⟩
  have supported_add (P Q : Polynomial F)
      (hP :
        polynomial_supported_on_residues (m * p) (canonical_set (m * p)) P)
      (hQ :
        polynomial_supported_on_residues (m * p) (canonical_set (m * p)) Q) :
      polynomial_supported_on_residues
        (m * p) (canonical_set (m * p)) (P + Q) := by
    intro e he
    have heu := Polynomial.support_add (p := P) (q := Q) he
    rw [Finset.mem_union] at heu
    exact heu.elim (hP e) (hQ e)
  have supported_sum {ι : Type} (s : Finset ι) (f : ι → Polynomial F)
      (hf : ∀ x ∈ s, polynomial_supported_on_residues
        (m * p) (canonical_set (m * p)) (f x)) :
      polynomial_supported_on_residues
        (m * p) (canonical_set (m * p)) (∑ x ∈ s, f x) := by
    induction s using Finset.induction_on with
    | empty => simp [polynomial_supported_on_residues]
    | @insert x s hxs ih =>
        rw [Finset.sum_insert hxs]
        exact supported_add _ _ (hf x (by simp)) (ih (by aesop))
  have coeff_sum {ι : Type} (s : Finset ι) (f : ι → Polynomial F) (e : ℕ) :
      (∑ x ∈ s, f x).coeff e = ∑ x ∈ s, (f x).coeff e := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert x s hxs ih =>
        simp [Finset.sum_insert, hxs, ih, Polynomial.coeff_add]
  have eval_sum {ι : Type} (s : Finset ι) (f : ι → Polynomial F) (x : F) :
      Polynomial.eval x (∑ a ∈ s, f a) =
        ∑ a ∈ s, Polynomial.eval x (f a) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s has ih =>
        simp [Finset.sum_insert, has, ih]
  have poly_supported (database : Fin n → Bool) (i : Fin n)
      (z : Fin k → ↥R) :
      polynomial_supported_on_residues
        (m * p) (canonical_set (m * p)) (poly database i z) := by
    apply supported_sum Finset.univ
    intro l hl
    by_cases hdl : database l
    · simp only [hdl, Bool.true_eq, if_true]
      apply supported_monomial
      by_cases hil : i = l
      · subst l
        simp [dot, family.diagonal, canonical_set]
      · exact (family.offDiagonal i l hil).1
    · simp [hdl, polynomial_supported_on_residues]
  have decode_hist0 (database : Fin n → Bool) (q : Fin k → ↥R) :
      decode (hist0 database q) =
        ∑ l : Fin n,
          if database l then ((monomial q l).1 : F) else 0 := by
    simp only [decode, hist0]
    simp_rw [map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hdl : database l
    · simp [hdl]
    · simp [hdl]
  have decode_histD (database : Fin n → Bool) (q : Fin k → ↥R)
      (a : Fin k) :
      decode (histD database q a) =
        ∑ l : Fin n,
          if database l then
            (ZMod.castHom (dvd_refl p) F)
                ((family.right l a).val : ZMod p) *
              ((monomial q l).1 : F)
          else 0 := by
    simp only [decode, histD]
    simp_rw [map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hdl : database l
    · simp only [hdl, Bool.true_eq, if_true]
      rw [Finset.sum_eq_single (monomial q l)]
      · simp
      · intro x hx hxl
        simp [hxl.symm]
      · simp
    · simp [hdl]
  have poly_coeff_zero (database : Fin n → Bool) (i : Fin n)
      (z : Fin k → ↥R) :
      (poly database i z).coeff 0 =
        if database i then ((monomial z i).1 : F) else 0 := by
    change
      (∑ l : Fin n,
        if database l then
          Polynomial.monomial (dot i l).val ((monomial z l).1 : F)
        else 0).coeff 0 = _
    have hcoeff := coeff_sum Finset.univ
      (fun l : Fin n =>
        if database l then
          Polynomial.monomial (dot i l).val ((monomial z l).1 : F)
        else 0) 0
    rw [hcoeff, Finset.sum_eq_single i]
    · by_cases hdi : database i <;>
        simp [hdi, dot, family.diagonal]
    · intro l hl hli
      have hoff := (family.offDiagonal i l (Ne.symm hli)).2
      have hval : (dot i l).val ≠ 0 := by
        intro hv
        apply hoff
        change dot i l = 0
        rw [← ZMod.natCast_zmod_val (dot i l), hv]
        simp
      by_cases hdl : database l <;>
        simp [hdl, Polynomial.coeff_monomial, hval]
    · simp_all
  have dot_cast (i l : Fin n) :
      ((dot i l).val : F) =
        ∑ a : Fin k,
          ((family.left i a).val : F) *
            ((family.right l a).val : F) := by
    let N := ∑ a : Fin k,
      (family.left i a).val * (family.right l a).val
    have hmodM : (dot i l).val ≡ N [MOD m * p] := by
      apply (ZMod.natCast_eq_natCast_iff _ _ (m * p)).mp
      simp [dot, N]
    calc
      ((dot i l).val : F) = (N : F) :=
        (CharP.natCast_eq_natCast F p).2
          (hmodM.of_dvd (by exact dvd_mul_left p m))
      _ = _ := by simp [N]
  have derivative_algebra (database : Fin n → Bool) (i : Fin n)
      (z : Fin k → ↥R) (b : B) :
      (b.1 : F)⁻¹ *
          (∑ a : Fin k, ((family.left i a).val : F) *
            decode (histD database (shift i b z) a)) =
        ∑ l : Fin n, if database l then
          ((dot i l).val : F) * ((monomial z l).1 : F) *
            (b.1 : F) ^ ((dot i l).val - 1)
        else 0 := by
    simp_rw [decode_histD, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hdl : database l
    · simp only [hdl, Bool.true_eq, if_true]
      calc
        (∑ x : Fin k,
          (b.1 : F)⁻¹ * (((family.left i x).val : F) *
            ((ZMod.castHom (dvd_refl p) F)
                ((family.right l x).val : ZMod p) *
              ((monomial (shift i b z) l).1 : F)))) =
            (b.1 : F)⁻¹ *
              (∑ x : Fin k, ((family.left i x).val : F) *
                ((family.right l x).val : F)) *
              ((monomial (shift i b z) l).1 : F) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x hx
          rw [map_natCast]
          ring
        _ = _ := by
          rw [← dot_cast]
          have hshift := congrArg (fun x : ↥R => (x.1 : F))
            (monomial_shift i l b z)
          rw [hshift]
          by_cases he : (dot i l).val = 0
          · rw [he]
            norm_num
          · have hb : (b.1 : F) ≠ 0 := by
              intro hb0
              have hbpow := hB.1 b b.property
              rw [hb0, zero_pow (Nat.ne_of_gt hM)] at hbpow
              exact zero_ne_one hbpow
            rw [show (dot i l).val = ((dot i l).val - 1) + 1 by omega]
            simp [pow_succ, rootOfB, hb]
            field_simp
    · simp [hdl]
  have eval_poly (database : Fin n → Bool) (i : Fin n)
      (z : Fin k → ↥R) (b : B) :
      Polynomial.eval b.1 (poly database i z) =
        decode (hist0 database (shift i b z)) := by
    rw [decode_hist0]
    change Polynomial.eval b.1
      (∑ l : Fin n, if database l then
        Polynomial.monomial (dot i l).val ((monomial z l).1 : F) else 0) = _
    have heval := eval_sum Finset.univ
      (fun l : Fin n => if database l then
        Polynomial.monomial (dot i l).val ((monomial z l).1 : F) else 0) b.1
    rw [heval]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hdl : database l
    · simp only [hdl, Bool.true_eq, if_true, Polynomial.eval_monomial]
      rw [monomial_shift]
      change
        ((monomial z l).1 : F) * b.1 ^ (dot i l).val =
          ((monomial z l).1 : F) * b.1 ^ (dot i l).val
      rfl
    · simp [hdl]
  have hasse_eval_sum {ι : Type} (s : Finset ι) (f : ι → Polynomial F)
      (j : ℕ) (x : F) :
      Polynomial.eval x (Polynomial.hasseDeriv j (∑ a ∈ s, f a)) =
        ∑ a ∈ s, Polynomial.eval x (Polynomial.hasseDeriv j (f a)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s has ih =>
        simp [Finset.sum_insert, has, ih]
        exact eval_sum s (fun a => Polynomial.hasseDeriv j (f a)) x
  have derivative_poly (database : Fin n → Bool) (i : Fin n)
      (z : Fin k → ↥R) (b : B) :
      Polynomial.eval b.1 (Polynomial.hasseDeriv 1 (poly database i z)) =
        (b.1 : F)⁻¹ *
          (∑ a : Fin k, ((family.left i a).val : F) *
            decode (histD database (shift i b z) a)) := by
    rw [derivative_algebra]
    change Polynomial.eval b.1 (Polynomial.hasseDeriv 1
      (∑ l : Fin n, if database l then
        Polynomial.monomial (dot i l).val ((monomial z l).1 : F) else 0)) = _
    have hderiv := hasse_eval_sum Finset.univ
      (fun l : Fin n => if database l then
        Polynomial.monomial (dot i l).val ((monomial z l).1 : F) else 0) 1 b.1
    rw [hderiv]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hdl : database l
    · simp only [hdl, Bool.true_eq, if_true,
        Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial,
        Nat.choose_one_right]
    · simp [hdl]
  let reply (database : Fin n → Bool) (_server : Fin t)
      (q : Fin k → ↥R) := (q, response database q)
  let transcript (i : Fin n) (database : Fin n → Bool)
      (z : Fin k → ↥R) (server : Fin t) :=
    reply database server (queries i z server)
  have transcript_unique (i : Fin n) (database database' : Fin n → Bool)
      (z z' : Fin k → ↥R)
      (htranscript : transcript i database z = transcript i database' z') :
      database i = database' i := by
    have hquery := congrArg
      (fun answers => (answers (serverOfB bzero)).1) htranscript
    have hzz' : z = z' := by
      apply (shift i bzero).injective
      simpa only [transcript, reply, queries, point_server] using hquery
    subst z'
    have hvalues : ∀ b : B,
        response database (shift i b z) =
          response database' (shift i b z) := by
      intro b
      have hresponse := congrArg
        (fun answers => (answers (serverOfB b)).2) htranscript
      simpa only [transcript, reply, queries, point_server] using hresponse
    have hcoeff : (poly database i z).coeff 0 =
        (poly database' i z).coeff 0 := by
      apply hB.2 (poly database i z) (poly database' i z)
          (poly_supported database i z) (poly_supported database' i z)
      intro b hb j hj
      let bB : B := ⟨b, hb⟩
      have hv := hvalues bB
      have hzero : decode (hist0 database (shift i bB z)) =
          decode (hist0 database' (shift i bB z)) := by
        have hz := congrArg (fun r => decode (r 0)) hv
        simpa only [response, Fin.cases_zero] using hz
      have hsucc : ∀ a : Fin k,
          decode (histD database (shift i bB z) a) =
            decode (histD database' (shift i bB z) a) := by
        intro a
        have ha := congrArg (fun r => decode (r a.succ)) hv
        simpa only [response, Fin.cases_succ] using ha
      have hjcases : j = 0 ∨ j = 1 := by omega
      rcases hjcases with rfl | rfl
      · rw [Polynomial.hasseDeriv_zero', Polynomial.hasseDeriv_zero']
        exact (eval_poly database i z bB).trans
          (hzero.trans (eval_poly database' i z bB).symm)
      · rw [derivative_poly database i z bB,
          derivative_poly database' i z bB]
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        rw [hsucc a]
    rw [poly_coeff_zero database i z,
      poly_coeff_zero database' i z] at hcoeff
    have hmonomial : ((monomial z i).1 : F) ≠ 0 := Units.ne_zero _
    by_cases hdi : database i
    · by_cases hdi' : database' i
      · simp [hdi, hdi']
      · exfalso
        apply hmonomial
        simpa [hdi, hdi'] using hcoeff
    · by_cases hdi' : database' i
      · exfalso
        apply hmonomial
        simpa [hdi, hdi'] using hcoeff.symm
      · simp [hdi, hdi']
  let reconstruct (i : Fin n)
      (answers : Fin t → (Fin k → ↥R) × (Fin (k + 1) → H)) : Bool :=
    if h : ∃ database : Fin n → Bool, ∃ z : Fin k → ↥R,
        transcript i database z = answers then h.choose i else false
  have reconstruct_transcript (i : Fin n) (database : Fin n → Bool)
      (z : Fin k → ↥R) :
      reconstruct i (transcript i database z) = database i := by
    unfold reconstruct
    split
    · rename_i h
      exact transcript_unique i h.choose database h.choose_spec.choose z
        h.choose_spec.choose_spec
    · rename_i h
      exact (h ⟨database, z, rfl⟩).elim
  let random : PMF (Fin k → ↥R) :=
    PMF.ofFintype
      (fun _ => (Fintype.card (Fin k → ↥R) : ENNReal)⁻¹)
      (by
        rw [Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
        have hc : (Fintype.card (Fin k → ↥R) : ENNReal) ≠ 0 := by
          exact_mod_cast Fintype.card_ne_zero
        exact ENNReal.mul_inv_cancel hc (by simp))
  have random_apply (z : Fin k → ↥R) :
      random z = (Fintype.card (Fin k → ↥R) : ENNReal)⁻¹ := by
    simp [random]
  have random_shift (i : Fin n) (b : B) :
      PMF.map (shift i b) random = random := by
    ext q
    rw [PMF.map_apply, random_apply,
      tsum_eq_single ((shift i b).symm q)]
    · rw [random_apply]
      simp
    · intro a ha
      rw [random_apply]
      split_ifs with h
      · exfalso
        apply ha
        simpa using congrArg (shift i b).symm h.symm
      · simp
  let eR := Fintype.equivFin R
  let encodeQuery : (Fin k → ↥R) ↪
      (Fin (k * Fintype.card R) → Bool) :=
    { toFun := fun q j =>
        let aj := (finProdFinEquiv :
          (Fin k × Fin (Fintype.card R)) ≃
            Fin (k * Fintype.card R)).symm j
        decide (q aj.1 = eR.symm aj.2)
      inj' := by
        intro q q' hq
        funext a
        let j : Fin (k * Fintype.card R) :=
          finProdFinEquiv (a, eR (q a))
        have hj := congrFun hq j
        have hqa : q' a = q a := by
          simpa [j] using hj
        exact hqa.symm }
  let eH := Fintype.equivFin H
  let encodeResponse : (Fin (k + 1) → H) ↪
      (Fin ((k + 1) * Fintype.card H) → Bool) :=
    { toFun := fun r j =>
        let ah := (finProdFinEquiv :
          (Fin (k + 1) × Fin (Fintype.card H)) ≃
            Fin ((k + 1) * Fintype.card H)).symm j
        decide (r ah.1 = eH.symm ah.2)
      inj' := by
        intro r r' hr
        funext a
        let j : Fin ((k + 1) * Fintype.card H) :=
          finProdFinEquiv (a, eH (r a))
        have hj := congrFun hr j
        have hra : r' a = r a := by
          simpa [j] using hj
        exact hra.symm }
  let encodeAnswer : ((Fin k → ↥R) × (Fin (k + 1) → H)) ↪
      (Fin (k * Fintype.card R +
        (k + 1) * Fintype.card H) → Bool) :=
    { toFun := fun answer =>
        Fin.addCases (encodeQuery answer.1) (encodeResponse answer.2)
      inj' := by
        intro answer answer' hanswer
        apply Prod.ext
        · apply encodeQuery.injective
          funext j
          have hj := congrFun hanswer
            (Fin.castAdd ((k + 1) * Fintype.card H) j)
          simpa using hj
        · apply encodeResponse.injective
          funext j
          have hj := congrFun hanswer
            (Fin.natAdd (k * Fintype.card R) j)
          simpa using hj }
  let qEquiv := Fintype.equivFin (Fin k → ↥R)
  let aEquiv := Fintype.equivFin
    ((Fin k → ↥R) × (Fin (k + 1) → H))
  let scheme : one_round_pir_scheme t n :=
    { Query := Fin (Fintype.card (Fin k → ↥R))
      Answer := Fin (Fintype.card
        ((Fin k → ↥R) × (Fin (k + 1) → H)))
      queryBits := k * Fintype.card R
      answerBits := k * Fintype.card R +
        (k + 1) * Fintype.card H
      encodeQuery := qEquiv.symm.toEmbedding.trans encodeQuery
      encodeAnswer := aEquiv.symm.toEmbedding.trans encodeAnswer
      query := fun i => PMF.map
        (fun z server => qEquiv (queries i z server)) random
      answer := fun database server q =>
        aEquiv (reply database server (qEquiv.symm q))
      reconstruct := fun i answers =>
        reconstruct i (fun server => aEquiv.symm (answers server))
      correctness := by
        intro database index
        change PMF.map
          (fun qs => reconstruct index
            (fun server => aEquiv.symm
              (aEquiv (reply database server
                (qEquiv.symm (qs server))))))
          (PMF.map (fun z server =>
            qEquiv (queries index z server)) random) =
            PMF.pure (database index)
        simp only [Equiv.symm_apply_apply]
        rw [PMF.map_comp]
        have hfunction :
            ((fun qs => reconstruct index
                (fun server => reply database server
                  (qEquiv.symm (qs server)))) ∘
              (fun z server => qEquiv (queries index z server))) =
            Function.const (Fin k → ↥R) (database index) := by
          funext z
          simp only [Function.comp_apply, Equiv.symm_apply_apply]
          exact reconstruct_transcript index database z
        rw [hfunction]
        exact PMF.map_const random (database index)
      privacy := by
        intro server i j
        change PMF.map (fun qs => qs server)
            (PMF.map (fun z server =>
              qEquiv (queries i z server)) random) =
          PMF.map (fun qs => qs server)
            (PMF.map (fun z server =>
              qEquiv (queries j z server)) random)
        rw [PMF.map_comp, PMF.map_comp]
        change PMF.map (qEquiv ∘ shift i (point server)) random =
          PMF.map (qEquiv ∘ shift j (point server)) random
        rw [← PMF.map_comp, random_shift,
          ← PMF.map_comp, random_shift] }
  refine ⟨scheme, ?_⟩
  simp only [pir_communication, scheme]
  nlinarith

@[blueprint "lem:matching-vector-rate-gives-target-communication"
  (statement := /-- Let \(m,p,t,r\) be natural numbers.  Suppose that there
  is a real constant \(c>0\) such that, for every sufficiently large
  dimension \(k\), there are a natural number \(N\) and a canonical
  matching-vector family modulo \(mp\), of dimension \(k\) and size \(N\),
  satisfying
  \[
    \exp\!\left(c\,\frac{(\log k)^{r+1}}
      {(\log\log k)^r}\right)\le N.
  \]
  Suppose also that there is a positive natural number \(C\) such that every
  canonical matching-vector family modulo \(mp\), of dimension \(k\) and
  size \(N\), yields a one-round \(t\)-server PIR scheme for an \(N\)-bit
  database with communication at most \(C(k+1)\).  Then there exist a
  one-round \(t\)-server PIR scheme \(\Pi_n\) for every natural number \(n\)
  and a natural number \(d\) such that, as \(n\to\infty\),
  \[
    \log\!\bigl(\operatorname{Comm}(\Pi_n)\bigr)
      =O\!\left((\log n)^{1/(r+1)}(\log\log n)^d\right).
  \] -/)
  (proof := /-- Unpack the constants \(c>0\) and \(C>0\) in
  \cref{def:has-large-canonical-matching-vector-families} and
  \cref{def:has-pir-at-matching-vector-cost}.  The unique canonical
  matching-vector family of size one and dimension zero gives a one-bit PIR
  scheme.  Hence \(t>0\): if \(t=0\), the empty response tuple would be the
  same for the all-false and all-true one-bit databases, contradicting the
  correctness field of \cref{def:one-round-pir-scheme}.  This positivity also
  gives, for every \(n\), a fallback scheme whose query is trivial and in
  which every server returns the entire database.

  Put
  \[
    q_n=(\log n)^{1/(r+1)}\log\log n,
    \qquad k_n=\left\lceil\exp(q_n)\right\rceil.
  \]
  Both \(q_n\) and \(k_n\) tend to infinity.  The ceiling inequalities and
  monotonicity of the logarithm give, eventually,
  \[
    q_n\le\log k_n,
    \qquad \log\log k_n\le 3\log\log n.
  \]
  Moreover,
  \[
    q_n^{r+1}=\log n\,(\log\log n)^{r+1}.
  \]
  Since \(c\log\log n\ge 3^r\) eventually, these three relations imply
  \[
    \log n\le
      c\,\frac{(\log k_n)^{r+1}}{(\log\log k_n)^r}.
  \]
  Thus the family supplied by
  \cref{def:has-large-canonical-matching-vector-families} in dimension
  \(k_n\) has size at least \(n\).  Restrict its two indexed vector families
  along \(\operatorname{Fin}(n)\hookrightarrow\operatorname{Fin}(N)\); the
  diagonal and off-diagonal conditions in
  \cref{def:canonical-matching-vector-family} are preserved.  Applying
  \cref{def:has-pir-at-matching-vector-cost} produces a scheme \(\Pi_n\) with
  \(\operatorname{Comm}(\Pi_n)\le C(k_n+1)\).  Use this scheme whenever it is
  available and the fallback scheme otherwise; the former case holds for
  all sufficiently large \(n\).

  Finally, \(k_n+1\le3\exp(q_n)\) eventually, so
  \[
    \log\!\bigl(\operatorname{Comm}(\Pi_n)\bigr)
      \le \log(3C)+q_n
      \le (\log(3C)+1)q_n.
  \]
  By \cref{def:pir-communication} and
  \cref{def:has-target-communication-rate}, this is the required Big-O bound
  with \(d=1\). -/)
  (title := /-- Matching-vector growth implies the target rate -/)
  (latexEnv := "lemma")]
lemma matching_vector_rate_gives_target_communication
    {m p t r : ℕ}
    (hmvf :
      has_large_canonical_matching_vector_families (m * p) (r + 1))
    (hconstruction : has_pir_at_matching_vector_cost t (m * p)) :
    has_target_communication_rate t r := by
  classical
  rcases hmvf with ⟨c, hc, hfamilies⟩
  rcases hconstruction with ⟨C, hC, hconstruct⟩
  let singletonFamily : canonical_matching_vector_family (m * p) 0 1 :=
    { left := fun _ i => Fin.elim0 i
      right := fun _ i => Fin.elim0 i
      diagonal := by
        intro i
        simp
      offDiagonal := by
        intro i j hij
        exact (hij (Subsingleton.elim i j)).elim }
  obtain ⟨schemeOne, hschemeOne⟩ := hconstruct singletonFamily
  have ht : 0 < t := by
    by_contra ht'
    have ht0 : t = 0 := Nat.eq_zero_of_not_pos ht'
    subst t
    have hfalse := schemeOne.correctness (fun _ => false) (0 : Fin 1)
    have htrue := schemeOne.correctness (fun _ => true) (0 : Fin 1)
    have hmaps :
        (fun queries : Fin 0 → schemeOne.Query =>
          schemeOne.reconstruct 0
            (fun server => schemeOne.answer (fun _ => false) server (queries server))) =
        (fun queries : Fin 0 → schemeOne.Query =>
          schemeOne.reconstruct 0
            (fun server => schemeOne.answer (fun _ => true) server (queries server))) := by
      funext queries
      congr 1
      funext server
      exact Fin.elim0 server
    rw [hmaps] at hfalse
    have hpure : PMF.pure false = PMF.pure true := hfalse.symm.trans htrue
    have happly := congrArg (fun q : PMF Bool => q false) hpure
    simpa using happly
  let trivialScheme (n : ℕ) : one_round_pir_scheme t n :=
    { Query := PUnit
      Answer := Fin n → Bool
      queryBits := 0
      answerBits := n
      encodeQuery :=
        { toFun := fun _ i => Fin.elim0 i
          inj' := fun _ _ _ => Subsingleton.elim _ _ }
      encodeAnswer := Function.Embedding.refl _
      query := fun _ => PMF.pure (fun _ => PUnit.unit)
      answer := fun database _ _ => database
      reconstruct := fun index answers => answers ⟨0, ht⟩ index
      correctness := by
        intro database index
        rw [PMF.pure_map]
      privacy := by
        intro server i j
        simp }
  let rate : ℕ → ℝ := fun n =>
    Real.rpow (Real.log (n : ℝ)) (1 / ((r + 1 : ℕ) : ℝ)) *
      Real.log (Real.log (n : ℝ))
  let dimension : ℕ → ℕ := fun n => ⌈Real.exp (rate n)⌉₊
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hexponent : 0 < (1 / ((r + 1 : ℕ) : ℝ)) := by positivity
  have hrate : Tendsto rate atTop atTop := by
    apply Tendsto.atTop_mul_atTop₀
    · exact (_root_.tendsto_rpow_atTop hexponent).comp hlog
    · exact hloglog
  have hdimension : Tendsto dimension atTop atTop := by
    exact tendsto_nat_ceil_atTop.comp (Real.tendsto_exp_atTop.comp hrate)
  have hfamiliesAt :
      ∀ᶠ n : ℕ in atTop,
        ∃ N : ℕ,
          Nonempty (canonical_matching_vector_family (m * p) (dimension n) N) ∧
            Real.exp
                (c * (Real.log (dimension n : ℝ)) ^ (r + 1) /
                  (Real.log (Real.log (dimension n : ℝ))) ^ ((r + 1) - 1)) ≤
              (N : ℝ) := by
    exact hdimension.eventually hfamilies
  have hrate_le_log_dimension :
      ∀ᶠ n : ℕ in atTop, rate n ≤ Real.log (dimension n : ℝ) := by
    filter_upwards with n
    have hceil : Real.exp (rate n) ≤ (dimension n : ℝ) := by
      exact Nat.le_ceil (Real.exp (rate n))
    simpa using Real.log_le_log (Real.exp_pos (rate n)) hceil
  have hlog_log_dimension_le :
      ∀ᶠ n : ℕ in atTop,
        Real.log (Real.log (dimension n : ℝ)) ≤
          3 * Real.log (Real.log (n : ℝ)) := by
    have hexponent_le_one : (1 / ((r + 1 : ℕ) : ℝ)) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.succ_ne_zero r)
    filter_upwards [hrate.eventually_ge_atTop 1, hlog.eventually_ge_atTop 2,
        hloglog.eventually_ge_atTop (Real.log 2), hrate_le_log_dimension] with n hn hln hlln hbelow
    have hrate_pos : 0 < rate n := lt_of_lt_of_le zero_lt_one hn
    have hexp_ge_one : 1 ≤ Real.exp (rate n) := Real.one_le_exp hrate_pos.le
    have hceil_lt : (dimension n : ℝ) < Real.exp (rate n) + 1 := by
      exact Nat.ceil_lt_add_one (Real.exp_pos (rate n)).le
    have hdim_le : (dimension n : ℝ) ≤ 2 * Real.exp (rate n) := by
      linarith
    have hlogdim_le : Real.log (dimension n : ℝ) ≤ rate n + Real.log 2 := by
      calc
        Real.log (dimension n : ℝ) ≤ Real.log (2 * Real.exp (rate n)) :=
          Real.log_le_log (by positivity) hdim_le
        _ = rate n + Real.log 2 := by
          rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
          ring
    have hlogdim_pos : 0 < Real.log (dimension n : ℝ) :=
      lt_of_lt_of_le zero_lt_one (hn.trans hbelow)
    have hell_pos : 0 < Real.log (Real.log (n : ℝ)) :=
      (Real.log_pos one_lt_two).trans_le hlln
    have hlogn_one : 1 < Real.log (n : ℝ) := lt_of_lt_of_le one_lt_two hln
    have htwo_le_rate : Real.log 2 ≤ rate n := by
      apply hlln.trans
      dsimp [rate]
      have hpow_ge_one :
          1 ≤ Real.rpow (Real.log (n : ℝ)) (1 / ((r + 1 : ℕ) : ℝ)) := by
        apply Real.one_le_rpow
        exact hlogn_one.le
        exact hexponent.le
      exact le_mul_of_one_le_left hell_pos.le hpow_ge_one
    have hloglogdim_le :
        Real.log (Real.log (dimension n : ℝ)) ≤ Real.log (2 * rate n) := by
      apply Real.log_le_log hlogdim_pos
      linarith
    have hlog_rate :
        Real.log (rate n) =
          (1 / ((r + 1 : ℕ) : ℝ)) * Real.log (Real.log (n : ℝ)) +
            Real.log (Real.log (Real.log (n : ℝ))) := by
      dsimp [rate]
      rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (lt_trans zero_lt_one hlogn_one) _))
          (ne_of_gt hell_pos), Real.log_rpow (lt_trans zero_lt_one hlogn_one)]
    calc
      Real.log (Real.log (dimension n : ℝ)) ≤ Real.log (2 * rate n) := hloglogdim_le
      _ = Real.log 2 + Real.log (rate n) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hrate_pos)]
      _ ≤ 3 * Real.log (Real.log (n : ℝ)) := by
        rw [hlog_rate]
        have hthird :
            Real.log (Real.log (Real.log (n : ℝ))) ≤
              Real.log (Real.log (n : ℝ)) :=
          Real.log_le_self hell_pos.le
        nlinarith
  have hrate_pow :
      ∀ᶠ n : ℕ in atTop,
        (rate n) ^ (r + 1) =
          Real.log (n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ (r + 1) := by
    filter_upwards [hlog.eventually_ge_atTop 0] with n hn
    dsimp [rate]
    rw [mul_pow, one_div, Real.rpow_inv_natCast_pow hn (Nat.succ_ne_zero r)]
  have hgrowth :
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ≤
          Real.exp
            (c * (Real.log (dimension n : ℝ)) ^ (r + 1) /
              (Real.log (Real.log (dimension n : ℝ))) ^ ((r + 1) - 1)) := by
    filter_upwards [hlog.eventually_ge_atTop 2, hrate.eventually_ge_atTop 2,
        hloglog.eventually_ge_atTop 1,
        hloglog.eventually_ge_atTop (((3 : ℝ) ^ r) / c),
        hrate_le_log_dimension, hlog_log_dimension_le, hrate_pow] with
        n hln hnrate hlln hcoefficient hbelow habove hpower
    have hn0 : n ≠ 0 := by
      intro hn
      subst n
      norm_num at hln
    have hlogn_pos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le zero_lt_two hln
    have hloglogn_pos : 0 < Real.log (Real.log (n : ℝ)) :=
      lt_of_lt_of_le zero_lt_one hlln
    have hrate_pos : 0 < rate n := by
      dsimp [rate]
      positivity
    have hlogdim_pos : 0 < Real.log (dimension n : ℝ) := hrate_pos.trans_le hbelow
    have hloglogdim_pos : 0 < Real.log (Real.log (dimension n : ℝ)) :=
      Real.log_pos (lt_of_lt_of_le one_lt_two (hnrate.trans hbelow))
    have hdenom :
        (Real.log (Real.log (dimension n : ℝ))) ^ r ≤
          (3 * Real.log (Real.log (n : ℝ))) ^ r := by
      gcongr
    have hnumerator :
        (rate n) ^ (r + 1) ≤ (Real.log (dimension n : ℝ)) ^ (r + 1) := by
      gcongr
    have hthree : (3 : ℝ) ^ r ≤ c * Real.log (Real.log (n : ℝ)) := by
      simpa [mul_comm] using (div_le_iff₀ hc).mp hcoefficient
    have hlog_bound :
        Real.log (n : ℝ) ≤
          c * (Real.log (dimension n : ℝ)) ^ (r + 1) /
            (Real.log (Real.log (dimension n : ℝ))) ^ r := by
      rw [le_div_iff₀ (pow_pos hloglogdim_pos r)]
      calc
        Real.log (n : ℝ) * (Real.log (Real.log (dimension n : ℝ))) ^ r ≤
            Real.log (n : ℝ) * (3 * Real.log (Real.log (n : ℝ))) ^ r := by
          gcongr
        _ = Real.log (n : ℝ) * (3 : ℝ) ^ r *
              (Real.log (Real.log (n : ℝ))) ^ r := by
          rw [mul_pow]
          ring
        _ ≤ c * Real.log (n : ℝ) *
              (Real.log (Real.log (n : ℝ))) ^ (r + 1) := by
          rw [pow_succ]
          calc
            Real.log (n : ℝ) * 3 ^ r *
                  Real.log (Real.log (n : ℝ)) ^ r =
                (Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) ^ r) * 3 ^ r := by
              ring
            _ ≤ (Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) ^ r) *
                  (c * Real.log (Real.log (n : ℝ))) :=
              mul_le_mul_of_nonneg_left hthree
                (mul_nonneg hlogn_pos.le (pow_nonneg hloglogn_pos.le r))
            _ = c * Real.log (n : ℝ) *
                  (Real.log (Real.log (n : ℝ)) ^ r * Real.log (Real.log (n : ℝ))) := by
              ring
        _ = c * (rate n) ^ (r + 1) := by rw [hpower]; ring
        _ ≤ c * (Real.log (dimension n : ℝ)) ^ (r + 1) := by
          gcongr
    simpa only [Nat.add_sub_cancel] using
      (calc
        (n : ℝ) = Real.exp (Real.log (n : ℝ)) :=
          (Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hn0)).symm
        _ ≤ Real.exp
              (c * (Real.log (dimension n : ℝ)) ^ (r + 1) /
                (Real.log (Real.log (dimension n : ℝ))) ^ r) :=
          Real.exp_le_exp.mpr hlog_bound)
  have restrictFamily :
      ∀ {k N n : ℕ}, n ≤ N →
        canonical_matching_vector_family (m * p) k N →
          canonical_matching_vector_family (m * p) k n := by
    intro k N n hn family
    exact
      { left := fun i => family.left (Fin.castLE hn i)
        right := fun i => family.right (Fin.castLE hn i)
        diagonal := fun i => family.diagonal (Fin.castLE hn i)
        offDiagonal := by
          intro i j hij
          apply family.offDiagonal
          intro heq
          apply hij
          exact Fin.castLE_injective hn heq }
  have hefficient :
      ∀ᶠ n : ℕ in atTop,
        ∃ scheme : one_round_pir_scheme t n,
          pir_communication scheme ≤ C * (dimension n + 1) := by
    filter_upwards [hfamiliesAt, hgrowth] with n hfamily hgrow
    rcases hfamily with ⟨N, ⟨family⟩, hsize⟩
    have hnN : n ≤ N := by
      exact_mod_cast hgrow.trans hsize
    exact hconstruct (restrictFamily hnN family)
  let schemes : (n : ℕ) → one_round_pir_scheme t n := fun n =>
    if h : ∃ scheme : one_round_pir_scheme t n,
        pir_communication scheme ≤ C * (dimension n + 1) then
      Classical.choose h
    else
      trivialScheme n
  have hschemes :
      ∀ᶠ n : ℕ in atTop,
        pir_communication (schemes n) ≤ C * (dimension n + 1) := by
    filter_upwards [hefficient] with n hn
    dsimp [schemes]
    rw [dif_pos hn]
    exact Classical.choose_spec hn
  refine ⟨schemes, 1, ?_⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨Real.log ((3 * C : ℕ) : ℝ) + 1, ?_⟩
  filter_upwards [hschemes, hrate.eventually_ge_atTop 1] with n hscheme hn
  have hrate_nonneg : 0 ≤ rate n := zero_le_one.trans hn
  have hexp_ge_one : 1 ≤ Real.exp (rate n) := Real.one_le_exp hrate_nonneg
  have hceil_lt : (dimension n : ℝ) < Real.exp (rate n) + 1 := by
    exact Nat.ceil_lt_add_one (Real.exp_pos (rate n)).le
  have hdimension_bound : ((dimension n + 1 : ℕ) : ℝ) ≤ 3 * Real.exp (rate n) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hcommunication_bound :
      (pir_communication (schemes n) : ℝ) ≤
        ((3 * C : ℕ) : ℝ) * Real.exp (rate n) := by
    calc
      (pir_communication (schemes n) : ℝ) ≤ (C * (dimension n + 1) : ℕ) := by
        exact_mod_cast hscheme
      _ ≤ (C : ℝ) * (3 * Real.exp (rate n)) := by
        norm_num only [Nat.cast_mul]
        exact mul_le_mul_of_nonneg_left hdimension_bound (Nat.cast_nonneg C)
      _ = ((3 * C : ℕ) : ℝ) * Real.exp (rate n) := by
        norm_num
        ring
  have hlogcommunication :
      Real.log (pir_communication (schemes n) : ℝ) ≤
        Real.log ((3 * C : ℕ) : ℝ) + rate n := by
    by_cases hz : pir_communication (schemes n) = 0
    · have hlogC_nonneg : 0 ≤ Real.log ((3 * C : ℕ) : ℝ) :=
        Real.log_natCast_nonneg _
      rw [hz]
      simp only [Nat.cast_zero, Real.log_zero]
      exact add_nonneg hlogC_nonneg hrate_nonneg
    · calc
        Real.log (pir_communication (schemes n) : ℝ) ≤
            Real.log (((3 * C : ℕ) : ℝ) * Real.exp (rate n)) :=
          Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) hcommunication_bound
        _ = Real.log ((3 * C : ℕ) : ℝ) + rate n := by
          rw [Real.log_mul, Real.log_exp]
          · exact_mod_cast (show 3 * C ≠ 0 from Nat.ne_of_gt (Nat.mul_pos (by omega) hC))
          · exact Real.exp_ne_zero _
  have htarget_eq :
      Real.rpow (Real.log (n : ℝ)) (1 / ((r + 1 : ℕ) : ℝ)) *
          (Real.log (Real.log (n : ℝ))) ^ 1 = rate n := by
    simp [rate]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, htarget_eq,
    abs_of_nonneg (Real.log_natCast_nonneg _), abs_of_nonneg hrate_nonneg]
  calc
    Real.log (pir_communication (schemes n) : ℝ) ≤
        Real.log ((3 * C : ℕ) : ℝ) + rate n := hlogcommunication
    _ ≤ (Real.log ((3 * C : ℕ) : ℝ) + 1) * rate n := by
      have hlogC_nonneg : 0 ≤ Real.log ((3 * C : ℕ) : ℝ) :=
        Real.log_natCast_nonneg _
      nlinarith

@[blueprint "lem:sparse-decoder-main-construction"
  (statement := /-- Let \(F\) be a field, and let \(m,r,p,t\) be natural
  numbers.  Assume that \(F\) has characteristic \(p\), that \(m>0\) has
  exactly \(r\) distinct prime factors, that \(p\) is prime and does not
  divide \(m\), and that the canonical set modulo \(m\) has a decoding
  polynomial over \(F\) with support of cardinality at most \(t\).  Then
  there exist a family \((\Pi_n)_{n\in\mathbb N}\) of one-round
  \(t\)-server PIR schemes for \(n\)-bit databases, with perfect correctness
  and information-theoretic privacy, and a natural number \(d\) such that
  \[
    \log\!\bigl(\operatorname{Comm}(\Pi_n)\bigr)
      =O\!\left((\log n)^{1/(r+1)}(\log\log n)^d\right)
  \]
  as \(n\to\infty\). -/)
  (proof := /-- By
  \cref{lem:sparse-decoder-yields-small-zero-interpolation}, the sparse
  decoding polynomial supplies a zero-interpolating set of size at most
  \(t\).  By
  \cref{lem:canonical-zero-interpolation-lifts-to-multiplicity}, that set
  gives multiplicity-two interpolation modulo \(mp\).  The required
  rank-\((r+1)\) matching-vector input is the explicitly isolated
  \cref{lem:main-matching-vector-input-gap}.  Apply
  \cref{lem:multiplicity-interpolation-gives-pir-cost} to obtain protocols
  whose communication is linear in the matching-vector dimension, and then
  apply \cref{lem:matching-vector-rate-gives-target-communication} to obtain
  the asserted family and rate. -/)
  (title := /-- Sparse decoding polynomial gives the main PIR construction -/)
  (latexEnv := "lemma")]
lemma sparse_decoder_main_construction
    {F : Type u} [Field F] {m r p t : ℕ}
    [CharP F p]
    (hm : 0 < m)
    (hr : m.primeFactors.card = r)
    (hp : p.Prime)
    (hcoprime : ¬p ∣ m)
    (hdecoder : has_sparse_canonical_decoder (F := F) m t) :
    has_target_communication_rate t r := by
  exact matching_vector_rate_gives_target_communication
    (main_matching_vector_input_gap hm hr hp hcoprime)
    (multiplicity_interpolation_gives_pir_cost hm hp
      (canonical_zero_interpolation_lifts_to_multiplicity hp hcoprime
        (sparse_decoder_yields_small_zero_interpolation hm hdecoder)))

@[blueprint "thm:main"
  (statement := /-- Let \(m\) be a positive integer with exactly \(r\)
  distinct prime factors, let \(p\) be a prime not dividing \(m\), and let
  \(F\) be a field of characteristic \(p\).  Suppose that the canonical set
  \(S_m^*\subseteq\mathbb Z/m\mathbb Z\) has a decoding polynomial over \(F\)
  with sparsity at most \(t\).  Then there is a family of one-round
  \(t\)-server PIR schemes for \(n\)-bit databases with perfect correctness,
  information-theoretic privacy, and communication
  \[
    \exp\!\left(\widetilde O\!\left(
      (\log n)^{1/(r+1)}\right)\right).
  \] -/)
  (proof := /-- This is exactly
  \cref{lem:sparse-decoder-main-construction} applied to the stated
  positivity, prime-factor-count, characteristic, coprimality, and sparse
  decoding hypotheses. -/)
  (title := /-- Improved PIR scheme from a sparse canonical decoder -/)
  (latexEnv := "theorem")]
theorem main
    {F : Type u} [Field F] {m r p t : ℕ}
    [CharP F p]
    (hm : 0 < m)
    (hr : m.primeFactors.card = r)
    (hp : p.Prime)
    (hcoprime : ¬p ∣ m)
    (hdecoder : has_sparse_canonical_decoder (F := F) m t) :
    has_target_communication_rate t r := by
  exact sparse_decoder_main_construction hm hr hp hcoprime hdecoder

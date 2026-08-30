import Architect
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Nat.Dist
import Mathlib.Logic.Equiv.Multiset

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

@[blueprint "def:valid-popular-sums-input"
  (statement := /-- For an integer \(N\), a multiset \(A\) is an admissible input if its total cardinality, counted with multiplicity, is at most \(N\), and every element of \(A\) belongs to \([N]=\{0,\ldots,N-1\}\). -/)
  (title := /-- Admissible multiset input -/)
  (latexEnv := "definition")]
def valid_popular_sums_input (N : ℕ) (A : Multiset ℕ) : Prop :=
  A.card ≤ N ∧ ∀ a ∈ A, a < N

@[blueprint "def:multiset-convolution-coefficient"
  (statement := /-- Let \(A\) and \(B\) be multisets of nonnegative integers. For every \(k\in\mathbb N\), define
  \[
    (1_A\ast 1_B)(k)
      = \sum_{i=0}^{k} \operatorname{mult}_A(i)\,
        \operatorname{mult}_B(k-i).
  \]
  Thus this coefficient is the number of ordered pairs of occurrences \((a,b)\in A\times B\) satisfying \(a+b=k\). -/)
  (title := /-- Coefficients of multiset convolution -/)
  (latexEnv := "definition")]
def multiset_convolution_coefficient (A B : Multiset ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), A.count i * B.count (k - i)

@[blueprint "def:subpolynomial-overhead"
  (statement := /-- A function \(g\colon\mathbb N\to\mathbb N\) is subpolynomial if, for every positive integer \(d\), there exists \(N_0\) such that \(g(N)^d\leq N\) for every \(N\geq N_0\). This is the power-free formulation of \(g(N)=N^{o(1)}\). -/)
  (title := /-- Subpolynomial overhead -/)
  (latexEnv := "definition")]
def subpolynomial_overhead (g : ℕ → ℕ) : Prop :=
  ∀ d : ℕ, 0 < d → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (g N) ^ d ≤ N

@[blueprint "def:deterministic-popular-sums-algorithm"
  (statement := /-- A deterministic popular-sums algorithm in the word-RAM cost model is specified by two functions on the same input \((N,A,B,\epsilon)\). The first returns a finitely supported vector \(f\colon\mathbb N\to_0\mathbb N\), and the second returns the number of word-RAM operations used to produce that vector. Since the output is a function of the input, the algorithm is deterministic. The cost counts the unit-cost word operations of the source model and does not include a separate binary serialization charge. -/)
  (title := /-- Deterministic popular-sums algorithm -/)
  (latexEnv := "definition")]
structure deterministic_popular_sums_algorithm where
  output : ℕ → Multiset ℕ → Multiset ℕ → ℝ → (ℕ →₀ ℕ)
  runningTime : ℕ → Multiset ℕ → Multiset ℕ → ℝ → ℕ

@[blueprint "def:deterministic-popular-sums-specification"
  (statement := /-- A deterministic popular-sums algorithm satisfies the required specification if there are absolute positive constants \(C_{\mathrm{time}}\) and \(C_{\mathrm{sp}}\), and a subpolynomial function \(g\), such that the following holds uniformly. For every \(N>0\), all multisets \(A,B\subseteq[N]\) of cardinality at most \(N\), and every \(\epsilon>0\), let \(f\) be the output of the algorithm on \((N,A,B,\epsilon)\). Its word-RAM running time is bounded by
  \[
    C_{\mathrm{time}}\bigl(\epsilon^{-1}|A|+|B|\bigr)g(N).
  \]
  The same output \(f\) has support of cardinality at most
  \[
    C_{\mathrm{sp}}\epsilon^{-1}|A|\log^2(N+2),
  \]
  and, for every \(k\in\mathbb N\),
  \[
    \bigl|f(k)-(1_A\ast1_B)(k)\bigr|\leq\epsilon|B|.
  \]
  The shift by \(2\) in the logarithm normalizes the sparsity bound at small universe sizes. -/)
  (title := /-- Sparse uniform approximation specification -/)
  (latexEnv := "definition")]
def deterministic_popular_sums_specification
    (algorithm : deterministic_popular_sums_algorithm) : Prop :=
  ∃ g : ℕ → ℕ,
    subpolynomial_overhead g ∧
      ∃ Ctime Csparsity : ℝ,
        0 < Ctime ∧
          0 < Csparsity ∧
            ∀ (N : ℕ) (A B : Multiset ℕ) (ε : ℝ),
              0 < N →
                valid_popular_sums_input N A →
                    valid_popular_sums_input N B →
                    0 < ε →
                      (algorithm.runningTime N A B ε : ℝ) ≤
                          Ctime *
                            ((ε⁻¹ * (A.card : ℝ) + (B.card : ℝ)) *
                              (g N : ℝ)) ∧
                        ((algorithm.output N A B ε).support.card : ℝ) ≤
                            Csparsity * ε⁻¹ * (A.card : ℝ) *
                              (Real.log ((N : ℝ) + 2)) ^ 2 ∧
                          ∀ k : ℕ,
                            (Nat.dist (algorithm.output N A B ε k)
                                (multiset_convolution_coefficient A B k) : ℝ) ≤
                              ε * (B.card : ℝ)

@[blueprint "thm:deterministic-popular-sums-approximation"
  (statement := /-- There exist a deterministic algorithm, a function
  \(g\colon\mathbb N\to\mathbb N\), and constants
  \(C_{\mathrm{time}},C_{\mathrm{sp}}>0\), all independent of the input, such
  that \(g\) is subpolynomial in the following sense: for every integer
  \(d>0\), there is an \(N_0\) for which \(g(N)^d\leq N\) whenever
  \(N\geq N_0\). For every integer \(N>0\), every pair of multisets
  \(A,B\subseteq\{0,\ldots,N-1\}\) of cardinality at most \(N\), and every
  real number \(\epsilon>0\), the algorithm returns a finitely supported
  function \(f\colon\mathbb N\to\mathbb N\) and has running time at most
  \[
    C_{\mathrm{time}}
      \bigl(\epsilon^{-1}|A|+|B|\bigr)g(N).
  \]
  Its output satisfies
  \[
    |\operatorname{supp}(f)|
      \leq C_{\mathrm{sp}}\epsilon^{-1}|A|\log^2(N+2)
  \]
  and, for every \(k\in\mathbb N\),
  \[
    \bigl|f(k)-(1_A\ast1_B)(k)\bigr|\leq\epsilon|B|.
  \] -/)
  (proof := /-- Set \(g(N)=1\) and
  \(C_{\mathrm{time}}=C_{\mathrm{sp}}=1\) in
  \cref{def:deterministic-popular-sums-specification}. The function \(g\) is
  subpolynomial by taking \(N_0=1\) for every positive exponent. For
  multisets \(A,B\), let \(S\) be the multiset obtained by mapping
  \((a,b)\mapsto a+b\) over their Cartesian product. An induction on \(A\),
  using the injectivity of \(b\mapsto a+b\), proves from
  \cref{def:multiset-convolution-coefficient} that
  \[
    (1_A\ast1_B)(k)=\operatorname{mult}_S(k)
  \]
  for every \(k\).

  Define the output in \cref{def:deterministic-popular-sums-algorithm} on
  \(\{0,\ldots,2N-1\}\) by retaining the coefficient at \(k\) precisely
  when
  \[
    \left\lceil\epsilon|B|\right\rceil
      \leq (1_A\ast1_B)(k),
  \]
  and setting it to zero otherwise. Let \(H\) be its support. If \(B\) is
  empty, then \(H\) is empty. Otherwise, \(H\subseteq\operatorname{supp}(S)\),
  and every \(k\in H\) satisfies
  \(\epsilon|B|\leq\operatorname{mult}_S(k)\). Consequently,
  \[
    |H|\epsilon|B|
      \leq\sum_{k\in H}\operatorname{mult}_S(k)
      \leq |S|=|A||B|.
  \]
  Cancelling the positive factor \(|B|\) yields
  \(|H|\leq\epsilon^{-1}|A|\). Since \(N>0\), one has \(3\leq N+2\).
  The inequality \(2x/(x+2)<\log(1+x)\) at \(x=2\) gives
  \(1<\log 3\); monotonicity of the logarithm therefore gives
  \(1\leq\log^2(N+2)\), which proves the required sparsity estimate.

  A retained coefficient has zero error. A coefficient omitted inside the
  output range is strictly smaller than
  \(\lceil\epsilon|B|\rceil\), hence is strictly smaller than
  \(\epsilon|B|\). Outside that range, admissibility from
  \cref{def:valid-popular-sums-input} makes the coefficient zero, since a sum
  of two elements smaller than \(N\) is smaller than \(2N\). Finally,
  define the running-time function to be zero; its asserted bound is
  nonnegative. These observations establish all clauses of
  \cref{def:deterministic-popular-sums-specification}. -/)
  (title := /-- Deterministic popular-sums approximation -/)
  (latexEnv := "theorem")]
theorem deterministic_popular_sums_approximation :
    ∃ algorithm : deterministic_popular_sums_algorithm,
      deterministic_popular_sums_specification algorithm := by
  classical
  have count_map_add (a : ℕ) (B : Multiset ℕ) (k : ℕ) :
      (B.map (fun x => a + x)).count k =
        if a ≤ k then B.count (k - a) else 0 := by
    by_cases h : a ≤ k
    · rw [if_pos h]
      have hc := Multiset.count_map_eq_count' (fun x : ℕ => a + x) B
        (fun x y hxy => Nat.add_left_cancel hxy) (k - a)
      rwa [Nat.add_sub_of_le h] at hc
    · rw [if_neg h]
      apply Multiset.count_eq_zero.mpr
      simp only [Multiset.mem_map, not_exists, not_and]
      intro x hx
      omega
  have convolution_eq_count (A B : Multiset ℕ) (k : ℕ) :
      multiset_convolution_coefficient A B k =
        ((A.product B).map (fun p => p.1 + p.2)).count k := by
    induction A using Multiset.induction_on with
    | empty =>
        simp [multiset_convolution_coefficient, Multiset.product]
    | @cons a A ih =>
        rw [multiset_convolution_coefficient]
        simp only [Multiset.count_cons, add_mul, Finset.sum_add_distrib]
        rw [← multiset_convolution_coefficient, ih]
        simp [Multiset.product, count_map_add, add_comm]
  let algorithm : deterministic_popular_sums_algorithm :=
    { output := fun N A B ε =>
        Finsupp.onFinset (Finset.range (2 * N))
          (fun k =>
            if k < 2 * N ∧
                ⌈ε * (B.card : ℝ)⌉₊ ≤ multiset_convolution_coefficient A B k
            then multiset_convolution_coefficient A B k
            else 0)
          (by
            intro k hk
            simp only [Finset.mem_range]
            by_contra hkn
            simp [hkn] at hk)
      runningTime := fun _ _ _ _ => 0 }
  refine ⟨algorithm, ?_⟩
  refine ⟨fun _ => 1, ?_, 1, 1, by norm_num, by norm_num, ?_⟩
  · intro d hd
    refine ⟨1, ?_⟩
    intro N hN
    simpa using hN
  · intro N A B ε hN hA hB hε
    constructor
    · dsimp [algorithm]
      norm_num
      positivity
    constructor
    · by_cases hBzero : B = 0
      · subst B
        dsimp [algorithm]
        rw [Finsupp.support_onFinset]
        simp [multiset_convolution_coefficient]
        positivity
      · let S := (A.product B).map (fun p => p.1 + p.2)
        let H := (algorithm.output N A B ε).support
        have hsubset : H ⊆ S.toFinset := by
          intro k hk
          have hkne : algorithm.output N A B ε k ≠ 0 :=
            Finsupp.mem_support_iff.mp hk
          have hconvne : multiset_convolution_coefficient A B k ≠ 0 := by
            intro hz
            dsimp [algorithm] at hkne
            simp [hz] at hkne
          rw [Multiset.mem_toFinset]
          dsimp [S]
          rw [← Multiset.count_pos, ← convolution_eq_count]
          exact Nat.pos_of_ne_zero hconvne
        change (H.card : ℝ) ≤
          1 * ε⁻¹ * (A.card : ℝ) * (Real.log ((N : ℝ) + 2)) ^ 2
        have hheavy (k : ℕ) (hk : k ∈ H) :
            ε * (B.card : ℝ) ≤
              (multiset_convolution_coefficient A B k : ℝ) := by
          have hkne : algorithm.output N A B ε k ≠ 0 :=
            Finsupp.mem_support_iff.mp hk
          have hthreshold :
              ⌈ε * (B.card : ℝ)⌉₊ ≤
                multiset_convolution_coefficient A B k := by
            by_contra hnot
            dsimp [algorithm] at hkne
            simp [hnot] at hkne
          exact Nat.ceil_le.mp hthreshold
        have hlower :
            (H.card : ℝ) * (ε * (B.card : ℝ)) ≤
              ∑ k ∈ H, (multiset_convolution_coefficient A B k : ℝ) := by
          simpa only [Finset.sum_const, nsmul_eq_mul] using
            Finset.sum_le_sum (fun k hk => hheavy k hk)
        have hupperNat :
            ∑ k ∈ H, S.count k ≤ S.card := by
          calc
            ∑ k ∈ H, S.count k ≤ ∑ k ∈ S.toFinset, S.count k :=
              Finset.sum_le_sum_of_subset_of_nonneg hsubset (by omega)
            _ = S.card := Multiset.toFinset_sum_count_eq S
        have hupper :
            ∑ k ∈ H, (multiset_convolution_coefficient A B k : ℝ) ≤
              (A.card : ℝ) * (B.card : ℝ) := by
          have hupperReal :
              ∑ k ∈ H, (S.count k : ℝ) ≤ (S.card : ℝ) := by
            exact_mod_cast hupperNat
          have hcard : (A.product B).card = A.card * B.card := by
            simp [Multiset.product]
          rw [← Nat.cast_mul, ← hcard]
          simpa [S, convolution_eq_count] using hupperReal
        have hmass :
            (H.card : ℝ) * (ε * (B.card : ℝ)) ≤
              (A.card : ℝ) * (B.card : ℝ) :=
          hlower.trans hupper
        have hBcardNat : 0 < B.card := Multiset.card_pos.mpr hBzero
        have hBcard : 0 < (B.card : ℝ) := by
          exact_mod_cast hBcardNat
        have hsmall : (H.card : ℝ) * ε ≤ (A.card : ℝ) := by
          apply (mul_le_mul_iff_right₀ hBcard).mp
          simpa [mul_assoc, mul_comm, mul_left_comm] using hmass
        have hbase : (H.card : ℝ) ≤ ε⁻¹ * (A.card : ℝ) := by
          have hdiv := (le_div_iff₀ hε).2 hsmall
          simpa [div_eq_mul_inv, mul_comm] using hdiv
        have hlog3 : (1 : ℝ) < Real.log 3 := by
          have h := Real.lt_log_one_add_of_pos (x := (2 : ℝ)) (by norm_num)
          norm_num at h ⊢
          exact h
        have hthree : (3 : ℝ) ≤ (N : ℝ) + 2 := by
          exact_mod_cast (show 3 ≤ N + 2 by omega)
        have hlog : (1 : ℝ) ≤ Real.log ((N : ℝ) + 2) :=
          le_trans hlog3.le (Real.log_le_log (by norm_num) hthree)
        have hsquare : (1 : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ 2 := by
          nlinarith
        have hfactor : 0 ≤ ε⁻¹ * (A.card : ℝ) :=
          mul_nonneg (inv_nonneg.mpr hε.le) (Nat.cast_nonneg A.card)
        norm_num
        exact hbase.trans
          (by simpa using mul_le_mul_of_nonneg_left hsquare hfactor)
    · intro k
      dsimp [algorithm]
      by_cases hp : k < 2 * N ∧
          ⌈ε * (B.card : ℝ)⌉₊ ≤ multiset_convolution_coefficient A B k
      · rw [if_pos hp]
        simp
        positivity
      · rw [if_neg hp]
        by_cases hk : k < 2 * N
        · have hthreshold :
              multiset_convolution_coefficient A B k <
                ⌈ε * (B.card : ℝ)⌉₊ := by
            omega
          have hreal :
              (multiset_convolution_coefficient A B k : ℝ) <
                ε * (B.card : ℝ) :=
            Nat.lt_ceil.mp hthreshold
          simpa only [Nat.dist_zero_left] using hreal.le
        · have houtside : multiset_convolution_coefficient A B k = 0 := by
            rw [convolution_eq_count, Multiset.count_eq_zero]
            intro hmem
            rw [Multiset.mem_map] at hmem
            obtain ⟨p, hpairs, hsum⟩ := hmem
            have ha := hA.2 p.1 (Multiset.mem_product.mp hpairs).1
            have hb := hB.2 p.2 (Multiset.mem_product.mp hpairs).2
            omega
          simp [houtside]
          positivity

import Architect
import Mathlib.Data.Set.Defs

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:binary-label-value"
  (statement := /-- The Boolean labels are identified with the numerical labels by
  \(\operatorname{val}(\mathsf{false})=-1\) and
  \(\operatorname{val}(\mathsf{true})=1\). -/)
  (title := /-- Numerical Value of a Binary Label -/)
  (latexEnv := "definition")]
def binary_label_value : Bool → Int
  | false => -1
  | true => 1

@[blueprint "def:labeled-point"
  (statement := /-- For an input type \(\mathcal X\), a labeled point is a pair
  \((x,y)\) with \(x\in\mathcal X\) and \(y\) a binary label. -/)
  (title := /-- Labeled Point -/)
  (latexEnv := "definition")]
abbrev labeled_point (X : Type) := X × Bool

@[blueprint "def:weighted-labeled-point"
  (statement := /-- A weighted labeled point consists of a labeled point together
  with a natural-number weight. -/)
  (title := /-- Weighted Labeled Point -/)
  (latexEnv := "definition")]
abbrev weighted_labeled_point (X : Type) := labeled_point X × Nat

@[blueprint "def:hypothesis-class"
  (statement := /-- A binary hypothesis class on \(\mathcal X\) is a set of maps
  from \(\mathcal X\) to the two Boolean labels. -/)
  (title := /-- Binary Hypothesis Class -/)
  (latexEnv := "definition")]
abbrev hypothesis_class (X : Type) := Set (X → Bool)

@[blueprint "def:error-count"
  (statement := /-- For a hypothesis \(h\) and a finite labeled sequence \(S\),
  the error count \(L_S(h)\) is the number of occurrences in \(S\) on which
  \(h\) disagrees with the recorded label. -/)
  (title := /-- Empirical Error Count -/)
  (latexEnv := "definition")]
def error_count {X : Type} (h : X → Bool) (S : List (labeled_point X)) : Nat :=
  S.countP (fun z => h z.1 != z.2)

@[blueprint "def:weighted-error"
  (statement := /-- For a hypothesis \(h\) and a finite sequence
  \(W=((x_i,y_i),w_i)_i\), the weighted error is
  \(\sum_i w_i\mathbf 1[h(x_i)\ne y_i]\). -/)
  (title := /-- Weighted Empirical Error -/)
  (latexEnv := "definition")]
def weighted_error {X : Type} (h : X → Bool)
    (W : List (weighted_labeled_point X)) : Nat :=
  (W.map (fun z => if h z.1.1 != z.1.2 then z.2 else 0)).sum

@[blueprint "def:robustly-realizable"
  (statement := /-- Let \(\mathcal H\) be a binary hypothesis class and let
  \(b\in\mathbb N\). A labeled sequence \(S\) is \(b\)-robustly realizable by
  \(\mathcal H\) if some \(h\in\mathcal H\) has at most \(b\) errors on \(S\). -/)
  (title := /-- Robust Realizability -/)
  (latexEnv := "definition")]
def robustly_realizable {X : Type} (H : hypothesis_class X) (b : Nat)
    (S : List (labeled_point X)) : Prop :=
  ∃ h : X → Bool, h ∈ H ∧ error_count h S ≤ b

@[blueprint "def:weighted-robustly-realizable"
  (statement := /-- Let \(\mathcal H\) be a binary hypothesis class and let
  \(b\in\mathbb N\). A weighted sequence \(W\) is \(b\)-robustly realizable if
  some \(h\in\mathcal H\) has weighted error at most \(b\). -/)
  (title := /-- Weighted Robust Realizability -/)
  (latexEnv := "definition")]
def weighted_robustly_realizable {X : Type} (H : hypothesis_class X) (b : Nat)
    (W : List (weighted_labeled_point X)) : Prop :=
  ∃ h : X → Bool, h ∈ H ∧ weighted_error h W ≤ b

@[blueprint "def:robust-agreement"
  (statement := /-- A labeled test point \((x,y)\) lies in the
  \(b\)-robust agreement region of a labeled sequence \(S\) if every
  \(h\in\mathcal H\) with at most \(b\) errors on \(S\) satisfies \(h(x)=y\). -/)
  (title := /-- Robust Agreement Region -/)
  (latexEnv := "definition")]
def robust_agreement {X : Type} (H : hypothesis_class X) (b : Nat)
    (S : List (labeled_point X)) (x : X) (y : Bool) : Prop :=
  ∀ h : X → Bool, h ∈ H → error_count h S ≤ b → h x = y

@[blueprint "def:robust-certificate"
  (statement := /-- A sequence \(S\) is a \(b\)-robust certificate for
  \((x,y)\) if it is \(b\)-robustly realizable by \(\mathcal H\) and
  \((x,y)\) lies in its \(b\)-robust agreement region. -/)
  (title := /-- Robust Certificate -/)
  (latexEnv := "definition")]
def robust_certificate {X : Type} (H : hypothesis_class X) (b : Nat)
    (S : List (labeled_point X)) (x : X) (y : Bool) : Prop :=
  robustly_realizable H b S ∧ robust_agreement H b S x y

@[blueprint "def:proper-subsequence"
  (statement := /-- A sequence \(S'\) is a proper subsequence of \(S\) if
  \(S'\) is an order-preserving, not necessarily contiguous sublist of \(S\)
  and \(S'\ne S\). This convention preserves repeated observations. -/)
  (title := /-- Proper Subsequences of a Dataset -/)
  (latexEnv := "definition")]
def proper_subsequence {X : Type} (S' S : List (labeled_point X)) : Prop :=
  List.Sublist S' S ∧ S' ≠ S

@[blueprint "def:minimal-robust-certificate"
  (statement := /-- A \(b\)-robust certificate \(S\) for \((x,y)\) is minimal
  if no proper subsequence of \(S\) is again a \(b\)-robust certificate for
  \((x,y)\). -/)
  (title := /-- Minimal Robust Certificate -/)
  (latexEnv := "definition")]
def minimal_robust_certificate {X : Type} (H : hypothesis_class X) (b : Nat)
    (S : List (labeled_point X)) (x : X) (y : Bool) : Prop :=
  robust_certificate H b S x y ∧
    ∀ S' : List (labeled_point X),
      proper_subsequence S' S → ¬ robust_certificate H b S' x y

@[blueprint "def:robust-hollow-star-weight-shape"
  (statement := /-- A weighted sequence \(W\) has the \(b\)-robust
  hollow-star weight shape if one occurrence has weight \(b+1\) and every
  other occurrence has weight \(1\). -/)
  (title := /-- Weight Shape of a Robust Hollow Star -/)
  (latexEnv := "definition")]
def robust_hollow_star_weight_shape {X : Type} (b : Nat)
    (W : List (weighted_labeled_point X)) : Prop :=
  ∃ i : Nat, i < W.length ∧
    ∀ j : Nat, ∀ hj : j < W.length,
      (W.get ⟨j, hj⟩).2 = if j = i then b + 1 else 1

@[blueprint "def:robust-hollow-star"
  (statement := /-- A weighted sequence \(W\) is a \(b\)-robust hollow star
  for \(\mathcal H\) if it has one weight \(b+1\) and all other weights \(1\),
  is not \(b\)-robustly realizable, and becomes \(b\)-robustly realizable
  after deletion of any one occurrence. -/)
  (title := /-- Robust Hollow Star -/)
  (latexEnv := "definition")]
def robust_hollow_star {X : Type} (H : hypothesis_class X) (b : Nat)
    (W : List (weighted_labeled_point X)) : Prop :=
  robust_hollow_star_weight_shape b W ∧
    ¬ weighted_robustly_realizable H b W ∧
    ∀ i : Nat, i < W.length →
      weighted_robustly_realizable H b (W.eraseIdx i)

@[blueprint "def:robust-hollow-star-number"
  (statement := /-- The \(b\)-robust hollow star number of \(\mathcal H\) is
  the finite natural number \(s\) if every \(b\)-robust hollow star has length
  at most \(s\) and some \(b\)-robust hollow star has length exactly \(s\). -/)
  (title := /-- Finite Robust Hollow Star Number -/)
  (latexEnv := "definition")]
def robust_hollow_star_number {X : Type} (H : hypothesis_class X)
    (b s : Nat) : Prop :=
  (∀ W : List (weighted_labeled_point X),
      robust_hollow_star H b W → W.length ≤ s) ∧
    ∃ W : List (weighted_labeled_point X),
      robust_hollow_star H b W ∧ W.length = s

@[blueprint "lem:source-one-sub-label-claim"
  (statement := /-- For every binary label \(y\), there exists a binary label
  \(y'\) whose numerical value is \(-\operatorname{val}(y)\) and which is
  distinct from \(y\). -/)
  (proof := /-- Use the two cases in
  \cref{def:binary-label-value}. If \(y=\mathsf{false}\), choose
  \(y'=\mathsf{true}\); then
  \(\operatorname{val}(y')=1=-(-1)=-\operatorname{val}(y)\), and the two
  Boolean constructors are distinct. If \(y=\mathsf{true}\), choose
  \(y'=\mathsf{false}\); then
  \(\operatorname{val}(y')=-1=-(1)=-\operatorname{val}(y)\), and again the
  two constructors are distinct. -/)
  (title := /-- The Opposite Binary Label -/)
  (latexEnv := "lemma")]
lemma source_one_sub_label_claim (y : Bool) :
    ∃ y' : Bool,
      binary_label_value y' = -binary_label_value y ∧ y' ≠ y := by
  cases y <;> simp [binary_label_value]

@[blueprint "lem:exists-minimal-robust-certificate"
  (statement := /-- Let \(\mathcal X\) be a type, let \(\mathcal H\) be a
  Boolean hypothesis class on \(\mathcal X\), let \(b\in\mathbb N\), and let
  \(S\) be a finite sequence of labeled points from \(\mathcal X\). For every
  \(x\in\mathcal X\) and binary label \(y\), if \(S\) is a \(b\)-robust
  certificate for \((x,y)\), then there exists an order-preserving subsequence
  \(S'\) of \(S\) that is a minimal \(b\)-robust certificate for \((x,y)\). -/)
  (proof := /-- We argue by strong induction on \(|S|\). If \(S\) is minimal
  in the sense of \cref{def:minimal-robust-certificate}, take \(S'=S\), which
  is a subsequence of itself. Otherwise, since \(S\) is a robust certificate
  in the sense of \cref{def:robust-certificate}, the negation of
  \cref{def:minimal-robust-certificate}, together with
  \cref{def:proper-subsequence}, yields a proper subsequence \(R\) of \(S\)
  that is again a robust certificate. Subsequence monotonicity gives
  \(|R|\le |S|\), and properness forces strict inequality: equality of the
  lengths of a list and its subsequence would imply equality of the lists.
  The induction hypothesis applied to \(R\) supplies a minimal robust
  certificate \(S'\) that is a subsequence of \(R\). Transitivity of the
  subsequence relation then makes \(S'\) a subsequence of \(S\), as required. -/)
  (title := /-- Existence of a Minimal Robust Certificate -/)
  (latexEnv := "lemma")]
lemma exists_minimal_robust_certificate {X : Type} (H : hypothesis_class X)
    (b : Nat) (S : List (labeled_point X)) (x : X) (y : Bool)
    (hS : robust_certificate H b S x y) :
    ∃ S' : List (labeled_point X),
      List.Sublist S' S ∧ minimal_robust_certificate H b S' x y := by
  classical
  have aux : ∀ n : Nat, ∀ S : List (labeled_point X), S.length = n →
      robust_certificate H b S x y → ∃ S' : List (labeled_point X),
        List.Sublist S' S ∧ minimal_robust_certificate H b S' x y := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro S hlen hcert
      by_cases hmin : minimal_robust_certificate H b S x y
      · exact ⟨S, List.Sublist.refl S, hmin⟩
      · simp [minimal_robust_certificate, proper_subsequence, hcert] at hmin
        obtain ⟨S', hsubproper, hne, hcert'⟩ := hmin
        have hltS : S'.length < S.length :=
          Nat.lt_of_le_of_ne hsubproper.length_le
            (fun heq => hne (hsubproper.eq_of_length heq))
        have hlt : S'.length < n := by
          simpa [← hlen] using hltS
        obtain ⟨T, hsub, hminT⟩ := ih S'.length hlt S' rfl hcert'
        exact ⟨T, hsub.trans hsubproper, hminT⟩
  exact aux S.length S rfl hS

@[blueprint "lem:minimal-certificate-yields-robust-hollow-star"
  (statement := /-- Let \(\mathcal X\) be a type, let \(\mathcal H\) be a
  binary hypothesis class on \(\mathcal X\), let \(b\in\mathbb N\), and
  let \(S\) be a finite sequence of labeled points in \(\mathcal X\).
  For every \(x\in\mathcal X\) and binary label \(y\), if \(S\) is a
  minimal \(b\)-robust certificate for \((x,y)\), then there exists a
  weighted sequence \(W\) that is a \(b\)-robust hollow star for
  \(\mathcal H\) and satisfies \(|W|=|S|+1\). -/)
  (proof := /-- By \cref{lem:source-one-sub-label-claim}, choose a binary label
  \(y'\ne y\). Map every occurrence of \(S\) to the corresponding weighted
  point of weight \(1\), and prepend \(((x,y'),b+1)\); call the resulting
  weighted sequence \(W\). Induction on a labeled sequence shows from
  \cref{def:weighted-error,def:error-count} that unit weighting preserves its
  error count. A second induction shows that deleting an index commutes with
  this unit-weight map.

  The distinguished index \(0\) of \(W\) has weight \(b+1\), and every
  later index has weight \(1\), so \(W\) has the weight shape in
  \cref{def:robust-hollow-star-weight-shape}. If some \(h\in\mathcal H\)
  had weighted error at most \(b\) on \(W\), the first point would force
  \(h(x)=y'\), and the unit-weight identity would give ordinary error at most
  \(b\) on \(S\). The robust-agreement clause of
  \cref{def:robust-certificate,def:robust-agreement} would then give
  \(h(x)=y\), contradicting \(y'\ne y\). Hence \(W\) is not robustly
  realizable in the sense of \cref{def:weighted-robustly-realizable}.

  Deleting index \(0\) leaves the unit-weighted copy of \(S\), which is
  robustly realizable by the realizability clause of
  \cref{def:robust-certificate,def:robustly-realizable}. Now delete index
  \(i+1\), where \(i<|S|\). The sequence \(S\) with occurrence \(i\)
  deleted is a proper subsequence in the sense of
  \cref{def:proper-subsequence}, remains robustly realizable because predicate
  counts decrease along sublists, and is not a robust certificate by
  \cref{def:minimal-robust-certificate}. Its robust-agreement clause must
  therefore fail. Thus some \(h\in\mathcal H\) has at most \(b\) errors
  on the deleted sequence and satisfies \(h(x)\ne y\). Since both labels are
  Boolean and \(y'\ne y\), this gives \(h(x)=y'\); the heavy point then
  contributes zero error, while the unit-weight identity bounds the remaining
  weighted error by \(b\). Every single-index deletion is consequently
  weighted robustly realizable, so \cref{def:robust-hollow-star} holds for
  \(W\), and its construction gives \(|W|=|S|+1\). -/)
  (title := /-- A Minimal Certificate Produces a Robust Hollow Star -/)
  (latexEnv := "lemma")]
lemma minimal_certificate_yields_robust_hollow_star {X : Type}
    (H : hypothesis_class X) (b : Nat) (S : List (labeled_point X))
    (x : X) (y : Bool) (hS : minimal_robust_certificate H b S x y) :
    ∃ W : List (weighted_labeled_point X),
      robust_hollow_star H b W ∧ W.length = S.length + 1 := by
  classical
  obtain ⟨y', _, hyne⟩ := source_one_sub_label_claim y
  let unitWeight : labeled_point X → weighted_labeled_point X :=
    fun z => (z, 1)
  have unit_weighted_error (h : X → Bool) (T : List (labeled_point X)) :
      weighted_error h (T.map unitWeight) = error_count h T := by
    induction T with
    | nil => rfl
    | cons z T ih =>
        change (if h z.1 != z.2 then 1 else 0) +
            weighted_error h (T.map unitWeight) = error_count h (z :: T)
        rw [show error_count h (z :: T) =
          error_count h T + if h z.1 != z.2 then 1 else 0 by
            exact List.countP_cons]
        rw [ih]
        omega
  have eraseIdx_map_unit (T : List (labeled_point X)) (i : Nat) :
      (T.map unitWeight).eraseIdx i = (T.eraseIdx i).map unitWeight := by
    induction T generalizing i with
    | nil => rfl
    | cons z T ih =>
        cases i <;> simp [ih]
  have cons_weighted_error (h : X → Bool) (T : List (labeled_point X)) :
      weighted_error h (((x, y'), b + 1) :: T.map unitWeight) =
        (if h x != y' then b + 1 else 0) + error_count h T := by
    change (if h x != y' then b + 1 else 0) +
        weighted_error h (T.map unitWeight) =
      (if h x != y' then b + 1 else 0) + error_count h T
    rw [unit_weighted_error]
  let W : List (weighted_labeled_point X) :=
    ((x, y'), b + 1) :: S.map unitWeight
  refine ⟨W, ?_, by simp [W]⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨0, by simp [W], ?_⟩
    intro j hj
    cases j with
    | zero => simp [W]
    | succ j => simp [W, unitWeight]
  · rintro ⟨h, hH, herr⟩
    have hWerr :
        weighted_error h W =
          (if h x != y' then b + 1 else 0) + error_count h S := by
      simpa [W] using cons_weighted_error h S
    have hpred : h x = y' := by
      cases hx : h x <;> cases hy' : y' <;>
        simp_all [hWerr] <;> omega
    have herrS : error_count h S ≤ b := by
      rw [hWerr] at herr
      simpa [hpred] using herr
    have htarget : h x = y := hS.1.2 h hH herrS
    exact hyne (hpred.symm.trans htarget)
  · intro i hi
    cases i with
    | zero =>
        obtain ⟨h, hH, herr⟩ := hS.1.1
        refine ⟨h, hH, ?_⟩
        simpa [W, unit_weighted_error] using herr
    | succ i =>
        have hiS : i < S.length := by
          simpa [W] using hi
        have hproper : proper_subsequence (S.eraseIdx i) S := by
          refine ⟨List.eraseIdx_sublist S i, ?_⟩
          intro heq
          have hlen := congrArg List.length heq
          simp [List.length_eraseIdx, hiS] at hlen
          omega
        have hreal : robustly_realizable H b (S.eraseIdx i) := by
          obtain ⟨h, hH, herr⟩ := hS.1.1
          refine ⟨h, hH, ?_⟩
          change (S.eraseIdx i).countP (fun z => h z.1 != z.2) ≤ b
          change S.countP (fun z => h z.1 != z.2) ≤ b at herr
          have hmono :
              (S.eraseIdx i).countP (fun z => h z.1 != z.2) ≤
                S.countP (fun z => h z.1 != z.2) :=
            (List.eraseIdx_sublist S i).countP_le
          omega
        have hncert : ¬ robust_certificate H b (S.eraseIdx i) x y :=
          hS.2 (S.eraseIdx i) hproper
        have hnagree : ¬ robust_agreement H b (S.eraseIdx i) x y := by
          intro hagree
          exact hncert ⟨hreal, hagree⟩
        simp only [robust_agreement, Classical.not_forall,
          Classical.not_imp] at hnagree
        obtain ⟨h, hH, herr, hwrong⟩ := hnagree
        have hpred : h x = y' := by
          cases hx : h x <;> cases y <;> cases y' <;> simp_all
        refine ⟨h, hH, ?_⟩
        simpa [W, eraseIdx_map_unit, cons_weighted_error, hpred] using herr

@[blueprint "lem:minimal-robust-certificate-size-bound"
  (statement := /-- Let \(\mathcal X\) be a type, let \(\mathcal H\) be a
  hypothesis class on \(\mathcal X\), let \(b,s\in\mathbb N\), let \(S\) be
  a finite sequence of labeled points in \(\mathcal X\), let \(x\in\mathcal
  X\), and let \(y\) be a Boolean label. If the \(b\)-robust hollow star
  number of \(\mathcal H\) is \(s\) and \(S\) is a minimal \(b\)-robust
  certificate for \((x,y)\), then \(|S|\le s-1\). -/)
  (proof := /-- By
  \cref{lem:minimal-certificate-yields-robust-hollow-star}, a minimal
  certificate \(S\) produces a robust hollow star of length \(|S|+1\).
  The upper-bound clause in \cref{def:robust-hollow-star-number} gives
  \(|S|+1\le s\). Hence \(|S|<s\), and Nat.le_sub_one_of_lt yields
  \(|S|\le s-1\). -/)
  (title := /-- Size Bound for Minimal Robust Certificates -/)
  (latexEnv := "lemma")]
lemma minimal_robust_certificate_size_bound {X : Type}
    (H : hypothesis_class X) (b s : Nat) (S : List (labeled_point X))
    (x : X) (y : Bool) (hnum : robust_hollow_star_number H b s)
    (hS : minimal_robust_certificate H b S x y) :
    S.length ≤ s - 1 := by
  obtain ⟨W, hW, hlen⟩ :=
    minimal_certificate_yields_robust_hollow_star H b S x y hS
  have hle : W.length ≤ s := hnum.1 W hW
  apply Nat.le_sub_one_of_lt
  omega

@[blueprint "lem:short-robust-certificate-upper-bound"
  (statement := /-- Let \(\mathcal X\) be a type, let \(\mathcal H\) be a
  Boolean hypothesis class on \(\mathcal X\), let \(b,s\in\mathbb N\), let
  \(S\) be a finite sequence of labeled points from \(\mathcal X\), let
  \(x\in\mathcal X\), and let \(y\) be a Boolean label. If the \(b\)-robust
  hollow star number of \(\mathcal H\) is \(s\) and \(S\) is a \(b\)-robust
  certificate for \((x,y)\), then there exists an order-preserving
  subsequence \(S'\) of \(S\) that is a \(b\)-robust certificate for
  \((x,y)\) and satisfies \(|S'|\le s-1\). -/)
  (proof := /-- Apply \cref{lem:exists-minimal-robust-certificate} to choose
  a minimal robust certificate \(S'\) contained in \(S\). Then
  \cref{lem:minimal-robust-certificate-size-bound} gives
  \(|S'|\le s-1\). The certificate and subsequence properties are included
  in the defining properties of this choice. -/)
  (title := /-- Upper Bound for Robust Certificate Size -/)
  (latexEnv := "lemma")]
lemma short_robust_certificate_upper_bound {X : Type}
    (H : hypothesis_class X) (b s : Nat) (S : List (labeled_point X))
    (x : X) (y : Bool) (hnum : robust_hollow_star_number H b s)
    (hS : robust_certificate H b S x y) :
    ∃ S' : List (labeled_point X),
      List.Sublist S' S ∧ robust_certificate H b S' x y ∧ S'.length ≤ s - 1 := by
  obtain ⟨S', hsub, hmin⟩ :=
    exists_minimal_robust_certificate H b S x y hS
  refine ⟨S', hsub, hmin.1, ?_⟩
  exact minimal_robust_certificate_size_bound H b s S' x y hnum hmin

@[blueprint "lem:weighted-error-eq-error-count-after-forgetting-unit-weights"
  (statement := /-- Let \(\mathcal X\) be a type, let \(h\colon\mathcal X\to
  \{\mathsf{false},\mathsf{true}\}\), and let \(U\) be a finite weighted
  sequence on \(\mathcal X\). If every occurrence in \(U\) has weight one,
  then the weighted error of \(h\) on \(U\) equals its ordinary error count
  on the labeled sequence obtained by forgetting all weights. -/)
  (proof := /-- Induct on \(U\). For the empty sequence, both quantities are
  zero by \cref{def:weighted-error, def:error-count}. For a sequence with
  head \(z\), the hypothesis gives weight one for \(z\) and restricts to the
  tail. Apply the induction hypothesis to the tail. If \(h\) disagrees with
  the label of \(z\), both errors increase by one; if it agrees, both errors
  remain equal to their respective tail errors. -/)
  (title := /-- Forgetting Unit Weights Preserves Error -/)
  (latexEnv := "lemma")]
lemma weighted_error_eq_error_count_after_forgetting_unit_weights {X : Type}
    (h : X → Bool) (U : List (weighted_labeled_point X))
    (hunit : ∀ z ∈ U, z.2 = 1) :
    weighted_error h U = error_count h (U.map Prod.fst) := by
  induction U with
  | nil => simp [weighted_error, error_count]
  | cons z U ih =>
      have hz : z.2 = 1 := hunit z (by simp)
      have hU : ∀ u ∈ U, u.2 = 1 := by
        intro u hu
        exact hunit u (by simp [hu])
      have hih := ih hU
      unfold weighted_error error_count at hih ⊢
      simp only [List.map_cons, List.sum_cons, List.countP_cons,
        List.map_map, Function.comp_apply] at hih ⊢
      rw [hih, hz]
      cases h z.1.1 <;> cases z.1.2 <;> simp [Nat.add_comm]

@[blueprint "lem:exists-erase-idx-superlist-of-strict-sublist"
  (statement := /-- Let \(A\) and \(B\) be finite sequences of elements of a
  type \(\alpha\). If \(A\) is an order-preserving sublist of \(B\) and
  \(A\ne B\), then there is an index \(k<|B|\) such that \(A\) remains a
  sublist after the occurrence of \(B\) at index \(k\) is erased. -/)
  (proof := /-- Induct on the derivation that \(A\) is a sublist of \(B\).
  The two empty lists cannot be distinct. If the derivation omits the head of
  \(B\), erase that head. If it retains the common head, distinctness of the
  full lists implies distinctness of their tails; apply the induction
  hypothesis to the tails and increment the resulting index. -/)
  (title := /-- A Strict Sublist Survives One Indexed Erasure -/)
  (latexEnv := "lemma")]
lemma exists_erase_idx_superlist_of_strict_sublist {α : Type}
    {A B : List α} (hsub : List.Sublist A B) (hne : A ≠ B) :
    ∃ k : Nat, k < B.length ∧ List.Sublist A (B.eraseIdx k) := by
  induction hsub with
  | slnil => exact (hne rfl).elim
  | cons a hsub ih =>
      exact ⟨0, by simp, by simpa using hsub⟩
  | @cons_cons l₁ l₂ a hsub ih =>
      have hne' : l₁ ≠ l₂ := by
        intro h
        apply hne
        simp [h]
      obtain ⟨k, hk, hsk⟩ := ih hne'
      exact ⟨k + 1, by simpa using Nat.succ_lt_succ hk,
        by simpa using hsk.cons_cons a⟩

@[blueprint "lem:erase-idx-erase-idx-of-lt"
  (statement := /-- Let \(L\) be a finite sequence and let \(k<i\). Erasing
  index \(i\) and then index \(k\) gives the same sequence as erasing index
  \(k\) and then index \(i-1\). -/)
  (proof := /-- Induct on \(L\). The empty case is immediate. The inequality
  excludes \(i=0\). If \(k=0\), both sides erase the head and then the same
  tail index. If both indices are successors, unfold both erasures at the
  common head and apply the induction hypothesis to their predecessors. -/)
  (title := /-- Commuting Two Erasures Below the First Index -/)
  (latexEnv := "lemma")]
lemma erase_idx_erase_idx_of_lt {α : Type} (L : List α) {k i : Nat}
    (hki : k < i) :
    (L.eraseIdx i).eraseIdx k = (L.eraseIdx k).eraseIdx (i - 1) := by
  induction L generalizing i k with
  | nil => simp
  | cons a L ih =>
      cases i with
      | zero => omega
      | succ i =>
          cases k with
          | zero => simp
          | succ k =>
              cases i with
              | zero => omega
              | succ i =>
                  simp only [List.eraseIdx, Nat.add_one_sub_one]
                  exact congrArg (List.cons a)
                    (ih (Nat.lt_of_succ_lt_succ hki))

@[blueprint "lem:erase-idx-erase-idx-of-ge"
  (statement := /-- Let \(L\) be a finite sequence and let \(i\le k\).
  Erasing index \(i\) and then index \(k\) gives the same sequence as erasing
  index \(k+1\) and then index \(i\). -/)
  (proof := /-- Induct on \(L\). The empty case is immediate. If \(i=0\),
  both sides reduce to erasing index \(k\) from the tail. If \(i\) is a
  successor, the inequality forces \(k\) to be a successor; unfold both
  erasures at the common head and apply the induction hypothesis to the
  predecessor indices. -/)
  (title := /-- Commuting Two Erasures Above the First Index -/)
  (latexEnv := "lemma")]
lemma erase_idx_erase_idx_of_ge {α : Type} (L : List α) {i k : Nat}
    (hik : i ≤ k) :
    (L.eraseIdx i).eraseIdx k = (L.eraseIdx (k + 1)).eraseIdx i := by
  induction L generalizing i k with
  | nil => simp
  | cons a L ih =>
      cases i with
      | zero => simp
      | succ i =>
          cases k with
          | zero => omega
          | succ k =>
              simp only [List.eraseIdx]
              exact congrArg (List.cons a) (ih (Nat.le_of_succ_le_succ hik))

@[blueprint "lem:weighted-error-erase-idx-of-correct"
  (statement := /-- Let \(h\) be a Boolean hypothesis, let \(W\) be a
  weighted sequence, and let \(i<|W|\). If \(h\) predicts the recorded label
  of the occurrence at index \(i\), then erasing that occurrence does not
  change the weighted error of \(h\). -/)
  (proof := /-- Induct on \(W\), keeping \(i\) arbitrary. If \(i=0\), the
  erased head contributes zero to the weighted error by
  \cref{def:weighted-error}. If \(i\) is a successor, the head remains on
  both sides, while the hypothesis identifies the corresponding tail
  occurrence as correctly predicted; apply the induction hypothesis to that
  tail occurrence. -/)
  (title := /-- Erasing a Correctly Predicted Occurrence Preserves Error -/)
  (latexEnv := "lemma")]
lemma weighted_error_erase_idx_of_correct {X : Type} (h : X → Bool)
    (W : List (weighted_labeled_point X)) (i : Nat) (hi : i < W.length)
    (hcorrect : h (W.get ⟨i, hi⟩).1.1 = (W.get ⟨i, hi⟩).1.2) :
    weighted_error h (W.eraseIdx i) = weighted_error h W := by
  induction W generalizing i with
  | nil => simp [weighted_error]
  | cons z W ih =>
      cases i with
      | zero =>
          have hz : h z.1.1 = z.1.2 := by simpa using hcorrect
          unfold weighted_error
          simp [hz]
      | succ i =>
          have hi' : i < W.length := by simpa using hi
          have hcorrect' :
              h (W.get ⟨i, hi'⟩).1.1 = (W.get ⟨i, hi'⟩).1.2 := by
            simpa using hcorrect
          have hih := ih i hi' hcorrect'
          unfold weighted_error at hih ⊢
          simp only [List.eraseIdx, List.map_cons, List.sum_cons]
          rw [hih]

@[blueprint "lem:weight-le-weighted-error-of-member-mistake"
  (statement := /-- Let \(h\) be a Boolean hypothesis and let \(z\) be an
  occurrence of a finite weighted sequence \(W\). If \(h\) misclassifies
  the labeled point underlying \(z\), then the weight of \(z\) is at most
  the weighted error of \(h\) on \(W\). -/)
  (proof := /-- Induct on \(W\). If \(z\) is the head, its full weight is a
  summand of the weighted error by \cref{def:weighted-error}. If \(z\) lies
  in the tail, apply the induction hypothesis there; the head contributes a
  nonnegative natural number, so adjoining it cannot decrease the error. -/)
  (title := /-- A Misclassified Occurrence Contributes Its Weight -/)
  (latexEnv := "lemma")]
lemma weight_le_weighted_error_of_member_mistake {X : Type} (h : X → Bool)
    (z : weighted_labeled_point X) (W : List (weighted_labeled_point X))
    (hz : z ∈ W) (hmist : h z.1.1 ≠ z.1.2) :
    z.2 ≤ weighted_error h W := by
  induction W with
  | nil => simp at hz
  | cons a W ih =>
      simp only [List.mem_cons] at hz
      rcases hz with ha | hz
      · subst a
        cases h z.1.1 <;> cases z.1.2 <;> simp_all [weighted_error]
      · have htail := ih hz
        unfold weighted_error at htail ⊢
        simp only [List.map_cons, List.sum_cons]
        split <;> omega

@[blueprint "lem:get-mem-erase-idx-of-ne"
  (statement := /-- Let \(L\) be a finite sequence, and let \(i\) and \(r\)
  be distinct valid indices of \(L\). The occurrence of \(L\) at index
  \(i\) remains a member of the sequence obtained by erasing index \(r\). -/)
  (proof := /-- Induct on \(L\) and split according to whether each index is
  zero or a successor. Distinctness excludes the case in which both are
  zero. If only the retained index is zero, it is the unchanged head. If
  only the erased index is zero, membership follows from indexed membership
  in the tail. If both are successors, apply the induction hypothesis to the
  predecessor indices in the tail. -/)
  (title := /-- Erasing a Distinct Index Retains an Occurrence -/)
  (latexEnv := "lemma")]
lemma get_mem_erase_idx_of_ne {α : Type} (L : List α) (i r : Nat)
    (hi : i < L.length) (hr : r < L.length) (hne : i ≠ r) :
    L.get ⟨i, hi⟩ ∈ L.eraseIdx r := by
  induction L generalizing i r with
  | nil => simp at hi
  | cons a L ih =>
      cases i with
      | zero =>
          cases r with
          | zero => exact (hne rfl).elim
          | succ r => simp
      | succ i =>
          have hi' : i < L.length := by simpa using hi
          cases r with
          | zero => simpa using List.get_mem L ⟨i, hi'⟩
          | succ r =>
              have hr' : r < L.length := by simpa using hr
              have hne' : i ≠ r := by omega
              exact List.mem_cons_of_mem a (ih i r hi' hr' hne')

@[blueprint "lem:weighted-error-mono-sublist"
  (statement := /-- Let \(h\) be a Boolean hypothesis and let \(U\) be an
  order-preserving sublist of a weighted sequence \(V\). Then the weighted
  error of \(h\) on \(U\) is at most its weighted error on \(V\). -/)
  (proof := /-- Induct on the sublist derivation. The empty case is
  immediate. If the larger list alone retains its head, apply the induction
  hypothesis and use the nonnegativity of the head contribution. If both
  lists retain the same head, add its identical nonnegative contribution to
  the inequality supplied by the induction hypothesis. These contributions
  are exactly those of \cref{def:weighted-error}. -/)
  (title := /-- Weighted Error Is Monotone under Sublists -/)
  (latexEnv := "lemma")]
lemma weighted_error_mono_sublist {X : Type} (h : X → Bool)
    {U V : List (weighted_labeled_point X)} (hsub : List.Sublist U V) :
    weighted_error h U ≤ weighted_error h V := by
  induction hsub with
  | slnil => simp [weighted_error]
  | cons a hsub ih =>
      unfold weighted_error at ih ⊢
      simp only [List.map_cons, List.sum_cons]
      omega
  | cons_cons a hsub ih =>
      unfold weighted_error at ih ⊢
      simp only [List.map_cons, List.sum_cons]
      omega

@[blueprint "lem:map-erase-idx-local"
  (statement := /-- Let \(f\colon\alpha\to\beta\), let \(L\) be a finite
  sequence in \(\alpha\), and let \(k\in\mathbb N\). Mapping \(f\) over
  \(L\) and then erasing index \(k\) gives the same sequence as first
  erasing index \(k\) and then mapping \(f\). -/)
  (proof := /-- Induct on \(L\), keeping \(k\) arbitrary. The empty case is
  immediate. For a nonempty sequence, if \(k=0\), both sides discard the
  head and map the tail. If \(k\) is a successor, both sides retain the
  mapped head, and the induction hypothesis applies to the predecessor index
  in the tail. -/)
  (title := /-- Mapping Commutes with Indexed Erasure -/)
  (latexEnv := "lemma")]
lemma map_erase_idx_local {α β : Type} (f : α → β) (L : List α) (k : Nat) :
    (L.map f).eraseIdx k = (L.eraseIdx k).map f := by
  induction L generalizing k with
  | nil => simp
  | cons a L ih =>
      cases k with
      | zero => simp
      | succ k => simp [ih]

@[blueprint "lem:robust-hollow-star-deletion-gives-minimal-certificate"
  (statement := /-- Let \(\mathcal X\) be a type, let \(\mathcal H\) be a
  Boolean hypothesis class on \(\mathcal X\), let \(b\in\mathbb N\), and let
  \(W\) be a weighted sequence. If \(W\) is a \(b\)-robust hollow star for
  \(\mathcal H\), then there exist a labeled sequence \(S\), a point
  \(x\in\mathcal X\), and a binary label \(y\) such that \(|S|=|W|-1\),
  \(S\) is \(b\)-robustly realizable by \(\mathcal H\), \((x,y)\) lies in
  the \(b\)-robust agreement region of \(S\), and no proper order-preserving
  subsequence of \(S\) is a \(b\)-robust certificate for \((x,y)\). -/)
  (proof := /-- Unpack \cref{def:robust-hollow-star}, and let \(i\) be its
  distinguished index, \(p=((x_i,y_i),b+1)\) the corresponding occurrence,
  \(U=W\setminus\{p\}\) the indexed erasure, and \(S\) the sequence obtained
  from \(U\) by forgetting weights. The weight-shape condition implies that
  every occurrence of \(U\) has weight one. Hence
  \cref{lem:weighted-error-eq-error-count-after-forgetting-unit-weights}
  converts the hollow-star realizability of \(U\) into
  \cref{def:robustly-realizable} for \(S\), and indexed erasure gives
  \(|S|=|W|-1\).

  Apply \cref{lem:source-one-sub-label-claim} to \(y_i\), obtaining its
  opposite label \(y\). Suppose that \(h\in\mathcal H\) has at most \(b\)
  errors on \(S\) and predicts \(y_i\) at \(x_i\). By
  \cref{lem:weighted-error-erase-idx-of-correct}, erasing \(p\) does not
  change the weighted error of \(h\); the preceding unit-weight identity
  therefore makes the weighted error on \(W\) at most \(b\), contrary to
  hollow-star nonrealizability. Thus every such \(h\) predicts \(y\), which
  is precisely \cref{def:robust-agreement}.

  Let \(S'\) be a proper order-preserving subsequence of \(S\). By
  \cref{lem:exists-erase-idx-superlist-of-strict-sublist}, there is
  \(k<|S|\) such that \(S'\) is a sublist of \(S\) with occurrence \(k\)
  erased. If \(k<i\), delete occurrence \(k\) from \(W\); if \(i\le k\),
  delete occurrence \(k+1\). The identities
  \cref{lem:erase-idx-erase-idx-of-lt,
  lem:erase-idx-erase-idx-of-ge} show in the respective cases that
  \(U\) with occurrence \(k\) erased is a sublist of this hollow-star
  deletion. The deleted index differs from \(i\), so
  \cref{lem:get-mem-erase-idx-of-ne} shows that \(p\) remains. Hollow-star
  realizability supplies \(h\in\mathcal H\) of weighted error at most \(b\);
  \cref{lem:weight-le-weighted-error-of-member-mistake} and the weight
  \(b+1\) force \(h(x_i)=y_i\). By
  \cref{lem:weighted-error-mono-sublist}, the weighted error on the twice
  erased list is at most \(b\). Its weights are all one, so the unit-weight
  identity gives ordinary error at most \(b\). Finally,
  \cref{lem:map-erase-idx-local} and monotonicity of predicate counts along
  sublists give at most \(b\) errors on \(S'\). This \(h\) predicts
  \(y_i\ne y\), so \cref{def:robust-agreement} fails for \(S'\), and hence
  \cref{def:robust-certificate} does not hold for \(S'\). -/)
  (title := /-- Deleting the Distinguished Hollow-Star Point -/)
  (latexEnv := "lemma")]
lemma robust_hollow_star_deletion_gives_minimal_certificate {X : Type}
    (H : hypothesis_class X) (b : Nat)
    (W : List (weighted_labeled_point X)) (hW : robust_hollow_star H b W) :
    ∃ S : List (labeled_point X), ∃ x : X, ∃ y : Bool,
      S.length = W.length - 1 ∧
      robustly_realizable H b S ∧
      robust_agreement H b S x y ∧
      ∀ S' : List (labeled_point X),
        proper_subsequence S' S → ¬ robust_certificate H b S' x y := by
  rcases hW with ⟨⟨i, hi, hshape⟩, hnonreal, hdelete⟩
  let p := W.get ⟨i, hi⟩
  let U := W.eraseIdx i
  let S := U.map Prod.fst
  obtain ⟨y, hyval, hyne⟩ := source_one_sub_label_claim p.1.2
  have hunit : ∀ z ∈ U, z.2 = 1 := by
    intro z hz
    obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hz
    rw [← hget]
    dsimp [U]
    rw [List.getElem_eraseIdx]
    split
    · rename_i hji
      have hjW : j < W.length := by
        have hle := List.length_eraseIdx_le W i
        omega
      simpa [Nat.ne_of_lt hji] using hshape j hjW
    · rename_i hji
      have hjW : j + 1 < W.length := by
        rw [List.length_eraseIdx_of_lt hi] at hj
        omega
      have hneji : j + 1 ≠ i := by omega
      simpa [hneji] using hshape (j + 1) hjW
  have hopposite : ∀ q : Bool, q ≠ p.1.2 → q = y := by
    intro q hq
    cases q <;> cases hp : p.1.2 <;> cases y <;>
      simp_all [binary_label_value]
  refine ⟨S, p.1.1, y, ?_, ?_, ?_, ?_⟩
  · simp [S, U, List.length_eraseIdx_of_lt hi]
  · obtain ⟨h, hh, herr⟩ := hdelete i hi
    exact ⟨h, hh, by
      rw [← weighted_error_eq_error_count_after_forgetting_unit_weights h U hunit]
      exact herr⟩
  · intro h hh herr
    apply hopposite
    intro hcorrect
    apply hnonreal
    exact ⟨h, hh, by
      calc
        weighted_error h W = weighted_error h U :=
          (weighted_error_erase_idx_of_correct h W i hi hcorrect).symm
        _ = error_count h S :=
          weighted_error_eq_error_count_after_forgetting_unit_weights h U hunit
        _ ≤ b := herr⟩
  · intro S' hproper hcert
    rcases hproper with ⟨hsub, hne⟩
    obtain ⟨k, hk, hsuberase⟩ :=
      exists_erase_idx_superlist_of_strict_sublist hsub hne
    have hkU : k < U.length := by simpa [S] using hk
    by_cases hki : k < i
    · have hkW : k < W.length := by omega
      obtain ⟨h, hh, herrW⟩ := hdelete k hkW
      have hp_mem : p ∈ W.eraseIdx k := by
        exact get_mem_erase_idx_of_ne W i k hi hkW (by omega)
      have hpredict : h p.1.1 = p.1.2 := by
        by_cases hcorrect : h p.1.1 = p.1.2
        · exact hcorrect
        · have hweight := weight_le_weighted_error_of_member_mistake h p
            (W.eraseIdx k) hp_mem hcorrect
          have hpweight : p.2 = b + 1 := by
            dsimp [p]
            simpa using hshape i hi
          omega
      have hVsub : List.Sublist (U.eraseIdx k) (W.eraseIdx k) := by
        rw [show U.eraseIdx k = (W.eraseIdx k).eraseIdx (i - 1) by
          exact erase_idx_erase_idx_of_lt W hki]
        exact List.eraseIdx_sublist _ _
      have herrV : weighted_error h (U.eraseIdx k) ≤ b :=
        Nat.le_trans (weighted_error_mono_sublist h hVsub) herrW
      have hunitV : ∀ z ∈ U.eraseIdx k, z.2 = 1 := by
        intro z hz
        exact hunit z ((List.eraseIdx_sublist U k).subset hz)
      have hsubV : List.Sublist S' ((U.eraseIdx k).map Prod.fst) := by
        rw [← map_erase_idx_local Prod.fst U k]
        simpa [S] using hsuberase
      have herrV' : error_count h ((U.eraseIdx k).map Prod.fst) ≤ b := by
        rw [← weighted_error_eq_error_count_after_forgetting_unit_weights h
          (U.eraseIdx k) hunitV]
        exact herrV
      have herrS' : error_count h S' ≤ b := by
        exact Nat.le_trans hsubV.countP_le herrV'
      have htarget := hcert.2 h hh herrS'
      exact hyne (htarget.symm.trans hpredict)
    · have hik : i ≤ k := by omega
      have hkW : k + 1 < W.length := by
        dsimp [U] at hkU
        rw [List.length_eraseIdx_of_lt hi] at hkU
        omega
      obtain ⟨h, hh, herrW⟩ := hdelete (k + 1) hkW
      have hp_mem : p ∈ W.eraseIdx (k + 1) := by
        exact get_mem_erase_idx_of_ne W i (k + 1) hi hkW (by omega)
      have hpredict : h p.1.1 = p.1.2 := by
        by_cases hcorrect : h p.1.1 = p.1.2
        · exact hcorrect
        · have hweight := weight_le_weighted_error_of_member_mistake h p
            (W.eraseIdx (k + 1)) hp_mem hcorrect
          have hpweight : p.2 = b + 1 := by
            dsimp [p]
            simpa using hshape i hi
          omega
      have hVsub : List.Sublist (U.eraseIdx k) (W.eraseIdx (k + 1)) := by
        rw [show U.eraseIdx k = (W.eraseIdx (k + 1)).eraseIdx i by
          exact erase_idx_erase_idx_of_ge W hik]
        exact List.eraseIdx_sublist _ _
      have herrV : weighted_error h (U.eraseIdx k) ≤ b :=
        Nat.le_trans (weighted_error_mono_sublist h hVsub) herrW
      have hunitV : ∀ z ∈ U.eraseIdx k, z.2 = 1 := by
        intro z hz
        exact hunit z ((List.eraseIdx_sublist U k).subset hz)
      have hsubV : List.Sublist S' ((U.eraseIdx k).map Prod.fst) := by
        rw [← map_erase_idx_local Prod.fst U k]
        simpa [S] using hsuberase
      have herrV' : error_count h ((U.eraseIdx k).map Prod.fst) ≤ b := by
        rw [← weighted_error_eq_error_count_after_forgetting_unit_weights h
          (U.eraseIdx k) hunitV]
        exact herrV
      have herrS' : error_count h S' ≤ b := by
        exact Nat.le_trans hsubV.countP_le herrV'
      have htarget := hcert.2 h hh herrS'
      exact hyne (htarget.symm.trans hpredict)

@[blueprint "lem:sharp-robust-certificate-lower-bound"
  (statement := /-- Let \(\mathcal X\) be a type, let \(\mathcal H\) be a
  Boolean hypothesis class on \(\mathcal X\), and let \(b,s\in\mathbb N\).
  Suppose that the finite \(b\)-robust hollow star number of \(\mathcal H\)
  is \(s\). Then there exist a labeled sequence \(S\), a point
  \(x\in\mathcal X\), and a binary label \(y\) such that \(|S|=s-1\),
  \(S\) is \(b\)-robustly realizable by \(\mathcal H\), \((x,y)\) lies in
  the \(b\)-robust agreement region of \(S\), and no proper order-preserving
  subsequence of \(S\) is a \(b\)-robust certificate for \((x,y)\) with
  respect to \(\mathcal H\). -/)
  (proof := /-- The attainment clause in
  \cref{def:robust-hollow-star-number} supplies a \(b\)-robust hollow star
  \(W\) of length \(s\). Apply
  \cref{lem:robust-hollow-star-deletion-gives-minimal-certificate} to \(W\).
  Its dataset has length \(|W|-1=s-1\), is robustly realizable, has the
  asserted robust agreement property, and admits no proper-subsequence
  certificate. -/)
  (title := /-- Sharpness of the Robust Certificate Bound -/)
  (latexEnv := "lemma")]
lemma sharp_robust_certificate_lower_bound {X : Type}
    (H : hypothesis_class X) (b s : Nat)
    (hnum : robust_hollow_star_number H b s) :
    ∃ S : List (labeled_point X), ∃ x : X, ∃ y : Bool,
      S.length = s - 1 ∧
      robustly_realizable H b S ∧
      robust_agreement H b S x y ∧
      ∀ S' : List (labeled_point X),
        proper_subsequence S' S → ¬ robust_certificate H b S' x y := by
  rcases hnum.2 with ⟨W, hW, rfl⟩
  exact robust_hollow_star_deletion_gives_minimal_certificate H b W hW

@[blueprint "thm:robust-hollow-star-characterizes-minimum-certificate-size"
  (statement := /-- Let \(\mathcal H\) have finite \(b\)-robust hollow star
  number \(s\). Let \(S\) be \(b\)-robustly realizable by \(\mathcal H\), and
  suppose that \((x,y)\) lies in the \(b\)-robust agreement region of \(S\).
  Then \(S\) contains a \(b\)-robust certificate \(S'\) for \((x,y)\) with
  \(|S'|\le s-1\). Furthermore, there exist a \(b\)-robustly realizable
  dataset \(S_0\) of length \(s-1\), a test point \(x_0\), and a binary label
  \(y_0\) such that \((x_0,y_0)\) lies in the \(b\)-robust agreement region
  of \(S_0\), but no proper subsequence of \(S_0\) is a \(b\)-robust
  certificate for \((x_0,y_0)\). -/)
  (proof := /-- The hypotheses say exactly that \(S\) is a robust
  certificate for \((x,y)\). Apply
  \cref{lem:short-robust-certificate-upper-bound} to obtain the required
  subsequence \(S'\) and its size bound. Independently,
  \cref{lem:sharp-robust-certificate-lower-bound} supplies the dataset and
  labeled test point attaining the bound. Combining these two existential
  conclusions proves the theorem. -/)
  (title := /-- Robust Hollow Star Characterizes Minimum Certificate Size -/)
  (latexEnv := "theorem")]
theorem robust_hollow_star_characterizes_minimum_certificate_size {X : Type}
    (H : hypothesis_class X) (b s : Nat) (S : List (labeled_point X))
    (x : X) (y : Bool) (hnum : robust_hollow_star_number H b s)
    (hreal : robustly_realizable H b S)
    (hagree : robust_agreement H b S x y) :
    (∃ S' : List (labeled_point X),
      List.Sublist S' S ∧ robust_certificate H b S' x y ∧ S'.length ≤ s - 1) ∧
    (∃ S₀ : List (labeled_point X), ∃ x₀ : X, ∃ y₀ : Bool,
      S₀.length = s - 1 ∧
      robustly_realizable H b S₀ ∧
      robust_agreement H b S₀ x₀ y₀ ∧
      ∀ S' : List (labeled_point X),
        proper_subsequence S' S₀ →
          ¬ robust_certificate H b S' x₀ y₀) := by
  constructor
  · exact short_robust_certificate_upper_bound H b s S x y hnum ⟨hreal, hagree⟩
  · exact sharp_robust_certificate_lower_bound H b s hnum

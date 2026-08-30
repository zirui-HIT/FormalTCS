import Architect
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators
open MeasureTheory

@[blueprint "def:cool-matrix"
  (statement := /-- For positive integers $m$ and $n$, a matrix with $m$ rows and $n$ ordered columns is represented as a family $A=(a_j)_{j\in\operatorname{Fin}(n)}$, where each column $a_j$ is a vector in $\mathbb{R}^m$. -/)
  (title := /-- Column representation of a real matrix -/)
  (latexEnv := "definition")]
abbrev cool_matrix (m n : ℕ) := Fin n → Fin m → ℝ

@[blueprint "def:cool-gaussian-column-measure"
  (statement := /-- The standard Gaussian law on $\mathbb{R}^m$ is the finite product of $m$ copies of $\mathcal{N}(0,1)$. -/)
  (title := /-- Standard Gaussian column law -/)
  (latexEnv := "definition")]
noncomputable def cool_gaussian_column_measure (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi fun _ => ProbabilityTheory.gaussianReal 0 1

@[blueprint "def:cool-gaussian-matrix-measure"
  (statement := /-- The law of an $m\times n$ standard Gaussian matrix is the finite product, over its $n$ ordered columns, of the standard Gaussian law on $\mathbb{R}^m$. -/)
  (title := /-- Independent Gaussian matrix law -/)
  (latexEnv := "definition")]
noncomputable def cool_gaussian_matrix_measure (m n : ℕ) : Measure (cool_matrix m n) :=
  Measure.pi fun _ => cool_gaussian_column_measure m

@[blueprint "def:cool-initial-block-length"
  (statement := /-- For parameters $n,m,B,K\in\mathbb{N}$, the initial block of the cooling schedule has length $n-Km\log_2 B$, with subtraction taken in $\mathbb{N}$. -/)
  (title := /-- Length of the initial cooling block -/)
  (latexEnv := "definition")]
def cool_initial_block_length (n m B K : ℕ) : ℕ :=
  n - K * m * Nat.log2 B

@[blueprint "def:cool-temperature"
  (statement := /-- At time $j<n$, the cooling temperature is $B$ on the initial block.  Thereafter it is divided by $2$ after each block of $Km$ samples, so the successive temperatures are $B/2,B/4,\ldots,1$. -/)
  (title := /-- COOL temperature schedule -/)
  (latexEnv := "definition")]
def cool_temperature (n m B K : ℕ) (j : Fin n) : ℕ :=
  if j.1 < cool_initial_block_length n m B K then
    B
  else
    B / 2 ^ (1 + (j.1 - cool_initial_block_length n m B K) / (K * m))

@[blueprint "def:cool-column"
  (statement := /-- The $j$th column of a matrix $A$ is regarded as an element of the Euclidean space $\mathbb{R}^m$. -/)
  (title := /-- Euclidean realization of a matrix column -/)
  (latexEnv := "definition")]
noncomputable def cool_column {m n : ℕ} (A : cool_matrix m n) (j : Fin n) :
    EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm (A j)

@[blueprint "def:cool-state"
  (statement := /-- Starting from $y_0=0$, the COOL state compares $\lVert y_t-b_ta_t\rVert_2$ and $\lVert y_t+b_ta_t\rVert_2$ and chooses the state of smaller Euclidean norm.  After all $n$ columns have been processed, the state remains fixed. -/)
  (title := /-- Recursive state of the COOL algorithm -/)
  (latexEnv := "definition")]
noncomputable def cool_state (n m B K : ℕ) (A : cool_matrix m n) :
    ℕ → EuclideanSpace ℝ (Fin m)
  | 0 => 0
  | t + 1 =>
      if ht : t < n then
        let j : Fin n := ⟨t, ht⟩
        let y := cool_state n m B K A t
        let a := cool_column A j
        let b : ℝ := cool_temperature n m B K j
        if ‖y - b • a‖ ≤ ‖y + b • a‖ then y - b • a else y + b • a
      else
        cool_state n m B K A t

@[blueprint "def:cool-output"
  (statement := /-- The $j$th coordinate output by COOL is $-b_j$ when the update $y_j-b_ja_j$ is selected and is $b_j$ when the update $y_j+b_ja_j$ is selected. -/)
  (title := /-- Coordinate output of the COOL algorithm -/)
  (latexEnv := "definition")]
noncomputable def cool_output (n m B K : ℕ) (A : cool_matrix m n) (j : Fin n) : ℝ :=
  let y := cool_state n m B K A j.1
  let a := cool_column A j
  let b : ℝ := cool_temperature n m B K j
  if ‖y - b • a‖ ≤ ‖y + b • a‖ then -b else b

@[blueprint "def:cool-output-vector"
  (statement := /-- The coordinate function produced by COOL is regarded as a vector in the Euclidean space $\mathbb{R}^n$. -/)
  (title := /-- Euclidean COOL output vector -/)
  (latexEnv := "definition")]
noncomputable def cool_output_vector (n m B K : ℕ) (A : cool_matrix m n) :
    EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (cool_output n m B K A)

@[blueprint "def:cool-matrix-vector"
  (statement := /-- For a column family $A=(a_j)_{j<n}$ and a vector $x\in\mathbb{R}^n$, define $Ax=\sum_{j<n}x_ja_j\in\mathbb{R}^m$. -/)
  (title := /-- Matrix--vector product in column form -/)
  (latexEnv := "definition")]
noncomputable def cool_matrix_vector {m n : ℕ} (A : cool_matrix m n) (x : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm fun i => ∑ j, A j i * x j

@[blueprint "def:cool-contraction-ratio"
  (statement := /-- The contraction ratio of $A$ at $x$ is $\lVert Ax\rVert_2/\lVert x\rVert_2$. -/)
  (title := /-- Euclidean contraction ratio -/)
  (latexEnv := "definition")]
noncomputable def cool_contraction_ratio {m n : ℕ} (A : cool_matrix m n) (x : Fin n → ℝ) : ℝ :=
  ‖cool_matrix_vector A x‖ /
    ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x‖

@[blueprint "def:cool-bad-event"
  (statement := /-- For $C>0$, the bad event consists of the Gaussian matrices for which the output $x$ of COOL satisfies
  \[
    \frac{\lVert Ax\rVert_2}{\lVert x\rVert_2}>
    C\frac{m}{B\sqrt n}.
  \] -/)
  (title := /-- Bad contraction event -/)
  (latexEnv := "definition")]
noncomputable def cool_bad_event (n m B K : ℕ) (C : ℝ) : Set (cool_matrix m n) :=
  {A | cool_contraction_ratio A (cool_output n m B K A) >
    C * (m : ℝ) / ((B : ℝ) * Real.sqrt (n : ℝ))}

@[blueprint "def:cool-constant-block"
  (statement := /-- A time interval $[s,s+\ell)$ is a constant-temperature block at temperature $b$ when it lies within the first $n$ steps and every index in that interval has cooling temperature $b$. -/)
  (title := /-- Constant-temperature block -/)
  (latexEnv := "definition")]
def cool_constant_block (n m B K start length b : ℕ) : Prop :=
  start + length ≤ n ∧
    ∀ j : Fin n, start ≤ j.1 → j.1 < start + length →
      cool_temperature n m B K j = b

@[blueprint "lem:cool-gaussian-columns-independent"
  (statement := /-- For every $m,n\in\mathbb{N}$, the coordinate projections $A\mapsto a_j$ are independent random vectors under the product Gaussian matrix law. -/)
  (proof := /-- By \,\cref{def:cool-gaussian-column-measure}, each column law is a probability measure, since it is a finite product of standard Gaussian probability measures.  By \,\cref{def:cool-gaussian-matrix-measure}, the matrix law is the finite product of these column laws.  The coordinate projections on a finite product probability space are independent; applying this result to the measurable identity map on each column gives the assertion. -/)
  (title := /-- Independence of the Gaussian columns -/)
  (latexEnv := "lemma")]
lemma cool_gaussian_columns_independent (m n : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun j (A : cool_matrix m n) => A j)
      (cool_gaussian_matrix_measure m n) := by
  letI : IsProbabilityMeasure (cool_gaussian_column_measure m) := by
    unfold cool_gaussian_column_measure
    infer_instance
  simpa [cool_gaussian_matrix_measure] using
    (ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : Fin n => cool_gaussian_column_measure m)
      (X := fun _ => id)
      (fun _ => measurable_id.aemeasurable))

@[blueprint "def:cool-type-a-comparison"
  (statement := /-- Let $(\Omega,\mu)$ be a measure space and let $m\in\mathbb{N}$.  A measurable random variable $X\colon\Omega\to\mathbb{R}$ is a type-$A$ comparison variable in dimension $m$ if, for every $u\ge 0$,
  \[
    \mu\{X>\sqrt m+u\}\le 2e^{-u^2/2}.
  \]
  This is the uniform upper-tail contract used for a possible outward COOL increment while the state norm is below $2bm$. -/)
  (title := /-- Type-$A$ comparison-variable contract -/)
  (latexEnv := "definition")]
def cool_type_a_comparison {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (m : ℕ) (X : Ω → ℝ) : Prop :=
  Measurable X ∧
    ∀ u : ℝ, 0 ≤ u →
      μ.real {ω | Real.sqrt (m : ℝ) + u < X ω} ≤
        2 * Real.exp (-(u ^ 2) / 2)

@[blueprint "def:cool-type-b-comparison"
  (statement := /-- Let $(\Omega,\mu)$ be a measure space.  A measurable random variable $X\colon\Omega\to\mathbb{R}$ is a type-$B$ comparison variable if, for every $t\in[0,1]$, the function
  \[
    \omega\longmapsto e^{t(1/4-X(\omega))}
  \]
  is integrable with respect to $\mu$ and its lower-tail moment-generating function satisfies
  \[
    \mathbb{E}_{\mu}\!\left[e^{t(1/4-X)}\right]\le e^{2t^2}
    \qquad (0\le t\le 1).
  \]
  Thus the expectation is a genuine finite exponential moment, rather than the value assigned by the Bochner integral to a non-integrable function.  In particular, this contract records a uniform positive inward drift of at least $1/4$ together with the subexponential lower-tail control needed for sums of independent copies. -/)
  (title := /-- Type-$B$ comparison-variable contract -/)
  (latexEnv := "definition")]
def cool_type_b_comparison {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  Measurable X ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      MeasureTheory.Integrable
          (fun ω => Real.exp (t * ((1 / 4 : ℝ) - X ω))) μ ∧
        ProbabilityTheory.mgf (fun ω => (1 / 4 : ℝ) - X ω) μ t ≤
          Real.exp (2 * t ^ 2)

@[blueprint "lem:cool-gaussian-column-rotation"
  (statement := /-- For every $m\in\mathbb N$, conjugating a linear isometric automorphism of Euclidean $m$-space by the canonical coordinate equivalence preserves the product standard-Gaussian measure on $\mathbb R^m$. -/)
  (proof := /-- By \cref{def:cool-gaussian-column-measure}, the column law is the product of $m$ standard real Gaussian measures.  Its pushforward under the inverse coordinate equivalence is the standard Gaussian measure on Euclidean space.  The latter is invariant under every linear isometric automorphism, and pushing forward again by the coordinate equivalence recovers the original product measure. -/)
  (title := /-- Orthogonal invariance of the Gaussian column law -/)
  (latexEnv := "lemma")]
lemma cool_gaussian_column_rotation (m : ℕ)
    (U : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) :
    Measure.map
        (fun x : Fin m → ℝ =>
          (EuclideanSpace.equiv (Fin m) ℝ)
            (U ((EuclideanSpace.equiv (Fin m) ℝ).symm x)))
        (cool_gaussian_column_measure m) =
      cool_gaussian_column_measure m := by
  unfold cool_gaussian_column_measure
  let e := EuclideanSpace.equiv (Fin m) ℝ
  change Measure.map (fun x => e (U (e.symm x)))
      (Measure.pi fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1) =
    Measure.pi fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1
  have hmap :
      Measure.map e.symm
          (Measure.pi fun _ : Fin m =>
            ProbabilityTheory.gaussianReal 0 1) =
        ProbabilityTheory.stdGaussian
          (EuclideanSpace ℝ (Fin m)) := by
    have he :
        (e.symm : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) =
          fun x => WithLp.toLp 2 x := by
      funext x
      rfl
    rw [he]
    exact ProbabilityTheory.map_pi_eq_stdGaussian
  calc
    Measure.map (fun x => e (U (e.symm x)))
        (Measure.pi fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1) =
      Measure.map e
        (Measure.map U
          (Measure.map e.symm
            (Measure.pi fun _ : Fin m =>
              ProbabilityTheory.gaussianReal 0 1))) := by
        rw [Measure.map_map, Measure.map_map]
        · rfl
        all_goals fun_prop
    _ = Measure.map e
        (Measure.map U
          (ProbabilityTheory.stdGaussian
            (EuclideanSpace ℝ (Fin m)))) := by
      rw [hmap]
    _ = Measure.map e
        (ProbabilityTheory.stdGaussian
          (EuclideanSpace ℝ (Fin m))) := by
      rw [ProbabilityTheory.stdGaussian_map]
    _ = Measure.pi fun _ : Fin m =>
        ProbabilityTheory.gaussianReal 0 1 := by
      rw [← hmap, Measure.map_map]
      · simp
      all_goals fun_prop

@[blueprint "lem:cool-predictable-gaussian-full-rotation"
  (statement := /-- Let every column $j<n$ of a standard Gaussian matrix be acted on by a linear isometric automorphism that depends only on the columns preceding $j$.  If the resulting matrix-valued map is Borel measurable, then it preserves the product standard-Gaussian matrix measure. -/)
  (proof := /-- Induct on the number of columns.  Split a matrix measurably into its initial segment and last column.  The induction hypothesis preserves the product law of the initial segment.  Conditional on that segment, predictability makes the last isometry fixed, so \cref{lem:cool-gaussian-column-rotation} shows that its action preserves the last-column law.  The measure-preserving skew-product theorem combines these facts, and conjugating by the measurable splitting equivalence gives the asserted matrix law. -/)
  (title := /-- Predictable rotations preserve a full Gaussian matrix law -/)
  (latexEnv := "lemma")]
lemma cool_predictable_gaussian_full_rotation :
    ∀ (m n : ℕ)
      (U : Fin n → cool_matrix m n →
        (EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m))),
      Measurable
        (fun A : cool_matrix m n => fun j =>
          (EuclideanSpace.equiv (Fin m) ℝ)
            (U j A ((EuclideanSpace.equiv (Fin m) ℝ).symm (A j)))) →
      (∀ (j : Fin n) (A A' : cool_matrix m n),
        (∀ k : Fin n, k.1 < j.1 → A k = A' k) →
        U j A = U j A') →
      MeasurePreserving
        (fun A : cool_matrix m n => fun j =>
          (EuclideanSpace.equiv (Fin m) ℝ)
            (U j A ((EuclideanSpace.equiv (Fin m) ℝ).symm (A j))))
        (cool_gaussian_matrix_measure m n)
        (cool_gaussian_matrix_measure m n) := by
  intro m n
  induction n with
  | zero =>
      intro U hmeas hpast
      have hfun :
          (fun A : cool_matrix m 0 => fun j =>
            (EuclideanSpace.equiv (Fin m) ℝ)
              (U j A ((EuclideanSpace.equiv (Fin m) ℝ).symm (A j)))) =
            id := by
        funext A
        ext j
        exact Fin.elim0 j
      rw [hfun]
      exact MeasurePreserving.id
        (μ := cool_gaussian_matrix_measure m 0)
  | succ n ih =>
      intro U hmeas hpast
      let μ := cool_gaussian_column_measure m
      let split :
          cool_matrix m (n + 1) ≃ᵐ
            (cool_matrix m n × (Fin m → ℝ)) :=
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => Fin m → ℝ) (Fin.last n)).trans
            MeasurableEquiv.prodComm
      have split_fst (A : cool_matrix m (n + 1)) :
          (split A).1 = Fin.init A := by
        simp [split, MeasurableEquiv.piFinSuccAbove, Fin.snocEquiv,
          MeasurableEquiv.prodComm, Equiv.prodComm]
      have split_snd (A : cool_matrix m (n + 1)) :
          (split A).2 = A (Fin.last n) := by
        simp [split, MeasurableEquiv.piFinSuccAbove, Fin.snocEquiv,
          MeasurableEquiv.prodComm, Equiv.prodComm]
      have split_symm_cast (A : cool_matrix m n) (x : Fin m → ℝ)
          (j : Fin n) :
          split.symm (A, x) j.castSucc = A j := by
        have h := congrFun (split_fst (split.symm (A, x))) j
        rw [split.apply_symm_apply] at h
        change Fin.init (split.symm (A, x)) j = A j
        exact h.symm
      have split_symm_last (A : cool_matrix m n) (x : Fin m → ℝ) :
          split.symm (A, x) (Fin.last n) = x := by
        have h := split_snd (split.symm (A, x))
        simpa using h.symm
      let T : cool_matrix m (n + 1) → cool_matrix m (n + 1) :=
        fun A j =>
          (EuclideanSpace.equiv (Fin m) ℝ)
            (U j A ((EuclideanSpace.equiv (Fin m) ℝ).symm (A j)))
      letI : IsProbabilityMeasure μ := by
        dsimp [μ, cool_gaussian_column_measure]
        infer_instance
      letI : IsProbabilityMeasure
          (cool_gaussian_matrix_measure m n) := by
        unfold cool_gaussian_matrix_measure
        infer_instance
      letI : IsProbabilityMeasure
          (cool_gaussian_matrix_measure m (n + 1)) := by
        unfold cool_gaussian_matrix_measure
        infer_instance
      have hsplit :
          MeasurePreserving split
            (cool_gaussian_matrix_measure m (n + 1))
            ((cool_gaussian_matrix_measure m n).prod μ) := by
        have h :=
          (MeasureTheory.Measure.measurePreserving_swap.comp
            (MeasureTheory.measurePreserving_piFinSuccAbove
              (fun _ : Fin (n + 1) => cool_gaussian_column_measure m)
              (Fin.last n)))
        have hfun :
            (split : cool_matrix m (n + 1) →
              cool_matrix m n × (Fin m → ℝ)) =
              Prod.swap ∘
                (MeasurableEquiv.piFinSuccAbove
                  (fun _ : Fin (n + 1) => Fin m → ℝ)
                  (Fin.last n)) := by
          funext A
          simp [split, MeasurableEquiv.prodComm, Equiv.prodComm,
            Function.comp_def]
        rw [hfun]
        simpa [μ, cool_gaussian_matrix_measure] using h
      let U' : Fin n → cool_matrix m n →
          (EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ]
            EuclideanSpace ℝ (Fin m)) :=
        fun j A => U j.castSucc (split.symm (A, 0))
      have hU'past :
          ∀ (j : Fin n) (A A' : cool_matrix m n),
            (∀ k : Fin n, k.1 < j.1 → A k = A' k) →
            U' j A = U' j A' := by
        intro j A A' hAA
        apply hpast j.castSucc
        intro k hk
        let k' : Fin n := ⟨k.1, lt_trans hk j.isLt⟩
        have hk_eq : k = k'.castSucc := Fin.ext rfl
        rw [hk_eq]
        rw [split_symm_cast, split_symm_cast]
        apply hAA k'
        simpa [k'] using hk
      have hU'meas :
          Measurable
            (fun A : cool_matrix m n => fun j =>
              (EuclideanSpace.equiv (Fin m) ℝ)
                (U' j A
                  ((EuclideanSpace.equiv (Fin m) ℝ).symm (A j)))) := by
        have hjoin :
            Measurable
              (fun A : cool_matrix m n => split.symm (A, 0)) :=
          split.symm.measurable.comp
            (measurable_id.prodMk measurable_const)
        have hcomp := hmeas.comp hjoin
        rw [measurable_pi_iff]
        intro j
        convert (measurable_pi_apply j.castSucc).comp hcomp using 1
        funext A
        simp only [Function.comp_apply, U', split_symm_cast]
      have hprefix :
          MeasurePreserving
            (fun A : cool_matrix m n => fun j =>
              (EuclideanSpace.equiv (Fin m) ℝ)
                (U' j A
                  ((EuclideanSpace.equiv (Fin m) ℝ).symm (A j))))
            (cool_gaussian_matrix_measure m n)
            (cool_gaussian_matrix_measure m n) :=
        ih U' hU'meas hU'past
      let g : cool_matrix m n → (Fin m → ℝ) → (Fin m → ℝ) :=
        fun A x => T (split.symm (A, x)) (Fin.last n)
      have hgmeas : Measurable (Function.uncurry g) := by
        have hcomp := hmeas.comp split.symm.measurable
        convert (measurable_pi_apply (Fin.last n)).comp hcomp using 1
        rfl
      have hgmap :
          ∀ A : cool_matrix m n, Measure.map (g A) μ = μ := by
        intro A
        have hrot :
            Measure.map
                (fun x : Fin m → ℝ =>
                  (EuclideanSpace.equiv (Fin m) ℝ)
                    (U (Fin.last n) (split.symm (A, 0))
                      ((EuclideanSpace.equiv (Fin m) ℝ).symm x)))
                μ = μ := by
          simpa [μ] using
            cool_gaussian_column_rotation m
              (U (Fin.last n) (split.symm (A, 0)))
        calc
          Measure.map (g A) μ =
              Measure.map
                (fun x : Fin m → ℝ =>
                  (EuclideanSpace.equiv (Fin m) ℝ)
                    (U (Fin.last n) (split.symm (A, 0))
                      ((EuclideanSpace.equiv (Fin m) ℝ).symm x)))
                μ := by
            apply Measure.map_congr
            filter_upwards [] with x
            have hU :
                U (Fin.last n) (split.symm (A, x)) =
                  U (Fin.last n) (split.symm (A, 0)) := by
              apply hpast (Fin.last n)
              intro k hk
              let k' : Fin n := ⟨k.1, by simpa using hk⟩
              have hk_eq : k = k'.castSucc := Fin.ext rfl
              rw [hk_eq]
              simp only [split_symm_cast]
            simp only [g, T, hU, split_symm_last]
          _ = μ := hrot
      have hskew :
          MeasurePreserving
            (fun p : cool_matrix m n × (Fin m → ℝ) =>
              ((fun A : cool_matrix m n => fun j =>
                (EuclideanSpace.equiv (Fin m) ℝ)
                  (U' j A
                    ((EuclideanSpace.equiv (Fin m) ℝ).symm (A j)))) p.1,
                g p.1 p.2))
            ((cool_gaussian_matrix_measure m n).prod μ)
            ((cool_gaussian_matrix_measure m n).prod μ) := by
        exact hprefix.skew_product hgmeas
          (Filter.Eventually.of_forall hgmap)
      have hconj :=
        (hsplit.symm split).comp (hskew.comp hsplit)
      refine hconj.congr hmeas ?_
      filter_upwards [] with A
      apply split.injective
      simp only [Function.comp_apply, split.apply_symm_apply]
      apply Prod.ext
      · funext j
        have hU :
            U j.castSucc A =
              U j.castSucc (split.symm ((split A).1, 0)) := by
          apply hpast j.castSucc
          intro k hk
          let k' : Fin n := ⟨k.1, lt_trans hk j.isLt⟩
          have hk_eq : k = k'.castSucc := Fin.ext rfl
          rw [hk_eq]
          simp only [split_symm_cast, split_fst]
          rw [Fin.init_def]
        rw [split_fst]
        simp only [Prod.fst, split_fst]
        have hinit : Fin.init (T A) j = T A j.castSucc := by
          rfl
        rw [hinit]
        change
          (EuclideanSpace.equiv (Fin m) ℝ)
              (U' j (Fin.init A)
                ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.init A j))) =
            T A j.castSucc
        simp only [U', T, split_symm_cast, split_fst]
        rw [split_fst] at hU
        rw [← hU]
        rfl
      · simp only [Prod.snd, split_snd, split_fst]
        change g (Fin.init A) (A (Fin.last n)) = T A (Fin.last n)
        rw [← split_fst A, ← split_snd A]
        change T (split.symm (split A)) (Fin.last n) =
          T A (Fin.last n)
        rw [split.symm_apply_apply]

@[blueprint "lem:cool-predictable-gaussian-rotation"
  (statement := /-- Let $m,n,\ell\in\mathbb N$, let $j_0<\cdots<j_{\ell-1}<n$ be column indices, and, for every $i<\ell$ and every matrix $A$, let $R_i(A)$ be a linear isometric automorphism of $\mathbb R^m$.  Suppose that $A\mapsto R_i(A)a_{j_i}$ is Borel measurable for every $i<\ell$, and that $R_i(A)=R_i(A')$ whenever $A$ and $A'$ agree in every column $a_j$ with $j<j_i$.  Then the triangular transformation
  \[
    A\longmapsto \bigl(R_i(A)a_{j_i}\bigr)_{i<\ell}
  \]
  pushes the product standard-Gaussian matrix law forward to the product law of $\ell$ standard-Gaussian vectors.  In particular, its coordinate vectors are jointly independent and each has the standard Gaussian law on $\mathbb R^m$. -/)
  (proof := /-- The strict ordering of the selected indices makes $i\mapsto j_i$ injective.  Extend the family $R_i$ to all $n$ columns by assigning the identity isometry to every unselected column.  The stated measurability and predictability hypotheses imply the corresponding hypotheses for this full triangular transformation, so \cref{lem:cool-predictable-gaussian-full-rotation} shows that it preserves the $n$-column product Gaussian law.  By \cref{lem:cool-gaussian-columns-independent}, restriction of the original coordinate family along the injective map $i\mapsto j_i$ is independent; since every selected coordinate has the standard Gaussian column law, its joint law is the $\ell$-fold product law.  Composing the full measure-preserving transformation with this coordinate restriction gives the asserted pushforward equality.  Mapping that equality through each coordinate projection identifies every transformed marginal with the standard Gaussian column law, and the finite-product characterization of independence then proves that the transformed coordinate family is jointly independent. -/)
  (title := /-- Predictable rotations preserve the Gaussian product law -/)
  (latexEnv := "lemma")]
lemma cool_predictable_gaussian_rotation :
    ∀ (m n length : ℕ) (index : Fin length → Fin n)
      (R : Fin length → cool_matrix m n →
        (EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m))),
      (∀ i k : Fin length, i.1 < k.1 → (index i).1 < (index k).1) →
      (∀ i : Fin length,
        Measurable (fun A : cool_matrix m n =>
          (EuclideanSpace.equiv (Fin m) ℝ)
            (R i A ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (A (index i)))))) →
      (∀ (i : Fin length) (A A' : cool_matrix m n),
        (∀ j : Fin n, j.1 < (index i).1 → A j = A' j) →
        R i A = R i A') →
      Measure.map
          (fun A : cool_matrix m n => fun i =>
            (EuclideanSpace.equiv (Fin m) ℝ)
              (R i A ((EuclideanSpace.equiv (Fin m) ℝ).symm
                (A (index i)))))
          (cool_gaussian_matrix_measure m n) =
        cool_gaussian_matrix_measure m length ∧
      ProbabilityTheory.iIndepFun
        (fun i : Fin length => fun A : cool_matrix m n =>
          (EuclideanSpace.equiv (Fin m) ℝ)
            (R i A ((EuclideanSpace.equiv (Fin m) ℝ).symm
              (A (index i)))))
        (cool_gaussian_matrix_measure m n) := by
  classical
  intro m n length index R horder hmeas hpast
  have hindex : Function.Injective index := by
    intro i k hik
    apply Fin.ext
    have hv : (index i).1 = (index k).1 :=
      congrArg Fin.val hik
    by_contra hne
    rcases lt_or_gt_of_ne hne with hik' | hki'
    · have := horder i k hik'
      omega
    · have := horder k i hki'
      omega
  let U : Fin n → cool_matrix m n →
      (EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin m)) :=
    fun j A =>
      if h : ∃ i : Fin length, index i = j then
        R (Classical.choose h) A
      else LinearIsometryEquiv.refl ℝ _
  let T : cool_matrix m n → cool_matrix m n :=
    fun A j =>
      (EuclideanSpace.equiv (Fin m) ℝ)
        (U j A ((EuclideanSpace.equiv (Fin m) ℝ).symm (A j)))
  have hchosen (i : Fin length) :
      Classical.choose
          (show ∃ k : Fin length, index k = index i from ⟨i, rfl⟩) = i := by
    let hi : ∃ k : Fin length, index k = index i := ⟨i, rfl⟩
    change Classical.choose hi = i
    apply hindex
    exact Classical.choose_spec hi
  have hTmeas : Measurable T := by
    rw [measurable_pi_iff]
    intro j
    by_cases hj : ∃ i : Fin length, index i = j
    · let i := Classical.choose hj
      have hi : index i = j := Classical.choose_spec hj
      have hm := hmeas i
      simpa [T, U, hj, i, hi] using hm
    · convert (measurable_pi_apply j) using 1
      funext A
      simp [T, U, hj]
      exact
        (EuclideanSpace.equiv (Fin m) ℝ).apply_symm_apply (A j)
  have hUpast :
      ∀ (j : Fin n) (A A' : cool_matrix m n),
        (∀ k : Fin n, k.1 < j.1 → A k = A' k) →
        U j A = U j A' := by
    intro j A A' hAA
    by_cases hj : ∃ i : Fin length, index i = j
    · simp only [U, dif_pos hj]
      apply hpast (Classical.choose hj)
      intro k hk
      apply hAA k
      rw [Classical.choose_spec hj] at hk
      exact hk
    · simp [U, hj]
  have hfull :
      MeasurePreserving T
        (cool_gaussian_matrix_measure m n)
        (cool_gaussian_matrix_measure m n) := by
    simpa [T] using
      cool_predictable_gaussian_full_rotation m n U hTmeas hUpast
  let select : cool_matrix m n → cool_matrix m length :=
    fun A i => A (index i)
  have hselect : Measurable select := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply (index i)
  letI : IsProbabilityMeasure (cool_gaussian_column_measure m) := by
    unfold cool_gaussian_column_measure
    infer_instance
  letI : IsProbabilityMeasure
      (cool_gaussian_matrix_measure m n) := by
    unfold cool_gaussian_matrix_measure
    infer_instance
  letI : IsProbabilityMeasure
      (cool_gaussian_matrix_measure m length) := by
    unfold cool_gaussian_matrix_measure
    infer_instance
  have hselected_indep :
      ProbabilityTheory.iIndepFun
        (fun i : Fin length => fun A : cool_matrix m n =>
          A (index i))
        (cool_gaussian_matrix_measure m n) :=
    (cool_gaussian_columns_independent m n).precomp hindex
  have hselected_law :
      Measure.map select (cool_gaussian_matrix_measure m n) =
        cool_gaussian_matrix_measure m length := by
    have hlaw :
        ∀ i : Fin length,
          ProbabilityTheory.HasLaw
            (fun A : cool_matrix m n => A (index i))
            (cool_gaussian_column_measure m)
            (cool_gaussian_matrix_measure m n) := by
      intro i
      exact
        { aemeasurable := (measurable_pi_apply (index i)).aemeasurable
          map_eq :=
            (MeasureTheory.measurePreserving_eval
              (fun _ : Fin n => cool_gaussian_column_measure m)
              (index i)).map_eq }
    simpa [select, cool_gaussian_matrix_measure] using
      (hselected_indep.hasLaw_pi hlaw).map_eq
  let F : Fin length → cool_matrix m n → (Fin m → ℝ) :=
    fun i A =>
      (EuclideanSpace.equiv (Fin m) ℝ)
        (R i A ((EuclideanSpace.equiv (Fin m) ℝ).symm
          (A (index i))))
  have hFT :
      (fun A : cool_matrix m n => fun i => F i A) =
        select ∘ T := by
    funext A i
    have hi :
        ∃ k : Fin length, index k = index i := ⟨i, rfl⟩
    have hc : Classical.choose hi = i := hchosen i
    simp [F, select, T, U, hi, hc]
  have hmap :
      Measure.map (fun A : cool_matrix m n => fun i => F i A)
          (cool_gaussian_matrix_measure m n) =
        cool_gaussian_matrix_measure m length := by
    rw [hFT]
    calc
      Measure.map (select ∘ T)
          (cool_gaussian_matrix_measure m n) =
        Measure.map select
          (Measure.map T (cool_gaussian_matrix_measure m n)) := by
            rw [Measure.map_map hselect hfull.measurable]
      _ = Measure.map select
          (cool_gaussian_matrix_measure m n) := by
            rw [hfull.map_eq]
      _ = cool_gaussian_matrix_measure m length := hselected_law
  constructor
  · simpa [F] using hmap
  · have hmarg :
        ∀ i : Fin length,
          Measure.map (F i) (cool_gaussian_matrix_measure m n) =
            cool_gaussian_column_measure m := by
      intro i
      calc
        Measure.map (F i) (cool_gaussian_matrix_measure m n) =
            Measure.map (fun X : cool_matrix m length => X i)
              (Measure.map (fun A : cool_matrix m n => fun k => F k A)
                (cool_gaussian_matrix_measure m n)) := by
                  rw [Measure.map_map]
                  · rfl
                  · exact (measurable_pi_apply i)
                  · simpa [F] using measurable_pi_iff.mpr hmeas
        _ = Measure.map (fun X : cool_matrix m length => X i)
              (cool_gaussian_matrix_measure m length) := by
                rw [hmap]
        _ = cool_gaussian_column_measure m :=
          (MeasureTheory.measurePreserving_eval
            (fun _ : Fin length => cool_gaussian_column_measure m) i).map_eq
    apply
      (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
        (fun i => (hmeas i).aemeasurable)).2
    change
      Measure.map (fun A : cool_matrix m n => fun i => F i A)
          (cool_gaussian_matrix_measure m n) =
        Measure.pi (fun i =>
          Measure.map (F i) (cool_gaussian_matrix_measure m n))
    calc
      Measure.map (fun A : cool_matrix m n => fun i => F i A)
          (cool_gaussian_matrix_measure m n) =
        cool_gaussian_matrix_measure m length := hmap
      _ = Measure.pi (fun i =>
          Measure.map (F i) (cool_gaussian_matrix_measure m n)) := by
        change
          Measure.pi (fun _ : Fin length =>
            cool_gaussian_column_measure m) =
          Measure.pi (fun i =>
            Measure.map (F i) (cool_gaussian_matrix_measure m n))
        exact congrArg
          (fun ν : Fin length → Measure (Fin m → ℝ) => Measure.pi ν)
          (funext fun i => (hmarg i).symm)

@[blueprint "lem:cool-standard-gaussian-norm-tail"
  (statement := /-- If $Z$ has the product standard-Gaussian law on $\mathbb R^m$, then its Euclidean norm is a type-$A$ comparison variable in dimension $m$; explicitly, for every $u\ge0$,
  \[
    \mathbb P\!\left(\lVert Z\rVert_2>\sqrt m+u\right)
      \le 2e^{-u^2/2}.
  \] -/)
  (proof := /-- Unfold the product Gaussian law and the type-$A$ contract from
  \cref{def:cool-gaussian-column-measure,def:cool-type-a-comparison}.  The
  Euclidean norm is Borel measurable.  The case $u=0$ follows because a
  probability is at most one, and the case $m=0<u$ follows because the unique
  vector in dimension zero has norm zero.

  Suppose that $m>0$ and $u>0$.  For $t<1/2$, the standard Gaussian density
  and the Gaussian integral give
  \[
    \mathbb E e^{tZ_1^2}
      =\frac1{\sqrt{2\pi}}
        \int_{\mathbb R}e^{-(1/2-t)x^2}\,dx
      =\frac1{\sqrt{1-2t}}.
  \]
  The squared coordinate functions are measurable and independent under the
  finite product measure.  Hence their moment-generating functions factor,
  and
  \[
    \mathbb E e^{t\lVert Z\rVert_2^2}
      =\left(\frac1{\sqrt{1-2t}}\right)^m.
  \]

  Put $r=\sqrt m+u$ and $t=u/(2r)$.  Then $0<t<1/2$.  Since
  $\lVert Z\rVert_2>r$ implies
  $\sum_{i<m}Z_i^2\ge r^2$, the exponential Markov inequality yields
  \[
    \mathbb P(\lVert Z\rVert_2>r)
      \le e^{-tr^2}
        \left(\frac1{\sqrt{1-2t}}\right)^m.
  \]
  Set $a=1-2t=\sqrt m/r$.  The inequality
  $1-a^{-1}\le\log a$ for $a>0$ gives
  \[
    \log\frac1{\sqrt a}
      \le\frac{a^{-1}-1}{2}
      =\frac{u}{2\sqrt m}.
  \]
  Therefore the logarithm of the preceding upper bound is at most
  \[
    -\frac{ur}{2}+\frac{m u}{2\sqrt m}
      =-\frac{u^2}{2}.
  \]
  Exponentiation proves the stronger estimate $e^{-u^2/2}$, which is at most
  the required $2e^{-u^2/2}$. -/)
  (title := /-- Euclidean-norm tail of a standard Gaussian vector -/)
  (latexEnv := "lemma")]
lemma cool_standard_gaussian_norm_tail (m : ℕ) :
    cool_type_a_comparison (cool_gaussian_column_measure m) m
      (fun z => ‖(EuclideanSpace.equiv (Fin m) ℝ).symm z‖) := by
  refine ⟨by fun_prop, ?_⟩
  intro u hu
  have hmgf1 : ∀ t : ℝ, t < 1 / 2 →
      ProbabilityTheory.mgf (fun x : ℝ => x ^ 2)
        (ProbabilityTheory.gaussianReal 0 1) t =
        1 / Real.sqrt (1 - 2 * t) := by
    intro t ht
    unfold ProbabilityTheory.mgf
    rw [ProbabilityTheory.gaussianReal]
    norm_num
    rw [integral_withDensity_eq_integral_toReal_smul]
    · simp only [ProbabilityTheory.gaussianPDF, ENNReal.toReal_ofReal
          (ProbabilityTheory.gaussianPDFReal_nonneg 0 1 _), smul_eq_mul]
      simp only [ProbabilityTheory.gaussianPDFReal_def]
      norm_num
      have hb : 0 < 1 / 2 - t := sub_pos.mpr ht
      rw [show (fun x : ℝ =>
          (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ *
            Real.exp (-x ^ 2 / 2) * Real.exp (t * x ^ 2)) =
          (fun x : ℝ => (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ *
            Real.exp (-(1 / 2 - t) * x ^ 2)) by
        funext x
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring]
      rw [integral_const_mul, integral_gaussian]
      rw [Real.sqrt_div Real.pi_pos.le]
      rw [show 1 - 2 * t = 2 * (1 / 2 - t) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp [Real.sqrt_ne_zero'.mpr Real.pi_pos,
        Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2),
        Real.sqrt_ne_zero'.mpr hb]
    · exact ProbabilityTheory.measurable_gaussianPDF 0 1
    · exact Filter.Eventually.of_forall fun x =>
        lt_top_iff_ne_top.mpr
          (ProbabilityTheory.gaussianPDF_ne_top (μ := 0) (v := 1) (x := x))
  letI : IsProbabilityMeasure (cool_gaussian_column_measure m) := by
    unfold cool_gaussian_column_measure
    infer_instance
  rcases hu.eq_or_lt with rfl | hu
  · calc
      (cool_gaussian_column_measure m).real
          {ω | Real.sqrt (m : ℝ) + 0 <
            ‖(EuclideanSpace.equiv (Fin m) ℝ).symm ω‖} ≤ 1 :=
        measureReal_le_one
      _ ≤ 2 * Real.exp (-(0 : ℝ) ^ 2 / 2) := by norm_num
  · by_cases hm : m = 0
    · subst m
      simp only [Nat.cast_zero, Real.sqrt_zero, zero_add]
      have hz : ∀ z : Fin 0 → ℝ,
          ‖(EuclideanSpace.equiv (Fin 0) ℝ).symm z‖ = 0 := by
        intro z
        rw [show z = 0 from Subsingleton.elim _ _]
        simp
      simp_rw [hz]
      simp [not_lt_of_ge hu.le]
      positivity
    · have hmpos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
      have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmpos
      let r : ℝ := Real.sqrt (m : ℝ) + u
      have hr : 0 < r := by dsimp [r]; positivity
      let t : ℝ := u / (2 * r)
      have ht0 : 0 ≤ t := by dsimp [t]; positivity
      have ht : t < 1 / 2 := by
        dsimp [t]
        rw [div_lt_iff₀' (by positivity : (0 : ℝ) < 2 * r)]
        nlinarith
      let X : Fin m → (Fin m → ℝ) → ℝ := fun i z => z i ^ 2
      have hindep0 : ProbabilityTheory.iIndepFun
          (fun i : Fin m => fun z : Fin m → ℝ => z i)
          (cool_gaussian_column_measure m) := by
        unfold cool_gaussian_column_measure
        exact ProbabilityTheory.iIndepFun_pi
          (μ := fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)
          (X := fun _ => id)
          (fun _ => measurable_id.aemeasurable)
      have hindep : ProbabilityTheory.iIndepFun X
          (cool_gaussian_column_measure m) := by
        exact hindep0.comp (fun _ => fun x : ℝ => x ^ 2) (fun _ => by fun_prop)
      have hmeas : ∀ i, Measurable (X i) := by
        intro i
        fun_prop
      have hcoord : ∀ i, ProbabilityTheory.mgf (X i)
          (cool_gaussian_column_measure m) t =
          1 / Real.sqrt (1 - 2 * t) := by
        intro i
        change ProbabilityTheory.mgf
          ((fun x : ℝ => x ^ 2) ∘ fun z : Fin m → ℝ => z i)
            (cool_gaussian_column_measure m) t =
          1 / Real.sqrt (1 - 2 * t)
        rw [← ProbabilityTheory.mgf_map
          (Y := fun z : Fin m → ℝ => z i) (X := fun x : ℝ => x ^ 2)
          (μ := cool_gaussian_column_measure m) (t := t)
          (measurable_pi_apply i).aemeasurable
          ((by fun_prop : Measurable
            (fun x : ℝ => Real.exp (t * x ^ 2))).aestronglyMeasurable)]
        simp [cool_gaussian_column_measure, Measure.pi_map_eval]
        simpa only [one_div] using hmgf1 t ht
      have hmgfsum :
          ProbabilityTheory.mgf (∑ i : Fin m, X i)
            (cool_gaussian_column_measure m) t =
            (1 / Real.sqrt (1 - 2 * t)) ^ m := by
        rw [hindep.mgf_sum (t := t) hmeas Finset.univ]
        simp [hcoord]
      have hbase : 0 < 1 / Real.sqrt (1 - 2 * t) := by
        have : 0 < 1 - 2 * t := by linarith
        positivity
      have hint : Integrable
          (fun z : Fin m → ℝ =>
            Real.exp (t * (∑ i : Fin m, X i) z))
          (cool_gaussian_column_measure m) := by
        apply (ProbabilityTheory.mgf_pos_iff
          (X := ∑ i : Fin m, X i) (t := t)).mp
        rw [hmgfsum]
        positivity
      have hnorm : ∀ z : Fin m → ℝ,
          ‖(EuclideanSpace.equiv (Fin m) ℝ).symm z‖ ^ 2 =
            (∑ i : Fin m, X i) z := by
        intro z
        simpa [X] using
          EuclideanSpace.real_norm_sq_eq
            ((EuclideanSpace.equiv (Fin m) ℝ).symm z)
      have hsubset :
          {z : Fin m → ℝ |
            r < ‖(EuclideanSpace.equiv (Fin m) ℝ).symm z‖} ⊆
          {z : Fin m → ℝ | r ^ 2 ≤ (∑ i : Fin m, X i) z} := by
        intro z hz
        simp only [Set.mem_setOf_eq] at hz ⊢
        rw [← hnorm]
        nlinarith [norm_nonneg ((EuclideanSpace.equiv (Fin m) ℝ).symm z)]
      have hchern :
          (cool_gaussian_column_measure m).real
              {z : Fin m → ℝ | r ^ 2 ≤ (∑ i : Fin m, X i) z} ≤
            Real.exp (-t * r ^ 2) *
              (1 / Real.sqrt (1 - 2 * t)) ^ m := by
        simpa [hmgfsum] using
          (ProbabilityTheory.measure_ge_le_exp_mul_mgf
            (μ := cool_gaussian_column_measure m)
            (X := ∑ i : Fin m, X i) (t := t) (r ^ 2) ht0 hint)
      calc
        (cool_gaussian_column_measure m).real
            {z | Real.sqrt (m : ℝ) + u <
              ‖(EuclideanSpace.equiv (Fin m) ℝ).symm z‖} ≤
            (cool_gaussian_column_measure m).real
              {z | r ^ 2 ≤ (∑ i : Fin m, X i) z} := by
                exact measureReal_mono (by simpa [r] using hsubset)
                  (measure_ne_top _ _)
        _ ≤ Real.exp (-t * r ^ 2) *
              (1 / Real.sqrt (1 - 2 * t)) ^ m := hchern
        _ ≤ 2 * Real.exp (-u ^ 2 / 2) := by
          have ha : 0 < 1 - 2 * t := by linarith
          have haeq : 1 - 2 * t = Real.sqrt (m : ℝ) / r := by
            dsimp [t, r]
            field_simp [ne_of_gt hr]
            ring
          have hinv :
              (1 - 2 * t)⁻¹ - 1 = u / Real.sqrt (m : ℝ) := by
            rw [haeq]
            field_simp [ne_of_gt hr, ne_of_gt hsqrt]
            ring
          have hlog :
              Real.log (1 / Real.sqrt (1 - 2 * t)) ≤
                ((1 - 2 * t)⁻¹ - 1) / 2 := by
            rw [one_div, Real.log_inv, Real.log_sqrt ha.le]
            nlinarith [Real.one_sub_inv_le_log_of_pos ha]
          have hsqrt_sq :
              Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) :=
            Real.sq_sqrt hmpos.le
          have hexponent :
              -t * r ^ 2 +
                  (m : ℝ) *
                    Real.log (1 / Real.sqrt (1 - 2 * t)) ≤
                -u ^ 2 / 2 := by
            calc
              -t * r ^ 2 +
                    (m : ℝ) *
                      Real.log (1 / Real.sqrt (1 - 2 * t)) ≤
                  -t * r ^ 2 +
                    (m : ℝ) * (((1 - 2 * t)⁻¹ - 1) / 2) := by
                      gcongr
              _ = -u ^ 2 / 2 := by
                rw [hinv]
                dsimp [t, r]
                field_simp [ne_of_gt hsqrt]
                nlinarith
          rw [← Real.exp_log hbase, ← Real.exp_nat_mul, ← Real.exp_add]
          calc
            Real.exp
                (-t * r ^ 2 +
                  (m : ℝ) *
                    Real.log (1 / Real.sqrt (1 - 2 * t))) ≤
                Real.exp (-u ^ 2 / 2) :=
              Real.exp_le_exp.mpr hexponent
            _ ≤ 2 * Real.exp (-u ^ 2 / 2) := by
              nlinarith [Real.exp_pos (-u ^ 2 / 2)]

@[blueprint "lem:cool-gaussian-square-mgf"
  (statement := /-- For every real $t<1/2$, the moment-generating function of the square of a standard real Gaussian satisfies
  \[
    \mathbb E[e^{tZ^2}]=\frac{1}{\sqrt{1-2t}}.
  \] -/)
  (proof := /-- Expand the standard Gaussian measure using its density.  Combining the density exponential with $e^{tx^2}$ gives the Gaussian integral with coefficient $1/2-t>0$.  Evaluate that integral and simplify the square roots. -/)
  (title := /-- Moment-generating function of a squared Gaussian -/)
  (latexEnv := "lemma")]
lemma cool_gaussian_square_mgf : ∀ t : ℝ, t < 1 / 2 →
    ProbabilityTheory.mgf (fun x : ℝ => x ^ 2)
      (ProbabilityTheory.gaussianReal 0 1) t =
      1 / Real.sqrt (1 - 2 * t) := by
  intro t ht
  unfold ProbabilityTheory.mgf
  rw [ProbabilityTheory.gaussianReal]
  norm_num
  rw [integral_withDensity_eq_integral_toReal_smul]
  · simp only [ProbabilityTheory.gaussianPDF, ENNReal.toReal_ofReal
        (ProbabilityTheory.gaussianPDFReal_nonneg 0 1 _), smul_eq_mul]
    simp only [ProbabilityTheory.gaussianPDFReal_def]
    norm_num
    have hb : 0 < 1 / 2 - t := sub_pos.mpr ht
    rw [show (fun x : ℝ =>
        (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ *
          Real.exp (-x ^ 2 / 2) * Real.exp (t * x ^ 2)) =
        (fun x : ℝ => (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ *
          Real.exp (-(1 / 2 - t) * x ^ 2)) by
      funext x
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring]
    rw [integral_const_mul, integral_gaussian]
    rw [Real.sqrt_div Real.pi_pos.le]
    rw [show 1 - 2 * t = 2 * (1 / 2 - t) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp [Real.sqrt_ne_zero'.mpr Real.pi_pos,
      Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2),
      Real.sqrt_ne_zero'.mpr hb]
  · exact ProbabilityTheory.measurable_gaussianPDF 0 1
  · exact Filter.Eventually.of_forall fun x =>
      lt_top_iff_ne_top.mpr
        (ProbabilityTheory.gaussianPDF_ne_top (μ := 0) (v := 1) (x := x))

@[blueprint "lem:cool-standard-gaussian-abs-mean-lower"
  (statement := /-- If $Z$ is a standard real Gaussian, then $\mathbb E|Z|\ge 1/2$ and $\mathbb E[Z^2]=1$. -/)
  (proof := /-- The pointwise polynomial inequality $|x|\ge x^2-(4/27)x^4$ follows by factoring its difference as a nonnegative multiple of $|x|(2|x|-3)^2(|x|+3)$.  The standard-Gaussian second moment is obtained from its variance, while the fourth moment is obtained from the fourth derivative at zero of its moment-generating function; these moments are $1$ and $3$.  Integrating the pointwise inequality therefore gives $\mathbb E|Z|\ge 1-4/9=5/9>1/2$. -/)
  (title := /-- Lower bound for the Gaussian absolute first moment -/)
  (latexEnv := "lemma")]
lemma cool_standard_gaussian_abs_mean_lower :
    (1 / 2 : ℝ) ≤ ∫ x : ℝ, |x| ∂ProbabilityTheory.gaussianReal 0 1 ∧
      (∫ x : ℝ, x ^ 2 ∂ProbabilityTheory.gaussianReal 0 1) = 1 := by
  have htwo : ∫ x : ℝ, x ^ 2 ∂ProbabilityTheory.gaussianReal 0 1 = 1 := by
    have hv : ProbabilityTheory.variance id
        (ProbabilityTheory.gaussianReal 0 1) = 1 :=
      ProbabilityTheory.variance_id_gaussianReal
    rw [ProbabilityTheory.variance_eq_integral measurable_id.aemeasurable] at hv
    simpa using hv
  have hfour : ∫ x : ℝ, x ^ 4 ∂ProbabilityTheory.gaussianReal 0 1 = 3 := by
    calc
      ∫ x : ℝ, x ^ 4 ∂ProbabilityTheory.gaussianReal 0 1 =
          iteratedDeriv 4
            (ProbabilityTheory.mgf (fun x : ℝ => x)
              (ProbabilityTheory.gaussianReal 0 1)) 0 := by
              rw [ProbabilityTheory.iteratedDeriv_mgf_zero] <;> simp
      _ = iteratedDeriv 4 (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 := by
            rw [ProbabilityTheory.mgf_fun_id_gaussianReal]
            norm_num
      _ = 3 := by
        have h1 : deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
            fun t => t * Real.exp (t ^ 2 / 2) := by
          ext t
          rw [deriv_exp (by fun_prop)]
          norm_num [deriv_div_const, deriv_pow]
          ring
        have h2 : deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) =
            fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
          ext t
          rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_exp (by fun_prop)]
          norm_num [deriv_div_const, deriv_pow]
          ring
        have h3 : deriv (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) =
            fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
          ext t
          rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_exp (by fun_prop)]
          norm_num [deriv_div_const, deriv_pow]
          ring
        have h4 : deriv (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) =
            fun t => (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2) := by
          ext t
          rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_exp (by fun_prop)]
          rw [show deriv (fun s : ℝ => 3 * s + s ^ 3) t = 3 + 3 * t ^ 2 by
            rw [deriv_fun_add (by fun_prop) (by fun_prop)]
            norm_num [deriv_fun_mul, deriv_pow]]
          norm_num [deriv_div_const, deriv_pow]
          ring
        simp only [iteratedDeriv_succ, iteratedDeriv_zero]
        rw [h1, h2, h3, h4]
        norm_num
  have habs : Integrable (fun x : ℝ => |x|)
      (ProbabilityTheory.gaussianReal 0 1) := by
    simpa [Function.comp_def, Real.norm_eq_abs] using
      ((ProbabilityTheory.memLp_id_gaussianReal
        (μ := 0) (v := 1) 1).integrable (by norm_num)).norm
  have hpow2 : Integrable (fun x : ℝ => x ^ 2)
      (ProbabilityTheory.gaussianReal 0 1) := by
    simpa [Real.norm_eq_abs, sq_abs] using
      (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_norm_pow
        (by norm_num)
  have hpow4 : Integrable (fun x : ℝ => x ^ 4)
      (ProbabilityTheory.gaussianReal 0 1) := by
    have hi :=
      (ProbabilityTheory.memLp_id_gaussianReal
        (μ := 0) (v := 1) 4).integrable_norm_pow (by norm_num)
    convert hi using 1
    funext x
    simp only [id_eq, Real.norm_eq_abs]
    have hx2 : x ^ 2 = |x| ^ 2 := by rw [sq_abs]
    nlinarith [sq_nonneg (x ^ 2)]
  have hpoint (x : ℝ) : x ^ 2 - (4 / 27 : ℝ) * x ^ 4 ≤ |x| := by
    have hx : 0 ≤ |x| := abs_nonneg x
    have hp : 0 ≤ |x| * (2 * |x| - 3) ^ 2 * (|x| + 3) := by positivity
    have hx2 : x ^ 2 = |x| ^ 2 := by rw [sq_abs]
    have hx4 : x ^ 4 = |x| ^ 4 := by
      calc
        x ^ 4 = (x ^ 2) ^ 2 := by ring
        _ = (|x| ^ 2) ^ 2 := by rw [hx2]
        _ = |x| ^ 4 := by ring
    nlinarith
  refine ⟨?_, htwo⟩
  calc
    (1 / 2 : ℝ) ≤ 1 - (4 / 27 : ℝ) * 3 := by norm_num
    _ = ∫ x : ℝ, (x ^ 2 - (4 / 27 : ℝ) * x ^ 4)
          ∂ProbabilityTheory.gaussianReal 0 1 := by
        rw [integral_sub hpow2 (hpow4.const_mul _), integral_const_mul,
          htwo, hfour]
    _ ≤ ∫ x : ℝ, |x| ∂ProbabilityTheory.gaussianReal 0 1 := by
      exact integral_mono (hpow2.sub (hpow4.const_mul _)) habs hpoint

@[blueprint "lem:cool-norm-increment-linearization"
  (statement := /-- Let $m\in\mathbb N$, let $y,a\in\mathbb R^m$, and let $c\in\mathbb R$.  If $\lVert y\rVert>0$, then
  \[
    \lVert y+ca\rVert-\lVert y\rVert
      \le \frac{2c\langle y,a\rangle+c^2\lVert a\rVert^2}
                    {2\lVert y\rVert}.
  \] -/)
  (proof := /-- Expand the squared norm by bilinearity of the real inner product.  The inequality $2\lVert y\rVert(\lVert y+ca\rVert-\lVert y\rVert)\le \lVert y+ca\rVert^2-\lVert y\rVert^2$ is the nonnegativity of $(\lVert y+ca\rVert-\lVert y\rVert)^2$.  Division by the positive number $2\lVert y\rVert$ gives the claim. -/)
  (title := /-- Linearized bound for a norm increment -/)
  (latexEnv := "lemma")]
lemma cool_norm_increment_linearization (m : ℕ)
    (y a : EuclideanSpace ℝ (Fin m)) (c : ℝ) (hy : 0 < ‖y‖) :
    ‖y + c • a‖ - ‖y‖ ≤
      (2 * c * inner ℝ y a + c ^ 2 * ‖a‖ ^ 2) / (2 * ‖y‖) := by
  have hsquare : ‖y + c • a‖ ^ 2 =
      ‖y‖ ^ 2 + 2 * c * inner ℝ y a + c ^ 2 * ‖a‖ ^ 2 := by
    rw [norm_add_sq_real]
    simp only [inner_smul_right, conj_trivial, norm_smul,
      Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    ring
  have htangent : 2 * ‖y‖ * (‖y + c • a‖ - ‖y‖) ≤
      ‖y + c • a‖ ^ 2 - ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖y + c • a‖ - ‖y‖)]
  rw [hsquare] at htangent
  apply (le_div_iff₀ (by positivity : 0 < 2 * ‖y‖)).2
  nlinarith

@[blueprint "lem:cool-adaptive-state-measurable"
  (statement := /-- For every choice of natural-number parameters $n,m,B,K$ and every time $t\in\mathbb N$, the COOL state $A\mapsto y_t(A)$ is a measurable function of the input matrix. -/)
  (proof := /-- Induct on $t$.  The initial state is constant.  At a successor time, unfold \cref{def:cool-state}.  If the time is outside the input range, use the induction hypothesis.  Otherwise, the previous state and the current coordinate projection are measurable; scalar multiplication, subtraction, addition, norms, comparison, and the resulting piecewise choice preserve measurability. -/)
  (title := /-- Measurability of the COOL state -/)
  (latexEnv := "lemma")]
lemma cool_adaptive_state_measurable (n m B K t : ℕ) :
    Measurable (fun A : cool_matrix m n => cool_state n m B K A t) := by
  induction t with
  | zero =>
      simp [cool_state]
  | succ t ih =>
      rw [show (fun A : cool_matrix m n => cool_state n m B K A (t + 1)) =
          fun A =>
            if ht : t < n then
              let j : Fin n := ⟨t, ht⟩
              let y := cool_state n m B K A t
              let a := cool_column A j
              let b : ℝ := cool_temperature n m B K j
              if ‖y - b • a‖ ≤ ‖y + b • a‖ then y - b • a else y + b • a
            else cool_state n m B K A t by
        funext A
        rw [cool_state]]
      by_cases ht : t < n
      · simp only [dif_pos ht]
        have hcolumn : Measurable
            (fun A : cool_matrix m n => cool_column A ⟨t, ht⟩) := by
          unfold cool_column
          fun_prop
        apply Measurable.ite
        · exact measurableSet_le (by fun_prop) (by fun_prop)
        · fun_prop
        · fun_prop
      · simp only [dif_neg ht]
        exact ih

@[blueprint "lem:cool-adaptive-state-depends-on-past"
  (statement := /-- For all natural-number parameters $n,m,B,K,t$ and matrices $A,A'$, if $A$ and $A'$ agree in every column whose index is less than $t$, then their COOL states at time $t$ are equal. -/)
  (proof := /-- Induct on $t$ and unfold \cref{def:cool-state}.  At a successor time outside the input range, the conclusion is the induction hypothesis.  Inside the range, the induction hypothesis identifies the previous states and the assumed column agreement identifies the current columns, so both norm comparisons select the same update. -/)
  (title := /-- Dependence of the COOL state on preceding columns -/)
  (latexEnv := "lemma")]
lemma cool_adaptive_state_depends_on_past :
    ∀ (n m B K t : ℕ) (A A' : cool_matrix m n),
      (∀ j : Fin n, j.1 < t → A j = A' j) →
      cool_state n m B K A t = cool_state n m B K A' t := by
  intro n m B K t
  induction t with
  | zero =>
      intro A A' hA
      simp [cool_state]
  | succ t ih =>
      intro A A' hA
      have hpast : cool_state n m B K A t = cool_state n m B K A' t :=
        ih A A' (fun j hj => hA j (Nat.lt.step hj))
      by_cases ht : t < n
      · have hcolumn : A ⟨t, ht⟩ = A' ⟨t, ht⟩ := hA ⟨t, ht⟩ (by simp)
        simp [cool_state, ht, cool_column, hpast, hcolumn]
      · simp [cool_state, ht, hpast]

@[blueprint "lem:cool-adaptive-drift-comparison"
  (statement := /-- Let $m,n,B,K,s,\ell,b\in\mathbb N$, with $m\ge 4$ and $b>0$, and suppose that $[s,s+\ell)$ is a constant-temperature block at temperature $b$ for the COOL process with parameters $n,m,B,K$.  Under the standard-Gaussian law on $m\times n$ matrices, there exist families of real random variables $(A_i)_{i\in\mathbb N}$ and $(D_i)_{i\in\mathbb N}$ such that the pairs $(A_i,D_i)_{0\le i<\ell}$ are jointly independent, every $A_i$ with $i<\ell$ is a type-$A$ comparison variable in dimension $m$, every $D_i$ with $i<\ell$ is a type-$B$ comparison variable, and
  \[
  \begin{split}
    &\mathbb{P}\!\left(\lVert y_s\rVert\le 8bm,\
          \lVert y_{s+\ell}\rVert>4bm\right)\\
    &\quad\le
      \mathbb{P}\!\left(\sum_{i<\ell}D_i\le4m\right)
      +\sum_{t<\ell}
        \mathbb{P}\!\left(A_t-\sum_{i<t}D_i>2m\right).
  \end{split}
  \]
  Thus the adaptive greedy process is reduced to independent scalar comparison variables. -/)
  (proof := /-- For $0\le i<\ell$, let $\mathcal H_i$ be the sigma-algebra generated by the columns preceding the $(s+i)$th column.  By \,\cref{lem:cool-adaptive-state-measurable}, the state $y_{s+i}$ is measurable, and \,\cref{lem:cool-adaptive-state-depends-on-past} shows that it depends only on those preceding columns.  Choose the Householder reflection $R_i$ in the hyperplane orthogonal to the difference between the unit direction of $y_{s+i}$ and the first coordinate vector, using the first coordinate vector itself when the state vanishes.  The reflection formula shows that $R_i$ is measurable, depends only on the preceding columns, and maps the chosen direction to the first coordinate vector.

  Put $Z_i=R_i a_{s+i}$.  Apply \,\cref{lem:cool-predictable-gaussian-rotation} to the strictly increasing index family $i\mapsto s+i$ and the maps $R_i$.  Its hypotheses were verified in the preceding paragraph, so the joint pushforward law of $(Z_i)_{i<\ell}$ is the product of $\ell$ copies of the measure in \,\cref{def:cool-gaussian-column-measure}.  In particular, the $Z_i$ are jointly independent standard Gaussian vectors; this conclusion accounts for the full dependence of $R_i$ on all preceding columns, rather than treating the rotations as fixed coordinatewise maps.

  Write $N_i=(Z_i)_1$, $Q_i=\sum_{j=2}^m(Z_i)_j^2$, and $S_i=N_i^2+Q_i=\lVert Z_i\rVert_2^2$.  Thus $N_i$ is standard normal, $Q_i$ has the chi-square distribution with $m-1$ degrees of freedom, and the two are independent.  Define the chronological comparison variables
  \[
    \widehat A_i=\lVert Z_i\rVert_2,
    \qquad \widehat D_i=|N_i|-\frac{S_i}{4m}.
  \]
  The pushforward-law identity above and \,\cref{lem:cool-standard-gaussian-norm-tail} show that every $\widehat A_i$ satisfies \,\cref{def:cool-type-a-comparison}.

  We next verify the stronger moment contract in \,\cref{def:cool-type-b-comparison}.  The variable $\widehat D_i$ is Borel measurable.  For $0\le t\le1$, the integrand $e^{t(1/4-\widehat D_i)}$ is bounded by $e^{1/4+tS_i/(4m)}$; its expectation is finite because $t/(4m)\le1/16<1/2$.  Hence the required exponential is integrable.

  Let $X=|N_i|$ and $S_i=\sum_j(Z_i)_j^2$.  Coordinate independence and \,\cref{lem:cool-gaussian-square-mgf} give
  \[
    \mathbb E e^{sS_i}=(1-2s)^{-m/2}\qquad(s<1/2).
  \]
  Set $U=e^{-tX}$ and $V=e^{tS_i/(4m)}$.  By Cauchy--Schwarz,
  \[
    \mathbb E(UV)\le
      (\mathbb E U^2)^{1/2}(\mathbb E V^2)^{1/2}.
  \]
  The inequality $e^{-u}\le1-u+u^2/2$, together with
  $\mathbb E X\ge1/2$ and $\mathbb E X^2=1$ from
  \,\cref{lem:cool-standard-gaussian-abs-mean-lower}, yields
  \[
    \mathbb E U^2\le1-t+2t^2,
    \qquad
    (\mathbb E U^2)^{1/2}\le e^{-t/2+t^2}.
  \]
  The displayed square-MGF formula gives
  $\mathbb E V^2=(1-t/m)^{-m/2}$.  Applying
  $1-(1-x)^{-1}\le\log(1-x)$ with $x=t/m$, and using
  $m\ge4$ and $0\le t\le1$, gives
  \[
    (\mathbb E V^2)^{1/2}\le e^{t/4+t^2/12}.
  \]
  After restoring the factor $e^{t/4}$, these estimates yield
  \[
    \mathbb E e^{t(1/4-\widehat D_i)}
      \le e^{t/4}e^{-t/2+t^2}e^{t/4+t^2/12}
      \le e^{2t^2}.
  \]
  The preceding square-MGF estimate also supplies the required integrability.  Therefore $\widehat D_i$ satisfies \,\cref{def:cool-type-b-comparison}.  Since $(\widehat A_i,\widehat D_i)$ is the same fixed Borel function of $Z_i$ for every $i$, the chronological comparison pairs are independent.

  Define the variables appearing in the conclusion by reversing the chronological family:
  \[
    A_r=\widehat A_{\ell-1-r},\qquad
    D_r=\widehat D_{\ell-1-r}\qquad(0\le r<\ell),
  \]
  and set both variables equal to zero for $r\ge\ell$.  A fixed permutation preserves joint independence and the one-variable comparison contracts.  Hence the pairs $(A_r,D_r)_{r<\ell}$ are independent, every $A_r$ is type-$A$, and every $D_r$ is type-$B$.

  It remains to compare the chronological variables with every adaptive increment.  Write $L_i=\lVert y_{s+i}\rVert_2$.  The triangle inequality gives $L_{i+1}-L_i\le b\widehat A_i$.  If $L_i\ge2bm$, the greedy update in \,\cref{def:cool-state} chooses the sign whose inner product with the current state is nonpositive.  Applying \,\cref{lem:cool-norm-increment-linearization} and then $L_i\ge2bm$ yields
  \[
  \begin{split}
    L_{i+1}-L_i
      &\le \frac{-2bL_i|N_i|+b^2S_i}{2L_i}\\
      &\le-b|N_i|+\frac{bS_i}{4m}=-b\widehat D_i.
  \end{split}
  \]
  Put $G_r=L_{\ell-r}$.  Suppose that the bad endpoint event holds, that
  $\sum_{r<\ell}D_r>4m$, and that every escape inequality fails.  A backward induction proves simultaneously that
  \[
    G_0-G_r\le-b\sum_{k<r}D_k
    \quad\text{and}\quad
    r=0\ \text{or}\ G_r\ge2bm.
  \]
  At the successor step, if $G_{r+1}<2bm$, the accumulated inward bounds, the outward increment bound, and
  $A_r-\sum_{k<r}D_k\le2m$ imply $G_0-G_{r+1}\le2bm$, contradicting
  $G_0>4bm$.  Thus $G_{r+1}\ge2bm$, so the inward bound extends the accumulated inequality.  At $r=\ell$, the assumptions
  $G_\ell\le8bm$ and $\sum_{r<\ell}D_r>4m$ contradict $G_0>4bm$.
  Hence the bad event lies in the union of the lower-tail event and the finitely many escape events.  Monotonicity and finite subadditivity of the real-valued measure give the asserted probability inequality. -/)
  (title := /-- Adaptive Gaussian drift comparison -/)
  (latexEnv := "lemma")]
lemma cool_adaptive_drift_comparison :
    ∀ (m n B K start length b : ℕ),
      4 ≤ m → 0 < b →
      cool_constant_block n m B K start length b →
      ∃ upward downward : ℕ → cool_matrix m n → ℝ,
        ProbabilityTheory.iIndepFun
          (fun i : Fin length => fun A =>
            (upward i.1 A, downward i.1 A))
          (cool_gaussian_matrix_measure m n) ∧
        (∀ i : Fin length,
          cool_type_a_comparison (cool_gaussian_matrix_measure m n) m
            (upward i.1)) ∧
        (∀ i : Fin length,
          cool_type_b_comparison (cool_gaussian_matrix_measure m n)
            (downward i.1)) ∧
        (cool_gaussian_matrix_measure m n).real
            {A | ‖cool_state n m B K A start‖ ≤
                (8 : ℝ) * (b : ℝ) * (m : ℝ) ∧
              (4 : ℝ) * (b : ℝ) * (m : ℝ) <
                ‖cool_state n m B K A (start + length)‖} ≤
          (cool_gaussian_matrix_measure m n).real
              {A | (∑ i ∈ Finset.range length, downward i A) ≤
                (4 : ℝ) * (m : ℝ)} +
            ∑ t ∈ Finset.range length,
              (cool_gaussian_matrix_measure m n).real
                {A | (2 : ℝ) * (m : ℝ) <
                  upward t A -
                    ∑ i ∈ Finset.range t, downward i A} := by
  classical
  intro m n B K start length b hm hb hblock
  rcases hblock with ⟨hend, htemperature⟩
  have hmpos : 0 < m := by omega
  let first : Fin m := ⟨0, hmpos⟩
  let e : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single first 1
  have he_norm : ‖e‖ = 1 := by simp [e]
  let index : Fin length → Fin n := fun i => ⟨start + i.1, by omega⟩
  have hindex_order : ∀ i k : Fin length, i.1 < k.1 →
      (index i).1 < (index k).1 := by
    intro i k hik
    simp only [index]
    omega
  let direction : Fin length → cool_matrix m n →
      EuclideanSpace ℝ (Fin m) := fun i A =>
    let y := cool_state n m B K A (start + i.1)
    if y = 0 then e else ‖y‖⁻¹ • y
  have hdirection_meas (i : Fin length) : Measurable (direction i) := by
    dsimp only [direction]
    apply Measurable.ite
    · exact measurableSet_eq_fun (cool_adaptive_state_measurable n m B K _) measurable_const
    · exact measurable_const
    · have hs := cool_adaptive_state_measurable n m B K (start + i.1)
      exact hs.norm.inv.smul hs
  have hdirection_norm (i : Fin length) (A : cool_matrix m n) :
      ‖direction i A‖ = 1 := by
    dsimp only [direction]
    split_ifs with hy
    · exact he_norm
    · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_norm, inv_mul_cancel₀]
      exact norm_ne_zero_iff.mpr hy
  let R : Fin length → cool_matrix m n →
      (EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) :=
    fun i A => ((ℝ ∙ (direction i A - e))ᗮ).reflection
  have hRdirection (i : Fin length) (A : cool_matrix m n) :
      R i A (direction i A) = e := by
    exact Submodule.reflection_sub (by rw [hdirection_norm, he_norm])
  have hRmeas (i : Fin length) : Measurable (fun A : cool_matrix m n =>
      (EuclideanSpace.equiv (Fin m) ℝ)
        (R i A ((EuclideanSpace.equiv (Fin m) ℝ).symm
          (A (index i))))) := by
    simp only [R, Submodule.reflection_orthogonal_apply,
      Submodule.reflection_singleton_apply]
    have hd : Measurable (fun A => direction i A - e) :=
      (hdirection_meas i).sub measurable_const
    have ha0 : Measurable (fun A : cool_matrix m n => A (index i)) :=
      measurable_pi_apply (index i)
    have ha : Measurable (fun A : cool_matrix m n =>
        (EuclideanSpace.equiv (Fin m) ℝ).symm (A (index i))) :=
      (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.measurable.comp ha0
    have hi : Measurable (fun A : cool_matrix m n =>
        inner ℝ (direction i A - e)
          ((EuclideanSpace.equiv (Fin m) ℝ).symm (A (index i)))) :=
      continuous_inner.measurable.comp (hd.prodMk ha)
    have hout : Measurable (fun A : cool_matrix m n =>
        -(2 • (inner ℝ (direction i A - e)
              ((EuclideanSpace.equiv (Fin m) ℝ).symm (A (index i))) /
            (‖direction i A - e‖ : ℝ) ^ 2) • (direction i A - e) -
          (EuclideanSpace.equiv (Fin m) ℝ).symm (A (index i)))) := by
      fun_prop
    exact (EuclideanSpace.equiv (Fin m) ℝ).continuous.measurable.comp hout
  have hRpast (i : Fin length) (A A' : cool_matrix m n)
      (hAA : ∀ j : Fin n, j.1 < (index i).1 → A j = A' j) :
      R i A = R i A' := by
    have hy : cool_state n m B K A (start + i.1) =
        cool_state n m B K A' (start + i.1) := by
      apply cool_adaptive_state_depends_on_past
      intro j hj
      apply hAA j
      simpa [index] using hj
    simp [R, direction, hy]
  obtain ⟨hmap, hindepZ⟩ := cool_predictable_gaussian_rotation
    m n length index R hindex_order hRmeas hRpast
  let Z : Fin length → cool_matrix m n → (Fin m → ℝ) := fun i A =>
    (EuclideanSpace.equiv (Fin m) ℝ)
      (R i A ((EuclideanSpace.equiv (Fin m) ℝ).symm (A (index i))))
  let Ahat : Fin length → cool_matrix m n → ℝ := fun i A =>
    ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (Z i A)‖
  let Dhat : Fin length → cool_matrix m n → ℝ := fun i A =>
    |Z i A first| -
      (∑ j : Fin m, (Z i A j) ^ 2) / (4 * (m : ℝ))
  let upward : ℕ → cool_matrix m n → ℝ := fun r A =>
    if hr : r < length then Ahat (Fin.rev ⟨r, hr⟩) A else 0
  let downward : ℕ → cool_matrix m n → ℝ := fun r A =>
    if hr : r < length then Dhat (Fin.rev ⟨r, hr⟩) A else 0
  have hZmeas (i : Fin length) : Measurable (Z i) := by
    simpa [Z] using hRmeas i
  have hZallmeas : Measurable
      (fun A : cool_matrix m n => fun i => Z i A) :=
    measurable_pi_iff.mpr hZmeas
  have hZmap : Measure.map (fun A : cool_matrix m n => fun i => Z i A)
      (cool_gaussian_matrix_measure m n) =
      cool_gaussian_matrix_measure m length := by
    simpa [Z] using hmap
  letI : IsProbabilityMeasure (cool_gaussian_column_measure m) := by
    unfold cool_gaussian_column_measure
    infer_instance
  letI : IsProbabilityMeasure (cool_gaussian_matrix_measure m length) := by
    unfold cool_gaussian_matrix_measure
    infer_instance
  letI : IsProbabilityMeasure (cool_gaussian_matrix_measure m n) := by
    unfold cool_gaussian_matrix_measure
    infer_instance
  have hZlaw (i : Fin length) :
      Measure.map (Z i) (cool_gaussian_matrix_measure m n) =
        cool_gaussian_column_measure m := by
    calc
      Measure.map (Z i) (cool_gaussian_matrix_measure m n) =
          Measure.map (fun X : cool_matrix m length => X i)
            (Measure.map (fun A : cool_matrix m n => fun k => Z k A)
              (cool_gaussian_matrix_measure m n)) := by
                rw [Measure.map_map]
                · rfl
                · exact measurable_pi_apply i
                · exact hZallmeas
      _ = Measure.map (fun X : cool_matrix m length => X i)
            (cool_gaussian_matrix_measure m length) := by rw [hZmap]
      _ = cool_gaussian_column_measure m :=
        (MeasureTheory.measurePreserving_eval
          (fun _ : Fin length => cool_gaussian_column_measure m) i).map_eq
  have hstandardB : cool_type_b_comparison
      (cool_gaussian_column_measure m)
      (fun z => |z first| -
        (∑ j : Fin m, (z j) ^ 2) / (4 * (m : ℝ))) := by
    let X : Fin m → (Fin m → ℝ) → ℝ := fun j z => z j ^ 2
    let S : (Fin m → ℝ) → ℝ := fun z => ∑ j : Fin m, X j z
    have hindep0 : ProbabilityTheory.iIndepFun
        (fun j : Fin m => fun z : Fin m → ℝ => z j)
        (cool_gaussian_column_measure m) := by
      unfold cool_gaussian_column_measure
      exact ProbabilityTheory.iIndepFun_pi
        (μ := fun _ : Fin m => ProbabilityTheory.gaussianReal 0 1)
        (X := fun _ => id)
        (fun _ => measurable_id.aemeasurable)
    have hindepX : ProbabilityTheory.iIndepFun X
        (cool_gaussian_column_measure m) := by
      exact hindep0.comp (fun _ => fun x : ℝ => x ^ 2) (fun _ => by fun_prop)
    have hXmeas : ∀ j, Measurable (X j) := by
      intro j
      fun_prop
    have hmgfS : ∀ s : ℝ, s < 1 / 2 →
        ProbabilityTheory.mgf S (cool_gaussian_column_measure m) s =
          (1 / Real.sqrt (1 - 2 * s)) ^ m := by
      intro s hs
      have hcoord : ∀ j, ProbabilityTheory.mgf (X j)
          (cool_gaussian_column_measure m) s =
          1 / Real.sqrt (1 - 2 * s) := by
        intro j
        change ProbabilityTheory.mgf
          ((fun x : ℝ => x ^ 2) ∘ fun z : Fin m → ℝ => z j)
            (cool_gaussian_column_measure m) s = _
        rw [← ProbabilityTheory.mgf_map
          (Y := fun z : Fin m → ℝ => z j) (X := fun x : ℝ => x ^ 2)
          (μ := cool_gaussian_column_measure m) (t := s)
          (measurable_pi_apply j).aemeasurable
          ((by fun_prop : Measurable
            (fun x : ℝ => Real.exp (s * x ^ 2))).aestronglyMeasurable)]
        simp [cool_gaussian_column_measure, Measure.pi_map_eval]
        simpa only [one_div] using cool_gaussian_square_mgf s hs
      have hS : S = ∑ j : Fin m, X j := by
        funext z
        simp [S]
      rw [hS]
      rw [hindepX.mgf_sum (t := s) hXmeas Finset.univ]
      simp [hcoord]
    refine ⟨by fun_prop, ?_⟩
    intro t ht0 ht1
    have hmreal : 0 < (m : ℝ) := by exact_mod_cast hmpos
    let s : ℝ := t / (4 * (m : ℝ))
    have hs0 : 0 ≤ s := by dsimp [s]; positivity
    have hs : s < 1 / 2 := by
      dsimp [s]
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * (m : ℝ))).2
      nlinarith [show (4 : ℝ) ≤ m by exact_mod_cast hm]
    have hSint : Integrable (fun z => Real.exp (s * S z))
        (cool_gaussian_column_measure m) := by
      apply (ProbabilityTheory.mgf_pos_iff (X := S) (t := s)).mp
      rw [hmgfS s hs]
      have hspos : 0 < 1 - 2 * s := by linarith
      positivity
    have htargetint : Integrable
        (fun z : Fin m → ℝ => Real.exp
          (t * ((1 / 4 : ℝ) -
            (|z first| - (∑ j : Fin m, z j ^ 2) / (4 * (m : ℝ))))))
        (cool_gaussian_column_measure m) := by
      apply Integrable.mono' ((hSint.const_mul (Real.exp (t / 4)))) (by fun_prop)
      filter_upwards with z
      simp only [Real.norm_eq_abs]
      rw [abs_of_pos (Real.exp_pos _)]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp only [S, X, s]
      have habs : 0 ≤ |z first| := abs_nonneg _
      have hnonpos : -t * |z first| ≤ 0 := by
        nlinarith [mul_nonneg ht0 habs]
      field_simp
      nlinarith
    refine ⟨htargetint, ?_⟩
    let U : (Fin m → ℝ) → ℝ := fun z => Real.exp (-t * |z first|)
    let V : (Fin m → ℝ) → ℝ := fun z => Real.exp (t * S z / (4 * (m : ℝ)))
    have hcoordlaw : Measure.map (fun z : Fin m → ℝ => z first)
        (cool_gaussian_column_measure m) =
        ProbabilityTheory.gaussianReal 0 1 := by
      simp [cool_gaussian_column_measure, Measure.pi_map_eval]
    have habsmean : (1 / 2 : ℝ) ≤
        ∫ z : Fin m → ℝ, |z first| ∂cool_gaussian_column_measure m := by
      have h := cool_standard_gaussian_abs_mean_lower.1
      rw [← hcoordlaw] at h
      rw [integral_map (measurable_pi_apply first).aemeasurable (by fun_prop)] at h
      simpa [Function.comp_def] using h
    have hsecond : (∫ z : Fin m → ℝ, (z first) ^ 2
        ∂cool_gaussian_column_measure m) = 1 := by
      have h := cool_standard_gaussian_abs_mean_lower.2
      rw [← hcoordlaw] at h
      rw [integral_map (measurable_pi_apply first).aemeasurable (by fun_prop)] at h
      simpa [Function.comp_def] using h
    have habsint : Integrable (fun z : Fin m → ℝ => |z first|)
        (cool_gaussian_column_measure m) := by
      have hi : Integrable (fun x : ℝ => |x|)
          (ProbabilityTheory.gaussianReal 0 1) := by
        simpa [Function.comp_def, Real.norm_eq_abs] using
        ((ProbabilityTheory.memLp_id_gaussianReal
          (μ := 0) (v := 1) 1).integrable (by norm_num)).norm
      rw [← hcoordlaw] at hi
      exact (integrable_map_measure
        ((by fun_prop : Measurable (fun x : ℝ => |x|)).aestronglyMeasurable)
        (measurable_pi_apply first).aemeasurable).mp hi
    have hsecondint : Integrable (fun z : Fin m → ℝ => (z first) ^ 2)
        (cool_gaussian_column_measure m) := by
      have hi : Integrable (fun x : ℝ => x ^ 2)
          (ProbabilityTheory.gaussianReal 0 1) := by
        simpa [Function.comp_def, Real.norm_eq_abs, sq_abs] using
        (ProbabilityTheory.memLp_id_gaussianReal
          (μ := 0) (v := 1) 2).integrable_norm_pow (by norm_num)
      rw [← hcoordlaw] at hi
      exact (integrable_map_measure
        ((by fun_prop : Measurable (fun x : ℝ => x ^ 2)).aestronglyMeasurable)
        (measurable_pi_apply first).aemeasurable).mp hi
    have hexp_poly (u : ℝ) (hu : 0 ≤ u) :
        Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
      calc
        Real.exp (-u) = (Real.exp u)⁻¹ := Real.exp_neg u
        _ ≤ (1 + u + u ^ 2 / 2)⁻¹ := by
          have hrec : (1 : ℝ) / Real.exp u ≤
              1 / (1 + u + u ^ 2 / 2) :=
            one_div_le_one_div_of_le
              (by nlinarith [sq_nonneg u] : (0 : ℝ) < 1 + u + u ^ 2 / 2)
              (Real.quadratic_le_exp_of_nonneg hu)
          simpa only [one_div] using hrec
        _ ≤ 1 - u + u ^ 2 / 2 := by
          have h := (div_le_iff₀
            (by nlinarith [sq_nonneg u] : (0 : ℝ) < 1 + u + u ^ 2 / 2)).2
            (show (1 : ℝ) ≤
                (1 - u + u ^ 2 / 2) * (1 + u + u ^ 2 / 2) by
              nlinarith [sq_nonneg (u ^ 2)])
          simpa only [one_div] using h
    have hU2int : Integrable (fun z : Fin m → ℝ => U z ^ 2)
        (cool_gaussian_column_measure m) := by
      apply Integrable.of_bound (by fun_prop) 1
      filter_upwards with z
      dsimp only [U]
      rw [Real.norm_eq_abs, abs_pow, abs_of_pos (Real.exp_pos _)]
      have hnonpos : -t * |z first| ≤ 0 := by
        nlinarith [mul_nonneg ht0 (abs_nonneg (z first))]
      have := Real.exp_le_one_iff.mpr hnonpos
      nlinarith [Real.exp_nonneg (-t * |z first|)]
    have hfold : (∫ z : Fin m → ℝ, U z ^ 2
          ∂cool_gaussian_column_measure m) ≤ 1 - t + 2 * t ^ 2 := by
      have hpolyint : Integrable (fun z : Fin m → ℝ =>
          1 - 2 * t * |z first| + 2 * t ^ 2 * (z first) ^ 2)
          (cool_gaussian_column_measure m) := by
        fun_prop
      calc
        (∫ z : Fin m → ℝ, U z ^ 2
            ∂cool_gaussian_column_measure m) ≤
            ∫ z : Fin m → ℝ,
              (1 - 2 * t * |z first| + 2 * t ^ 2 * (z first) ^ 2)
              ∂cool_gaussian_column_measure m := by
                apply integral_mono hU2int hpolyint
                intro z
                dsimp only [U]
                have hp := hexp_poly (2 * t * |z first|) (by positivity)
                calc
                  Real.exp (-t * |z first|) ^ 2 =
                      Real.exp (-(2 * t * |z first|)) := by
                        rw [pow_two, ← Real.exp_add]
                        congr 1
                        ring
                  _ ≤ 1 - 2 * t * |z first| +
                      (2 * t * |z first|) ^ 2 / 2 := hp
                  _ = 1 - 2 * t * |z first| +
                      2 * t ^ 2 * (z first) ^ 2 := by
                        have hsqa : |z first| ^ 2 = (z first) ^ 2 := sq_abs _
                        nlinarith
        _ = 1 - 2 * t * (∫ z : Fin m → ℝ, |z first|
              ∂cool_gaussian_column_measure m) +
              2 * t ^ 2 * (∫ z : Fin m → ℝ, (z first) ^ 2
                ∂cool_gaussian_column_measure m) := by
                have hc : Integrable (fun _ : Fin m → ℝ => (1 : ℝ))
                    (cool_gaussian_column_measure m) := integrable_const 1
                have ha := habsint.const_mul (2 * t)
                have hq := hsecondint.const_mul (2 * t ^ 2)
                rw [show (fun z : Fin m → ℝ =>
                    1 - 2 * t * |z first| + 2 * t ^ 2 * (z first) ^ 2) =
                    (fun z => (1 : ℝ)) - (fun z => 2 * t * |z first|) +
                      (fun z => 2 * t ^ 2 * (z first) ^ 2) by
                      funext z
                      rfl]
                change (∫ z : Fin m → ℝ,
                    (((fun _ : Fin m → ℝ => (1 : ℝ)) -
                      (fun x : Fin m → ℝ => 2 * t * |x first|)) z +
                      (fun x : Fin m → ℝ => 2 * t ^ 2 * (x first) ^ 2) z)
                    ∂cool_gaussian_column_measure m) = _
                rw [integral_add (hc.sub ha) hq]
                change (∫ z : Fin m → ℝ, 1 - 2 * t * |z first|
                    ∂cool_gaussian_column_measure m) +
                    (∫ z : Fin m → ℝ, 2 * t ^ 2 * (z first) ^ 2
                      ∂cool_gaussian_column_measure m) = _
                rw [integral_sub hc ha,
                  integral_const_mul, integral_const_mul]
                simp
        _ ≤ 1 - t + 2 * t ^ 2 := by
          rw [hsecond]
          nlinarith
    let s₂ : ℝ := t / (2 * (m : ℝ))
    have hs₂ : s₂ < 1 / 2 := by
      dsimp [s₂]
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))).2
      nlinarith [show (4 : ℝ) ≤ m by exact_mod_cast hm]
    have hV2int : Integrable (fun z : Fin m → ℝ => V z ^ 2)
        (cool_gaussian_column_measure m) := by
      have hi : Integrable (fun z => Real.exp (s₂ * S z))
          (cool_gaussian_column_measure m) := by
        apply (ProbabilityTheory.mgf_pos_iff (X := S) (t := s₂)).mp
        rw [hmgfS s₂ hs₂]
        have : 0 < 1 - 2 * s₂ := by linarith
        positivity
      convert hi using 1
      funext z
      dsimp only [V, s₂]
      rw [pow_two, ← Real.exp_add]
      congr 1 <;> ring
    have hUmem : MemLp U 2 (cool_gaussian_column_measure m) :=
      (memLp_two_iff_integrable_sq (by fun_prop)).2 hU2int
    have hVmem : MemLp V 2 (cool_gaussian_column_measure m) :=
      (memLp_two_iff_integrable_sq (by fun_prop)).2 hV2int
    have hcs := integral_mul_norm_le_Lp_mul_Lq
      (μ := cool_gaussian_column_measure m) (p := (2 : ℝ)) (q := (2 : ℝ))
      Real.HolderConjugate.two_two (by simpa using hUmem) (by simpa using hVmem)
    have hV2eval : (∫ z : Fin m → ℝ, V z ^ 2
        ∂cool_gaussian_column_measure m) =
        (1 / Real.sqrt (1 - t / (m : ℝ))) ^ m := by
      have hfun : (fun z : Fin m → ℝ => V z ^ 2) =
          fun z => Real.exp (s₂ * S z) := by
        funext z
        dsimp only [V, s₂]
        rw [pow_two, ← Real.exp_add]
        congr 1 <;> ring
      rw [hfun]
      change ProbabilityTheory.mgf S (cool_gaussian_column_measure m) s₂ = _
      rw [hmgfS s₂ hs₂]
      congr 2
      dsimp [s₂]
      ring_nf
    have hPpos : 0 < 1 - t + 2 * t ^ 2 := by
      nlinarith [sq_nonneg (t - 1 / 4)]
    have hAnneg : 0 ≤ ∫ z : Fin m → ℝ, U z ^ 2
        ∂cool_gaussian_column_measure m :=
      integral_nonneg (fun z => sq_nonneg (U z))
    have hUpow : (∫ z : Fin m → ℝ, U z ^ 2
          ∂cool_gaussian_column_measure m) ^ (1 / 2 : ℝ) ≤
        Real.exp (-t / 2 + t ^ 2) := by
      calc
        (∫ z : Fin m → ℝ, U z ^ 2
            ∂cool_gaussian_column_measure m) ^ (1 / 2 : ℝ) ≤
            (1 - t + 2 * t ^ 2) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hAnneg hfold (by norm_num)
        _ = Real.exp ((1 / 2 : ℝ) *
            Real.log (1 - t + 2 * t ^ 2)) :=
          by
            rw [Real.rpow_def_of_pos hPpos]
            congr 1
            ring
        _ ≤ Real.exp (-t / 2 + t ^ 2) := by
          apply Real.exp_le_exp.mpr
          have hlog := Real.log_le_sub_one_of_pos hPpos
          nlinarith
    have hm4real : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have ht_lt_m : t < (m : ℝ) := by nlinarith
    have ha : 0 < 1 - t / (m : ℝ) :=
      sub_pos.mpr ((div_lt_one hmreal).2 ht_lt_m)
    have hden3 : (3 : ℝ) ≤ (m : ℝ) - t := by nlinarith
    have hdenpos : 0 < (m : ℝ) - t := by linarith
    have hinvsub : (1 - t / (m : ℝ))⁻¹ - 1 =
        t / ((m : ℝ) - t) := by
      field_simp [ne_of_gt hmreal, ne_of_gt hdenpos]
      ring
    have hloginv : -Real.log (1 - t / (m : ℝ)) ≤
        t / ((m : ℝ) - t) := by
      have hlog := Real.one_sub_inv_le_log_of_pos ha
      rw [show 1 - (1 - t / (m : ℝ))⁻¹ =
          -((1 - t / (m : ℝ))⁻¹ - 1) by ring, hinvsub] at hlog
      linarith
    have hrem : (m : ℝ) / 4 * (t / ((m : ℝ) - t)) ≤
        t / 4 + t ^ 2 / 12 := by
      have heq : (m : ℝ) / 4 * (t / ((m : ℝ) - t)) =
          t / 4 + t ^ 2 / (4 * ((m : ℝ) - t)) := by
        field_simp [ne_of_gt hdenpos]
        ring
      rw [heq]
      gcongr
      nlinarith
    have hgausslog : -(m : ℝ) / 4 * Real.log (1 - t / (m : ℝ)) ≤
        t / 4 + t ^ 2 / 12 := by
      calc
        -(m : ℝ) / 4 * Real.log (1 - t / (m : ℝ)) =
            (m : ℝ) / 4 * (-Real.log (1 - t / (m : ℝ))) := by ring
        _ ≤ (m : ℝ) / 4 * (t / ((m : ℝ) - t)) :=
          mul_le_mul_of_nonneg_left hloginv (by positivity)
        _ ≤ t / 4 + t ^ 2 / 12 := hrem
    have hVpow : (∫ z : Fin m → ℝ, V z ^ 2
          ∂cool_gaussian_column_measure m) ^ (1 / 2 : ℝ) ≤
        Real.exp (t / 4 + t ^ 2 / 12) := by
      rw [hV2eval]
      have hbase : 0 < 1 / Real.sqrt (1 - t / (m : ℝ)) := by positivity
      rw [Real.rpow_def_of_pos (pow_pos hbase m), Real.log_pow,
        one_div, Real.log_inv, Real.log_sqrt ha.le]
      apply Real.exp_le_exp.mpr
      norm_num
      nlinarith [hgausslog]
    have hcs' : (∫ z : Fin m → ℝ, U z * V z
          ∂cool_gaussian_column_measure m) ≤
        (∫ z : Fin m → ℝ, U z ^ 2
          ∂cool_gaussian_column_measure m) ^ (1 / 2 : ℝ) *
        (∫ z : Fin m → ℝ, V z ^ 2
          ∂cool_gaussian_column_measure m) ^ (1 / 2 : ℝ) := by
      simpa [U, V, Real.norm_eq_abs, abs_of_pos] using hcs
    have hprod : (∫ z : Fin m → ℝ, U z * V z
          ∂cool_gaussian_column_measure m) ≤
        Real.exp (-t / 2 + t ^ 2) *
          Real.exp (t / 4 + t ^ 2 / 12) := by
      calc
        (∫ z : Fin m → ℝ, U z * V z
            ∂cool_gaussian_column_measure m) ≤
            (∫ z : Fin m → ℝ, U z ^ 2
              ∂cool_gaussian_column_measure m) ^ (1 / 2 : ℝ) *
            (∫ z : Fin m → ℝ, V z ^ 2
              ∂cool_gaussian_column_measure m) ^ (1 / 2 : ℝ) := hcs'
        _ ≤ Real.exp (-t / 2 + t ^ 2) *
            Real.exp (t / 4 + t ^ 2 / 12) := by
          gcongr
    calc
      ProbabilityTheory.mgf
          (fun z : Fin m → ℝ => (1 / 4 : ℝ) -
            (|z first| - (∑ j : Fin m, z j ^ 2) / (4 * (m : ℝ))))
          (cool_gaussian_column_measure m) t =
          Real.exp (t / 4) *
            ∫ z : Fin m → ℝ, U z * V z
              ∂cool_gaussian_column_measure m := by
        unfold ProbabilityTheory.mgf
        rw [← integral_const_mul]
        congr 1
        funext z
        dsimp only [U, V, S, X]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        field_simp [ne_of_gt hmreal]
        ring
      _ ≤ Real.exp (t / 4) *
          (Real.exp (-t / 2 + t ^ 2) *
            Real.exp (t / 4 + t ^ 2 / 12)) :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
      _ = Real.exp (t / 4 +
          ((-t / 2 + t ^ 2) + (t / 4 + t ^ 2 / 12))) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp (2 * t ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg t]
  refine ⟨upward, downward, ?_, ?_, ?_, ?_⟩
  · have hpair : ProbabilityTheory.iIndepFun
        (fun i : Fin length => fun A => (Ahat i A, Dhat i A))
        (cool_gaussian_matrix_measure m n) := by
      have hindepZ' : ProbabilityTheory.iIndepFun Z
          (cool_gaussian_matrix_measure m n) := by
        simpa [Z] using hindepZ
      have hp := hindepZ'.comp
        (fun _ z =>
          (‖(EuclideanSpace.equiv (Fin m) ℝ).symm z‖,
            |z first| - (∑ j : Fin m, (z j) ^ 2) / (4 * (m : ℝ))))
        (fun _ => by fun_prop)
      convert hp using 1 <;> simp [Ahat, Dhat, Function.comp_def]
    have hrev := hpair.precomp Fin.rev_injective
    simpa [upward, downward] using hrev
  · intro i
    simp only [upward, i.isLt, dif_pos]
    let k : Fin length := Fin.rev i
    rcases cool_standard_gaussian_norm_tail m with ⟨hmeasA, htailA⟩
    refine ⟨?_, ?_⟩
    · simpa [Ahat, k, Function.comp_def] using hmeasA.comp (hZmeas k)
    · intro u hu
      have hset : MeasurableSet
          {z : Fin m → ℝ | Real.sqrt (m : ℝ) + u <
            ‖(EuclideanSpace.equiv (Fin m) ℝ).symm z‖} :=
        measurableSet_lt measurable_const (by fun_prop)
      have hmeasure :
          (cool_gaussian_matrix_measure m n).real
              {A | Real.sqrt (m : ℝ) + u < Ahat k A} =
            (Measure.map (Z k) (cool_gaussian_matrix_measure m n)).real
              {z | Real.sqrt (m : ℝ) + u <
                ‖(EuclideanSpace.equiv (Fin m) ℝ).symm z‖} := by
        have happ := Measure.map_apply
          (μ := cool_gaussian_matrix_measure m n) (hZmeas k) hset
        exact congrArg ENNReal.toReal happ.symm
      calc
        (cool_gaussian_matrix_measure m n).real
            {A | Real.sqrt (m : ℝ) + u < Ahat k A} =
            (Measure.map (Z k) (cool_gaussian_matrix_measure m n)).real
              {z | Real.sqrt (m : ℝ) + u <
                ‖(EuclideanSpace.equiv (Fin m) ℝ).symm z‖} := hmeasure
        _ = (cool_gaussian_column_measure m).real
              {z | Real.sqrt (m : ℝ) + u <
                ‖(EuclideanSpace.equiv (Fin m) ℝ).symm z‖} := by
                  rw [hZlaw k]
        _ ≤ 2 * Real.exp (-(u ^ 2) / 2) := htailA u hu
  · intro i
    simp only [downward, i.isLt, dif_pos]
    let k : Fin length := Fin.rev i
    let f : (Fin m → ℝ) → ℝ := fun z =>
      |z first| - (∑ j : Fin m, z j ^ 2) / (4 * (m : ℝ))
    rcases hstandardB with ⟨hfmeas, hfbound⟩
    have hDcomp : Dhat k = f ∘ Z k := by
      funext A
      simp [Dhat, f, Function.comp_def]
    rw [hDcomp]
    refine ⟨hfmeas.comp (hZmeas k), ?_⟩
    intro t ht0 ht1
    rcases hfbound t ht0 ht1 with ⟨hfint, hfmgf⟩
    refine ⟨?_, ?_⟩
    · rw [← hZlaw k] at hfint
      exact (integrable_map_measure
        ((by fun_prop : Measurable
          (fun z => Real.exp (t * ((1 / 4 : ℝ) - f z)))).aestronglyMeasurable)
        (hZmeas k).aemeasurable).mp hfint
    · change ProbabilityTheory.mgf
          (((fun x : ℝ => (1 / 4 : ℝ) - x) ∘ f) ∘ Z k)
          (cool_gaussian_matrix_measure m n) t ≤ _
      rw [← ProbabilityTheory.mgf_map
        (Y := Z k) (X := (fun x : ℝ => (1 / 4 : ℝ) - x) ∘ f)
        (μ := cool_gaussian_matrix_measure m n) (t := t)
        (hZmeas k).aemeasurable
        ((by fun_prop : Measurable
          (fun z => Real.exp (t * (((1 / 4 : ℝ) - ·) ∘ f) z))).aestronglyMeasurable)]
      rw [hZlaw k]
      simpa [Function.comp_def] using hfmgf
  · have hAhat_norm (i : Fin length) (A : cool_matrix m n) :
        Ahat i A = ‖cool_column A (index i)‖ := by
      simp [Ahat, Z, cool_column]
    have hsumZ (i : Fin length) (A : cool_matrix m n) :
        (∑ j : Fin m, (Z i A j) ^ 2) =
          ‖cool_column A (index i)‖ ^ 2 := by
      calc
        (∑ j : Fin m, (Z i A j) ^ 2) =
            ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (Z i A)‖ ^ 2 :=
          by
            convert (EuclideanSpace.real_norm_sq_eq
              ((EuclideanSpace.equiv (Fin m) ℝ).symm (Z i A))).symm using 1 <;>
              rfl
        _ = ‖cool_column A (index i)‖ ^ 2 := by
          change ‖R i A (cool_column A (index i))‖ ^ 2 = _
          rw [(R i A).norm_map]
    have hcoordZ (i : Fin length) (A : cool_matrix m n) :
        Z i A first = inner ℝ (direction i A) (cool_column A (index i)) := by
      calc
        Z i A first = inner ℝ e (R i A (cool_column A (index i))) := by
          change (R i A (cool_column A (index i))) first = _
          rw [show e = EuclideanSpace.single first 1 by rfl,
            EuclideanSpace.inner_single_left]
          simp
        _ = inner ℝ (R i A (direction i A))
            (R i A (cool_column A (index i))) := by rw [hRdirection]
        _ = inner ℝ (direction i A) (cool_column A (index i)) :=
          (R i A).inner_map_map _ _
    have hstep (i : Fin length) (A : cool_matrix m n) :
        cool_state n m B K A (start + i.1 + 1) =
          (let y := cool_state n m B K A (start + i.1)
           let a := cool_column A (index i)
           if ‖y - (b : ℝ) • a‖ ≤ ‖y + (b : ℝ) • a‖ then
             y - (b : ℝ) • a
           else y + (b : ℝ) • a) := by
      rw [cool_state]
      simp only [dif_pos (show start + i.1 < n by omega)]
      rw [htemperature (index i) (by simp [index]) (by
        simp only [index, Fin.is_lt]
        omega)]
    have hcoord_norm (i : Fin length) (A : cool_matrix m n)
        (hy : cool_state n m B K A (start + i.1) ≠ 0) :
        |Z i A first| =
          |inner ℝ (cool_state n m B K A (start + i.1))
            (cool_column A (index i))| /
            ‖cool_state n m B K A (start + i.1)‖ := by
      rw [hcoordZ, show direction i A =
          ‖cool_state n m B K A (start + i.1)‖⁻¹ •
            cool_state n m B K A (start + i.1) by
        simp [direction, hy]]
      simp only [inner_smul_left, conj_trivial, abs_mul, abs_inv, abs_norm]
      simpa only [div_eq_mul_inv, mul_comm]
    have hDhat_formula (i : Fin length) (A : cool_matrix m n)
        (hy : cool_state n m B K A (start + i.1) ≠ 0) :
        Dhat i A =
          |inner ℝ (cool_state n m B K A (start + i.1))
            (cool_column A (index i))| /
              ‖cool_state n m B K A (start + i.1)‖ -
            ‖cool_column A (index i)‖ ^ 2 / (4 * (m : ℝ)) := by
      rw [show Dhat i A = |Z i A first| -
          (∑ j : Fin m, (Z i A j) ^ 2) / (4 * (m : ℝ)) by rfl,
        hsumZ, hcoord_norm i A hy]
    have hstep_out (i : Fin length) (A : cool_matrix m n) :
        ‖cool_state n m B K A (start + i.1 + 1)‖ -
            ‖cool_state n m B K A (start + i.1)‖ ≤
          (b : ℝ) * Ahat i A := by
      rw [hstep]
      dsimp only
      split_ifs
      · rw [hAhat_norm, norm_sub_rev]
        calc
          ‖(b : ℝ) • cool_column A (index i) -
                cool_state n m B K A (start + i.1)‖ -
              ‖cool_state n m B K A (start + i.1)‖ ≤
              ‖(b : ℝ) • cool_column A (index i)‖ :=
            sub_le_iff_le_add.mpr (norm_sub_le _ _)
          _ = (b : ℝ) * ‖cool_column A (index i)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      · rw [hAhat_norm]
        calc
          ‖cool_state n m B K A (start + i.1) +
                (b : ℝ) • cool_column A (index i)‖ -
              ‖cool_state n m B K A (start + i.1)‖ ≤
              ‖(b : ℝ) • cool_column A (index i)‖ :=
            sub_le_iff_le_add.mpr (by
              simpa only [add_comm] using
                norm_add_le (cool_state n m B K A (start + i.1))
                  ((b : ℝ) • cool_column A (index i)))
          _ = (b : ℝ) * ‖cool_column A (index i)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsign_minus (y a : EuclideanSpace ℝ (Fin m))
        (hc : ‖y - (b : ℝ) • a‖ ≤ ‖y + (b : ℝ) • a‖) :
        0 ≤ inner ℝ y a := by
      have hs : ‖y - (b : ℝ) • a‖ ^ 2 ≤
          ‖y + (b : ℝ) • a‖ ^ 2 := by
        nlinarith [norm_nonneg (y - (b : ℝ) • a),
          norm_nonneg (y + (b : ℝ) • a)]
      rw [norm_sub_sq_real, norm_add_sq_real] at hs
      simp only [inner_smul_right, conj_trivial] at hs
      have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
      nlinarith
    have hsign_plus (y a : EuclideanSpace ℝ (Fin m))
        (hc : ¬ ‖y - (b : ℝ) • a‖ ≤ ‖y + (b : ℝ) • a‖) :
        inner ℝ y a ≤ 0 := by
      have hs : ‖y + (b : ℝ) • a‖ ^ 2 ≤
          ‖y - (b : ℝ) • a‖ ^ 2 := by
        have hlt := lt_of_not_ge hc
        nlinarith [norm_nonneg (y - (b : ℝ) • a),
          norm_nonneg (y + (b : ℝ) • a)]
      rw [norm_sub_sq_real, norm_add_sq_real] at hs
      simp only [inner_smul_right, conj_trivial] at hs
      have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
      nlinarith
    have hstep_in (i : Fin length) (A : cool_matrix m n)
        (hlarge : (2 : ℝ) * (b : ℝ) * (m : ℝ) ≤
          ‖cool_state n m B K A (start + i.1)‖) :
        ‖cool_state n m B K A (start + i.1 + 1)‖ -
            ‖cool_state n m B K A (start + i.1)‖ ≤
          -(b : ℝ) * Dhat i A := by
      let y := cool_state n m B K A (start + i.1)
      let a := cool_column A (index i)
      have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
      have hypos : 0 < ‖y‖ := by
        dsimp only [y]
        exact lt_of_lt_of_le (by positivity) hlarge
      have hy : y ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hypos)
      have hD := hDhat_formula i A hy
      have hcoef : (b : ℝ) ^ 2 / (2 * ‖y‖) ≤
          (b : ℝ) / (4 * (m : ℝ)) := by
        apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ‖y‖)
          (by positivity : (0 : ℝ) < 4 * (m : ℝ))).2
        calc
          (b : ℝ) ^ 2 * (4 * (m : ℝ)) =
              (2 * (b : ℝ)) *
                ((2 : ℝ) * (b : ℝ) * (m : ℝ)) := by ring
          _ ≤ (2 * (b : ℝ)) * ‖y‖ :=
            mul_le_mul_of_nonneg_left hlarge (by positivity)
          _ = (b : ℝ) * (2 * ‖y‖) := by ring
      have hquad : (b : ℝ) ^ 2 * ‖a‖ ^ 2 / (2 * ‖y‖) ≤
          (b : ℝ) * ‖a‖ ^ 2 / (4 * (m : ℝ)) := by
        calc
          (b : ℝ) ^ 2 * ‖a‖ ^ 2 / (2 * ‖y‖) =
              ((b : ℝ) ^ 2 / (2 * ‖y‖)) * ‖a‖ ^ 2 := by ring
          _ ≤ ((b : ℝ) / (4 * (m : ℝ))) * ‖a‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖a‖)
          _ = (b : ℝ) * ‖a‖ ^ 2 / (4 * (m : ℝ)) := by ring
      rw [hstep]
      change ‖(if ‖y - (b : ℝ) • a‖ ≤ ‖y + (b : ℝ) • a‖ then
          y - (b : ℝ) • a else y + (b : ℝ) • a)‖ - ‖y‖ ≤
        -(b : ℝ) * Dhat i A
      split_ifs with hc
      · have hlin := cool_norm_increment_linearization m y a (-(b : ℝ)) hypos
        have hsign := hsign_minus y a hc
        rw [hD, abs_of_nonneg hsign]
        calc
          ‖y - (b : ℝ) • a‖ - ‖y‖ ≤
              (2 * (-(b : ℝ)) * inner ℝ y a +
                (-(b : ℝ)) ^ 2 * ‖a‖ ^ 2) / (2 * ‖y‖) := by
            simpa [sub_eq_add_neg] using hlin
          _ = -(b : ℝ) * (inner ℝ y a / ‖y‖) +
              (b : ℝ) ^ 2 * ‖a‖ ^ 2 / (2 * ‖y‖) := by ring
          _ ≤ -(b : ℝ) * (inner ℝ y a / ‖y‖) +
              (b : ℝ) * ‖a‖ ^ 2 / (4 * (m : ℝ)) := by linarith
          _ = -(b : ℝ) *
              (inner ℝ y a / ‖y‖ - ‖a‖ ^ 2 / (4 * (m : ℝ))) := by ring
      · have hlin := cool_norm_increment_linearization m y a (b : ℝ) hypos
        have hsign := hsign_plus y a hc
        rw [hD, abs_of_nonpos hsign]
        calc
          ‖y + (b : ℝ) • a‖ - ‖y‖ ≤
              (2 * (b : ℝ) * inner ℝ y a +
                (b : ℝ) ^ 2 * ‖a‖ ^ 2) / (2 * ‖y‖) := hlin
          _ = -(b : ℝ) * ((-inner ℝ y a) / ‖y‖) +
              (b : ℝ) ^ 2 * ‖a‖ ^ 2 / (2 * ‖y‖) := by ring
          _ ≤ -(b : ℝ) * ((-inner ℝ y a) / ‖y‖) +
              (b : ℝ) * ‖a‖ ^ 2 / (4 * (m : ℝ)) := by linarith
          _ = -(b : ℝ) *
              ((-inner ℝ y a) / ‖y‖ - ‖a‖ ^ 2 / (4 * (m : ℝ))) := by ring
    let G : ℕ → cool_matrix m n → ℝ := fun r A =>
      ‖cool_state n m B K A (start + (length - r))‖
    have hrev_step_out (r : ℕ) (hr : r < length) (A : cool_matrix m n) :
        G r A - G (r + 1) A ≤ (b : ℝ) * upward r A := by
      have h := hstep_out (Fin.rev ⟨r, hr⟩) A
      have hpost : start + (Fin.rev ⟨r, hr⟩).1 + 1 =
          start + (length - r) := by
        simp only [Fin.val_rev]
        omega
      have hpre : start + (Fin.rev ⟨r, hr⟩).1 =
          start + (length - (r + 1)) := by
        simp only [Fin.val_rev]
      rw [show upward r A = Ahat (Fin.rev ⟨r, hr⟩) A by
        simp [upward, hr]]
      dsimp only [G]
      rw [← hpost, ← hpre]
      exact h
    have hrev_step_in (r : ℕ) (hr : r < length) (A : cool_matrix m n)
        (hlarge : (2 : ℝ) * (b : ℝ) * (m : ℝ) ≤ G (r + 1) A) :
        G r A - G (r + 1) A ≤ -(b : ℝ) * downward r A := by
      have hlarge' : (2 : ℝ) * (b : ℝ) * (m : ℝ) ≤
          ‖cool_state n m B K A
            (start + (Fin.rev ⟨r, hr⟩).1)‖ := by
        have hpre : start + (Fin.rev ⟨r, hr⟩).1 =
            start + (length - (r + 1)) := by
          simp only [Fin.val_rev]
        rw [hpre]
        exact hlarge
      have h := hstep_in (Fin.rev ⟨r, hr⟩) A hlarge'
      have hpost : start + (Fin.rev ⟨r, hr⟩).1 + 1 =
          start + (length - r) := by
        simp only [Fin.val_rev]
        omega
      have hpre : start + (Fin.rev ⟨r, hr⟩).1 =
          start + (length - (r + 1)) := by
        simp only [Fin.val_rev]
      rw [show downward r A = Dhat (Fin.rev ⟨r, hr⟩) A by
        simp [downward, hr]]
      dsimp only [G]
      rw [← hpost, ← hpre]
      exact h
    have hsubset :
        {A | ‖cool_state n m B K A start‖ ≤
              (8 : ℝ) * (b : ℝ) * (m : ℝ) ∧
            (4 : ℝ) * (b : ℝ) * (m : ℝ) <
              ‖cool_state n m B K A (start + length)‖} ⊆
          {A | (∑ i ∈ Finset.range length, downward i A) ≤
              (4 : ℝ) * (m : ℝ)} ∪
            ⋃ i : Fin length,
              {A | (2 : ℝ) * (m : ℝ) <
                upward i.1 A -
                  ∑ k ∈ Finset.range i.1, downward k A} := by
      intro A hA
      by_cases hdown :
          (∑ i ∈ Finset.range length, downward i A) ≤
            (4 : ℝ) * (m : ℝ)
      · exact Set.mem_union_left _ hdown
      · apply Set.mem_union_right
        by_contra hescape
        have hnoescape (r : ℕ) (hr : r < length) :
            upward r A - ∑ k ∈ Finset.range r, downward k A ≤
              (2 : ℝ) * (m : ℝ) := by
          apply le_of_not_gt
          intro hbad
          apply hescape
          exact Set.mem_iUnion.2 ⟨⟨r, hr⟩, hbad⟩
        have hstart :
            G length A ≤ (8 : ℝ) * (b : ℝ) * (m : ℝ) := by
          simpa [G] using hA.1
        have hendA :
            (4 : ℝ) * (b : ℝ) * (m : ℝ) < G 0 A := by
          simpa [G] using hA.2
        have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
        have hback : ∀ r : ℕ, r ≤ length →
            G 0 A - G r A ≤
                -(b : ℝ) * ∑ k ∈ Finset.range r, downward k A ∧
              (r = 0 ∨
                (2 : ℝ) * (b : ℝ) * (m : ℝ) ≤ G r A) := by
          intro r
          induction r with
          | zero =>
              intro hr
              constructor
              · simp
              · exact Or.inl rfl
          | succ r ih =>
              intro hr
              have hrlt : r < length := by omega
              rcases ih (by omega) with ⟨hcum, _⟩
              have hout := hrev_step_out r hrlt A
              have hsmall_bound := hnoescape r hrlt
              have hlarge :
                  (2 : ℝ) * (b : ℝ) * (m : ℝ) ≤ G (r + 1) A := by
                by_contra hsmall
                have hsmall' :
                    G (r + 1) A <
                      (2 : ℝ) * (b : ℝ) * (m : ℝ) :=
                  lt_of_not_ge hsmall
                have hdiff :
                    G 0 A - G (r + 1) A ≤
                      (2 : ℝ) * (b : ℝ) * (m : ℝ) := by
                  calc
                    G 0 A - G (r + 1) A =
                        (G 0 A - G r A) +
                          (G r A - G (r + 1) A) := by ring
                    _ ≤ -(b : ℝ) *
                          ∑ k ∈ Finset.range r, downward k A +
                        (b : ℝ) * upward r A :=
                      add_le_add hcum hout
                    _ = (b : ℝ) *
                        (upward r A -
                          ∑ k ∈ Finset.range r, downward k A) := by ring
                    _ ≤ (b : ℝ) * ((2 : ℝ) * (m : ℝ)) :=
                      mul_le_mul_of_nonneg_left hsmall_bound hbR.le
                    _ = (2 : ℝ) * (b : ℝ) * (m : ℝ) := by ring
                linarith
              have hin := hrev_step_in r hrlt A hlarge
              constructor
              · calc
                  G 0 A - G (r + 1) A =
                      (G 0 A - G r A) +
                        (G r A - G (r + 1) A) := by ring
                  _ ≤ -(b : ℝ) *
                        ∑ k ∈ Finset.range r, downward k A +
                      -(b : ℝ) * downward r A :=
                    add_le_add hcum hin
                  _ = -(b : ℝ) *
                      ∑ k ∈ Finset.range (r + 1), downward k A := by
                    rw [Finset.sum_range_succ]
                    ring
              · exact Or.inr hlarge
        rcases hback length le_rfl with ⟨hfinal, _⟩
        have hsum :
            (4 : ℝ) * (m : ℝ) <
              ∑ i ∈ Finset.range length, downward i A :=
          lt_of_not_ge hdown
        have hprod : 0 < (b : ℝ) *
            ((∑ i ∈ Finset.range length, downward i A) -
              (4 : ℝ) * (m : ℝ)) :=
          mul_pos hbR (sub_pos.mpr hsum)
        have hGlength :
            G length A = ‖cool_state n m B K A start‖ := by
          simp [G]
        rw [hGlength] at hfinal
        linarith
    calc
      (cool_gaussian_matrix_measure m n).real
          {A | ‖cool_state n m B K A start‖ ≤
                (8 : ℝ) * (b : ℝ) * (m : ℝ) ∧
              (4 : ℝ) * (b : ℝ) * (m : ℝ) <
                ‖cool_state n m B K A (start + length)‖} ≤
          (cool_gaussian_matrix_measure m n).real
            ({A | (∑ i ∈ Finset.range length, downward i A) ≤
                (4 : ℝ) * (m : ℝ)} ∪
              ⋃ i : Fin length,
                {A | (2 : ℝ) * (m : ℝ) <
                  upward i.1 A -
                    ∑ k ∈ Finset.range i.1, downward k A}) :=
        MeasureTheory.measureReal_mono hsubset (measure_ne_top _ _)
      _ ≤ (cool_gaussian_matrix_measure m n).real
              {A | (∑ i ∈ Finset.range length, downward i A) ≤
                (4 : ℝ) * (m : ℝ)} +
            (cool_gaussian_matrix_measure m n).real
              (⋃ i : Fin length,
                {A | (2 : ℝ) * (m : ℝ) <
                  upward i.1 A -
                    ∑ k ∈ Finset.range i.1, downward k A}) :=
        MeasureTheory.measureReal_union_le _ _
      _ ≤ (cool_gaussian_matrix_measure m n).real
              {A | (∑ i ∈ Finset.range length, downward i A) ≤
                (4 : ℝ) * (m : ℝ)} +
            ∑ i : Fin length,
              (cool_gaussian_matrix_measure m n).real
                {A | (2 : ℝ) * (m : ℝ) <
                  upward i.1 A -
                    ∑ k ∈ Finset.range i.1, downward k A} := by
        gcongr
        exact MeasureTheory.measureReal_iUnion_fintype_le _
      _ = (cool_gaussian_matrix_measure m n).real
              {A | (∑ i ∈ Finset.range length, downward i A) ≤
                (4 : ℝ) * (m : ℝ)} +
            ∑ t ∈ Finset.range length,
              (cool_gaussian_matrix_measure m n).real
                {A | (2 : ℝ) * (m : ℝ) <
                  upward t A -
                    ∑ i ∈ Finset.range t, downward i A} := by
        congr 1
        exact Fin.sum_univ_eq_sum_range
          (fun t : ℕ =>
            (cool_gaussian_matrix_measure m n).real
              {A | (2 : ℝ) * (m : ℝ) <
                upward t A -
                  ∑ i ∈ Finset.range t, downward i A}) length

@[blueprint "lem:cool-independent-mgf-tail"
  (statement := /-- Let $(X_i)_{i\in I}$ be an independent family of measurable real random variables on a finite measure space, let $S\subset I$ be finite, and let $q,x\in\mathbb{R}$ with $q\ge0$.  Suppose that $e^{qX_i}$ is integrable and that $\mathbb{E}[e^{qX_i}]\le e^{2q^2}$ for every $i\in S$.  Then
  \[
    \mathbb{P}\!\left(x\le\sum_{i\in S}X_i\right)
      \le \exp\!\left(-qx+2q^2|S|\right).
  \] -/)
  (proof := /-- Apply the Chernoff bound at parameter $q$ to the sum over $S$.  Independence and measurability imply both integrability of the exponential of the sum and factorization of its moment-generating function.  Bound each factor by $e^{2q^2}$ and combine the resulting exponentials. -/)
  (title := /-- Chernoff bound for an independent finite sum -/)
  (latexEnv := "lemma")]
lemma cool_independent_mgf_tail {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ι → Ω → ℝ)
    (s : Finset ι) (q x : ℝ) (hq : 0 ≤ q)
    (hindep : ProbabilityTheory.iIndepFun X μ)
    (hmeas : ∀ i, Measurable (X i))
    (hint : ∀ i ∈ s, MeasureTheory.Integrable
      (fun ω => Real.exp (q * X i ω)) μ)
    (hmgf : ∀ i ∈ s, ProbabilityTheory.mgf (X i) μ q ≤
      Real.exp (2 * q ^ 2)) :
    μ.real {ω | x ≤ ∑ i ∈ s, X i ω} ≤
      Real.exp (-q * x + 2 * q ^ 2 * (s.card : ℝ)) := by
  have hsum_int := hindep.integrable_exp_mul_sum hmeas hint
  calc
    μ.real {ω | x ≤ ∑ i ∈ s, X i ω} ≤
        Real.exp (-q * x) *
          ProbabilityTheory.mgf (∑ i ∈ s, X i) μ q :=
      by simpa only [Finset.sum_apply] using
        ProbabilityTheory.measure_ge_le_exp_mul_mgf x hq hsum_int
    _ = Real.exp (-q * x) *
          ∏ i ∈ s, ProbabilityTheory.mgf (X i) μ q := by
      rw [hindep.mgf_sum hmeas s]
    _ ≤ Real.exp (-q * x) * ∏ _i ∈ s, Real.exp (2 * q ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact Finset.prod_le_prod (fun i _ => ProbabilityTheory.mgf_nonneg) hmgf
    _ = Real.exp (-q * x + 2 * q ^ 2 * (s.card : ℝ)) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      norm_num
      ring

@[blueprint "lem:cool-finite-exponential-sum"
  (statement := /-- For every $a>0$ and $m,L\in\mathbb{N}$,
  \[
    \sum_{t<L}e^{-a(m+t)}
      \le e^{-am}\bigl(1-e^{-a}\bigr)^{-1}.
  \] -/)
  (proof := /-- Factor $e^{-am}$ from the finite sum.  The remaining terms form an initial segment of the nonnegative geometric series with ratio $e^{-a}\in(0,1)$, so they are bounded by its sum $(1-e^{-a})^{-1}$. -/)
  (title := /-- Bound for a finite exponential series -/)
  (latexEnv := "lemma")]
lemma cool_finite_exponential_sum (a : ℝ) (ha : 0 < a) (m length : ℕ) :
    ∑ t ∈ Finset.range length,
        Real.exp (-a * ((m : ℝ) + (t : ℝ))) ≤
      Real.exp (-a * (m : ℝ)) * (1 - Real.exp (-a))⁻¹ := by
  have hr0 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  have hr1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha)
  have hsum := hasSum_geometric_of_lt_one hr0 hr1
  calc
    ∑ t ∈ Finset.range length,
        Real.exp (-a * ((m : ℝ) + (t : ℝ))) =
        Real.exp (-a * (m : ℝ)) *
          ∑ t ∈ Finset.range length, Real.exp (-a) ^ t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    _ ≤ Real.exp (-a * (m : ℝ)) * ∑' t : ℕ, Real.exp (-a) ^ t := by
      gcongr
      exact hsum.summable.sum_le_tsum (Finset.range length)
        (fun i _ => pow_nonneg hr0 i)
    _ = Real.exp (-a * (m : ℝ)) * (1 - Real.exp (-a))⁻¹ := by
      rw [hsum.tsum_eq]

@[blueprint "lem:cool-type-a-escape-tail"
  (statement := /-- Let $m,t\in\mathbb{N}$ with $m\ge4$, and let $X$ satisfy the type-$A$ comparison contract in dimension $m$.  Then
  \[
    \mathbb{P}\!\left(X>m+\frac{t}{8}\right)
      \le 2\exp\!\left(-\frac{m+t}{512}\right).
  \] -/)
  (proof := /-- In the type-$A$ contract take $u=m-\sqrt m+t/8$.  Since $m\ge4$, one has $\sqrt m\le m/2$, hence $u\ge m/2+t/8\ge0$.  The resulting Gaussian exponent satisfies $u^2/2\ge(m+t)/512$, which gives the stated weaker exponential bound. -/)
  (title := /-- Type-$A$ escape estimate -/)
  (latexEnv := "lemma")]
lemma cool_type_a_escape_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (m t : ℕ) (X : Ω → ℝ) (hm : 4 ≤ m)
    (hX : cool_type_a_comparison μ m X) :
    μ.real {ω | (m : ℝ) + (t : ℝ) / 8 < X ω} ≤
      2 * Real.exp (-((m : ℝ) + (t : ℝ)) / 512) := by
  rcases hX with ⟨hmeas, htail⟩
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hm4 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have ht0 : 0 ≤ (t : ℝ) := by positivity
  have hs0 : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) := Real.sq_sqrt hm0
  have hs_le : Real.sqrt (m : ℝ) ≤ (m : ℝ) / 2 := by
    nlinarith
  let u : ℝ := (m : ℝ) - Real.sqrt (m : ℝ) + (t : ℝ) / 8
  have hu : 0 ≤ u := by
    dsimp [u]
    nlinarith
  have hu_lower : (m : ℝ) / 2 + (t : ℝ) / 8 ≤ u := by
    dsimp [u]
    linarith
  have hexp : -(u ^ 2) / 2 ≤ -((m : ℝ) + (t : ℝ)) / 512 := by
    have hv0 : 0 ≤ (m : ℝ) / 2 + (t : ℝ) / 8 := by positivity
    nlinarith [sq_nonneg (u - ((m : ℝ) / 2 + (t : ℝ) / 8))]
  calc
    μ.real {ω | (m : ℝ) + (t : ℝ) / 8 < X ω} =
        μ.real {ω | Real.sqrt (m : ℝ) + u < X ω} := by
      congr 2 with ω
      dsimp [u]
      ring_nf
    _ ≤ 2 * Real.exp (-(u ^ 2) / 2) := htail u hu
    _ ≤ 2 * Real.exp (-((m : ℝ) + (t : ℝ)) / 512) := by
      gcongr

@[blueprint "lem:cool-type-b-finite-tail"
  (statement := /-- Let $(D_i)_{i\in I}$ be independent type-$B$ comparison variables on a finite measure space.  For every finite $S\subset I$ and every $x\in\mathbb{R}$,
  \[
    \mathbb{P}\!\left(x\le\sum_{i\in S}(1/4-D_i)\right)
      \le \exp\!\left(-\frac{x}{32}+\frac{|S|}{512}\right).
  \] -/)
  (proof := /-- Compose the independent variables with $y\mapsto1/4-y$.  The type-$B$ contract supplies measurability, integrability, and the moment-generating-function estimate at $q=1/32$.  Applying \cref{lem:cool-independent-mgf-tail} and simplifying the constants gives the result. -/)
  (title := /-- Finite-sum tail estimate for type-$B$ variables -/)
  (latexEnv := "lemma")]
lemma cool_type_b_finite_tail {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (D : ι → Ω → ℝ)
    (s : Finset ι) (x : ℝ)
    (hindep : ProbabilityTheory.iIndepFun D μ)
    (hD : ∀ i, cool_type_b_comparison μ (D i)) :
    μ.real {ω | x ≤ ∑ i ∈ s, ((1 / 4 : ℝ) - D i ω)} ≤
      Real.exp (-x / 32 + (s.card : ℝ) / 512) := by
  let Y : ι → Ω → ℝ := fun i ω => (1 / 4 : ℝ) - D i ω
  have hYindep : ProbabilityTheory.iIndepFun Y μ := by
    have hcomp := hindep.comp
      (fun _ => fun y : ℝ => (1 / 4 : ℝ) - y)
      (fun _ => measurable_const.sub measurable_id)
    simpa only [Y, Function.comp_def] using hcomp
  have hYmeas : ∀ i, Measurable (Y i) := by
    intro i
    exact measurable_const.sub (hD i).1
  have hYint : ∀ i ∈ s, MeasureTheory.Integrable
      (fun ω => Real.exp ((1 / 32 : ℝ) * Y i ω)) μ := by
    intro i hi
    exact (hD i).2 (1 / 32) (by norm_num) (by norm_num) |>.1
  have hYmgf : ∀ i ∈ s, ProbabilityTheory.mgf (Y i) μ (1 / 32) ≤
      Real.exp (2 * (1 / 32 : ℝ) ^ 2) := by
    intro i hi
    exact (hD i).2 (1 / 32) (by norm_num) (by norm_num) |>.2
  have htail := cool_independent_mgf_tail μ Y s (1 / 32) x
    (by norm_num) hYindep hYmeas hYint hYmgf
  norm_num [Y] at htail ⊢
  convert htail using 1 <;> ring_nf

@[blueprint "lem:cool-type-b-prefix-tail"
  (statement := /-- Let $D_0,\ldots,D_{L-1}$ be independent type-$B$ comparison variables on a finite measure space.  If $t\le L$, then for every $m\in\mathbb{N}$,
  \[
    \mathbb{P}\!\left(\sum_{i<t}D_i<-m+\frac{t}{8}\right)
      \le \exp\!\left(-\frac{m}{32}-\frac{t}{512}\right).
  \] -/)
  (proof := /-- Restrict the independent family along the injective inclusion $\operatorname{Fin}(t)\hookrightarrow\operatorname{Fin}(L)$.  The displayed event implies
  $m+t/8\le\sum_{i<t}(1/4-D_i)$.  Apply \cref{lem:cool-type-b-finite-tail} to this prefix and simplify the exponent. -/)
  (title := /-- Prefix lower-tail estimate for type-$B$ variables -/)
  (latexEnv := "lemma")]
lemma cool_type_b_prefix_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (length t m : ℕ)
    (D : ℕ → Ω → ℝ) (ht : t ≤ length)
    (hindep : ProbabilityTheory.iIndepFun
      (fun i : Fin length => D i.1) μ)
    (hD : ∀ i : Fin length, cool_type_b_comparison μ (D i.1)) :
    μ.real {ω | (∑ i ∈ Finset.range t, D i ω) <
        -(m : ℝ) + (t : ℝ) / 8} ≤
      Real.exp (-(m : ℝ) / 32 - (t : ℝ) / 512) := by
  let emb : Fin t → Fin length := fun i => ⟨i.1, lt_of_lt_of_le i.2 ht⟩
  have hemb : Function.Injective emb := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun z : Fin length => z.val) hij
  have hindep_t : ProbabilityTheory.iIndepFun
      (fun i : Fin t => D i.1) μ := by
    have hpre := hindep.precomp hemb
    simpa only [emb] using hpre
  have hD_t : ∀ i : Fin t, cool_type_b_comparison μ (D i.1) := by
    intro i
    exact hD (emb i)
  have htail := cool_type_b_finite_tail μ (fun i : Fin t => D i.1)
    Finset.univ ((m : ℝ) + (t : ℝ) / 8) hindep_t hD_t
  calc
    μ.real {ω | (∑ i ∈ Finset.range t, D i ω) <
        -(m : ℝ) + (t : ℝ) / 8} ≤
        μ.real {ω | (m : ℝ) + (t : ℝ) / 8 ≤
          ∑ i : Fin t, ((1 / 4 : ℝ) - D i.1 ω)} := by
      refine MeasureTheory.measureReal_mono ?_ (by finiteness)
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      rw [Fin.sum_univ_eq_sum_range
        (fun i => (1 / 4 : ℝ) - D i ω) t]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
      norm_num
      push_cast at hω ⊢
      linarith
    _ ≤ Real.exp (-((m : ℝ) + (t : ℝ) / 8) / 32 +
        ((Finset.univ : Finset (Fin t)).card : ℝ) / 512) := by
      exact htail
    _ = Real.exp (-(m : ℝ) / 32 - (t : ℝ) / 512) := by
      rw [Finset.card_univ, Fintype.card_fin]
      congr 1
      ring

@[blueprint "lem:cool-type-b-long-sum-tail"
  (statement := /-- Let $m,L\in\mathbb{N}$ with $L\ge64m$, and let $D_0,\ldots,D_{L-1}$ be independent type-$B$ comparison variables on a finite measure space.  Then
  \[
    \mathbb{P}\!\left(\sum_{i<L}D_i\le4m\right)
      \le \exp\!\left(-\frac{m}{512}\right).
  \] -/)
  (proof := /-- The event implies $L/4-4m\le\sum_{i<L}(1/4-D_i)$.  Apply \cref{lem:cool-type-b-finite-tail} to all $L$ variables.  Its exponent is $m/8-3L/512$, which is at most $-m/4$, and hence at most $-m/512$, because $L\ge64m$. -/)
  (title := /-- Lower tail for a long sum of type-$B$ variables -/)
  (latexEnv := "lemma")]
lemma cool_type_b_long_sum_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (m length : ℕ)
    (D : ℕ → Ω → ℝ) (hlength : 64 * m ≤ length)
    (hindep : ProbabilityTheory.iIndepFun
      (fun i : Fin length => D i.1) μ)
    (hD : ∀ i : Fin length, cool_type_b_comparison μ (D i.1)) :
    μ.real {ω | (∑ i ∈ Finset.range length, D i ω) ≤ 4 * (m : ℝ)} ≤
      Real.exp (-(m : ℝ) / 512) := by
  have htail := cool_type_b_finite_tail μ
    (fun i : Fin length => D i.1) Finset.univ
    ((length : ℝ) / 4 - 4 * (m : ℝ)) hindep hD
  calc
    μ.real {ω | (∑ i ∈ Finset.range length, D i ω) ≤ 4 * (m : ℝ)} ≤
        μ.real {ω | (length : ℝ) / 4 - 4 * (m : ℝ) ≤
          ∑ i : Fin length, ((1 / 4 : ℝ) - D i.1 ω)} := by
      refine MeasureTheory.measureReal_mono ?_ (by finiteness)
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      rw [Fin.sum_univ_eq_sum_range
        (fun i => (1 / 4 : ℝ) - D i ω) length]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
      norm_num
      push_cast at hω ⊢
      linarith
    _ ≤ Real.exp (-((length : ℝ) / 4 - 4 * (m : ℝ)) / 32 +
        ((Finset.univ : Finset (Fin length)).card : ℝ) / 512) := htail
    _ ≤ Real.exp (-(m : ℝ) / 512) := by
      rw [Finset.card_univ, Fintype.card_fin]
      gcongr
      have hlengthR : (64 : ℝ) * (m : ℝ) ≤ (length : ℝ) := by
        exact_mod_cast hlength
      norm_num
      linarith

@[blueprint "lem:cool-comparison-exponential-tail"
  (statement := /-- There are absolute constants $K_0\in\mathbb{N}$ and $C,c>0$ such that the following holds for every $m,n,\ell\in\mathbb{N}$.  For each $i\in\mathbb{N}$, let $A_i$ and $D_i$ be real-valued functions on the space of $m\times n$ matrices.  Suppose that $m\ge4$, that $\ell\ge K_0m$, and that the pairs $(A_i,D_i)_{0\le i<\ell}$ are independent under the Gaussian matrix law.  If every $A_i$ with $i<\ell$ satisfies the type-$A$ contract in dimension $m$ and every $D_i$ with $i<\ell$ satisfies the type-$B$ contract, then
  \[
    \mathbb{P}\!\left(\sum_{i<\ell}D_i\le4m\right)
      +\sum_{t<\ell}
        \mathbb{P}\!\left(A_t-\sum_{i<t}D_i>2m\right)
      \le Ce^{-cm}.
  \] -/)
  (proof := /-- Set
  \[
    K_0=64,\qquad c=\frac1{512},\qquad
    C=1+3\bigl(1-e^{-1/512}\bigr)^{-1}.
  \]
  These constants are positive.  Projecting the independent pairs onto their second coordinates shows that the variables $D_i$ are independent.  Since $\ell\ge64m$, \,\cref{lem:cool-type-b-long-sum-tail} gives
  \[
    \mathbb{P}\!\left(\sum_{i<\ell}D_i\le4m\right)
      \le e^{-m/512}.
  \]

  Fix $t<\ell$.  The event
  $A_t-\sum_{i<t}D_i>2m$ is contained in the union of the events
  \[
    A_t>m+\frac{t}{8}
    \quad\text{and}\quad
    \sum_{i<t}D_i<-m+\frac{t}{8}.
  \]
  By \,\cref{lem:cool-type-a-escape-tail} and
  \,\cref{lem:cool-type-b-prefix-tail}, respectively, their probabilities are at most
  $2e^{-(m+t)/512}$ and $e^{-m/32-t/512}$.  The latter is at most
  $e^{-(m+t)/512}$, so the $t$th escape probability is at most
  $3e^{-(m+t)/512}$.  Finally, \,\cref{lem:cool-finite-exponential-sum} yields
  \[
    \sum_{t<\ell}3e^{-(m+t)/512}
      \le 3e^{-m/512}\bigl(1-e^{-1/512}\bigr)^{-1}.
  \]
  Adding the long-sum estimate gives $Ce^{-cm}$ with the constants above. -/)
  (title := /-- Exponential tail for the comparison process -/)
  (latexEnv := "lemma")]
lemma cool_comparison_exponential_tail :
    ∃ K₀ : ℕ, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (m n length : ℕ)
        (upward downward : ℕ → cool_matrix m n → ℝ),
        4 ≤ m → K₀ * m ≤ length →
        ProbabilityTheory.iIndepFun
          (fun i : Fin length => fun A =>
            (upward i.1 A, downward i.1 A))
          (cool_gaussian_matrix_measure m n) →
        (∀ i : Fin length,
          cool_type_a_comparison (cool_gaussian_matrix_measure m n) m
            (upward i.1)) →
        (∀ i : Fin length,
          cool_type_b_comparison (cool_gaussian_matrix_measure m n)
            (downward i.1)) →
        (cool_gaussian_matrix_measure m n).real
              {A | (∑ i ∈ Finset.range length, downward i A) ≤
                (4 : ℝ) * (m : ℝ)} +
            ∑ t ∈ Finset.range length,
              (cool_gaussian_matrix_measure m n).real
                {A | (2 : ℝ) * (m : ℝ) <
                  upward t A -
                    ∑ i ∈ Finset.range t, downward i A} ≤
          C * Real.exp (-c * (m : ℝ)) := by
  let q : ℝ := Real.exp (-(1 : ℝ) / 512)
  have hq_lt : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hden : 0 < 1 - q := sub_pos.mpr hq_lt
  have hC : 0 < 1 + 3 * (1 - q)⁻¹ := by positivity
  refine ⟨64, 1 + 3 * (1 - q)⁻¹, 1 / 512, hC, by norm_num, ?_⟩
  intro m n length upward downward hm hlength hindep hup hdown
  let μ := cool_gaussian_matrix_measure m n
  letI : IsFiniteMeasure μ := by
    dsimp [μ, cool_gaussian_matrix_measure, cool_gaussian_column_measure]
    infer_instance
  have hindepD : ProbabilityTheory.iIndepFun
      (fun i : Fin length => downward i.1) μ := by
    have hcomp := hindep.comp
      (fun _ => fun p : ℝ × ℝ => p.2)
      (fun _ => measurable_snd)
    simpa only [μ, Function.comp_def] using hcomp
  have hlong : μ.real
      {A | (∑ i ∈ Finset.range length, downward i A) ≤
        (4 : ℝ) * (m : ℝ)} ≤ Real.exp (-(m : ℝ) / 512) := by
    exact cool_type_b_long_sum_tail μ m length downward hlength hindepD hdown
  have hsplit : ∀ t ∈ Finset.range length,
      μ.real {A | (2 : ℝ) * (m : ℝ) <
        upward t A - ∑ i ∈ Finset.range t, downward i A} ≤
        3 * Real.exp (-((m : ℝ) + (t : ℝ)) / 512) := by
    intro t ht
    have htlt : t < length := Finset.mem_range.mp ht
    have hA := cool_type_a_escape_tail μ m t (upward t) hm
      (hup ⟨t, htlt⟩)
    have hB := cool_type_b_prefix_tail μ length t m downward htlt.le
      hindepD hdown
    calc
      μ.real {A | (2 : ℝ) * (m : ℝ) <
          upward t A - ∑ i ∈ Finset.range t, downward i A} ≤
          μ.real ({A | (m : ℝ) + (t : ℝ) / 8 < upward t A} ∪
            {A | (∑ i ∈ Finset.range t, downward i A) <
              -(m : ℝ) + (t : ℝ) / 8}) := by
        refine MeasureTheory.measureReal_mono ?_ (by finiteness)
        intro A hAevent
        simp only [Set.mem_setOf_eq, Set.mem_union] at hAevent ⊢
        by_cases hlarge : (m : ℝ) + (t : ℝ) / 8 < upward t A
        · exact Or.inl hlarge
        · right
          have hlarge' : upward t A ≤ (m : ℝ) + (t : ℝ) / 8 :=
            le_of_not_gt hlarge
          linarith
      _ ≤ μ.real {A | (m : ℝ) + (t : ℝ) / 8 < upward t A} +
          μ.real {A | (∑ i ∈ Finset.range t, downward i A) <
            -(m : ℝ) + (t : ℝ) / 8} :=
        MeasureTheory.measureReal_union_le _ _
      _ ≤ 2 * Real.exp (-((m : ℝ) + (t : ℝ)) / 512) +
          Real.exp (-(m : ℝ) / 32 - (t : ℝ) / 512) :=
        add_le_add hA hB
      _ ≤ 2 * Real.exp (-((m : ℝ) + (t : ℝ)) / 512) +
          Real.exp (-((m : ℝ) + (t : ℝ)) / 512) := by
        gcongr
        have hm0 : 0 ≤ (m : ℝ) := by positivity
        linarith
      _ = 3 * Real.exp (-((m : ℝ) + (t : ℝ)) / 512) := by ring
  have hsum : ∑ t ∈ Finset.range length,
      μ.real {A | (2 : ℝ) * (m : ℝ) <
        upward t A - ∑ i ∈ Finset.range t, downward i A} ≤
      ∑ t ∈ Finset.range length,
        3 * Real.exp (-((m : ℝ) + (t : ℝ)) / 512) :=
    Finset.sum_le_sum hsplit
  have hgeom := cool_finite_exponential_sum (1 / 512) (by norm_num) m length
  change μ.real {A | (∑ i ∈ Finset.range length, downward i A) ≤
      (4 : ℝ) * (m : ℝ)} +
      ∑ t ∈ Finset.range length,
        μ.real {A | (2 : ℝ) * (m : ℝ) <
          upward t A - ∑ i ∈ Finset.range t, downward i A} ≤ _
  calc
    μ.real {A | (∑ i ∈ Finset.range length, downward i A) ≤
        (4 : ℝ) * (m : ℝ)} +
        ∑ t ∈ Finset.range length,
          μ.real {A | (2 : ℝ) * (m : ℝ) <
            upward t A - ∑ i ∈ Finset.range t, downward i A} ≤
        Real.exp (-(m : ℝ) / 512) +
          ∑ t ∈ Finset.range length,
            3 * Real.exp (-((m : ℝ) + (t : ℝ)) / 512) :=
      add_le_add hlong hsum
    _ = Real.exp (-(m : ℝ) / 512) + 3 *
          ∑ t ∈ Finset.range length,
            Real.exp (-(1 / 512 : ℝ) * ((m : ℝ) + (t : ℝ))) := by
      rw [Finset.mul_sum]
      congr 3 with t
      congr 1
      ring_nf
    _ ≤ Real.exp (-(m : ℝ) / 512) + 3 *
          (Real.exp (-(1 / 512 : ℝ) * (m : ℝ)) *
            (1 - Real.exp (-(1 / 512 : ℝ)))⁻¹) := by
      gcongr
    _ = (1 + 3 * (1 - Real.exp (-(1 : ℝ) / 512))⁻¹) *
          Real.exp (-(1 / 512 : ℝ) * (m : ℝ)) := by
      congr 1 <;> ring_nf
    _ = (1 + 3 * (1 - q)⁻¹) *
          Real.exp (-(1 / 512 : ℝ) * (m : ℝ)) := by rfl

@[blueprint "lem:cool-constant-block-evolution"
  (statement := /-- There exist absolute constants $K_0\in\mathbb{N}$ and $C,c>0$ with the following property.  Let $[s,s+\ell)$ be a constant-temperature block at an integer temperature $b>0$, where $\ell\ge Km$ and $K\ge K_0$.  If the state at its beginning has norm at most $8bm$, then the probability that the state at its end has norm greater than $4bm$ is at most $C e^{-cm}$. -/)
  (proof := /-- Choose the absolute constants supplied by \,\cref{lem:cool-comparison-exponential-tail}, enlarging $C$ if necessary to cover the finitely many dimensions $m<4$ by the elementary bound $\mathbb{P}(E)\le1$.  Suppose henceforth that $m\ge4$.  By \,\cref{lem:cool-adaptive-drift-comparison}, the bad block event is bounded by the lower-tail probability for a sum of independent type-$B$ variables plus the sum, over all possible last-exit times, of the corresponding type-$A$/type-$B$ escape probabilities.  The hypothesis $\ell\ge Km$ and the choice $K\ge K_0$ imply $\ell\ge K_0m$.  Applying \,\cref{lem:cool-comparison-exponential-tail} to these comparison variables bounds the entire right-hand side by $Ce^{-cm}$, as required. -/)
  (title := /-- Evolution through one cooling block -/)
  (latexEnv := "lemma")]
lemma cool_constant_block_evolution :
    ∃ K₀ : ℕ, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (m n B K start length b : ℕ),
        K₀ ≤ K → 0 < b → K * m ≤ length →
        cool_constant_block n m B K start length b →
        (cool_gaussian_matrix_measure m n).real
          {A | ‖cool_state n m B K A start‖ ≤
              (8 : ℝ) * (b : ℝ) * (m : ℝ) ∧
            (4 : ℝ) * (b : ℝ) * (m : ℝ) <
              ‖cool_state n m B K A (start + length)‖} ≤
          C * Real.exp (-c * (m : ℝ)) := by
  classical
  obtain ⟨K₀, C₁, c₁, hC₁, hc₁, htail⟩ := cool_comparison_exponential_tail
  refine ⟨K₀, C₁ + Real.exp (3 * c₁), c₁, by positivity, hc₁, ?_⟩
  intro m n B K start length b hK hb hlen hblock
  letI : IsProbabilityMeasure (cool_gaussian_column_measure m) := by
    unfold cool_gaussian_column_measure
    infer_instance
  letI : IsProbabilityMeasure (cool_gaussian_matrix_measure m n) := by
    unfold cool_gaussian_matrix_measure
    infer_instance
  rcases Nat.lt_or_ge m 4 with hm | hm
  · have hmle : (m : ℝ) ≤ 3 := by
      have hm3 : m ≤ 3 := by omega
      exact_mod_cast hm3
    have hstep : Real.exp (-(3 * c₁)) ≤ Real.exp (-c₁ * (m : ℝ)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hid : Real.exp (3 * c₁) * Real.exp (-(3 * c₁)) = 1 := by
      rw [← Real.exp_add]
      simp
    refine le_trans measureReal_le_one ?_
    calc (1 : ℝ) = Real.exp (3 * c₁) * Real.exp (-(3 * c₁)) := hid.symm
      _ ≤ (C₁ + Real.exp (3 * c₁)) * Real.exp (-c₁ * (m : ℝ)) :=
        mul_le_mul (by linarith) hstep (Real.exp_pos _).le (by positivity)
  · obtain ⟨upward, downward, hindep, hup, hdown, hbound⟩ :=
      cool_adaptive_drift_comparison m n B K start length b hm hb hblock
    have hlen' : K₀ * m ≤ length := le_trans (Nat.mul_le_mul hK le_rfl) hlen
    have hfinal := htail m n length upward downward hm hlen' hindep hup hdown
    have hmono : C₁ * Real.exp (-c₁ * (m : ℝ)) ≤
        (C₁ + Real.exp (3 * c₁)) * Real.exp (-c₁ * (m : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos (3 * c₁)])
        (Real.exp_pos _).le
    exact le_trans (le_trans hbound hfinal) hmono

@[blueprint "lem:cool-terminal-state-tail"
  (statement := /-- There exist absolute constants $K_0\in\mathbb{N}$ and $C,c>0$ such that, whenever $B\ge 2$ is a power of two, $K\ge K_0$, and $n\ge 2Km\log_2 B$, the terminal COOL state obeys
  \[
    \mathbb{P}\bigl(\lVert y_n\rVert_2>4m\bigr)
      \le C(\log_2 B)e^{-cm}.
  \] -/)
  (proof := /-- Apply \,\cref{lem:cool-constant-block-evolution} first to the block of temperature $B$.  Except on an event of probability at most $Ce^{-cm}$, its terminal norm is at most $4Bm=8(B/2)m$.  Assuming this bound, apply the same lemma to the next block, of temperature $B/2$, and continue through the temperatures $B/4,\ldots,1$.  The last successful application gives $\lVert y_n\rVert_2\le 4m$.  Since $B\ge 2$ is a power of two, $\log_2 B\ge 1$, and hence the initial block together with the $\log_2 B$ subsequent cooling blocks contributes at most $2\log_2 B$ failure events.  The finite union bound, with the factor $2$ absorbed into $C$, yields the stated cumulative failure probability. -/)
  (title := /-- High-probability terminal state bound -/)
  (latexEnv := "lemma")]
lemma cool_terminal_state_tail :
    ∃ K₀ : ℕ, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (m n B K : ℕ),
        K₀ ≤ K → Nat.isPowerOfTwo B → 2 ≤ B →
        2 * K * m * Nat.log2 B ≤ n →
        (cool_gaussian_matrix_measure m n).real
          {A | (4 : ℝ) * (m : ℝ) < ‖cool_state n m B K A n‖} ≤
          C * (Nat.log2 B : ℝ) * Real.exp (-c * (m : ℝ)) := by
  classical
  obtain ⟨K₀, C₁, c₁, hC₁, hc₁, hblockev⟩ := cool_constant_block_evolution
  refine ⟨K₀, 2 * C₁, c₁, by positivity, hc₁, ?_⟩
  intro m n B K hK hBpow hB2 hsize
  letI : IsProbabilityMeasure (cool_gaussian_column_measure m) := by
    unfold cool_gaussian_column_measure
    infer_instance
  letI : IsProbabilityMeasure (cool_gaussian_matrix_measure m n) := by
    unfold cool_gaussian_matrix_measure
    infer_instance
  obtain ⟨ℓ, hBeq⟩ := hBpow
  have hlog : Nat.log2 B = ℓ := by
    rw [hBeq, Nat.log2_eq_log_two, Nat.log_pow Nat.one_lt_two]
  have hBpos : 0 < B := by omega
  have hlpos : 1 ≤ ℓ := by
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · rw [h, pow_zero] at hBeq
      omega
    · exact h
  obtain ⟨L, hLdef⟩ : ∃ L, cool_initial_block_length n m B K = L := ⟨_, rfl⟩
  have hLval : L = n - K * m * ℓ := by
    rw [← hLdef]
    unfold cool_initial_block_length
    rw [hlog]
  have hbig : K * m * ℓ + K * m * ℓ ≤ n := by
    have heq : K * m * ℓ + K * m * ℓ = 2 * K * m * Nat.log2 B := by
      rw [hlog]
      ring
    rw [heq]
    exact hsize
  have hKmlow : K * m ≤ K * m * ℓ := by
    calc K * m = K * m * 1 := by ring
      _ ≤ K * m * ℓ := Nat.mul_le_mul le_rfl hlpos
  have hLn : L + K * m * ℓ = n := by omega
  have hKmL : K * m ≤ L := by omega
  have key : ∀ i : ℕ, i ≤ ℓ →
      (cool_gaussian_matrix_measure m n).real
          {A | (4 : ℝ) * ((B / 2 ^ i : ℕ) : ℝ) * (m : ℝ) <
            ‖cool_state n m B K A (L + i * (K * m))‖} ≤
        ((i : ℝ) + 1) * (C₁ * Real.exp (-c₁ * (m : ℝ))) := by
    intro i
    induction i with
    | zero =>
        intro _
        have hblock0 : cool_constant_block n m B K 0 L B := by
          refine ⟨by omega, ?_⟩
          intro j hj1 hj2
          have hjL : j.1 < cool_initial_block_length n m B K := by
            rw [hLdef]
            omega
          unfold cool_temperature
          rw [if_pos hjL]
        have hmain := hblockev m n B K 0 L B hK hBpos hKmL hblock0
        have hzL : (0 : ℕ) + L = L := by omega
        rw [hzL] at hmain
        simp only [pow_zero, Nat.div_one, Nat.zero_mul, Nat.add_zero, Nat.cast_zero]
        refine le_trans (le_trans (MeasureTheory.measureReal_mono ?_ (by finiteness)) hmain) ?_
        · intro A hA
          simp only [Set.mem_setOf_eq] at hA ⊢
          refine ⟨?_, hA⟩
          have h0 : cool_state n m B K A 0 = 0 := by
            simp [cool_state]
          rw [h0, norm_zero]
          positivity
        · have hX : 0 ≤ C₁ * Real.exp (-c₁ * (m : ℝ)) := by positivity
          linarith
    | succ i ih =>
        intro hi
        have hile : i + 1 ≤ ℓ := hi
        have hi' : i ≤ ℓ := by omega
        have hpow : B / 2 ^ i = 2 * (B / 2 ^ (i + 1)) := by
          rw [hBeq, Nat.pow_div (by omega : i ≤ ℓ) (by norm_num : 0 < 2),
            Nat.pow_div (by omega : i + 1 ≤ ℓ) (by norm_num : 0 < 2)]
          have hsub : ℓ - i = (ℓ - (i + 1)) + 1 := by omega
          rw [hsub, pow_succ]
          ring
        have hb'pos : 0 < B / 2 ^ (i + 1) := by
          rw [hBeq, Nat.pow_div (by omega : i + 1 ≤ ℓ) (by norm_num : 0 < 2)]
          positivity
        have hstartend : L + i * (K * m) + K * m = L + (i + 1) * (K * m) := by ring
        have hblocki : cool_constant_block n m B K (L + i * (K * m)) (K * m)
            (B / 2 ^ (i + 1)) := by
          refine ⟨?_, ?_⟩
          · rw [hstartend]
            have h1 : (i + 1) * (K * m) ≤ ℓ * (K * m) := Nat.mul_le_mul hile le_rfl
            have h2 : ℓ * (K * m) = K * m * ℓ := by ring
            omega
          · intro j hj1 hj2
            have hKmpos : 0 < K * m := by
              by_contra hcon
              have hzero : K * m = 0 := by omega
              rw [hzero] at hj1 hj2
              simp only [Nat.mul_zero, Nat.add_zero] at hj1 hj2
              omega
            have hjL : ¬ (j.1 < cool_initial_block_length n m B K) := by
              rw [hLdef]
              omega
            have hdiv : (j.1 - cool_initial_block_length n m B K) / (K * m) = i := by
              rw [hLdef]
              refine Nat.div_eq_of_lt_le ?_ ?_
              · omega
              · have hsucc : (i + 1) * (K * m) = i * (K * m) + K * m := by ring
                rw [hsucc]
                omega
            unfold cool_temperature
            rw [if_neg hjL, hdiv, Nat.add_comm 1 i]
        have hmain := hblockev m n B K (L + i * (K * m)) (K * m)
          (B / 2 ^ (i + 1)) hK hb'pos le_rfl hblocki
        rw [hstartend] at hmain
        have hcast : ((B / 2 ^ i : ℕ) : ℝ) = 2 * ((B / 2 ^ (i + 1) : ℕ) : ℝ) := by
          rw [hpow]
          push_cast
          ring
        have hsub :
            {A : cool_matrix m n |
                (4 : ℝ) * ((B / 2 ^ (i + 1) : ℕ) : ℝ) * (m : ℝ) <
                  ‖cool_state n m B K A (L + (i + 1) * (K * m))‖} ⊆
              {A : cool_matrix m n |
                  (4 : ℝ) * ((B / 2 ^ i : ℕ) : ℝ) * (m : ℝ) <
                    ‖cool_state n m B K A (L + i * (K * m))‖} ∪
                {A : cool_matrix m n |
                  ‖cool_state n m B K A (L + i * (K * m))‖ ≤
                      (8 : ℝ) * ((B / 2 ^ (i + 1) : ℕ) : ℝ) * (m : ℝ) ∧
                    (4 : ℝ) * ((B / 2 ^ (i + 1) : ℕ) : ℝ) * (m : ℝ) <
                      ‖cool_state n m B K A (L + (i + 1) * (K * m))‖} := by
          intro A hA
          simp only [Set.mem_setOf_eq, Set.mem_union] at hA ⊢
          by_cases hcase : (4 : ℝ) * ((B / 2 ^ i : ℕ) : ℝ) * (m : ℝ) <
              ‖cool_state n m B K A (L + i * (K * m))‖
          · exact Or.inl hcase
          · refine Or.inr ⟨?_, hA⟩
            have hle := le_of_not_gt hcase
            rw [hcast] at hle
            linarith
        refine le_trans (MeasureTheory.measureReal_mono hsub (by finiteness)) ?_
        refine le_trans (MeasureTheory.measureReal_union_le _ _) ?_
        have hih := ih hi'
        have hcastsucc : (((i + 1 : ℕ) : ℝ) + 1) = ((i : ℝ) + 1) + 1 := by
          push_cast
          ring
        rw [hcastsucc]
        linarith
  have hfinal := key ℓ le_rfl
  have hb_last : B / 2 ^ ℓ = 1 := by
    rw [hBeq]
    exact Nat.div_self (by positivity)
  have hend : L + ℓ * (K * m) = n := by
    have h : ℓ * (K * m) = K * m * ℓ := by ring
    omega
  rw [hb_last, hend] at hfinal
  have hset : {A : cool_matrix m n |
        (4 : ℝ) * ((1 : ℕ) : ℝ) * (m : ℝ) < ‖cool_state n m B K A n‖} =
      {A : cool_matrix m n | (4 : ℝ) * (m : ℝ) < ‖cool_state n m B K A n‖} := by
    ext A
    simp
  rw [hset] at hfinal
  rw [hlog]
  have hX : 0 ≤ C₁ * Real.exp (-c₁ * (m : ℝ)) := by positivity
  have hlR : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hlpos
  have hprod : 0 ≤ ((ℓ : ℝ) - 1) * (C₁ * Real.exp (-c₁ * (m : ℝ))) :=
    mul_nonneg (by linarith) hX
  linarith

@[blueprint "lem:cool-terminal-state-eq-matrix-vector"
  (statement := /-- For all $n,m,B,K\in\mathbb{N}$ and every column family
  $A=(a_j)_{j\in\operatorname{Fin}(n)}$ with $a_j\in\mathbb{R}^m$, let
  $x=(x_j)_{j\in\operatorname{Fin}(n)}$ be the coordinate function output by
  COOL with parameters $B$ and $K$.  Then its terminal recursive state satisfies
  $y_n=Ax=\sum_{j\in\operatorname{Fin}(n)}x_ja_j$. -/)
  (proof := /-- For each $t\le n$, prove by induction on $t$ that every
  coordinate of $y_t$ equals the sum of the first $t$ columns, embedded from
  $\operatorname{Fin}(t)$ into $\operatorname{Fin}(n)$, weighted by the
  corresponding COOL outputs.  The assertion is zero at $t=0$ by
  \cref{def:cool-state}.  For the successor step, $t+1\le n$ implies $t<n$.
  Split the sum over $\operatorname{Fin}(t+1)$ into its first $t$ terms and its
  last term, and apply the induction hypothesis to the former.  The comparison
  in \cref{def:cool-state} is identical to that in \cref{def:cool-output}; in
  its first branch the state changes by $-b_ta_t$ and the output is $-b_t$,
  while in its second branch the state changes by $b_ta_t$ and the output is
  $b_t$.  By the coordinate realization in \cref{def:cool-column}, the last
  summand is therefore exactly the change in each state coordinate.  Taking
  $t=n$ makes the embedding the identity, and \cref{def:cool-matrix-vector}
  identifies the resulting coordinate sum with $Ax$. -/)
  (title := /-- Terminal state as a matrix--vector product -/)
  (latexEnv := "lemma")]
lemma cool_terminal_state_eq_matrix_vector (n m B K : ℕ) (A : cool_matrix m n) :
    cool_state n m B K A n =
      cool_matrix_vector A (cool_output n m B K A) := by
  classical
  have hstate : ∀ (t : ℕ) (ht : t ≤ n) (i : Fin m),
      (EuclideanSpace.equiv (Fin m) ℝ (cool_state n m B K A t)) i =
        ∑ j : Fin t,
          A (Fin.castLE ht j) i * cool_output n m B K A (Fin.castLE ht j) := by
    intro t
    induction t with
    | zero =>
        intro ht i
        simp [cool_state]
    | succ t ih =>
        intro ht i
        have htn : t < n := Nat.lt_of_succ_le ht
        rw [Fin.sum_univ_castSucc]
        have hcast (j : Fin t) :
            Fin.castLE ht j.castSucc = Fin.castLE (Nat.le_of_lt htn) j := rfl
        simp_rw [hcast]
        rw [← ih (Nat.le_of_lt htn) i]
        have hlast : Fin.castLE ht (Fin.last t) = (⟨t, htn⟩ : Fin n) := rfl
        simp_rw [hlast]
        simp only [cool_state, dif_pos htn, cool_output]
        split_ifs <;> simp [cool_column, mul_comm, sub_eq_add_neg]
  apply (EuclideanSpace.equiv (Fin m) ℝ).injective
  funext i
  simpa [cool_matrix_vector] using hstate n (Nat.le_refl n) i

@[blueprint "lem:cool-initial-output-coordinates"
  (statement := /-- For all $n,m,B,K\in\mathbb{N}$, every matrix $A\in\mathbb{R}^{m\times n}$, and every $j\in\operatorname{Fin}(n)$ satisfying $j<n-Km\log_2 B$, where the subtraction is in $\mathbb{N}$, the $j$th coordinate produced by COOL has absolute value $B$. -/)
  (proof := /-- Fix $n,m,B,K\in\mathbb{N}$, a matrix $A\in\mathbb{R}^{m\times n}$, and $j\in\operatorname{Fin}(n)$ with $j<n-Km\log_2 B$.  By \,\cref{def:cool-temperature}, the temperature at $j$ is $B$.  Expanding \,\cref{def:cool-output} and splitting according to its norm comparison, the output coordinate is respectively $-B$ or $B$.  Since the real cast of $B\in\mathbb{N}$ is nonnegative, both alternatives have absolute value $B$. -/)
  (title := /-- Magnitudes on the initial block -/)
  (latexEnv := "lemma")]
lemma cool_initial_output_coordinates (n m B K : ℕ) (A : cool_matrix m n)
    (j : Fin n) (hj : j.1 < cool_initial_block_length n m B K) :
    |cool_output n m B K A j| = (B : ℝ) := by
  simp [cool_output, cool_temperature, hj] <;> split <;> simp

@[blueprint "lem:cool-output-norm-lower-bound"
  (statement := /-- For all $n,m,B,K\in\mathbb{N}$ and every matrix
  $A\in\mathbb{R}^{m\times n}$, if $n\ge 2Km\log_2 B$, then the output $x$
  of COOL on $A$ satisfies
  \[
    \lVert x\rVert_2\ge B\sqrt{n/2}.
  \] -/)
  (proof := /-- Put $q=Km\log_2 B$ and let $S$ be the set of indices
  $j<n-q$.  The size hypothesis gives $q\le n$ and
  $n/2\le n-q$.  By \,\cref{def:cool-initial-block-length} and
  \,\cref{lem:cool-initial-output-coordinates}, every $j\in S$ satisfies
  $x_j^2=B^2$.  Thus
  \[
    \sum_{j\in S}x_j^2=(n-q)B^2\ge (n/2)B^2.
  \]
  Every omitted squared coordinate is nonnegative, so this partial sum is at
  most the sum over all coordinates.  By \,\cref{def:cool-output-vector} and
  the coordinate formula for the Euclidean norm, that full sum is
  $\lVert x\rVert_2^2$.  Both $B\sqrt{n/2}$ and $\lVert x\rVert_2$ are
  nonnegative; monotonicity of squaring on the nonnegative reals therefore
  gives the asserted inequality. -/)
  (title := /-- Lower bound for the output norm -/)
  (latexEnv := "lemma")]
lemma cool_output_norm_lower_bound (n m B K : ℕ) (A : cool_matrix m n)
    (hsize : 2 * K * m * Nat.log2 B ≤ n) :
    (B : ℝ) * Real.sqrt ((n : ℝ) / 2) ≤
      ‖cool_output_vector n m B K A‖ := by
  let q := K * m * Nat.log2 B
  let S : Finset (Fin n) := Finset.univ.filter fun j => j.1 < n - q
  have hsize' : 2 * q ≤ n := by
    simpa [q, mul_assoc] using hsize
  have hq : q ≤ n := by
    omega
  have hblock : (n : ℝ) / 2 ≤ ((n - q : ℕ) : ℝ) := by
    rw [Nat.cast_sub hq]
    have hsizeReal : ((2 * q : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hsize'
    norm_num at hsizeReal ⊢
    linarith
  have hcard : S.card = n - q := by
    simp [S, Fin.card_filter_val_lt, Nat.sub_le]
  have hcoord : ∀ j ∈ S,
      (cool_output n m B K A j) ^ 2 = (B : ℝ) ^ 2 := by
    intro j hj
    have habs := cool_initial_output_coordinates n m B K A j (by
      simpa [S, q, cool_initial_block_length] using (Finset.mem_filter.mp hj).2)
    nlinarith [sq_abs (cool_output n m B K A j)]
  have hsumS : ∑ j ∈ S, (cool_output n m B K A j) ^ 2 =
      (S.card : ℝ) * (B : ℝ) ^ 2 := by
    calc
      ∑ j ∈ S, (cool_output n m B K A j) ^ 2 =
          ∑ _j ∈ S, (B : ℝ) ^ 2 := Finset.sum_congr rfl hcoord
      _ = (S.card : ℝ) * (B : ℝ) ^ 2 := by simp
  have hsum_le : ∑ j ∈ S, (cool_output n m B K A j) ^ 2 ≤
      ∑ j : Fin n, (cool_output n m B K A j) ^ 2 := by
    exact Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
  have hsq : ((B : ℝ) * Real.sqrt ((n : ℝ) / 2)) ^ 2 ≤
      ‖cool_output_vector n m B K A‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change ((B : ℝ) * Real.sqrt ((n : ℝ) / 2)) ^ 2 ≤
      ∑ j : Fin n, (cool_output n m B K A j) ^ 2
    calc
      ((B : ℝ) * Real.sqrt ((n : ℝ) / 2)) ^ 2 =
          (B : ℝ) ^ 2 * ((n : ℝ) / 2) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      _ ≤ (B : ℝ) ^ 2 * ((n - q : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hblock (sq_nonneg _)
      _ = (S.card : ℝ) * (B : ℝ) ^ 2 := by rw [hcard]; ring
      _ = ∑ j ∈ S, (cool_output n m B K A j) ^ 2 := hsumS.symm
      _ ≤ ∑ j : Fin n, (cool_output n m B K A j) ^ 2 := hsum_le
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq

@[blueprint "lem:cool-contraction-from-terminal-bound"
  (statement := /-- For all $n,m,B,K\in\mathbb{N}$ and every matrix
  $A\in\mathbb{R}^{m\times n}$, suppose that $m<n$, that $B$ is a power of
  two, and that $n\ge 2Km\log_2 B$.  If the terminal COOL state has norm at
  most $4m$, then its output $x$ satisfies
  \[
    \frac{\lVert Ax\rVert_2}{\lVert x\rVert_2}
      \le 8\frac{m}{B\sqrt n}.
  \] -/)
  (proof := /-- By \,\cref{def:cool-contraction-ratio,lem:cool-terminal-state-eq-matrix-vector},
  the numerator is the norm of the terminal state and is at most $4m$.  By
  \,\cref{lem:cool-output-norm-lower-bound}, the denominator is at least
  $B\sqrt{n/2}$.  The hypotheses $m<n$ and that $B$ is a power of two imply
  $n>0$ and $B>0$.  Comparing squares of nonnegative quantities gives
  $\sqrt n/2\le\sqrt{n/2}$, so the denominator is at least
  $B\sqrt n/2>0$.  Division by this positive denominator therefore yields
  [
    \frac{\lVert Ax\rVert_2}{\lVert x\rVert_2}
      \le \frac{4m}{B\sqrt n/2}
      = 8\frac{m}{B\sqrt n}.
  ] -/)
  (title := /-- Deterministic contraction from the terminal estimate -/)
  (latexEnv := "lemma")]
lemma cool_contraction_from_terminal_bound (n m B K : ℕ) (A : cool_matrix m n)
    (hmn : m < n) (hB : Nat.isPowerOfTwo B)
    (hsize : 2 * K * m * Nat.log2 B ≤ n)
    (hstate : ‖cool_state n m B K A n‖ ≤ (4 : ℝ) * (m : ℝ)) :
    cool_contraction_ratio A (cool_output n m B K A) ≤
      (8 : ℝ) * (m : ℝ) / ((B : ℝ) * Real.sqrt (n : ℝ)) := by
  rw [cool_contraction_ratio, ← cool_terminal_state_eq_matrix_vector]
  have hBposNat : 0 < B := Nat.pos_of_isPowerOfTwo hB
  have hnposNat : 0 < n := lt_of_le_of_lt (Nat.zero_le m) hmn
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast hBposNat
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hnposNat
  have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hsqrt_half :
      Real.sqrt (n : ℝ) / 2 ≤ Real.sqrt ((n : ℝ) / 2) := by
    have hsqn := Real.sq_sqrt (le_of_lt hnpos)
    have hsqhalf := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)
    have hsqrtn_nonneg := Real.sqrt_nonneg (n : ℝ)
    have hsqrt_half_nonneg := Real.sqrt_nonneg ((n : ℝ) / 2)
    nlinarith
  have houtput :=
    cool_output_norm_lower_bound n m B K A hsize
  have hden :
      (B : ℝ) * Real.sqrt (n : ℝ) / 2 ≤
        ‖cool_output_vector n m B K A‖ := by
    calc
      (B : ℝ) * Real.sqrt (n : ℝ) / 2 =
          (B : ℝ) * (Real.sqrt (n : ℝ) / 2) := by ring
      _ ≤ (B : ℝ) * Real.sqrt ((n : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hsqrt_half (le_of_lt hBpos)
      _ ≤ ‖cool_output_vector n m B K A‖ := houtput
  have hdenpos : 0 < ‖cool_output_vector n m B K A‖ :=
    lt_of_lt_of_le (by positivity) hden
  apply (div_le_iff₀ hdenpos).2
  calc
    ‖cool_state n m B K A n‖ ≤ (4 : ℝ) * (m : ℝ) := hstate
    _ = ((8 : ℝ) * (m : ℝ) / ((B : ℝ) * Real.sqrt (n : ℝ))) *
          ((B : ℝ) * Real.sqrt (n : ℝ) / 2) := by
      field_simp
      ring
    _ ≤ ((8 : ℝ) * (m : ℝ) / ((B : ℝ) * Real.sqrt (n : ℝ))) *
          ‖cool_output_vector n m B K A‖ :=
      mul_le_mul_of_nonneg_left hden (by positivity)

@[blueprint "lem:cool-bad-event-subset-terminal-event"
  (statement := /-- For all $n,m,B,K\in\mathbb{N}$ such that $m<n$, $B$ is a
  power of two, and $2Km\log_2 B\le n$, let $x(A)$ and $y_n(A)$ denote,
  respectively, the output and terminal state of COOL on
  $A\in\mathbb{R}^{m\times n}$.  Then
  \[
    \left\{A:\frac{\lVert Ax(A)\rVert_2}{\lVert x(A)\rVert_2}
      >\frac{8m}{B\sqrt n}\right\}
    \subseteq
    \left\{A:4m<\lVert y_n(A)\rVert_2\right\}.
  \] -/)
  (proof := /-- Let $A$ lie outside the terminal-state event, so that $\lVert y_n\rVert_2\le4m$.  Then \,\cref{lem:cool-contraction-from-terminal-bound} gives a contraction ratio at most $8m/(B\sqrt n)$, and hence $A$ does not belong to the bad event.  Taking the contrapositive proves the inclusion. -/)
  (title := /-- Inclusion of the contraction failure event -/)
  (latexEnv := "lemma")]
lemma cool_bad_event_subset_terminal_event (n m B K : ℕ)
    (hmn : m < n) (hB : Nat.isPowerOfTwo B)
    (hsize : 2 * K * m * Nat.log2 B ≤ n) :
    cool_bad_event n m B K 8 ⊆
      {A | (4 : ℝ) * (m : ℝ) < ‖cool_state n m B K A n‖} := by
  intro A hbad
  by_contra hstate
  exact (not_lt_of_ge
    (cool_contraction_from_terminal_bound n m B K A hmn hB hsize
      (le_of_not_gt hstate))) hbad

@[blueprint "thm:cool-online-algorithm-guarantee"
  (statement := /-- There exist an absolute threshold $K_0\in\mathbb{N}$ and absolute constants $C_{\mathrm{ratio}},C_{\mathrm{fail}},c>0$ such that the following holds.  For all $m<n$, every power of two $B\ge 2$, every $K\ge K_0$, and every $n\ge 2Km\log_2 B$, if $A$ has independent standard Gaussian columns and $x$ is the output of COOL, then
  \[
    \mathbb{P}\!\left(
      \frac{\lVert Ax\rVert_2}{\lVert x\rVert_2}>
      C_{\mathrm{ratio}}\frac{m}{B\sqrt n}
    \right)
    \le C_{\mathrm{fail}}(\log_2 B)e^{-cm}.
  \]
  Equivalently, the contraction ratio is $O(m/(B\sqrt n))$ except with probability $O(\log B)\,2^{-\Omega(m)}$. -/)
  (proof := /-- Choose the constants supplied by \,\cref{lem:cool-terminal-state-tail} and take $C_{\mathrm{ratio}}=8$.  The hypotheses that $B$ is a power of two and that $B\ge 2$, together with the lower bounds on $K$ and $n$, permit application of that lemma.  By \,\cref{lem:cool-bad-event-subset-terminal-event}, the event on which the contraction ratio exceeds $8m/(B\sqrt n)$ is contained in the terminal-state failure event.  Monotonicity of the Gaussian matrix measure and the terminal tail estimate give the asserted probability bound.  Finally, replacing $e^{-cm}$ by $2^{-c'm}$, with $c'=c/\log 2>0$, is precisely the notation $2^{-\Omega(m)}$. -/)
  (title := /-- Adaptive robustness of hypergrid Johnson--Lindenstrauss -/)
  (latexEnv := "theorem")]
theorem cool_online_algorithm_guarantee :
    ∃ K₀ : ℕ, ∃ C_ratio C_fail c : ℝ,
      0 < C_ratio ∧ 0 < C_fail ∧ 0 < c ∧
      ∀ (m n B K : ℕ),
        m < n → Nat.isPowerOfTwo B → 2 ≤ B → K₀ ≤ K →
        2 * K * m * Nat.log2 B ≤ n →
        (cool_gaussian_matrix_measure m n).real
          (cool_bad_event n m B K C_ratio) ≤
          C_fail * (Nat.log2 B : ℝ) * Real.exp (-c * (m : ℝ)) := by
  classical
  obtain ⟨K₀, C, c, hC, hc, htail⟩ := cool_terminal_state_tail
  refine ⟨K₀, 8, C, c, by norm_num, hC, hc, ?_⟩
  intro m n B K hmn hB hB2 hK hsize
  letI : IsProbabilityMeasure (cool_gaussian_column_measure m) := by
    unfold cool_gaussian_column_measure
    infer_instance
  letI : IsProbabilityMeasure (cool_gaussian_matrix_measure m n) := by
    unfold cool_gaussian_matrix_measure
    infer_instance
  refine le_trans (MeasureTheory.measureReal_mono
    (cool_bad_event_subset_terminal_event n m B K hmn hB hsize) (by finiteness))
    (htail m n B K hK hB hB2 hsize)

import Architect
import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:finite-random-variable"
  (statement := /-- A finite nonnegative random variable consists of a finite outcome
  space \(\Omega\), a probability mass \(p_\omega\) on \(\Omega\), and a nonnegative
  value \(W(\omega)\) at every outcome. Thus \(p_\omega\geq 0\) for every
  \(\omega\in\Omega\) and \(\sum_{\omega\in\Omega}p_\omega=1\). -/)
  (title := /-- Finite Nonnegative Random Variables -/)
  (latexEnv := "definition")]
structure finite_random_variable where
  Outcome : Type
  outcome_finite : Fintype Outcome
  probability : Outcome → ℝ
  probability_nonnegative : ∀ ω, 0 ≤ probability ω
  probability_sum_one :
    letI := outcome_finite
    ∑ ω, probability ω = 1
  value : Outcome → ℝ
  value_nonnegative : ∀ ω, 0 ≤ value ω

@[blueprint "def:finite-random-variable-truncated-expectation"
  (statement := /-- For a finite nonnegative random variable \(W\) and an outside-option
  value \(y\in\mathbb R\), its truncated expectation is
  \[
    \mathbb E[\min\{y,W\}]
      =\sum_{\omega\in\Omega}p_\omega\min\{y,W(\omega)\}.
  \] -/)
  (title := /-- Truncated Expectations -/)
  (latexEnv := "definition")]
noncomputable def finite_random_variable_truncated_expectation
    (W : finite_random_variable) (y : ℝ) : ℝ :=
  letI := W.outcome_finite
  ∑ ω, W.probability ω * min y (W.value ω)

@[blueprint "def:costly-information-mdp"
  (statement := /-- A costly-information Markov decision process consists of a finite state
  space, a finite action space at each state, an initial state, a set of terminal states with
  accepted values, nonnegative action costs, and a transition probability mass function.
  A natural-valued horizon strictly decreases along every transition, thereby expressing
  acyclicity. The structure also carries the water-filling surrogate cost \(W^*_{\mathcal M}\)
  induced by this process and, for every randomized commitment \(\pi\), the surrogate cost
  \(W^*_{\mathcal M^\pi}\) of the resulting Markov chain. These finite random variables are
  the semantic representatives from which the corresponding optimality curves are derived. -/)
  (title := /-- Costly-Information Markov Decision Processes -/)
  (latexEnv := "definition")]
structure costly_information_mdp where
  State : Type
  state_finite : Fintype State
  Action : State → Type
  action_finite : ∀ s, Fintype (Action s)
  initial : State
  terminal : Set State
  terminalValue : State → ℝ
  actionCost : (s : State) → Action s → ℝ
  actionCost_nonnegative : ∀ s a, 0 ≤ actionCost s a
  transition : (s : State) → Action s → PMF State
  horizon : State → ℕ
  transition_descends :
    ∀ s a t, t ∈ (transition s a).support → horizon t < horizon s
  waterFillingSurrogate : finite_random_variable
  committedWaterFillingSurrogate :
    (∀ s : {s : State // s ∉ terminal}, PMF (Action s.1)) →
      finite_random_variable

@[blueprint "def:costly-information-commitment"
  (statement := /-- Let \(\mathcal M\) be a costly-information MDP. A commitment for
  \(\mathcal M\) assigns to every nonterminal state \(s\) a probability distribution on
  the actions available at \(s\). Fixing these distributions reduces the controlled process
  to a Markov chain. -/)
  (title := /-- Commitments for a Costly-Information MDP -/)
  (latexEnv := "definition")]
abbrev costly_information_commitment (M : costly_information_mdp) :=
  ∀ s : {s : M.State // s ∉ M.terminal}, PMF (M.Action s.1)

@[blueprint "def:costly-information-optimality-curve"
  (statement := /-- The optimality curve of a costly-information MDP \(\mathcal M\) is
  the truncated-expectation curve of its water-filling surrogate:
  \[
    f_{\mathcal M}(y)=\mathbb E[\min\{y,W^*_{\mathcal M}\}]
    \qquad (y\in\mathbb R).
  \] -/)
  (title := /-- Optimality Curves from Water-Filling Surrogates -/)
  (latexEnv := "definition")]
noncomputable def costly_information_optimality_curve
    (M : costly_information_mdp) (y : ℝ) : ℝ :=
  finite_random_variable_truncated_expectation M.waterFillingSurrogate y

@[blueprint "def:costly-information-committed-optimality-curve"
  (statement := /-- If \(\pi\) is a commitment for a costly-information MDP
  \(\mathcal M\), then the optimality curve of the induced Markov chain
  \(\mathcal M^\pi\) is
  \[
    f_{\mathcal M^\pi}(y)=\mathbb E[\min\{y,W^*_{\mathcal M^\pi}\}]
    \qquad (y\in\mathbb R).
  \] -/)
  (title := /-- Committed Optimality Curves from Water-Filling Surrogates -/)
  (latexEnv := "definition")]
noncomputable def costly_information_committed_optimality_curve
    (M : costly_information_mdp) (π : costly_information_commitment M)
    (y : ℝ) : ℝ :=
  finite_random_variable_truncated_expectation
    (M.committedWaterFillingSurrogate π) y

@[blueprint "def:local-approximation"
  (statement := /-- Let \(\mathcal M\) be a costly-information MDP, let
  \(\alpha\in\mathbb R\), and let \(\pi\) be a commitment for \(\mathcal M\).
  The commitment \(\pi\) is an \(\alpha\)-local approximation if, for every outside-option
  value \(y\in\mathbb R\), the optimality curves satisfy
  \[
    f_{\mathcal M^\pi}(\alpha y)\leq
    \alpha f_{\mathcal M}(y).
  \] -/)
  (title := /-- Local Approximation -/)
  (latexEnv := "definition")]
def local_approximation (M : costly_information_mdp) (α : ℝ)
    (π : costly_information_commitment M) : Prop :=
  ∀ y : ℝ, costly_information_committed_optimality_curve M π (α * y) ≤
    α * costly_information_optimality_curve M y

@[blueprint "def:matroid-water-filling-cost"
  (statement := /-- Let \(\mathcal N\) be a matroid on a finite set \(I\), and let
  \((W_i)_{i\in I}\) be independent finite nonnegative random variables. Their
  matroid water-filling cost is
  \[
    \mathbb E\!\left[\min_{B\text{ a base of }\mathcal N}
      \sum_{i\in B}W_i\right].
  \]
  The displayed finite sum uses the product probability mass on the joint outcome
  space, while the inner infimum is a minimum because the ground set is finite. -/)
  (title := /-- Matroid Water-Filling Cost -/)
  (latexEnv := "definition")]
noncomputable def matroid_water_filling_cost {ι : Type*} [Fintype ι]
    (M : Matroid ι) (W : ι → finite_random_variable) : ℝ :=
  letI : DecidableEq ι := Classical.decEq ι
  letI : ∀ i, Fintype (W i).Outcome := fun i => (W i).outcome_finite
  ∑ ω : ∀ i, (W i).Outcome,
    (∏ i, (W i).probability (ω i)) *
      sInf {c : ℝ | ∃ B : Finset ι,
        M.IsBase (B : Set ι) ∧ c = ∑ i ∈ B, (W i).value (ω i)}

@[blueprint "lem:local-curves-bound-matroid-water-filling-cost"
  (statement := /-- Let \(\mathcal N\) be a matroid on a finite set \(I\), let
  \((W_i)_{i\in I}\) and \((\widehat W_i)_{i\in I}\) be families of independent
  finite nonnegative random variables, and let \(\alpha\geq 1\). Suppose that
  \[
    \mathbb E[\min\{\alpha y,\widehat W_i\}]
      \leq \alpha\,\mathbb E[\min\{y,W_i\}]
  \]
  for every \(i\in I\) and every \(y\in\mathbb R\). Then
  \[
    \mathbb E\!\left[\min_{B\text{ a base of }\mathcal N}
      \sum_{i\in B}\widehat W_i\right]
      \leq
    \alpha\,\mathbb E\!\left[\min_{B\text{ a base of }\mathcal N}
      \sum_{i\in B}W_i\right].
  \] -/)
  (proof := /-- By \cref{def:finite-random-variable-truncated-expectation}, the local
  hypothesis, reparametrized by \(t=\alpha y\), says that the truncated expectation of
  \(\widehat W_i\) at every \(t\in\mathbb R\) is at most that of \(\alpha W_i\).
  Put the two outcome spaces at each coordinate on their product, with product
  probability, and use either the first value or the scaled second value. Fixing all
  outcomes except the \(i\)-th one, partition the finite nonempty family of bases
  according to whether they contain \(i\). The minimum in
  \cref{def:matroid-water-filling-cost} then has the form
  \(a+\min\{x,t\}\) on both finite supports: the bases containing \(i\) contribute
  affine functions with slope one, whereas those omitting \(i\) contribute constants;
  if either class is empty, use nonnegativity and a finite upper bound for the two
  supports. The local truncated-expectation inequality therefore compares the two
  conditional expectations. Multiplying by the nonnegative product probability of the
  remaining coordinates and summing shows that replacing \(\widehat W_i\) by
  \(\alpha W_i\) cannot decrease the expected minimum-base cost. Induction over the
  finite index set replaces all coordinates. The unused factors in the auxiliary
  product outcome space each have total mass one, so its two endpoints are respectively
  the laws of \((\widehat W_i)_i\) and \((\alpha W_i)_i\). Finally, since
  \(\alpha\geq 0\), every finite minimum base sum scales by \(\alpha\), giving the
  asserted inequality. -/)
  (title := /-- Local Curve Domination Composes through a Matroid -/)
  (latexEnv := "lemma")]
lemma local_curves_bound_matroid_water_filling_cost
    {ι : Type*} [Fintype ι] (M : Matroid ι)
    (W W_hat : ι → finite_random_variable) (α : ℝ)
    (hα : 1 ≤ α)
    (hlocal : ∀ i y,
      finite_random_variable_truncated_expectation (W_hat i) (α * y) ≤
        α * finite_random_variable_truncated_expectation (W i) y) :
    matroid_water_filling_cost M W_hat ≤
      α * matroid_water_filling_cost M W := by
  classical
  let baseCost (v : ι → ℝ) : ℝ :=
    sInf {c : ℝ | ∃ B : Finset ι,
      M.IsBase (B : Set ι) ∧ c = ∑ j ∈ B, v j}
  have hbase : ∃ B : Finset ι, M.IsBase (B : Set ι) := by
    obtain ⟨B, hB⟩ := M.exists_isBase
    refine ⟨Finset.univ.filter (fun i => i ∈ B), ?_⟩
    convert hB using 1 <;> ext x <;> simp
  have hfinite (v : ι → ℝ) :
      Set.Finite {c : ℝ | ∃ B : Finset ι,
        M.IsBase (B : Set ι) ∧ c = ∑ j ∈ B, v j} := by
    refine (Set.finite_range (fun B : Finset ι => ∑ j ∈ B, v j)).subset ?_
    rintro c ⟨B, hB, rfl⟩
    exact ⟨B, rfl⟩
  have hnonempty (v : ι → ℝ) :
      Set.Nonempty {c : ℝ | ∃ B : Finset ι,
        M.IsBase (B : Set ι) ∧ c = ∑ j ∈ B, v j} := by
    obtain ⟨B, hB⟩ := hbase
    exact ⟨∑ j ∈ B, v j, B, hB, rfl⟩
  have hsum_update (i : ι) (v : ι → ℝ) (x : ℝ) (B : Finset ι) (hi : i ∈ B) :
      (∑ j ∈ B, Function.update v i x j) = (∑ j ∈ B.erase i, v j) + x := by
    rw [← Finset.sum_erase_add B (Function.update v i x) hi]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      simp [Function.update, (Finset.mem_erase.mp hj).1]
    · simp [Function.update]
  have hsum_update_not (i : ι) (v : ι → ℝ) (x : ℝ)
      (B : Finset ι) (hi : i ∉ B) :
      (∑ j ∈ B, Function.update v i x j) = ∑ j ∈ B, v j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Function.update, ne_of_mem_of_not_mem hj hi]
  have hshape (i : ι) (v : ι → ℝ) (X Y : finite_random_variable) :
      ∃ a t : ℝ,
        (∀ x : X.Outcome,
          baseCost (Function.update v i (X.value x)) = a + min (X.value x) t) ∧
        (∀ y : Y.Outcome,
          baseCost (Function.update v i (Y.value y)) = a + min (Y.value y) t) := by
    letI : Fintype X.Outcome := X.outcome_finite
    letI : Fintype Y.Outcome := Y.outcome_finite
    let bases : Finset (Finset ι) :=
      Finset.univ.filter (fun B => M.IsBase (B : Set ι))
    have hbases : bases.Nonempty := by
      obtain ⟨B, hB⟩ := hbase
      exact ⟨B, by simp [bases, hB]⟩
    by_cases hin : (bases.filter (fun B => i ∈ B)).Nonempty
    · obtain ⟨Bi, hBi, hBi_min⟩ :=
        (bases.filter (fun B => i ∈ B)).exists_min_image
          (fun B => ∑ j ∈ B.erase i, v j) hin
      have hBi_bases : Bi ∈ bases := (Finset.mem_filter.mp hBi).1
      have hBi_base : M.IsBase (Bi : Set ι) := by
        simpa [bases] using hBi_bases
      have hBi_i : i ∈ Bi := (Finset.mem_filter.mp hBi).2
      by_cases hout : (bases.filter (fun B => i ∉ B)).Nonempty
      · obtain ⟨Bo, hBo, hBo_min⟩ :=
          (bases.filter (fun B => i ∉ B)).exists_min_image
            (fun B => ∑ j ∈ B, v j) hout
        have hBo_bases : Bo ∈ bases := (Finset.mem_filter.mp hBo).1
        have hBo_base : M.IsBase (Bo : Set ι) := by
          simpa [bases] using hBo_bases
        have hBo_i : i ∉ Bo := (Finset.mem_filter.mp hBo).2
        let a := ∑ j ∈ Bi.erase i, v j
        let b := ∑ j ∈ Bo, v j
        refine ⟨a, b - a, ?_, ?_⟩
        · intro x
          apply le_antisymm
          · have hi_le :
                baseCost (Function.update v i (X.value x)) ≤ a + X.value x := by
              apply csInf_le (hfinite _).bddBelow
              exact ⟨Bi, hBi_base,
                (hsum_update i v (X.value x) Bi hBi_i).symm⟩
            have ho_le :
                baseCost (Function.update v i (X.value x)) ≤ b := by
              apply csInf_le (hfinite _).bddBelow
              exact ⟨Bo, hBo_base,
                (hsum_update_not i v (X.value x) Bo hBo_i).symm⟩
            rw [add_min, show a + (b - a) = b by ring]
            simpa only [min_self] using min_le_min hi_le ho_le
          · apply le_csInf (hnonempty _)
            rintro c ⟨B, hB, rfl⟩
            by_cases hiB : i ∈ B
            · have hmin := hBi_min B
              have hmem : B ∈ bases.filter (fun B => i ∈ B) := by
                simp [bases, hB, hiB]
              specialize hmin hmem
              rw [hsum_update i v (X.value x) B hiB]
              dsimp [a, b]
              exact add_le_add hmin (min_le_left _ _)
            · have hmin := hBo_min B
              have hmem : B ∈ bases.filter (fun B => i ∉ B) := by
                simp [bases, hB, hiB]
              specialize hmin hmem
              rw [hsum_update_not i v (X.value x) B hiB]
              dsimp [a, b]
              have hm := min_le_right (X.value x)
                ((∑ j ∈ Bo, v j) - ∑ j ∈ Bi.erase i, v j)
              calc
                _ ≤ ∑ j ∈ Bo, v j := by linarith
                _ ≤ _ := hmin
        · intro y
          apply le_antisymm
          · have hi_le :
                baseCost (Function.update v i (Y.value y)) ≤ a + Y.value y := by
              apply csInf_le (hfinite _).bddBelow
              exact ⟨Bi, hBi_base,
                (hsum_update i v (Y.value y) Bi hBi_i).symm⟩
            have ho_le :
                baseCost (Function.update v i (Y.value y)) ≤ b := by
              apply csInf_le (hfinite _).bddBelow
              exact ⟨Bo, hBo_base,
                (hsum_update_not i v (Y.value y) Bo hBo_i).symm⟩
            rw [add_min, show a + (b - a) = b by ring]
            simpa only [min_self] using min_le_min hi_le ho_le
          · apply le_csInf (hnonempty _)
            rintro c ⟨B, hB, rfl⟩
            by_cases hiB : i ∈ B
            · have hmin := hBi_min B
              have hmem : B ∈ bases.filter (fun B => i ∈ B) := by
                simp [bases, hB, hiB]
              specialize hmin hmem
              rw [hsum_update i v (Y.value y) B hiB]
              dsimp [a, b]
              exact add_le_add hmin (min_le_left _ _)
            · have hmin := hBo_min B
              have hmem : B ∈ bases.filter (fun B => i ∉ B) := by
                simp [bases, hB, hiB]
              specialize hmin hmem
              rw [hsum_update_not i v (Y.value y) B hiB]
              dsimp [a, b]
              have hm := min_le_right (Y.value y)
                ((∑ j ∈ Bo, v j) - ∑ j ∈ Bi.erase i, v j)
              calc
                _ ≤ ∑ j ∈ Bo, v j := by linarith
                _ ≤ _ := hmin
      · let a := ∑ j ∈ Bi.erase i, v j
        let t := (∑ x, X.value x) + ∑ y, Y.value y
        have hall_in : ∀ B ∈ bases, i ∈ B := by
          intro B hB
          by_contra hiB
          exact hout ⟨B, by simpa [hiB] using hB⟩
        have hx_le : ∀ x, X.value x ≤ t := by
          intro x
          dsimp [t]
          have hx : X.value x ≤ ∑ z, X.value z := by
            apply Finset.single_le_sum (fun z _ => X.value_nonnegative z)
            simp
          have hy : 0 ≤ ∑ y, Y.value y :=
            Finset.sum_nonneg (fun y _ => Y.value_nonnegative y)
          linarith
        have hy_le : ∀ y, Y.value y ≤ t := by
          intro y
          dsimp [t]
          have hx : 0 ≤ ∑ x, X.value x :=
            Finset.sum_nonneg (fun x _ => X.value_nonnegative x)
          have hy : Y.value y ≤ ∑ z, Y.value z := by
            apply Finset.single_le_sum (fun z _ => Y.value_nonnegative z)
            simp
          linarith
        refine ⟨a, t, ?_, ?_⟩
        · intro x
          rw [min_eq_left (hx_le x)]
          apply le_antisymm
          · apply csInf_le (hfinite _).bddBelow
            exact ⟨Bi, hBi_base,
              (hsum_update i v (X.value x) Bi hBi_i).symm⟩
          · apply le_csInf (hnonempty _)
            rintro c ⟨B, hB, rfl⟩
            have hiB := hall_in B (by simp [bases, hB])
            rw [hsum_update i v (X.value x) B hiB]
            dsimp [a]
            exact add_le_add (hBi_min B (by simp [bases, hB, hiB])) le_rfl
        · intro y
          rw [min_eq_left (hy_le y)]
          apply le_antisymm
          · apply csInf_le (hfinite _).bddBelow
            exact ⟨Bi, hBi_base,
              (hsum_update i v (Y.value y) Bi hBi_i).symm⟩
          · apply le_csInf (hnonempty _)
            rintro c ⟨B, hB, rfl⟩
            have hiB := hall_in B (by simp [bases, hB])
            rw [hsum_update i v (Y.value y) B hiB]
            dsimp [a]
            exact add_le_add (hBi_min B (by simp [bases, hB, hiB])) le_rfl
    · have hall_out : ∀ B ∈ bases, i ∉ B := by
        intro B hB
        by_contra hiB
        exact hin ⟨B, by simpa [hiB] using hB⟩
      obtain ⟨Bo, hBo, hBo_min⟩ :=
        bases.exists_min_image (fun B => ∑ j ∈ B, v j) hbases
      have hBo_base : M.IsBase (Bo : Set ι) := by
        simpa [bases] using hBo
      let b := ∑ j ∈ Bo, v j
      refine ⟨b, 0, ?_, ?_⟩
      · intro x
        rw [min_eq_right (X.value_nonnegative x)]
        simp only [add_zero]
        apply le_antisymm
        · apply csInf_le (hfinite _).bddBelow
          exact ⟨Bo, hBo_base,
            (hsum_update_not i v (X.value x) Bo (hall_out Bo hBo)).symm⟩
        · apply le_csInf (hnonempty _)
          rintro c ⟨B, hB, rfl⟩
          rw [hsum_update_not i v (X.value x) B
            (hall_out B (by simp [bases, hB]))]
          exact hBo_min B (by simp [bases, hB])
      · intro y
        rw [min_eq_right (Y.value_nonnegative y)]
        simp only [add_zero]
        apply le_antisymm
        · apply csInf_le (hfinite _).bddBelow
          exact ⟨Bo, hBo_base,
            (hsum_update_not i v (Y.value y) Bo (hall_out Bo hBo)).symm⟩
        · apply le_csInf (hnonempty _)
          rintro c ⟨B, hB, rfl⟩
          rw [hsum_update_not i v (Y.value y) B
            (hall_out B (by simp [bases, hB]))]
          exact hBo_min B (by simp [bases, hB])
  have hα0 : 0 ≤ α := le_trans zero_le_one hα
  have hαpos : 0 < α := lt_of_lt_of_le zero_lt_one hα
  let scaled (X : finite_random_variable) : finite_random_variable :=
    { Outcome := X.Outcome
      outcome_finite := X.outcome_finite
      probability := X.probability
      probability_nonnegative := X.probability_nonnegative
      probability_sum_one := X.probability_sum_one
      value := fun x => α * X.value x
      value_nonnegative := fun x => mul_nonneg hα0 (X.value_nonnegative x) }
  have hscaled_curve (i : ι) (t : ℝ) :
      finite_random_variable_truncated_expectation (W_hat i) t ≤
        finite_random_variable_truncated_expectation (scaled (W i)) t := by
    letI : Fintype (W_hat i).Outcome := (W_hat i).outcome_finite
    letI : Fintype (W i).Outcome := (W i).outcome_finite
    have h := hlocal i (t / α)
    have hscale : α * (t / α) = t := by field_simp
    rw [hscale] at h
    calc
      _ ≤ α * finite_random_variable_truncated_expectation (W i) (t / α) := h
      _ = _ := by
        simp only [finite_random_variable_truncated_expectation]
        dsimp only [scaled]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        calc
          α * ((W i).probability x * min (t / α) ((W i).value x)) =
              (W i).probability x * (α * min (t / α) ((W i).value x)) := by ring
          _ = (W i).probability x *
              min (α * (t / α)) (α * (W i).value x) := by
                rw [mul_min_of_nonneg _ _ hα0]
          _ = _ := by rw [hscale]
  let mixed (S : Finset ι) (i : ι) : finite_random_variable :=
    letI : Fintype (W_hat i).Outcome := (W_hat i).outcome_finite
    letI : Fintype (W i).Outcome := (W i).outcome_finite
    { Outcome := (W_hat i).Outcome × (W i).Outcome
      outcome_finite := inferInstance
      probability := fun z => (W_hat i).probability z.1 * (W i).probability z.2
      probability_nonnegative := by
        intro z
        exact mul_nonneg ((W_hat i).probability_nonnegative z.1)
          ((W i).probability_nonnegative z.2)
      probability_sum_one := by
        rw [Fintype.sum_prod_type]
        calc
          (∑ x, ∑ y, (W_hat i).probability x * (W i).probability y) =
              (∑ x, (W_hat i).probability x) *
                ∑ y, (W i).probability y := by
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [Finset.mul_sum]
          _ = 1 := by
            rw [(W_hat i).probability_sum_one, (W i).probability_sum_one]
            norm_num
      value := fun z =>
        if i ∈ S then (W_hat i).value z.1 else α * (W i).value z.2
      value_nonnegative := by
        intro z
        split_ifs
        · exact (W_hat i).value_nonnegative z.1
        · exact mul_nonneg hα0 ((W i).value_nonnegative z.2) }
  have hstep (S : Finset ι) (i : ι) (hi : i ∉ S) :
      matroid_water_filling_cost M (mixed (insert i S)) ≤
        matroid_water_filling_cost M (mixed S) := by
    letI : ∀ j, Fintype (W_hat j).Outcome := fun j => (W_hat j).outcome_finite
    letI : ∀ j, Fintype (W j).Outcome := fun j => (W j).outcome_finite
    let Ω (j : ι) := (W_hat j).Outcome × (W j).Outcome
    letI : ∀ j, Fintype (Ω j) := fun j => by
      dsimp only [Ω]
      infer_instance
    let p (j : ι) : Ω j → ℝ := fun z =>
      (W_hat j).probability z.1 * (W j).probability z.2
    let val (T : Finset ι) (j : ι) : Ω j → ℝ := fun z =>
      if j ∈ T then (W_hat j).value z.1 else α * (W j).value z.2
    have hmixcurve (t : ℝ) :
        finite_random_variable_truncated_expectation (mixed (insert i S) i) t ≤
          finite_random_variable_truncated_expectation (mixed S i) t := by
      calc
        _ = finite_random_variable_truncated_expectation (W_hat i) t := by
          simp only [finite_random_variable_truncated_expectation]
          dsimp only [mixed]
          rw [Fintype.sum_prod_type]
          simp only [Finset.mem_insert, true_or, ↓reduceIte]
          calc
            (∑ x, ∑ y, (W_hat i).probability x * (W i).probability y *
                min t ((W_hat i).value x)) =
                ∑ x, ((W_hat i).probability x * min t ((W_hat i).value x)) *
                  ∑ y, (W i).probability y := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro y hy
                    ring
            _ = _ := by rw [(W i).probability_sum_one]; simp
        _ ≤ finite_random_variable_truncated_expectation (scaled (W i)) t :=
          hscaled_curve i t
        _ = _ := by
          simp only [finite_random_variable_truncated_expectation]
          dsimp only [mixed, scaled]
          rw [Fintype.sum_prod_type]
          simp only [hi, ↓reduceIte]
          calc
            (∑ y, (W i).probability y * min t (α * (W i).value y)) =
                (∑ x, (W_hat i).probability x) *
                  ∑ y, (W i).probability y * min t (α * (W i).value y) := by
                    rw [(W_hat i).probability_sum_one]
                    simp
            _ = ∑ x, ∑ y, (W_hat i).probability x * (W i).probability y *
                min t (α * (W i).value y) := by
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro x hx
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro y hy
                    ring
    change (∑ ω : ∀ j, Ω j,
        (∏ j, p j (ω j)) * baseCost (fun j => val (insert i S) j (ω j))) ≤
      ∑ ω : ∀ j, Ω j,
        (∏ j, p j (ω j)) * baseCost (fun j => val S j (ω j))
    have hsplit (T : Finset ι) :
        (∑ ω : ∀ j, Ω j,
          (∏ j, p j (ω j)) * baseCost (fun j => val T j (ω j))) =
        ∑ x : Ω i,
          ∑ r : ∀ j : {j // j ≠ i}, Ω j,
            (∏ j, p j (((Equiv.piSplitAt i Ω).symm (x, r)) j)) *
              baseCost
                (fun j => val T j (((Equiv.piSplitAt i Ω).symm (x, r)) j)) := by
      rw [← (Equiv.piSplitAt i Ω).symm.sum_comp]
      rw [Fintype.sum_prod_type]
    rw [hsplit (insert i S), hsplit S]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro r hr
    let v : ι → ℝ := fun j =>
      if hj : j = i then 0 else val S j (r ⟨j, hj⟩)
    have hvecS (x : Ω i) :
        (fun j => val S j (((Equiv.piSplitAt i Ω).symm (x, r)) j)) =
          Function.update v i (val S i x) := by
      funext j
      by_cases hj : j = i
      · subst j
        simp [v, Function.update]
      · simp [v, Function.update, hj]
    have hvec_insert (x : Ω i) :
        (fun j => val (insert i S) j (((Equiv.piSplitAt i Ω).symm (x, r)) j)) =
          Function.update v i (val (insert i S) i x) := by
      funext j
      by_cases hj : j = i
      · subst j
        simp [v, Function.update]
      · simp [v, val, Function.update, hj]
    have hprod (x : Ω i) :
        (∏ j, p j (((Equiv.piSplitAt i Ω).symm (x, r)) j)) =
          p i x * ∏ j : {j // j ≠ i}, p j (r j) := by
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
      congr 1
      · simp
      · apply Finset.prod_congr rfl
        intro j hj
        simp [j.property]
    let q : ℝ := ∏ j : {j // j ≠ i}, p j (r j)
    have hq : 0 ≤ q := by
      apply Finset.prod_nonneg
      intro j hj
      exact mul_nonneg ((W_hat j).probability_nonnegative (r j).1)
        ((W j).probability_nonnegative (r j).2)
    let X := mixed (insert i S) i
    let Y := mixed S i
    obtain ⟨a, t, hX, hY⟩ := hshape i v X Y
    have hX' (x : Ω i) :
        baseCost (Function.update v i (val (insert i S) i x)) =
          a + min (val (insert i S) i x) t := by
      simpa [X, mixed, val] using hX x
    have hY' (x : Ω i) :
        baseCost (Function.update v i (val S i x)) =
          a + min (val S i x) t := by
      simpa [Y, mixed, val] using hY x
    have hp : ∑ x : Ω i, p i x = 1 := by
      have h := X.probability_sum_one
      change (∑ x : Ω i, p i x) = 1 at h
      exact h
    have hcurve_raw :
        (∑ x : Ω i, p i x * min t (val (insert i S) i x)) ≤
          ∑ x : Ω i, p i x * min t (val S i x) := by
      have h := hmixcurve t
      change
        (∑ x : Ω i, p i x * min t (val (insert i S) i x)) ≤
          ∑ x : Ω i, p i x * min t (val S i x) at h
      exact h
    have hinner :
        (∑ x : Ω i,
          p i x * baseCost (Function.update v i (val (insert i S) i x))) ≤
        ∑ x : Ω i,
          p i x * baseCost (Function.update v i (val S i x)) := by
      calc
        _ = ∑ x : Ω i,
            (p i x * a + p i x * min t (val (insert i S) i x)) := by
                apply Finset.sum_congr rfl
                intro x hx
                rw [hX' x, min_comm]
                ring
        _ = a + ∑ x : Ω i, p i x * min t (val (insert i S) i x) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp]
          ring
        _ ≤ a + ∑ x : Ω i, p i x * min t (val S i x) := by
          simpa [add_comm] using add_le_add_left hcurve_raw a
        _ = ∑ x : Ω i,
            (p i x * a + p i x * min t (val S i x)) := by
              rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp]
              ring
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hY' x, min_comm]
          ring
    calc
      _ = q * (∑ x : Ω i,
          p i x * baseCost (Function.update v i (val (insert i S) i x))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            rw [hprod, hvec_insert]
            dsimp only [q]
            ring
      _ ≤ q * (∑ x : Ω i,
          p i x * baseCost (Function.update v i (val S i x))) :=
            mul_le_mul_of_nonneg_left hinner hq
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [hprod, hvecS]
        dsimp only [q]
        ring
  have hmixed :
      matroid_water_filling_cost M (mixed Finset.univ) ≤
        matroid_water_filling_cost M (mixed ∅) := by
    have hsubset (S : Finset ι) :
        matroid_water_filling_cost M (mixed S) ≤
          matroid_water_filling_cost M (mixed ∅) := by
      induction S using Finset.induction with
      | empty => exact le_rfl
      | @insert i S hi ih => exact (hstep S i hi).trans ih
    exact hsubset Finset.univ
  have hmixed_univ :
      matroid_water_filling_cost M (mixed Finset.univ) =
        matroid_water_filling_cost M W_hat := by
    letI : ∀ i, Fintype (W_hat i).Outcome := fun i => (W_hat i).outcome_finite
    letI : ∀ i, Fintype (W i).Outcome := fun i => (W i).outcome_finite
    let Ω (i : ι) := (W_hat i).Outcome × (W i).Outcome
    letI : ∀ i, Fintype (Ω i) := fun i => by
      dsimp only [Ω]
      infer_instance
    let e : (∀ i, Ω i) ≃
        (∀ i, (W_hat i).Outcome) × (∀ i, (W i).Outcome) :=
      { toFun := fun z => (fun i => (z i).1, fun i => (z i).2)
        invFun := fun z i => (z.1 i, z.2 i)
        left_inv := by intro z; rfl
        right_inv := by intro z; rcases z with ⟨x, y⟩; rfl }
    have hmassW :
        (∑ ω : ∀ i, (W i).Outcome, ∏ i, (W i).probability (ω i)) = 1 := by
      rw [← Fintype.prod_sum]
      apply Finset.prod_eq_one
      intro i hi
      exact (W i).probability_sum_one
    unfold matroid_water_filling_cost
    dsimp only [mixed]
    simp only [Finset.mem_univ, ↓reduceIte]
    change (∑ z : ∀ i, Ω i,
        (∏ i, (W_hat i).probability (z i).1 * (W i).probability (z i).2) *
          baseCost (fun i => (W_hat i).value (z i).1)) =
      ∑ x : ∀ i, (W_hat i).Outcome,
        (∏ i, (W_hat i).probability (x i)) *
          baseCost (fun i => (W_hat i).value (x i))
    calc
      _ = ∑ z : (∀ i, (W_hat i).Outcome) × (∀ i, (W i).Outcome),
          (∏ i, (W_hat i).probability (z.1 i) * (W i).probability (z.2 i)) *
            baseCost (fun i => (W_hat i).value (z.1 i)) := by
              rw [← e.symm.sum_comp]
              rfl
      _ = ∑ x : ∀ i, (W_hat i).Outcome,
          ∑ y : ∀ i, (W i).Outcome,
            (∏ i, (W_hat i).probability (x i) * (W i).probability (y i)) *
              baseCost (fun i => (W_hat i).value (x i)) := by
                rw [Fintype.sum_prod_type]
      _ = ∑ x : ∀ i, (W_hat i).Outcome,
          ((∏ i, (W_hat i).probability (x i)) *
            baseCost (fun i => (W_hat i).value (x i))) *
              ∑ y : ∀ i, (W i).Outcome, ∏ i, (W i).probability (y i) := by
                apply Finset.sum_congr rfl
                intro x hx
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y hy
                rw [Finset.prod_mul_distrib]
                ring
      _ = _ := by rw [hmassW]; simp
  have hmixed_empty :
      matroid_water_filling_cost M (mixed ∅) =
        matroid_water_filling_cost M (fun i => scaled (W i)) := by
    letI : ∀ i, Fintype (W_hat i).Outcome := fun i => (W_hat i).outcome_finite
    letI : ∀ i, Fintype (W i).Outcome := fun i => (W i).outcome_finite
    let Ω (i : ι) := (W_hat i).Outcome × (W i).Outcome
    letI : ∀ i, Fintype (Ω i) := fun i => by
      dsimp only [Ω]
      infer_instance
    let e : (∀ i, Ω i) ≃
        (∀ i, (W_hat i).Outcome) × (∀ i, (W i).Outcome) :=
      { toFun := fun z => (fun i => (z i).1, fun i => (z i).2)
        invFun := fun z i => (z.1 i, z.2 i)
        left_inv := by intro z; rfl
        right_inv := by intro z; rcases z with ⟨x, y⟩; rfl }
    have hmass_hat :
        (∑ ω : ∀ i, (W_hat i).Outcome,
          ∏ i, (W_hat i).probability (ω i)) = 1 := by
      rw [← Fintype.prod_sum]
      apply Finset.prod_eq_one
      intro i hi
      exact (W_hat i).probability_sum_one
    unfold matroid_water_filling_cost
    dsimp only [mixed, scaled]
    simp only [Finset.notMem_empty, ↓reduceIte]
    change (∑ z : ∀ i, Ω i,
        (∏ i, (W_hat i).probability (z i).1 * (W i).probability (z i).2) *
          baseCost (fun i => α * (W i).value (z i).2)) =
      ∑ y : ∀ i, (W i).Outcome,
        (∏ i, (W i).probability (y i)) *
          baseCost (fun i => α * (W i).value (y i))
    calc
      _ = ∑ z : (∀ i, (W_hat i).Outcome) × (∀ i, (W i).Outcome),
          (∏ i, (W_hat i).probability (z.1 i) * (W i).probability (z.2 i)) *
            baseCost (fun i => α * (W i).value (z.2 i)) := by
              rw [← e.symm.sum_comp]
              rfl
      _ = ∑ x : ∀ i, (W_hat i).Outcome,
          ∑ y : ∀ i, (W i).Outcome,
            (∏ i, (W_hat i).probability (x i) * (W i).probability (y i)) *
              baseCost (fun i => α * (W i).value (y i)) := by
                rw [Fintype.sum_prod_type]
      _ = (∑ x : ∀ i, (W_hat i).Outcome,
          ∏ i, (W_hat i).probability (x i)) *
            ∑ y : ∀ i, (W i).Outcome,
              (∏ i, (W i).probability (y i)) *
                baseCost (fun i => α * (W i).value (y i)) := by
                  symm
                  rw [Finset.mul_sum]
                  simp_rw [Finset.sum_mul]
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro x hx
                  apply Finset.sum_congr rfl
                  intro y hy
                  rw [Finset.prod_mul_distrib]
                  ring
      _ = _ := by rw [hmass_hat]; simp
  have hbaseCost_scale (v : ι → ℝ) :
      baseCost (fun i => α * v i) = α * baseCost v := by
    apply le_antisymm
    · have hc :
          baseCost v ∈ {c : ℝ | ∃ B : Finset ι,
            M.IsBase (B : Set ι) ∧ c = ∑ i ∈ B, v i} := by
        dsimp only [baseCost]
        exact (hnonempty v).csInf_mem (hfinite v)
      obtain ⟨B, hB, hB_eq⟩ := hc
      apply csInf_le (hfinite _).bddBelow
      refine ⟨B, hB, ?_⟩
      rw [← Finset.mul_sum, hB_eq]
    · apply le_csInf (hnonempty _)
      rintro c ⟨B, hB, rfl⟩
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (csInf_le (hfinite v).bddBelow ⟨B, hB, rfl⟩) hα0
  have hscaled_cost :
      matroid_water_filling_cost M (fun i => scaled (W i)) =
        α * matroid_water_filling_cost M W := by
    letI : ∀ i, Fintype (W i).Outcome := fun i => (W i).outcome_finite
    unfold matroid_water_filling_cost
    dsimp only [scaled]
    change (∑ ω : ∀ i, (W i).Outcome,
        (∏ i, (W i).probability (ω i)) *
          baseCost (fun i => α * (W i).value (ω i))) =
      α * ∑ ω : ∀ i, (W i).Outcome,
        (∏ i, (W i).probability (ω i)) *
          baseCost (fun i => (W i).value (ω i))
    calc
      _ = ∑ ω : ∀ i, (W i).Outcome,
          (∏ i, (W i).probability (ω i)) *
            (α * baseCost (fun i => (W i).value (ω i))) := by
              apply Finset.sum_congr rfl
              intro ω hω
              rw [hbaseCost_scale]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω hω
        ring
  calc
    matroid_water_filling_cost M W_hat =
        matroid_water_filling_cost M (mixed Finset.univ) := hmixed_univ.symm
    _ ≤ matroid_water_filling_cost M (mixed ∅) := hmixed
    _ = matroid_water_filling_cost M (fun i => scaled (W i)) := hmixed_empty
    _ = α * matroid_water_filling_cost M W := hscaled_cost

@[blueprint "def:matroid-min-cics"
  (statement := /-- Let \(I\) be a finite index type. A matroid-min-CICS instance consists
  of a matroid on all indices, a constituent costly-information MDP \(\mathcal M_i\) for
  every \(i\in I\), and the positive optimal expected cost of the adaptive instance.
  The MDP lower-bound invariant requires this adaptive optimum to dominate the matroid
  water-filling cost of the constituent surrogates. The instance also specifies a committing
  policy that attains the minimum committed water-filling cost and certifies its minimality
  among all committing policies. -/)
  (title := /-- Matroid-Constrained Minimization CICS Instances -/)
  (latexEnv := "definition")]
structure matroid_min_cics (ι : Type*) [Fintype ι] where
  groundMatroid : Matroid ι
  ground_eq_univ : groundMatroid.E = Set.univ
  constituent : ι → costly_information_mdp
  optimalCost : ℝ
  optimalCost_pos : 0 < optimalCost
  optimalCost_lower_bound :
    matroid_water_filling_cost groundMatroid
      (fun i => (constituent i).waterFillingSurrogate) ≤ optimalCost
  minimizingPolicy :
    ∀ i, costly_information_commitment (constituent i)
  minimizingPolicy_minimal :
    ∀ policy : ∀ i, costly_information_commitment (constituent i),
      matroid_water_filling_cost groundMatroid
        (fun i => (constituent i).committedWaterFillingSurrogate
          (minimizingPolicy i)) ≤
      matroid_water_filling_cost groundMatroid
        (fun i => (constituent i).committedWaterFillingSurrogate (policy i))

@[blueprint "def:matroid-min-cics-feasible"
  (statement := /-- A set \(S\subseteq I\) is feasible for a matroid-min-CICS instance if
  it contains a base of the instance's matroid. Thus the feasible family is the upward closure
  of the family of matroid bases. -/)
  (title := /-- Feasible Sets of a Matroid-Min-CICS Instance -/)
  (latexEnv := "definition")]
def matroid_min_cics_feasible {ι : Type*} [Fintype ι]
    (I : matroid_min_cics ι) (S : Set ι) : Prop :=
  ∃ B : Set ι, I.groundMatroid.IsBase B ∧ B ⊆ S

@[blueprint "def:committing-policy"
  (statement := /-- A committing policy for a matroid-min-CICS instance chooses one
  commitment \(\pi_i\) for each constituent MDP \(\mathcal M_i\). -/)
  (title := /-- Committing Policies -/)
  (latexEnv := "definition")]
abbrev committing_policy {ι : Type*} [Fintype ι] (I : matroid_min_cics ι) :=
  ∀ i, costly_information_commitment (I.constituent i)

@[blueprint "def:committed-optimal-cost"
  (statement := /-- For a matroid-min-CICS instance \(\mathcal I\) and a committing
  policy \(\boldsymbol\pi=(\pi_i)_{i\in I}\), the optimal expected cost of the committed
  instance is the matroid water-filling cost of the Markov-chain surrogates:
  \[
    \operatorname{OPT}(\mathcal I_{\mid\boldsymbol\pi})
      =\mathbb E\!\left[\min_{B\text{ a base}}
        \sum_{i\in B}W^*_{\mathcal M_i^{\pi_i}}\right].
  \]
  This is the semantic identification supplied by optimality of the water-filling index
  policy for matroid selection over Markov chains. -/)
  (title := /-- Optimal Cost after Commitment -/)
  (latexEnv := "definition")]
noncomputable def committed_optimal_cost {ι : Type*} [Fintype ι]
    (I : matroid_min_cics ι) (policy : committing_policy I) : ℝ :=
  matroid_water_filling_cost I.groundMatroid
    (fun i => (I.constituent i).committedWaterFillingSurrogate (policy i))

@[blueprint "def:commitment-gap"
  (statement := /-- Let \(\mathcal I\) be a matroid-min-CICS instance with positive adaptive
  optimum \(\operatorname{OPT}(\mathcal I)\). Its commitment gap is
  \[
    \operatorname{cg}(\mathcal I)
      = \min_{\boldsymbol\pi}
        \frac{\operatorname{OPT}(\mathcal I_{\mid\boldsymbol\pi})}
             {\operatorname{OPT}(\mathcal I)},
  \]
  where the minimum ranges over all committing policies
  \(\boldsymbol\pi=(\pi_i)_{i\in I}\). The minimum is evaluated at the attaining
  policy carried by the instance. -/)
  (title := /-- Commitment Gap -/)
  (latexEnv := "definition")]
noncomputable def commitment_gap {ι : Type*} [Fintype ι]
    (I : matroid_min_cics ι) : ℝ :=
  committed_optimal_cost I I.minimizingPolicy / I.optimalCost

@[blueprint "lem:commitment-gap-le-committed-ratio"
  (statement := /-- Let \(\mathcal I\) be a matroid-min-CICS instance and let
  \(\boldsymbol\pi\) be a committing policy. Then
  \[
    \operatorname{cg}(\mathcal I)\leq
    \frac{\operatorname{OPT}(\mathcal I_{\mid\boldsymbol\pi})}
         {\operatorname{OPT}(\mathcal I)}.
  \] -/)
  (proof := /-- By \cref{def:commitment-gap}, the commitment gap is the ratio attained
  by the instance's minimizing committing policy. The minimality and strict-positivity
  certificates in \cref{def:matroid-min-cics} show that its numerator is no larger than
  the numerator associated with \(\boldsymbol\pi\) and that the common denominator
  \(\operatorname{OPT}(\mathcal I)\) is positive. Division by this denominator preserves
  the numerator inequality and gives the asserted bound. -/)
  (title := /-- The Commitment Gap Is Bounded by Every Committed Ratio -/)
  (latexEnv := "lemma")]
lemma commitment_gap_le_committed_ratio {ι : Type*} [Fintype ι]
    (I : matroid_min_cics ι) (policy : committing_policy I) :
    commitment_gap I ≤ committed_optimal_cost I policy / I.optimalCost := by
  unfold commitment_gap
  exact (div_le_div_iff_of_pos_right I.optimalCost_pos).2
    (I.minimizingPolicy_minimal policy)

@[blueprint "lem:local-approximations-bound-committed-cost"
  (statement := /-- Let \(I\) be a finite index type, let \(\mathcal I\) be a
  matroid-min-CICS instance with constituents \((\mathcal M_i)_{i\in I}\), let
  \(\alpha\in\mathbb R\) satisfy \(\alpha\geq 1\), and let
  \(\boldsymbol\pi=(\pi_i)_{i\in I}\) be a committing policy. Suppose that, for
  every \(i\in I\), the commitment \(\pi_i\) is an \(\alpha\)-local approximation
  for \(\mathcal M_i\). Then
  \[
    \operatorname{OPT}(\mathcal I_{\mid\boldsymbol\pi})
      \leq \alpha\operatorname{OPT}(\mathcal I).
  \] -/)
  (proof := /-- By \cref{def:committed-optimal-cost}, the left-hand side is the
  matroid water-filling cost of the committed surrogates
  \(W^*_{\mathcal M_i^{\pi_i}}\). The definitions in
  \cref{def:local-approximation, def:costly-information-optimality-curve,
  def:costly-information-committed-optimality-curve} identify each local-approximation
  hypothesis with the corresponding truncated-expectation inequality. Applying
  \cref{lem:local-curves-bound-matroid-water-filling-cost} to these committed surrogates
  and the adaptive surrogates \(W^*_{\mathcal M_i}\) therefore gives
  \[
    \operatorname{OPT}(\mathcal I_{\mid\boldsymbol\pi})
      \leq \alpha\,
      \mathbb E\!\left[\min_{B\text{ a base}}
        \sum_{i\in B}W^*_{\mathcal M_i}\right].
  \]
  The lower-bound field of the matroid-min-CICS instance in
  \cref{def:matroid-min-cics} bounds the expectation on the right by
  \(\operatorname{OPT}(\mathcal I)\). Since \(\alpha\geq 1\), multiplication by
  \(\alpha\) preserves this inequality, which proves the claim. -/)
  (title := /-- Composition of Constituent Local Approximations -/)
  (latexEnv := "lemma")]
lemma local_approximations_bound_committed_cost {ι : Type*} [Fintype ι]
    (I : matroid_min_cics ι) (α : ℝ) (policy : committing_policy I)
    (hα : 1 ≤ α)
    (hlocal : ∀ i, local_approximation (I.constituent i) α (policy i)) :
    committed_optimal_cost I policy ≤ α * I.optimalCost := by
  unfold committed_optimal_cost
  refine le_trans
    (local_curves_bound_matroid_water_filling_cost I.groundMatroid
      (fun i => (I.constituent i).waterFillingSurrogate)
      (fun i => (I.constituent i).committedWaterFillingSurrogate (policy i)) α hα ?_) ?_
  · intro i y
    exact hlocal i y
  · exact mul_le_mul_of_nonneg_left I.optimalCost_lower_bound (by linarith)

@[blueprint "thm:la-comp"
  (statement := /-- Let \(I\) be a finite index set, let
  \(\mathcal I=(\vec{\mathcal M},\mathcal F)\) be a matroid-min-CICS instance indexed
  by \(I\), and let \(\alpha\in\mathbb R\) satisfy \(\alpha\geq 1\). Suppose that, for
  every \(i\in I\), there exists a commitment \(\pi_i\) for \(\mathcal M_i\) under which
  \(\mathcal M_i\) admits an \(\alpha\)-local approximation. Then
  \[
    \operatorname{cg}(\mathcal I)\leq\alpha.
  \] -/)
  (proof := /-- For every \(i\), choose a commitment \(\pi_i\) satisfying the assumed
  local approximation and write \(\boldsymbol\pi=(\pi_i)_{i\in I}\). By
  \cref{lem:local-approximations-bound-committed-cost},
  \(\operatorname{OPT}(\mathcal I_{\mid\boldsymbol\pi})
  \leq\alpha\operatorname{OPT}(\mathcal I)\). Since
  \(\operatorname{OPT}(\mathcal I)>0\), division gives
  \[
    \frac{\operatorname{OPT}(\mathcal I_{\mid\boldsymbol\pi})}
         {\operatorname{OPT}(\mathcal I)}\leq\alpha.
  \]
  Applying \cref{lem:commitment-gap-le-committed-ratio} to
  \(\boldsymbol\pi\) yields
  \(\operatorname{cg}(\mathcal I)\leq\alpha\), as required. -/)
  (title := /-- Composition Theorem for Local Approximations -/)
  (latexEnv := "theorem")]
theorem la_comp {ι : Type*} [Fintype ι]
    (I : matroid_min_cics ι) (α : ℝ)
    (hα : 1 ≤ α)
    (hlocal : ∀ i, ∃ π : costly_information_commitment (I.constituent i),
      local_approximation (I.constituent i) α π) :
    commitment_gap I ≤ α := by
  choose policy hpolicy using hlocal
  calc
    commitment_gap I ≤ committed_optimal_cost I policy / I.optimalCost :=
      commitment_gap_le_committed_ratio I policy
    _ ≤ α := (div_le_iff₀ I.optimalCost_pos).2
      (local_approximations_bound_committed_cost I α policy hα hpolicy)

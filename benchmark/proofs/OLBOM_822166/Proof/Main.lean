import Architect
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Martingale.Centering
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Lattice.Fold

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:hard-context"
  (statement := /-- For a grid parameter $m\in\mathbb{N}$ and a time index $t\in\mathbb{N}$, the hard
  context $x^t$ is obtained by cycling round-robin through precisely the grid points $z_j=j/m$ whose
  indices satisfy $\lceil m/4\rceil\le j\le\lfloor 3m/4\rfloor$. Writing
  $a_m=\lceil m/4\rceil=(m+3)/4$ and $n_m=\lfloor 3m/4\rfloor-a_m+1$, one has
  $\mathrm{hardContext}(m,t)=\bigl(a_m+(t\bmod n_m)\bigr)/m$. For $m\ge 2$, the index interval is
  nonempty and its corresponding grid points are exactly those lying in $[1/4,3/4]$. -/)
  (title := /-- Hard context sequence -/)
  (latexEnv := "definition")]
noncomputable def hard_context (m t : ℕ) : ℝ :=
  let first := (m + 3) / 4
  let count := (3 * m) / 4 - first + 1
  ((first + t % count : ℕ) : ℝ) / (m : ℝ)

@[blueprint "def:hard-construction-constant"
  (statement := /-- The hard construction uses the single fixed positive constant
  $\delta_{\ast}=1/100$. Thus every hard instance uses the threshold
  $\eta=\delta_{\ast}\sqrt{m/T}$, and no lower-bound constant is permitted to depend on an
  instance-specific choice of $\delta$. -/)
  (title := /-- Fixed hard-construction constant -/)
  (latexEnv := "definition")]
noncomputable def hard_construction_constant : ℝ := (1 : ℝ) / 100

@[blueprint "def:hard-threshold"
  (statement := /-- Given a constant $\delta>0$, a grid size $m\in\mathbb{N}$ and a horizon
  $T\in\mathbb{N}$, the calibration threshold is $\eta=\delta\sqrt{m/T}$. -/)
  (title := /-- Calibration threshold -/)
  (latexEnv := "definition")]
noncomputable def hard_threshold (δ : ℝ) (m T : ℕ) : ℝ :=
  δ * Real.sqrt ((m : ℝ) / (T : ℝ))

@[blueprint "def:hard-group-family"
  (statement := /-- For a threshold $\eta\in\mathbb{R}$, the hard group family $G=\{g_0,g_1,g_2\}$
  consists of the binary-valued, prediction-dependent group functions
  $g_0(x,v)=\mathbf{1}[v\ge x+\eta]$, $g_1(x,v)=\mathbf{1}[v\le x-\eta]$, and
  $g_2(x,v)=\mathbf{1}[\lvert v-x\rvert<\eta]$, indexed by $i\in\{0,1,2\}$. -/)
  (title := /-- Hard group family -/)
  (latexEnv := "definition")]
noncomputable def hard_group_family (η : ℝ) : Fin 3 → ℝ → ℝ → ℝ :=
  fun i x v =>
    if i = 0 then (if x + η ≤ v then 1 else 0)
    else if i = 1 then (if v ≤ x - η then 1 else 0)
    else (if |v - x| < η then 1 else 0)

@[blueprint "def:empirical-bias"
  (statement := /-- Fix a horizon $T\in\mathbb{N}$, deterministic contexts
  $x:\{0,\dots,T-1\}\to\mathbb{R}$, a realized prediction sequence $p$ and label sequence $y$, a
  group function $g:\mathbb{R}\times\mathbb{R}\to\mathbb{R}$, and a prediction value $v\in\mathbb{R}$.
  The empirical bias at $v$ for $g$ is
  $B_T(v,g)=\sum_{t=1}^{T}\mathbf{1}[p^t=v]\,g(x^t,p^t)\,(p^t-y^t)$. -/)
  (title := /-- Empirical bias -/)
  (latexEnv := "definition")]
noncomputable def empirical_bias (T : ℕ) (x p y : Fin T → ℝ) (g : ℝ → ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑ t : Fin T, (if p t = v then (1 : ℝ) else 0) * g (x t) (p t) * (p t - y t)

@[blueprint "def:prediction-values"
  (statement := /-- For a horizon $T\in\mathbb{N}$ and a realized prediction sequence
  $p:\{0,\dots,T-1\}\to\mathbb{R}$, the set of realized prediction values is
  $V_T=\{p^t : 1\le t\le T\}$. -/)
  (title := /-- Prediction value set -/)
  (latexEnv := "definition")]
noncomputable def prediction_values (T : ℕ) (p : Fin T → ℝ) : Finset ℝ :=
  Finset.image p Finset.univ

@[blueprint "def:group-error"
  (statement := /-- For a horizon $T\in\mathbb{N}$, contexts $x$, realized predictions $p$ and labels
  $y$, and a group function $g:\mathbb{R}\times\mathbb{R}\to\mathbb{R}$, the group calibration error
  is $\mathrm{Err}_T(g)=\sum_{v\in V_T}\lvert B_T(v,g)\rvert$, summing the absolute empirical bias
  \cref{def:empirical-bias} over the realized prediction values \cref{def:prediction-values}. -/)
  (title := /-- Group calibration error -/)
  (latexEnv := "definition")]
noncomputable def group_error (T : ℕ) (x p y : Fin T → ℝ) (g : ℝ → ℝ → ℝ) : ℝ :=
  ∑ v ∈ prediction_values T p, |empirical_bias T x p y g v|

@[blueprint "def:multicalibration-error"
  (statement := /-- For a horizon $T\in\mathbb{N}$, contexts $x$, realized predictions $p$ and labels
  $y$, and a group family $G=(g_i)_{i\in\{0,1,2\}}$, the multicalibration error is
  $\mathrm{MCerr}_T(G)=\max_{i\in\{0,1,2\}}\mathrm{Err}_T(g_i)$, the maximum group calibration error
  \cref{def:group-error} over the family. -/)
  (title := /-- Multicalibration error -/)
  (latexEnv := "definition")]
noncomputable def multicalibration_error (T : ℕ) (x p y : Fin T → ℝ)
    (G : Fin 3 → ℝ → ℝ → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => group_error T x p y (G i))

@[blueprint "def:online-mc-hard-instance"
  (statement := /-- An online multicalibration hard instance packages: a probability space
  $(\Omega,\mathcal{F},\mu)$; a horizon $T$ and grid size $m$ with $2\le m$ and
  $m^3\le T<(m+1)^3$ (so $m=\lfloor T^{1/3}\rfloor=\Theta(T^{1/3})$); the fixed construction constant
  $\delta_{\ast}$ from \cref{def:hard-construction-constant}; a family of measurable labels
  $y^t:\Omega\to\mathbb{R}$ that are $\{0,1\}$-valued, mutually independent, and satisfy
  $\mathbb{E}_\mu[y^t]=x^t$ with $x^t$ the hard context \cref{def:hard-context} (i.e.\
  $y^t\sim\mathrm{Bernoulli}(x^t)$, modeling the oblivious adversary); a sub-$\sigma$-algebra
  $\mathcal{A}\subseteq\mathcal{F}$ representing the algorithm's internal randomness and independent of
  the labels; and predictions $p^t:\Omega\to[0,1]$ that are online, i.e.\ measurable with respect to
  $\mathcal{A}\vee\sigma(y^1,\dots,y^{t-1})$. -/)
  (title := /-- Online multicalibration hard instance -/)
  (latexEnv := "definition")]
structure online_mc_hard_instance where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  μ : MeasureTheory.Measure Ω
  [isProb : MeasureTheory.IsProbabilityMeasure μ]
  T : ℕ
  m : ℕ
  hm_grid : 2 ≤ m
  hm_lower : m ^ 3 ≤ T
  hm_upper : T < (m + 1) ^ 3
  y : Fin T → Ω → ℝ
  y_meas : ∀ t, Measurable (y t)
  y_binary : ∀ t ω, y t ω = 0 ∨ y t ω = 1
  y_mean : ∀ t, ∫ ω, y t ω ∂μ = hard_context m t.val
  y_indep : ProbabilityTheory.iIndepFun y μ
  algRandomness : MeasurableSpace Ω
  alg_le : algRandomness ≤ mΩ
  alg_indep : ProbabilityTheory.Indep algRandomness
    (⨆ t : Fin T, MeasurableSpace.comap (y t) inferInstance) μ
  p : Fin T → Ω → ℝ
  p_range : ∀ t ω, p t ω ∈ Set.Icc (0 : ℝ) 1
  p_adapted : ∀ t : Fin T,
    @Measurable Ω ℝ (algRandomness ⊔
      (⨆ s : Fin T, ⨆ _ : s < t, MeasurableSpace.comap (y s) inferInstance))
      inferInstance (p t)

@[blueprint "def:expected-mc-error"
  (statement := /-- For an online multicalibration hard instance $I$ \cref{def:online-mc-hard-instance}
  with horizon $T$, grid size $m$ and fixed construction constant $\delta_{\ast}$
  \cref{def:hard-construction-constant}, the expected multicalibration error is
  $\mathbb{E}_{\mathcal{D}_{T,m}}[\mathrm{MCerr}_T(G)]=\int_\Omega \mathrm{MCerr}_T(G_\eta)\,d\mu$,
  where $G_\eta$ is the hard group family \cref{def:hard-group-family} at threshold $\eta$
  \cref{def:hard-threshold}, and $\mathrm{MCerr}_T$ \cref{def:multicalibration-error} is evaluated on
  the contexts \cref{def:hard-context}, the realized predictions $p^t(\omega)$ and labels
  $y^t(\omega)$. -/)
  (title := /-- Expected multicalibration error -/)
  (latexEnv := "definition")]
noncomputable def expected_mc_error (inst : online_mc_hard_instance) : ℝ :=
  letI := inst.mΩ
  ∫ ω, multicalibration_error inst.T
      (fun t => hard_context inst.m t.val)
      (fun t => inst.p t ω)
      (fun t => inst.y t ω)
      (hard_group_family (hard_threshold hard_construction_constant inst.m inst.T)) ∂inst.μ

@[blueprint "lem:hard-group-family-partition"
  (statement := /-- Let $\eta>0$ and let $x,v\in\mathbb{R}$. The three members of the hard group
  family \cref{def:hard-group-family} at threshold $\eta$ partition the real line at $v$ relative to
  $x$: exactly one of the events $v\ge x+\eta$, $v\le x-\eta$, $\lvert v-x\rvert<\eta$ holds, and
  consequently $g_0(x,v)+g_1(x,v)+g_2(x,v)=1$, where $g_i=\mathrm{hardGroupFamily}(\eta)(i)$. -/)
  (proof := /-- Write $d=v-x$. The three defining predicates of \cref{def:hard-group-family} are
  $d\ge\eta$, $d\le-\eta$, and $\lvert d\rvert<\eta$. Because $\eta>0$, applying the trichotomy of the
  order on $\mathbb{R}$ to $d$ against the thresholds $\eta$ and $-\eta$ shows that exactly one of these
  predicates holds: if $d\ge\eta$ then $\lvert d\rvert=d\ge\eta$ so the third predicate fails, and
  $d\ge\eta>-\eta$ so the second fails; the case $d\le-\eta$ is symmetric; and if $\lvert d\rvert<\eta$
  then $-\eta<d<\eta$, so the first two predicates fail. Each indicator $g_i(x,v)$ equals $1$ on its
  predicate and $0$ otherwise, so the sum of the three indicators counts the unique satisfied predicate
  and equals $1$. The hypothesis $\eta>0$ is necessary: at $\eta=0$ and $v=x$ both $g_0$ and $g_1$
  equal $1$ while $g_2=0$, so the sum is $2$. -/)
  (title := /-- Hard group family partitions the line -/)
  (latexEnv := "lemma")]
lemma hard_group_family_partition (η : ℝ) (hη : 0 < η) (x v : ℝ) :
    hard_group_family η 0 x v + hard_group_family η 1 x v + hard_group_family η 2 x v = 1 := by
  simp only [hard_group_family]
  split_ifs with h0 h1 h2 <;> simp_all <;>
    rcases abs_cases (v - x) with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> linarith

@[blueprint "lem:mc-error-ge-avg-groups"
  (statement := /-- Fix a horizon $T\in\mathbb{N}$, contexts $x$, realized predictions $p$ and labels
  $y$ (each a map $\{0,\dots,T-1\}\to\mathbb{R}$), and a group family $G=(g_i)_{i\in\{0,1,2\}}$. The
  multicalibration error \cref{def:multicalibration-error} dominates the average of the three group
  calibration errors \cref{def:group-error}:
  $\mathrm{MCerr}_T(G)\ge\tfrac13\bigl(\mathrm{Err}_T(g_0)+\mathrm{Err}_T(g_1)+\mathrm{Err}_T(g_2)\bigr)$. -/)
  (proof := /-- By \cref{def:multicalibration-error}, $\mathrm{MCerr}_T(G)=\max_{i\in\{0,1,2\}}
  \mathrm{Err}_T(g_i)$ is the supremum of the nonempty finite family $(\mathrm{Err}_T(g_i))_{i\in\{0,1,2\}}$,
  so $\mathrm{MCerr}_T(G)\ge\mathrm{Err}_T(g_i)$ for each $i\in\{0,1,2\}$ \cref{def:group-error}. Adding
  the three inequalities gives $3\,\mathrm{MCerr}_T(G)\ge\mathrm{Err}_T(g_0)+\mathrm{Err}_T(g_1)+
  \mathrm{Err}_T(g_2)$, and dividing by $3$ yields the stated bound. -/)
  (title := /-- Multicalibration error dominates the group-error average -/)
  (latexEnv := "lemma")]
lemma mc_error_ge_avg_groups (T : ℕ) (x p y : Fin T → ℝ) (G : Fin 3 → ℝ → ℝ → ℝ) :
    multicalibration_error T x p y G ≥
      (group_error T x p y (G 0) + group_error T x p y (G 1) + group_error T x p y (G 2)) / 3 := by
  have h0 : group_error T x p y (G 0) ≤ multicalibration_error T x p y G :=
    Finset.le_sup' (fun i => group_error T x p y (G i)) (Finset.mem_univ (0 : Fin 3))
  have h1 : group_error T x p y (G 1) ≤ multicalibration_error T x p y G :=
    Finset.le_sup' (fun i => group_error T x p y (G i)) (Finset.mem_univ (1 : Fin 3))
  have h2 : group_error T x p y (G 2) ≤ multicalibration_error T x p y G :=
    Finset.le_sup' (fun i => group_error T x p y (G i)) (Finset.mem_univ (2 : Fin 3))
  linarith

@[blueprint "def:expected-sum-group-error"
  (statement := /-- For an online multicalibration hard instance $I$ \cref{def:online-mc-hard-instance}
  with horizon $T$, grid size $m$ and fixed construction constant $\delta_{\ast}$
  \cref{def:hard-construction-constant}, the expected summed group error is
  $\mathbb{E}_{\mathcal{D}_{T,m}}\bigl[\sum_{i=0}^{2}\mathrm{Err}_T(g_i)\bigr]=\int_\Omega\bigl(
  \mathrm{Err}_T(g_0)+\mathrm{Err}_T(g_1)+\mathrm{Err}_T(g_2)\bigr)\,d\mu$, where each group
  calibration error $\mathrm{Err}_T(g_i)$ \cref{def:group-error} is evaluated on the contexts
  \cref{def:hard-context}, the realized predictions $p^t(\omega)$ and labels $y^t(\omega)$, and
  $g_i=\mathrm{hardGroupFamily}(\eta)(i)$ is the $i$-th member of the hard group family
  \cref{def:hard-group-family} at threshold $\eta$ \cref{def:hard-threshold}. -/)
  (title := /-- Expected summed group error -/)
  (latexEnv := "definition")]
noncomputable def expected_sum_group_error (inst : online_mc_hard_instance) : ℝ :=
  letI := inst.mΩ
  ∫ ω, (group_error inst.T (fun t => hard_context inst.m t.val)
          (fun t => inst.p t ω) (fun t => inst.y t ω)
          (hard_group_family (hard_threshold hard_construction_constant inst.m inst.T) 0)
        + group_error inst.T (fun t => hard_context inst.m t.val)
          (fun t => inst.p t ω) (fun t => inst.y t ω)
          (hard_group_family (hard_threshold hard_construction_constant inst.m inst.T) 1)
        + group_error inst.T (fun t => hard_context inst.m t.val)
          (fun t => inst.p t ω) (fun t => inst.y t ω)
          (hard_group_family (hard_threshold hard_construction_constant inst.m inst.T) 2)) ∂inst.μ

@[blueprint "def:spread-drift-score"
  (statement := /-- Let $I$ be an online multicalibration hard instance
  \cref{def:online-mc-hard-instance}, put
  $\eta=\delta_{\ast}\sqrt{m/T}$ \cref{def:hard-construction-constant, def:hard-threshold}, and fix
  an outcome $\omega$. Write
  $D(\omega)=\#\{t:\lvert p^t(\omega)-x^t\rvert\ge\eta\}$ for the number of far rounds and, for
  the complementary set of near rounds, write
  $N(\omega)=\#\{t:\lvert p^t(\omega)-x^t\rvert<\eta\}=T-D(\omega)$. The spread--drift score is
  \[
    \mathcal{Q}(I)=\mathbb{E}_{\mu}\!\left[
      \eta D+\sqrt{\frac mT}\,N\right].
  \]
  Its first summand measures predictable tail-group drift. Its second is the aggregate scale furnished
  by the middle-group terminal-vector estimate after the near rounds are partitioned by grid context;
  unlike a sum of square roots of adaptively stopped cell occupancies, this quantity is stable under
  predictable allocation. -/)
  (title := /-- Spread--drift score of a hard instance -/)
  (latexEnv := "definition")]
noncomputable def spread_drift_score (inst : online_mc_hard_instance) : ℝ :=
  letI := inst.mΩ
  let η := hard_threshold hard_construction_constant inst.m inst.T
  ∫ ω, (η * ∑ t : Fin inst.T,
      if η ≤ |inst.p t ω - hard_context inst.m t.val| then (1 : ℝ) else 0) +
    Real.sqrt ((inst.m : ℝ) / (inst.T : ℝ)) * ∑ t : Fin inst.T,
      if |inst.p t ω - hard_context inst.m t.val| < η then (1 : ℝ) else 0 ∂inst.μ

@[blueprint "lem:online-mc-hard-instance-augmented-independence"
  (statement := /-- Let $I$ be an online multicalibration hard instance
  \cref{def:online-mc-hard-instance}. Index the algorithmic randomization by the left summand of
  $\{\ast\}\sqcup\{0,\ldots,T-1\}$ and the label-generated $\sigma$-algebras by its right
  summand. This augmented family of $\sigma$-algebras is mutually independent under $\mu$. -/)
  (proof := /-- The label-generated $\sigma$-algebras are mutually independent by the hypothesis
  $I.\mathrm{y\_indep}$ in \cref{def:online-mc-hard-instance}. The hypothesis
  $I.\mathrm{alg\_indep}$ says that the algorithmic $\sigma$-algebra is independent of the join
  of the entire label family. Apply the finite-intersection characterization of mutual independence:
  if the algorithmic index is absent, use mutual independence of the labels; if it is present,
  intersect the remaining label events first and then use independence from their join. This proves
  mutual independence of the augmented family. -/)
  (title := /-- Joint independence of algorithmic randomness and labels -/)
  (latexEnv := "lemma")]
lemma online_mc_hard_instance_augmented_independence :
    ∀ inst : online_mc_hard_instance,
      ProbabilityTheory.iIndep
        (fun i : Unit ⊕ Fin inst.T =>
          match i with
          | Sum.inl _ => inst.algRandomness
          | Sum.inr t => MeasurableSpace.comap (inst.y t) inferInstance)
        inst.μ := by
  intro inst
  classical
  let labelSpace : Fin inst.T → MeasurableSpace inst.Ω :=
    fun t => MeasurableSpace.comap (inst.y t) inferInstance
  have hLabels : ProbabilityTheory.iIndep labelSpace inst.μ := inst.y_indep.iIndep
  rw [ProbabilityTheory.iIndep_iff]
  intro s f hf
  let algIndex : Unit ⊕ Fin inst.T := Sum.inl ()
  let labelEmbedding : Fin inst.T ↪ Unit ⊕ Fin inst.T :=
    ⟨Sum.inr, Sum.inr_injective⟩
  let labelIndices : Finset (Fin inst.T) :=
    s.preimage Sum.inr Sum.inr_injective.injOn
  have hMapped : labelIndices.map labelEmbedding = s.erase algIndex := by
    ext i
    rcases i with (_ | t)
    · simp [algIndex, labelIndices, labelEmbedding]
    · simp [algIndex, labelIndices, labelEmbedding]
  have hLabelMeas : ∀ t ∈ labelIndices,
      @MeasurableSet inst.Ω (labelSpace t) (f (Sum.inr t)) := by
    intro t ht
    exact hf (Sum.inr t) (by simpa [labelIndices] using ht)
  have hLabelMeasure :
      inst.μ (⋂ t ∈ labelIndices, f (Sum.inr t)) =
        ∏ t ∈ labelIndices, inst.μ (f (Sum.inr t)) :=
    hLabels.meas_biInter hLabelMeas
  have hLabelJoinMeas :
      @MeasurableSet inst.Ω (⨆ t, labelSpace t)
        (⋂ t ∈ labelIndices, f (Sum.inr t)) := by
    refine labelIndices.measurableSet_biInter fun t ht => ?_
    exact (le_iSup labelSpace t) (f (Sum.inr t)) (hLabelMeas t ht)
  have hEraseInter :
      (⋂ i ∈ s.erase algIndex, f i) =
        ⋂ t ∈ labelIndices, f (Sum.inr t) := by
    rw [← hMapped]
    simp [labelEmbedding]
  have hEraseProd :
      (∏ i ∈ s.erase algIndex, inst.μ (f i)) =
        ∏ t ∈ labelIndices, inst.μ (f (Sum.inr t)) := by
    rw [← hMapped]
    simp [labelEmbedding]
  by_cases hAlg : algIndex ∈ s
  · have hAlgMeas : @MeasurableSet inst.Ω inst.algRandomness (f algIndex) := by
      simpa [algIndex] using hf algIndex hAlg
    have hSplitInter :
        (⋂ i ∈ s, f i) = f algIndex ∩ ⋂ i ∈ s.erase algIndex, f i := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_inter_iff]
      constructor
      · intro h
        exact ⟨h algIndex hAlg, fun i hi => h i (Finset.mem_of_mem_erase hi)⟩
      · rintro ⟨hleft, hrest⟩ i hi
        by_cases hil : i = algIndex
        · simpa [hil] using hleft
        · exact hrest i (Finset.mem_erase.mpr ⟨hil, hi⟩)
    calc
      inst.μ (⋂ i ∈ s, f i) =
          inst.μ (f algIndex ∩ ⋂ t ∈ labelIndices, f (Sum.inr t)) := by
            rw [hSplitInter, hEraseInter]
      _ = inst.μ (f algIndex) *
          inst.μ (⋂ t ∈ labelIndices, f (Sum.inr t)) := by
            exact (ProbabilityTheory.Indep_iff _ _ _).1 inst.alg_indep
              (f algIndex) (⋂ t ∈ labelIndices, f (Sum.inr t))
              hAlgMeas hLabelJoinMeas
      _ = inst.μ (f algIndex) *
          (∏ t ∈ labelIndices, inst.μ (f (Sum.inr t))) := by rw [hLabelMeasure]
      _ = ∏ i ∈ s, inst.μ (f i) := by
            rw [← hEraseProd]
            exact Finset.mul_prod_erase s (fun i => inst.μ (f i)) hAlg
  · have hErase : s.erase algIndex = s := Finset.erase_eq_of_notMem hAlg
    calc
      inst.μ (⋂ i ∈ s, f i) =
          inst.μ (⋂ t ∈ labelIndices, f (Sum.inr t)) := by
            rw [← hErase, hEraseInter]
      _ = ∏ t ∈ labelIndices, inst.μ (f (Sum.inr t)) := hLabelMeasure
      _ = ∏ i ∈ s, inst.μ (f i) := by rw [← hEraseProd, hErase]

@[blueprint "lem:online-mc-hard-instance-past-independent-label"
  (statement := /-- For every online multicalibration hard instance $I$
  \cref{def:online-mc-hard-instance} and every round $t$, the $\sigma$-algebra generated jointly by
  the algorithmic randomness and the labels $y^s$ with $s<t$ is independent of the
  $\sigma$-algebra generated by the current label $y^t$. -/)
  (proof := /-- Apply the augmented mutual independence statement
  \cref{lem:online-mc-hard-instance-augmented-independence} to the disjoint index sets consisting,
  respectively, of the algorithmic index together with all label indices $s<t$, and of the singleton
  label index $t$. Independence is preserved when the first family is replaced by the join of its
  members, which is precisely the strict-past $\sigma$-algebra in the assertion. -/)
  (title := /-- Independence of the current label from strict-past information -/)
  (latexEnv := "lemma")]
lemma online_mc_hard_instance_past_independent_label :
    ∀ (inst : online_mc_hard_instance) (t : Fin inst.T),
      ProbabilityTheory.Indep
        (inst.algRandomness ⊔
          (⨆ s : Fin inst.T, ⨆ _ : s < t,
            MeasurableSpace.comap (inst.y s) inferInstance))
        (MeasurableSpace.comap (inst.y t) inferInstance) inst.μ := by
  intro inst t
  classical
  let m : Unit ⊕ Fin inst.T → MeasurableSpace inst.Ω := fun i =>
    match i with
    | Sum.inl _ => inst.algRandomness
    | Sum.inr s => MeasurableSpace.comap (inst.y s) inferInstance
  let S : Set (Unit ⊕ Fin inst.T) :=
    {i | match i with | Sum.inl _ => True | Sum.inr s => s < t}
  let U : Set (Unit ⊕ Fin inst.T) := {Sum.inr t}
  have hm : ∀ i, m i ≤ inst.mΩ := by
    intro i
    rcases i with (_ | s)
    · exact inst.alg_le
    · simpa only [m] using (inst.y_meas s).comap_le
  have hdis : Disjoint S U := by
    rw [Set.disjoint_left]
    intro i hiS hiU
    simp only [U, Set.mem_singleton_iff] at hiU
    subst i
    simpa [S] using hiS
  have h := ProbabilityTheory.indep_iSup_of_disjoint hm
    (online_mc_hard_instance_augmented_independence inst) hdis
  rw [iSup_sum] at h
  simpa [S, U, m] using h

@[blueprint "lem:online-mc-hard-instance-predictable-centering"
  (statement := /-- Let $I$ be an online multicalibration hard instance
  \cref{def:online-mc-hard-instance}, let $t$ be a round, and write
  \[
    \mathcal F_{t-}
      =\mathcal A\vee\sigma\bigl(y^s:s<t\bigr)
  \]
  for the $\sigma$-algebra generated by the algorithmic randomness and the strict-past labels.
  For every $\mathcal F_{t-}$-measurable function $g:\Omega\to\mathbb R$ that is integrable with
  respect to $\mu$,
  \[
    \int_\Omega g\bigl(y^t-x^t\bigr)\,d\mu=0,
    \qquad x^t=\mathrm{hardContext}(m,t).
  \]
  Thus every integrable weight determined by the algorithmic randomness and the information
  available strictly before round $t$ is orthogonal in expectation to the centered current
  label. -/)
  (proof := /-- Put $\mathcal F_{t-}=\mathcal A\vee\sigma(y^s:s<t)$. By
  \cref{lem:online-mc-hard-instance-past-independent-label}, $\mathcal F_{t-}$ is independent of
  the $\sigma$-algebra generated by $y^t$. Hence the assumed $\mathcal F_{t-}$-measurability of
  $g$ implies that $g$ and $y^t$ are independent. Since $g$ is integrable and $y^t$ is
  $\{0,1\}$-valued by \cref{def:online-mc-hard-instance}, both $g y^t$ and
  $g(y^t-x^t)$ are integrable, where $x^t=\mathrm{hardContext}(m,t)$. Independence therefore
  factors the product integral:
  \[
    \int_\Omega g y^t\,d\mu
      =\left(\int_\Omega g\,d\mu\right)
       \left(\int_\Omega y^t\,d\mu\right).
  \]
  The label-mean condition in \cref{def:online-mc-hard-instance} gives
  $\int_\Omega y^t\,d\mu=x^t$. Since $\mu$ is a probability measure, the integral of the
  constant $x^t$ is $x^t$. Linearity of the integral now yields
  \[
    \int_\Omega g(y^t-x^t)\,d\mu
      =\left(\int_\Omega g\,d\mu\right)x^t
       -x^t\left(\int_\Omega g\,d\mu\right)=0.
  \] -/)
  (title := /-- Predictable centering of each Bernoulli increment -/)
  (latexEnv := "lemma")]
lemma online_mc_hard_instance_predictable_centering :
    ∀ (inst : online_mc_hard_instance) (t : Fin inst.T) (g : inst.Ω → ℝ),
      @Measurable inst.Ω ℝ
        (inst.algRandomness ⊔
          (⨆ s : Fin inst.T, ⨆ _ : s < t,
            MeasurableSpace.comap (inst.y s) inferInstance))
        inferInstance g →
      MeasureTheory.Integrable g inst.μ →
      ∫ ω, g ω *
        (inst.y t ω - hard_context inst.m t.val) ∂inst.μ = 0 := by
  intro inst t g hg hgi
  letI := inst.mΩ
  letI := inst.isProb
  have hind : ProbabilityTheory.IndepFun g (inst.y t) inst.μ := by
    rw [ProbabilityTheory.IndepFun_iff_Indep]
    intro s u hs hu
    exact (online_mc_hard_instance_past_independent_label inst t) s u
      (hg.comap_le s hs) hu
  have hy_ae : MeasureTheory.AEStronglyMeasurable (inst.y t) inst.μ :=
    (inst.y_meas t).aestronglyMeasurable
  have hy_bound : ∀ᵐ ω ∂inst.μ, ‖inst.y t ω‖ ≤ 1 := by
    filter_upwards with ω
    rcases inst.y_binary t ω with h | h <;> simp [h]
  have hgy : MeasureTheory.Integrable (fun ω => g ω * inst.y t ω) inst.μ :=
    hgi.mul_bdd hy_ae hy_bound
  have hprod :=
    hind.integral_fun_mul_eq_mul_integral hgi.aestronglyMeasurable hy_ae
  simp_rw [mul_sub]
  rw [MeasureTheory.integral_sub hgy
    (hgi.mul_const (hard_context inst.m t.val))]
  rw [hprod, MeasureTheory.integral_mul_const, inst.y_mean]
  ring

@[blueprint "lem:predictable-bernoulli-mask-moment-lower-bound"
  (statement := /-- Let $I$ be an online multicalibration hard instance, let $S$ be a finite set of
  rounds, and let $w_t:\Omega\to\{0,1\}$ be measurable with respect to the information available
  strictly before round $t$. If every hard context $x^t$ with $t\in S$ lies in $[1/4,3/4]$, then
  \[
    \frac{37}{432}\,\mathbb E_\mu\sum_{t\in S}w_t
      \le 4\sqrt{|S|}\,\mathbb E_\mu\left|\sum_{t\in S}w_t(x^t-y^t)\right|.
  \]
  Thus a predictably selected sum of the centered Bernoulli increments has an $L^1$ lower bound
  proportional to its expected selected mass divided by $\sqrt{|S|}$. -/)
  (proof := /-- Order $S$ chronologically and expose its rounds one at a time. Predictable
  centering \cref{lem:online-mc-hard-instance-predictable-centering} cancels the mixed term in the
  second moment and the term that is linear in the newest increment in the fourth moment. Since
  $y^t\in\{0,1\}$ and $x^t\in[1/4,3/4]$, the conditional second moment lies between
  $3w_t/16$ and $w_t$. Expanding the fourth power and using $|x^t-y^t|\le1$ gives inductively
  \[
    \mathbb E M_S^4\le 11|S|\,\mathbb E\sum_{t\in S}w_t,
    \qquad
    \mathbb E M_S^2\ge\frac3{16}\,\mathbb E\sum_{t\in S}w_t.
  \]
  Finally, the pointwise polynomial inequality
  $z^2\le4\sqrt{|S|}|z|+z^4/(108|S|)$, whose remainder factors as a nonnegative square, combines
  these two estimates and yields the displayed constant $3/16-11/108=37/432$. -/)
  (title := /-- Moment lower bound for a predictably masked Bernoulli sum -/)
  (latexEnv := "lemma")]
lemma predictable_bernoulli_mask_moment_lower_bound
    (inst : online_mc_hard_instance) (S : Finset (Fin inst.T))
    (w : Fin inst.T → inst.Ω → ℝ)
    (hw_meas : ∀ t, @Measurable inst.Ω ℝ
      (inst.algRandomness ⊔
        (⨆ s : Fin inst.T, ⨆ _ : s < t,
          MeasurableSpace.comap (inst.y s) inferInstance))
      inferInstance (w t))
    (hw_binary : ∀ t ω, w t ω = 0 ∨ w t ω = 1)
    (hx : ∀ t ∈ S,
      (1 : ℝ) / 4 ≤ hard_context inst.m t.val ∧
        hard_context inst.m t.val ≤ (3 : ℝ) / 4) :
    (37 : ℝ) / 432 * ∫ ω, ∑ t ∈ S, w t ω ∂inst.μ ≤
      4 * Real.sqrt (S.card : ℝ) *
        ∫ ω, |∑ t ∈ S,
          w t ω * (hard_context inst.m t.val - inst.y t ω)| ∂inst.μ := by
  classical
  letI := inst.mΩ
  letI := inst.isProb
  let X (A : Finset (Fin inst.T)) (ω : inst.Ω) :=
    ∑ t ∈ A, w t ω * (hard_context inst.m t.val - inst.y t ω)
  let W (A : Finset (Fin inst.T)) (ω : inst.Ω) := ∑ t ∈ A, w t ω
  have hw_ambient (t : Fin inst.T) : Measurable (w t) := by
    exact (hw_meas t).mono
      (sup_le inst.alg_le
        (iSup_le fun s => iSup_le fun _ => (inst.y_meas s).comap_le)) le_rfl
  have hw_norm (t : Fin inst.T) (ω : inst.Ω) : ‖w t ω‖ ≤ 1 := by
    rcases hw_binary t ω with h | h <;> simp [h]
  have hw_nonneg (t : Fin inst.T) (ω : inst.Ω) : 0 ≤ w t ω := by
    rcases hw_binary t ω with h | h <;> simp [h]
  have hw_integrable (t : Fin inst.T) :
      MeasureTheory.Integrable (w t) inst.μ := by
    apply MeasureTheory.Integrable.of_bound (hw_ambient t).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (hw_norm t)
  have hW_meas (A : Finset (Fin inst.T)) : Measurable (W A) := by
    dsimp [W]
    exact Finset.measurable_sum _ fun t _ => hw_ambient t
  have hW_nonneg (A : Finset (Fin inst.T)) (ω : inst.Ω) : 0 ≤ W A ω := by
    dsimp [W]
    exact Finset.sum_nonneg fun t _ => hw_nonneg t ω
  have hW_bound (A : Finset (Fin inst.T)) (ω : inst.Ω) :
      ‖W A ω‖ ≤ (A.card : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hW_nonneg A ω)]
    dsimp [W]
    calc
      ∑ t ∈ A, w t ω ≤ ∑ _t ∈ A, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro t _
        rcases hw_binary t ω with h | h <;> simp [h]
      _ = (A.card : ℝ) := by simp
  have hW_integrable (A : Finset (Fin inst.T)) :
      MeasureTheory.Integrable (W A) inst.μ := by
    apply MeasureTheory.Integrable.of_bound
      (hW_meas A).aestronglyMeasurable (A.card : ℝ)
    exact Filter.Eventually.of_forall (hW_bound A)
  have hX_meas (A : Finset (Fin inst.T)) : Measurable (X A) := by
    dsimp [X]
    exact Finset.measurable_sum _ fun t _ =>
      (hw_ambient t).mul (measurable_const.sub (inst.y_meas t))
  have hX_past (A : Finset (Fin inst.T)) (a : Fin inst.T)
      (hlt : ∀ t ∈ A, t < a) :
      @Measurable inst.Ω ℝ
        (inst.algRandomness ⊔
          (⨆ s : Fin inst.T, ⨆ _ : s < a,
            MeasurableSpace.comap (inst.y s) inferInstance))
        inferInstance (X A) := by
    dsimp [X]
    apply Finset.measurable_sum
    intro t ht
    have hfiltration :
        inst.algRandomness ⊔
            (⨆ s : Fin inst.T, ⨆ _ : s < t,
              MeasurableSpace.comap (inst.y s) inferInstance) ≤
          inst.algRandomness ⊔
            (⨆ s : Fin inst.T, ⨆ _ : s < a,
              MeasurableSpace.comap (inst.y s) inferInstance) := by
      apply sup_le_sup_left
      exact iSup_le fun s => iSup_le fun hs =>
        le_iSup_of_le s (le_iSup_of_le (lt_trans hs (hlt t ht)) le_rfl)
    have hwt := (hw_meas t).mono hfiltration le_rfl
    have hyt : @Measurable inst.Ω ℝ
        (inst.algRandomness ⊔
          (⨆ s : Fin inst.T, ⨆ _ : s < a,
            MeasurableSpace.comap (inst.y s) inferInstance))
        inferInstance (inst.y t) := by
      rw [measurable_iff_comap_le]
      exact le_sup_of_le_right
        (le_iSup_of_le t (le_iSup_of_le (hlt t ht) le_rfl))
    exact hwt.mul (measurable_const.sub hyt)
  have hX_bound (A : Finset (Fin inst.T))
      (hxA : ∀ t ∈ A, (1 : ℝ) / 4 ≤ hard_context inst.m t.val ∧
        hard_context inst.m t.val ≤ (3 : ℝ) / 4) (ω : inst.Ω) :
      ‖X A ω‖ ≤ (A.card : ℝ) := by
    dsimp [X]
    calc
      ‖∑ t ∈ A, w t ω * (hard_context inst.m t.val - inst.y t ω)‖ ≤
          ∑ t ∈ A, ‖w t ω *
            (hard_context inst.m t.val - inst.y t ω)‖ := norm_sum_le _ _
      _ ≤ ∑ _t ∈ A, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        rcases hxA t ht with ⟨hxl, hxu⟩
        rcases hw_binary t ω with hw | hw
        · simp [hw]
        · rcases inst.y_binary t ω with hy | hy
          · rw [hw, hy]
            simp only [abs_one, one_mul, sub_zero]
            rw [abs_of_nonneg] <;> linarith
          · rw [hw, hy]
            simp only [abs_one, one_mul]
            rw [abs_of_nonpos] <;> linarith
      _ = (A.card : ℝ) := by simp
  have hX_pow_integrable (A : Finset (Fin inst.T))
      (hxA : ∀ t ∈ A, (1 : ℝ) / 4 ≤ hard_context inst.m t.val ∧
        hard_context inst.m t.val ≤ (3 : ℝ) / 4) (n : ℕ) :
      MeasureTheory.Integrable (fun ω => (X A ω) ^ n) inst.μ := by
    apply MeasureTheory.Integrable.of_bound
      ((hX_meas A).pow_const n).aestronglyMeasurable ((A.card : ℝ) ^ n)
    filter_upwards with ω
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hX_bound A hxA ω) n
  have hcross (A : Finset (Fin inst.T)) (a : Fin inst.T)
      (hlt : ∀ t ∈ A, t < a)
      (hxA : ∀ t ∈ A, (1 : ℝ) / 4 ≤ hard_context inst.m t.val ∧
        hard_context inst.m t.val ≤ (3 : ℝ) / 4) (q : ℕ) :
      ∫ ω, (X A ω) ^ q * w a ω *
        (hard_context inst.m a.val - inst.y a ω) ∂inst.μ = 0 := by
    have hg_past :
        @Measurable inst.Ω ℝ
          (inst.algRandomness ⊔
            (⨆ s : Fin inst.T, ⨆ _ : s < a,
              MeasurableSpace.comap (inst.y s) inferInstance))
          inferInstance (fun ω => (X A ω) ^ q * w a ω) :=
      ((hX_past A a hlt).pow_const q).mul (hw_meas a)
    have hg_integrable : MeasureTheory.Integrable
        (fun ω => (X A ω) ^ q * w a ω) inst.μ := by
      apply MeasureTheory.Integrable.of_bound
        (((hX_meas A).pow_const q).mul (hw_ambient a)).aestronglyMeasurable
        ((A.card : ℝ) ^ q)
      filter_upwards with ω
      change ‖X A ω ^ q * w a ω‖ ≤ (A.card : ℝ) ^ q
      rw [norm_mul, norm_pow]
      calc
        ‖X A ω‖ ^ q * ‖w a ω‖ ≤ (A.card : ℝ) ^ q * 1 := by
          gcongr
          · exact hX_bound A hxA ω
          · exact hw_norm a ω
        _ = (A.card : ℝ) ^ q := by ring
    have hc := online_mc_hard_instance_predictable_centering inst a
      (fun ω => -((X A ω) ^ q * w a ω)) hg_past.neg hg_integrable.neg
    calc
      ∫ ω, (X A ω) ^ q * w a ω *
          (hard_context inst.m a.val - inst.y a ω) ∂inst.μ =
          ∫ ω, -((X A ω) ^ q * w a ω) *
            (inst.y a ω - hard_context inst.m a.val) ∂inst.μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with ω
        ring
      _ = 0 := hc
  have hself (a : Fin inst.T)
      (hxa : (1 : ℝ) / 4 ≤ hard_context inst.m a.val ∧
        hard_context inst.m a.val ≤ (3 : ℝ) / 4) :
      ∫ ω, w a ω * (hard_context inst.m a.val - inst.y a ω) ^ 2 ∂inst.μ =
        hard_context inst.m a.val * (1 - hard_context inst.m a.val) *
          ∫ ω, w a ω ∂inst.μ := by
    let x := hard_context inst.m a.val
    have hcenter :
        ∫ ω, w a ω * (inst.y a ω - x) ∂inst.μ = 0 := by
      exact online_mc_hard_instance_predictable_centering inst a (w a)
        (hw_meas a) (hw_integrable a)
    have hident : ∀ ω, w a ω * (x - inst.y a ω) ^ 2 =
        x * (1 - x) * w a ω +
          (1 - 2 * x) * (w a ω * (inst.y a ω - x)) := by
      intro ω
      rcases inst.y_binary a ω with hy | hy <;> rw [hy] <;> ring
    have hyx_bound : ∀ᵐ ω ∂inst.μ, ‖inst.y a ω - x‖ ≤ (1 : ℝ) := by
      filter_upwards with ω
      rcases inst.y_binary a ω with hy | hy <;> rw [hy] <;>
        simp only [Real.norm_eq_abs] <;>
        rcases hxa with ⟨hxl, hxu⟩
      · rw [abs_of_nonpos] <;> linarith
      · rw [abs_of_nonneg] <;> linarith
    calc
      ∫ ω, w a ω *
          (hard_context inst.m a.val - inst.y a ω) ^ 2 ∂inst.μ =
          ∫ ω, x * (1 - x) * w a ω +
            (1 - 2 * x) * (w a ω * (inst.y a ω - x)) ∂inst.μ := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall hident
      _ = x * (1 - x) * ∫ ω, w a ω ∂inst.μ +
          (1 - 2 * x) * ∫ ω,
            w a ω * (inst.y a ω - x) ∂inst.μ := by
        rw [MeasureTheory.integral_add]
        · rw [MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul]
        · exact (hw_integrable a).const_mul _
        · exact ((hw_integrable a).mul_bdd
            ((inst.y_meas a).sub measurable_const).aestronglyMeasurable
            hyx_bound).const_mul _
      _ = x * (1 - x) * ∫ ω, w a ω ∂inst.μ := by
        rw [hcenter]
        ring
  have hdiff_bound (a : Fin inst.T)
      (hxa : (1 : ℝ) / 4 ≤ hard_context inst.m a.val ∧
        hard_context inst.m a.val ≤ (3 : ℝ) / 4) (ω : inst.Ω) :
      ‖hard_context inst.m a.val - inst.y a ω‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    rcases inst.y_binary a ω with hy | hy
    · rw [hy, sub_zero, abs_of_nonneg] <;> linarith [hxa.1, hxa.2]
    · rw [hy, abs_of_nonpos] <;> linarith [hxa.1, hxa.2]
  have hterm_integrable (A : Finset (Fin inst.T))
      (hxA : ∀ t ∈ A, (1 : ℝ) / 4 ≤ hard_context inst.m t.val ∧
        hard_context inst.m t.val ≤ (3 : ℝ) / 4)
      (a : Fin inst.T)
      (hxa : (1 : ℝ) / 4 ≤ hard_context inst.m a.val ∧
        hard_context inst.m a.val ≤ (3 : ℝ) / 4) (q r : ℕ) :
      MeasureTheory.Integrable (fun ω =>
        (X A ω) ^ q * w a ω *
          (hard_context inst.m a.val - inst.y a ω) ^ r) inst.μ := by
    have hfirst : MeasureTheory.Integrable
        (fun ω => (X A ω) ^ q * w a ω) inst.μ := by
      simpa only [Pi.mul_apply] using
        (hX_pow_integrable A hxA q).mul_bdd
          (hw_ambient a).aestronglyMeasurable
          (Filter.Eventually.of_forall (hw_norm a))
    simpa only [Pi.mul_apply, Pi.sub_apply] using hfirst.mul_bdd
      ((measurable_const.sub (inst.y_meas a)).pow_const r).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (hdiff_bound a hxa ω))
  change (37 : ℝ) / 432 * ∫ ω, W S ω ∂inst.μ ≤
    4 * Real.sqrt (S.card : ℝ) * ∫ ω, |X S ω| ∂inst.μ
  have hmoments : ∀ A : Finset (Fin inst.T),
      (∀ t ∈ A, (1 : ℝ) / 4 ≤ hard_context inst.m t.val ∧
        hard_context inst.m t.val ≤ (3 : ℝ) / 4) →
      ((3 : ℝ) / 16 * ∫ ω, W A ω ∂inst.μ ≤
          ∫ ω, (X A ω) ^ 2 ∂inst.μ) ∧
      (∫ ω, (X A ω) ^ 2 ∂inst.μ ≤ ∫ ω, W A ω ∂inst.μ) ∧
      (∫ ω, (X A ω) ^ 4 ∂inst.μ ≤
        11 * (A.card : ℝ) * ∫ ω, W A ω ∂inst.μ) := by
    intro A
    induction A using Finset.induction_on_max with
    | empty =>
        intro _
        simp [X, W]
    | insert a A hlt ih =>
        intro hx_insert
        have ha_not : a ∉ A := by
          intro ha
          exact (lt_irrefl a) (hlt a ha)
        have hxA : ∀ t ∈ A,
            (1 : ℝ) / 4 ≤ hard_context inst.m t.val ∧
              hard_context inst.m t.val ≤ (3 : ℝ) / 4 :=
          fun t ht => hx_insert t (Finset.mem_insert_of_mem ht)
        have hxa : (1 : ℝ) / 4 ≤ hard_context inst.m a.val ∧
            hard_context inst.m a.val ≤ (3 : ℝ) / 4 :=
          hx_insert a (Finset.mem_insert_self a A)
        rcases ih hxA with ⟨hsecond_lower, hsecond_upper, hfourth⟩
        have hX_insert (ω : inst.Ω) :
            X (insert a A) ω = X A ω +
              w a ω * (hard_context inst.m a.val - inst.y a ω) := by
          simp [X, ha_not, add_comm]
        have hW_insert (ω : inst.Ω) :
            W (insert a A) ω = W A ω + w a ω := by
          simp [W, ha_not, add_comm]
        have hW_eq :
            ∫ ω, W (insert a A) ω ∂inst.μ =
              ∫ ω, W A ω ∂inst.μ + ∫ ω, w a ω ∂inst.μ := by
          calc
            ∫ ω, W (insert a A) ω ∂inst.μ =
                ∫ ω, W A ω + w a ω ∂inst.μ := by
              apply MeasureTheory.integral_congr_ae
              exact Filter.Eventually.of_forall hW_insert
            _ = ∫ ω, W A ω ∂inst.μ + ∫ ω, w a ω ∂inst.μ := by
              simpa only [Pi.add_apply] using
                MeasureTheory.integral_add (hW_integrable A) (hw_integrable a)
        have hsecond_eq :
            ∫ ω, (X (insert a A) ω) ^ 2 ∂inst.μ =
              ∫ ω, (X A ω) ^ 2 ∂inst.μ +
                hard_context inst.m a.val *
                  (1 - hard_context inst.m a.val) *
                    ∫ ω, w a ω ∂inst.μ := by
          have hc1 : MeasureTheory.Integrable (fun ω =>
              X A ω * w a ω *
                (hard_context inst.m a.val - inst.y a ω)) inst.μ := by
            simpa using hterm_integrable A hxA a hxa 1 1
          have hc2 : MeasureTheory.Integrable (fun ω =>
              w a ω *
                (hard_context inst.m a.val - inst.y a ω) ^ 2) inst.μ := by
            simpa using hterm_integrable A hxA a hxa 0 2
          have hsep_inner :
              ∫ ω, (X A ω) ^ 2 +
                  2 * (X A ω * w a ω *
                    (hard_context inst.m a.val - inst.y a ω)) ∂inst.μ =
                ∫ ω, (X A ω) ^ 2 ∂inst.μ +
                  ∫ ω, 2 * (X A ω * w a ω *
                    (hard_context inst.m a.val - inst.y a ω)) ∂inst.μ := by
            simpa only [Pi.add_apply] using MeasureTheory.integral_add
              (hX_pow_integrable A hxA 2) (hc1.const_mul 2)
          have hsep_outer :
              ∫ ω, ((X A ω) ^ 2 +
                  2 * (X A ω * w a ω *
                    (hard_context inst.m a.val - inst.y a ω))) +
                  w a ω *
                    (hard_context inst.m a.val - inst.y a ω) ^ 2 ∂inst.μ =
                ∫ ω, (X A ω) ^ 2 +
                  2 * (X A ω * w a ω *
                    (hard_context inst.m a.val - inst.y a ω)) ∂inst.μ +
                ∫ ω, w a ω *
                  (hard_context inst.m a.val - inst.y a ω) ^ 2 ∂inst.μ := by
            simpa only [Pi.add_apply] using MeasureTheory.integral_add
              ((hX_pow_integrable A hxA 2).add (hc1.const_mul 2)) hc2
          have hcross1 := hcross A a hlt hxA 1
          norm_num at hcross1
          calc
            ∫ ω, (X (insert a A) ω) ^ 2 ∂inst.μ =
                ∫ ω, ((X A ω) ^ 2 +
                  2 * (X A ω * w a ω *
                    (hard_context inst.m a.val - inst.y a ω))) +
                  w a ω *
                    (hard_context inst.m a.val - inst.y a ω) ^ 2 ∂inst.μ := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with ω
              rw [hX_insert]
              rcases hw_binary a ω with hw | hw <;> rw [hw] <;> ring
            _ = ∫ ω, (X A ω) ^ 2 ∂inst.μ +
                ∫ ω, 2 * (X A ω * w a ω *
                  (hard_context inst.m a.val - inst.y a ω)) ∂inst.μ +
                ∫ ω, w a ω *
                  (hard_context inst.m a.val - inst.y a ω) ^ 2 ∂inst.μ := by
              rw [hsep_outer, hsep_inner]
            _ = ∫ ω, (X A ω) ^ 2 ∂inst.μ +
                hard_context inst.m a.val *
                  (1 - hard_context inst.m a.val) *
                    ∫ ω, w a ω ∂inst.μ := by
              rw [MeasureTheory.integral_const_mul, hcross1, hself a hxa]
              ring
        have hpoint4 (ω : inst.Ω) :
            (X (insert a A) ω) ^ 4 ≤
              ((X A ω) ^ 4 +
                4 * ((X A ω) ^ 3 * w a ω *
                  (hard_context inst.m a.val - inst.y a ω))) +
                8 * ((X A ω) ^ 2 * w a ω) + 3 * w a ω := by
          rw [hX_insert]
          rcases hw_binary a ω with hw | hw
          · simp [hw]
          · rw [hw]
            simp only [mul_one]
            let d := hard_context inst.m a.val - inst.y a ω
            have hdabs : |d| ≤ 1 := by
              simpa [Real.norm_eq_abs, d] using hdiff_bound a hxa ω
            have hdlo : -1 ≤ d := (abs_le.mp hdabs).1
            have hdhi : d ≤ 1 := (abs_le.mp hdabs).2
            have hd2 : d ^ 2 ≤ 1 := by
              nlinarith [mul_nonneg (sub_nonneg.mpr hdhi)
                (by linarith : 0 ≤ 1 + d)]
            have hd20 : 0 ≤ d ^ 2 := sq_nonneg d
            have hd4 : d ^ 4 ≤ 1 := by
              nlinarith [mul_nonneg hd20 (sub_nonneg.mpr hd2)]
            have hd40 : 0 ≤ d ^ 4 := by positivity
            have hd6 : d ^ 6 ≤ 1 := by
              nlinarith [mul_nonneg hd20 hd40,
                mul_nonneg hd20 (sub_nonneg.mpr hd4)]
            nlinarith [sq_nonneg (X A ω -
              (hard_context inst.m a.val - inst.y a ω) ^ 3),
              mul_nonneg (sq_nonneg (X A ω))
                (sub_nonneg.mpr hd2)]
        have hweighted_second :
            ∫ ω, (X A ω) ^ 2 * w a ω ∂inst.μ ≤
              ∫ ω, (X A ω) ^ 2 ∂inst.μ := by
          have hw2 : MeasureTheory.Integrable
              (fun ω => (X A ω) ^ 2 * w a ω) inst.μ := by
            simpa using hterm_integrable A hxA a hxa 2 0
          apply MeasureTheory.integral_mono hw2 (hX_pow_integrable A hxA 2)
          intro ω
          change X A ω ^ 2 * w a ω ≤ X A ω ^ 2
          rcases hw_binary a ω with hw | hw <;> rw [hw]
          · simp
            positivity
          · simp
        have hfourth_step :
            ∫ ω, (X (insert a A) ω) ^ 4 ∂inst.μ ≤
              ∫ ω, (X A ω) ^ 4 ∂inst.μ +
                8 * ∫ ω, (X A ω) ^ 2 * w a ω ∂inst.μ +
                  3 * ∫ ω, w a ω ∂inst.μ := by
          have hc3 : MeasureTheory.Integrable (fun ω =>
              (X A ω) ^ 3 * w a ω *
                (hard_context inst.m a.val - inst.y a ω)) inst.μ := by
            simpa using hterm_integrable A hxA a hxa 3 1
          have hc20 : MeasureTheory.Integrable
              (fun ω => (X A ω) ^ 2 * w a ω) inst.μ := by
            simpa using hterm_integrable A hxA a hxa 2 0
          have hright_integrable : MeasureTheory.Integrable (fun ω =>
              (((X A ω) ^ 4 +
                4 * ((X A ω) ^ 3 * w a ω *
                  (hard_context inst.m a.val - inst.y a ω))) +
                8 * ((X A ω) ^ 2 * w a ω)) + 3 * w a ω) inst.μ :=
            (((hX_pow_integrable A hxA 4).add (hc3.const_mul 4)).add
              (hc20.const_mul 8)).add ((hw_integrable a).const_mul 3)
          have hmono :
              ∫ ω, (X (insert a A) ω) ^ 4 ∂inst.μ ≤
                ∫ ω, (((X A ω) ^ 4 +
                  4 * ((X A ω) ^ 3 * w a ω *
                    (hard_context inst.m a.val - inst.y a ω))) +
                  8 * ((X A ω) ^ 2 * w a ω)) +
                    3 * w a ω ∂inst.μ := by
            apply MeasureTheory.integral_mono
              (hX_pow_integrable (insert a A) hx_insert 4) hright_integrable
            exact hpoint4
          have hsep1 :
              ∫ ω, (X A ω) ^ 4 +
                  4 * ((X A ω) ^ 3 * w a ω *
                    (hard_context inst.m a.val - inst.y a ω)) ∂inst.μ =
                ∫ ω, (X A ω) ^ 4 ∂inst.μ +
                  ∫ ω, 4 * ((X A ω) ^ 3 * w a ω *
                    (hard_context inst.m a.val - inst.y a ω)) ∂inst.μ := by
            simpa only [Pi.add_apply] using MeasureTheory.integral_add
              (hX_pow_integrable A hxA 4) (hc3.const_mul 4)
          have hsep2 :
              ∫ ω, ((X A ω) ^ 4 +
                  4 * ((X A ω) ^ 3 * w a ω *
                    (hard_context inst.m a.val - inst.y a ω))) +
                    8 * ((X A ω) ^ 2 * w a ω) ∂inst.μ =
                ∫ ω, (X A ω) ^ 4 +
                  4 * ((X A ω) ^ 3 * w a ω *
                    (hard_context inst.m a.val - inst.y a ω)) ∂inst.μ +
                  ∫ ω, 8 * ((X A ω) ^ 2 * w a ω) ∂inst.μ := by
            simpa only [Pi.add_apply] using MeasureTheory.integral_add
              ((hX_pow_integrable A hxA 4).add (hc3.const_mul 4))
              (hc20.const_mul 8)
          have hsep3 :
              ∫ ω, (((X A ω) ^ 4 +
                  4 * ((X A ω) ^ 3 * w a ω *
                    (hard_context inst.m a.val - inst.y a ω))) +
                    8 * ((X A ω) ^ 2 * w a ω)) +
                    3 * w a ω ∂inst.μ =
                ∫ ω, ((X A ω) ^ 4 +
                  4 * ((X A ω) ^ 3 * w a ω *
                    (hard_context inst.m a.val - inst.y a ω))) +
                    8 * ((X A ω) ^ 2 * w a ω) ∂inst.μ +
                  ∫ ω, 3 * w a ω ∂inst.μ := by
            simpa only [Pi.add_apply] using MeasureTheory.integral_add
              (((hX_pow_integrable A hxA 4).add (hc3.const_mul 4)).add
                (hc20.const_mul 8)) ((hw_integrable a).const_mul 3)
          have hcross3 := hcross A a hlt hxA 3
          norm_num at hcross3
          calc
            ∫ ω, (X (insert a A) ω) ^ 4 ∂inst.μ ≤
                ∫ ω, (((X A ω) ^ 4 +
                  4 * ((X A ω) ^ 3 * w a ω *
                    (hard_context inst.m a.val - inst.y a ω))) +
                    8 * ((X A ω) ^ 2 * w a ω)) +
                    3 * w a ω ∂inst.μ := hmono
            _ = ∫ ω, (X A ω) ^ 4 ∂inst.μ +
                8 * ∫ ω, (X A ω) ^ 2 * w a ω ∂inst.μ +
                  3 * ∫ ω, w a ω ∂inst.μ := by
              rw [hsep3, hsep2, hsep1]
              rw [MeasureTheory.integral_const_mul,
                MeasureTheory.integral_const_mul,
                MeasureTheory.integral_const_mul, hcross3]
              ring
        have hWA0 : 0 ≤ ∫ ω, W A ω ∂inst.μ :=
          MeasureTheory.integral_nonneg fun ω => hW_nonneg A ω
        have hwa0 : 0 ≤ ∫ ω, w a ω ∂inst.μ :=
          MeasureTheory.integral_nonneg fun ω => hw_nonneg a ω
        have hxvar_lower : (3 : ℝ) / 16 ≤
            hard_context inst.m a.val * (1 - hard_context inst.m a.val) := by
          nlinarith [hxa.1, hxa.2]
        have hxvar_upper :
            hard_context inst.m a.val * (1 - hard_context inst.m a.val) ≤ 1 := by
          nlinarith [hxa.1, hxa.2]
        refine ⟨?_, ?_, ?_⟩
        · rw [hsecond_eq, hW_eq]
          have hv := mul_le_mul_of_nonneg_right hxvar_lower hwa0
          nlinarith
        · rw [hsecond_eq, hW_eq]
          have hv := mul_le_mul_of_nonneg_right hxvar_upper hwa0
          nlinarith
        · rw [hW_eq, Finset.card_insert_of_notMem ha_not, Nat.cast_add,
            Nat.cast_one]
          have hcard_nonneg : 0 ≤ (A.card : ℝ) := by positivity
          have hcard_wa : 0 ≤ (A.card : ℝ) * ∫ ω, w a ω ∂inst.μ :=
            mul_nonneg hcard_nonneg hwa0
          nlinarith [hfourth_step, hweighted_second, hfourth]
  by_cases hS : S = ∅
  · subst S
    simp [X, W]
  · have hcard_pos_nat : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    have hcard_pos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hcard_pos_nat
    have hsqrt_pos : 0 < Real.sqrt (S.card : ℝ) := Real.sqrt_pos.2 hcard_pos
    have hsqrt_sq :
        Real.sqrt (S.card : ℝ) ^ 2 = (S.card : ℝ) :=
      Real.sq_sqrt (le_of_lt hcard_pos)
    rcases hmoments S hx with ⟨hsecond_lower, _, hfourth⟩
    have hX_integrable : MeasureTheory.Integrable (X S) inst.μ := by
      simpa using hX_pow_integrable S hx 1
    have habs_integrable :
        MeasureTheory.Integrable (fun ω => |X S ω|) inst.μ := by
      simpa only [Real.norm_eq_abs] using hX_integrable.norm
    have hpoint (ω : inst.Ω) :
        (X S ω) ^ 2 ≤
          4 * Real.sqrt (S.card : ℝ) * |X S ω| +
            (X S ω) ^ 4 / (108 * (S.card : ℝ)) := by
      let q := |X S ω|
      let r := Real.sqrt (S.card : ℝ)
      have hq : 0 ≤ q := abs_nonneg _
      have hr : 0 ≤ r := Real.sqrt_nonneg _
      have hfactor : 0 ≤ q * (q - 6 * r) ^ 2 * (q + 12 * r) :=
        mul_nonneg (mul_nonneg hq (sq_nonneg _)) (by positivity)
      have hpoly :
          108 * (S.card : ℝ) * (X S ω) ^ 2 ≤
            432 * (S.card : ℝ) * Real.sqrt (S.card : ℝ) * |X S ω| +
              (X S ω) ^ 4 := by
        have hq2 : q ^ 2 = (X S ω) ^ 2 := by
          dsimp [q]
          rw [sq_abs]
        have hq4 : q ^ 4 = (X S ω) ^ 4 := by
          nlinarith [hq2, sq_nonneg (q ^ 2), sq_nonneg ((X S ω) ^ 2)]
        dsimp [r] at hfactor
        nlinarith [hfactor, hsqrt_sq]
      have hden : 0 < 108 * (S.card : ℝ) := mul_pos (by norm_num) hcard_pos
      have hdiv :
          (X S ω) ^ 4 / (108 * (S.card : ℝ)) *
              (108 * (S.card : ℝ)) = (X S ω) ^ 4 :=
        div_mul_cancel₀ _ (ne_of_gt hden)
      nlinarith
    have hinterpolation :
        ∫ ω, (X S ω) ^ 2 ∂inst.μ ≤
          4 * Real.sqrt (S.card : ℝ) * ∫ ω, |X S ω| ∂inst.μ +
            (∫ ω, (X S ω) ^ 4 ∂inst.μ) /
              (108 * (S.card : ℝ)) := by
      have hright_integrable : MeasureTheory.Integrable (fun ω =>
          4 * Real.sqrt (S.card : ℝ) * |X S ω| +
            (X S ω) ^ 4 / (108 * (S.card : ℝ))) inst.μ :=
        (habs_integrable.const_mul _).add
          ((hX_pow_integrable S hx 4).div_const _)
      have hseparate :
          ∫ ω, 4 * Real.sqrt (S.card : ℝ) * |X S ω| +
              (X S ω) ^ 4 / (108 * (S.card : ℝ)) ∂inst.μ =
            ∫ ω, 4 * Real.sqrt (S.card : ℝ) * |X S ω| ∂inst.μ +
              ∫ ω, (X S ω) ^ 4 / (108 * (S.card : ℝ)) ∂inst.μ := by
        simpa only [Pi.add_apply] using MeasureTheory.integral_add
          (habs_integrable.const_mul _)
          ((hX_pow_integrable S hx 4).div_const _)
      calc
        ∫ ω, (X S ω) ^ 2 ∂inst.μ ≤
            ∫ ω, 4 * Real.sqrt (S.card : ℝ) * |X S ω| +
              (X S ω) ^ 4 / (108 * (S.card : ℝ)) ∂inst.μ := by
          apply MeasureTheory.integral_mono
            (hX_pow_integrable S hx 2) hright_integrable
          exact hpoint
        _ = 4 * Real.sqrt (S.card : ℝ) * ∫ ω, |X S ω| ∂inst.μ +
            (∫ ω, (X S ω) ^ 4 ∂inst.μ) /
              (108 * (S.card : ℝ)) := by
          rw [hseparate, MeasureTheory.integral_const_mul,
            MeasureTheory.integral_div]
    have hfourth_quot :
        (∫ ω, (X S ω) ^ 4 ∂inst.μ) / (108 * (S.card : ℝ)) ≤
          (11 : ℝ) / 108 * ∫ ω, W S ω ∂inst.μ := by
      calc
        (∫ ω, (X S ω) ^ 4 ∂inst.μ) / (108 * (S.card : ℝ)) ≤
            (11 * (S.card : ℝ) * ∫ ω, W S ω ∂inst.μ) /
              (108 * (S.card : ℝ)) :=
          (div_le_div_iff_of_pos_right
            (mul_pos (by norm_num) hcard_pos)).2 hfourth
        _ = (11 : ℝ) / 108 * ∫ ω, W S ω ∂inst.μ := by
          field_simp [ne_of_gt hcard_pos]
    nlinarith

@[blueprint "lem:group-error-ge-total-bias"
  (statement := /-- For every finite horizon, context sequence, prediction sequence, label sequence,
  and group function, the absolute total signed group bias is at most the group calibration error
  \cref{def:group-error}. -/)
  (proof := /-- Expand the group error using \cref{def:empirical-bias} and
  \cref{def:prediction-values}. Summing the empirical biases over all realized prediction values
  recovers the total signed group bias, since exactly one realized value equals the prediction on
  each round. The triangle inequality for the resulting finite sum gives the claim. -/)
  (title := /-- Group error dominates total signed bias -/)
  (latexEnv := "lemma")]
lemma group_error_ge_total_bias (T : ℕ) (x p y : Fin T → ℝ)
    (g : ℝ → ℝ → ℝ) :
    |∑ t : Fin T, g (x t) (p t) * (p t - y t)| ≤
      group_error T x p y g := by
  rw [group_error]
  have hsum :
      ∑ t : Fin T, g (x t) (p t) * (p t - y t) =
        ∑ v ∈ prediction_values T p, empirical_bias T x p y g v := by
    simp only [prediction_values, empirical_bias]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    symm
    calc
      ∑ v ∈ Finset.image p Finset.univ,
          (if p t = v then 1 else 0) * g (x t) (p t) * (p t - y t) =
          (∑ v ∈ Finset.image p Finset.univ,
            (if p t = v then (1 : ℝ) else 0)) *
              (g (x t) (p t) * (p t - y t)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = g (x t) (p t) * (p t - y t) := by simp
  rw [hsum]
  calc
    |∑ v ∈ prediction_values T p, empirical_bias T x p y g v| =
        ‖∑ v ∈ prediction_values T p, empirical_bias T x p y g v‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∑ v ∈ prediction_values T p, ‖empirical_bias T x p y g v‖ :=
      norm_sum_le _ _
    _ = ∑ v ∈ prediction_values T p, |empirical_bias T x p y g v| := by
      simp only [Real.norm_eq_abs]

@[blueprint "lem:partitioned-prediction-l1-bound"
  (statement := /-- Let a finite set of rounds carry predictions $p_t$, weights $a_t$, and
  partition labels $c_t$. If two nonzero-weight rounds with the same prediction always have the
  same partition label, then the sum over labels of the absolute aggregate weights is bounded by
  the sum over realized prediction values of the absolute aggregate weights. -/)
  (proof := /-- Refine each aggregate simultaneously by prediction value and partition label.
  The triangle inequality bounds each partition aggregate by the sum of the absolute refined
  aggregates. For a fixed prediction value, the disjointness hypothesis implies that at most one
  partition label has a nonzero refined aggregate, so summing its absolute values is exactly the
  absolute prediction-cell aggregate. Interchanging the two finite sums proves the inequality. -/)
  (title := /-- Partitioned aggregates inject into prediction-cell error -/)
  (latexEnv := "lemma")]
lemma partitioned_prediction_l1_bound (T : ℕ) {J : Type} [Fintype J]
    [DecidableEq J] (p a : Fin T → ℝ) (c : Fin T → J)
    (hdisjoint : ∀ s t, p s = p t → a s ≠ 0 → a t ≠ 0 → c s = c t) :
    (∑ j : J, |∑ t : Fin T, if c t = j then a t else 0|) ≤
      ∑ v ∈ Finset.image p Finset.univ,
        |∑ t : Fin T, if p t = v then a t else 0| := by
  let b (v : ℝ) (j : J) :=
    ∑ t : Fin T, if p t = v ∧ c t = j then a t else 0
  have hb_v (j : J) :
      ∑ v ∈ Finset.image p Finset.univ, b v j =
        ∑ t : Fin T, if c t = j then a t else 0 := by
    dsimp [b]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hc : c t = j
    · simp [hc]
    · simp [hc]
  have hb_j (v : ℝ) :
      ∑ j : J, b v j = ∑ t : Fin T, if p t = v then a t else 0 := by
    dsimp [b]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hp : p t = v
    · simp [hp]
    · simp [hp]
  have hb_cell (v : ℝ) : (∑ j : J, |b v j|) = |∑ j : J, b v j| := by
    by_cases he : ∃ t, p t = v ∧ a t ≠ 0
    · choose t0 ht0p ht0a using he
      let j0 := c t0
      have hzero (j : J) (hj : j ≠ j0) : b v j = 0 := by
        dsimp [b]
        apply Finset.sum_eq_zero
        intro t _
        by_cases hc : p t = v ∧ c t = j
        · by_cases hat : a t = 0
          · simp [hc, hat]
          · exfalso
            apply hj
            have hct := hdisjoint t0 t (ht0p.trans hc.1.symm) ht0a hat
            exact hc.2.symm.trans (hct.symm.trans rfl)
        · simp [hc]
      have habs : (∑ j : J, |b v j|) = |b v j0| := by
        apply Finset.sum_eq_single j0
        · intro j _ hj
          rw [hzero j hj, abs_zero]
        · simp
      have hsum : (∑ j : J, b v j) = b v j0 := by
        apply Finset.sum_eq_single j0
        · intro j _ hj
          exact hzero j hj
        · simp
      rw [habs, hsum]
    · have hall (t : Fin T) (ht : p t = v) : a t = 0 := by
        by_contra hat
        exact he ⟨t, ht, hat⟩
      have hz (j : J) : b v j = 0 := by
        dsimp [b]
        apply Finset.sum_eq_zero
        intro t _
        by_cases hc : p t = v ∧ c t = j
        · simp [hc, hall t hc.1]
        · simp [hc]
      simp [hz]
  calc
    (∑ j : J, |∑ t : Fin T, if c t = j then a t else 0|) =
        ∑ j : J, |∑ v ∈ Finset.image p Finset.univ, b v j| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hb_v]
    _ ≤ ∑ j : J, ∑ v ∈ Finset.image p Finset.univ, |b v j| := by
      apply Finset.sum_le_sum
      intro j _
      rw [← Real.norm_eq_abs]
      calc
        ‖∑ v ∈ Finset.image p Finset.univ, b v j‖ ≤
            ∑ v ∈ Finset.image p Finset.univ, ‖b v j‖ := norm_sum_le _ _
        _ = ∑ v ∈ Finset.image p Finset.univ, |b v j| := by
          simp only [Real.norm_eq_abs]
    _ = ∑ v ∈ Finset.image p Finset.univ, ∑ j : J, |b v j| := by
      rw [Finset.sum_comm]
    _ = ∑ v ∈ Finset.image p Finset.univ,
        |∑ t : Fin T, if p t = v then a t else 0| := by
      apply Finset.sum_congr rfl
      intro v _
      rw [hb_cell, hb_j]

@[blueprint "lem:finite-prediction-cell-l1-integrable"
  (statement := /-- On a probability space, let finitely many real-valued predictions and weights
  be measurable, and suppose every weight has norm at most one. Then the sum, over realized
  prediction values, of the absolute aggregate weight in each prediction fiber is integrable. -/)
  (proof := /-- Rewrite the sum over the outcome-dependent image of the prediction map as a sum
  over the fixed finite set of rounds: each fiber aggregate is divided by the positive cardinality
  of its fiber and then repeated once for each round in that fiber. The fiberwise image-sum identity
  proves this representation. Equality predicates between measurable real-valued predictions are
  measurable, so every numerator and fiber-cardinality denominator in the fixed finite sum is
  measurable. Finally, the triangle inequality and the unit bound on the weights bound the original
  cellwise $\ell^1$ sum by the number of rounds. Hence it is integrable. -/)
  (title := /-- Integrability of finite prediction-cell aggregates -/)
  (latexEnv := "lemma")]
lemma finite_prediction_cell_l1_integrable {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (T : ℕ) (p a : Fin T → Ω → ℝ)
    (hp : ∀ t, Measurable (p t)) (ha : ∀ t, Measurable (a t))
    (ha_bound : ∀ t ω, ‖a t ω‖ ≤ 1) :
    MeasureTheory.Integrable (fun ω =>
      ∑ v ∈ Finset.image (fun t => p t ω) Finset.univ,
        |∑ t : Fin T, if p t ω = v then a t ω else 0|) μ := by
  classical
  let A (s : Fin T) (ω : Ω) :=
    ∑ t : Fin T, if p t ω = p s ω then a t ω else 0
  let D (s : Fin T) (ω : Ω) :=
    ∑ t : Fin T, if p t ω = p s ω then (1 : ℝ) else 0
  let R (ω : Ω) := ∑ s : Fin T, |A s ω| / D s ω
  have hA_meas (s : Fin T) : Measurable (A s) := by
    dsimp [A]
    apply Finset.measurable_sum
    intro t _
    exact Measurable.ite (measurableSet_eq_fun (hp t) (hp s)) (ha t) measurable_const
  have hD_meas (s : Fin T) : Measurable (D s) := by
    dsimp [D]
    apply Finset.measurable_sum
    intro t _
    exact Measurable.ite (measurableSet_eq_fun (hp t) (hp s)) measurable_const
      measurable_const
  have hR_meas : Measurable R := by
    dsimp [R]
    apply Finset.measurable_sum
    intro s _
    have hAbs : Measurable (fun ω => |A s ω|) := by
      simpa only [Real.norm_eq_abs] using (hA_meas s).norm
    exact hAbs.div (hD_meas s)
  have hrepr (ω : Ω) :
      (∑ v ∈ Finset.image (fun t => p t ω) Finset.univ,
        |∑ t : Fin T, if p t ω = v then a t ω else 0|) = R ω := by
    dsimp [R]
    apply Finset.sum_image'
    intro s _
    have hcard_pos : 0 < (Finset.univ.filter
        (fun t : Fin T => p t ω = p s ω)).card := by
      rw [Finset.card_pos]
      exact ⟨s, by simp⟩
    have hDcard : D s ω = ((Finset.univ.filter
        (fun t : Fin T => p t ω = p s ω)).card : ℝ) := by
      simp [D]
    rw [Finset.sum_filter]
    calc
      |∑ t : Fin T, if p t ω = p s ω then a t ω else 0| =
          ∑ j ∈ Finset.univ.filter (fun t : Fin T => p t ω = p s ω),
            |A s ω| / D s ω := by
        rw [Finset.sum_const, hDcard]
        simp only [nsmul_eq_mul]
        field_simp [A]
        rfl
      _ = ∑ j ∈ Finset.univ.filter (fun t : Fin T => p t ω = p s ω),
          |∑ u : Fin T, if p u ω = p j ω then a u ω else 0| / D j ω := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjs : p j ω = p s ω := by simpa using hj
        have hnum :
            (∑ u : Fin T, if p u ω = p j ω then a u ω else 0) =
              ∑ u : Fin T, if p u ω = p s ω then a u ω else 0 := by
          rw [hjs]
        have hden : D j ω = D s ω := by
          dsimp [D]
          rw [hjs]
        rw [hnum, hden]
      _ = ∑ j : Fin T, if p j ω = p s ω then |A j ω| / D j ω else 0 := by
        rw [Finset.sum_filter]
  have hcell_meas : Measurable (fun ω =>
      ∑ v ∈ Finset.image (fun t => p t ω) Finset.univ,
        |∑ t : Fin T, if p t ω = v then a t ω else 0|) := by
    rw [show (fun ω =>
        ∑ v ∈ Finset.image (fun t => p t ω) Finset.univ,
          |∑ t : Fin T, if p t ω = v then a t ω else 0|) = R by
      funext ω
      exact hrepr ω]
    exact hR_meas
  apply MeasureTheory.Integrable.of_bound hcell_meas.aestronglyMeasurable (T : ℝ)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · calc
      ∑ v ∈ Finset.image (fun t => p t ω) Finset.univ,
          |∑ t : Fin T, if p t ω = v then a t ω else 0| ≤
          ∑ v ∈ Finset.image (fun t => p t ω) Finset.univ,
            ∑ t : Fin T, |if p t ω = v then a t ω else 0| := by
        apply Finset.sum_le_sum
        intro v _
        rw [← Real.norm_eq_abs]
        calc
          ‖∑ t : Fin T, if p t ω = v then a t ω else 0‖ ≤
              ∑ t : Fin T, ‖if p t ω = v then a t ω else 0‖ := norm_sum_le _ _
          _ = ∑ t : Fin T, |if p t ω = v then a t ω else 0| := by
            simp only [Real.norm_eq_abs]
      _ = ∑ t : Fin T, |a t ω| := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.sum_eq_single (p t ω)] <;> aesop
      _ ≤ ∑ _t : Fin T, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro t _
        simpa only [← Real.norm_eq_abs] using ha_bound t ω
      _ = (T : ℝ) := by simp
  · positivity

@[blueprint "lem:predictable-cell-instance-bound"
  (statement := /-- Every online multicalibration hard instance with horizon at least one million
  has expected summed group error at least $61/86400$ times its spread--drift score. -/)
  (proof := /-- Put $r=\sqrt{m/T}$ and $\eta=r/100$. The round-robin context cells have size at
  most $4T/m$, hence $r\sqrt{|S_j|}\le2$. Apply the predictable masked Bernoulli moment estimate
  \cref{lem:predictable-bernoulli-mask-moment-lower-bound} on each context cell. After subtracting
  the near-round displacement $|p^t-x^t|<\eta$, this yields the coefficient $61/86400$ for every
  cell. Context separation and \cref{lem:partitioned-prediction-l1-bound} embed the sum of these
  cellwise absolute biases into the middle-group error. The two tail groups are bounded by their
  signed total biases using \cref{lem:group-error-ge-total-bias}; predictable centering
  \cref{lem:online-mc-hard-instance-predictable-centering} removes their label noise, leaving
  $\eta$ times the number of far rounds. Integrability of all prediction-cell sums follows from
  \cref{lem:finite-prediction-cell-l1-integrable}. Finally
  \cref{lem:hard-group-family-partition} identifies the tail and near indicators as a partition,
  and summing the three bounds gives the stated multiple of the spread--drift score. -/)
  (title := /-- Fixed-instance predictable-cell lower bound -/)
  (latexEnv := "lemma")]
lemma predictable_cell_instance_bound (inst : online_mc_hard_instance)
    (hT : 1000000 ≤ inst.T) :
    expected_sum_group_error inst ≥ (61 : ℝ) / 86400 * spread_drift_score inst := by
  classical
  letI := inst.mΩ
  letI := inst.isProb
  let first := (inst.m + 3) / 4
  let count := (3 * inst.m) / 4 - first + 1
  let η := hard_threshold hard_construction_constant inst.m inst.T
  let r := Real.sqrt ((inst.m : ℝ) / (inst.T : ℝ))
  have hm_large : 100 ≤ inst.m := by
    by_contra hm
    have hmle : inst.m + 1 ≤ 100 := by omega
    have hcub := Nat.pow_le_pow_left hmle 3
    norm_num at hcub
    have hu := inst.hm_upper
    omega
  have hcount_pos : 0 < count := by
    dsimp [count, first]
    omega
  have hcount_large : inst.m ≤ 3 * count := by
    dsimp [count, first]
    omega
  have hmT : inst.m ≤ inst.T :=
    (Nat.le_pow (by norm_num : 0 < 3)).trans inst.hm_lower
  have hquotient_bound :
      (inst.T / count + 1) * inst.m ≤ 4 * inst.T := by
    calc
      (inst.T / count + 1) * inst.m =
          (inst.T / count) * inst.m + inst.m := by ring
      _ ≤ (inst.T / count) * (3 * count) + inst.T :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hcount_large) hmT
      _ = 3 * ((inst.T / count) * count) + inst.T := by ring
      _ ≤ 3 * inst.T + inst.T :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_left 3 (Nat.div_mul_le_self inst.T count)) inst.T
      _ = 4 * inst.T := by ring
  have hm_pos : (0 : ℝ) < inst.m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) inst.hm_grid)
  have hT_pos : (0 : ℝ) < inst.T := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hT)
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.sqrt_pos.2 (div_pos hm_pos hT_pos)
  have hr_sq : r ^ 2 = (inst.m : ℝ) / (inst.T : ℝ) := by
    dsimp [r]
    exact Real.sq_sqrt (div_nonneg (le_of_lt hm_pos) (le_of_lt hT_pos))
  have hcube : (inst.m : ℝ) ^ 3 ≤ (inst.T : ℝ) := by
    exact_mod_cast inst.hm_lower
  have hrm_sq : (r * (inst.m : ℝ)) ^ 2 ≤ 1 := by
    rw [mul_pow, hr_sq]
    calc
      (inst.m : ℝ) / (inst.T : ℝ) * (inst.m : ℝ) ^ 2 =
          (inst.m : ℝ) ^ 3 / (inst.T : ℝ) := by ring
      _ ≤ 1 := (div_le_iff₀ hT_pos).2 (by nlinarith)
  have hrm : r * (inst.m : ℝ) ≤ 1 := by
    nlinarith [sq_nonneg (r * (inst.m : ℝ) - 1)]
  have heta : η = r / 100 := by
    dsimp [η, hard_threshold]
    change hard_construction_constant * r = r / 100
    norm_num [hard_construction_constant]
    ring
  have heta_pos : 0 < η := by
    rw [heta]
    positivity
  have heta_sep : 2 * η < 1 / (inst.m : ℝ) := by
    apply (lt_div_iff₀ hm_pos).2
    rw [heta]
    nlinarith
  let cidx (t : Fin inst.T) : Fin count :=
    ⟨t.val % count, Nat.mod_lt _ hcount_pos⟩
  have hcontext_formula (t : Fin inst.T) :
      hard_context inst.m t.val =
        ((first + (cidx t).val : ℕ) : ℝ) / (inst.m : ℝ) := by
    simp only [hard_context]
    rfl
  have hcontext_range (t : Fin inst.T) :
      (1 : ℝ) / 4 ≤ hard_context inst.m t.val ∧
        hard_context inst.m t.val ≤ (3 : ℝ) / 4 := by
    rw [hcontext_formula]
    have hfirst : inst.m ≤ 4 * first := by
      dsimp [first]
      omega
    have hlast : first + (cidx t).val ≤ (3 * inst.m) / 4 := by
      have hj := (cidx t).isLt
      dsimp [count] at hj
      omega
    constructor
    · apply (le_div_iff₀ hm_pos).2
      have hfirst_real : (inst.m : ℝ) ≤ 4 * (first : ℝ) := by
        exact_mod_cast hfirst
      have hsum_ge : (first : ℝ) ≤ ((first + (cidx t).val : ℕ) : ℝ) := by
        exact_mod_cast (Nat.le_add_right first (cidx t).val)
      nlinarith
    · apply (div_le_iff₀ hm_pos).2
      have hlast4 : 4 * (first + (cidx t).val) ≤ 3 * inst.m := by
        omega
      have hlast_real :
          4 * ((first + (cidx t).val : ℕ) : ℝ) ≤ 3 * (inst.m : ℝ) := by
        exact_mod_cast hlast4
      nlinarith
  have hcontext_separated (s t : Fin inst.T) (hne : cidx s ≠ cidx t) :
      1 / (inst.m : ℝ) ≤
        |hard_context inst.m s.val - hard_context inst.m t.val| := by
    rw [hcontext_formula, hcontext_formula]
    have hvalne : (cidx s).val ≠ (cidx t).val := by
      intro h
      apply hne
      exact Fin.ext h
    rcases lt_or_gt_of_ne hvalne with hlt | hgt
    · have hnat : first + (cidx s).val + 1 ≤ first + (cidx t).val := by omega
      have hreal : (((first + (cidx s).val + 1 : ℕ) : ℝ) ≤
          ((first + (cidx t).val : ℕ) : ℝ)) := by exact_mod_cast hnat
      norm_num only [Nat.cast_add, Nat.cast_one] at hreal ⊢
      rw [abs_of_nonpos]
      · field_simp [ne_of_gt hm_pos]
        nlinarith
      · rw [sub_nonpos]
        apply (div_le_div_iff_of_pos_right hm_pos).2
        nlinarith
    · have hnat : first + (cidx t).val + 1 ≤ first + (cidx s).val := by omega
      have hreal : (((first + (cidx t).val + 1 : ℕ) : ℝ) ≤
          ((first + (cidx s).val : ℕ) : ℝ)) := by exact_mod_cast hnat
      norm_num only [Nat.cast_add, Nat.cast_one] at hreal ⊢
      rw [abs_of_nonneg]
      · field_simp [ne_of_gt hm_pos]
        nlinarith
      · rw [sub_nonneg]
        apply (div_le_div_iff_of_pos_right hm_pos).2
        nlinarith
  let cell (j : Fin count) : Finset (Fin inst.T) :=
    Finset.univ.filter (fun t => cidx t = j)
  have hcell_card (j : Fin count) :
      (cell j).card ≤ inst.T / count + 1 := by
    let f : Fin inst.T → ℕ := fun t => t.val / count
    rw [← Finset.card_range (inst.T / count + 1)]
    apply Finset.card_le_card_of_injOn f
      (s := cell j) (t := Finset.range (inst.T / count + 1))
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_range]
      dsimp [f]
      have hdiv : t.val / count ≤ inst.T / count :=
        Nat.div_le_div_right (Nat.le_of_lt t.isLt)
      omega
    · intro s hs t ht heq
      have hsmod : s.val % count = j.val := by
        have hsfin : cidx s = j := by simpa [cell] using hs
        have h := congrArg Fin.val hsfin
        simpa [cell, cidx] using h
      have htmod : t.val % count = j.val := by
        have htfin : cidx t = j := by simpa [cell] using ht
        have h := congrArg Fin.val htfin
        simpa [cell, cidx] using h
      dsimp [f] at heq
      apply Fin.ext
      calc
        s.val = count * (s.val / count) + s.val % count :=
          (Nat.div_add_mod s.val count).symm
        _ = count * (t.val / count) + t.val % count := by rw [heq, hsmod, htmod]
        _ = t.val := Nat.div_add_mod t.val count
  have hcell_nat (j : Fin count) : (cell j).card * inst.m ≤ 4 * inst.T := by
    exact le_trans (Nat.mul_le_mul_right inst.m (hcell_card j)) hquotient_bound
  have hcell_scale (j : Fin count) :
      r * Real.sqrt ((cell j).card : ℝ) ≤ 2 := by
    have hjreal : ((cell j).card : ℝ) * (inst.m : ℝ) ≤ 4 * (inst.T : ℝ) := by
      exact_mod_cast hcell_nat j
    have hsqrt_nonneg : 0 ≤ Real.sqrt ((cell j).card : ℝ) := Real.sqrt_nonneg _
    have hsqrt_sq : Real.sqrt ((cell j).card : ℝ) ^ 2 = ((cell j).card : ℝ) := by
      exact Real.sq_sqrt (by positivity)
    have hsq : (r * Real.sqrt ((cell j).card : ℝ)) ^ 2 ≤ 4 := by
      rw [mul_pow, hr_sq, hsqrt_sq]
      calc
        (inst.m : ℝ) / (inst.T : ℝ) * ((cell j).card : ℝ) =
            ((cell j).card : ℝ) * (inst.m : ℝ) / (inst.T : ℝ) := by ring
        _ ≤ 4 := (div_le_iff₀ hT_pos).2 (by nlinarith)
    nlinarith [sq_nonneg (r * Real.sqrt ((cell j).card : ℝ) + 2)]
  let near (t : Fin inst.T) (ω : inst.Ω) : ℝ :=
    if hard_context inst.m t.val - η < inst.p t ω ∧
      inst.p t ω < hard_context inst.m t.val + η then 1 else 0
  have hnear_past (t : Fin inst.T) :
      @Measurable inst.Ω ℝ
        (inst.algRandomness ⊔
          (⨆ s : Fin inst.T, ⨆ _ : s < t,
            MeasurableSpace.comap (inst.y s) inferInstance))
        inferInstance (near t) := by
    exact Measurable.ite
      ((measurableSet_lt measurable_const (inst.p_adapted t)).inter
        (measurableSet_lt (inst.p_adapted t) measurable_const))
      measurable_const measurable_const
  have hnear_meas (t : Fin inst.T) : Measurable (near t) := by
    exact (hnear_past t).mono
      (sup_le inst.alg_le
        (iSup_le fun s => iSup_le fun _ => (inst.y_meas s).comap_le)) le_rfl
  have hnear_binary (t : Fin inst.T) (ω : inst.Ω) :
      near t ω = 0 ∨ near t ω = 1 := by
    dsimp [near]
    split_ifs <;> simp
  have hnear_spec (t : Fin inst.T) (ω : inst.Ω) :
      near t ω = 1 ↔ |inst.p t ω - hard_context inst.m t.val| < η := by
    have heq :
        (hard_context inst.m t.val - η < inst.p t ω ∧
          inst.p t ω < hard_context inst.m t.val + η) ↔
        |inst.p t ω - hard_context inst.m t.val| < η := by
      rw [abs_lt]
      constructor <;> intro h <;> constructor <;> linarith
    dsimp [near]
    split_ifs with h <;> simp_all
  have hnear_nonneg (t : Fin inst.T) (ω : inst.Ω) : 0 ≤ near t ω := by
    rcases hnear_binary t ω with h | h <;> simp [h]
  have hnear_integrable (t : Fin inst.T) :
      MeasureTheory.Integrable (near t) inst.μ := by
    apply MeasureTheory.Integrable.of_bound (hnear_meas t).aestronglyMeasurable 1
    filter_upwards with ω
    rcases hnear_binary t ω with h | h <;> simp [h]
  have hxy_bound (t : Fin inst.T) (ω : inst.Ω) :
      ‖hard_context inst.m t.val - inst.y t ω‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    rcases inst.y_binary t ω with hy | hy
    · rw [hy, sub_zero, abs_of_nonneg] <;> linarith [(hcontext_range t).1,
        (hcontext_range t).2]
    · rw [hy, abs_of_nonpos] <;> linarith [(hcontext_range t).1,
        (hcontext_range t).2]
  have hpy_bound (t : Fin inst.T) (ω : inst.Ω) :
      ‖inst.p t ω - inst.y t ω‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    rcases inst.y_binary t ω with hy | hy
    · rw [hy, sub_zero, abs_of_nonneg] <;> linarith [(inst.p_range t ω).1,
        (inst.p_range t ω).2]
    · rw [hy, abs_of_nonpos] <;> linarith [(inst.p_range t ω).1,
        (inst.p_range t ω).2]
  have hnear_xy_integrable (t : Fin inst.T) :
      MeasureTheory.Integrable (fun ω => near t ω *
        (hard_context inst.m t.val - inst.y t ω)) inst.μ := by
    simpa only [Pi.mul_apply, Pi.sub_apply] using
      (hnear_integrable t).mul_bdd
        (measurable_const.sub (inst.y_meas t)).aestronglyMeasurable
        (Filter.Eventually.of_forall (hxy_bound t))
  have hnear_py_integrable (t : Fin inst.T) :
      MeasureTheory.Integrable (fun ω => near t ω *
        (inst.p t ω - inst.y t ω)) inst.μ := by
    have hp_meas : Measurable (inst.p t) :=
      (inst.p_adapted t).mono
        (sup_le inst.alg_le
          (iSup_le fun s => iSup_le fun _ => (inst.y_meas s).comap_le)) le_rfl
    simpa only [Pi.mul_apply, Pi.sub_apply] using
      (hnear_integrable t).mul_bdd
        (hp_meas.sub (inst.y_meas t)).aestronglyMeasurable
        (Filter.Eventually.of_forall (hpy_bound t))
  let N (j : Fin count) (ω : inst.Ω) := ∑ t ∈ cell j, near t ω
  let M (j : Fin count) (ω : inst.Ω) := ∑ t ∈ cell j,
    near t ω * (hard_context inst.m t.val - inst.y t ω)
  let B (j : Fin count) (ω : inst.Ω) := ∑ t ∈ cell j,
    near t ω * (inst.p t ω - inst.y t ω)
  have hN_integrable (j : Fin count) :
      MeasureTheory.Integrable (N j) inst.μ := by
    simpa [N] using MeasureTheory.integrable_finsetSum (cell j)
      (fun t _ => hnear_integrable t)
  have hM_integrable (j : Fin count) :
      MeasureTheory.Integrable (M j) inst.μ := by
    simpa [M] using MeasureTheory.integrable_finsetSum (cell j)
      (fun t _ => hnear_xy_integrable t)
  have hB_integrable (j : Fin count) :
      MeasureTheory.Integrable (B j) inst.μ := by
    simpa [B] using MeasureTheory.integrable_finsetSum (cell j)
      (fun t _ => hnear_py_integrable t)
  have hN_nonneg (j : Fin count) (ω : inst.Ω) : 0 ≤ N j ω := by
    dsimp [N]
    exact Finset.sum_nonneg fun t _ => hnear_nonneg t ω
  have hcell_moment (j : Fin count) :
      (37 : ℝ) / 432 * ∫ ω, N j ω ∂inst.μ ≤
        4 * Real.sqrt ((cell j).card : ℝ) * ∫ ω, |M j ω| ∂inst.μ := by
    simpa [N, M] using predictable_bernoulli_mask_moment_lower_bound
      inst (cell j) near hnear_past hnear_binary
        (fun t _ => hcontext_range t)
  have hMB_bound (j : Fin count) (ω : inst.Ω) :
      |M j ω - B j ω| ≤ η * N j ω := by
    have heq : M j ω - B j ω = ∑ t ∈ cell j,
        near t ω * (hard_context inst.m t.val - inst.p t ω) := by
      dsimp [M, B]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro t _
      ring
    rw [heq, ← Real.norm_eq_abs]
    calc
      ‖∑ t ∈ cell j, near t ω *
          (hard_context inst.m t.val - inst.p t ω)‖ ≤
          ∑ t ∈ cell j, ‖near t ω *
            (hard_context inst.m t.val - inst.p t ω)‖ := norm_sum_le _ _
      _ ≤ ∑ t ∈ cell j, η * near t ω := by
        apply Finset.sum_le_sum
        intro t _
        rcases hnear_binary t ω with hn | hn
        · simp [hn]
        · rw [hn, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          norm_num
          rw [abs_sub_comm]
          exact le_of_lt ((hnear_spec t ω).1 hn)
      _ = η * N j ω := by
        simp only [N, Finset.mul_sum]
  have hM_le_B (j : Fin count) :
      ∫ ω, |M j ω| ∂inst.μ ≤
        ∫ ω, |B j ω| ∂inst.μ + η * ∫ ω, N j ω ∂inst.μ := by
    have habsB_integrable : MeasureTheory.Integrable
        (fun ω => |B j ω|) inst.μ := by
      simpa only [Real.norm_eq_abs] using (hB_integrable j).norm
    have hMN_integrable : MeasureTheory.Integrable
        (fun ω => |B j ω| + η * N j ω) inst.μ :=
      habsB_integrable.add ((hN_integrable j).const_mul η)
    calc
      ∫ ω, |M j ω| ∂inst.μ ≤
          ∫ ω, |B j ω| + η * N j ω ∂inst.μ := by
        apply MeasureTheory.integral_mono
          (by simpa only [Real.norm_eq_abs] using (hM_integrable j).norm)
          hMN_integrable
        intro ω
        calc
          |M j ω| = |B j ω + (M j ω - B j ω)| := by ring_nf
          _ ≤ |B j ω| + |M j ω - B j ω| := abs_add_le _ _
          _ ≤ |B j ω| + η * N j ω :=
            add_le_add le_rfl (hMB_bound j ω)
      _ = ∫ ω, |B j ω| ∂inst.μ + η * ∫ ω, N j ω ∂inst.μ := by
        rw [MeasureTheory.integral_add, MeasureTheory.integral_const_mul]
        · simpa only [Real.norm_eq_abs] using (hB_integrable j).norm
        · exact (hN_integrable j).const_mul η
  have hcell_lower (j : Fin count) :
      (61 : ℝ) / 86400 * r * ∫ ω, N j ω ∂inst.μ ≤
        ∫ ω, |B j ω| ∂inst.μ := by
    have hNI : 0 ≤ ∫ ω, N j ω ∂inst.μ :=
      MeasureTheory.integral_nonneg (hN_nonneg j)
    have hMI : 0 ≤ ∫ ω, |M j ω| ∂inst.μ :=
      MeasureTheory.integral_nonneg fun _ => abs_nonneg _
    have hscaled := mul_le_mul_of_nonneg_left (hcell_moment j) hr_nonneg
    have hscale := hcell_scale j
    have hMlower :
        (37 : ℝ) / 3456 * r * ∫ ω, N j ω ∂inst.μ ≤
          ∫ ω, |M j ω| ∂inst.μ := by
      nlinarith
    rw [heta] at hM_le_B
    nlinarith [hM_le_B j]
  have hmiddle_point (ω : inst.Ω) :
      (∑ j : Fin count, |B j ω|) ≤
        group_error inst.T (fun t => hard_context inst.m t.val)
          (fun t => inst.p t ω) (fun t => inst.y t ω)
          (hard_group_family η 2) := by
    let a (t : Fin inst.T) := near t ω * (inst.p t ω - inst.y t ω)
    have hdisjoint (s t : Fin inst.T) (hp : inst.p s ω = inst.p t ω)
        (has : a s ≠ 0) (hat : a t ≠ 0) : cidx s = cidx t := by
      have hns : near s ω = 1 := by
        rcases hnear_binary s ω with hs | hs
        · exfalso
          apply has
          simp [a, hs]
        · exact hs
      have hnt : near t ω = 1 := by
        rcases hnear_binary t ω with ht | ht
        · exfalso
          apply hat
          simp [a, ht]
        · exact ht
      by_contra hc
      have hsep := hcontext_separated s t hc
      have hslt := (hnear_spec s ω).1 hns
      have htlt := (hnear_spec t ω).1 hnt
      have htri :
          |hard_context inst.m s.val - hard_context inst.m t.val| ≤
            |inst.p s ω - hard_context inst.m s.val| +
              |inst.p t ω - hard_context inst.m t.val| := by
        calc
          |hard_context inst.m s.val - hard_context inst.m t.val| =
              |(hard_context inst.m s.val - inst.p s ω) +
                (inst.p t ω - hard_context inst.m t.val)| := by rw [hp]; ring_nf
          _ ≤ |hard_context inst.m s.val - inst.p s ω| +
              |inst.p t ω - hard_context inst.m t.val| := abs_add_le _ _
          _ = |inst.p s ω - hard_context inst.m s.val| +
              |inst.p t ω - hard_context inst.m t.val| := by rw [abs_sub_comm]
      nlinarith [heta_sep]
    have hpart := partitioned_prediction_l1_bound inst.T
      (fun t => inst.p t ω) a cidx hdisjoint
    have hleft :
        (∑ j : Fin count, |∑ t : Fin inst.T,
          if cidx t = j then a t else 0|) = ∑ j : Fin count, |B j ω| := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      simp only [a, B, cell, Finset.sum_filter]
    have hg2 (t : Fin inst.T) :
        hard_group_family η 2 (hard_context inst.m t.val) (inst.p t ω) =
          near t ω := by
      simp only [hard_group_family]
      norm_num
      dsimp [near]
      have heq :
          (hard_context inst.m t.val - η < inst.p t ω ∧
            inst.p t ω < hard_context inst.m t.val + η) ↔
          |inst.p t ω - hard_context inst.m t.val| < η := by
        rw [abs_lt]
        constructor <;> intro h <;> constructor <;> linarith
      simp only [heq]
    have hright :
        (∑ v ∈ Finset.image (fun t => inst.p t ω) Finset.univ,
          |∑ t : Fin inst.T,
            if inst.p t ω = v then a t else 0|) =
          group_error inst.T (fun t => hard_context inst.m t.val)
            (fun t => inst.p t ω) (fun t => inst.y t ω)
            (hard_group_family η 2) := by
      rw [group_error]
      simp only [prediction_values, empirical_bias]
      apply Finset.sum_congr rfl
      intro v _
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      rw [hg2]
      by_cases hpv : inst.p t ω = v <;> simp [a, hpv]
    rw [← hleft, ← hright]
    exact hpart
  have hp_meas (t : Fin inst.T) : Measurable (inst.p t) := by
    exact (inst.p_adapted t).mono
      (sup_le inst.alg_le
        (iSup_le fun s => iSup_le fun _ => (inst.y_meas s).comap_le)) le_rfl
  let q0 (t : Fin inst.T) (ω : inst.Ω) : ℝ :=
    if hard_context inst.m t.val + η ≤ inst.p t ω then 1 else 0
  let q1 (t : Fin inst.T) (ω : inst.Ω) : ℝ :=
    if inst.p t ω ≤ hard_context inst.m t.val - η then 1 else 0
  have hq0_past (t : Fin inst.T) :
      @Measurable inst.Ω ℝ
        (inst.algRandomness ⊔
          (⨆ s : Fin inst.T, ⨆ _ : s < t,
            MeasurableSpace.comap (inst.y s) inferInstance))
        inferInstance (q0 t) := by
    exact Measurable.ite (measurableSet_le measurable_const (inst.p_adapted t))
      measurable_const measurable_const
  have hq1_past (t : Fin inst.T) :
      @Measurable inst.Ω ℝ
        (inst.algRandomness ⊔
          (⨆ s : Fin inst.T, ⨆ _ : s < t,
            MeasurableSpace.comap (inst.y s) inferInstance))
        inferInstance (q1 t) := by
    exact Measurable.ite (measurableSet_le (inst.p_adapted t) measurable_const)
      measurable_const measurable_const
  have hq0_meas (t : Fin inst.T) : Measurable (q0 t) := by
    exact (hq0_past t).mono
      (sup_le inst.alg_le
        (iSup_le fun s => iSup_le fun _ => (inst.y_meas s).comap_le)) le_rfl
  have hq1_meas (t : Fin inst.T) : Measurable (q1 t) := by
    exact (hq1_past t).mono
      (sup_le inst.alg_le
        (iSup_le fun s => iSup_le fun _ => (inst.y_meas s).comap_le)) le_rfl
  have hq0_binary (t : Fin inst.T) (ω : inst.Ω) :
      q0 t ω = 0 ∨ q0 t ω = 1 := by
    dsimp [q0]
    split_ifs <;> simp
  have hq1_binary (t : Fin inst.T) (ω : inst.Ω) :
      q1 t ω = 0 ∨ q1 t ω = 1 := by
    dsimp [q1]
    split_ifs <;> simp
  have hq0_spec (t : Fin inst.T) (ω : inst.Ω) :
      q0 t ω = 1 ↔ hard_context inst.m t.val + η ≤ inst.p t ω := by
    dsimp [q0]
    split_ifs with h <;> simp [h]
  have hq1_spec (t : Fin inst.T) (ω : inst.Ω) :
      q1 t ω = 1 ↔ inst.p t ω ≤ hard_context inst.m t.val - η := by
    dsimp [q1]
    split_ifs with h <;> simp [h]
  have hg0 (t : Fin inst.T) (ω : inst.Ω) :
      hard_group_family η 0 (hard_context inst.m t.val) (inst.p t ω) = q0 t ω := by
    simp [hard_group_family, q0]
  have hg1 (t : Fin inst.T) (ω : inst.Ω) :
      hard_group_family η 1 (hard_context inst.m t.val) (inst.p t ω) = q1 t ω := by
    simp [hard_group_family, q1]
  have hg2 (t : Fin inst.T) (ω : inst.Ω) :
      hard_group_family η 2 (hard_context inst.m t.val) (inst.p t ω) = near t ω := by
    simp only [hard_group_family]
    norm_num
    dsimp [near]
    have heq :
        (hard_context inst.m t.val - η < inst.p t ω ∧
          inst.p t ω < hard_context inst.m t.val + η) ↔
        |inst.p t ω - hard_context inst.m t.val| < η := by
      rw [abs_lt]
      constructor <;> intro h <;> constructor <;> linarith
    simp only [heq]
  let a0 (t : Fin inst.T) (ω : inst.Ω) :=
    q0 t ω * (inst.p t ω - inst.y t ω)
  let a1 (t : Fin inst.T) (ω : inst.Ω) :=
    q1 t ω * (inst.p t ω - inst.y t ω)
  let a2 (t : Fin inst.T) (ω : inst.Ω) :=
    near t ω * (inst.p t ω - inst.y t ω)
  have ha0_meas (t : Fin inst.T) : Measurable (a0 t) := by
    exact (hq0_meas t).mul ((hp_meas t).sub (inst.y_meas t))
  have ha1_meas (t : Fin inst.T) : Measurable (a1 t) := by
    exact (hq1_meas t).mul ((hp_meas t).sub (inst.y_meas t))
  have ha2_meas (t : Fin inst.T) : Measurable (a2 t) := by
    exact (hnear_meas t).mul ((hp_meas t).sub (inst.y_meas t))
  have ha0_bound (t : Fin inst.T) (ω : inst.Ω) : ‖a0 t ω‖ ≤ 1 := by
    dsimp [a0]
    rw [abs_mul]
    rcases hq0_binary t ω with h | h <;> rw [h]
    · simp
    · simpa using hpy_bound t ω
  have ha1_bound (t : Fin inst.T) (ω : inst.Ω) : ‖a1 t ω‖ ≤ 1 := by
    dsimp [a1]
    rw [abs_mul]
    rcases hq1_binary t ω with h | h <;> rw [h]
    · simp
    · simpa using hpy_bound t ω
  have ha2_bound (t : Fin inst.T) (ω : inst.Ω) : ‖a2 t ω‖ ≤ 1 := by
    dsimp [a2]
    rw [abs_mul]
    rcases hnear_binary t ω with h | h <;> rw [h]
    · simp
    · simpa using hpy_bound t ω
  have hG0_integrable : MeasureTheory.Integrable (fun ω =>
      group_error inst.T (fun t => hard_context inst.m t.val)
        (fun t => inst.p t ω) (fun t => inst.y t ω)
        (hard_group_family η 0)) inst.μ := by
    have hraw := finite_prediction_cell_l1_integrable inst.μ inst.T
      (fun t => inst.p t) a0 hp_meas ha0_meas ha0_bound
    simpa [group_error, prediction_values, empirical_bias, a0, hg0] using hraw
  have hG1_integrable : MeasureTheory.Integrable (fun ω =>
      group_error inst.T (fun t => hard_context inst.m t.val)
        (fun t => inst.p t ω) (fun t => inst.y t ω)
        (hard_group_family η 1)) inst.μ := by
    have hraw := finite_prediction_cell_l1_integrable inst.μ inst.T
      (fun t => inst.p t) a1 hp_meas ha1_meas ha1_bound
    simpa [group_error, prediction_values, empirical_bias, a1, hg1] using hraw
  have hG2_integrable : MeasureTheory.Integrable (fun ω =>
      group_error inst.T (fun t => hard_context inst.m t.val)
        (fun t => inst.p t ω) (fun t => inst.y t ω)
        (hard_group_family η 2)) inst.μ := by
    have hraw := finite_prediction_cell_l1_integrable inst.μ inst.T
      (fun t => inst.p t) a2 hp_meas ha2_meas ha2_bound
    simpa [group_error, prediction_values, empirical_bias, a2, hg2] using hraw
  have hq0_integrable (t : Fin inst.T) :
      MeasureTheory.Integrable (q0 t) inst.μ := by
    apply MeasureTheory.Integrable.of_bound (hq0_meas t).aestronglyMeasurable 1
    filter_upwards with ω
    rcases hq0_binary t ω with h | h <;> simp [h]
  have hq1_integrable (t : Fin inst.T) :
      MeasureTheory.Integrable (q1 t) inst.μ := by
    apply MeasureTheory.Integrable.of_bound (hq1_meas t).aestronglyMeasurable 1
    filter_upwards with ω
    rcases hq1_binary t ω with h | h <;> simp [h]
  have ha0_integrable (t : Fin inst.T) :
      MeasureTheory.Integrable (a0 t) inst.μ := by
    apply MeasureTheory.Integrable.of_bound (ha0_meas t).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (ha0_bound t)
  have ha1_integrable (t : Fin inst.T) :
      MeasureTheory.Integrable (a1 t) inst.μ := by
    apply MeasureTheory.Integrable.of_bound (ha1_meas t).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (ha1_bound t)
  have hpx_bound (t : Fin inst.T) (ω : inst.Ω) :
      ‖inst.p t ω - hard_context inst.m t.val‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    rcases le_total (inst.p t ω) (hard_context inst.m t.val) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      linarith [(inst.p_range t ω).1, (hcontext_range t).2]
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      linarith [(inst.p_range t ω).2, (hcontext_range t).1]
  have hq0_drift_integrable (t : Fin inst.T) :
      MeasureTheory.Integrable (fun ω => q0 t ω *
        (inst.p t ω - hard_context inst.m t.val)) inst.μ := by
    simpa only [Pi.mul_apply, Pi.sub_apply] using
      (hq0_integrable t).mul_bdd
        ((hp_meas t).sub measurable_const).aestronglyMeasurable
        (Filter.Eventually.of_forall (hpx_bound t))
  have hq1_drift_integrable (t : Fin inst.T) :
      MeasureTheory.Integrable (fun ω => q1 t ω *
        (hard_context inst.m t.val - inst.p t ω)) inst.μ := by
    simpa only [Pi.mul_apply, Pi.sub_apply] using
      (hq1_integrable t).mul_bdd
        (measurable_const.sub (hp_meas t)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by
          simpa only [Pi.sub_apply, norm_sub_rev] using hpx_bound t ω)
  have hq0_noise_integrable (t : Fin inst.T) :
      MeasureTheory.Integrable (fun ω => q0 t ω *
        (hard_context inst.m t.val - inst.y t ω)) inst.μ := by
    simpa only [Pi.mul_apply, Pi.sub_apply] using
      (hq0_integrable t).mul_bdd
        (measurable_const.sub (inst.y_meas t)).aestronglyMeasurable
        (Filter.Eventually.of_forall (hxy_bound t))
  have hq1_noise_integrable (t : Fin inst.T) :
      MeasureTheory.Integrable (fun ω => q1 t ω *
        (hard_context inst.m t.val - inst.y t ω)) inst.μ := by
    simpa only [Pi.mul_apply, Pi.sub_apply] using
      (hq1_integrable t).mul_bdd
        (measurable_const.sub (inst.y_meas t)).aestronglyMeasurable
        (Filter.Eventually.of_forall (hxy_bound t))
  have hq0_noise_mean (t : Fin inst.T) :
      ∫ ω, q0 t ω * (hard_context inst.m t.val - inst.y t ω) ∂inst.μ = 0 := by
    have hc := online_mc_hard_instance_predictable_centering inst t (q0 t)
      (hq0_past t) (hq0_integrable t)
    calc
      ∫ ω, q0 t ω * (hard_context inst.m t.val - inst.y t ω) ∂inst.μ =
          -∫ ω, q0 t ω * (inst.y t ω - hard_context inst.m t.val) ∂inst.μ := by
        rw [← MeasureTheory.integral_neg]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with ω
        ring
      _ = 0 := by rw [hc]; ring
  have hq1_noise_mean (t : Fin inst.T) :
      ∫ ω, q1 t ω * (hard_context inst.m t.val - inst.y t ω) ∂inst.μ = 0 := by
    have hc := online_mc_hard_instance_predictable_centering inst t (q1 t)
      (hq1_past t) (hq1_integrable t)
    calc
      ∫ ω, q1 t ω * (hard_context inst.m t.val - inst.y t ω) ∂inst.μ =
          -∫ ω, q1 t ω * (inst.y t ω - hard_context inst.m t.val) ∂inst.μ := by
        rw [← MeasureTheory.integral_neg]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with ω
        ring
      _ = 0 := by rw [hc]; ring
  have ha0_mean (t : Fin inst.T) :
      ∫ ω, a0 t ω ∂inst.μ =
        ∫ ω, q0 t ω * (inst.p t ω - hard_context inst.m t.val) ∂inst.μ := by
    calc
      ∫ ω, a0 t ω ∂inst.μ = ∫ ω,
          q0 t ω * (inst.p t ω - hard_context inst.m t.val) +
            q0 t ω * (hard_context inst.m t.val - inst.y t ω) ∂inst.μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with ω
        dsimp [a0]
        ring
      _ = ∫ ω, q0 t ω * (inst.p t ω - hard_context inst.m t.val) ∂inst.μ +
          ∫ ω, q0 t ω * (hard_context inst.m t.val - inst.y t ω) ∂inst.μ := by
        rw [MeasureTheory.integral_add (hq0_drift_integrable t)
          (hq0_noise_integrable t)]
      _ = ∫ ω, q0 t ω * (inst.p t ω - hard_context inst.m t.val) ∂inst.μ := by
        rw [hq0_noise_mean]
        ring
  have ha1_mean (t : Fin inst.T) :
      -∫ ω, a1 t ω ∂inst.μ =
        ∫ ω, q1 t ω * (hard_context inst.m t.val - inst.p t ω) ∂inst.μ := by
    have hsplit :
        ∫ ω, a1 t ω ∂inst.μ =
          ∫ ω, q1 t ω * (inst.p t ω - hard_context inst.m t.val) ∂inst.μ := by
      have hrev_integrable : MeasureTheory.Integrable
          (fun ω => q1 t ω * (inst.p t ω - hard_context inst.m t.val)) inst.μ := by
        simpa only [Pi.mul_apply, Pi.sub_apply] using
          (hq1_integrable t).mul_bdd
            ((hp_meas t).sub measurable_const).aestronglyMeasurable
            (Filter.Eventually.of_forall (hpx_bound t))
      calc
        ∫ ω, a1 t ω ∂inst.μ = ∫ ω,
            q1 t ω * (inst.p t ω - hard_context inst.m t.val) +
              q1 t ω * (hard_context inst.m t.val - inst.y t ω) ∂inst.μ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with ω
          dsimp [a1]
          ring
        _ = ∫ ω, q1 t ω * (inst.p t ω - hard_context inst.m t.val) ∂inst.μ +
            ∫ ω, q1 t ω * (hard_context inst.m t.val - inst.y t ω) ∂inst.μ := by
          rw [MeasureTheory.integral_add]
          · exact hrev_integrable
          · exact hq1_noise_integrable t
        _ = ∫ ω, q1 t ω * (inst.p t ω - hard_context inst.m t.val) ∂inst.μ := by
          rw [hq1_noise_mean]
          ring
    rw [hsplit, ← MeasureTheory.integral_neg]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with ω
    ring
  let Q0 (ω : inst.Ω) := ∑ t : Fin inst.T, q0 t ω
  let Q1 (ω : inst.Ω) := ∑ t : Fin inst.T, q1 t ω
  let Z0 (ω : inst.Ω) := ∑ t : Fin inst.T, a0 t ω
  let Z1 (ω : inst.Ω) := ∑ t : Fin inst.T, a1 t ω
  have hQ0_integrable : MeasureTheory.Integrable Q0 inst.μ := by
    simpa [Q0] using MeasureTheory.integrable_finsetSum Finset.univ
      (fun t _ => hq0_integrable t)
  have hQ1_integrable : MeasureTheory.Integrable Q1 inst.μ := by
    simpa [Q1] using MeasureTheory.integrable_finsetSum Finset.univ
      (fun t _ => hq1_integrable t)
  have hZ0_integrable : MeasureTheory.Integrable Z0 inst.μ := by
    simpa [Z0] using MeasureTheory.integrable_finsetSum Finset.univ
      (fun t _ => ha0_integrable t)
  have hZ1_integrable : MeasureTheory.Integrable Z1 inst.μ := by
    simpa [Z1] using MeasureTheory.integrable_finsetSum Finset.univ
      (fun t _ => ha1_integrable t)
  have hterm0 (t : Fin inst.T) :
      η * ∫ ω, q0 t ω ∂inst.μ ≤ ∫ ω, a0 t ω ∂inst.μ := by
    rw [ha0_mean t, ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_mono ((hq0_integrable t).const_mul η)
      (hq0_drift_integrable t)
    intro ω
    change η * q0 t ω ≤ q0 t ω * (inst.p t ω - hard_context inst.m t.val)
    rcases hq0_binary t ω with h | h
    · simp [h]
    · rw [h]
      have hs := (hq0_spec t ω).1 h
      nlinarith
  have hterm1 (t : Fin inst.T) :
      η * ∫ ω, q1 t ω ∂inst.μ ≤ -∫ ω, a1 t ω ∂inst.μ := by
    rw [ha1_mean t, ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_mono ((hq1_integrable t).const_mul η)
      (hq1_drift_integrable t)
    intro ω
    change η * q1 t ω ≤ q1 t ω * (hard_context inst.m t.val - inst.p t ω)
    rcases hq1_binary t ω with h | h
    · simp [h]
    · rw [h]
      have hs := (hq1_spec t ω).1 h
      nlinarith
  have htail0_drift : η * ∫ ω, Q0 ω ∂inst.μ ≤ ∫ ω, Z0 ω ∂inst.μ := by
    calc
      η * ∫ ω, Q0 ω ∂inst.μ =
          η * ∑ t : Fin inst.T, ∫ ω, q0 t ω ∂inst.μ := by
        congr 1
        simpa [Q0] using MeasureTheory.integral_finsetSum Finset.univ
          (fun t _ => hq0_integrable t)
      _ = ∑ t : Fin inst.T, η * ∫ ω, q0 t ω ∂inst.μ := by
        rw [Finset.mul_sum]
      _ ≤ ∑ t : Fin inst.T, ∫ ω, a0 t ω ∂inst.μ := by
        exact Finset.sum_le_sum fun t _ => hterm0 t
      _ = ∫ ω, Z0 ω ∂inst.μ := by
        symm
        simpa [Z0] using MeasureTheory.integral_finsetSum Finset.univ
          (fun t _ => ha0_integrable t)
  have htail1_drift : η * ∫ ω, Q1 ω ∂inst.μ ≤ -∫ ω, Z1 ω ∂inst.μ := by
    calc
      η * ∫ ω, Q1 ω ∂inst.μ =
          η * ∑ t : Fin inst.T, ∫ ω, q1 t ω ∂inst.μ := by
        congr 1
        simpa [Q1] using MeasureTheory.integral_finsetSum Finset.univ
          (fun t _ => hq1_integrable t)
      _ = ∑ t : Fin inst.T, η * ∫ ω, q1 t ω ∂inst.μ := by
        rw [Finset.mul_sum]
      _ ≤ ∑ t : Fin inst.T, -∫ ω, a1 t ω ∂inst.μ := by
        exact Finset.sum_le_sum fun t _ => hterm1 t
      _ = -∑ t : Fin inst.T, ∫ ω, a1 t ω ∂inst.μ := by
        rw [Finset.sum_neg_distrib]
      _ = -∫ ω, Z1 ω ∂inst.μ := by
        congr 1
        simpa [Z1] using (MeasureTheory.integral_finsetSum Finset.univ
          (fun t _ => ha1_integrable t)).symm
  have hG0_point (ω : inst.Ω) : Z0 ω ≤
      group_error inst.T (fun t => hard_context inst.m t.val)
        (fun t => inst.p t ω) (fun t => inst.y t ω)
        (hard_group_family η 0) := by
    have htotal := group_error_ge_total_bias inst.T
      (fun t => hard_context inst.m t.val) (fun t => inst.p t ω)
      (fun t => inst.y t ω) (hard_group_family η 0)
    have heq : (∑ t : Fin inst.T,
        hard_group_family η 0 (hard_context inst.m t.val) (inst.p t ω) *
          (inst.p t ω - inst.y t ω)) = Z0 ω := by
      apply Finset.sum_congr rfl
      intro t _
      rw [hg0]
    rw [heq] at htotal
    exact le_trans (le_abs_self _) htotal
  have hG1_point (ω : inst.Ω) : -Z1 ω ≤
      group_error inst.T (fun t => hard_context inst.m t.val)
        (fun t => inst.p t ω) (fun t => inst.y t ω)
        (hard_group_family η 1) := by
    have htotal := group_error_ge_total_bias inst.T
      (fun t => hard_context inst.m t.val) (fun t => inst.p t ω)
      (fun t => inst.y t ω) (hard_group_family η 1)
    have heq : (∑ t : Fin inst.T,
        hard_group_family η 1 (hard_context inst.m t.val) (inst.p t ω) *
          (inst.p t ω - inst.y t ω)) = Z1 ω := by
      apply Finset.sum_congr rfl
      intro t _
      rw [hg1]
    rw [heq] at htotal
    exact le_trans (neg_le_abs _) htotal
  have htail0 : η * ∫ ω, Q0 ω ∂inst.μ ≤ ∫ ω,
      group_error inst.T (fun t => hard_context inst.m t.val)
        (fun t => inst.p t ω) (fun t => inst.y t ω)
        (hard_group_family η 0) ∂inst.μ := by
    exact htail0_drift.trans (MeasureTheory.integral_mono hZ0_integrable
      hG0_integrable hG0_point)
  have htail1 : η * ∫ ω, Q1 ω ∂inst.μ ≤ ∫ ω,
      group_error inst.T (fun t => hard_context inst.m t.val)
        (fun t => inst.p t ω) (fun t => inst.y t ω)
        (hard_group_family η 1) ∂inst.μ := by
    have hnegZ1 : MeasureTheory.Integrable (fun ω => -Z1 ω) inst.μ :=
      hZ1_integrable.neg
    have hmono := MeasureTheory.integral_mono hnegZ1 hG1_integrable hG1_point
    rw [MeasureTheory.integral_neg] at hmono
    exact htail1_drift.trans hmono
  let Q2 (ω : inst.Ω) := ∑ t : Fin inst.T, near t ω
  have hQ2_integrable : MeasureTheory.Integrable Q2 inst.μ := by
    simpa [Q2] using MeasureTheory.integrable_finsetSum Finset.univ
      (fun t _ => hnear_integrable t)
  have hcell_partition (ω : inst.Ω) :
      (∑ j : Fin count, N j ω) = Q2 ω := by
    dsimp [N, Q2]
    calc
      (∑ j : Fin count, ∑ t ∈ cell j, near t ω) =
          ∑ j : Fin count, ∑ t : Fin inst.T,
            if cidx t = j then near t ω else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_filter]
      _ = ∑ t : Fin inst.T, near t ω := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        simp
  have hsumB_integrable : MeasureTheory.Integrable
      (fun ω => ∑ j : Fin count, |B j ω|) inst.μ := by
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro j _
    simpa only [Real.norm_eq_abs] using (hB_integrable j).norm
  have hmiddle_cells :
      (61 : ℝ) / 86400 * r * ∫ ω, Q2 ω ∂inst.μ ≤
        ∫ ω, ∑ j : Fin count, |B j ω| ∂inst.μ := by
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hcell_lower j)
    have hpartition_integral :
        (∫ ω, Q2 ω ∂inst.μ) =
          ∫ ω, ∑ j : Fin count, N j ω ∂inst.μ := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => (hcell_partition ω).symm
    calc
      (61 : ℝ) / 86400 * r * ∫ ω, Q2 ω ∂inst.μ =
          (61 : ℝ) / 86400 * r * ∫ ω, ∑ j : Fin count, N j ω ∂inst.μ := by
        rw [hpartition_integral]
      _ = (61 : ℝ) / 86400 * r *
          (∑ j : Fin count, ∫ ω, N j ω ∂inst.μ) := by
        rw [MeasureTheory.integral_finsetSum]
        intro j _
        exact hN_integrable j
      _ = ∑ j : Fin count,
          (61 : ℝ) / 86400 * r * ∫ ω, N j ω ∂inst.μ := by
        rw [Finset.mul_sum]
      _ ≤ ∑ j : Fin count, ∫ ω, |B j ω| ∂inst.μ := hsum
      _ = ∫ ω, ∑ j : Fin count, |B j ω| ∂inst.μ := by
        symm
        apply MeasureTheory.integral_finsetSum
        intro j _
        simpa only [Real.norm_eq_abs] using (hB_integrable j).norm
  have hmiddle :
      (61 : ℝ) / 86400 * r * ∫ ω, Q2 ω ∂inst.μ ≤ ∫ ω,
        group_error inst.T (fun t => hard_context inst.m t.val)
          (fun t => inst.p t ω) (fun t => inst.y t ω)
          (hard_group_family η 2) ∂inst.μ := by
    exact hmiddle_cells.trans (MeasureTheory.integral_mono hsumB_integrable
      hG2_integrable hmiddle_point)
  have hnear_indicator (t : Fin inst.T) (ω : inst.Ω) :
      near t ω =
        if |inst.p t ω - hard_context inst.m t.val| < η then 1 else 0 := by
    rcases hnear_binary t ω with h | h
    · have hn : ¬|inst.p t ω - hard_context inst.m t.val| < η := by
        intro hlt
        have hone := (hnear_spec t ω).2 hlt
        rw [h] at hone
        norm_num at hone
      simp [h, hn]
    · have hn := (hnear_spec t ω).1 h
      simp [h, hn]
  have hfar_indicator (t : Fin inst.T) (ω : inst.Ω) :
      q0 t ω + q1 t ω =
        if η ≤ |inst.p t ω - hard_context inst.m t.val| then 1 else 0 := by
    have hpart := hard_group_family_partition η heta_pos
      (hard_context inst.m t.val) (inst.p t ω)
    rw [hg0, hg1, hg2] at hpart
    by_cases hf : η ≤ |inst.p t ω - hard_context inst.m t.val|
    · have hn : near t ω = 0 := by
        rcases hnear_binary t ω with h | h
        · exact h
        · exact False.elim ((not_lt_of_ge hf) ((hnear_spec t ω).1 h))
      simp [hf, hn] at hpart ⊢
      exact hpart
    · have hlt : |inst.p t ω - hard_context inst.m t.val| < η := lt_of_not_ge hf
      have hn : near t ω = 1 := (hnear_spec t ω).2 hlt
      simp [hf, hn] at hpart ⊢
      linarith
  have hQ0Q1 (ω : inst.Ω) : Q0 ω + Q1 ω =
      ∑ t : Fin inst.T,
        if η ≤ |inst.p t ω - hard_context inst.m t.val| then (1 : ℝ) else 0 := by
    dsimp [Q0, Q1]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    exact hfar_indicator t ω
  have hQ2 (ω : inst.Ω) : Q2 ω =
      ∑ t : Fin inst.T,
        if |inst.p t ω - hard_context inst.m t.val| < η then (1 : ℝ) else 0 := by
    dsimp [Q2]
    apply Finset.sum_congr rfl
    intro t _
    exact hnear_indicator t ω
  have hQ0_nonneg (ω : inst.Ω) : 0 ≤ Q0 ω := by
    dsimp [Q0]
    apply Finset.sum_nonneg
    intro t _
    rcases hq0_binary t ω with h | h <;> simp [h]
  have hQ1_nonneg (ω : inst.Ω) : 0 ≤ Q1 ω := by
    dsimp [Q1]
    apply Finset.sum_nonneg
    intro t _
    rcases hq1_binary t ω with h | h <;> simp [h]
  have hQ2_nonneg (ω : inst.Ω) : 0 ≤ Q2 ω := by
    dsimp [Q2]
    exact Finset.sum_nonneg fun t _ => hnear_nonneg t ω
  have hIQ0 : 0 ≤ ∫ ω, Q0 ω ∂inst.μ := MeasureTheory.integral_nonneg hQ0_nonneg
  have hIQ1 : 0 ≤ ∫ ω, Q1 ω ∂inst.μ := MeasureTheory.integral_nonneg hQ1_nonneg
  have hIQ2 : 0 ≤ ∫ ω, Q2 ω ∂inst.μ := MeasureTheory.integral_nonneg hQ2_nonneg
  have hGsum :
      (61 : ℝ) / 86400 *
          (η * (∫ ω, Q0 ω ∂inst.μ + ∫ ω, Q1 ω ∂inst.μ) +
            r * ∫ ω, Q2 ω ∂inst.μ) ≤
        ∫ ω,
          group_error inst.T (fun t => hard_context inst.m t.val)
              (fun t => inst.p t ω) (fun t => inst.y t ω)
              (hard_group_family η 0) +
            group_error inst.T (fun t => hard_context inst.m t.val)
              (fun t => inst.p t ω) (fun t => inst.y t ω)
              (hard_group_family η 1) +
            group_error inst.T (fun t => hard_context inst.m t.val)
              (fun t => inst.p t ω) (fun t => inst.y t ω)
              (hard_group_family η 2) ∂inst.μ := by
    have hsep :
        ∫ ω,
            group_error inst.T (fun t => hard_context inst.m t.val)
                (fun t => inst.p t ω) (fun t => inst.y t ω)
                (hard_group_family η 0) +
              group_error inst.T (fun t => hard_context inst.m t.val)
                (fun t => inst.p t ω) (fun t => inst.y t ω)
                (hard_group_family η 1) +
              group_error inst.T (fun t => hard_context inst.m t.val)
                (fun t => inst.p t ω) (fun t => inst.y t ω)
                (hard_group_family η 2) ∂inst.μ =
          (∫ ω, group_error inst.T (fun t => hard_context inst.m t.val)
              (fun t => inst.p t ω) (fun t => inst.y t ω)
              (hard_group_family η 0) ∂inst.μ) +
          (∫ ω, group_error inst.T (fun t => hard_context inst.m t.val)
              (fun t => inst.p t ω) (fun t => inst.y t ω)
              (hard_group_family η 1) ∂inst.μ) +
          ∫ ω, group_error inst.T (fun t => hard_context inst.m t.val)
              (fun t => inst.p t ω) (fun t => inst.y t ω)
              (hard_group_family η 2) ∂inst.μ := by
      calc
        ∫ ω,
              group_error inst.T (fun t => hard_context inst.m t.val)
                  (fun t => inst.p t ω) (fun t => inst.y t ω)
                  (hard_group_family η 0) +
                group_error inst.T (fun t => hard_context inst.m t.val)
                  (fun t => inst.p t ω) (fun t => inst.y t ω)
                  (hard_group_family η 1) +
                group_error inst.T (fun t => hard_context inst.m t.val)
                  (fun t => inst.p t ω) (fun t => inst.y t ω)
                  (hard_group_family η 2) ∂inst.μ =
            (∫ ω,
                group_error inst.T (fun t => hard_context inst.m t.val)
                    (fun t => inst.p t ω) (fun t => inst.y t ω)
                    (hard_group_family η 0) +
                  group_error inst.T (fun t => hard_context inst.m t.val)
                    (fun t => inst.p t ω) (fun t => inst.y t ω)
                    (hard_group_family η 1) ∂inst.μ) +
              ∫ ω, group_error inst.T (fun t => hard_context inst.m t.val)
                  (fun t => inst.p t ω) (fun t => inst.y t ω)
                  (hard_group_family η 2) ∂inst.μ := by
          simpa only [Pi.add_apply] using
            MeasureTheory.integral_add (hG0_integrable.add hG1_integrable)
              hG2_integrable
        _ = (∫ ω, group_error inst.T (fun t => hard_context inst.m t.val)
                (fun t => inst.p t ω) (fun t => inst.y t ω)
                (hard_group_family η 0) ∂inst.μ) +
              (∫ ω, group_error inst.T (fun t => hard_context inst.m t.val)
                (fun t => inst.p t ω) (fun t => inst.y t ω)
                (hard_group_family η 1) ∂inst.μ) +
              ∫ ω, group_error inst.T (fun t => hard_context inst.m t.val)
                (fun t => inst.p t ω) (fun t => inst.y t ω)
                (hard_group_family η 2) ∂inst.μ := by
          rw [MeasureTheory.integral_add hG0_integrable hG1_integrable]
    rw [hsep]
    have hk0 : (0 : ℝ) ≤ 61 / 86400 := by norm_num
    have hk1 : (61 : ℝ) / 86400 ≤ 1 := by norm_num
    nlinarith [htail0, htail1, hmiddle,
      mul_nonneg heta_pos.le hIQ0, mul_nonneg heta_pos.le hIQ1]
  change ∫ ω,
      group_error inst.T (fun t => hard_context inst.m t.val)
          (fun t => inst.p t ω) (fun t => inst.y t ω)
          (hard_group_family η 0) +
        group_error inst.T (fun t => hard_context inst.m t.val)
          (fun t => inst.p t ω) (fun t => inst.y t ω)
          (hard_group_family η 1) +
        group_error inst.T (fun t => hard_context inst.m t.val)
          (fun t => inst.p t ω) (fun t => inst.y t ω)
          (hard_group_family η 2) ∂inst.μ ≥
    (61 : ℝ) / 86400 * ∫ ω,
      η * ∑ t : Fin inst.T,
          (if η ≤ |inst.p t ω - hard_context inst.m t.val| then (1 : ℝ) else 0) +
        r * ∑ t : Fin inst.T,
          (if |inst.p t ω - hard_context inst.m t.val| < η then (1 : ℝ) else 0) ∂inst.μ
  calc
    (61 : ℝ) / 86400 * ∫ ω,
        η * ∑ t : Fin inst.T,
            (if η ≤ |inst.p t ω - hard_context inst.m t.val| then (1 : ℝ) else 0) +
          r * ∑ t : Fin inst.T,
            (if |inst.p t ω - hard_context inst.m t.val| < η then (1 : ℝ) else 0) ∂inst.μ =
        (61 : ℝ) / 86400 *
          (η * (∫ ω, Q0 ω ∂inst.μ + ∫ ω, Q1 ω ∂inst.μ) +
            r * ∫ ω, Q2 ω ∂inst.μ) := by
      congr 1
      rw [← MeasureTheory.integral_add hQ0_integrable hQ1_integrable,
        ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
        ← MeasureTheory.integral_add]
      · apply MeasureTheory.integral_congr_ae
        filter_upwards with ω
        rw [← hQ0Q1 ω, ← hQ2 ω]
      · exact (hQ0_integrable.add hQ1_integrable).const_mul η
      · exact hQ2_integrable.const_mul r
    _ ≤ ∫ ω,
        group_error inst.T (fun t => hard_context inst.m t.val)
            (fun t => inst.p t ω) (fun t => inst.y t ω)
            (hard_group_family η 0) +
          group_error inst.T (fun t => hard_context inst.m t.val)
            (fun t => inst.p t ω) (fun t => inst.y t ω)
            (hard_group_family η 1) +
          group_error inst.T (fun t => hard_context inst.m t.val)
            (fun t => inst.p t ω) (fun t => inst.y t ω)
            (hard_group_family η 2) ∂inst.μ := hGsum

@[blueprint "lem:predictable-cell-moment-lower-bound"
  (statement := /-- There exist a universal constant $\kappa>0$ and a threshold
  $T_{\mathrm{mom}}\in\mathbb N$ such that every online multicalibration hard instance $I$
  \cref{def:online-mc-hard-instance} with $T\ge T_{\mathrm{mom}}$ satisfies
  \[
    \mathbb E_\mu\!\left[\sum_{i=0}^{2}\mathrm{Err}_T(g_i)\right]
      \ge \kappa\,\mathcal Q(I),
  \]
  where the left-hand side is \cref{def:expected-sum-group-error} and
  $\mathcal Q(I)$ is the stopping-stable spread--drift score
  \cref{def:spread-drift-score}. -/)
  (proof := /-- Take $\kappa=61/86400$ and $T_{\mathrm{mom}}=10^6$; the former is strictly
  positive. For every online multicalibration hard instance whose horizon is at least
  $T_{\mathrm{mom}}$, the fixed-instance estimate
  \cref{lem:predictable-cell-instance-bound} gives
  $\mathbb E_\mu[\sum_{i=0}^{2}\mathrm{Err}_T(g_i)]
    \ge (61/86400)\mathcal Q(I)$, which is the required inequality. -/)
  (title := /-- Moment interpolation for predictably allocated Bernoulli increments -/)
  (latexEnv := "lemma")]
lemma predictable_cell_moment_lower_bound :
    ∃ κ : ℝ, 0 < κ ∧ ∃ T₀ : ℕ, ∀ inst : online_mc_hard_instance, T₀ ≤ inst.T →
      expected_sum_group_error inst ≥ κ * spread_drift_score inst := by
  classical
  refine ⟨(61 : ℝ) / 86400, by norm_num, 1000000, ?_⟩
  intro inst hT
  exact predictable_cell_instance_bound inst hT

@[blueprint "lem:spread-drift-score-ge-sqrt-mt"
  (statement := /-- There exist a universal constant $c_{\mathcal Q}>0$ and a threshold
  $T_{\mathcal Q}\in\mathbb N$ such that every online multicalibration hard instance $I$
  \cref{def:online-mc-hard-instance} with $T\ge T_{\mathcal Q}$ satisfies
  \[
    \mathcal Q(I)\ge c_{\mathcal Q}\sqrt{mT},
  \]
  where $\mathcal Q$ is \cref{def:spread-drift-score}. -/)
  (proof := /-- Take $c_{\mathcal Q}=\delta_\ast=1/100$ and $T_{\mathcal Q}=0$, where
  $\delta_\ast$ is the fixed constant in \cref{def:hard-construction-constant}. Fix an instance
  $I$ as in \cref{def:online-mc-hard-instance}. The adaptedness of each prediction, the inclusion of
  the algorithmic sigma-algebra in the ambient sigma-algebra, and the measurability of every label
  imply that each prediction $p^t$ is ambient-measurable. Consequently the two threshold indicators
  in \cref{def:spread-drift-score} are measurable and bounded, hence integrable because $\mu$ is a
  probability measure.

  Put $r=\sqrt{m/T}$ and $\eta=\delta_\ast r$ as in \cref{def:hard-threshold}, and fix an outcome
  $\omega$. If $D$ is the number of indices satisfying
  $\eta\leq\lvert p^t(\omega)-x^t\rvert$ and $N$ is the number satisfying the complementary strict
  inequality, then trichotomy gives $D+N=T$. Since $r,D,N\geq0$ and
  $0<\delta_\ast\leq1$,
  \[
    \eta D+rN
      =r(\delta_\ast D+N)
      \ge\delta_\ast r(D+N)
      =\delta_\ast\sqrt{mT},
  \]
  where the last equality follows from
  $\sqrt{m/T}\,T=(\sqrt m/\sqrt T)T=\sqrt m\sqrt T=\sqrt{mT}$.
  Monotonicity of the integral now bounds the score in \cref{def:spread-drift-score} below by the
  integral of the constant $\delta_\ast\sqrt{mT}$. Since $\mu$ is a probability measure, that
  integral equals $\delta_\ast\sqrt{mT}$, which proves the claim for the stated constant and
  threshold. -/)
  (title := /-- Deterministic lower bound for the spread--drift score -/)
  (latexEnv := "lemma")]
lemma spread_drift_score_ge_sqrt_mt :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ inst : online_mc_hard_instance, T₀ ≤ inst.T →
      spread_drift_score inst ≥ c * Real.sqrt ((inst.m : ℝ) * (inst.T : ℝ)) := by
  refine ⟨hard_construction_constant, by norm_num [hard_construction_constant], 0, ?_⟩
  intro inst _
  letI := inst.mΩ
  letI := inst.isProb
  let η := hard_threshold hard_construction_constant inst.m inst.T
  let r := Real.sqrt ((inst.m : ℝ) / (inst.T : ℝ))
  have hp (t : Fin inst.T) : Measurable (inst.p t) := by
    exact (inst.p_adapted t).mono
      (sup_le inst.alg_le (iSup_le fun s => iSup_le fun _ => (inst.y_meas s).comap_le)) le_rfl
  have hfar_integrable (t : Fin inst.T) :
      MeasureTheory.Integrable
        (fun ω => if η ≤ |inst.p t ω - hard_context inst.m t.val| then (1 : ℝ) else 0)
        inst.μ := by
    have hdist : Measurable
        (fun ω => |inst.p t ω - hard_context inst.m t.val|) := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using ((hp t).sub measurable_const).norm
    apply MeasureTheory.Integrable.of_bound
      (Measurable.ite (measurableSet_le measurable_const hdist) measurable_const
        measurable_const).aestronglyMeasurable 1
    filter_upwards with ω
    split_ifs <;> norm_num
  have hnear_integrable (t : Fin inst.T) :
      MeasureTheory.Integrable
        (fun ω => if |inst.p t ω - hard_context inst.m t.val| < η then (1 : ℝ) else 0)
        inst.μ := by
    have hdist : Measurable
        (fun ω => |inst.p t ω - hard_context inst.m t.val|) := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using ((hp t).sub measurable_const).norm
    apply MeasureTheory.Integrable.of_bound
      (Measurable.ite (measurableSet_lt hdist measurable_const) measurable_const
        measurable_const).aestronglyMeasurable 1
    filter_upwards with ω
    split_ifs <;> norm_num
  have hscore_integrable :
      MeasureTheory.Integrable
        (fun ω => (η * ∑ t : Fin inst.T,
          if η ≤ |inst.p t ω - hard_context inst.m t.val| then (1 : ℝ) else 0) +
        r * ∑ t : Fin inst.T,
          if |inst.p t ω - hard_context inst.m t.val| < η then (1 : ℝ) else 0)
        inst.μ := by
    apply MeasureTheory.Integrable.add
    · apply MeasureTheory.Integrable.const_mul
      simpa using
        (MeasureTheory.integrable_finsetSum Finset.univ
          (fun t _ => hfar_integrable t))
    · apply MeasureTheory.Integrable.const_mul
      simpa using
        (MeasureTheory.integrable_finsetSum Finset.univ
          (fun t _ => hnear_integrable t))
  have hconst_integrable :
      MeasureTheory.Integrable
        (fun _ : inst.Ω =>
          hard_construction_constant * Real.sqrt ((inst.m : ℝ) * (inst.T : ℝ))) inst.μ :=
    MeasureTheory.integrable_const _
  calc
    spread_drift_score inst =
        ∫ ω, (η * ∑ t : Fin inst.T,
          if η ≤ |inst.p t ω - hard_context inst.m t.val| then (1 : ℝ) else 0) +
        r * ∑ t : Fin inst.T,
          if |inst.p t ω - hard_context inst.m t.val| < η then (1 : ℝ) else 0 ∂inst.μ := by
      rfl
    _ ≥ ∫ _ : inst.Ω,
        hard_construction_constant * Real.sqrt ((inst.m : ℝ) * (inst.T : ℝ)) ∂inst.μ := by
      apply MeasureTheory.integral_mono hconst_integrable hscore_integrable
      intro ω
      let D : ℝ := ∑ t : Fin inst.T,
        if η ≤ |inst.p t ω - hard_context inst.m t.val| then (1 : ℝ) else 0
      let N : ℝ := ∑ t : Fin inst.T,
        if |inst.p t ω - hard_context inst.m t.val| < η then (1 : ℝ) else 0
      change hard_construction_constant * Real.sqrt ((inst.m : ℝ) * (inst.T : ℝ)) ≤
        η * D + r * N
      have hpartition :
          D + N = (inst.T : ℝ) := by
        dsimp [D, N]
        rw [← Finset.sum_add_distrib]
        calc
          (∑ t : Fin inst.T,
              ((if η ≤ |inst.p t ω - hard_context inst.m t.val| then (1 : ℝ) else 0) +
              (if |inst.p t ω - hard_context inst.m t.val| < η then (1 : ℝ) else 0))) =
              ∑ _t : Fin inst.T, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro t ht
            by_cases h : η ≤ |inst.p t ω - hard_context inst.m t.val|
            · simp [h, not_lt_of_ge h]
            · have h' : |inst.p t ω - hard_context inst.m t.val| < η := lt_of_not_ge h
              simp [h, h']
          _ = (inst.T : ℝ) := by simp
      have hfar_nonneg : 0 ≤ D := by
        dsimp [D]
        positivity
      have hnear_nonneg : 0 ≤ N := by
        dsimp [N]
        positivity
      have hr : 0 ≤ r := Real.sqrt_nonneg _
      have heta : η = hard_construction_constant * r := by
        rfl
      have hsqrt :
          r * (inst.T : ℝ) = Real.sqrt ((inst.m : ℝ) * (inst.T : ℝ)) := by
        dsimp [r]
        rw [Real.sqrt_div (by positivity)]
        calc
          Real.sqrt (inst.m : ℝ) / Real.sqrt (inst.T : ℝ) * (inst.T : ℝ) =
              Real.sqrt (inst.m : ℝ) *
                ((inst.T : ℝ) / Real.sqrt (inst.T : ℝ)) := by ring
          _ = Real.sqrt (inst.m : ℝ) * Real.sqrt (inst.T : ℝ) := by
            rw [Real.div_sqrt]
          _ = Real.sqrt ((inst.m : ℝ) * (inst.T : ℝ)) := by
            rw [Real.sqrt_mul (by positivity)]
      have hc : hard_construction_constant ≤ 1 := by
        norm_num [hard_construction_constant]
      have hc0 : 0 ≤ hard_construction_constant := by
        norm_num [hard_construction_constant]
      have hgap : 0 ≤ (r * N) * (1 - hard_construction_constant) :=
        mul_nonneg (mul_nonneg hr hnear_nonneg) (sub_nonneg.mpr hc)
      nth_rewrite 1 [heta]
      rw [← hsqrt]
      calc
        hard_construction_constant * (r * (inst.T : ℝ)) =
            hard_construction_constant * r * (D + N) := by
          rw [hpartition]
          ring
        _ = hard_construction_constant * r * D +
            hard_construction_constant * r * N := by ring
        _ ≤ hard_construction_constant * r * D + r * N := by
          nlinarith [hgap]
    _ = hard_construction_constant *
        Real.sqrt ((inst.m : ℝ) * (inst.T : ℝ)) := by simp

@[blueprint "lem:adaptive-cell-anti-concentration"
  (statement := /-- There exist a universal constant $c_{\mathrm{ac}}>0$ and a threshold
  $T_{\mathrm{ac}}\in\mathbb{N}$ such that every online multicalibration hard instance
  $I$ \cref{def:online-mc-hard-instance} with horizon $T\ge T_{\mathrm{ac}}$ and grid size $m$
  satisfying $2\le m$ and $m^3\le T<(m+1)^3$ obeys
  \[
    \mathbb{E}_{\mathcal{D}_{T,m}}\!\left[\sum_{i=0}^{2}\mathrm{Err}_T(g_i)\right]
      \ge c_{\mathrm{ac}}\sqrt{mT},
  \]
  where the expectation is \cref{def:expected-sum-group-error}. The constants are uniform over the
  probability space, the independent Bernoulli labels with means given by the hard contexts
  \cref{def:hard-context}, the algorithmic randomness independent of all labels, and every
  $[0,1]$-valued prediction process measurable with respect to the algorithmic randomness and the
  labels revealed strictly before the current round, as required in
  \cref{def:online-mc-hard-instance}. -/)
  (proof := /-- The predictable-cell moment bound
  \cref{lem:predictable-cell-moment-lower-bound} supplies constants $\kappa>0$ and
  $T_{\mathrm{mom}}$ for which
  \[
    \mathbb E_\mu\sum_{i=0}^{2}\mathrm{Err}_T(g_i)\ge\kappa\mathcal Q(I)
  \]
  whenever $T\ge T_{\mathrm{mom}}$. The deterministic score estimate
  \cref{lem:spread-drift-score-ge-sqrt-mt} supplies $c_{\mathcal Q}>0$ and $T_{\mathcal Q}$ for
  which $\mathcal Q(I)\ge c_{\mathcal Q}\sqrt{mT}$. For
  $T\ge\max\{T_{\mathrm{mom}},T_{\mathcal Q}\}$, multiplication by $\kappa>0$ and transitivity give
  \[
    \mathbb E_\mu\sum_{i=0}^{2}\mathrm{Err}_T(g_i)
      \ge\kappa c_{\mathcal Q}\sqrt{mT}.
  \]
  The product $\kappa c_{\mathcal Q}$ is positive, so it and the maximum threshold are the required
  universal constants. -/)
  (title := /-- Stopping-stable adaptive anti-concentration -/)
  (latexEnv := "lemma")]
lemma adaptive_cell_anti_concentration :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ inst : online_mc_hard_instance, T₀ ≤ inst.T →
      expected_sum_group_error inst ≥ c * Real.sqrt ((inst.m : ℝ) * (inst.T : ℝ)) := by
  obtain ⟨κ, hκ, Tmom, hmom⟩ := predictable_cell_moment_lower_bound
  obtain ⟨cQ, hcQ, TQ, hQ⟩ := spread_drift_score_ge_sqrt_mt
  refine ⟨κ * cQ, mul_pos hκ hcQ, max Tmom TQ, ?_⟩
  intro inst hT
  have hTmom : Tmom ≤ inst.T := le_trans (Nat.le_max_left Tmom TQ) hT
  have hTQ : TQ ≤ inst.T := le_trans (Nat.le_max_right Tmom TQ) hT
  calc
    expected_sum_group_error inst ≥ κ * spread_drift_score inst := hmom inst hTmom
    _ ≥ κ * (cQ * Real.sqrt ((inst.m : ℝ) * (inst.T : ℝ))) :=
      mul_le_mul_of_nonneg_left (hQ inst hTQ) (le_of_lt hκ)
    _ = (κ * cQ) * Real.sqrt ((inst.m : ℝ) * (inst.T : ℝ)) := by ring

@[blueprint "lem:expected-sum-group-error-ge-sqrt-mt"
  (statement := /-- There exist a constant $c>0$ and a threshold $T_0\in\mathbb{N}$ such that every
  online multicalibration hard instance $I$ \cref{def:online-mc-hard-instance} with horizon
  $T\ge T_0$ and grid size $m$ satisfying $2\le m$ and $m^3\le T<(m+1)^3$ obeys
  \[
    \mathbb{E}_{\mathcal{D}_{T,m}}\!\left[\sum_{i=0}^{2}\mathrm{Err}_T(g_i)\right]
      \ge c\sqrt{mT},
  \]
  where the expected summed group error is defined in \cref{def:expected-sum-group-error} using the
  hard group family with the fixed construction constant $\delta_{\ast}$
  \cref{def:hard-construction-constant}. The constants $c$ and $T_0$ are independent of $I$, hence
  uniform over all probability spaces, admissible label families, independent algorithmic randomness,
  and online adapted prediction processes packaged by \cref{def:online-mc-hard-instance}. -/)
  (proof := /-- Apply the stopping-stable adaptive anti-concentration theorem
  \cref{lem:adaptive-cell-anti-concentration}. It supplies universal constants
  $c_{\mathrm{ac}}>0$ and $T_{\mathrm{ac}}\in\mathbb N$ such that every hard instance with
  $T\ge T_{\mathrm{ac}}$ satisfies
  \[
    \mathbb E_{\mathcal D_{T,m}}\sum_{i=0}^{2}\mathrm{Err}_T(g_i)
      \ge c_{\mathrm{ac}}\sqrt{mT}.
  \]
  Taking $c=c_{\mathrm{ac}}$ and $T_0=T_{\mathrm{ac}}$ proves the assertion. -/)
  (title := /-- Anti-concentration lower bound on the expected summed group error -/)
  (latexEnv := "lemma")]
lemma expected_sum_group_error_ge_sqrt_mt :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ inst : online_mc_hard_instance, T₀ ≤ inst.T →
      expected_sum_group_error inst ≥ c * Real.sqrt ((inst.m : ℝ) * (inst.T : ℝ)) := by
  exact adaptive_cell_anti_concentration

@[blueprint "lem:expected-mc-error-ge-third-sum"
  (statement := /-- For every online multicalibration hard instance $I$, the expected
  multicalibration error is at least one third of the expected sum of the three hard-group errors:
  $\mathbb{E}[\mathrm{MCerr}_T(G)]\ge \frac13\mathbb{E}[\sum_{i=0}^2\mathrm{Err}_T(g_i)]$. -/)
  (proof := /-- For each of the three hard groups, its indicator is measurable and binary. Since the
  predictions lie in $[0,1]$ and the labels are binary, every weighted residual has absolute value at
  most one. The finite prediction-cell integrability result
  \cref{lem:finite-prediction-cell-l1-integrable} therefore makes each group-error random variable
  integrable, and hence also their finite maximum and their average. Pointwise,
  \cref{lem:mc-error-ge-avg-groups} bounds that maximum below by the average. Monotonicity of the
  integral gives the asserted expectation inequality. -/)
  (title := /-- Expected multicalibration error dominates the expected group-error average -/)
  (latexEnv := "lemma")]
lemma expected_mc_error_ge_third_sum (inst : online_mc_hard_instance) :
    expected_mc_error inst ≥ expected_sum_group_error inst / 3 := by
  classical
  letI := inst.mΩ
  letI := inst.isProb
  let η := hard_threshold hard_construction_constant inst.m inst.T
  have hp_meas (t : Fin inst.T) : Measurable (inst.p t) := by
    exact (inst.p_adapted t).mono
      (sup_le inst.alg_le
        (iSup_le fun s => iSup_le fun _ => (inst.y_meas s).comap_le)) le_rfl
  have hpy_bound (t : Fin inst.T) (ω : inst.Ω) :
      ‖inst.p t ω - inst.y t ω‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    rcases inst.y_binary t ω with hy | hy
    · rw [hy, sub_zero, abs_of_nonneg] <;> linarith [(inst.p_range t ω).1,
        (inst.p_range t ω).2]
    · rw [hy, abs_of_nonpos] <;> linarith [(inst.p_range t ω).1,
        (inst.p_range t ω).2]
  have hgroup_meas (i : Fin 3) (t : Fin inst.T) : Measurable (fun ω =>
      hard_group_family η i (hard_context inst.m t.val) (inst.p t ω)) := by
    fin_cases i
    · simpa [hard_group_family] using Measurable.ite
        (measurableSet_le measurable_const (hp_meas t)) measurable_const measurable_const
    · simpa [hard_group_family] using Measurable.ite
        (measurableSet_le (hp_meas t) measurable_const) measurable_const measurable_const
    · simpa [hard_group_family] using Measurable.ite
        (measurableSet_lt ((hp_meas t).sub measurable_const).norm measurable_const)
        measurable_const measurable_const
  have hgroup_binary (i : Fin 3) (t : Fin inst.T) (ω : inst.Ω) :
      hard_group_family η i (hard_context inst.m t.val) (inst.p t ω) = 0 ∨
        hard_group_family η i (hard_context inst.m t.val) (inst.p t ω) = 1 := by
    fin_cases i <;> simp only [hard_group_family] <;> split_ifs <;> simp
  let a (i : Fin 3) (t : Fin inst.T) (ω : inst.Ω) :=
    hard_group_family η i (hard_context inst.m t.val) (inst.p t ω) *
      (inst.p t ω - inst.y t ω)
  have ha_meas (i : Fin 3) (t : Fin inst.T) : Measurable (a i t) := by
    exact (hgroup_meas i t).mul ((hp_meas t).sub (inst.y_meas t))
  have ha_bound (i : Fin 3) (t : Fin inst.T) (ω : inst.Ω) : ‖a i t ω‖ ≤ 1 := by
    dsimp [a]
    rw [abs_mul]
    rcases hgroup_binary i t ω with h | h <;> rw [h]
    · simp
    · simpa using hpy_bound t ω
  have hgroup_integrable (i : Fin 3) : MeasureTheory.Integrable (fun ω =>
      group_error inst.T (fun t => hard_context inst.m t.val)
        (fun t => inst.p t ω) (fun t => inst.y t ω)
        (hard_group_family η i)) inst.μ := by
    have hraw := finite_prediction_cell_l1_integrable inst.μ inst.T
      (fun t => inst.p t) (a i) hp_meas (ha_meas i) (ha_bound i)
    simpa [group_error, prediction_values, empirical_bias, a] using hraw
  have hmc_integrable : MeasureTheory.Integrable (fun ω =>
      multicalibration_error inst.T (fun t => hard_context inst.m t.val)
        (fun t => inst.p t ω) (fun t => inst.y t ω)
        (hard_group_family η)) inst.μ := by
    apply ((hgroup_integrable 0).sup
      ((hgroup_integrable 1).sup (hgroup_integrable 2))).congr
    filter_upwards with ω
    simp [multicalibration_error,
      show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} from rfl]
  have havg_integrable : MeasureTheory.Integrable (fun ω =>
      (group_error inst.T (fun t => hard_context inst.m t.val)
          (fun t => inst.p t ω) (fun t => inst.y t ω) (hard_group_family η 0) +
        group_error inst.T (fun t => hard_context inst.m t.val)
          (fun t => inst.p t ω) (fun t => inst.y t ω) (hard_group_family η 1) +
        group_error inst.T (fun t => hard_context inst.m t.val)
          (fun t => inst.p t ω) (fun t => inst.y t ω) (hard_group_family η 2)) / 3) inst.μ := by
    simpa [div_eq_mul_inv, mul_comm] using
      (((hgroup_integrable 0).add (hgroup_integrable 1)).add
        (hgroup_integrable 2)).const_mul (3 : ℝ)⁻¹
  rw [expected_mc_error, expected_sum_group_error, ← MeasureTheory.integral_div]
  exact MeasureTheory.integral_mono havg_integrable hmc_integrable fun ω =>
    mc_error_ge_avg_groups inst.T (fun t => hard_context inst.m t.val)
      (fun t => inst.p t ω) (fun t => inst.y t ω) (hard_group_family η)

@[blueprint "lem:expected-mc-error-ge-sqrt-mt"
  (statement := /-- There exist a universal constant $c>0$ and a threshold $T_0\in\mathbb{N}$ such
  that every online multicalibration hard instance $I$ \cref{def:online-mc-hard-instance} with horizon
  $T\ge T_0$ and grid size $m$ satisfying $2\le m$ and $m^3\le T<(m+1)^3$ obeys
  $\mathbb{E}_{\mathcal{D}_{T,m}}[\mathrm{MCerr}_T(G)]\ge c\sqrt{mT}$. Here the hard group family uses
  the fixed construction constant $\delta_{\ast}$ \cref{def:hard-construction-constant}, and the
  expectation is the expected multicalibration error \cref{def:expected-mc-error}. -/)
  (proof := /-- Apply \cref{lem:expected-sum-group-error-ge-sqrt-mt} to obtain constants $c_1>0$ and
  $T_0\in\mathbb{N}$ such that every instance with horizon $T\ge T_0$ has expected summed group error
  at least $c_1\sqrt{mT}$. For any such instance,
  \cref{lem:expected-mc-error-ge-third-sum} bounds its expected multicalibration error below by one
  third of that expected sum. Consequently
  $\mathbb{E}_{\mathcal{D}_{T,m}}[\mathrm{MCerr}_T(G)]\ge(c_1/3)\sqrt{mT}$.
  Taking $c=c_1/3>0$ proves the assertion. -/)
  (title := /-- Core lower bound on the expected multicalibration error -/)
  (latexEnv := "lemma")]
lemma expected_mc_error_ge_sqrt_mt :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ inst : online_mc_hard_instance, T₀ ≤ inst.T →
      expected_mc_error inst ≥ c * Real.sqrt ((inst.m : ℝ) * (inst.T : ℝ)) := by
  obtain ⟨c, hc, T₀, hsum⟩ := expected_sum_group_error_ge_sqrt_mt
  refine ⟨c / 3, div_pos hc (by norm_num), T₀, ?_⟩
  intro inst hT
  calc
    expected_mc_error inst ≥ expected_sum_group_error inst / 3 :=
      expected_mc_error_ge_third_sum inst
    _ ≥ (c * Real.sqrt ((inst.m : ℝ) * (inst.T : ℝ))) / 3 := by
      exact div_le_div_of_nonneg_right (hsum inst hT) (by norm_num)
    _ = (c / 3) * Real.sqrt ((inst.m : ℝ) * (inst.T : ℝ)) := by ring

@[blueprint "lem:sqrt-mt-ge-pow"
  (statement := /-- There exist a constant $c'>0$ and a threshold $T_0\in\mathbb{N}$ such that for all
  $m,T\in\mathbb{N}$ satisfying $m\ge 1$, $m^3\le T<(m+1)^3$, and $T\ge T_0$, one has
  $\sqrt{mT}\ge c'\,T^{2/3}$. -/)
  (proof := /-- We prove the statement with $c'=\sqrt2/2=1/\sqrt2>0$ and $T_0=8$. Fix $m,T\in\mathbb{N}$
  with $m\ge 1$, $m^3\le T<(m+1)^3$ and $8\le T$, and set $s=T^{1/3}\ge 0$; then $s^3=T$ and
  $s^2=T^{2/3}$, both by writing $s=T^{1/3}$ as a real power and combining exponents. Since $m\ge 1$ we
  have $(m+1)^3\le(2m)^3=8m^3$, so from $T<(m+1)^3$ we obtain $T\le 8m^3$, that is $s^3\le(2m)^3$;
  because the cube is monotone on the nonnegative reals this gives $s\le 2m$, equivalently
  $m\ge s/2$. Therefore $mT=m\,s^3\ge\tfrac12 s\cdot s^3=\tfrac12 s^4$. Taking square roots, a monotone
  operation on the nonnegative reals, yields
  $\sqrt{mT}\ge\sqrt{\tfrac12 s^4}=\tfrac{1}{\sqrt2}\,s^2=\tfrac{\sqrt2}{2}\,T^{2/3}$, which is the
  asserted bound. -/)
  (title := /-- Square-root grid bound in terms of the horizon rate -/)
  (latexEnv := "lemma")]
lemma sqrt_mt_ge_pow :
    ∃ c' : ℝ, 0 < c' ∧ ∃ T₀ : ℕ, ∀ m T : ℕ, 1 ≤ m → m ^ 3 ≤ T → T < (m + 1) ^ 3 → T₀ ≤ T →
      Real.sqrt ((m : ℝ) * (T : ℝ)) ≥ c' * (T : ℝ) ^ ((2 : ℝ) / 3) := by
  refine ⟨Real.sqrt 2 / 2, by positivity, 8, ?_⟩
  intro m T hm h1 h2 h3
  set s : ℝ := (T : ℝ) ^ ((1 : ℝ) / 3) with hs
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := by positivity
  have hs0 : 0 ≤ s := Real.rpow_nonneg hT0 _
  have hs3 : s ^ 3 = (T : ℝ) := by
    rw [hs, ← Real.rpow_natCast ((T : ℝ) ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hT0]
    norm_num
  have hs2 : s ^ 2 = (T : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [hs, ← Real.rpow_natCast ((T : ℝ) ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul hT0]
    norm_num
  have hTle : (T : ℝ) ≤ 8 * (m : ℝ) ^ 3 := by
    have h2' : (T : ℝ) < ((m : ℝ) + 1) ^ 3 := by exact_mod_cast h2
    have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith [h2', hm', mul_nonneg (sub_nonneg.mpr hm') (sub_nonneg.mpr hm'), sq_nonneg ((m : ℝ) - 1)]
  have hs_le : s ≤ 2 * (m : ℝ) := by
    have hcube : s ^ 3 ≤ (2 * (m : ℝ)) ^ 3 := by rw [hs3]; nlinarith [hTle]
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hcube
  rw [ge_iff_le, ← hs2, show (m : ℝ) * (T : ℝ) = (m : ℝ) * s ^ 3 by rw [hs3]]
  rw [Real.le_sqrt (by positivity) (mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hs0 3))]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), hs0, hs_le, pow_nonneg hs0 3,
    mul_le_mul_of_nonneg_right hs_le (pow_nonneg hs0 3)]

@[blueprint "thm:main-lower-bound"
  (statement := /-- Let $(\mathcal{D}_{T,m},G)$ be the online multicalibration hard instance
  \cref{def:online-mc-hard-instance}, with the fixed positive construction constant $\delta_{\ast}$
  \cref{def:hard-construction-constant} and threshold $\eta=\delta_{\ast}\sqrt{m/T}$
  \cref{def:hard-threshold} defining the hard group family \cref{def:hard-group-family}. There exist a
  universal constant $c>0$ and a threshold $T_0\in\mathbb{N}$ such that for every such instance with
  $T\ge T_0$, and hence for every possibly randomized online prediction algorithm represented by the
  instance, the expected multicalibration error \cref{def:expected-mc-error} satisfies
  $\mathbb{E}_{\mathcal{D}_{T,m}}[\mathrm{MCerr}_T(G)]\ge c\,T^{2/3}$. -/)
  (proof := /-- Apply \cref{lem:expected-mc-error-ge-sqrt-mt} to obtain a universal constant
  $c_1>0$ and a threshold $T_1\in\mathbb{N}$ such that every online multicalibration hard instance
  \cref{def:online-mc-hard-instance} with horizon $T\ge T_1$ satisfies
  $\mathbb{E}_{\mathcal{D}_{T,m}}[\mathrm{MCerr}_T(G)]\ge
  c_1\sqrt{mT}$ \cref{def:expected-mc-error}. Apply \cref{lem:sqrt-mt-ge-pow} to obtain a constant
  $c_2>0$ and a threshold $T_2\in\mathbb{N}$ such that $\sqrt{mT}\ge c_2\,T^{2/3}$ whenever $m\ge 1$,
  $m^3\le T<(m+1)^3$ and $T\ge T_2$. Set $c=c_1c_2>0$ and $T_0=\max(T_1,T_2)$. Let an instance with
  horizon $T\ge T_0$ be given. Its grid size satisfies $m\ge 2$, hence $m\ge 1$, and
  $m^3\le T<(m+1)^3$ by \cref{def:online-mc-hard-instance}; moreover $T\ge T_1$ and $T\ge T_2$. Chaining
  the two bounds gives $\mathbb{E}_{\mathcal{D}_{T,m}}[\mathrm{MCerr}_T(G)]\ge c_1\sqrt{mT}\ge
  c_1c_2\,T^{2/3}=c\,T^{2/3}$, which is the asserted bound. -/)
  (title := /-- Prediction-dependent lower bound -/)
  (latexEnv := "theorem")]
theorem main_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ inst : online_mc_hard_instance, T₀ ≤ inst.T →
      expected_mc_error inst ≥ c * (inst.T : ℝ) ^ ((2 : ℝ) / 3) := by
  rcases expected_mc_error_ge_sqrt_mt with ⟨c₁, hc₁, T₁, h₁⟩
  rcases sqrt_mt_ge_pow with ⟨c₂, hc₂, T₂, h₂⟩
  refine ⟨c₁ * c₂, mul_pos hc₁ hc₂, max T₁ T₂, fun inst hT => ?_⟩
  have hm : 1 ≤ inst.m := le_trans (by norm_num) inst.hm_grid
  have h₁T : T₁ ≤ inst.T := le_trans (le_max_left _ _) hT
  have h₂T : T₂ ≤ inst.T := le_trans (le_max_right _ _) hT
  calc
    expected_mc_error inst ≥ c₁ * Real.sqrt ((inst.m : ℝ) * (inst.T : ℝ)) := h₁ inst h₁T
    _ ≥ c₁ * (c₂ * (inst.T : ℝ) ^ ((2 : ℝ) / 3)) :=
      mul_le_mul_of_nonneg_left (h₂ inst.m inst.T hm inst.hm_lower inst.hm_upper h₂T) hc₁.le
    _ = (c₁ * c₂) * (inst.T : ℝ) ^ ((2 : ℝ) / 3) := by ring

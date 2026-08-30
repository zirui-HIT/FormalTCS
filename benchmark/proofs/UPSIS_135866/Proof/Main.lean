import Architect
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.Preorder.Finite
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.UniformOn

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:incremental-update"
  (statement := /-- For a universe of size $n$, an incremental update consists of an index
  $v\in[n]$ and a strictly positive real increment $\Delta$. -/)
  (title := /-- Incremental update -/)
  (latexEnv := "definition")]
structure incremental_update (n : ℕ) where
  index : Fin n
  increment : ℝ
  increment_pos : 0 < increment

@[blueprint "def:apply-incremental-update"
  (statement := /-- Applying $(v,\Delta)$ to $x\in\mathbb R^n$ replaces $x(v)$ by
  $x(v)+\Delta$ and leaves every other coordinate unchanged. -/)
  (title := /-- Action of an incremental update -/)
  (latexEnv := "definition")]
def apply_incremental_update {n : ℕ} (x : Fin n → ℝ) (u : incremental_update n) :
    Fin n → ℝ :=
  Function.update x u.index (x u.index + u.increment)

@[blueprint "def:stream-vector"
  (statement := /-- Given a list of incremental updates and a time $t$, the vector
  $x_t\in\mathbb R_+^n$ is obtained from the zero vector by applying the first $t$
  updates in their stream order. -/)
  (title := /-- Vector represented by a stream prefix -/)
  (latexEnv := "definition")]
def stream_vector {n : ℕ} (updates : List (incremental_update n)) (t : ℕ) : Fin n → ℝ :=
  (updates.take t).foldl apply_incremental_update (fun _ ↦ 0)

@[blueprint "def:weight-moment"
  (statement := /-- For a weight function $G:\mathbb R_+\to\mathbb R_+$ and a finite vector
  $x$, its $G$-moment is $G(x)=\sum_{v\in[n]}G(x(v))$. -/)
  (title := /-- The $G$-moment -/)
  (latexEnv := "definition")]
def weight_moment {n : ℕ} (G : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ v, G (x v)

@[blueprint "def:killed-laplace-kernel"
  (statement := /-- For $z\in\mathbb R$ and $x\in[0,\infty]$, define the killed
  Laplace kernel by $K(0,x)=1$, by $K(z,\infty)=0$ when $z\neq0$, and by
  $K(z,x)=e^{-zx}$ otherwise. This convention records killing at infinity while retaining
  the identity of the Laplace transform at $z=0$. -/)
  (title := /-- Laplace kernel for a killed process -/)
  (latexEnv := "definition")]
noncomputable def killed_laplace_kernel (z : ℝ) (x : ENNReal) : ENNReal :=
  if z = 0 then 1
  else if x = ⊤ then 0
  else ENNReal.ofReal (Real.exp (-z * x.toReal))

@[blueprint "def:killed-subordinator-law"
  (statement := /-- A killed-subordinator law with Laplace exponent
  $G:\mathbb R_+\to\mathbb R_+$ is a probability law $\mathsf P$ on paths
  $X:\mathbb R\to[0,\infty]$. Its coordinate maps are measurable; almost every path is
  zero at nonpositive times and nondecreasing; its tail map
  $(t,a)\mapsto\mathsf P(X_t\geq a)$ is measurable and is continuous in $t$ for every
  $a>0$; and, for all $t,z\geq0$,
  \[
    \int K(z,X_t)\,d\mathsf P=\exp(-tG(z)).
  \]
  The value $X_t=\infty$ represents killing. -/)
  (title := /-- Path law of a killed subordinator -/)
  (latexEnv := "definition")]
structure killed_subordinator_law (G : ℝ → ℝ) where
  law : MeasureTheory.Measure (ℝ → ENNReal)
  probability : law Set.univ = 1
  coordinate_measurable : ∀ t : ℝ, Measurable (fun path : ℝ → ENNReal ↦ path t)
  monotone_paths : law {path | Monotone path ∧ ∀ t : ℝ, t ≤ 0 → path t = 0} = 1
  tail_jointly_measurable : Measurable (fun p : ℝ × ℝ ↦
    law {path | ENNReal.ofReal p.2 ≤ path p.1})
  tail_continuous : ∀ a : ℝ, 0 < a →
    Continuous (fun t : ℝ ↦ law {path | ENNReal.ofReal a ≤ path t})
  laplace_transform : ∀ t z : ℝ, 0 ≤ t → 0 ≤ z →
    MeasureTheory.lintegral law (fun path ↦ killed_laplace_kernel z (path t)) =
      ENNReal.ofReal (Real.exp (-t * G z))

@[blueprint "def:levy-induced-level"
  (statement := /-- Let $\mathsf P$ be a killed-subordinator path law. Its induced level
  function is the generalized tail quantile
  \[
    \ell_{\mathsf P}(a,b)=
      \inf\{t\in[0,\infty):\mathsf P(X_t\geq a)\geq b\},
  \]
  with the infimum taken in $[0,\infty]$. Real arguments outside the probabilistic domain
  are interpreted through their nonnegative parts. -/)
  (title := /-- Lévy-induced level function -/)
  (latexEnv := "definition")]
noncomputable def levy_induced_level {G : ℝ → ℝ} (X : killed_subordinator_law G) :
    ℝ × ℝ → ENNReal :=
  fun p ↦ sInf {t : ENNReal | t ≠ ⊤ ∧
    ENNReal.ofReal p.2 ≤ X.law {path | ENNReal.ofReal p.1 ≤ path t.toReal}}

@[blueprint "def:is-admissible-weight"
  (statement := /-- A function $G:\mathbb R_+\to\mathbb R_+$ is admissible when there are
  $c,\gamma_0\geq0$ and a measure $\nu$ supported on $(0,\infty)$ with
  $\int\min(r,1)\,\nu(dr)<\infty$ such that, for every $z\geq0$,
  \[
    G(z)=c\mathbf 1_{\{z>0\}}+\gamma_0z+
      \int_{(0,\infty)}(1-e^{-rz})\,\nu(dr).
  \]
  The admissibility data also include the killed-subordinator path law with Laplace exponent
  $G$ furnished by the converse Lévy--Khintchine theorem. -/)
  (title := /-- Admissible weight functions -/)
  (latexEnv := "definition")]
def is_admissible_weight (G : ℝ → ℝ) : Prop :=
  (∀ z, 0 ≤ z → 0 ≤ G z) ∧
    (∃ c γ : ℝ, ∃ ν : MeasureTheory.Measure ℝ,
      0 ≤ c ∧ 0 ≤ γ ∧ ν (Set.Iic 0) = 0 ∧
      MeasureTheory.lintegral ν (fun r ↦ ENNReal.ofReal (min r 1)) < ⊤ ∧
      ∀ z, 0 ≤ z →
        G z = c * (if 0 < z then 1 else 0) + γ * z +
          (MeasureTheory.lintegral ν
            (fun r ↦ ENNReal.ofReal (1 - Real.exp (-r * z)))).toReal) ∧
    Nonempty (killed_subordinator_law G)

@[blueprint "def:has-law"
  (statement := /-- A random variable $X$ on $(\Omega,\mu)$ has law $\nu$ when its
  pushforward measure $X_\#\mu$ equals $\nu$. -/)
  (title := /-- Law of a random variable -/)
  (latexEnv := "definition")]
def has_law {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → α) (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure Ω) : Prop :=
  MeasureTheory.Measure.map X μ = ν

@[blueprint "def:has-uniform-unit-law"
  (statement := /-- A real random variable is uniform on $(0,1]$ when its law is Lebesgue
  measure restricted to that interval. Endpoints are immaterial because they have measure zero. -/)
  (title := /-- Uniform unit-interval law -/)
  (latexEnv := "definition")]
def has_uniform_unit_law {Ω : Type*} [MeasurableSpace Ω] (U : Ω → ℝ)
    (μ : MeasureTheory.Measure Ω) : Prop :=
  has_law U (MeasureTheory.volume.restrict (Set.Ioc 0 1)) μ

@[blueprint "def:exponential-with-top"
  (statement := /-- For a real rate $\lambda$, the extended exponential law on
  $\mathbb R_+\cup\{\infty\}$ is the ordinary exponential law, transported by the
  nonnegative-part inclusion, when $\lambda>0$, and is the Dirac law at $\infty$ when
  $\lambda\leq0$. In particular, rate zero represents an inactive clock. -/)
  (title := /-- Extended exponential law -/)
  (latexEnv := "definition")]
noncomputable def exponential_with_top (rate : ℝ) : MeasureTheory.Measure ENNReal :=
  if 0 < rate then
    MeasureTheory.Measure.map ENNReal.ofReal (ProbabilityTheory.expMeasure rate)
  else
    MeasureTheory.Measure.dirac ⊤

@[blueprint "def:pareto-random-source"
  (statement := /-- For a stream of length $m$ over $[n]$, a Pareto random source consists
  of independent uniform hash values $H(v)$ and independent rate-one exponential variables
  $Y_i$, with the two families jointly independent. -/)
  (title := /-- Randomness used by the Pareto sampler -/)
  (latexEnv := "definition")]
structure pareto_random_source (Ω : Type*) [MeasurableSpace Ω] (n m : ℕ)
    (μ : MeasureTheory.Measure Ω) where
  hash : Fin n → Ω → ℝ
  noise : Fin m → Ω → ℝ
  hash_measurable : ∀ v, Measurable (hash v)
  noise_measurable : ∀ i, Measurable (noise i)
  hash_uniform : ∀ v, has_uniform_unit_law (hash v) μ
  noise_exponential : ∀ i, has_law (noise i) (ProbabilityTheory.expMeasure 1) μ
  jointly_independent :
    ProbabilityTheory.iIndepFun (fun j ↦ Sum.elim hash noise j) μ

@[blueprint "def:pareto-tuple"
  (statement := /-- A stored tuple records a priority $Y_i/\Delta_i$, the hash value of the
  updated coordinate, and the coordinate itself. -/)
  (title := /-- Pareto tuple -/)
  (latexEnv := "definition")]
structure pareto_tuple (n : ℕ) where
  priority : ℝ
  hashValue : ℝ
  index : Fin n

@[blueprint "def:pareto-tuple-coordinates"
  (statement := /-- The order coordinates of a Pareto tuple are its priority and hash value. -/)
  (title := /-- Order coordinates of a tuple -/)
  (latexEnv := "definition")]
def pareto_tuple_coordinates {n : ℕ} (p : pareto_tuple n) : ℝ × ℝ :=
  (p.priority, p.hashValue)

@[blueprint "def:pareto-frontier"
  (statement := /-- The minimum Pareto frontier of a finite tuple set consists of those tuples
  for which every coordinatewise smaller tuple has the same two order coordinates. -/)
  (title := /-- Minimum Pareto frontier -/)
  (latexEnv := "definition")]
noncomputable def pareto_frontier {n : ℕ} (s : Finset (pareto_tuple n)) :
    Finset (pareto_tuple n) := by
  classical
  exact s.filter fun p ↦
    ∀ q ∈ s, pareto_tuple_coordinates q ≤ pareto_tuple_coordinates p →
      pareto_tuple_coordinates p ≤ pareto_tuple_coordinates q

@[blueprint "def:active-update-indices"
  (statement := /-- At time $t$, the active update indices for $v$ are precisely the positions
  among the first $t$ stream entries whose updated coordinate is $v$. -/)
  (title := /-- Active updates of one coordinate -/)
  (latexEnv := "definition")]
noncomputable def active_update_indices {n : ℕ} (updates : List (incremental_update n))
    (t : ℕ) (v : Fin n) : Finset (Fin updates.length) := by
  classical
  exact Finset.univ.filter fun i ↦ i.val < t ∧ (updates.get i).index = v

@[blueprint "def:finite-minimum-with-infinity"
  (statement := /-- The minimum of a real-valued function on a finite set is viewed in
  $\mathbb R\cup\{\infty\}$; the value on the empty set is $\infty$. -/)
  (title := /-- Finite minimum with empty value infinity -/)
  (latexEnv := "definition")]
noncomputable def finite_minimum_with_infinity {α : Type*} (s : Finset α)
    (f : α → ENNReal) : ENNReal := by
  classical
  exact if h : s.Nonempty then
    (s.image f).min' (h.image f)
  else ⊤

@[blueprint "def:generated-pareto-tuple"
  (statement := /-- The tuple generated by update $i=(v_i,\Delta_i)$ is
  $(Y_i/\Delta_i,H(v_i),v_i)$. -/)
  (title := /-- Tuple generated by an update -/)
  (latexEnv := "definition")]
noncomputable def generated_pareto_tuple {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ) (ω : Ω)
    (i : Fin updates.length) : pareto_tuple n where
  priority := source.noise i ω / (updates.get i).increment
  hashValue := source.hash (updates.get i).index ω
  index := (updates.get i).index

@[blueprint "def:generated-tuples"
  (statement := /-- The set $T_t$ contains all tuples generated by the first $t$ updates. -/)
  (title := /-- Generated tuple set -/)
  (latexEnv := "definition")]
noncomputable def generated_tuples {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ) (ω : Ω) (t : ℕ) :
    Finset (pareto_tuple n) := by
  classical
  exact (Finset.univ.filter fun i : Fin updates.length ↦ i.val < t).image
    (generated_pareto_tuple updates μ source ω)

@[blueprint "def:pareto-state"
  (statement := /-- The state $S_t$ of the Pareto sampler is the minimum Pareto frontier of
  the tuples generated by the first $t$ updates. -/)
  (title := /-- State of the Pareto sampler -/)
  (latexEnv := "definition")]
noncomputable def pareto_state {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ) (ω : Ω) (t : ℕ) :
    Finset (pareto_tuple n) :=
  pareto_frontier (generated_tuples updates μ source ω t)

@[blueprint "def:pareto-space-words"
  (statement := /-- Since each stored tuple occupies three words, the space at time $t$ is
  three times the cardinality of the maintained Pareto frontier. -/)
  (title := /-- Space used by the Pareto state -/)
  (latexEnv := "definition")]
noncomputable def pareto_space_words {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ) (ω : Ω) (t : ℕ) : ℕ :=
  3 * (pareto_state updates μ source ω t).card

@[blueprint "def:coordinate-priority"
  (statement := /-- For coordinate $v$ at time $t$, let $h_v$ be the minimum of
  $Y_i/\Delta_i$ over updates to $v$ among the first $t$ entries, with $h_v=\infty$ when
  there is no such update. -/)
  (title := /-- Minimum update priority of a coordinate -/)
  (latexEnv := "definition")]
noncomputable def coordinate_priority {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ) (ω : Ω) (t : ℕ) (v : Fin n) :
    ENNReal :=
  finite_minimum_with_infinity (active_update_indices updates t v)
    (fun i ↦ ENNReal.ofReal (source.noise i ω / (updates.get i).increment))

@[blueprint "def:level-function-spec"
  (statement := /-- A level function for $G$ is a measurable coordinatewise monotone map
  $\ell_G:\mathbb R^2\to\mathbb R_+\cup\{\infty\}$. The function $G$ vanishes at
  zero and is nonnegative on $\mathbb R_+$. Whenever $\lambda>0$,
  $Y\sim\operatorname{Exp}(\lambda)$, and $U\sim\operatorname{Unif}(0,1)$ are
  independent, the transformed variable has the extended exponential law of rate
  $G(\lambda)$. -/)
  (title := /-- Level-function specification -/)
  (latexEnv := "definition")]
def level_function_spec (G : ℝ → ℝ) (ell : ℝ × ℝ → ENNReal) : Prop :=
  Measurable ell ∧ Monotone ell ∧
    (∀ rate : ℝ, 0 < rate →
      has_law ell (exponential_with_top (G rate))
        ((ProbabilityTheory.expMeasure rate).prod
          (MeasureTheory.volume.restrict (Set.Ioc 0 1)))) ∧
    G 0 = 0 ∧
    ∀ z : ℝ, 0 ≤ z → 0 ≤ G z

@[blueprint "def:coordinate-level-score"
  (statement := /-- For a level function $\ell$, the score of coordinate $v$ at time $t$
  is the minimum of $\ell(Y_i/\Delta_i,H(v))$ over its active updates, and is $\infty$
  if the coordinate has not appeared. -/)
  (title := /-- Coordinate score for a level function -/)
  (latexEnv := "definition")]
noncomputable def coordinate_level_score {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ) (ell : ℝ × ℝ → ENNReal)
    (ω : Ω) (t : ℕ) (v : Fin n) : ENNReal :=
  finite_minimum_with_infinity (active_update_indices updates t v)
    (fun i ↦ ell (source.noise i ω / (updates.get i).increment,
      source.hash v ω))

@[blueprint "def:exponential-race-family"
  (statement := /-- A finite score family is an exponential race with rates $(r_v)$ when
  every rate is nonnegative, the coordinates are independent, and the score at $v$ has the
  extended exponential law of rate $r_v$. Thus a coordinate of rate zero is almost surely
  equal to $\infty$. -/)
  (title := /-- Finite exponential race -/)
  (latexEnv := "definition")]
def exponential_race_family {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : MeasureTheory.Measure Ω) (rates : Fin n → ℝ)
    (scores : Fin n → Ω → ENNReal) : Prop :=
  (∀ v, has_law (scores v) (exponential_with_top (rates v)) μ) ∧
    ProbabilityTheory.iIndepFun scores μ ∧
    ∀ v, 0 ≤ rates v

@[blueprint "def:full-sample-at"
  (statement := /-- An output is a full $G$-sampler at time $t$ when some valid level
  function makes its selected coordinate attain the minimum score among all coordinates. -/)
  (title := /-- Full-tuple sampler at a fixed time -/)
  (latexEnv := "definition")]
def full_sample_at {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ) (t : ℕ) (G : ℝ → ℝ)
    (out : Ω → Fin n) : Prop :=
  ∃ ell : ℝ × ℝ → ENNReal, level_function_spec G ell ∧
    ∀ ω v, coordinate_level_score updates μ source ell ω t (out ω) ≤
      coordinate_level_score updates μ source ell ω t v

@[blueprint "def:pareto-sample-at"
  (statement := /-- An output is a Pareto sample at time $t$ if, for some valid level function,
  it is the index of a tuple of $S_t$ whose level is minimal throughout $S_t$. -/)
  (title := /-- Pareto-frontier sampler at a fixed time -/)
  (latexEnv := "definition")]
def pareto_sample_at {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ) (t : ℕ) (G : ℝ → ℝ)
    (out : Ω → Fin n) : Prop :=
  ∃ ell : ℝ × ℝ → ENNReal, level_function_spec G ell ∧
    ∀ ω, ∃ p ∈ pareto_state updates μ source ω t,
      p.index = out ω ∧
      ∀ q ∈ pareto_state updates μ source ω t,
        ell (pareto_tuple_coordinates p) ≤ ell (pareto_tuple_coordinates q)

@[blueprint "def:pareto-sampler-run"
  (statement := /-- A run of the universal sampler has a query operation which, at every
  time and for every admissible $G$, returns an index in $[n]$. -/)
  (title := /-- Query interface of a Pareto sampler run -/)
  (latexEnv := "definition")]
structure pareto_sampler_run (Ω : Type*) [MeasurableSpace Ω] (n : ℕ) where
  output : (t : ℕ) → (G : ℝ → ℝ) → is_admissible_weight G → Ω → Fin n
  output_measurable : ∀ t G hG, Measurable (output t G hG)

@[blueprint "def:implements-pareto-sampler"
  (statement := /-- A run implements the Pareto sampler on a fixed stream if, at every
  time and for every admissible query function having positive moment, its output is obtained
  by minimizing a valid level function on the maintained Pareto frontier. -/)
  (title := /-- Implementation relation for the Pareto sampler -/)
  (latexEnv := "definition")]
def implements_pareto_sampler {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ)
    (run : pareto_sampler_run Ω n) : Prop :=
  ∀ (t : ℕ), t ≤ updates.length → ∀ (G : ℝ → ℝ) (hG : is_admissible_weight G),
    0 < weight_moment G (stream_vector updates t) →
      pareto_sample_at updates μ source t G (run.output t G hG)

@[blueprint "def:is-prefix-record"
  (statement := /-- Fix priorities $h$ on $[n]$ and break equal priorities by the natural
  order of their coordinate labels. In a permutation $\sigma$, position $i$ is a prefix
  record when the pair $(h_{\sigma(i)},\sigma(i))$ is lexicographically minimal among
  $(h_{\sigma(j)},\sigma(j))$ for $j\leq i$. The coordinate tie-break makes these pairs
  distinct for every priority vector. -/)
  (title := /-- Prefix record minimum -/)
  (latexEnv := "definition")]
def is_prefix_record {n : ℕ} (priority : Fin n → ENNReal)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∀ j : Fin n, j.val ≤ i.val →
    priority (σ i) < priority (σ j) ∨
      (priority (σ i) = priority (σ j) ∧ (σ i).val ≤ (σ j).val)

@[blueprint "def:record-count"
  (statement := /-- The record count is the number of positions which are prefix record
  minima in a given permutation. -/)
  (title := /-- Number of prefix record minima -/)
  (latexEnv := "definition")]
noncomputable def record_count {n : ℕ} (priority : Fin n → ENNReal)
    (σ : Equiv.Perm (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter fun i ↦ is_prefix_record priority σ i).card

@[blueprint "def:is-active-prefix-record"
  (statement := /-- In a permutation $\sigma$ of coordinates with extended priorities $h$,
  position $i$ is an active strict prefix record when $h_{\sigma(i)}<\infty$ and its
  priority is strictly smaller than every priority in an earlier position. Thus inactive
  coordinates and later occurrences of a tied minimum are not counted. -/)
  (title := /-- Active strict prefix record -/)
  (latexEnv := "definition")]
def is_active_prefix_record {n : ℕ} (priority : Fin n → ENNReal)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  priority (σ i) ≠ ⊤ ∧
    ∀ j : Fin n, j.val < i.val → priority (σ i) < priority (σ j)

@[blueprint "def:active-record-count"
  (statement := /-- The active record count is the number of positions that are active
  strict prefix records. -/)
  (title := /-- Number of active strict prefix records -/)
  (latexEnv := "definition")]
noncomputable def active_record_count {n : ℕ} (priority : Fin n → ENNReal)
    (σ : Equiv.Perm (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter fun i ↦ is_active_prefix_record priority σ i).card

@[blueprint "def:uniform-permutation"
  (statement := /-- The uniform probability mass function on the finite symmetric group of
  $[n]$ assigns equal mass to every permutation. -/)
  (title := /-- Uniform random permutation -/)
  (latexEnv := "definition")]
noncomputable def uniform_permutation (n : ℕ) : PMF (Equiv.Perm (Fin n)) :=
  PMF.uniformOfFintype (Equiv.Perm (Fin n))

@[blueprint "def:pmf-event"
  (statement := /-- The probability of a predicate under a probability mass function is the
  sum of the masses of the points satisfying that predicate. -/)
  (title := /-- Event probability for a PMF -/)
  (latexEnv := "definition")]
noncomputable def pmf_event {α : Type*} [Fintype α] (p : PMF α)
    (P : α → Prop) : ENNReal := by
  classical
  exact ∑ a, if P a then p a else 0

@[blueprint "def:has-pmf-law"
  (statement := /-- A finite-valued random variable has probability mass function $p$ when
  every singleton fibre has the mass assigned by $p$. -/)
  (title := /-- Law specified by a PMF -/)
  (latexEnv := "definition")]
def has_pmf_law {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
    (X : Ω → α) (p : PMF α) (μ : MeasureTheory.Measure Ω) : Prop :=
  ∀ a, μ {ω | X ω = a} = p a

@[blueprint "def:independent-of-pmf"
  (statement := /-- A random element $X$ is independent of a finite random element $Y$ with
  mass function $p$ when, for every measurable event $A$ in the codomain of $X$ and every
  subset $B$ of the finite codomain of $Y$, the probability of the corresponding product
  event is the product of the two marginal probabilities. -/)
  (title := /-- Independence from a finite PMF-valued variable -/)
  (latexEnv := "definition")]
def independent_of_pmf {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [Fintype β]
    (X : Ω → α) (Y : Ω → β) (p : PMF β) (μ : MeasureTheory.Measure Ω) : Prop :=
  ∀ A : Set α, MeasurableSet A → ∀ B : Set β,
    μ {ω | X ω ∈ A ∧ Y ω ∈ B} =
      μ {ω | X ω ∈ A} * pmf_event p (fun y ↦ y ∈ B)

@[blueprint "lem:admissible-level-function"
  (statement := /-- Every admissible weight function $G:\mathbb R\to\mathbb R$ admits a
  measurable, coordinatewise nondecreasing function
  $\ell_G:\mathbb R^2\to\mathbb R_+\cup\{\infty\}$. For every $\lambda>0$, the pushforward
  under $\ell_G$ of the product of the rate-$\lambda$ exponential law and the uniform law
  on $(0,1]$ is the extended exponential law of rate $G(\lambda)$. Moreover,
  $G(0)=0$ and $G(z)\geq0$ for every $z\geq0$. -/)
  (proof := /-- Choose the killed-subordinator law $\mathsf P$ supplied by
  \cref{def:is-admissible-weight, def:killed-subordinator-law}. Define $\ell_G(a,b)$ as the
  infimum of the nonnegative rational times $q$ for which
  $b<\mathsf P(X_q\geq a)$, with value $\infty$ if there is no such time. This countable
  infimum is measurable by joint measurability of the tail map. Almost-sure monotonicity of
  the paths makes the tail nondecreasing in time and nonincreasing in the level, and hence
  makes $\ell_G$ coordinatewise nondecreasing. Continuity in time and density of the
  rationals give, for every $t>0$,
  \[
    t\leq\ell_G(a,b)\quad\Longleftrightarrow\quad
    \mathsf P(X_t\geq a)\leq b.
  \]
  Consequently, under the product of the rate-$\lambda$ exponential law and the uniform
  law on $(0,1]$, Tonelli's theorem and \cref{def:killed-laplace-kernel} yield
  \[
    \mathbb P(\ell_G(Y,U)\geq t)
      =\int\bigl(1-\mathsf P(X_t\geq a)\bigr)\,d\operatorname{Exp}(\lambda)(a)
      =\int K(\lambda,X_t)\,d\mathsf P
      =e^{-tG(\lambda)}.
  \]
  Equality on finite closed upper rays, followed by continuity from above at $\infty$,
  identifies the pushforward measure with the law in
  \cref{def:exponential-with-top}. Finally, the representation in
  \cref{def:is-admissible-weight} evaluated at zero gives $G(0)=0$, while its first clause
  gives $G(z)\geq0$ for $z\geq0$. These properties establish
  \cref{def:level-function-spec}. -/)
  (title := /-- Existence of the Lévy-induced level function -/)
  (latexEnv := "lemma")]
lemma admissible_level_function (G : ℝ → ℝ) (hG : is_admissible_weight G) :
    ∃ ell : ℝ × ℝ → ENNReal, level_function_spec G ell := by
  classical
  rcases hG.2.2 with ⟨X⟩
  let ell : ℝ × ℝ → ENNReal := fun p ↦
    ⨅ q : ℚ, if 0 ≤ q ∧ ENNReal.ofReal p.2 <
        X.law {path | ENNReal.ofReal p.1 ≤ path (q : ℝ)} then
      ENNReal.ofReal (q : ℝ) else ⊤
  have hell_measurable : Measurable ell := by
    dsimp [ell]
    apply Measurable.iInf
    intro q
    by_cases hq : 0 ≤ q
    · simp only [hq, true_and]
      apply Measurable.ite
      · exact measurableSet_lt measurable_snd.ennreal_ofReal
          (X.tail_jointly_measurable.comp (measurable_const.prodMk measurable_fst))
      · exact measurable_const
      · exact measurable_const
    · simp [hq]
  have hell_monotone : Monotone ell := by
    intro p p' hpp'
    dsimp [ell]
    refine iInf_mono fun q ↦ ?_
    by_cases hq' : 0 ≤ q ∧ ENNReal.ofReal p'.2 <
        X.law {path | ENNReal.ofReal p'.1 ≤ path (q : ℝ)}
    · have hevent : {path : ℝ → ENNReal | ENNReal.ofReal p'.1 ≤ path (q : ℝ)} ⊆
          {path : ℝ → ENNReal | ENNReal.ofReal p.1 ≤ path (q : ℝ)} := by
        intro path hpath
        exact (ENNReal.ofReal_le_ofReal hpp'.1).trans hpath
      have htail : X.law {path | ENNReal.ofReal p'.1 ≤ path (q : ℝ)} ≤
          X.law {path | ENNReal.ofReal p.1 ≤ path (q : ℝ)} :=
        MeasureTheory.measure_mono hevent
      have hq : 0 ≤ q ∧ ENNReal.ofReal p.2 <
          X.law {path | ENNReal.ofReal p.1 ≤ path (q : ℝ)} :=
        ⟨hq'.1, (ENNReal.ofReal_le_ofReal hpp'.2).trans_lt (hq'.2.trans_le htail)⟩
      simp [hq, hq']
    · simp [hq']
  have hG_zero : G 0 = 0 := by
    rcases hG.2.1 with ⟨c, γ, ν, hc, hγ, hν, hint, hrep⟩
    simpa using hrep 0 le_rfl
  letI : MeasureTheory.IsProbabilityMeasure X.law := ⟨X.probability⟩
  have hpath_mono (s t : ℝ) (hst : s ≤ t) :
      ∀ᵐ path ∂X.law, path s ≤ path t := by
    have hset : {path : ℝ → ENNReal | Monotone path ∧
        ∀ u : ℝ, u ≤ 0 → path u = 0} ⊆ {path | path s ≤ path t} := by
      intro path hpath
      exact hpath.1 hst
    have hle : (1 : ENNReal) ≤ X.law {path | path s ≤ path t} := by
      rw [← X.monotone_paths]
      exact MeasureTheory.measure_mono hset
    have heq : X.law {path | path s ≤ path t} = 1 :=
      le_antisymm (calc
        X.law {path | path s ≤ path t} ≤ X.law Set.univ :=
          MeasureTheory.measure_mono (Set.subset_univ _)
        _ = 1 := X.probability) hle
    exact (MeasureTheory.ae_mem_iff_measure_eq
      (measurableSet_le (X.coordinate_measurable s)
        (X.coordinate_measurable t)).nullMeasurableSet).2 (by simpa using heq)
  have htail_mono (a s t : ℝ) (hst : s ≤ t) :
      X.law {path | ENNReal.ofReal a ≤ path s} ≤
        X.law {path | ENNReal.ofReal a ≤ path t} := by
    apply MeasureTheory.measure_mono_ae
    filter_upwards [hpath_mono s t hst] with path hpath hat
    exact hat.trans hpath
  have hell_Ici (a b t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal t ≤ ell (a, b) ↔
        X.law {path | ENNReal.ofReal a ≤ path t} ≤ ENNReal.ofReal b := by
    constructor
    · intro htell
      by_contra hnot
      have hlt : ENNReal.ofReal b <
          X.law {path | ENNReal.ofReal a ≤ path t} := lt_of_not_ge hnot
      by_cases ha : 0 < a
      · have heventually :=
          continuousAt_const.eventually_lt (X.tail_continuous a ha).continuousAt hlt
        rw [Metric.eventually_nhds_iff] at heventually
        rcases heventually with ⟨ε, hε, hepsilon⟩
        have hlower : max 0 (t - ε) < t :=
          max_lt ht (sub_lt_self t hε)
        rcases exists_rat_btwn hlower with ⟨q, hq_lower, hq_upper⟩
        have hq_nonneg : 0 ≤ (q : ℝ) :=
          (le_max_left 0 (t - ε)).trans hq_lower.le
        have hq_near : dist (q : ℝ) t < ε := by
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hq_upper.le)]
          have : t - ε < (q : ℝ) :=
            (le_max_right 0 (t - ε)).trans_lt hq_lower
          linarith
        have hq_tail : ENNReal.ofReal b <
            X.law {path | ENNReal.ofReal a ≤ path (q : ℝ)} := hepsilon hq_near
        have hq_nonneg_rat : 0 ≤ q := by exact_mod_cast hq_nonneg
        have hell_q : ell (a, b) ≤ ENNReal.ofReal (q : ℝ) := by
          dsimp [ell]
          exact iInf_le_of_le q (by simp [hq_nonneg_rat, hq_tail])
        have htq : t ≤ (q : ℝ) :=
          (ENNReal.ofReal_le_ofReal_iff hq_nonneg).mp (htell.trans hell_q)
        exact (not_le_of_gt hq_upper) htq
      · have ha_nonpos : a ≤ 0 := le_of_not_gt ha
        have htail_one (s : ℝ) :
            X.law {path | ENNReal.ofReal a ≤ path s} = 1 := by
          rw [ENNReal.ofReal_eq_zero.mpr ha_nonpos]
          simpa using X.probability
        have hb_one : ENNReal.ofReal b < 1 := by
          simpa [htail_one] using hlt
        have hell_zero : ell (a, b) ≤ ENNReal.ofReal 0 := by
          dsimp [ell]
          exact iInf_le_of_le (0 : ℚ) (by simp [htail_one, hb_one])
        have ht0 : t ≤ 0 :=
          (ENNReal.ofReal_le_ofReal_iff le_rfl).mp (htell.trans hell_zero)
        exact (not_le_of_gt ht) ht0
    · intro htail
      dsimp [ell]
      apply le_iInf
      intro q
      split_ifs with hq
      · apply ENNReal.ofReal_le_ofReal
        by_contra htq
        have hqt : (q : ℝ) < t := lt_of_not_ge htq
        have hmono := htail_mono a (q : ℝ) t hqt.le
        exact (hq.2.trans_le (hmono.trans htail)).false
      · exact le_top
  have huniform_tail (u : ENNReal) (hu : u ≤ 1) :
      (MeasureTheory.volume.restrict (Set.Ioc 0 1))
          {b : ℝ | u ≤ ENNReal.ofReal b} = 1 - u := by
    by_cases hu_zero : u = 0
    · subst u
      simp
    · have hu_top : u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hu
      have hu_pos : 0 < u.toReal := ENNReal.toReal_pos hu_zero hu_top
      rw [MeasureTheory.Measure.restrict_apply
        (measurableSet_le measurable_const ENNReal.measurable_ofReal)]
      have hset : Set.Ioc (0 : ℝ) 1 ∩ {b : ℝ | u ≤ ENNReal.ofReal b} =
          Set.Icc u.toReal 1 := by
        ext b
        simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_setOf_eq, Set.mem_Icc]
        constructor
        · rintro ⟨⟨hb_zero, hb_one⟩, hub⟩
          exact ⟨(ENNReal.le_ofReal_iff_toReal_le hu_top hb_zero.le).mp hub, hb_one⟩
        · rintro ⟨hub, hb_one⟩
          have hb_zero : 0 < b := hu_pos.trans_le hub
          exact ⟨⟨hb_zero, hb_one⟩,
            (ENNReal.le_ofReal_iff_toReal_le hu_top hb_zero.le).mpr hub⟩
      rw [Set.inter_comm, hset, Real.volume_Icc,
        ENNReal.ofReal_sub 1 ENNReal.toReal_nonneg,
        ENNReal.ofReal_one, ENNReal.ofReal_toReal hu_top]
  refine ⟨ell, hell_measurable, hell_monotone, ?_, hG_zero, hG.1⟩
  intro rate hrate
  letI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.expMeasure rate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  have hexp_Ioi (r : ℝ) (hr : 0 < r) (s : ℝ) (hs : 0 ≤ s) :
      ProbabilityTheory.expMeasure r (Set.Ioi s) =
        ENNReal.ofReal (Real.exp (-r * s)) := by
    letI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.expMeasure r) :=
      ProbabilityTheory.isProbabilityMeasure_expMeasure hr
    rw [show Set.Ioi s = (Set.Iic s)ᶜ by simp,
      MeasureTheory.prob_compl_eq_one_sub measurableSet_Iic]
    rw [← ProbabilityTheory.ofReal_cdf,
      ProbabilityTheory.cdf_expMeasure_eq hr]
    simp only [hs, if_pos, ENNReal.ofReal_sub 1 (Real.exp_nonneg _),
      ENNReal.ofReal_one]
    rw [show -r * s = -(r * s) by ring]
    apply ENNReal.sub_sub_cancel ENNReal.one_ne_top
    simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hr.le hs))
  have hexp_tail (x : ENNReal) :
      ProbabilityTheory.expMeasure rate {a : ℝ | x < ENNReal.ofReal a} =
        killed_laplace_kernel rate x := by
    by_cases hx : x = ⊤
    · subst x
      simp [killed_laplace_kernel, ne_of_gt hrate]
    · have hset : {a : ℝ | x < ENNReal.ofReal a} = Set.Ioi x.toReal := by
        ext a
        exact ENNReal.lt_ofReal_iff_toReal_lt hx
      rw [hset, hexp_Ioi rate hrate x.toReal ENNReal.toReal_nonneg]
      simp [killed_laplace_kernel, ne_of_gt hrate, hx]
  have htail_le_one (a t : ℝ) :
      X.law {path | ENNReal.ofReal a ≤ path t} ≤ 1 := calc
    X.law {path | ENNReal.ofReal a ≤ path t} ≤ X.law Set.univ :=
      MeasureTheory.measure_mono (Set.subset_univ _)
    _ = 1 := X.probability
  have hsource_survival (t : ℝ) (ht : 0 < t) :
      MeasureTheory.Measure.map ell
          ((ProbabilityTheory.expMeasure rate).prod
            (MeasureTheory.volume.restrict (Set.Ioc 0 1)))
          (Set.Ici (ENNReal.ofReal t)) =
        ENNReal.ofReal (Real.exp (-t * G rate)) := by
    rw [MeasureTheory.Measure.map_apply hell_measurable measurableSet_Ici,
      MeasureTheory.Measure.prod_apply (hell_measurable measurableSet_Ici)]
    have hsections : ∀ a : ℝ,
        (MeasureTheory.volume.restrict (Set.Ioc 0 1))
            ((fun b ↦ (a, b)) ⁻¹' (ell ⁻¹' Set.Ici (ENNReal.ofReal t))) =
          1 - X.law {path | ENNReal.ofReal a ≤ path t} := by
      intro a
      rw [show (fun b ↦ (a, b)) ⁻¹' (ell ⁻¹' Set.Ici (ENNReal.ofReal t)) =
          {b : ℝ | X.law {path | ENNReal.ofReal a ≤ path t} ≤ ENNReal.ofReal b} by
        ext b
        exact hell_Ici a b t ht]
      exact huniform_tail _ (htail_le_one a t)
    simp_rw [hsections]
    calc
      (∫⁻ a, 1 - X.law {path | ENNReal.ofReal a ≤ path t}
          ∂ProbabilityTheory.expMeasure rate) =
          ∫⁻ a, X.law {path | path t < ENNReal.ofReal a}
            ∂ProbabilityTheory.expMeasure rate := by
        congr 1
        funext a
        rw [← MeasureTheory.prob_compl_eq_one_sub
          (measurableSet_le measurable_const (X.coordinate_measurable t))]
        congr 1
        ext path
        simp
      _ = ∫⁻ path, ProbabilityTheory.expMeasure rate
          {a : ℝ | path t < ENNReal.ofReal a} ∂X.law := by
        let S : Set (ℝ × (ℝ → ENNReal)) :=
          {p | p.2 t < ENNReal.ofReal p.1}
        have hS : MeasurableSet S :=
          measurableSet_lt ((X.coordinate_measurable t).comp measurable_snd)
            measurable_fst.ennreal_ofReal
        calc
          (∫⁻ a, X.law {path | path t < ENNReal.ofReal a}
              ∂ProbabilityTheory.expMeasure rate) =
              (ProbabilityTheory.expMeasure rate).prod X.law S := by
            rw [MeasureTheory.Measure.prod_apply hS]
            rfl
          _ = ∫⁻ path, ProbabilityTheory.expMeasure rate
              {a : ℝ | path t < ENNReal.ofReal a} ∂X.law := by
            rw [MeasureTheory.Measure.prod_apply_symm hS]
            rfl
      _ = ∫⁻ path, killed_laplace_kernel rate (path t) ∂X.law := by
        simp_rw [hexp_tail]
      _ = ENNReal.ofReal (Real.exp (-t * G rate)) :=
        X.laplace_transform t rate ht.le hrate.le
  have hexp_Ici (r : ℝ) (hr : 0 < r) (s : ℝ) :
      ProbabilityTheory.expMeasure r (Set.Ici s) =
        ProbabilityTheory.expMeasure r (Set.Ioi s) := by
    rw [show Set.Ici s = {s} ∪ Set.Ioi s by
      ext x
      simp only [Set.mem_Ici, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioi]
      simpa [eq_comm] using (le_iff_eq_or_lt : s ≤ x ↔ s = x ∨ s < x)]
    rw [MeasureTheory.measure_union (by simp) measurableSet_Ioi]
    simp [ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure]
  have htarget_survival (t : ℝ) (ht : 0 < t) :
      exponential_with_top (G rate) (Set.Ici (ENNReal.ofReal t)) =
        ENNReal.ofReal (Real.exp (-t * G rate)) := by
    have hG_nonneg : 0 ≤ G rate := hG.1 rate hrate.le
    by_cases hG_pos : 0 < G rate
    · rw [exponential_with_top, if_pos hG_pos,
        MeasureTheory.Measure.map_apply ENNReal.measurable_ofReal measurableSet_Ici]
      have hpreimage : ENNReal.ofReal ⁻¹' Set.Ici (ENNReal.ofReal t) =
          Set.Ici t := by
        ext x
        simp [ENNReal.ofReal_le_ofReal_iff', (not_le_of_gt ht)]
      rw [hpreimage, hexp_Ici (G rate) hG_pos t,
        hexp_Ioi (G rate) hG_pos t ht.le]
      congr 2
      ring
    · have hG_zero : G rate = 0 := le_antisymm (le_of_not_gt hG_pos) hG_nonneg
      simp [exponential_with_top, hG_pos, hG_zero]
  letI : MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  let sourceMeasure :=
    MeasureTheory.Measure.map ell
      ((ProbabilityTheory.expMeasure rate).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 1)))
  letI : MeasureTheory.IsProbabilityMeasure sourceMeasure :=
    MeasureTheory.Measure.isProbabilityMeasure_map hell_measurable.aemeasurable
  let targetMeasure := exponential_with_top (G rate)
  letI : MeasureTheory.IsProbabilityMeasure targetMeasure := ⟨by
    dsimp [targetMeasure, exponential_with_top]
    split_ifs with h
    · letI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.expMeasure (G rate)) :=
        ProbabilityTheory.isProbabilityMeasure_expMeasure h
      rw [MeasureTheory.Measure.map_apply ENNReal.measurable_ofReal MeasurableSet.univ]
      simp
    · simp⟩
  unfold has_law
  change sourceMeasure = targetMeasure
  apply MeasureTheory.Measure.ext_of_Ici
  intro x
  by_cases hx_zero : x = 0
  · subst x
    simp
  by_cases hx_top : x = ⊤
  · subst x
    have hInter : (⋂ n : ℕ, Set.Ici ((n + 1 : ℕ) : ENNReal)) =
        ({⊤} : Set ENNReal) := by
      ext y
      simp only [Set.mem_iInter, Set.mem_Ici, Set.mem_singleton_iff]
      constructor
      · intro hy
        apply top_unique
        rw [← ENNReal.iSup_natCast]
        exact iSup_le fun n ↦
          (show (n : ENNReal) ≤ ((n + 1 : ℕ) : ENNReal) by norm_num).trans (hy n)
      · rintro rfl
        exact fun n ↦ le_top
    have hanti : Antitone (fun n : ℕ ↦ Set.Ici ((n + 1 : ℕ) : ENNReal)) := by
      intro i j hij
      exact Set.Ici_subset_Ici.2 (by exact_mod_cast Nat.add_le_add_right hij 1)
    rw [show Set.Ici (⊤ : ENNReal) = ({⊤} : Set ENNReal) by simp, ← hInter,
      hanti.measure_iInter (fun _ ↦ measurableSet_Ici.nullMeasurableSet)
        ⟨0, MeasureTheory.measure_ne_top sourceMeasure _⟩,
      hanti.measure_iInter (fun _ ↦ measurableSet_Ici.nullMeasurableSet)
        ⟨0, MeasureTheory.measure_ne_top targetMeasure _⟩]
    congr 1
    funext n
    have hn : 0 < (n + 1 : ℝ) := by positivity
    have hcast : ENNReal.ofReal (n + 1 : ℝ) = ((n + 1 : ℕ) : ENNReal) := by
      convert ENNReal.ofReal_natCast (n + 1) using 1 <;> norm_num
    rw [← hcast]
    simpa [sourceMeasure, targetMeasure] using
      (hsource_survival (n + 1 : ℝ) hn).trans
        (htarget_survival (n + 1 : ℝ) hn).symm
  · have hx_pos : 0 < x.toReal := ENNReal.toReal_pos hx_zero hx_top
    rw [← ENNReal.ofReal_toReal hx_top]
    exact (hsource_survival x.toReal hx_pos).trans
      (htarget_survival x.toReal hx_pos).symm

@[blueprint "lem:scaled-unit-exponential-has-law"
  (statement := /-- Let $(\Omega,\mu)$ be a probability space and let $Y:\Omega\to\mathbb R$
  be a measurable random variable with the rate-one exponential law. For every $d>0$, the
  scaled variable $Y/d$ has the exponential law of rate $d$. -/)
  (proof := /-- The map $y\mapsto y/d$ is measurable. For every $x\in\mathbb R$, positivity
  of $d$ identifies the event $\{Y/d\leq x\}$ with $\{Y\leq dx\}$. The rate-one exponential
  cumulative distribution function at $dx$ equals the rate-$d$ exponential cumulative
  distribution function at $x$. Equality of the cumulative distribution functions therefore
  gives equality of the two laws. -/)
  (title := /-- Positive scaling of a unit exponential variable -/)
  (latexEnv := "lemma")]
lemma scaled_unit_exponential_has_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hYmeas : Measurable Y)
    (hYlaw : has_law Y (ProbabilityTheory.expMeasure 1) μ) (d : ℝ) (hd : 0 < d) :
    has_law (fun ω ↦ Y ω / d) (ProbabilityTheory.expMeasure d) μ := by
  have hscaled : Measurable (fun ω ↦ Y ω / d) := hYmeas.div_const d
  letI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.expMeasure d) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hd
  letI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  letI : MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.map (fun ω ↦ Y ω / d) μ) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hscaled.aemeasurable
  unfold has_law
  rw [← MeasureTheory.Measure.cdf_eq_iff]
  ext x
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real,
    MeasureTheory.Measure.real, MeasureTheory.Measure.map_apply hscaled measurableSet_Iic]
  have hpre : (fun ω ↦ Y ω / d) ⁻¹' Set.Iic x = Y ⁻¹' Set.Iic (d * x) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic]
    rw [div_le_iff₀ hd, mul_comm]
  rw [hpre, ← MeasureTheory.Measure.map_apply hYmeas measurableSet_Iic, hYlaw,
    ]
  change (ProbabilityTheory.expMeasure 1).real (Set.Iic (d * x)) =
    (ProbabilityTheory.expMeasure d).real (Set.Iic x)
  rw [← ProbabilityTheory.cdf_eq_real, ← ProbabilityTheory.cdf_eq_real,
    ProbabilityTheory.cdf_expMeasure_eq (r := 1) (by norm_num),
    ProbabilityTheory.cdf_expMeasure_eq (r := d) hd]
  by_cases hx : 0 ≤ x
  · simp [hx, mul_nonneg hd.le hx]
  · have hdx : ¬ 0 ≤ d * x := by nlinarith
    simp [hx, hdx]

@[blueprint "lem:exponential-survival-of-has-law"
  (statement := /-- Let $(\Omega,\mu)$ be a probability space, let $r>0$, and let
  $X:\Omega\to\mathbb R$ be measurable with exponential law of rate $r$. Then for every
  $x\in\mathbb R$, the probability of $X>x$ is $e^{-rx}$ when $x\geq0$ and is one when
  $x<0$. -/)
  (proof := /-- The event $\{X>x\}$ is the complement of $\{X\leq x\}$. The law of $X$
  identifies the latter probability with the cumulative distribution function of the
  rate-$r$ exponential measure. Substituting its explicit formula and taking the complement
  yields the asserted two cases. -/)
  (title := /-- Survival function of an exponential variable -/)
  (latexEnv := "lemma")]
lemma exponential_survival_of_has_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXmeas : Measurable X) (r : ℝ) (hr : 0 < r)
    (hXlaw : has_law X (ProbabilityTheory.expMeasure r) μ) (x : ℝ) :
    μ.real {ω | x < X ω} = if 0 ≤ x then Real.exp (-(r * x)) else 1 := by
  letI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.expMeasure r) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hr
  have hset : {ω | x < X ω} = {ω | X ω ≤ x}ᶜ := by
    ext ω
    simp
  have hle_meas : MeasurableSet {ω | X ω ≤ x} := hXmeas measurableSet_Iic
  rw [hset, MeasureTheory.probReal_compl_eq_one_sub hle_meas]
  have hcdf : μ.real {ω | X ω ≤ x} =
      ProbabilityTheory.cdf (ProbabilityTheory.expMeasure r) x := by
    rw [ProbabilityTheory.cdf_eq_real]
    change μ.real (X ⁻¹' Set.Iic x) =
      (ProbabilityTheory.expMeasure r).real (Set.Iic x)
    unfold MeasureTheory.Measure.real
    rw [← MeasureTheory.Measure.map_apply hXmeas measurableSet_Iic, hXlaw]
  rw [hcdf, ProbabilityTheory.cdf_expMeasure_eq hr]
  by_cases hx : 0 ≤ x <;> simp [hx]

@[blueprint "lem:finite-infimum-exponentials-has-law"
  (statement := /-- Let $s$ be a nonempty finite index set and let $(X_i)_{i\in s}$ be
  mutually independent measurable exponential variables with positive rates $(r_i)_{i\in s}$.
  Then their pointwise infimum has the exponential law of rate $\sum_{i\in s}r_i$. -/)
  (proof := /-- For each threshold $x$, the event that the finite infimum exceeds $x$ is the
  intersection of the events $\{X_i>x\}$. Mutual independence factors its probability into
  the product of the individual survival probabilities. By
  \cref{lem:exponential-survival-of-has-law}, this product is one for $x<0$ and is
  $\prod_i e^{-r_i x}=e^{-x\sum_i r_i}$ for $x\geq0$. Taking complements gives the
  cumulative distribution function of an exponential variable of rate $\sum_i r_i$, and
  equality of cumulative distribution functions gives the asserted law. -/)
  (title := /-- Minimum of finitely many independent exponentials -/)
  (latexEnv := "lemma")]
lemma finite_infimum_exponentials_has_law {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (s : Finset ι) (hs : s.Nonempty) (X : ι → Ω → ℝ) (rates : ι → ℝ)
    (hXmeas : ∀ i ∈ s, Measurable (X i))
    (hrates : ∀ i ∈ s, 0 < rates i)
    (hXlaw : ∀ i ∈ s, has_law (X i) (ProbabilityTheory.expMeasure (rates i)) μ)
    (hXindep : ProbabilityTheory.iIndepFun X μ) :
    has_law (fun ω ↦ s.inf' hs (fun i ↦ X i ω))
      (ProbabilityTheory.expMeasure (∑ i ∈ s, rates i)) μ := by
  classical
  have hr_sum : 0 < ∑ i ∈ s, rates i :=
    Finset.sum_pos (fun i hi ↦ hrates i hi) hs
  have hmin_meas_general : ∀ (u : Finset ι) (hu : u.Nonempty),
      (∀ i ∈ u, Measurable (X i)) →
        Measurable (fun ω ↦ u.inf' hu (fun i ↦ X i ω)) := by
    intro u hu hmeas
    induction u using Finset.induction_on with
    | empty => simp at hu
    | @insert a u ha ih =>
        by_cases hu' : u.Nonempty
        · simpa [Finset.inf'_insert, hu'] using
            (hmeas a (by simp)).min
              (ih hu' (fun i hi ↦ hmeas i (by simp [hi])))
        · have hu_empty : u = ∅ := Finset.not_nonempty_iff_eq_empty.mp hu'
          subst u
          simpa using hmeas a (by simp)
  have hmin_meas : Measurable (fun ω ↦ s.inf' hs (fun i ↦ X i ω)) := by
    exact hmin_meas_general s hs hXmeas
  letI : MeasureTheory.IsProbabilityMeasure
      (ProbabilityTheory.expMeasure (∑ i ∈ s, rates i)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hr_sum
  letI : MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.map (fun ω ↦ s.inf' hs (fun i ↦ X i ω)) μ) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hmin_meas.aemeasurable
  unfold has_law
  rw [← MeasureTheory.Measure.cdf_eq_iff]
  ext x
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
  unfold MeasureTheory.Measure.real
  rw [MeasureTheory.Measure.map_apply hmin_meas measurableSet_Iic]
  change μ.real {ω | s.inf' hs (fun i ↦ X i ω) ≤ x} =
    (ProbabilityTheory.expMeasure (∑ i ∈ s, rates i)).real (Set.Iic x)
  have hle_meas : MeasurableSet {ω | s.inf' hs (fun i ↦ X i ω) ≤ x} :=
    hmin_meas measurableSet_Iic
  have hcompl : {ω | s.inf' hs (fun i ↦ X i ω) ≤ x}ᶜ =
      ⋂ i ∈ s, {ω | x < X i ω} := by
    ext ω
    simp
  have hfactor := hXindep.meas_biInter (S := s)
    (s := fun i ↦ {ω | x < X i ω}) (by
      intro i hi
      change @MeasurableSet Ω (MeasurableSpace.comap (X i) inferInstance)
        (X i ⁻¹' Set.Ioi x)
      exact ⟨Set.Ioi x, measurableSet_Ioi, rfl⟩)
  have hfactor_real : μ.real (⋂ i ∈ s, {ω | x < X i ω}) =
      ∏ i ∈ s, μ.real {ω | x < X i ω} := by
    unfold MeasureTheory.Measure.real
    rw [hfactor, ENNReal.toReal_prod]
  have hcomplement_probability :
      μ.real {ω | s.inf' hs (fun i ↦ X i ω) ≤ x} =
        1 - μ.real (⋂ i ∈ s, {ω | x < X i ω}) := by
    have h := MeasureTheory.probReal_compl_eq_one_sub (μ := μ) hle_meas
    rw [hcompl] at h
    linarith
  rw [hcomplement_probability, hfactor_real]
  have hprod_surv : (∏ i ∈ s, μ.real {ω | x < X i ω}) =
      ∏ i ∈ s, if 0 ≤ x then Real.exp (-(rates i * x)) else 1 := by
    apply Finset.prod_congr rfl
    intro i hi
    exact exponential_survival_of_has_law μ (X i) (hXmeas i hi)
      (rates i) (hrates i hi) (hXlaw i hi) x
  rw [hprod_surv]
  rw [← ProbabilityTheory.cdf_eq_real,
    ProbabilityTheory.cdf_expMeasure_eq hr_sum]
  by_cases hx : 0 ≤ x
  · simp only [if_pos hx]
    rw [← Real.exp_sum]
    congr 2
    rw [Finset.sum_neg_distrib, Finset.sum_mul]
  · simp [hx]

@[blueprint "lem:active-update-priority-infimum-has-law"
  (statement := /-- Fix a nonempty set of active updates to one coordinate. The infimum of
  their priorities $Y_i/\Delta_i$ has the exponential law whose rate is the sum of their
  positive increments. -/)
  (proof := /-- Each noise variable has the unit exponential law, so
  \cref{lem:scaled-unit-exponential-has-law} gives the exponential law of rate $\Delta_i$
  for $Y_i/\Delta_i$. The noise subfamily remains mutually independent under coordinatewise
  positive scaling. Applying \cref{lem:finite-infimum-exponentials-has-law} to the active
  index set gives the result. -/)
  (title := /-- Law of the minimum active-update priority -/)
  (latexEnv := "lemma")]
lemma active_update_priority_infimum_has_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (updates : List (incremental_update n))
    (source : pareto_random_source Ω n updates.length μ) (t : ℕ) (v : Fin n)
    (hs : (active_update_indices updates t v).Nonempty) :
    has_law
      (fun ω ↦ (active_update_indices updates t v).inf' hs
        (fun i ↦ source.noise i ω / (updates.get i).increment))
      (ProbabilityTheory.expMeasure
        (∑ i ∈ active_update_indices updates t v, (updates.get i).increment)) μ := by
  apply finite_infimum_exponentials_has_law μ
  · intro i hi
    exact (source.noise_measurable i).div_const (updates.get i).increment
  · intro i hi
    exact (updates.get i).increment_pos
  · intro i hi
    exact scaled_unit_exponential_has_law μ (source.noise i) (source.noise_measurable i)
      (source.noise_exponential i) (updates.get i).increment
        (updates.get i).increment_pos
  · have hnoise : ProbabilityTheory.iIndepFun source.noise μ := by
      simpa using source.jointly_independent.precomp Sum.inr_injective
    simpa [Function.comp_def] using hnoise.comp
      (fun i y ↦ y / (updates.get i).increment)
      (fun i ↦ measurable_id.div_const (updates.get i).increment)

@[blueprint "lem:measurable-finite-infimum"
  (statement := /-- The pointwise infimum of a nonempty finite family of measurable
  real-valued functions is measurable. -/)
  (proof := /-- Induct on the finite index set. A singleton infimum is its sole function,
  while adjoining an index to a nonempty family replaces the infimum by the pointwise
  minimum of two measurable functions. -/)
  (title := /-- Measurability of a finite pointwise infimum -/)
  (latexEnv := "lemma")]
lemma measurable_finite_infimum {Ω ι : Type*} [MeasurableSpace Ω]
    (s : Finset ι) (hs : s.Nonempty) (X : ι → Ω → ℝ)
    (hXmeas : ∀ i ∈ s, Measurable (X i)) :
    Measurable (fun ω ↦ s.inf' hs (fun i ↦ X i ω)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
      by_cases hs' : s.Nonempty
      · simpa [Finset.inf'_insert, hs'] using
          (hXmeas a (by simp)).min
            (ih hs' (fun i hi ↦ hXmeas i (by simp [hi])))
      · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
        subst s
        simpa using hXmeas a (by simp)

@[blueprint "lem:active-priority-infimum-independent-hash"
  (statement := /-- For a nonempty active-update set of a coordinate $v$, the infimum of
  its scaled noise priorities is independent of the hash value $H(v)$. -/)
  (proof := /-- The active noises and the hash variable $H(v)$ form disjoint subfamilies of
  the jointly independent Pareto random source. Hence the corresponding finite noise tuple
  and singleton hash tuple are independent. The priority infimum is a measurable function of
  the former tuple by \cref{lem:measurable-finite-infimum}, and evaluation at $v$ is a
  measurable function of the latter. Measurable images of independent variables remain
  independent. -/)
  (title := /-- Independence of a coordinate priority and its hash -/)
  (latexEnv := "lemma")]
lemma active_priority_infimum_independent_hash {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) {n : ℕ} (updates : List (incremental_update n))
    (source : pareto_random_source Ω n updates.length μ) (t : ℕ) (v : Fin n)
    (hs : (active_update_indices updates t v).Nonempty) :
    ProbabilityTheory.IndepFun
      (fun ω ↦ (active_update_indices updates t v).inf' hs
        (fun i ↦ source.noise i ω / (updates.get i).increment))
      (source.hash v) μ := by
  classical
  let s := active_update_indices updates t v
  let S : Finset (Sum (Fin n) (Fin updates.length)) := s.image Sum.inr
  let T : Finset (Sum (Fin n) (Fin updates.length)) := {Sum.inl v}
  have hdisjoint : Disjoint S T := by
    simp [S, T]
  have hbase := source.jointly_independent.indepFun_finset S T hdisjoint
    (by
      intro j
      cases j with
      | inl w => exact source.hash_measurable w
      | inr i => exact source.noise_measurable i)
  let φ : (S → ℝ) → ℝ := fun z ↦ s.inf' hs
    (fun i ↦ if hi : i ∈ s then
      z ⟨Sum.inr i, Finset.mem_image.2 ⟨i, hi, rfl⟩⟩ / (updates.get i).increment
    else 0)
  let ψ : (T → ℝ) → ℝ := fun z ↦ z ⟨Sum.inl v, by simp [T]⟩
  have hφ : Measurable φ := by
    dsimp [φ]
    apply measurable_finite_infimum s hs
    intro i hi
    simp only [hi, dite_true]
    have heval : Measurable (fun z : S → ℝ ↦
        z ⟨Sum.inr i, Finset.mem_image.2 ⟨i, hi, rfl⟩⟩) := measurable_pi_apply _
    exact heval.div_const (updates.get i).increment
  have hψ : Measurable ψ := by
    exact measurable_pi_apply _
  have hleft :
      φ ∘ (fun a (j : S) ↦ Sum.elim source.hash source.noise (j :
        Sum (Fin n) (Fin updates.length)) a) =
        (fun ω ↦ (active_update_indices updates t v).inf' hs
          (fun i ↦ source.noise i ω / (updates.get i).increment)) := by
    funext ω
    dsimp [φ, Function.comp_def]
    apply Finset.inf'_congr hs rfl
    intro i hi
    simp [hi, S, s]
  have hright :
      ψ ∘ (fun a (j : T) ↦ Sum.elim source.hash source.noise (j :
        Sum (Fin n) (Fin updates.length)) a) = source.hash v := by
    funext ω
    simp [ψ, T, Function.comp_def]
  rw [← hleft, ← hright]
  exact hbase.comp hφ hψ

@[blueprint "lem:finite-minimum-monotone-transform"
  (statement := /-- Let $s$ be a nonempty finite set, let $a_i\in\mathbb R$, and let
  $\ell:\mathbb R^2\to\mathbb R_+\cup\{\infty\}$ be monotone. For fixed $b$, the minimum
  of the values $\ell(a_i,b)$ equals $\ell(\inf_{i\in s}a_i,b)$. -/)
  (proof := /-- The finite infimum is attained by some $a_j$, so its transform occurs among
  the values whose minimum defines the left-hand side. Conversely, the infimum is at most
  every $a_i$; monotonicity in the first coordinate makes its transform at most every
  $\ell(a_i,b)$. The two inequalities give equality. -/)
  (title := /-- A monotone map commutes with a finite minimum -/)
  (latexEnv := "lemma")]
lemma finite_minimum_monotone_transform {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℝ) (b : ℝ) (ell : ℝ × ℝ → ENNReal) (hell : Monotone ell) :
    finite_minimum_with_infinity s (fun i ↦ ell (a i, b)) =
      ell (s.inf' hs a, b) := by
  classical
  unfold finite_minimum_with_infinity
  rw [dif_pos hs]
  apply le_antisymm
  · rcases Finset.exists_mem_eq_inf' (s := s) hs a with ⟨i, hi, hmin⟩
    apply Finset.min'_le
    exact Finset.mem_image.2 ⟨i, hi, by rw [hmin]⟩
  · apply Finset.le_min'
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
    apply hell
    exact ⟨Finset.inf'_le _ hi, le_rfl⟩

@[blueprint "lem:coordinate-level-score-has-active-sum-law"
  (statement := /-- Under a valid level-function specification, the score of a fixed
  coordinate has the extended exponential law whose rate is $G$ applied to the sum of the
  coordinate's active increments. -/)
  (proof := /-- If there is no active update, the score is identically infinity and the
  increment sum is zero; the identity $G(0)=0$ gives the rate-zero extended exponential law.
  Otherwise, \cref{lem:active-update-priority-infimum-has-law} gives the exponential law of
  the raw priority infimum, \cref{lem:measurable-finite-infimum} gives its measurability, and
  \cref{lem:active-priority-infimum-independent-hash} makes it independent of the uniform
  coordinate hash. The level-function transformation property therefore gives the required
  law after \cref{lem:finite-minimum-monotone-transform} identifies the transformed infimum
  with the coordinate score. -/)
  (title := /-- Marginal law of a coordinate level score -/)
  (latexEnv := "lemma")]
lemma coordinate_level_score_has_active_sum_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (updates : List (incremental_update n))
    (source : pareto_random_source Ω n updates.length μ) (t : ℕ) (v : Fin n)
    (G : ℝ → ℝ) (ell : ℝ × ℝ → ENNReal) (hell : level_function_spec G ell) :
    has_law (fun ω ↦ coordinate_level_score updates μ source ell ω t v)
      (exponential_with_top
        (G (∑ i ∈ active_update_indices updates t v, (updates.get i).increment))) μ := by
  classical
  rcases hell with ⟨hell_meas, hell_mono, hell_law, hG_zero, hG_nonneg⟩
  by_cases hs : (active_update_indices updates t v).Nonempty
  · let r := ∑ i ∈ active_update_indices updates t v, (updates.get i).increment
    have hr : 0 < r := Finset.sum_pos
      (fun i hi ↦ (updates.get i).increment_pos) hs
    let q : Ω → ℝ := fun ω ↦ (active_update_indices updates t v).inf' hs
      (fun i ↦ source.noise i ω / (updates.get i).increment)
    have hq_meas : Measurable q := by
      apply measurable_finite_infimum
      intro i hi
      exact (source.noise_measurable i).div_const (updates.get i).increment
    have hq_law := active_update_priority_infimum_has_law μ updates source t v hs
    have hpair_meas : Measurable (fun ω ↦ (q ω, source.hash v ω)) :=
      hq_meas.prodMk (source.hash_measurable v)
    have hq_hash_indep := active_priority_infimum_independent_hash
      μ updates source t v hs
    have hpair_law : MeasureTheory.Measure.map (fun ω ↦ (q ω, source.hash v ω)) μ =
        (ProbabilityTheory.expMeasure r).prod
          (MeasureTheory.volume.restrict (Set.Ioc 0 1)) := by
      calc
        MeasureTheory.Measure.map (fun ω ↦ (q ω, source.hash v ω)) μ =
            (MeasureTheory.Measure.map q μ).prod
              (MeasureTheory.Measure.map (source.hash v) μ) :=
          hq_hash_indep.map_prod_eq_prod_map_map hq_meas.aemeasurable
            (source.hash_measurable v).aemeasurable
        _ = (ProbabilityTheory.expMeasure r).prod
              (MeasureTheory.volume.restrict (Set.Ioc 0 1)) := by
          rw [hq_law, source.hash_uniform v]
    have hscore : (fun ω ↦ coordinate_level_score updates μ source ell ω t v) =
        fun ω ↦ ell (q ω, source.hash v ω) := by
      funext ω
      exact finite_minimum_monotone_transform
        (active_update_indices updates t v) hs
        (fun i ↦ source.noise i ω / (updates.get i).increment)
        (source.hash v ω) ell hell_mono
    change has_law (fun ω ↦ coordinate_level_score updates μ source ell ω t v)
      (exponential_with_top (G r)) μ
    rw [hscore]
    unfold has_law
    calc
      MeasureTheory.Measure.map (fun ω ↦ ell (q ω, source.hash v ω)) μ =
          MeasureTheory.Measure.map ell
            (MeasureTheory.Measure.map (fun ω ↦ (q ω, source.hash v ω)) μ) :=
        (MeasureTheory.Measure.map_map hell_meas hpair_meas).symm
      _ = MeasureTheory.Measure.map ell
            ((ProbabilityTheory.expMeasure r).prod
              (MeasureTheory.volume.restrict (Set.Ioc 0 1))) := by rw [hpair_law]
      _ = exponential_with_top (G r) := hell_law r hr
  · have hs_empty : active_update_indices updates t v = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hs
    unfold has_law
    simp [coordinate_level_score, finite_minimum_with_infinity, hs_empty,
      exponential_with_top, hG_zero, MeasureTheory.Measure.map_const]

@[blueprint "lem:fold-incremental-updates-coordinate"
  (statement := /-- Folding a finite list of incremental updates over a vector changes a
  fixed coordinate by the sum of precisely the increments whose update index is that
  coordinate. -/)
  (proof := /-- Induct on the update list. The empty fold contributes zero. At a cons step,
  unfold the coordinate update: if the new update index is the chosen coordinate its
  increment is added, while otherwise that coordinate is unchanged; the induction
  hypothesis accounts for the remaining updates. -/)
  (title := /-- Coordinate formula for a folded update list -/)
  (latexEnv := "lemma")]
lemma fold_incremental_updates_coordinate {n : ℕ} (updates : List (incremental_update n))
    (x : Fin n → ℝ) (v : Fin n) :
    updates.foldl apply_incremental_update x v =
      x v + (updates.map fun u ↦ if u.index = v then u.increment else 0).sum := by
  induction updates generalizing x with
  | nil => simp
  | cons u updates ih =>
      rw [List.foldl_cons, ih]
      by_cases huv : u.index = v
      · subst v
        simp [apply_incremental_update]
        ring
      · have hvu : v ≠ u.index := Ne.symm huv
        simp [apply_incremental_update, huv, hvu]

@[blueprint "lem:sum-indexed-prefix"
  (statement := /-- Summing a function of list entries over indices smaller than $t$ equals
  summing that function over the list prefix obtained by taking the first $t$ entries. -/)
  (proof := /-- Induct simultaneously on the list and on $t$. The empty-list and zero-prefix
  cases are immediate. In the successor case, split the finite-index sum into its zeroth
  term and the sum over successor indices, then apply the induction hypothesis to the tail. -/)
  (title := /-- Index sum over a list prefix -/)
  (latexEnv := "lemma")]
lemma sum_indexed_prefix {α : Type*} (updates : List α) (t : ℕ) (f : α → ℝ) :
    (∑ i : Fin updates.length, if i.val < t then f (updates.get i) else 0) =
      ((updates.take t).map f).sum := by
  induction updates generalizing t with
  | nil => simp
  | cons u updates ih =>
      cases t with
      | zero => simp
      | succ t =>
          simpa [Fin.sum_univ_succ] using
            congrArg (fun z : ℝ ↦ f u + z) (ih t)

@[blueprint "lem:stream-coordinate-equals-active-increment-sum"
  (statement := /-- At every time $t$, a coordinate of the stream vector equals the sum of
  the increments among the active updates to that coordinate. -/)
  (proof := /-- By \cref{lem:fold-incremental-updates-coordinate}, the coordinate of the
  folded prefix is the sum of the increments in that prefix whose index is the chosen
  coordinate. The index-prefix identity \cref{lem:sum-indexed-prefix} rewrites this list sum
  as the sum over the filtered finite set defining the active update indices. -/)
  (title := /-- Stream coordinate as a sum of active increments -/)
  (latexEnv := "lemma")]
lemma stream_coordinate_equals_active_increment_sum {n : ℕ}
    (updates : List (incremental_update n)) (t : ℕ) (v : Fin n) :
    stream_vector updates t v =
      ∑ i ∈ active_update_indices updates t v, (updates.get i).increment := by
  rw [show (∑ i ∈ active_update_indices updates t v, (updates.get i).increment) =
      ∑ i : Fin updates.length, if i.val < t then
        (if (updates.get i).index = v then (updates.get i).increment else 0) else 0 by
    unfold active_update_indices
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hit : i.val < t <;> by_cases hiv : (updates.get i).index = v <;>
      simp [hit, hiv]]
  rw [sum_indexed_prefix updates t
    (fun u ↦ if u.index = v then u.increment else 0)]
  unfold stream_vector
  rw [fold_incremental_updates_coordinate]
  simp

@[blueprint "lem:mutual-independence-from-finite-complement-independence"
  (statement := /-- Let $(\mathcal M_i)_{i\in I}$ be sigma-algebras on a probability space.
  If, for every $i$ and finite $S\subseteq I\setminus\{i\}$, $\mathcal M_i$ is independent
  of $\bigvee_{j\in S}\mathcal M_j$, then the family $(\mathcal M_i)_{i\in I}$ is mutually
  independent. -/)
  (proof := /-- Use the finite-intersection characterization of mutual independence and
  induct on the finite set of indices. At an insertion step, the new measurable event is
  independent of the intersection of the previous events because that intersection is
  measurable in the join of their sigma-algebras. Factor its probability and apply the
  induction hypothesis to the remaining intersection. -/)
  (title := /-- Mutual independence from independence of finite complements -/)
  (latexEnv := "lemma")]
lemma mutual_independence_from_finite_complement_independence
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (m : ι → MeasurableSpace Ω)
    (hsep : ∀ i (s : Finset ι), i ∉ s →
      ProbabilityTheory.Indep (m i) (⨆ j ∈ s, m j) μ) :
    ProbabilityTheory.iIndep m μ := by
  classical
  rw [ProbabilityTheory.iIndep_iff]
  intro s f hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hfi : @MeasurableSet Ω (m i) (f i) := hf i (by simp)
      have hrest : @MeasurableSet Ω (⨆ j ∈ s, m j) (⋂ j ∈ s, f j) := by
        apply Finset.measurableSet_biInter s
        intro j hj
        have hle : m j ≤ ⨆ k ∈ s, m k := by
          calc
            m j ≤ ⨆ (_ : j ∈ s), m j := le_iSup (fun _ : j ∈ s ↦ m j) hj
            _ ≤ ⨆ k, ⨆ (_ : k ∈ s), m k := le_iSup (fun k ↦ ⨆ (_ : k ∈ s), m k) j
        exact hle (f j) (hf j (by simp [hj]))
      have hind := hsep i s hi
      have hset_indep := hind.indepSet_of_measurableSet hfi hrest
      have hfactor := hset_indep.measure_inter_eq_mul
      rw [Finset.prod_insert hi]
      rw [show (⋂ j ∈ insert i s, f j) = f i ∩ ⋂ j ∈ s, f j by
        simp [hi]]
      rw [hfactor, ih (fun j hj ↦ hf j (by simp [hj]))]

@[blueprint "lem:grouped-independent-fibers"
  (statement := /-- Let $(\mathcal M_i)_{i\in I}$ be mutually independent sigma-algebras
  and let $o:I\to K$ assign each index to one owner. For each $k\in K$, join the
  sigma-algebras in the fiber $o^{-1}(k)$. The resulting fiber sigma-algebras are mutually
  independent. -/)
  (proof := /-- For a fixed owner $k$ and finite set $S$ of other owners, the fiber
  $o^{-1}(k)$ is disjoint from the union of the fibers over $S$.
  The independence-of-disjoint-joins theorem makes the corresponding two joins independent.
  Rearranging iterated joins identifies the second join with the join of the fiber
  sigma-algebras indexed by $S$. Apply
  \cref{lem:mutual-independence-from-finite-complement-independence}. -/)
  (title := /-- Grouping independent sigma-algebras by disjoint fibers -/)
  (latexEnv := "lemma")]
lemma grouped_independent_fibers {Ω ι κ : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (m : ι → MeasurableSpace Ω) (owner : ι → κ)
    (hm_le : ∀ i, m i ≤ (inferInstance : MeasurableSpace Ω))
    (hm_indep : ProbabilityTheory.iIndep m μ) :
    ProbabilityTheory.iIndep (fun k ↦ ⨆ i, ⨆ (_ : owner i = k), m i) μ := by
  apply mutual_independence_from_finite_complement_independence μ
  intro k s hk
  have hdisjoint : Disjoint {i | owner i = k} {i | owner i ∈ s} := by
    rw [Set.disjoint_left]
    intro i hik his
    exact hk (hik ▸ his)
  have hbase := ProbabilityTheory.indep_iSup_of_disjoint hm_le hm_indep hdisjoint
  have hright : (⨆ i, ⨆ (_ : owner i ∈ s), m i) =
      ⨆ w ∈ s, ⨆ i, ⨆ (_ : owner i = w), m i := by
    apply le_antisymm
    · refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
      exact le_iSup_of_le (owner i) (le_iSup_of_le hi
        (le_iSup_of_le i (le_iSup_of_le rfl le_rfl)))
    · refine iSup_le fun w ↦ iSup_le fun hw ↦ iSup_le fun i ↦ iSup_le fun hi ↦ ?_
      exact le_iSup_of_le i (le_iSup_of_le (hi ▸ hw) le_rfl)
  rw [← hright]
  exact hbase

@[blueprint "lem:coordinate-level-scores-independent"
  (statement := /-- For every stream prefix and measurable monotone level function, the
  coordinate level scores form a mutually independent family. -/)
  (proof := /-- Assign each primitive random variable to its coordinate: $H(v)$ is assigned
  to $v$, and $Y_i$ is assigned to the index updated at step $i$. The fibers are disjoint, so
  \cref{lem:grouped-independent-fibers} makes their generated sigma-algebras mutually
  independent. For a coordinate with active updates, its raw priority infimum is measurable
  in its fiber by \cref{lem:measurable-finite-infimum}; its hash is measurable in the same
  fiber, and \cref{lem:finite-minimum-monotone-transform} expresses the score as the
  measurable level function of this pair. An inactive score is constant. Thus every score's
  pullback sigma-algebra lies below its independent coordinate fiber, which proves mutual
  independence of the scores. -/)
  (title := /-- Independence of coordinate level scores -/)
  (latexEnv := "lemma")]
lemma coordinate_level_scores_independent {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (updates : List (incremental_update n))
    (source : pareto_random_source Ω n updates.length μ) (t : ℕ)
    (ell : ℝ × ℝ → ENNReal) (hell_meas : Measurable ell) (hell_mono : Monotone ell) :
    ProbabilityTheory.iIndepFun
      (fun v ω ↦ coordinate_level_score updates μ source ell ω t v) μ := by
  classical
  let F : Sum (Fin n) (Fin updates.length) → Ω → ℝ :=
    Sum.elim source.hash source.noise
  let owner : Sum (Fin n) (Fin updates.length) → Fin n :=
    Sum.elim id (fun i ↦ (updates.get i).index)
  let m : Sum (Fin n) (Fin updates.length) → MeasurableSpace Ω :=
    fun j ↦ (inferInstance : MeasurableSpace ℝ).comap (F j)
  let group : Fin n → MeasurableSpace Ω :=
    fun v ↦ ⨆ j, ⨆ (_ : owner j = v), m j
  have hm_le : ∀ j, m j ≤ (inferInstance : MeasurableSpace Ω) := by
    intro j
    apply Measurable.comap_le
    cases j with
    | inl v => exact source.hash_measurable v
    | inr i => exact source.noise_measurable i
  have hm_indep : ProbabilityTheory.iIndep m μ := by
    exact source.jointly_independent.iIndep
  have hgroup : ProbabilityTheory.iIndep group μ := by
    exact grouped_independent_fibers μ m owner hm_le hm_indep
  apply ProbabilityTheory.iIndep_of_iIndep_of_le hgroup
  intro v
  apply Measurable.comap_le
  change @Measurable Ω ENNReal (group v) inferInstance
    (fun ω ↦ coordinate_level_score updates μ source ell ω t v)
  by_cases hs : (active_update_indices updates t v).Nonempty
  · let q : Ω → ℝ := fun ω ↦ (active_update_indices updates t v).inf' hs
      (fun i ↦ source.noise i ω / (updates.get i).increment)
    have hhash_group : @Measurable Ω ℝ (group v) inferInstance (source.hash v) := by
      apply Measurable.of_comap_le
      change m (Sum.inl v) ≤ group v
      exact le_iSup_of_le (Sum.inl v) (le_iSup_of_le rfl le_rfl)
    have hq_group : @Measurable Ω ℝ (group v) inferInstance q := by
      refine @measurable_finite_infimum Ω (Fin updates.length) (group v)
        (active_update_indices updates t v) hs
        (fun i ω ↦ source.noise i ω / (updates.get i).increment) ?_
      intro i hi
      have hindex : (updates.get i).index = v := by
        have hactive : i.val < t ∧ (updates.get i).index = v := by
          simpa [active_update_indices] using hi
        exact hactive.2
      have hnoise_group : @Measurable Ω ℝ (group v) inferInstance
          (source.noise i) := by
        apply Measurable.of_comap_le
        change m (Sum.inr i) ≤ group v
        exact le_iSup_of_le (Sum.inr i) (le_iSup_of_le hindex le_rfl)
      exact hnoise_group.div_const (updates.get i).increment
    have hscore : (fun ω ↦ coordinate_level_score updates μ source ell ω t v) =
        fun ω ↦ ell (q ω, source.hash v ω) := by
      funext ω
      exact finite_minimum_monotone_transform
        (active_update_indices updates t v) hs
        (fun i ↦ source.noise i ω / (updates.get i).increment)
        (source.hash v ω) ell hell_mono
    rw [hscore]
    exact hell_meas.comp (hq_group.prodMk hhash_group)
  · have hs_empty : active_update_indices updates t v = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hs
    simp [coordinate_level_score, finite_minimum_with_infinity, hs_empty]

@[blueprint "lem:update-scores-form-exponential-race"
  (statement := /-- Let $(\Omega,\mu)$ be a probability space, let $n\in\mathbb N$, let
  $(u_i)$ be a finite incremental-update stream on $[n]$, and equip the stream with a Pareto
  random source on $(\Omega,\mu)$. For every time $t\in\mathbb N$, function
  $G:\mathbb R\to\mathbb R$, and level function $\ell:\mathbb R^2\to
  \mathbb R_+\cup\{\infty\}$ satisfying the level-function specification for $G$, the
  coordinate scores are mutually independent. For every $v\in[n]$, the score has the
  extended exponential law of rate $G(x_t(v))$, and this rate is nonnegative. -/)
  (proof := /-- By \cref{lem:stream-coordinate-equals-active-increment-sum}, the value
  $x_t(v)$ is the sum of the positive increments active at coordinate $v$.
  Hence \cref{lem:coordinate-level-score-has-active-sum-law} gives the extended exponential
  law of the coordinate score with rate $G(x_t(v))$. The scores are mutually independent by
  \cref{lem:coordinate-level-scores-independent}. Finally, the active-increment formula makes
  every $x_t(v)$ nonnegative, so the nonnegativity clause of the level-function specification
  gives $G(x_t(v))\geq0$ for every coordinate. -/)
  (title := /-- Coordinate scores are an exponential race -/)
  (latexEnv := "lemma")]
lemma update_scores_form_exponential_race {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (updates : List (incremental_update n))
    (source : pareto_random_source Ω n updates.length μ) (t : ℕ)
    (G : ℝ → ℝ) (ell : ℝ × ℝ → ENNReal) (hell : level_function_spec G ell) :
    exponential_race_family μ (fun v ↦ G (stream_vector updates t v))
      (fun v ω ↦ coordinate_level_score updates μ source ell ω t v) := by
  rcases hell with ⟨hell_meas, hell_mono, hell_law, hG_zero, hG_nonneg⟩
  refine ⟨?_, ?_, ?_⟩
  · intro v
    change has_law (fun ω ↦ coordinate_level_score updates μ source ell ω t v)
      (exponential_with_top (G (stream_vector updates t v))) μ
    rw [stream_coordinate_equals_active_increment_sum]
    exact coordinate_level_score_has_active_sum_law μ updates source t v G ell
      ⟨hell_meas, hell_mono, hell_law, hG_zero, hG_nonneg⟩
  · exact coordinate_level_scores_independent μ updates source t ell hell_meas hell_mono
  · intro v
    apply hG_nonneg
    rw [stream_coordinate_equals_active_increment_sum]
    exact Finset.sum_nonneg fun i hi ↦ (updates.get i).increment_pos.le

@[blueprint "lem:exponential-race-selects-proportionally"
  (statement := /-- Let $(\Omega,\Sigma,\mu)$ be a probability space and let $n\in\mathbb N$.
  Suppose that the scores $S_v:\Omega\to\overline{\mathbb R}_{\geq0}$ form an exponential
  race with real rates $(r_v)_{v\in[n]}$ in the sense of
  \cref{def:exponential-race-family}, and that $\sum_{u\in[n]}r_u>0$. If
  $V_*:\Omega\to[n]$ satisfies $S_{V_*(\omega)}(\omega)\leq S_v(\omega)$ for every
  $\omega\in\Omega$ and $v\in[n]$, then
  $\mu\{\omega:V_*(\omega)=v\}=r_v/\sum_{u\in[n]}r_u$ for every $v\in[n]$. -/)
  (proof := /-- The independence and marginal-law clauses of
  \cref{def:exponential-race-family} identify the joint score law with the product of the
  coordinate laws. For a coordinate $v$ of positive rate, split this product into the
  $v$-coordinate and all remaining coordinates. At a value $s\geq0$, the latter coordinates
  all exceed $s$ with probability $\prod_{u\ne v}e^{-r_us}$, while the $v$-coordinate has
  density $r_ve^{-r_vs}$. Integration therefore gives
  $\int_0^\infty r_ve^{-s\sum_u r_u}\,ds=r_v/\sum_u r_u$ for the strict-winner event of
  $v$. If $r_v=0$, then its law is the Dirac mass at $\infty$ by
  \cref{def:exponential-with-top}; since the positive total rate supplies another coordinate
  of positive rate, the strict-winner event of $v$ has measure zero. Hence every strict-winner
  event has measure $r_v/\sum_u r_u$. These events are pairwise disjoint, and their measures
  sum to one, so almost every outcome has a unique strict winner. On this full-measure union,
  the pointwise minimum property forces the selector to equal that winner. Thus the selector
  event and the corresponding strict-winner event agree almost everywhere, yielding the
  asserted real-valued probability. -/)
  (title := /-- Winner law for an exponential race -/)
  (latexEnv := "lemma")]
lemma exponential_race_selects_proportionally {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (rates : Fin n → ℝ) (scores : Fin n → Ω → ENNReal)
    (htotal : 0 < ∑ u, rates u) (hrace : exponential_race_family μ rates scores)
    (out : Ω → Fin n)
    (hout : ∀ ω v, scores (out ω) ω ≤ scores v ω) :
    ∀ v, μ.real {ω | out ω = v} = rates v / ∑ u, rates u := by
  classical
  have expMeasure_real_Ioi (r t : ℝ) (hr : 0 < r) :
      (ProbabilityTheory.expMeasure r).real (Set.Ioi t) =
        if 0 ≤ t then Real.exp (-(r * t)) else 1 := by
    letI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.expMeasure r) :=
      ProbabilityTheory.isProbabilityMeasure_expMeasure hr
    rw [show Set.Ioi t = (Set.Iic t)ᶜ by ext; simp]
    rw [MeasureTheory.probReal_compl_eq_one_sub measurableSet_Iic]
    rw [← ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_expMeasure_eq hr]
    split_ifs <;> ring
  have exponential_with_top_Ioi (r t : ℝ) (hr : 0 < r) (ht : 0 ≤ t) :
      exponential_with_top r (Set.Ioi (ENNReal.ofReal t)) =
        ENNReal.ofReal (Real.exp (-(r * t))) := by
    letI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.expMeasure r) :=
      ProbabilityTheory.isProbabilityMeasure_expMeasure hr
    rw [exponential_with_top, if_pos hr]
    rw [MeasureTheory.Measure.map_apply_of_aemeasurable
      ENNReal.measurable_ofReal.aemeasurable measurableSet_Ioi]
    rw [show ENNReal.ofReal ⁻¹' Set.Ioi (ENNReal.ofReal t) = Set.Ioi t by
      ext x
      simp [ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht]]
    rw [← MeasureTheory.ofReal_measureReal]
    rw [expMeasure_real_Ioi r t hr, if_pos ht]
  have exponential_with_top_Ioi_nonneg (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
      exponential_with_top r (Set.Ioi (ENNReal.ofReal t)) =
        ENNReal.ofReal (Real.exp (-(r * t))) := by
    rcases hr.eq_or_lt with rfl | hr
    · simp [exponential_with_top]
    · exact exponential_with_top_Ioi r t hr ht
  have expMeasure_real_singleton (r t : ℝ) :
      (ProbabilityTheory.expMeasure r).real {t} = 0 := by
    simp [MeasureTheory.Measure.real, ProbabilityTheory.expMeasure,
      ProbabilityTheory.gammaMeasure]
  have expMeasure_real_Ici (r t : ℝ) (hr : 0 < r) :
      (ProbabilityTheory.expMeasure r).real (Set.Ici t) =
        if 0 ≤ t then Real.exp (-(r * t)) else 1 := by
    letI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.expMeasure r) :=
      ProbabilityTheory.isProbabilityMeasure_expMeasure hr
    rw [show Set.Ici t = Set.Ioi t ∪ {t} by ext x; simp [le_iff_lt_or_eq]]
    rw [MeasureTheory.measureReal_union (μ := ProbabilityTheory.expMeasure r)
      (s₁ := Set.Ioi t) (s₂ := {t})
      (Set.disjoint_left.2 (by intro x htx hxt; exact (ne_of_gt htx) hxt))
      (measurableSet_singleton t)]
    rw [expMeasure_real_Ioi r t hr, expMeasure_real_singleton r t, add_zero]
  have exponential_with_top_Ici (r t : ℝ) (hr : 0 < r) (ht : 0 ≤ t) :
      exponential_with_top r (Set.Ici (ENNReal.ofReal t)) =
        ENNReal.ofReal (Real.exp (-(r * t))) := by
    letI : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.expMeasure r) :=
      ProbabilityTheory.isProbabilityMeasure_expMeasure hr
    rcases ht.eq_or_lt with rfl | ht
    · rw [exponential_with_top, if_pos hr]
      rw [show Set.Ici (ENNReal.ofReal 0) = Set.univ by ext x; simp]
      rw [MeasureTheory.Measure.map_apply_of_aemeasurable
        ENNReal.measurable_ofReal.aemeasurable MeasurableSet.univ]
      simp
    · rw [exponential_with_top, if_pos hr]
      rw [MeasureTheory.Measure.map_apply_of_aemeasurable
        ENNReal.measurable_ofReal.aemeasurable measurableSet_Ici]
      rw [show ENNReal.ofReal ⁻¹' Set.Ici (ENNReal.ofReal t) = Set.Ici t by
        ext x
        rw [Set.mem_preimage, Set.mem_Ici, Set.mem_Ici,
          ENNReal.ofReal_le_ofReal_iff']
        exact or_iff_left (not_le_of_gt ht)]
      rw [← MeasureTheory.ofReal_measureReal]
      rw [expMeasure_real_Ici r t hr, if_pos ht.le]
  have exponential_with_top_Ici_nonneg (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
      exponential_with_top r (Set.Ici (ENNReal.ofReal t)) =
        ENNReal.ofReal (Real.exp (-(r * t))) := by
    rcases hr.eq_or_lt with rfl | hr
    · simp [exponential_with_top]
    · exact exponential_with_top_Ici r t hr ht
  have exponential_with_top_isProbabilityMeasure (r : ℝ) (hr : 0 ≤ r) :
      MeasureTheory.IsProbabilityMeasure (exponential_with_top r) := by
    constructor
    rcases hr.eq_or_lt with rfl | hr
    · simp [exponential_with_top]
    · rw [exponential_with_top, if_pos hr]
      rw [MeasureTheory.Measure.map_apply_of_aemeasurable
        ENNReal.measurable_ofReal.aemeasurable MeasurableSet.univ]
      exact (ProbabilityTheory.isProbabilityMeasure_expMeasure hr).measure_univ
  have product_exponential_tail (s : Finset (Fin n)) (t : ℝ) (ht : 0 ≤ t) :
      ∏ u ∈ s, exponential_with_top (rates u) (Set.Ioi (ENNReal.ofReal t)) =
        ENNReal.ofReal (Real.exp (-((∑ u ∈ s, rates u) * t))) := by
    simp_rw [exponential_with_top_Ioi_nonneg _ _ (hrace.2.2 _) ht]
    rw [← ENNReal.ofReal_prod_of_nonneg
      (fun u hu ↦ Real.exp_nonneg (-((rates u) * t)))]
    rw [← Real.exp_sum]
    congr 2
    rw [Finset.sum_neg_distrib, Finset.sum_mul]
  have pi_strict_winner (v : Fin n) (hv : 0 < rates v) :
      (MeasureTheory.Measure.pi (fun u ↦ exponential_with_top (rates u)))
          {x | ∀ u, u ≠ v → x v < x u} =
        ENNReal.ofReal (rates v / ∑ u, rates u) := by
    letI (u : Fin n) : MeasureTheory.IsProbabilityMeasure
        (exponential_with_top (rates u)) :=
      exponential_with_top_isProbabilityMeasure (rates u) (hrace.2.2 u)
    letI : Fintype {u : Fin n // u = v} := Subtype.fintype _
    let e : (Fin n → ENNReal) ≃ᵐ
        ((∀ u : {u : Fin n // u = v}, ENNReal) ×
          (∀ u : {u : Fin n // ¬u = v}, ENNReal)) :=
      MeasurableEquiv.piEquivPiSubtypeProd (π := fun _ : Fin n ↦ ENNReal)
        (fun u : Fin n ↦ u = v)
    let D : Set ((∀ u : {u : Fin n // u = v}, ENNReal) ×
        (∀ u : {u : Fin n // ¬u = v}, ENNReal)) :=
      {z | ∀ u, z.1 ⟨v, rfl⟩ < z.2 u}
    rw [show {x : Fin n → ENNReal | ∀ u, u ≠ v → x v < x u} = e ⁻¹' D by
      ext x
      simp [e, D]]
    rw [(MeasureTheory.measurePreserving_piEquivPiSubtypeProd
      (μ := fun u ↦ exponential_with_top (rates u))
      (fun u : Fin n ↦ u = v)).measure_preimage_equiv D]
    rw [MeasureTheory.Measure.prod_apply (by dsimp [D]; measurability)]
    let F : ENNReal → ENNReal := fun y ↦
      (MeasureTheory.Measure.pi
        (fun i : {u : Fin n // ¬u = v} ↦ exponential_with_top (rates i)))
          {z | ∀ u, y < z u}
    have hF : Measurable F := by
      change Measurable (fun y : ENNReal ↦
        (MeasureTheory.Measure.pi
          (fun i : {u : Fin n // ¬u = v} ↦ exponential_with_top (rates i)))
            (Prod.mk y ⁻¹' {z | ∀ u, z.1 < z.2 u}))
      exact measurable_measure_prodMk_left
        (ν := MeasureTheory.Measure.pi
          (fun i : {u : Fin n // ¬u = v} ↦ exponential_with_top (rates i))) (by measurability)
    have hsection (x : {u : Fin n // u = v} → ENNReal) :
        (MeasureTheory.Measure.pi
          (fun i : {u : Fin n // ¬u = v} ↦ exponential_with_top (rates i)))
            (Prod.mk x ⁻¹' D) = F (x ⟨v, rfl⟩) := by
      rfl
    simp_rw [hsection]
    rw [← MeasureTheory.lintegral_map hF
      (measurable_pi_apply (⟨v, rfl⟩ : {u : Fin n // u = v}))]
    rw [MeasureTheory.Measure.pi_map_eval]
    simp
    have hF_ofReal (t : ℝ) (ht : 0 ≤ t) :
        F (ENNReal.ofReal t) =
          ENNReal.ofReal
            (Real.exp (-((∑ u ∈ Finset.univ.erase v, rates u) * t))) := by
      simp only [F]
      rw [show {z : {u : Fin n // ¬u = v} → ENNReal |
          ∀ u, ENNReal.ofReal t < z u} =
          Set.univ.pi (fun _ ↦ Set.Ioi (ENNReal.ofReal t)) by
        ext z
        simp]
      rw [MeasureTheory.Measure.pi_pi]
      rw [← Finset.prod_subtype (Finset.univ.erase v) (by simp)
        (fun u ↦ exponential_with_top (rates u) (Set.Ioi (ENNReal.ofReal t)))]
      exact product_exponential_tail (Finset.univ.erase v) t ht
    rw [exponential_with_top, if_pos hv]
    rw [MeasureTheory.lintegral_map hF ENNReal.measurable_ofReal]
    change (∫⁻ a, F (ENNReal.ofReal a) ∂MeasureTheory.volume.withDensity
      (ProbabilityTheory.exponentialPDF (rates v))) = _
    have hpdf : Measurable (ProbabilityTheory.exponentialPDF (rates v)) := by
      exact (ProbabilityTheory.measurable_exponentialPDFReal _).ennreal_ofReal
    rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul
      (g := fun a ↦ F (ENNReal.ofReal a)) MeasureTheory.volume
      hpdf (hF.comp ENNReal.measurable_ofReal)]
    have hsum : (∑ u ∈ Finset.univ.erase v, rates u) + rates v = ∑ u, rates u := by
      simpa using Finset.sum_erase_add Finset.univ rates (Finset.mem_univ v)
    let g : ℝ → ℝ := fun a ↦ rates v * Real.exp (-((∑ u, rates u) * a))
    have hintegrand (a : ℝ) :
        (ProbabilityTheory.exponentialPDF (rates v) *
            fun a ↦ F (ENNReal.ofReal a)) a =
          ENNReal.ofReal (Set.indicator (Set.Ici 0) g a) := by
      change ProbabilityTheory.exponentialPDF (rates v) a * F (ENNReal.ofReal a) = _
      by_cases ha : 0 ≤ a
      · rw [ProbabilityTheory.exponentialPDF_of_nonneg ha, hF_ofReal a ha]
        rw [← ENNReal.ofReal_mul (mul_nonneg hv.le (Real.exp_pos _).le)]
        congr 1
        rw [Set.indicator_of_mem (show a ∈ Set.Ici 0 from ha)]
        simp only [g]
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        rw [← hsum]
        ring_nf
      · rw [ProbabilityTheory.exponentialPDF_of_neg (lt_of_not_ge ha)]
        simp [ha]
    simp_rw [hintegrand]
    have hgIoi : MeasureTheory.IntegrableOn g (Set.Ioi 0) := by
      have h := (integrableOn_exp_mul_Ioi (a := -(∑ u, rates u))
        (neg_neg_of_pos htotal) 0).const_mul (rates v)
      simpa [MeasureTheory.IntegrableOn, g, neg_mul] using h
    have hgIci : MeasureTheory.IntegrableOn g (Set.Ici 0) :=
      (integrableOn_Ici_iff_integrableOn_Ioi).2 hgIoi
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (f := Set.indicator (Set.Ici 0) g)
      (hgIci.integrable_indicator measurableSet_Ici)
      (Filter.Eventually.of_forall (Set.indicator_nonneg
        (fun _ _ ↦ mul_nonneg hv.le (Real.exp_pos _).le)))]
    rw [show (∫ x, Set.indicator (Set.Ici 0) g x) =
        ∫ x in Set.Ici 0, g x from MeasureTheory.integral_indicator measurableSet_Ici]
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    rw [MeasureTheory.integral_const_mul]
    rw [show (∫ a : ℝ in Set.Ioi 0, Real.exp (-((∑ u, rates u) * a))) =
        ∫ a : ℝ in Set.Ioi 0, Real.exp ((-(∑ u, rates u)) * a) by
      congr 1
      funext a
      congr 1
      ring]
    rw [integral_exp_mul_Ioi (a := -(∑ u, rates u)) (neg_neg_of_pos htotal) 0]
    simp only [mul_zero, Real.exp_zero, neg_div, neg_neg]
    ring_nf
  have pi_strict_winner_zero (v : Fin n) (hv : rates v = 0) :
      (MeasureTheory.Measure.pi (fun u ↦ exponential_with_top (rates u)))
          {x | ∀ u, u ≠ v → x v < x u} = 0 := by
    letI (u : Fin n) : MeasureTheory.IsProbabilityMeasure
        (exponential_with_top (rates u)) :=
      exponential_with_top_isProbabilityMeasure (rates u) (hrace.2.2 u)
    obtain ⟨u, hu⟩ : ∃ u, 0 < rates u := by
      by_contra h
      simp only [not_exists, not_lt] at h
      have hz : rates = 0 := funext fun i ↦ le_antisymm (h i) (hrace.2.2 i)
      simp [hz] at htotal
    have huv : u ≠ v := by
      intro huv
      subst u
      exact hu.ne' hv
    apply MeasureTheory.measure_mono_null
      (show {x : Fin n → ENNReal | ∀ u, u ≠ v → x v < x u} ⊆
          {x | x v ≠ ⊤} by
        intro x hx
        exact ne_top_of_lt (hx u huv))
    rw [show {x : Fin n → ENNReal | x v ≠ ⊤} =
        Function.eval v ⁻¹' ({⊤}ᶜ) by ext x; simp]
    rw [← MeasureTheory.Measure.map_apply (measurable_pi_apply v)
      (measurableSet_singleton (⊤ : ENNReal)).compl]
    rw [MeasureTheory.Measure.pi_map_eval]
    simp [exponential_with_top, hv]
  have pi_strict_winner_all (v : Fin n) :
      (MeasureTheory.Measure.pi (fun u ↦ exponential_with_top (rates u)))
          {x | ∀ u, u ≠ v → x v < x u} =
        ENNReal.ofReal (rates v / ∑ u, rates u) := by
    rcases (hrace.2.2 v).eq_or_lt with hv | hv
    · rw [pi_strict_winner_zero v hv.symm, ← hv, zero_div, ENNReal.ofReal_zero]
    · exact pi_strict_winner v hv
  let B : Fin n → Set Ω := fun v ↦ {ω | ∀ u, u ≠ v → scores v ω < scores u ω}
  have hscores_ae (u : Fin n) : AEMeasurable (scores u) μ := by
    apply AEMeasurable.of_map_ne_zero
    rw [hrace.1 u]
    exact (exponential_with_top_isProbabilityMeasure (rates u) (hrace.2.2 u)).ne_zero
  have hvec : AEMeasurable (fun ω u ↦ scores u ω) μ :=
    aemeasurable_pi_lambda _ hscores_ae
  have hjoint : MeasureTheory.Measure.map (fun ω u ↦ scores u ω) μ =
      MeasureTheory.Measure.pi (fun u ↦ exponential_with_top (rates u)) := by
    rw [hrace.2.1.map_fun_eq_pi_map hscores_ae]
    congr 1
    funext u
    exact hrace.1 u
  have hB (v : Fin n) : μ (B v) = ENNReal.ofReal (rates v / ∑ u, rates u) := by
    let C : Set (Fin n → ENNReal) := {x | ∀ u, u ≠ v → x v < x u}
    rw [show B v = (fun ω u ↦ scores u ω) ⁻¹' C by ext ω; simp [B, C]]
    rw [← MeasureTheory.Measure.map_apply_of_aemeasurable hvec (by
      dsimp [C]
      measurability)]
    rw [hjoint]
    exact pi_strict_winner_all v
  have hBnull (v : Fin n) : MeasureTheory.NullMeasurableSet (B v) μ := by
    let C : Set (Fin n → ENNReal) := {x | ∀ u, u ≠ v → x v < x u}
    rw [show B v = (fun ω u ↦ scores u ω) ⁻¹' C by ext ω; simp [B, C]]
    exact hvec.nullMeasurableSet_preimage (by dsimp [C]; measurability)
  have hBpair : Pairwise (fun v w ↦ MeasureTheory.AEDisjoint μ (B v) (B w)) := by
    intro v w hvw
    exact (Set.disjoint_left.2 (by
      intro ω hv hw
      exact (lt_asymm (hv w hvw.symm) (hw v hvw)))).aedisjoint
  have hBunion : μ (⋃ v, B v) = 1 := by
    rw [MeasureTheory.measure_iUnion₀ hBpair hBnull]
    rw [tsum_fintype]
    simp_rw [hB]
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun i _ ↦ div_nonneg (hrace.2.2 i) htotal.le)]
    congr 1
    rw [← Finset.sum_div]
    simp [htotal.ne']
  have hBunion_null : MeasureTheory.NullMeasurableSet (⋃ v, B v) μ :=
    MeasureTheory.NullMeasurableSet.iUnion hBnull
  have hfull : ∀ᵐ ω ∂μ, ω ∈ ⋃ v, B v := by
    rw [MeasureTheory.ae_iff]
    change μ ((⋃ v, B v)ᶜ) = 0
    rw [MeasureTheory.measure_compl₀ hBunion_null
      (MeasureTheory.measure_ne_top μ _), hBunion]
    simp
  intro v
  have heq : {ω | out ω = v} =ᵐ[μ] B v := by
    filter_upwards [hfull] with ω hω
    apply propext
    constructor
    · intro houtv
      rcases Set.mem_iUnion.mp hω with ⟨u, hu⟩
      simp only [B, Set.mem_setOf_eq] at hu
      have huv : u = v := by
        by_contra huv
        have hlt := hu v (Ne.symm huv)
        have hle := hout ω u
        rw [houtv] at hle
        exact (not_lt_of_ge hle) hlt
      subst u
      change ∀ u, u ≠ v → scores v ω < scores u ω
      exact hu
    · intro hv
      simp only [B, Set.mem_setOf_eq] at hv
      by_contra hov
      exact (not_lt_of_ge (hout ω v)) (hv (out ω) hov)
  rw [MeasureTheory.measureReal_congr heq]
  rw [MeasureTheory.Measure.real, hB v]
  exact ENNReal.toReal_ofReal (div_nonneg (hrace.2.2 v) htotal.le)

@[blueprint "lem:generic-sampler-exact"
  (statement := /-- Let $(\Omega,\Sigma,\mu)$ be a probability space, let $n\in\mathbb N$,
  let $(u_i)$ be a finite incremental-update stream on $[n]$, and equip the stream with a
  compatible Pareto random source. Fix $t\in\mathbb N$, a function
  $G:\mathbb R\to\mathbb R$, and an output map $V:\Omega\to[n]$. Suppose that
  $G(x_t)=\sum_{u\in[n]}G(x_t(u))>0$ and that there exists a level function satisfying the
  specification for $G$ such that, for every $\omega\in\Omega$ and $v\in[n]$, the coordinate
  score of $V(\omega)$ is at most the coordinate score of $v$. Then, for every $v\in[n]$,
  $\mu\{\omega:V(\omega)=v\}=G(x_t(v))/G(x_t)$. -/)
  (proof := /-- Unfolding \cref{def:full-sample-at}, choose a level function satisfying the
  specification for $G$ and witnessing the pointwise minimum property of the output. By
  \cref{lem:update-scores-form-exponential-race}, its coordinate scores form an exponential
  race with rates $v\mapsto G(x_t(v))$. By \cref{def:weight-moment}, the assumed positivity
  of $G(x_t)$ is precisely positivity of the sum of these rates. The minimum witness is the
  selector hypothesis of \cref{lem:exponential-race-selects-proportionally}, so that lemma
  gives probability $G(x_t(v))/\sum_u G(x_t(u))$ for every $v$. A second application of
  \cref{def:weight-moment} identifies the denominator with $G(x_t)$. -/)
  (title := /-- Correctness of the generic $G$-sampler -/)
  (latexEnv := "lemma")]
lemma generic_sampler_exact {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (updates : List (incremental_update n))
    (source : pareto_random_source Ω n updates.length μ) (t : ℕ)
    (G : ℝ → ℝ) (out : Ω → Fin n)
    (hpositive : 0 < weight_moment G (stream_vector updates t))
    (hfull : full_sample_at updates μ source t G out) :
    ∀ v, μ.real {ω | out ω = v} =
      G (stream_vector updates t v) / weight_moment G (stream_vector updates t) := by
  obtain ⟨ell, hell, hout⟩ := hfull
  apply exponential_race_selects_proportionally μ
    (fun v ↦ G (stream_vector updates t v))
    (fun v ω ↦ coordinate_level_score updates μ source ell ω t v)
  · simpa only [weight_moment] using hpositive
  · exact update_scores_form_exponential_race μ updates source t G ell hell
  · exact hout

@[blueprint "lem:pareto-frontier-minimum-transfer"
  (statement := /-- Let $\Omega$ be a measurable space, let $\mu$ be a measure on $\Omega$,
  let $n\in\mathbb N$, and let an incremental stream over $[n]$ be equipped with a compatible
  Pareto random source. Fix $t\in\mathbb N$, a weight function $G:\mathbb R\to\mathbb R$,
  and an output map $\Omega\to[n]$. If the output is a Pareto sample at time $t$, witnessed
  by a level function satisfying the specification for $G$ and minimizing pointwise on the
  maintained minimum Pareto frontier, then the same level function makes the output minimize
  the coordinate score over every index; equivalently, the output is a full sample at time
  $t$. -/)
  (proof := /-- Fix an outcome $\omega$. By \cref{def:pareto-sample-at}, choose the specified
  level function and a minimizing tuple $p$ in the state, with index equal to the output.
  For each tuple $q$ in the finite set of generated tuples from
  \cref{def:generated-tuples}, take a minimal element $r$ of the nonempty down-set of tuples
  whose order coordinates are at most those of $q$. Minimality places $r$ in the frontier
  defined by \cref{def:pareto-frontier}, hence in the state of \cref{def:pareto-state}.
  The frontier minimality of $p$ and the monotonicity supplied by
  \cref{def:level-function-spec} give $\ell(p)\leq\ell(r)\leq\ell(q)$.
  Since $p$ is generated, \cref{def:generated-pareto-tuple} supplies an active update of the
  output index which generates $p$. Thus the output's score, defined in
  \cref{def:coordinate-level-score, def:finite-minimum-with-infinity}, is at most
  $\ell(p)$. If an index has active updates, the preceding bound holds for every level in its
  defining finite set and therefore for its minimum; if it has none, its score is $\infty$.
  The chosen level function consequently witnesses \cref{def:full-sample-at}. -/)
  (title := /-- Transfer of a minimum to the Pareto frontier -/)
  (latexEnv := "lemma")]
lemma pareto_frontier_minimum_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) {n : ℕ} (updates : List (incremental_update n))
    (source : pareto_random_source Ω n updates.length μ) (t : ℕ) (G : ℝ → ℝ)
    (out : Ω → Fin n) (hpareto : pareto_sample_at updates μ source t G out) :
    full_sample_at updates μ source t G out := by
  classical
  rcases hpareto with ⟨ell, hell, hsample⟩
  refine ⟨ell, hell, ?_⟩
  intro ω v
  rcases hsample ω with ⟨p, hp, hpindex, hpmin⟩
  let s := generated_tuples updates μ source ω t
  have hp_s : p ∈ s := by
    change p ∈ pareto_frontier s at hp
    exact (Finset.mem_filter.mp hp).1
  have hlevel : ∀ q ∈ s,
      ell (pareto_tuple_coordinates p) ≤ ell (pareto_tuple_coordinates q) := by
    intro q hq
    let d := s.filter fun r ↦ pareto_tuple_coordinates r ≤ pareto_tuple_coordinates q
    have hd : d.Nonempty := by
      refine ⟨q, Finset.mem_filter.mpr ⟨hq, le_rfl⟩⟩
    obtain ⟨r, hr⟩ := d.exists_minimalFor pareto_tuple_coordinates hd
    have hr_s : r ∈ s := (Finset.mem_filter.mp hr.1).1
    have hrq : pareto_tuple_coordinates r ≤ pareto_tuple_coordinates q :=
      (Finset.mem_filter.mp hr.1).2
    have hr_frontier : r ∈ pareto_state updates μ source ω t := by
      change r ∈ pareto_frontier s
      rw [pareto_frontier]
      refine Finset.mem_filter.mpr ⟨hr_s, ?_⟩
      intro z hz hzr
      exact hr.2 (Finset.mem_filter.mpr ⟨hz, hzr.trans hrq⟩) hzr
    exact (hpmin r hr_frontier).trans (hell.2.1 hrq)
  have hp_generated :
      ∃ i ∈ active_update_indices updates t (out ω),
        generated_pareto_tuple updates μ source ω i = p := by
    change p ∈ generated_tuples updates μ source ω t at hp_s
    rw [generated_tuples] at hp_s
    rcases Finset.mem_image.mp hp_s with ⟨i, hi, hip⟩
    have hit : i.val < t := (Finset.mem_filter.mp hi).2
    have hiindex : (updates.get i).index = out ω := by
      calc
        (updates.get i).index = (generated_pareto_tuple updates μ source ω i).index := rfl
        _ = p.index := congrArg pareto_tuple.index hip
        _ = out ω := hpindex
    refine ⟨i, ?_, hip⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hit, hiindex⟩
  rcases hp_generated with ⟨i, hi, hip⟩
  have hactive_out : (active_update_indices updates t (out ω)).Nonempty := ⟨i, hi⟩
  have houtput : coordinate_level_score updates μ source ell ω t (out ω) ≤
      ell (pareto_tuple_coordinates p) := by
    rw [coordinate_level_score, finite_minimum_with_infinity, dif_pos hactive_out]
    apply Finset.min'_le
    apply Finset.mem_image.mpr
    refine ⟨i, hi, ?_⟩
    rw [← (Finset.mem_filter.mp hi).2.2]
    change ell (pareto_tuple_coordinates (generated_pareto_tuple updates μ source ω i)) =
      ell (pareto_tuple_coordinates p)
    rw [hip]
  unfold coordinate_level_score finite_minimum_with_infinity at houtput ⊢
  rw [dif_pos hactive_out] at houtput ⊢
  by_cases hv : (active_update_indices updates t v).Nonempty
  · rw [dif_pos hv]
    apply Finset.le_min'
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
    apply houtput.trans
    rw [← (Finset.mem_filter.mp hj).2.2]
    change ell (pareto_tuple_coordinates p) ≤
      ell (pareto_tuple_coordinates (generated_pareto_tuple updates μ source ω j))
    apply hlevel
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2.1⟩
  · rw [dif_neg hv]
    exact le_top

@[blueprint "lem:pareto-sampler-sampling-correct"
  (statement := /-- Let $(\Omega,\mu)$ be a probability space, let $(u_1,\ldots,u_m)$ be an
  incremental-update stream on $[n]$, and let the Pareto random source be defined on
  $\Omega$. If a run implements the Pareto sampler for this stream and source, then for every
  $t\leq m$, every admissible query function $G$ with $G(x_t)>0$, and every $v\in[n]$,
  \[
    \mu\{\omega:\operatorname{output}(t,G,\omega)=v\}
      =\frac{G(x_t(v))}{G(x_t)}.
  \] -/)
  (proof := /-- Fix $t\leq m$, an admissible $G$ with $G(x_t)>0$, and $v\in[n]$. By
  \cref{def:implements-pareto-sampler}, the output at time $t$ is a Pareto sample. Applying
  \cref{lem:pareto-frontier-minimum-transfer} shows that this output minimizes the coordinate
  level score over all indices. The positive-moment hypothesis and
  \cref{lem:generic-sampler-exact} then give
  $\mu\{\omega:\operatorname{output}(t,G,\omega)=v\}=G(x_t(v))/G(x_t)$. -/)
  (title := /-- Exact sampling by the Pareto sampler -/)
  (latexEnv := "lemma")]
lemma pareto_sampler_sampling_correct {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (updates : List (incremental_update n))
    (source : pareto_random_source Ω n updates.length μ)
    (run : pareto_sampler_run Ω n) (himpl : implements_pareto_sampler updates μ source run) :
    ∀ (t : ℕ), t ≤ updates.length → ∀ (G : ℝ → ℝ) (hG : is_admissible_weight G)
      (hpositive : 0 < weight_moment G (stream_vector updates t)) (v : Fin n),
      μ.real {ω | run.output t G hG ω = v} =
        G (stream_vector updates t v) / weight_moment G (stream_vector updates t) := by
  intro t ht G hG hpositive
  apply generic_sampler_exact μ updates source t G (run.output t G hG) hpositive
  exact pareto_frontier_minimum_transfer μ updates source t G (run.output t G hG)
    (himpl t ht G hG hpositive)

@[blueprint "def:pareto-hash-order"
  (statement := /-- For a hash vector $h:[n]\to\mathbb R$, the hash order is the
  permutation which lists coordinates increasingly by the lexicographic keys $(h(v),v)$. -/)
  (title := /-- Coordinate order induced by hash values -/)
  (latexEnv := "definition")]
noncomputable def pareto_hash_order {n : ℕ} (h : Fin n → ℝ) : Equiv.Perm (Fin n) := by
  classical
  let key : Fin n → Lex (ℝ × Fin n) := fun v ↦ toLex (h v, v)
  have hkey : Function.Injective key := by
    intro a b hab
    exact congrArg (fun z ↦ (ofLex z).2) hab
  let keys := (Finset.univ : Finset (Fin n)).image key
  have hcard : keys.card = n := by
    dsimp [keys]
    rw [Finset.card_image_of_injective _ hkey]
    simp
  let e := Finset.orderIsoOfFin keys hcard
  exact
    { toFun := fun i ↦ (ofLex (e i).1).2
      invFun := fun v ↦ e.symm ⟨key v, by simp [keys]⟩
      left_inv := fun i ↦ by
        apply e.injective
        apply Subtype.ext
        have hei : (e i).1 ∈ keys := (e i).2
        simp only [keys, Finset.mem_image] at hei
        rcases hei with ⟨v, hv, hev⟩
        simpa [key, ← hev]
      right_inv := fun v ↦ by
        have he := e.apply_symm_apply ⟨key v, by simp [keys]⟩
        exact congrArg (fun z : {x // x ∈ keys} ↦ (ofLex z.1 : ℝ × Fin n).2) he }

@[blueprint "lem:pareto-hash-order-strictly-increases-keys"
  (statement := /-- The lexicographic hash-and-label keys are strictly increasing along the
  coordinate permutation defined by \cref{def:pareto-hash-order}. -/)
  (proof := /-- The increasing enumeration of a finite linearly ordered set is strictly
  monotone. Every key in the image recovers its originating coordinate from its label
  component, so the enumeration used in \cref{def:pareto-hash-order} enumerates the keys
  themselves in strictly increasing order. -/)
  (title := /-- Strict increase along the hash order -/)
  (latexEnv := "lemma")]
lemma pareto_hash_order_strictly_increases_keys {n : ℕ} (h : Fin n → ℝ) :
    StrictMono (fun i ↦ toLex (h (pareto_hash_order h i), pareto_hash_order h i)) := by
  classical
  let key : Fin n → Lex (ℝ × Fin n) := fun v ↦ toLex (h v, v)
  have hkey : Function.Injective key := by
    intro a b hab
    exact congrArg (fun z ↦ (ofLex z).2) hab
  let keys := (Finset.univ : Finset (Fin n)).image key
  have hcard : keys.card = n := by
    dsimp [keys]
    rw [Finset.card_image_of_injective _ hkey]
    simp
  let e := Finset.orderIsoOfFin keys hcard
  have hvalue : ∀ i, key ((ofLex (e i).1 : ℝ × Fin n).2) = (e i).1 := by
    intro i
    have hei : (e i).1 ∈ keys := (e i).2
    simp only [keys, Finset.mem_image] at hei
    rcases hei with ⟨v, hv, hev⟩
    simpa [key, ← hev]
  intro i j hij
  change key (pareto_hash_order h i) < key (pareto_hash_order h j)
  change key ((ofLex (e i).1 : ℝ × Fin n).2) <
    key ((ofLex (e j).1 : ℝ × Fin n).2)
  rw [hvalue i, hvalue j]
  exact e.strictMono hij

@[blueprint "lem:strictly-monotone-finite-permutation-is-identity"
  (statement := /-- Every strictly monotone permutation of a finite ordinal is the identity. -/)
  (proof := /-- Well-founded induction shows that every strictly monotone self-map of a
  finite ordinal lies pointwise above the identity. The inverse permutation is also strictly
  monotone; applying the same fact to it and then applying the original monotone map gives
  the reverse pointwise inequality. Antisymmetry yields the identity. -/)
  (title := /-- Strictly monotone finite permutations are trivial -/)
  (latexEnv := "lemma")]
lemma strictly_monotone_finite_permutation_is_identity {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (hσ : StrictMono σ) : σ = Equiv.refl _ := by
  have self_le : ∀ (f : Fin n → Fin n), StrictMono f → ∀ i, i ≤ f i := by
    intro f hf i
    by_contra! hnot
    obtain ⟨m, hm, hm'⟩ := wellFounded_lt.has_min {j | f j < j} ⟨i, hnot⟩
    exact hm' _ (hf hm) hm
  have hsymm : StrictMono σ.symm := by
    intro i j hij
    by_contra hnot
    have hle : σ.symm j ≤ σ.symm i := le_of_not_gt hnot
    have himage := hσ.monotone hle
    simp at himage
    exact (not_le_of_gt hij) himage
  apply Equiv.ext
  intro i
  apply le_antisymm
  · simpa using self_le σ.symm hsymm (σ i)
  · exact self_le σ hσ i

@[blueprint "lem:pareto-hash-order-characterization"
  (statement := /-- A permutation is the hash order if and only if the lexicographic
  hash-and-label keys are strictly increasing along it. -/)
  (proof := /-- The forward implication is
  \cref{lem:pareto-hash-order-strictly-increases-keys}. Conversely, conjugate the proposed
  permutation by the hash order. Strict increase of both key enumerations makes the resulting
  finite permutation strictly monotone, so
  \cref{lem:strictly-monotone-finite-permutation-is-identity} makes it the identity. -/)
  (title := /-- Characterization of the hash order -/)
  (latexEnv := "lemma")]
lemma pareto_hash_order_characterization {n : ℕ} (h : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) :
    pareto_hash_order h = σ ↔ StrictMono (fun i ↦ toLex (h (σ i), σ i)) := by
  constructor
  · rintro rfl
    exact pareto_hash_order_strictly_increases_keys h
  · intro hσ
    let τ : Equiv.Perm (Fin n) := σ.trans (pareto_hash_order h).symm
    have hτ : StrictMono τ := by
      intro i j hij
      apply (pareto_hash_order_strictly_increases_keys h).lt_iff_lt.mp
      simpa [τ] using hσ hij
    have hτid := strictly_monotone_finite_permutation_is_identity τ hτ
    apply Equiv.ext
    intro i
    have := Equiv.congr_fun hτid i
    simpa [τ] using (congrArg (pareto_hash_order h) this).symm

@[blueprint "lem:pareto-hash-order-fiber-measurable"
  (statement := /-- For each fixed coordinate permutation, the set of real hash vectors
  inducing that permutation is measurable. -/)
  (proof := /-- By \cref{lem:pareto-hash-order-characterization}, the fiber is the finite
  intersection of pairwise lexicographic comparison events. Each such event is either a
  strict or a weak comparison of two measurable coordinate projections, according to the
  fixed coordinate-label comparison, and hence is measurable. -/)
  (title := /-- Measurability of hash-order fibers -/)
  (latexEnv := "lemma")]
lemma pareto_hash_order_fiber_measurable {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurableSet {h : Fin n → ℝ | pareto_hash_order h = σ} := by
  have hpair : ∀ i j : Fin n, MeasurableSet {h : Fin n → ℝ |
      toLex (h (σ i), σ i) < toLex (h (σ j), σ j)} := by
    intro i j
    by_cases hij : σ i < σ j
    · simpa [Prod.Lex.lt_iff, hij, Set.setOf_or] using
        (measurableSet_lt (measurable_pi_apply (σ i)) (measurable_pi_apply (σ j))).union
          (measurableSet_eq_fun
            (measurable_pi_apply (σ i) : Measurable (fun h : Fin n → ℝ ↦ h (σ i)))
            (measurable_pi_apply (σ j) : Measurable (fun h : Fin n → ℝ ↦ h (σ j))))
    · simpa [Prod.Lex.lt_iff, hij] using
        (measurableSet_lt (measurable_pi_apply (σ i)) (measurable_pi_apply (σ j)))
  rw [show {h : Fin n → ℝ | pareto_hash_order h = σ} =
      ⋂ i, ⋂ j, if i < j then
        {h | toLex (h (σ i), σ i) < toLex (h (σ j), σ j)} else Set.univ by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hm i j
      by_cases hij : i < j
      · simp only [hij, if_true, Set.mem_setOf_eq]
        exact (pareto_hash_order_characterization h σ).mp hm hij
      · simp [hij]
    · intro hm
      apply (pareto_hash_order_characterization h σ).mpr
      intro i j hij
      simpa [hij] using hm i j]
  exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦ by
    by_cases hij : i < j <;> simp [hij, hpair]

@[blueprint "lem:pareto-hash-vector-exchangeable"
  (statement := /-- The joint law of the Pareto hash vector is invariant under every
  permutation of its coordinate indices. -/)
  (proof := /-- By \cref{def:pareto-random-source}, the hash coordinates are mutually
  independent and all have the same uniform law. The joint map law is therefore the finite
  product of these common marginal laws, both before and after reindexing. -/)
  (title := /-- Exchangeability of the Pareto hash vector -/)
  (latexEnv := "lemma")]
lemma pareto_hash_vector_exchangeable {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) {n : ℕ} (updates : List (incremental_update n))
    (source : pareto_random_source Ω n updates.length μ) (σ : Equiv.Perm (Fin n)) :
    MeasureTheory.Measure.map (fun ω i ↦ source.hash (σ i) ω) μ =
      MeasureTheory.Measure.map (fun ω i ↦ source.hash i ω) μ := by
  have hhash : ProbabilityTheory.iIndepFun source.hash μ := by
    simpa using source.jointly_independent.precomp Sum.inl_injective
  have hperm : ProbabilityTheory.iIndepFun (fun i ↦ source.hash (σ i)) μ :=
    hhash.precomp σ.injective
  rw [hperm.map_fun_eq_pi_map (fun i ↦ (source.hash_measurable (σ i)).aemeasurable)]
  rw [hhash.map_fun_eq_pi_map (fun i ↦ (source.hash_measurable i).aemeasurable)]
  congr 2
  funext i
  simpa [has_uniform_unit_law, has_law] using
    (source.hash_uniform (σ i)).trans (source.hash_uniform i).symm

@[blueprint "lem:pareto-hash-order-has-uniform-law"
  (statement := /-- The permutation induced by the Pareto hash vector has the uniform
  probability mass function on coordinate permutations. -/)
  (proof := /-- Pairwise independence and atomlessness of the common restricted Lebesgue
  hash law give almost-sure injectivity of the finite hash vector. The permutation fibers
  are measurable by \cref{lem:pareto-hash-order-fiber-measurable}. On the injectivity event,
  \cref{lem:pareto-hash-order-characterization} identifies a permutation fiber with the
  event that the hashes in that permuted order are strictly increasing. Exchangeability from
  \cref{lem:pareto-hash-vector-exchangeable} therefore gives every measurable fiber the same
  mass. The fibers form a measurable disjoint partition of the probability space, so their
  common mass is the reciprocal of the number of permutations. -/)
  (title := /-- Uniform law of the Pareto hash order -/)
  (latexEnv := "lemma")]
lemma pareto_hash_order_has_uniform_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (updates : List (incremental_update n))
    (source : pareto_random_source Ω n updates.length μ) :
    has_pmf_law (fun ω ↦ pareto_hash_order (fun v ↦ source.hash v ω))
      (uniform_permutation n) μ := by
  classical
  let X : Ω → (Fin n → ℝ) := fun ω v ↦ source.hash v ω
  have hXmeas : Measurable X := measurable_pi_lambda _ source.hash_measurable
  have hinj : ∀ᵐ ω ∂μ, Function.Injective (fun v ↦ source.hash v ω) := by
    let ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc 0 1)
    have hhash : ProbabilityTheory.iIndepFun source.hash μ := by
      simpa using source.jointly_independent.precomp Sum.inl_injective
    have hlaw : ∀ v, MeasureTheory.Measure.map (source.hash v) μ = ν := by
      intro v
      simpa [ν, has_uniform_unit_law, has_law] using source.hash_uniform v
    have hpairs : ∀ i j : Fin n, i ≠ j →
        ∀ᵐ ω ∂μ, source.hash i ω ≠ source.hash j ω := by
      intro i j hij
      have hpair := (hhash.indepFun hij).map_prod_eq_prod_map_map
        (source.hash_measurable i).aemeasurable (source.hash_measurable j).aemeasurable
      rw [hlaw i, hlaw j] at hpair
      have hprod : ∀ᵐ z ∂ν.prod ν, z.1 ≠ z.2 := by
        have hne_meas : MeasurableSet {z : ℝ × ℝ | z.1 ≠ z.2} :=
          (measurableSet_eq_fun measurable_fst measurable_snd).compl
        rw [MeasureTheory.Measure.ae_prod_iff_ae_ae hne_meas]
        filter_upwards with x
        exact (ν.ae_ne x).mono (fun y hy ↦ Ne.symm hy)
      rw [MeasureTheory.ae_iff]
      rw [show {ω | ¬source.hash i ω ≠ source.hash j ω} =
          (fun ω ↦ (source.hash i ω, source.hash j ω)) ⁻¹'
            {z : ℝ × ℝ | z.1 = z.2} by ext; simp]
      rw [← MeasureTheory.Measure.map_apply
        ((source.hash_measurable i).prodMk (source.hash_measurable j))
        (measurableSet_eq_fun measurable_fst measurable_snd)]
      rw [hpair]
      simpa [MeasureTheory.ae_iff] using hprod
    change ∀ᵐ ω ∂μ, ∀ ⦃i j : Fin n⦄, source.hash i ω = source.hash j ω → i = j
    rw [MeasureTheory.ae_all_iff]
    intro i
    rw [MeasureTheory.ae_all_iff]
    intro j
    by_cases hij : i = j
    · simp [hij]
    · exact (hpairs i j hij).mono (fun ω hne heq ↦ (hne heq).elim)
  have hsame : ∀ σ : Equiv.Perm (Fin n),
      μ {ω | pareto_hash_order (X ω) = σ} =
        μ {ω | pareto_hash_order (X ω) = Equiv.refl _} := by
    intro σ
    have hae : ∀ᵐ ω ∂μ,
        (pareto_hash_order (X ω) = σ) ↔
          (pareto_hash_order (fun i ↦ X ω (σ i)) = Equiv.refl _) := by
      filter_upwards [hinj] with ω hω
      rw [pareto_hash_order_characterization, pareto_hash_order_characterization]
      constructor <;> intro hm i j hij
      · have hk := hm hij
        rw [Prod.Lex.lt_iff] at hk ⊢
        rcases hk with hk | ⟨heq, _⟩
        · exact Or.inl hk
        · exact ((ne_of_lt hij) (σ.injective (hω heq))).elim
      · have hk := hm hij
        rw [Prod.Lex.lt_iff] at hk ⊢
        rcases hk with hk | ⟨heq, _⟩
        · exact Or.inl hk
        · exact ((ne_of_lt hij) (σ.injective (hω heq))).elim
    have hsetae : {ω | pareto_hash_order (X ω) = σ} =ᵐ[μ]
        {ω | pareto_hash_order (fun i ↦ X ω (σ i)) = Equiv.refl _} :=
      hae.mono (fun ω hω ↦ propext hω)
    rw [MeasureTheory.measure_congr hsetae]
    let F : Set (Fin n → ℝ) := {h | pareto_hash_order h = Equiv.refl _}
    have hF : MeasurableSet F := pareto_hash_order_fiber_measurable _
    calc
      μ {ω | pareto_hash_order (fun i ↦ X ω (σ i)) = Equiv.refl _} =
          (MeasureTheory.Measure.map (fun ω i ↦ X ω (σ i)) μ) F := by
            symm
            exact MeasureTheory.Measure.map_apply
              (measurable_pi_lambda _ fun i ↦ source.hash_measurable (σ i)) hF
      _ = (MeasureTheory.Measure.map X μ) F := by
        rw [pareto_hash_vector_exchangeable μ updates source σ]
      _ = μ {ω | pareto_hash_order (X ω) = Equiv.refl _} := by
        exact MeasureTheory.Measure.map_apply hXmeas hF
  intro σ
  have hsum : ∑ τ : Equiv.Perm (Fin n), μ {ω | pareto_hash_order (X ω) = τ} = 1 := by
    have hdis : Pairwise (Function.onFun Disjoint fun τ : Equiv.Perm (Fin n) ↦
        {ω | pareto_hash_order (X ω) = τ}) := by
      intro a b hab
      rw [Function.onFun, Set.disjoint_left]
      intro ω ha hb
      exact hab (ha.symm.trans hb)
    have hmeas : ∀ τ : Equiv.Perm (Fin n),
        MeasurableSet {ω | pareto_hash_order (X ω) = τ} := fun τ ↦
      (pareto_hash_order_fiber_measurable τ).preimage hXmeas
    have hu := MeasureTheory.measure_iUnion (μ := μ) hdis hmeas
    rw [show (⋃ τ : Equiv.Perm (Fin n), {ω | pareto_hash_order (X ω) = τ}) =
        Set.univ by ext ω; simp, MeasureTheory.measure_univ] at hu
    simpa only [tsum_fintype] using hu.symm
  have hmul : (Fintype.card (Equiv.Perm (Fin n)) : ENNReal) *
      μ {ω | pareto_hash_order (X ω) = Equiv.refl _} = 1 := by
    simpa [hsame] using hsum
  rw [hsame σ]
  rw [show μ {ω | pareto_hash_order (X ω) = Equiv.refl _} =
      (Fintype.card (Equiv.Perm (Fin n)) : ENNReal)⁻¹ by
    exact ENNReal.eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hmul)]
  simp [uniform_permutation]

@[blueprint "lem:pareto-priority-transform-measurable"
  (statement := /-- For a fixed stream and time, taking every coordinate's finite minimum
  of embedded scaled noises defines a measurable map from the finite noise vector to the
  extended coordinate-priority vector. -/)
  (proof := /-- Each scaled coordinate projection and its nonnegative-real embedding are
  measurable. For a nonempty active-index set, induct on that finite set and express its
  infimum after an insertion as the minimum of two measurable functions; for an empty set,
  the priority is the constant infinity. Coordinatewise measurability gives measurability of
  the finite priority vector. -/)
  (title := /-- Measurability of the priority transform -/)
  (latexEnv := "lemma")]
lemma pareto_priority_transform_measurable {n : ℕ}
    (updates : List (incremental_update n)) (t : ℕ) :
    Measurable (fun z : Fin updates.length → ℝ ↦ fun v ↦
      finite_minimum_with_infinity (active_update_indices updates t v)
        (fun i ↦ ENNReal.ofReal (z i / (updates.get i).increment))) := by
  apply measurable_pi_lambda
  intro v
  let s := active_update_indices updates t v
  by_cases hs : s.Nonempty
  · have hmin_general : ∀ (u : Finset (Fin updates.length)) (hu : u.Nonempty),
        Measurable (fun z : Fin updates.length → ℝ ↦
          u.inf' hu (fun i ↦ ENNReal.ofReal (z i / (updates.get i).increment))) := by
      intro u hu
      induction u using Finset.induction_on with
      | empty => simp at hu
      | @insert a u ha ih =>
          by_cases hu' : u.Nonempty
          · simpa [Finset.inf'_insert, hu'] using
              ((by simpa [Function.comp_def] using (ENNReal.measurable_ofReal.comp
                ((measurable_pi_apply a : Measurable
                  (fun z : Fin updates.length → ℝ ↦ z a)).div_const
                    (updates.get a).increment)) : Measurable (fun z : Fin updates.length → ℝ ↦
                      ENNReal.ofReal (z a / (updates.get a).increment))).min
                (ih hu'))
          · have huempty : u = ∅ := Finset.not_nonempty_iff_eq_empty.mp hu'
            subst u
            simpa [Function.comp_def] using ENNReal.measurable_ofReal.comp
              ((measurable_pi_apply a : Measurable
                (fun z : Fin updates.length → ℝ ↦ z a)).div_const (updates.get a).increment)
    have hmin := hmin_general s hs
    have heq : (fun z : Fin updates.length → ℝ ↦
        finite_minimum_with_infinity s
          (fun i ↦ ENNReal.ofReal (z i / (updates.get i).increment))) =
        (fun z ↦ s.inf' hs
          (fun i ↦ ENNReal.ofReal (z i / (updates.get i).increment))) := by
      funext z
      unfold finite_minimum_with_infinity
      simp only [hs, dite_true]
      let f : Fin updates.length → ENNReal := fun i ↦
        ENNReal.ofReal (z i / (updates.get i).increment)
      rcases Finset.exists_mem_eq_inf' hs f with ⟨i, hi, heq⟩
      apply le_antisymm
      · change (s.image f).min' _ ≤ s.inf' hs f
        rw [heq]
        apply Finset.min'_le
        exact Finset.mem_image.2 ⟨i, hi, rfl⟩
      · have hmem := Finset.min'_mem (s.image f) (hs.image f)
        rcases Finset.mem_image.1 hmem with ⟨i, hi, him⟩
        rw [← him]
        exact Finset.inf'_le f hi
    change Measurable (fun z : Fin updates.length → ℝ ↦
      finite_minimum_with_infinity s
        (fun i ↦ ENNReal.ofReal (z i / (updates.get i).increment)))
    rw [heq]
    exact hmin
  · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [finite_minimum_with_infinity, s, hsempty]

@[blueprint "lem:pareto-priorities-independent-of-hash-order"
  (statement := /-- For every stream and time, the random coordinate-priority vector is
  independent, in the measurable-event sense, of the permutation induced by the hash
  vector, whose mass function is uniform. -/)
  (proof := /-- Split the jointly independent primitive family from
  \cref{def:pareto-random-source} into all noise coordinates and all hash coordinates. The
  priority vector is a measurable function of the noise block by
  \cref{lem:pareto-priority-transform-measurable}. Every event of the finite hash order is a
  finite union of the measurable fibers from
  \cref{lem:pareto-hash-order-fiber-measurable}. Independence of the two blocks therefore
  factors the corresponding events. Finally,
  \cref{lem:pareto-hash-order-has-uniform-law} identifies the hash-order event probability
  with its uniform-PMF probability. -/)
  (title := /-- Independence of priorities and hash order -/)
  (latexEnv := "lemma")]
lemma pareto_priorities_independent_of_hash_order {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (updates : List (incremental_update n))
    (source : pareto_random_source Ω n updates.length μ) (t : ℕ) :
    independent_of_pmf
      (fun ω v ↦ coordinate_priority updates μ source ω t v)
      (fun ω ↦ pareto_hash_order (fun v ↦ source.hash v ω))
      (uniform_permutation n) μ := by
  classical
  let S : Finset (Sum (Fin n) (Fin updates.length)) := Finset.univ.image Sum.inr
  let T : Finset (Sum (Fin n) (Fin updates.length)) := Finset.univ.image Sum.inl
  let noiseBlock : Ω → (S → ℝ) := fun ω j ↦
    Sum.elim source.hash source.noise (j : Sum (Fin n) (Fin updates.length)) ω
  let hashBlock : Ω → (T → ℝ) := fun ω j ↦
    Sum.elim source.hash source.noise (j : Sum (Fin n) (Fin updates.length)) ω
  have hdisjoint : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    rcases Finset.mem_image.1 hxS with ⟨i, hi, rfl⟩
    simp [T] at hxT
  have hbase : ProbabilityTheory.IndepFun noiseBlock hashBlock μ := by
    exact source.jointly_independent.indepFun_finset S T hdisjoint (by
      intro j
      cases j with
      | inl v => exact source.hash_measurable v
      | inr i => exact source.noise_measurable i)
  let extractNoise : (S → ℝ) → (Fin updates.length → ℝ) := fun z i ↦
    z ⟨Sum.inr i, by simp [S]⟩
  let extractHash : (T → ℝ) → (Fin n → ℝ) := fun z v ↦
    z ⟨Sum.inl v, by simp [T]⟩
  let priorityMap : (S → ℝ) → (Fin n → ENNReal) := fun z v ↦
    finite_minimum_with_infinity (active_update_indices updates t v)
      (fun i ↦ ENNReal.ofReal (extractNoise z i / (updates.get i).increment))
  have hnoiseBlock : Measurable noiseBlock := measurable_pi_lambda _ fun j ↦ by
    rcases j with ⟨j, hj⟩
    cases j with
    | inl v => exact source.hash_measurable v
    | inr i => exact source.noise_measurable i
  have hhashBlock : Measurable hashBlock := measurable_pi_lambda _ fun j ↦ by
    rcases j with ⟨j, hj⟩
    cases j with
    | inl v => exact source.hash_measurable v
    | inr i => exact source.noise_measurable i
  have hextractNoise : Measurable extractNoise := measurable_pi_lambda _ fun i ↦
    measurable_pi_apply (show S from ⟨Sum.inr i, by simp [S]⟩)
  have hextractHash : Measurable extractHash := measurable_pi_lambda _ fun v ↦
    measurable_pi_apply (show T from ⟨Sum.inl v, by simp [T]⟩)
  have hpriorityMap : Measurable priorityMap := by
    exact (pareto_priority_transform_measurable updates t).comp hextractNoise
  have hleft : priorityMap ∘ noiseBlock =
      (fun ω v ↦ coordinate_priority updates μ source ω t v) := by
    rfl
  have hright : (fun z ↦ pareto_hash_order (extractHash z)) ∘ hashBlock =
      (fun ω ↦ pareto_hash_order (fun v ↦ source.hash v ω)) := by
    rfl
  intro A hA B
  let FB := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter fun σ ↦ σ ∈ B
  let D : Set (T → ℝ) := {z | pareto_hash_order (extractHash z) ∈ B}
  have hD : MeasurableSet D := by
    rw [show D = ⋃ σ ∈ FB, extractHash ⁻¹' {h | pareto_hash_order h = σ} by
      ext z
      simp [D, FB]]
    exact Finset.measurableSet_biUnion FB fun σ hσ ↦
      (pareto_hash_order_fiber_measurable σ).preimage hextractHash
  have hind := (ProbabilityTheory.indepFun_iff_indepSet_preimage
    hnoiseBlock hhashBlock).mp hbase (priorityMap ⁻¹' A) D
    (hA.preimage hpriorityMap) hD
  have hfactor := hind.measure_inter_eq_mul
  have hlaw := pareto_hash_order_has_uniform_law μ updates source
  have horderB : μ {ω | pareto_hash_order (fun v ↦ source.hash v ω) ∈ B} =
      pmf_event (uniform_permutation n) (fun σ ↦ σ ∈ B) := by
    have hdis : Set.PairwiseDisjoint (↑FB) fun σ ↦
        {ω | pareto_hash_order (fun v ↦ source.hash v ω) = σ} := by
      intro a ha b hb hab
      rw [Function.onFun, Set.disjoint_left]
      intro ω hwa hwb
      exact hab (hwa.symm.trans hwb)
    have hm : ∀ σ ∈ FB, MeasurableSet
        {ω | pareto_hash_order (fun v ↦ source.hash v ω) = σ} := by
      intro σ hσ
      exact (pareto_hash_order_fiber_measurable σ).preimage
        (measurable_pi_lambda _ source.hash_measurable)
    rw [show {ω | pareto_hash_order (fun v ↦ source.hash v ω) ∈ B} =
        ⋃ σ ∈ FB, {ω | pareto_hash_order (fun v ↦ source.hash v ω) = σ} by
      ext ω
      simp [FB]]
    rw [MeasureTheory.measure_biUnion_finset hdis hm]
    unfold pmf_event
    simp only [FB, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro σ hσ
    by_cases hσB : σ ∈ B
    · simpa [hσB] using hlaw σ
    · simp [hσB]
  rw [← hleft, ← hright]
  change μ (noiseBlock ⁻¹' (priorityMap ⁻¹' A) ∩ hashBlock ⁻¹' D) = _
  rw [hfactor]
  have hnoiseEvent : noiseBlock ⁻¹' (priorityMap ⁻¹' A) =
      {ω | (priorityMap ∘ noiseBlock) ω ∈ A} := rfl
  have hhashEvent : hashBlock ⁻¹' D =
      {ω | pareto_hash_order (fun v ↦ source.hash v ω) ∈ B} := by
    ext ω
    have heq := congrFun hright ω
    simpa [D, Function.comp_def] using congrArg (fun x ↦ x ∈ B) heq
  rw [hnoiseEvent, hhashEvent, horderB]

@[blueprint "lem:active-record-count-bounded-by-record-count"
  (statement := /-- For every extended priority vector and every permutation, the number of
  active strict prefix records is at most the lexicographically tie-broken prefix-record
  count. -/)
  (proof := /-- Each active strict record is a tie-broken prefix record. For an earlier
  position this follows from strict priority minimality; for the position itself, equality
  of priorities and reflexivity of the coordinate-label order apply. Inclusion of the two
  filtered finite sets gives the cardinality inequality. -/)
  (title := /-- Active records are bounded by tie-broken records -/)
  (latexEnv := "lemma")]
lemma active_record_count_bounded_by_record_count {n : ℕ} (priority : Fin n → ENNReal)
    (σ : Equiv.Perm (Fin n)) :
    active_record_count priority σ ≤ record_count priority σ := by
  classical
  unfold active_record_count record_count
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rcases hi with ⟨hfinite, hstrict⟩
  intro j hji
  rcases Nat.lt_or_eq_of_le hji with hjlt | hjeq
  · exact Or.inl (hstrict j hjlt)
  · have hfin : j = i := Fin.ext hjeq
    subst j
    exact Or.inr ⟨rfl, le_rfl⟩

@[blueprint "lem:pareto-hashes-almost-surely-injective"
  (statement := /-- On a probability space carrying a Pareto random source, the finite hash
  vector is injective almost surely. -/)
  (proof := /-- By \cref{def:pareto-random-source}, every pair of distinct hash coordinates
  is independent and has the uniform law on $(0,1]$. Their joint law is therefore the
  product of two restricted Lebesgue measures. This product assigns measure zero to the
  diagonal because restricted Lebesgue measure is atomless. Intersecting these full-measure
  pairwise-inequality events over the finite coordinate type proves injectivity almost
  surely. -/)
  (title := /-- Almost-sure injectivity of Pareto hashes -/)
  (latexEnv := "lemma")]
lemma pareto_hashes_almost_surely_injective {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (updates : List (incremental_update n))
    (source : pareto_random_source Ω n updates.length μ) :
    ∀ᵐ ω ∂μ, Function.Injective (fun v ↦ source.hash v ω) := by
  let ν : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.Ioc 0 1)
  have hhash : ProbabilityTheory.iIndepFun source.hash μ := by
    simpa using source.jointly_independent.precomp Sum.inl_injective
  have hlaw : ∀ v, MeasureTheory.Measure.map (source.hash v) μ = ν := by
    intro v
    simpa [ν, has_uniform_unit_law, has_law] using source.hash_uniform v
  have hpairs : ∀ i j : Fin n, i ≠ j →
      ∀ᵐ ω ∂μ, source.hash i ω ≠ source.hash j ω := by
    intro i j hij
    have hpair := (hhash.indepFun hij).map_prod_eq_prod_map_map
      (source.hash_measurable i).aemeasurable (source.hash_measurable j).aemeasurable
    rw [hlaw i, hlaw j] at hpair
    have hprod : ∀ᵐ z ∂ν.prod ν, z.1 ≠ z.2 := by
      have hne_meas : MeasurableSet {z : ℝ × ℝ | z.1 ≠ z.2} := by
        exact (measurableSet_eq_fun measurable_fst measurable_snd).compl
      rw [MeasureTheory.Measure.ae_prod_iff_ae_ae hne_meas]
      filter_upwards with x
      exact (ν.ae_ne x).mono (fun y hy ↦ Ne.symm hy)
    rw [MeasureTheory.ae_iff]
    rw [show {ω | ¬source.hash i ω ≠ source.hash j ω} =
        (fun ω ↦ (source.hash i ω, source.hash j ω)) ⁻¹'
          {z : ℝ × ℝ | z.1 = z.2} by ext; simp]
    rw [← MeasureTheory.Measure.map_apply
      ((source.hash_measurable i).prodMk (source.hash_measurable j))
      (measurableSet_eq_fun measurable_fst measurable_snd)]
    rw [hpair]
    simpa [MeasureTheory.ae_iff] using hprod
  change ∀ᵐ ω ∂μ, ∀ ⦃i j : Fin n⦄, source.hash i ω = source.hash j ω → i = j
  rw [MeasureTheory.ae_all_iff]
  intro i
  rw [MeasureTheory.ae_all_iff]
  intro j
  by_cases hij : i = j
  · simp [hij]
  · exact (hpairs i j hij).mono (fun ω hne heq ↦ (hne heq).elim)

@[blueprint "lem:pareto-noises-almost-surely-nonnegative"
  (statement := /-- On a probability space carrying a Pareto random source, every noise
  variable in the finite stream is nonnegative almost surely. -/)
  (proof := /-- Apply \cref{lem:exponential-survival-of-has-law} at threshold zero to each
  rate-one exponential noise variable. Each variable is in fact strictly positive with
  probability one. Intersecting these full-measure events over the finite update-index type
  gives simultaneous nonnegativity. -/)
  (title := /-- Almost-sure nonnegativity of Pareto noises -/)
  (latexEnv := "lemma")]
lemma pareto_noises_almost_surely_nonnegative {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (updates : List (incremental_update n))
    (source : pareto_random_source Ω n updates.length μ) :
    ∀ᵐ ω ∂μ, ∀ i, 0 ≤ source.noise i ω := by
  rw [MeasureTheory.ae_all_iff]
  intro i
  have hreal := exponential_survival_of_has_law μ (source.noise i)
    (source.noise_measurable i) 1 (by norm_num) (source.noise_exponential i) 0
  have hprob : μ {ω | 0 < source.noise i ω} = 1 := by
    apply (ENNReal.toReal_eq_one_iff _).mp
    norm_num at hreal
    exact hreal
  have hpos : ∀ᵐ ω ∂μ, 0 < source.noise i ω :=
    (MeasureTheory.ae_iff_prob_eq_one
      (measurable_const.lt (source.noise_measurable i))).2 hprob
  exact hpos.mono (fun ω hω ↦ hω.le)

@[blueprint "def:pareto-minimum-update-index"
  (statement := /-- For a coordinate having an active update at time $t$, choose an active
  update whose scaled noise priority is minimal among the active updates of that coordinate. -/)
  (title := /-- A minimum-priority update index -/)
  (latexEnv := "definition")]
noncomputable def pareto_minimum_update_index {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ) (ω : Ω) (t : ℕ) (v : Fin n)
    (hv : (active_update_indices updates t v).Nonempty) : Fin updates.length :=
  Classical.choose (Finset.exists_min_image (active_update_indices updates t v)
    (fun i ↦ source.noise i ω / (updates.get i).increment) hv)

@[blueprint "lem:pareto-minimum-update-index-specification"
  (statement := /-- The chosen minimum update belongs to the active set and its scaled noise
  priority is at most that of every other active update of the same coordinate. -/)
  (proof := /-- This is the membership and minimality assertion supplied by the finite-set
  minimizer used in \cref{def:pareto-minimum-update-index}. -/)
  (title := /-- Specification of the minimum update index -/)
  (latexEnv := "lemma")]
lemma pareto_minimum_update_index_specification {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ) (ω : Ω) (t : ℕ) (v : Fin n)
    (hv : (active_update_indices updates t v).Nonempty) :
    pareto_minimum_update_index updates μ source ω t v hv ∈ active_update_indices updates t v ∧
      ∀ j ∈ active_update_indices updates t v,
        source.noise (pareto_minimum_update_index updates μ source ω t v hv) ω /
            (updates.get (pareto_minimum_update_index updates μ source ω t v hv)).increment ≤
          source.noise j ω / (updates.get j).increment := by
  exact Classical.choose_spec (Finset.exists_min_image (active_update_indices updates t v)
    (fun i ↦ source.noise i ω / (updates.get i).increment) hv)

@[blueprint "lem:coordinate-priority-at-minimum-update"
  (statement := /-- If a coordinate has an active update, then its extended coordinate
  priority equals the nonnegative-real embedding of the scaled noise at the chosen minimum
  update. -/)
  (proof := /-- Unfold the finite minimum in \cref{def:coordinate-priority}. The chosen
  value belongs to the finite image and, by
  \cref{lem:pareto-minimum-update-index-specification}, is a lower bound for every member.
  The two defining inequalities for the finite minimum give equality. -/)
  (title := /-- Coordinate priority is attained at the chosen update -/)
  (latexEnv := "lemma")]
lemma coordinate_priority_at_minimum_update {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ) (ω : Ω) (t : ℕ) (v : Fin n)
    (hv : (active_update_indices updates t v).Nonempty) :
    coordinate_priority updates μ source ω t v =
      ENNReal.ofReal
        (source.noise (pareto_minimum_update_index updates μ source ω t v hv) ω /
          (updates.get (pareto_minimum_update_index updates μ source ω t v hv)).increment) := by
  classical
  let s := active_update_indices updates t v
  let f : Fin updates.length → ENNReal := fun i ↦
    ENNReal.ofReal (source.noise i ω / (updates.get i).increment)
  have hspec := pareto_minimum_update_index_specification updates μ source ω t v hv
  unfold coordinate_priority finite_minimum_with_infinity
  simp only [hv, dite_true]
  apply le_antisymm
  · apply Finset.min'_le
    exact Finset.mem_image.2 ⟨_, hspec.1, rfl⟩
  · apply Finset.le_min'
    intro x hx
    rcases Finset.mem_image.1 hx with ⟨j, hj, rfl⟩
    exact ENNReal.ofReal_le_ofReal (hspec.2 j hj)

@[blueprint "lem:coordinate-priority-bounds-active-update"
  (statement := /-- The coordinate priority is at most the embedded scaled-noise priority of
  every active update of that coordinate. -/)
  (proof := /-- The active update contributes its value to the nonempty finite image whose
  minimum defines \cref{def:coordinate-priority}; the minimum is at most each member. -/)
  (title := /-- Coordinate priority bounds each active update -/)
  (latexEnv := "lemma")]
lemma coordinate_priority_bounds_active_update {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (updates : List (incremental_update n)) (μ : MeasureTheory.Measure Ω)
    (source : pareto_random_source Ω n updates.length μ) (ω : Ω) (t : ℕ)
    (j : Fin updates.length) (hj : j.val < t) :
    coordinate_priority updates μ source ω t (updates.get j).index ≤
      ENNReal.ofReal (source.noise j ω / (updates.get j).increment) := by
  classical
  have hjmem : j ∈ active_update_indices updates t (updates.get j).index := by
    simp [active_update_indices, hj]
  have hs : (active_update_indices updates t (updates.get j).index).Nonempty :=
    ⟨j, hjmem⟩
  unfold coordinate_priority finite_minimum_with_infinity
  simp only [hs, dite_true]
  apply Finset.min'_le
  exact Finset.mem_image.2 ⟨j, hjmem, rfl⟩

@[blueprint "lem:pareto-frontier-cardinality-is-active-record-count"
  (statement := /-- Fix a stream realization for which every primitive noise is nonnegative
  and the coordinate hashes are injective. Then the Pareto-state cardinality equals the
  active strict prefix-record count in hash order. -/)
  (proof := /-- Use \cref{def:pareto-minimum-update-index} to associate to every active
  record the minimum-priority tuple of its coordinate. The specification
  \cref{lem:pareto-minimum-update-index-specification}, the attainment identity
  \cref{lem:coordinate-priority-at-minimum-update}, and the lower bound
  \cref{lem:coordinate-priority-bounds-active-update} show that this tuple lies on the
  Pareto frontier. Strict increase of hashes along the order follows from
  \cref{lem:pareto-hash-order-strictly-increases-keys} and hash injectivity. Conversely,
  every frontier tuple must have minimum priority within its coordinate, and any earlier
  coordinate of no larger priority would dominate it. Thus its coordinate is an active
  record. The two constructions are inverse because a frontier contains at most one tuple
  for each coordinate, giving the cardinality equality. -/)
  (title := /-- Pareto-frontier cardinality as an active record count -/)
  (latexEnv := "lemma")]
lemma pareto_frontier_cardinality_is_active_record_count {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) {n : ℕ} (updates : List (incremental_update n))
    (source : pareto_random_source Ω n updates.length μ) (ω : Ω) (t : ℕ)
    (hnoise : ∀ i, 0 ≤ source.noise i ω)
    (hhash : Function.Injective (fun v ↦ source.hash v ω)) :
    (pareto_state updates μ source ω t).card =
      active_record_count (fun v ↦ coordinate_priority updates μ source ω t v)
        (pareto_hash_order (fun v ↦ source.hash v ω)) := by
  classical
  let priority : Fin n → ENNReal := fun v ↦ coordinate_priority updates μ source ω t v
  let σ := pareto_hash_order (fun v ↦ source.hash v ω)
  have hσhash : StrictMono (fun i ↦ source.hash (σ i) ω) := by
    intro i j hij
    have hk := pareto_hash_order_strictly_increases_keys
      (fun v ↦ source.hash v ω) hij
    rw [Prod.Lex.lt_iff] at hk
    rcases hk with hk | ⟨heq, hlabel⟩
    · exact hk
    · exfalso
      have hv : σ i = σ j := hhash heq
      exact (Fin.ne_of_lt hij) (σ.injective hv)
  have hactive : ∀ v, priority v ≠ ⊤ →
      (active_update_indices updates t v).Nonempty := by
    intro v hv
    by_contra hempty
    apply hv
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    simp [priority, coordinate_priority, finite_minimum_with_infinity, hempty]
  let R := (Finset.univ : Finset (Fin n)).filter
    (fun i ↦ is_active_prefix_record priority σ i)
  let recordTuple : ∀ i, i ∈ R → pareto_tuple n := fun i hi ↦ by
    have hri : is_active_prefix_record priority σ i := by simpa [R] using hi
    have hs := hactive (σ i) hri.1
    exact generated_pareto_tuple updates μ source ω
      (pareto_minimum_update_index updates μ source ω t (σ i) hs)
  have hrecord_mem : ∀ i hi, recordTuple i hi ∈ pareto_state updates μ source ω t := by
    intro i hi
    have hri : is_active_prefix_record priority σ i := by simpa [R] using hi
    have hs := hactive (σ i) hri.1
    let k := pareto_minimum_update_index updates μ source ω t (σ i) hs
    have hkspec := pareto_minimum_update_index_specification updates μ source ω t (σ i) hs
    have hkdata : k.val < t ∧ (updates.get k).index = σ i := by
      simpa [k, active_update_indices] using hkspec.1
    have hrindex : (recordTuple i hi).index = σ i := by
      change (updates.get (pareto_minimum_update_index updates μ source ω t (σ i) _)).index = σ i
      convert hkdata.2 using 1
    have hrgen : generated_pareto_tuple updates μ source ω k ∈
        generated_tuples updates μ source ω t := by
      apply Finset.mem_image.2
      exact ⟨k, by simp [hkdata.1], rfl⟩
    unfold pareto_state pareto_frontier
    simp only [Finset.mem_filter]
    refine ⟨hrgen, ?_⟩
    intro q hq hqr
    rcases Finset.mem_image.1 hq with ⟨j, hj, rfl⟩
    have hjt : j.val < t := by simpa using hj
    have hhash_le : source.hash (updates.get j).index ω ≤ source.hash (σ i) ω := by
      have hh := hqr.2
      change source.hash (updates.get j).index ω ≤ source.hash (recordTuple i hi).index ω at hh
      simpa [hrindex] using hh
    let pos := σ.symm (updates.get j).index
    have hpos : pos.val ≤ i.val := by
      by_contra hnot
      have hip : i < pos := Fin.mk_lt_mk.2 (Nat.lt_of_not_ge hnot)
      have hh := hσhash hip
      simp [pos] at hh
      exact (not_lt_of_ge hhash_le) hh
    rcases Nat.lt_or_eq_of_le hpos with hplt | hpeq
    · have hpri_strict := hri.2 pos hplt
      have hjbound := coordinate_priority_bounds_active_update updates μ source ω t j hjt
      have hkpriority := coordinate_priority_at_minimum_update updates μ source ω t (σ i) hs
      have hreal_le : source.noise j ω / (updates.get j).increment ≤
          source.noise k ω / (updates.get k).increment := hqr.1
      have hofreal := ENNReal.ofReal_le_ofReal hreal_le
      have hposindex : σ pos = (updates.get j).index := by simp [pos]
      rw [hposindex] at hpri_strict
      have : priority (σ i) < priority (σ i) := by
        calc
          priority (σ i) < priority (updates.get j).index := hpri_strict
          _ ≤ ENNReal.ofReal (source.noise j ω / (updates.get j).increment) := by
            simpa [priority] using hjbound
          _ ≤ ENNReal.ofReal (source.noise k ω / (updates.get k).increment) := hofreal
          _ = priority (σ i) := by simpa [priority, k] using hkpriority.symm
      exact (lt_irrefl _ this).elim
    · have hposeq : pos = i := Fin.ext hpeq
      have hindex : (updates.get j).index = σ i := by
        have := congrArg σ hposeq
        simpa [pos] using this
      have hjactive : j ∈ active_update_indices updates t (σ i) := by
        simp only [active_update_indices, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hjt, hindex⟩
      have hmin_le := hkspec.2 j hjactive
      constructor
      · simpa [pareto_tuple_coordinates, recordTuple, generated_pareto_tuple, k] using hmin_le
      · change source.hash (recordTuple i hi).index ω ≤ source.hash (updates.get j).index ω
        rw [hrindex, hindex]
  have hrecord_inj : ∀ i hi j hj, recordTuple i hi = recordTuple j hj → i = j := by
    intro i hi j hj heq
    have hindex := congrArg pareto_tuple.index heq
    have hri : is_active_prefix_record priority σ i := by simpa [R] using hi
    have hrj : is_active_prefix_record priority σ j := by simpa [R] using hj
    have hsi := hactive (σ i) hri.1
    have hsj := hactive (σ j) hrj.1
    have hispec := (pareto_minimum_update_index_specification updates μ source ω t (σ i) hsi).1
    have hjspec := (pareto_minimum_update_index_specification updates μ source ω t (σ j) hsj).1
    have hispecdata :
        (pareto_minimum_update_index updates μ source ω t (σ i) hsi).val < t ∧
          (updates.get (pareto_minimum_update_index updates μ source ω t (σ i) hsi)).index = σ i := by
      simpa [active_update_indices] using hispec
    have hjspecdata :
        (pareto_minimum_update_index updates μ source ω t (σ j) hsj).val < t ∧
          (updates.get (pareto_minimum_update_index updates μ source ω t (σ j) hsj)).index = σ j := by
      simpa [active_update_indices] using hjspec
    have hidxi : (recordTuple i hi).index = σ i := by
      simpa [recordTuple, generated_pareto_tuple] using hispecdata.2
    have hidxj : (recordTuple j hj).index = σ j := by
      simpa [recordTuple, generated_pareto_tuple] using hjspecdata.2
    apply σ.injective
    rw [← hidxi, heq, hidxj]
  have hrecord_surj : ∀ q ∈ pareto_state updates μ source ω t,
      ∃ i hi, recordTuple i hi = q := by
    intro q hq
    unfold pareto_state pareto_frontier at hq
    simp only [Finset.mem_filter] at hq
    rcases hq with ⟨hqgen, hfront⟩
    rcases Finset.mem_image.1 hqgen with ⟨j, hj, rfl⟩
    have hjt : j.val < t := by simpa using hj
    let v := (updates.get j).index
    have hs : (active_update_indices updates t v).Nonempty := by
      exact ⟨j, by simp [v, active_update_indices, hjt]⟩
    let k := pareto_minimum_update_index updates μ source ω t v hs
    have hkspec := pareto_minimum_update_index_specification updates μ source ω t v hs
    have hkdata : k.val < t ∧ (updates.get k).index = v := by
      simpa [k, active_update_indices] using hkspec.1
    have hkgen : generated_pareto_tuple updates μ source ω k ∈
        generated_tuples updates μ source ω t := by
      apply Finset.mem_image.2
      exact ⟨k, by simp [hkdata.1], rfl⟩
    have hkj_le : pareto_tuple_coordinates (generated_pareto_tuple updates μ source ω k) ≤
        pareto_tuple_coordinates (generated_pareto_tuple updates μ source ω j) := by
      refine ⟨hkspec.2 j (by simp [active_update_indices, hjt, v]), ?_⟩
      change source.hash (updates.get k).index ω ≤ source.hash (updates.get j).index ω
      rw [hkdata.2]
    have hjk_le := hfront _ hkgen hkj_le
    have hpriority_eq : source.noise k ω / (updates.get k).increment =
        source.noise j ω / (updates.get j).increment := le_antisymm hkj_le.1 hjk_le.1
    have htuple_eq : generated_pareto_tuple updates μ source ω k =
        generated_pareto_tuple updates μ source ω j := by
      have hindex_eq := hkdata.2
      change (updates.get k).index = (updates.get j).index at hindex_eq
      simp only [generated_pareto_tuple, pareto_tuple.mk.injEq]
      exact ⟨hpriority_eq, congrArg (fun w ↦ source.hash w ω) hindex_eq, hindex_eq⟩
    let i := σ.symm v
    have hfinite : priority v ≠ ⊤ := by
      change coordinate_priority updates μ source ω t v ≠ ⊤
      rw [coordinate_priority_at_minimum_update updates μ source ω t v hs]
      exact ENNReal.ofReal_ne_top
    have hri : is_active_prefix_record priority σ i := by
      refine ⟨by simpa [i] using hfinite, ?_⟩
      intro a hai
      have hhash_lt : source.hash (σ a) ω < source.hash v ω := by
        have := hσhash hai
        simpa [i] using this
      by_contra hnlt
      have hσi : σ i = v := by simp [i]
      rw [hσi] at hnlt
      have hle : priority (σ a) ≤ priority v := le_of_not_gt hnlt
      have hafin : priority (σ a) ≠ ⊤ := by
        exact ne_top_of_le_ne_top hfinite hle
      have hsa := hactive (σ a) hafin
      let ka := pareto_minimum_update_index updates μ source ω t (σ a) hsa
      have haspec := pareto_minimum_update_index_specification updates μ source ω t (σ a) hsa
      have hakdata : ka.val < t ∧ (updates.get ka).index = σ a := by
        simpa [ka, active_update_indices] using haspec.1
      have hagen : generated_pareto_tuple updates μ source ω ka ∈
          generated_tuples updates μ source ω t := by
        apply Finset.mem_image.2
        exact ⟨ka, by simp [hakdata.1], rfl⟩
      have hpa := coordinate_priority_at_minimum_update updates μ source ω t (σ a) hsa
      have hpv := coordinate_priority_at_minimum_update updates μ source ω t v hs
      have hreal_le : source.noise ka ω / (updates.get ka).increment ≤
          source.noise j ω / (updates.get j).increment := by
        rw [← hpriority_eq]
        apply (ENNReal.ofReal_le_ofReal_iff (by
          exact div_nonneg (hnoise k) (le_of_lt (updates.get k).increment_pos))).1
        simpa [priority, hpa, hpv, k] using hle
      have hdom : pareto_tuple_coordinates (generated_pareto_tuple updates μ source ω ka) ≤
          pareto_tuple_coordinates (generated_pareto_tuple updates μ source ω j) :=
        ⟨hreal_le, by
          change source.hash (updates.get ka).index ω ≤ source.hash (updates.get j).index ω
          rw [hakdata.2]
          simpa [v] using hhash_lt.le⟩
      have hreverse := hfront _ hagen hdom
      have hhrev : source.hash v ω ≤ source.hash (σ a) ω := by
        have hh := hreverse.2
        change source.hash (updates.get j).index ω ≤ source.hash (updates.get ka).index ω at hh
        rw [hakdata.2] at hh
        simpa [v] using hh
      exact (not_lt_of_ge hhrev) hhash_lt
    have hiR : i ∈ R := by simpa [R]
    refine ⟨i, hiR, ?_⟩
    dsimp [recordTuple]
    have hσi : σ i = v := by simp [i]
    subst v
    convert htuple_eq using 1 <;> simp [k, i]
  have hcard := Finset.card_bij recordTuple hrecord_mem hrecord_inj hrecord_surj
  simpa [active_record_count, R, priority, σ] using hcard.symm

@[blueprint "lem:pareto-state-record-representation"
  (statement := /-- Let $\mu$ be a probability measure on a measurable space $\Omega$, let
  $n\in\mathbb N$, let an incremental stream over $[n]$ and a Pareto random source for that
  stream be fixed, and let $t\in\mathbb N$. There exists a random permutation of $[n]$ with
  the uniform law which is independent of the random coordinate-priority vector in the
  measurable-event sense. With $\mu$-probability one, the Pareto-state cardinality at time
  $t$ equals the active strict prefix-record count in this permutation, and this count is at
  most the prefix-record count obtained by breaking equal priorities by coordinate label. -/)
  (proof := /-- Define the random coordinate order by sorting the hash-and-label keys as in
  \cref{def:pareto-hash-order}. Its law is uniform by
  \cref{lem:pareto-hash-order-has-uniform-law}, and
  \cref{lem:pareto-priorities-independent-of-hash-order} gives the required measurable-event
  independence from the coordinate-priority vector. By
  \cref{lem:pareto-noises-almost-surely-nonnegative} and
  \cref{lem:pareto-hashes-almost-surely-injective}, almost every realization has
  nonnegative primitive noises and distinct coordinate hashes. On their intersection,
  \cref{lem:pareto-frontier-cardinality-is-active-record-count} identifies the Pareto-state
  cardinality with the active strict prefix-record count. Finally,
  \cref{lem:active-record-count-bounded-by-record-count} bounds this count by the
  label-tie-broken record count for every realization. Thus the conjunction of the equality
  and inequality holds outside a null set, and hence has probability one. -/)
  (title := /-- Pareto-frontier size as a record count -/)
  (latexEnv := "lemma")]
lemma pareto_state_record_representation {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (updates : List (incremental_update n))
    (source : pareto_random_source Ω n updates.length μ) (t : ℕ) :
    ∃ order : Ω → Equiv.Perm (Fin n),
      has_pmf_law order (uniform_permutation n) μ ∧
      independent_of_pmf
        (fun ω v ↦ coordinate_priority updates μ source ω t v) order
        (uniform_permutation n) μ ∧
      μ {ω |
        (pareto_state updates μ source ω t).card =
          active_record_count
            (fun v ↦ coordinate_priority updates μ source ω t v) (order ω) ∧
        active_record_count
            (fun v ↦ coordinate_priority updates μ source ω t v) (order ω) ≤
          record_count
            (fun v ↦ coordinate_priority updates μ source ω t v) (order ω)} = 1 := by
  let order : Ω → Equiv.Perm (Fin n) := fun ω ↦
    pareto_hash_order (fun v ↦ source.hash v ω)
  refine ⟨order, ?_, ?_, ?_⟩
  · simpa [order] using pareto_hash_order_has_uniform_law μ updates source
  · simpa [order] using pareto_priorities_independent_of_hash_order μ updates source t
  · have hgood := (pareto_noises_almost_surely_nonnegative μ updates source).and
        (pareto_hashes_almost_surely_injective μ updates source)
    have hevent : ∀ᵐ ω ∂μ,
        (pareto_state updates μ source ω t).card =
            active_record_count
              (fun v ↦ coordinate_priority updates μ source ω t v) (order ω) ∧
          active_record_count
              (fun v ↦ coordinate_priority updates μ source ω t v) (order ω) ≤
            record_count
              (fun v ↦ coordinate_priority updates μ source ω t v) (order ω) := by
      filter_upwards [hgood] with ω hω
      constructor
      · simpa [order] using pareto_frontier_cardinality_is_active_record_count
          μ updates source ω t hω.1 hω.2
      · exact active_record_count_bounded_by_record_count _ _
    have hcompl : μ {ω |
        (pareto_state updates μ source ω t).card =
            active_record_count
              (fun v ↦ coordinate_priority updates μ source ω t v) (order ω) ∧
          active_record_count
              (fun v ↦ coordinate_priority updates μ source ω t v) (order ω) ≤
            record_count
              (fun v ↦ coordinate_priority updates μ source ω t v) (order ω)}ᶜ = 0 := by
      exact hevent
    rw [MeasureTheory.measure_of_measure_compl_eq_zero hcompl,
      MeasureTheory.measure_univ]

@[blueprint "def:uniform-record-key"
  (statement := /-- The key of a coordinate is its priority followed lexicographically by
  its coordinate label. -/)
  (title := /-- Tie-broken priority key -/)
  (latexEnv := "definition")]
def uniform_record_key {n : ℕ} (priority : Fin n → ENNReal) (v : Fin n) :
    Lex (ENNReal × ℕ) :=
  toLex (priority v, v.val)

@[blueprint "lem:finset-strict-lower-card-injective"
  (statement := /-- Given an injective key from a finite set into a linear order, an element
  is determined by the number of keys in the set that are strictly below its key. -/)
  (proof := /-- If the key of $a$ is below the key of $b$, the elements with key below that
  of $a$ form a proper subset of those with key below that of $b$: inclusion follows by
  transitivity, and $a$ witnesses strictness. Their cardinalities are strictly ordered. The
  reverse inequality is symmetric, while equal keys identify the elements by injectivity. -/)
  (title := /-- Injectivity of finite-set rank -/)
  (latexEnv := "lemma")]
lemma finset_strict_lower_card_injective {α β : Type*} [LinearOrder β] (s : Finset α)
    (key : α → β) (hkey : Function.Injective key) :
    Function.Injective
      (fun x : {x // x ∈ s} ↦ (s.filter fun y ↦ key y < key x.1).card) := by
  classical
  intro a b h
  apply Subtype.ext
  rcases lt_trichotomy (key a.1) (key b.1) with hab | hab | hab
  · have hsub : s.filter (fun y ↦ key y < key a.1) ⊂
        s.filter (fun y ↦ key y < key b.1) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, ?_⟩
      · intro y hy
        simp only [Finset.mem_filter] at hy ⊢
        exact ⟨hy.1, lt_trans hy.2 hab⟩
      · intro heq
        have hm : a.1 ∈ s.filter (fun y ↦ key y < key b.1) := by
          simp [a.property, hab]
        rw [← heq] at hm
        simp at hm
    exact False.elim ((Nat.ne_of_lt (Finset.card_lt_card hsub)) h)
  · exact hkey hab
  · have hsub : s.filter (fun y ↦ key y < key b.1) ⊂
        s.filter (fun y ↦ key y < key a.1) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, ?_⟩
      · intro y hy
        simp only [Finset.mem_filter] at hy ⊢
        exact ⟨hy.1, lt_trans hy.2 hab⟩
      · intro heq
        have hm : b.1 ∈ s.filter (fun y ↦ key y < key a.1) := by
          simp [b.property, hab]
        rw [← heq] at hm
        simp at hm
    exact False.elim ((Nat.ne_of_gt (Finset.card_lt_card hsub)) h)

@[blueprint "def:uniform-record-rank"
  (statement := /-- The relative rank at position $i$ is the number of earlier-or-current
  entries whose tie-broken key is strictly smaller than the key at position $i$. -/)
  (title := /-- Relative rank in a permutation prefix -/)
  (latexEnv := "definition")]
noncomputable def uniform_record_rank {n : ℕ} (priority : Fin n → ENNReal)
  (σ : Equiv.Perm (Fin n)) (i : Fin n) : Fin (i.val + 1) := by
  classical
  refine ⟨(((Finset.Iic i).image σ).filter fun v ↦
    uniform_record_key priority v < uniform_record_key priority (σ i)).card, ?_⟩
  calc
    _ < ((Finset.Iic i).image σ).card :=
      Finset.card_lt_card ((Finset.filter_ssubset).2 ⟨σ i, by simp, by simp⟩)
    _ = (Finset.Iic i).card := Finset.card_image_of_injective _ σ.injective
    _ = i.val + 1 := Fin.card_Iic i

@[blueprint "lem:uniform-record-rank-zero"
  (statement := /-- A position is a prefix record exactly when its relative rank in the
  prefix is zero. -/)
  (proof := /-- Unfold \cref{def:is-prefix-record},
  \cref{def:uniform-record-rank}, and \cref{def:uniform-record-key}. The rank is zero
  precisely when no key in the prefix is strictly smaller than the current key, which by
  linearity of the lexicographic order is precisely the prefix-record condition. -/)
  (title := /-- Prefix records have relative rank zero -/)
  (latexEnv := "lemma")]
lemma uniform_record_rank_zero {n : ℕ} (priority : Fin n → ENNReal)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    is_prefix_record priority σ i ↔ uniform_record_rank priority σ i = 0 := by
  classical
  simp [is_prefix_record, uniform_record_rank, uniform_record_key,
    Prod.Lex.toLex_le_toLex]

@[blueprint "lem:permutation-prefix-image-eq-of-suffix-eq"
  (statement := /-- If two permutations agree at every position strictly after $i$, then
  the sets of values occurring through position $i$ are equal. -/)
  (proof := /-- A value in the first prefix has a unique preimage under the second
  permutation. If that preimage were after $i$, suffix agreement and injectivity of the
  first permutation would identify it with the original prefix position, a contradiction.
  This proves one inclusion, and interchanging the permutations proves the other. -/)
  (title := /-- Equal suffixes have equal complementary prefix images -/)
  (latexEnv := "lemma")]
lemma permutation_prefix_image_eq_of_suffix_eq {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (i : Fin n) (h : ∀ j : Fin n, i.val < j.val → σ j = τ j) :
    (Finset.Iic i).image σ = (Finset.Iic i).image τ := by
  classical
  ext v
  constructor
  · intro hv
    rw [Finset.mem_image] at hv ⊢
    rcases hv with ⟨j, hj, rfl⟩
    refine ⟨τ.symm (σ j), ?_, by simp⟩
    simp only [Finset.mem_Iic]
    by_contra hk
    have hik : i.val < (τ.symm (σ j)).val := by simpa using lt_of_not_ge hk
    have heq : τ.symm (σ j) = j := by
      apply σ.injective
      calc
        σ (τ.symm (σ j)) = τ (τ.symm (σ j)) := h _ hik
        _ = σ j := by simp
    have hjle : j.val ≤ i.val := by simpa using hj
    omega
  · intro hv
    rw [Finset.mem_image] at hv ⊢
    rcases hv with ⟨j, hj, rfl⟩
    refine ⟨σ.symm (τ j), ?_, by simp⟩
    simp only [Finset.mem_Iic]
    by_contra hk
    have hik : i.val < (σ.symm (τ j)).val := by simpa using lt_of_not_ge hk
    have heq : σ.symm (τ j) = j := by
      apply τ.injective
      calc
        τ (σ.symm (τ j)) = σ (σ.symm (τ j)) := (h _ hik).symm
        _ = τ j := by simp
    have hjle : j.val ≤ i.val := by simpa using hj
    omega

@[blueprint "def:uniform-record-code"
  (statement := /-- The relative-rank code of a permutation records its relative rank at
  every position. -/)
  (title := /-- Relative-rank code of a permutation -/)
  (latexEnv := "definition")]
noncomputable def uniform_record_code {n : ℕ} (priority : Fin n → ENNReal)
    (σ : Equiv.Perm (Fin n)) : ∀ i : Fin n, Fin (i.val + 1) :=
  fun i ↦ uniform_record_rank priority σ i

@[blueprint "lem:uniform-record-code-injective"
  (statement := /-- For any fixed priority vector, the relative-rank code is injective on
  permutations. -/)
  (proof := /-- Compare two codes from \cref{def:uniform-record-code} from the last position
  backwards. Once the underlying permutations agree on their strict suffixes,
  \cref{lem:permutation-prefix-image-eq-of-suffix-eq} identifies the sets of values in their
  complementary prefixes. Equality of the current ranks from
  \cref{def:uniform-record-rank}, together with
  \cref{lem:finset-strict-lower-card-injective}, identifies the current values because the
  key from \cref{def:uniform-record-key} is injective. Reverse induction identifies every
  position. -/)
  (title := /-- Injectivity of the relative-rank code -/)
  (latexEnv := "lemma")]
lemma uniform_record_code_injective {n : ℕ} (priority : Fin n → ENNReal) :
    Function.Injective (uniform_record_code priority) := by
  classical
  intro σ τ hcode
  apply Equiv.ext
  intro i
  have hkey : Function.Injective (uniform_record_key priority) := by
    intro a b hab
    apply Fin.ext
    exact congrArg (fun z : Lex (ENNReal × ℕ) ↦ (ofLex z).2) hab
  have current_eq (k : Fin n)
      (htail : ∀ j : Fin n, k.val < j.val → σ j = τ j) : σ k = τ k := by
    let S := (Finset.Iic k).image σ
    have hS : S = (Finset.Iic k).image τ :=
      permutation_prefix_image_eq_of_suffix_eq σ τ k htail
    have hσ : σ k ∈ S := by simp [S]
    have hτ : τ k ∈ S := by rw [hS]; simp
    have hr := congrArg Fin.val (congrFun hcode k)
    simp only [uniform_record_code, uniform_record_rank] at hr
    change (S.filter fun v ↦ uniform_record_key priority v <
      uniform_record_key priority (σ k)).card = _ at hr
    rw [← hS] at hr
    have heq : (⟨σ k, hσ⟩ : {x // x ∈ S}) = ⟨τ k, hτ⟩ :=
      (finset_strict_lower_card_injective S (uniform_record_key priority) hkey) hr
    exact congrArg Subtype.val heq
  have wf : WellFounded (fun a b : Fin n ↦ n - 1 - a.val < n - 1 - b.val) :=
    WellFounded.onFun Nat.lt_wfRel.wf
  exact wf.induction i
    (fun k ih ↦ current_eq k (fun j hj ↦ ih j (by omega)))

@[blueprint "lem:uniform-record-code-bijective"
  (statement := /-- For any fixed priority vector, relative-rank coding is a bijection from
  permutations of $\operatorname{Fin}(n)$ to functions assigning position $i$ an element of
  $\operatorname{Fin}(i+1)$. -/)
  (proof := /-- For the code of \cref{def:uniform-record-code}, injectivity is
  \cref{lem:uniform-record-code-injective}. The permutation set has cardinality $n!$.
  The code space has cardinality
  $\prod_{i=0}^{n-1}(i+1)=n!$, so injectivity between these finite sets implies
  surjectivity. -/)
  (title := /-- Bijection with relative-rank codes -/)
  (latexEnv := "lemma")]
lemma uniform_record_code_bijective {n : ℕ} (priority : Fin n → ENNReal) :
    Function.Bijective (uniform_record_code priority) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨uniform_record_code_injective priority, ?_⟩
  have hprod := Fin.prod_univ_eq_prod_range (fun k : ℕ ↦ k + 1) n
  simp at hprod
  simp only [Fintype.card_perm, Fintype.card_pi, Fintype.card_fin]
  exact hprod.symm

@[blueprint "lem:card-dependent-functions-fixed-on-finset"
  (statement := /-- For a finite dependent family of finite types with chosen basepoints,
  the number of dependent functions fixed at the basepoint on an index set is the product
  of the cardinalities of the fibres outside that index set. -/)
  (proof := /-- Restriction sends each constrained function to a function on the complement
  of the fixed index set. Its inverse extends a complementary function by the chosen
  basepoints on the fixed indices. These operations are inverse by function extensionality,
  and the standard cardinality formula for a finite dependent product gives the result. -/)
  (title := /-- Cardinality of functions with fixed coordinates -/)
  (latexEnv := "lemma")]
lemma card_dependent_functions_fixed_on_finset {α : Type*} [Fintype α] [DecidableEq α]
    (β : α → Type*) [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (z : ∀ i, β i) (I : Finset α) :
    ({f | ∀ i ∈ I, f i = z i} : Finset (∀ i, β i)).card =
      ∏ i ∈ Finset.univ.filter (fun i ↦ i ∉ I), Fintype.card (β i) := by
  classical
  rw [← Fintype.card_subtype]
  let e : {f : ∀ i, β i // ∀ i ∈ I, f i = z i} ≃
      (∀ j : {i // i ∉ I}, β j.1) :=
    { toFun := fun f j ↦ f.1 j.1
      invFun := fun g ↦ ⟨fun i ↦ if hi : i ∈ I then z i else g ⟨i, hi⟩,
        by intro i hi; simp [hi]⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ I
        · simp [hi, f.property i hi]
        · simp [hi]
      right_inv := by
        intro g
        funext j
        simp [j.property] }
  rw [Fintype.card_congr e, Fintype.card_pi]
  have hp : ∀ x, x ∈ Finset.univ.filter (fun i ↦ i ∉ I) ↔
      (fun i ↦ i ∉ I) x := by simp
  rw [← Finset.prod_subtype (Finset.univ.filter (fun i ↦ i ∉ I)) hp
    (fun i ↦ Fintype.card (β i))]

@[blueprint "lem:uniform-record-code-zero-probability"
  (statement := /-- Under the uniform distribution on relative-rank codes, the probability
  that every coordinate in $I$ is zero is $\prod_{i\in I}(i+1)^{-1}$. -/)
  (proof := /-- By \cref{lem:card-dependent-functions-fixed-on-finset}, the number of codes
  vanishing on $I$ is the product of the fibre cardinalities outside $I$. Divide this by the
  product of all fibre cardinalities; cancellation of the positive complementary factors
  leaves the product of the inverse fibre cardinalities over $I$. -/)
  (title := /-- Zero-coordinate probability for uniform rank codes -/)
  (latexEnv := "lemma")]
lemma uniform_record_code_zero_probability {n : ℕ} (I : Finset (Fin n)) :
    (∑ c : (∀ i : Fin n, Fin (i.val + 1)),
      if ∀ i ∈ I, c i = 0 then
        (Fintype.card (∀ i : Fin n, Fin (i.val + 1)) : ENNReal)⁻¹ else 0) =
      ∏ i ∈ I, ((i.val + 1 : ℕ) : ENNReal)⁻¹ := by
  classical
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcount' :
      ({x | ∀ i ∈ I, x i = 0} : Finset (∀ i : Fin n, Fin (i.val + 1))).card =
        ∏ i ∈ Finset.univ.filter (fun i ↦ i ∉ I), (i.val + 1) := by
    convert card_dependent_functions_fixed_on_finset
      (fun i : Fin n ↦ Fin (i.val + 1)) (fun i ↦ 0) I using 1
    · congr 1
      ext c
      simp
    · simp
  rw [hcount']
  simp only [Fintype.card_pi, Fintype.card_fin, Nat.cast_prod]
  have hcompl : Finset.univ.filter (fun i : Fin n ↦ i ∉ I) = Iᶜ := by
    ext
    simp
  rw [hcompl]
  let a : Fin n → ENNReal := fun i ↦ (i.val + 1 : ℕ)
  have hall := Finset.prod_mul_prod_compl I a
  change (∏ i ∈ Iᶜ, a i) * (∏ i, a i)⁻¹ = ∏ i ∈ I, (a i)⁻¹
  rw [← hall]
  have hB0 : (∏ i ∈ Iᶜ, a i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    simp [a]
  have hBtop : (∏ i ∈ Iᶜ, a i) ≠ ⊤ := by
    apply ENNReal.prod_ne_top
    intro i hi
    simp [a]
  have hInvA : (∏ i ∈ I, a i)⁻¹ = ∏ i ∈ I, (a i)⁻¹ := by
    apply ENNReal.prod_inv_distrib
    intro i hi j hj hij
    left
    simp [a]
  rw [ENNReal.mul_inv (Or.inr hBtop) (Or.inr hB0), ← hInvA]
  calc
    (∏ i ∈ Iᶜ, a i) * ((∏ i ∈ I, a i)⁻¹ * (∏ i ∈ Iᶜ, a i)⁻¹) =
        (∏ i ∈ I, a i)⁻¹ * ((∏ i ∈ Iᶜ, a i) * (∏ i ∈ Iᶜ, a i)⁻¹) := by
      ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel hB0 hBtop, mul_one]

@[blueprint "lem:uniform-record-indicators"
  (statement := /-- For every $n\in\mathbb{N}$, priority vector
  $h:\operatorname{Fin}(n)\to[0,\infty]$, and subset $I\subseteq\operatorname{Fin}(n)$, order
  priority-coordinate pairs lexicographically and choose a permutation $\sigma$ uniformly.
  The probability that, for every $i\in I$, the pair $(h_{\sigma(i)},\sigma(i))$ is minimal
  among the pairs in positions $j\leq i$ is $\prod_{i\in I}(i+1)^{-1}$. -/)
  (proof := /-- By \cref{lem:uniform-record-rank-zero}, the joint prefix-record event is the
  event that the coordinates indexed by $I$ of \cref{def:uniform-record-code} are zero.
  The bijection \cref{lem:uniform-record-code-bijective} reindexes the uniform sum in
  \cref{def:pmf-event} for \cref{def:uniform-permutation} as the uniform sum over all rank
  codes. Finally, \cref{lem:uniform-record-code-zero-probability} evaluates that sum as
  $\prod_{i\in I}(i+1)^{-1}$. -/)
  (title := /-- Independence of record-minimum indicators -/)
  (latexEnv := "lemma")]
lemma uniform_record_indicators {n : ℕ} (priority : Fin n → ENNReal) :
    ∀ I : Finset (Fin n),
      pmf_event (uniform_permutation n)
        (fun σ ↦ ∀ i ∈ I, is_prefix_record priority σ i) =
      ∏ i ∈ I, ((i.val + 1 : ℕ) : ENNReal)⁻¹ := by
  classical
  intro I
  simp_rw [uniform_record_rank_zero]
  unfold pmf_event uniform_permutation
  simp only [PMF.uniformOfFintype_apply]
  let e : Equiv.Perm (Fin n) ≃ (∀ i : Fin n, Fin (i.val + 1)) :=
    Equiv.ofBijective (uniform_record_code priority)
      (uniform_record_code_bijective priority)
  calc
    (∑ x, if ∀ i ∈ I, uniform_record_rank priority x i = 0 then
        ((Fintype.card (Equiv.Perm (Fin n)) : ENNReal))⁻¹ else 0) =
        ∑ c : (∀ i : Fin n, Fin (i.val + 1)), if ∀ i ∈ I, c i = 0 then
          ((Fintype.card (Equiv.Perm (Fin n)) : ENNReal))⁻¹ else 0 := by
      apply Fintype.sum_equiv e
      intro σ
      simp [e, uniform_record_code]
    _ = _ := by
      rw [Fintype.card_congr e]
      exact uniform_record_code_zero_probability I

@[blueprint "lem:uniform-record-inverse-product"
  (statement := /-- For every $n\in\mathbb{N}$,
  $\prod_{i\in\operatorname{Fin}(n)}(1+(i+1)^{-1})=n+1$ in $[0,\infty]$. -/)
  (proof := /-- Separate the final factor and apply induction on $n$.  The final
  multiplication telescopes because $n+1$ is finite and nonzero in $[0,\infty]$. -/)
  (title := /-- Telescoping product of inverse record probabilities -/)
  (latexEnv := "lemma")]
lemma uniform_record_inverse_product (n : ℕ) :
    ∏ i : Fin n, (1 + ((i.val + 1 : ℕ) : ENNReal)⁻¹) = ((n + 1 : ℕ) : ENNReal) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      simp [mul_add, ENNReal.mul_inv_cancel]

@[blueprint "lem:uniform-record-two-moment"
  (statement := /-- For every $n\in\mathbb{N}$ and every priority vector
  $h:\operatorname{Fin}(n)\to[0,\infty]$, if $R$ is the record count of a uniformly
  random permutation, then $\mathbb{E}[2^R]=n+1$. -/)
  (proof := /-- Expand $2^R$ as the sum of the indicators that a subset of positions
  consists entirely of records.  Interchanging the two finite sums and applying
  \cref{lem:uniform-record-indicators} turns the moment into the sum, over all subsets,
  of the products of the corresponding inverse record probabilities.  The binomial
  product identity and \cref{lem:uniform-record-inverse-product} evaluate this sum as
  $n+1$. -/)
  (title := /-- Exponential moment of the uniform record count -/)
  (latexEnv := "lemma")]
lemma uniform_record_two_moment {n : ℕ} (priority : Fin n → ENNReal) :
    ∑ σ, uniform_permutation n σ * (2 : ENNReal) ^ record_count priority σ =
      ((n + 1 : ℕ) : ENNReal) := by
  classical
  calc
    ∑ σ, uniform_permutation n σ * (2 : ENNReal) ^ record_count priority σ =
        ∑ σ, ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
          if ∀ i ∈ I, is_prefix_record priority σ i then uniform_permutation n σ else 0 := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [show (2 : ENNReal) ^ record_count priority σ =
          ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
            if ∀ i ∈ I, is_prefix_record priority σ i then 1 else 0 by
        simp only [record_count]
        simp
        rw [show ({I | ∀ i ∈ I, is_prefix_record priority σ i} :
            Finset (Finset (Fin n))) =
            (Finset.univ.filter fun i => is_prefix_record priority σ i).powerset by
          ext I
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
          constructor
          · intro h i hi
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h i hi⟩
          · intro h i hi
            exact (Finset.mem_filter.mp (h hi)).2]
        simp [Finset.card_powerset], Finset.mul_sum]
      simp [mul_ite]
    _ = ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
        pmf_event (uniform_permutation n)
          (fun σ ↦ ∀ i ∈ I, is_prefix_record priority σ i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro I _
      unfold pmf_event
      apply Finset.sum_congr rfl
      intro σ _
      by_cases h : ∀ i ∈ I, is_prefix_record priority σ i <;> simp [h]
    _ = ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∏ i ∈ I, ((i.val + 1 : ℕ) : ENNReal)⁻¹ := by
      apply Finset.sum_congr rfl
      intro I _
      exact uniform_record_indicators priority I
    _ = ∏ i : Fin n, (1 + ((i.val + 1 : ℕ) : ENNReal)⁻¹) := by
      symm
      exact Finset.prod_one_add Finset.univ
    _ = ((n + 1 : ℕ) : ENNReal) := uniform_record_inverse_product n

@[blueprint "lem:uniform-record-count-tail"
  (statement := /-- For every $q\in\mathbb{N}$, there exists a constant $C\in\mathbb{R}$
  with $C>0$ such that, for every $n\in\mathbb{N}$ with $n\geq2$ and every priority vector
  $h:\operatorname{Fin}(n)\to[0,\infty]$, the probability that the record count of a
  uniformly random permutation exceeds $C(1+\log n)$ is at most $n^{-q}$. -/)
  (proof := /-- Let $R$ denote the record count and set
  $C=(q+2)/\log 2$, which is positive.  By
  \cref{lem:uniform-record-two-moment}, $\mathbb{E}[2^R]=n+1$.  On the event
  $R>C(1+\log n)$, multiplication by $\log 2>0$ and monotonicity of the logarithm give
  $2^R>n^{q+2}$.  Multiplying the probability of this event by $n^{q+2}$, bounding each
  summand by its contribution to $\mathbb{E}[2^R]$, and summing yields
  $\mathbb{P}(R>C(1+\log n))n^{q+2}\leq n+1$.  Since $n\geq2$ implies $n+1\leq n^2$,
  division by the positive number $n^{q+2}$ gives the required bound $n^{-q}$. -/)
  (title := /-- Polynomial tail for the number of records -/)
  (latexEnv := "lemma")]
lemma uniform_record_count_tail (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ priority : Fin n → ENNReal,
      (pmf_event (uniform_permutation n)
        (fun σ ↦ C * (1 + Real.log n) < (record_count priority σ : ℝ))).toReal ≤
      (n : ℝ)⁻¹ ^ q := by
  let C : ℝ := (q + 2 : ℕ) / Real.log 2
  have hlog_two : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C, div_pos (by positivity) hlog_two, ?_⟩
  intro n hn priority
  let E : Equiv.Perm (Fin n) → Prop := fun σ ↦
    C * (1 + Real.log n) < (record_count priority σ : ℝ)
  have hpoint : ∀ σ, E σ →
      ((n : ℕ) : ENNReal) ^ (q + 2) ≤
        (2 : ENNReal) ^ record_count priority σ := by
    intro σ hσ
    have hscaled : ((q + 2 : ℕ) : ℝ) * (1 + Real.log n) <
        (record_count priority σ : ℝ) * Real.log 2 := by
      calc
        ((q + 2 : ℕ) : ℝ) * (1 + Real.log n) =
            (C * (1 + Real.log n)) * Real.log 2 := by
          dsimp [C]
          field_simp
        _ < (record_count priority σ : ℝ) * Real.log 2 :=
          mul_lt_mul_of_pos_right hσ hlog_two
    have hlogs : Real.log ((n : ℝ) ^ (q + 2)) <
        (record_count priority σ : ℝ) * Real.log 2 := by
      rw [Real.log_pow]
      have hq : (0 : ℝ) < (q + 2 : ℕ) := by positivity
      nlinarith
    have hpows : (n : ℝ) ^ (q + 2) <
        (2 : ℝ) ^ record_count priority σ :=
      Real.pow_lt_of_lt_log (by norm_num) hlogs
    have hpows_nat : n ^ (q + 2) < 2 ^ record_count priority σ := by
      exact_mod_cast hpows
    exact_mod_cast hpows_nat.le
  have hweighted :
      pmf_event (uniform_permutation n) E * ((n : ℕ) : ENNReal) ^ (q + 2) ≤
        ∑ σ, uniform_permutation n σ * (2 : ENNReal) ^ record_count priority σ := by
    unfold pmf_event
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro σ _
    by_cases hσ : E σ
    · simp only [hσ, if_true]
      exact mul_le_mul_left' (hpoint σ hσ) _
    · simp [hσ]
  have hmoment :
      pmf_event (uniform_permutation n) E * ((n : ℕ) : ENNReal) ^ (q + 2) ≤
        ((n + 1 : ℕ) : ENNReal) := by
    calc
      _ ≤ ∑ σ, uniform_permutation n σ *
          (2 : ENNReal) ^ record_count priority σ := hweighted
      _ = ((n + 1 : ℕ) : ENNReal) := uniform_record_two_moment priority
  have hmoment_real :
      (pmf_event (uniform_permutation n) E).toReal * (n : ℝ) ^ (q + 2) ≤
        (n : ℝ) + 1 := by
    have := ENNReal.toReal_mono (by simp) hmoment
    rw [ENNReal.toReal_mul] at this
    convert this using 1 <;> norm_cast
  have hn_real : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hn_real
  change (pmf_event (uniform_permutation n) E).toReal ≤ (n : ℝ)⁻¹ ^ q
  calc
    (pmf_event (uniform_permutation n) E).toReal ≤
        ((n : ℝ) + 1) / (n : ℝ) ^ (q + 2) := by
      apply (le_div_iff₀ (pow_pos hn_pos _)).2
      exact_mod_cast hmoment_real
    _ ≤ (n : ℝ) ^ 2 / (n : ℝ) ^ (q + 2) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (le_of_lt hn_pos) _)
      nlinarith
    _ = (n : ℝ)⁻¹ ^ q := by
      rw [pow_add, inv_pow]
      field_simp

@[blueprint "lem:finite-pmf-independent-event-bound"
  (statement := /-- Let $X$ be a measurable random element and let $Y$ be an independent
  random element with values in a finite type and probability mass function $p$.  If every
  section of an event is measurable and has $p$-probability at most $b$, then the joint event
  obtained by evaluating the section at $X$ and $Y$ has probability at most $b$. -/)
  (proof := /-- Partition the range of $X$ according to the finite subset of values of $Y$
  for which the event holds.  The section measurability assumption makes every class in this
  partition measurable.  On each class, independence in
  \cref{def:independent-of-pmf} factors the joint probability into the class probability and
  the corresponding event probability from \cref{def:pmf-event}, which is at most $b$.
  Finite subadditivity and summation over the measurable partition give the result. -/)
  (title := /-- A finite independent conditional event bound -/)
  (latexEnv := "lemma")]
lemma finite_pmf_independent_event_bound
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [Fintype β]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (p : PMF β) (P : α → β → Prop)
    (hX : Measurable X) (hsection : ∀ y, MeasurableSet {x | P x y})
    (hindep : independent_of_pmf X Y p μ) (b : ENNReal)
    (hbound : ∀ x, pmf_event p (P x) ≤ b) :
    μ {ω | P (X ω) (Y ω)} ≤ b := by
  classical
  let pattern : α → Finset β := fun x ↦ Finset.univ.filter fun y ↦ P x y
  have hclass : ∀ s : Finset β, MeasurableSet {x | pattern x = s} := by
    intro s
    have heq : {x | pattern x = s} =
        ⋂ y : β, if y ∈ s then {x | P x y} else {x | ¬ P x y} := by
      ext x
      simp [pattern, Finset.ext_iff]
      constructor
      · intro h i
        specialize h i
        by_cases hi : i ∈ s <;> simp_all
      · intro h i
        specialize h i
        by_cases hi : i ∈ s <;> simp_all
    rw [heq]
    exact MeasurableSet.iInter fun y ↦ by
      by_cases hy : y ∈ s
      · simpa [hy] using hsection y
      · simp only [hy, if_false]
        change MeasurableSet ({x | P x y}ᶜ)
        exact (hsection y).compl
  have hevent : {ω | P (X ω) (Y ω)} =
      ⋃ s : Finset β, {ω | pattern (X ω) = s ∧ Y ω ∈ s} := by
    ext ω
    simp [pattern]
  have hsum : ∑ s : Finset β, μ {ω | pattern (X ω) = s} = μ Set.univ := by
    have hdisjoint : Set.PairwiseDisjoint
        (↑(Finset.univ : Finset (Finset β)))
        (fun s ↦ {ω | pattern (X ω) = s}) := by
      intro s hs t ht hst
      change Disjoint {ω | pattern (X ω) = s} {ω | pattern (X ω) = t}
      rw [Set.disjoint_left]
      intro ω hωs hωt
      exact hst (hωs.symm.trans hωt)
    have hmeasure := MeasureTheory.measure_biUnion_finset
      (μ := μ) hdisjoint (fun s _ ↦ (hclass s).preimage hX)
    calc
      ∑ s : Finset β, μ {ω | pattern (X ω) = s} =
          μ (⋃ s ∈ (Finset.univ : Finset (Finset β)),
            {ω | pattern (X ω) = s}) := by simpa using hmeasure.symm
      _ = μ Set.univ := by
        congr 1
        ext ω
        simp
  rw [hevent]
  calc
    μ (⋃ s : Finset β, {ω | pattern (X ω) = s ∧ Y ω ∈ s}) ≤
        ∑ s : Finset β, μ {ω | pattern (X ω) = s ∧ Y ω ∈ s} :=
      MeasureTheory.measure_iUnion_fintype_le μ _
    _ = ∑ s : Finset β,
        μ {ω | pattern (X ω) = s} * pmf_event p (fun y ↦ y ∈ s) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact hindep {x | pattern x = s} (hclass s) s
    _ ≤ ∑ s : Finset β, μ {ω | pattern (X ω) = s} * b := by
      apply Finset.sum_le_sum
      intro s hs
      by_cases hnonempty : ∃ x, pattern x = s
      · obtain ⟨x, hx⟩ := hnonempty
        apply mul_le_mul_left'
        simpa [pattern, ← hx] using hbound x
      · have hempty : {ω | pattern (X ω) = s} = ∅ := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
          constructor
          · exact fun hω ↦ hnonempty ⟨X ω, hω⟩
          · intro h
            contradiction
        simp [hempty]
    _ = (∑ s : Finset β, μ {ω | pattern (X ω) = s}) * b := by
      rw [Finset.sum_mul]
    _ = b := by simp [hsum]

@[blueprint "lem:pareto-state-single-time-tail"
  (statement := /-- For every $q\in\mathbb{N}$, there exists a constant $C>0$ such that,
  for every probability space, every $n\in\mathbb{N}$ with $n\geq 2$, every incremental
  update stream on $\operatorname{Fin}(n)$, every valid Pareto random source for that stream,
  and every time $t$ not exceeding the stream length, the probability that the Pareto state
  at time $t$ uses more than $C(1+\log n)$ words is at most $n^{-q}$. -/)
  (proof := /-- Let $C_0$ be the constant supplied by
  \cref{lem:uniform-record-count-tail} and set $C=3C_0$.  The priority-vector map is
  measurable by \cref{lem:pareto-priority-transform-measurable}, and its independence from
  the canonical hash order follows from
  \cref{lem:pareto-priorities-independent-of-hash-order}.  Applying
  \cref{lem:finite-pmf-independent-event-bound} to the record-count sections therefore
  transfers the uniform-permutation tail estimate to the random priority vector.  The
  independent order furnished by \cref{lem:pareto-state-record-representation} satisfies
  the same conditional bound, so the maximum of the two record-tail probabilities is still
  bounded by $n^{-q}$.  By \cref{lem:pareto-noises-almost-surely-nonnegative,
  lem:pareto-hashes-almost-surely-injective}, almost every realization has nonnegative
  noises and injective hashes.  On this event,
  \cref{lem:pareto-frontier-cardinality-is-active-record-count} identifies the frontier
  cardinality with the active record count, which
  \cref{lem:active-record-count-bounded-by-record-count} bounds by the canonical record
  count.  Consequently the event that three times the frontier cardinality exceeds
  $3C_0(1+\log n)$ is almost everywhere contained in the canonical record-tail event, and
  the preceding probability bound proves the claim. -/)
  (title := /-- Fixed-time space tail -/)
  (latexEnv := "lemma")]
lemma pareto_state_single_time_tail (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure μ] (n : ℕ), 2 ≤ n →
        ∀ (updates : List (incremental_update n))
          (source : pareto_random_source Ω n updates.length μ) (t : ℕ),
          t ≤ updates.length →
            μ.real {ω |
              C * (1 + Real.log n) < (pareto_space_words updates μ source ω t : ℝ)} ≤
                (n : ℝ)⁻¹ ^ q := by
  classical
  obtain ⟨C, hC, htail⟩ := uniform_record_count_tail q
  refine ⟨3 * C, mul_pos (by norm_num) hC, ?_⟩
  intro Ω _ μ _ n hn updates source t ht
  let priority : Ω → (Fin n → ENNReal) := fun ω v ↦
    coordinate_priority updates μ source ω t v
  let order : Ω → Equiv.Perm (Fin n) := fun ω ↦
    pareto_hash_order (fun v ↦ source.hash v ω)
  have hpriority : Measurable priority := by
    let noiseVector : Ω → (Fin updates.length → ℝ) := fun ω i ↦ source.noise i ω
    have hnoiseVector : Measurable noiseVector :=
      measurable_pi_lambda _ source.noise_measurable
    change Measurable
      ((fun z : Fin updates.length → ℝ ↦ fun v ↦
        finite_minimum_with_infinity (active_update_indices updates t v)
          (fun i ↦ ENNReal.ofReal (z i / (updates.get i).increment))) ∘ noiseVector)
    exact (pareto_priority_transform_measurable updates t).comp hnoiseVector
  have hindep : independent_of_pmf priority order (uniform_permutation n) μ := by
    simpa [priority, order] using
      pareto_priorities_independent_of_hash_order μ updates source t
  let recordEvent : (Fin n → ENNReal) → Equiv.Perm (Fin n) → Prop :=
    fun x σ ↦ C * (1 + Real.log n) < (record_count x σ : ℝ)
  have hsection : ∀ σ, MeasurableSet {x | recordEvent x σ} := by
    intro σ
    have hfilter : Measurable (fun x : Fin n → ENNReal ↦
        Finset.univ.filter fun i ↦ is_prefix_record x σ i) := by
      rw [measurable_finset_iff]
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold is_prefix_record
      measurability
    have hcard : Measurable (fun x : Fin n → ENNReal ↦
        ((Finset.univ.filter fun i ↦ is_prefix_record x σ i).card : ℝ)) :=
      (measurable_of_countable
        (fun s : Finset (Fin n) ↦ (s.card : ℝ))).comp hfilter
    simpa [recordEvent, record_count] using measurableSet_lt measurable_const hcard
  have hpmfBound : ∀ x, pmf_event (uniform_permutation n) (recordEvent x) ≤
      ENNReal.ofReal ((n : ℝ)⁻¹ ^ q) := by
    intro x
    have hfinite : pmf_event (uniform_permutation n) (recordEvent x) ≠ ⊤ := by
      unfold pmf_event
      rw [ENNReal.sum_ne_top]
      intro σ
      intro hσ
      split_ifs
      · exact PMF.apply_ne_top _ _
      · simp
    apply (ENNReal.le_ofReal_iff_toReal_le hfinite (by positivity)).2
    simpa [recordEvent] using htail n hn x
  have hrecord :
      μ {ω | recordEvent (priority ω) (order ω)} ≤
        ENNReal.ofReal ((n : ℝ)⁻¹ ^ q) :=
    finite_pmf_independent_event_bound μ priority order (uniform_permutation n)
      recordEvent hpriority hsection hindep _ hpmfBound
  obtain ⟨representedOrder, _, hrepresentedIndep, _⟩ :=
    pareto_state_record_representation μ updates source t
  have hrecordRepresented :
      μ {ω | recordEvent (priority ω) (representedOrder ω)} ≤
        ENNReal.ofReal ((n : ℝ)⁻¹ ^ q) :=
    finite_pmf_independent_event_bound μ priority representedOrder (uniform_permutation n)
      recordEvent hpriority hsection (by simpa [priority] using hrepresentedIndep) _
        hpmfBound
  have hgood := (pareto_noises_almost_surely_nonnegative μ updates source).and
    (pareto_hashes_almost_surely_injective μ updates source)
  have hdom : ∀ᵐ ω ∂μ,
      (pareto_state updates μ source ω t).card ≤
        record_count (priority ω) (order ω) := by
    filter_upwards [hgood] with ω hω
    calc
      (pareto_state updates μ source ω t).card =
          active_record_count (priority ω) (order ω) := by
        simpa [priority, order] using
          pareto_frontier_cardinality_is_active_record_count
            μ updates source ω t hω.1 hω.2
      _ ≤ record_count (priority ω) (order ω) :=
        active_record_count_bounded_by_record_count _ _
  have hmeasure :
      μ {ω | (3 * C) * (1 + Real.log n) <
        (pareto_space_words updates μ source ω t : ℝ)} ≤
      μ {ω | recordEvent (priority ω) (order ω)} := by
    apply MeasureTheory.measure_mono_ae
    filter_upwards [hdom] with ω hω hlarge
    have hcard :
        C * (1 + Real.log n) <
          ((pareto_state updates μ source ω t).card : ℝ) := by
      change (3 * C) * (1 + Real.log n) <
        ((3 * (pareto_state updates μ source ω t).card : ℕ) : ℝ) at hlarge
      norm_num [Nat.cast_mul] at hlarge
      nlinarith
    have hω' :
        ((pareto_state updates μ source ω t).card : ℝ) ≤
          (record_count (priority ω) (order ω) : ℝ) := by
      exact_mod_cast hω
    exact hcard.trans_le hω'
  change
    (μ {ω | (3 * C) * (1 + Real.log n) <
      (pareto_space_words updates μ source ω t : ℝ)}).toReal ≤
      (n : ℝ)⁻¹ ^ q
  have hcombined :
      max (μ {ω | recordEvent (priority ω) (order ω)})
          (μ {ω | recordEvent (priority ω) (representedOrder ω)}) ≤
        ENNReal.ofReal ((n : ℝ)⁻¹ ^ q) :=
    max_le hrecord hrecordRepresented
  have hfinal := ENNReal.toReal_mono (by simp)
    (hmeasure.trans ((le_max_left _ _).trans hcombined))
  simpa using hfinal

@[blueprint "lem:pareto-sampler-space-bound"
  (statement := /-- For every $d,q\in\mathbb{N}$, there exists a constant $C>0$ such that,
  for every probability space, every $n\in\mathbb{N}$ with $n\geq 2$, every incremental
  update stream on $\operatorname{Fin}(n)$ of length at most $n^d$, and every valid Pareto
  random source for that stream, the state uses at most $C(1+\log n)$ words simultaneously
  at every stream time with probability at least $1-n^{-q}$. -/)
  (proof := /-- Apply \cref{lem:pareto-state-single-time-tail} with exponent $q+d+1$ and
  let $C>0$ be its uniform constant. The union bound over the
  $\operatorname{length}(\mathtt{updates})+1$ prefixes bounds the probability of any
  violation by
  \[
    (\operatorname{length}(\mathtt{updates})+1)n^{-(q+d+1)}.
  \]
  Since $n\geq2$ and the stream length is at most $n^d$, the number of prefixes is at most
  $n^{d+1}$, so this bound is at most $n^{-q}$. The simultaneous good event together with
  the union of the bad prefix events covers the sample space. Subadditivity therefore gives
  probability at least $1-n^{-q}$ to the good event. -/)
  (title := /-- Logarithmic space throughout a polynomial stream -/)
  (latexEnv := "lemma")]
lemma pareto_sampler_space_bound (d q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure μ] (n : ℕ), 2 ≤ n →
        ∀ (updates : List (incremental_update n))
          (source : pareto_random_source Ω n updates.length μ),
          updates.length ≤ n ^ d →
            1 - (n : ℝ)⁻¹ ^ q ≤
              μ.real {ω | ∀ t : ℕ, t ≤ updates.length →
                (pareto_space_words updates μ source ω t : ℝ) ≤
                  C * (1 + Real.log n)} := by
  classical
  obtain ⟨C, hC, htail⟩ := pareto_state_single_time_tail (q + d + 1)
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ n hn updates source hlength
  let bad : Set Ω :=
    ⋃ t : Fin (updates.length + 1),
      {ω | C * (1 + Real.log n) <
        (pareto_space_words updates μ source ω t : ℝ)}
  have hbad :
      μ.real bad ≤ ((updates.length + 1 : ℕ) : ℝ) *
        (n : ℝ)⁻¹ ^ (q + d + 1) := by
    calc
      μ.real bad ≤ ∑ t : Fin (updates.length + 1),
          μ.real {ω | C * (1 + Real.log n) <
            (pareto_space_words updates μ source ω t : ℝ)} :=
        MeasureTheory.measureReal_iUnion_fintype_le _
      _ ≤ ∑ _t : Fin (updates.length + 1),
          (n : ℝ)⁻¹ ^ (q + d + 1) := by
        apply Finset.sum_le_sum
        intro t ht
        exact htail Ω μ n hn updates source t (by omega)
      _ = ((updates.length + 1 : ℕ) : ℝ) *
          (n : ℝ)⁻¹ ^ (q + d + 1) := by simp
  have hnpos : 0 < n := by omega
  have hcount_nat : updates.length + 1 ≤ n ^ (d + 1) := by
    calc
      updates.length + 1 ≤ n ^ d + 1 := Nat.add_le_add_right hlength 1
      _ ≤ n ^ d * n := by
        have hpowpos : 0 < n ^ d := pow_pos hnpos d
        nlinarith
      _ = n ^ (d + 1) := by rw [pow_succ]
  have hcount : ((updates.length + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ (d + 1) := by
    exact_mod_cast hcount_nat
  have hnpos_real : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hpower :
      (n : ℝ) ^ (d + 1) * (n : ℝ)⁻¹ ^ (q + d + 1) =
        (n : ℝ)⁻¹ ^ q := by
    rw [show q + d + 1 = q + (d + 1) by omega]
    rw [pow_add (n : ℝ)⁻¹ q (d + 1)]
    calc
      (n : ℝ) ^ (d + 1) * ((n : ℝ)⁻¹ ^ q * (n : ℝ)⁻¹ ^ (d + 1)) =
          (n : ℝ)⁻¹ ^ q * ((n : ℝ) ^ (d + 1) * (n : ℝ)⁻¹ ^ (d + 1)) := by ring
      _ = (n : ℝ)⁻¹ ^ q := by simp [ne_of_gt hnpos_real]
  have hbad_final : μ.real bad ≤ (n : ℝ)⁻¹ ^ q :=
    hbad.trans <| calc
      ((updates.length + 1 : ℕ) : ℝ) * (n : ℝ)⁻¹ ^ (q + d + 1) ≤
          (n : ℝ) ^ (d + 1) * (n : ℝ)⁻¹ ^ (q + d + 1) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = (n : ℝ)⁻¹ ^ q := hpower
  let good : Set Ω := {ω | ∀ t : ℕ, t ≤ updates.length →
    (pareto_space_words updates μ source ω t : ℝ) ≤ C * (1 + Real.log n)}
  have hcover : good ∪ bad = Set.univ := by
    ext ω
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hω : ω ∈ good
    · exact Or.inl hω
    · right
      simp only [good, Set.mem_setOf_eq] at hω
      push Not at hω
      obtain ⟨t, ht, hviolate⟩ := hω
      exact Set.mem_iUnion.2 ⟨⟨t, by omega⟩, hviolate⟩
  have htotal : (1 : ℝ) ≤ μ.real good + μ.real bad := by
    have hunion := MeasureTheory.measureReal_union_le (μ := μ) good bad
    rw [hcover] at hunion
    simpa using hunion
  change 1 - (n : ℝ)⁻¹ ^ q ≤ μ.real good
  linarith

@[blueprint "lem:measurable-lexicographic-list-minimum"
  (statement := /-- Let $\Omega$ and $I$ be measurable spaces, let $i_0\in I$, and let
  $L$ be a finite list in $I$. If $a_i:\Omega\to\mathbb R_+\cup\{\infty\}$ and
  $b_i:\Omega\to\mathbb R$ are measurable for every $i\in I$, then there is a measurable
  selector $j:\Omega\to I$ which belongs pointwise to $i_0::L$ and whose pair
  $(a_j,b_j)$ is lexicographically minimal among the pairs indexed by $i_0::L$.
  Moreover, both selected coordinate functions are measurable. -/)
  (proof := /-- Induct on $L$. For the empty list, use the constant selector $i_0$. At an
  insertion step, compare the new pair with the pair selected for the shorter list and use
  the new index precisely on the measurable event where its pair is no larger. This event is
  measurable because lexicographic comparison is the union of a strict inequality in the
  first coordinate and the intersection of equality there with weak inequality in the
  second coordinate. The two selected coordinate functions are therefore measurable by
  piecewise measurability. Totality and transitivity of the lexicographic order establish
  membership and minimality. -/)
  (title := /-- Measurable lexicographic minimum on a finite list -/)
  (latexEnv := "lemma")]
lemma measurable_lexicographic_list_minimum {Ω ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] (i₀ : ι) (l : List ι) (a : ι → Ω → ENNReal)
    (b : ι → Ω → ℝ) (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i)) :
    ∃ out : Ω → ι, Measurable out ∧
      Measurable (fun ω ↦ a (out ω) ω) ∧
      Measurable (fun ω ↦ b (out ω) ω) ∧
      (∀ ω, out ω ∈ i₀ :: l) ∧
      ∀ ω i, i ∈ i₀ :: l →
        (toLex (a (out ω) ω, b (out ω) ω) : ENNReal ×ₗ ℝ) ≤
          toLex (a i ω, b i ω) := by
  classical
  induction l with
  | nil =>
      refine ⟨fun _ ↦ i₀, measurable_const, ha i₀, hb i₀, ?_, ?_⟩
      · simp
      · intro ω i hi
        simp only [List.mem_singleton] at hi
        subst i
        exact le_rfl
  | cons i l ih =>
      obtain ⟨out, hout, haout, hbout, hout_mem, hout_min⟩ := ih
      let A : Ω → ENNReal := fun ω ↦ a (out ω) ω
      let B : Ω → ℝ := fun ω ↦ b (out ω) ω
      let E : Set Ω := {ω | a i ω < A ω ∨ a i ω = A ω ∧ b i ω ≤ B ω}
      have hE : MeasurableSet E := by
        dsimp [E]
        exact (measurableSet_lt (ha i) haout).union
          ((measurableSet_eq_fun (ha i) haout).inter (measurableSet_le (hb i) hbout))
      let next : Ω → ι := fun ω ↦ if ω ∈ E then i else out ω
      refine ⟨next, measurable_const.ite hE hout, ?_, ?_, ?_, ?_⟩
      · have heq : (fun ω ↦ a (next ω) ω) =
            fun ω ↦ if ω ∈ E then a i ω else A ω := by
          funext ω
          by_cases hω : ω ∈ E <;> simp [next, A, hω]
        rw [heq]
        exact (ha i).ite hE haout
      · have heq : (fun ω ↦ b (next ω) ω) =
            fun ω ↦ if ω ∈ E then b i ω else B ω := by
          funext ω
          by_cases hω : ω ∈ E <;> simp [next, B, hω]
        rw [heq]
        exact (hb i).ite hE hbout
      · intro ω
        by_cases hω : ω ∈ E
        · simp [next, hω]
        · rw [show next ω = out ω by simp [next, hω]]
          rcases List.mem_cons.mp (hout_mem ω) with h | h
          · exact List.mem_cons.mpr (Or.inl h)
          · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h)))
      · intro ω j hj
        by_cases hω : ω ∈ E
        · have hij :
              (toLex (a i ω, b i ω) : ENNReal ×ₗ ℝ) ≤ toLex (A ω, B ω) := by
            exact Prod.Lex.toLex_le_toLex.mpr hω
          rw [show next ω = i by simp [next, hω]]
          rcases List.mem_cons.mp hj with hj | hj
          · subst j
            exact hij.trans (hout_min ω i₀ (by simp))
          · rcases List.mem_cons.mp hj with rfl | hj
            · exact le_rfl
            · exact hij.trans (hout_min ω j (by simp [hj]))
        · have hji :
              (toLex (A ω, B ω) : ENNReal ×ₗ ℝ) ≤ toLex (a i ω, b i ω) := by
            apply le_of_not_ge
            exact fun h ↦ hω (Prod.Lex.toLex_le_toLex.mp h)
          rw [show next ω = out ω by simp [next, hω]]
          rcases List.mem_cons.mp hj with hj | hj
          · subst j
            exact hout_min ω i₀ (by simp)
          · rcases List.mem_cons.mp hj with rfl | hj
            · exact hji
            · exact hout_min ω j (by simp [hj])

@[blueprint "lem:pareto-sampler-constructed"
  (statement := /-- Let $\Omega$ be a measurable space with probability measure $\mu$, let
  $n\in\mathbb N$ satisfy $n>0$, let $U$ be a finite stream of positive incremental updates
  on $[n]$, and let $R$ be a Pareto random source for $U$ on $(\Omega,\mu)$. Then there exists
  a Pareto sampler run on $\Omega$ and $[n]$ which implements the Pareto sampler for
  $(U,\mu,R)$. -/)
  (proof := /-- For each admissible query $G$, choose the level function supplied by
  \cref{lem:admissible-level-function}. For every stream prefix, apply
  \cref{lem:measurable-lexicographic-list-minimum} to the generated tuples, ordering them
  first by their level and then by the sum of their two order coordinates; return the index
  of the selected tuple from \cref{def:generated-pareto-tuple}, and use an arbitrary fixed
  index when the prefix is empty. This gives the measurable output maps required by
  \cref{def:pareto-sampler-run}. If $G(x_t)>0$, the zero-value clause in
  \cref{def:level-function-spec} implies $t>0$, so the active update set is nonempty. The
  selected tuple has minimum level. If another generated tuple is coordinatewise below it,
  monotonicity from \cref{def:level-function-spec} and lexicographic minimality force equality
  of the sums of their coordinates; the coordinatewise inequalities then force equality in
  both coordinates. Thus the selected tuple lies in the frontier of
  \cref{def:pareto-frontier}, hence in the state of \cref{def:pareto-state}, and minimizes
  the level throughout that state. This is precisely the relation in
  \cref{def:implements-pareto-sampler}. -/)
  (title := /-- Construction of the universal Pareto sampler -/)
  (latexEnv := "lemma")]
lemma pareto_sampler_constructed {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (hn : 0 < n) (updates : List (incremental_update n))
    (source : pareto_random_source Ω n updates.length μ) :
    ∃ run : pareto_sampler_run Ω n, implements_pareto_sampler updates μ source run := by
  classical
  let ell : (G : ℝ → ℝ) → is_admissible_weight G → ℝ × ℝ → ENNReal :=
    fun G hG ↦ Classical.choose (admissible_level_function G hG)
  have hell (G : ℝ → ℝ) (hG : is_admissible_weight G) :
      level_function_spec G (ell G hG) :=
    Classical.choose_spec (admissible_level_function G hG)
  let active : ℕ → Finset (Fin updates.length) := fun t ↦
    Finset.univ.filter fun i ↦ i.val < t
  let firstScore (t : ℕ) (G : ℝ → ℝ) (hG : is_admissible_weight G)
      (i : Fin updates.length) (ω : Ω) : ENNReal :=
    ell G hG (pareto_tuple_coordinates
      (generated_pareto_tuple updates μ source ω i))
  let secondScore (i : Fin updates.length) (ω : Ω) : ℝ :=
    (generated_pareto_tuple updates μ source ω i).priority +
      (generated_pareto_tuple updates μ source ω i).hashValue
  have hfirst (t : ℕ) (G : ℝ → ℝ) (hG : is_admissible_weight G)
      (i : Fin updates.length) : Measurable (firstScore t G hG i) := by
    change Measurable (fun ω ↦ ell G hG
      (source.noise i ω / (updates.get i).increment,
        source.hash (updates.get i).index ω))
    exact (hell G hG).1.comp
      ((source.noise_measurable i).div_const (updates.get i).increment |>.prodMk
        (source.hash_measurable (updates.get i).index))
  have hsecond (i : Fin updates.length) : Measurable (secondScore i) := by
    change Measurable (fun ω ↦ source.noise i ω / (updates.get i).increment +
      source.hash (updates.get i).index ω)
    exact ((source.noise_measurable i).div_const (updates.get i).increment).add
      (source.hash_measurable (updates.get i).index)
  have hchoice (t : ℕ) (G : ℝ → ℝ) (hG : is_admissible_weight G) :
      ∃ out : Ω → Fin n, Measurable out ∧
        ((active t).Nonempty → ∀ ω, ∃ i ∈ active t,
          (updates.get i).index = out ω ∧
          ∀ j ∈ active t,
            (toLex (firstScore t G hG i ω, secondScore i ω) : ENNReal ×ₗ ℝ) ≤
              toLex (firstScore t G hG j ω, secondScore j ω)) := by
    by_cases hs : (active t).Nonempty
    · let i₀ : Fin updates.length := Classical.choose hs
      have hi₀ : i₀ ∈ active t := Classical.choose_spec hs
      obtain ⟨pick, hpick, hfirstPick, hsecondPick, hpick_mem, hpick_min⟩ :=
        measurable_lexicographic_list_minimum i₀ (active t).toList
          (firstScore t G hG) secondScore (hfirst t G hG) hsecond
      refine ⟨fun ω ↦ (updates.get (pick ω)).index,
        (measurable_of_finite
          (fun k : Fin updates.length ↦ (updates.get k).index)).comp hpick, ?_⟩
      intro _ ω
      have hpick_active : pick ω ∈ active t := by
        rcases List.mem_cons.mp (hpick_mem ω) with h | h
        · simpa [h] using hi₀
        · simpa using h
      refine ⟨pick ω, hpick_active, rfl, ?_⟩
      intro j hj
      exact hpick_min ω j (by simp [hj])
    · refine ⟨fun _ ↦ ⟨0, hn⟩, measurable_const, ?_⟩
      exact fun hs' ↦ (hs hs').elim
  let output : (t : ℕ) → (G : ℝ → ℝ) → is_admissible_weight G → Ω → Fin n :=
    fun t G hG ↦ Classical.choose (hchoice t G hG)
  have houtput (t : ℕ) (G : ℝ → ℝ) (hG : is_admissible_weight G) :
      Measurable (output t G hG) ∧
        ((active t).Nonempty → ∀ ω, ∃ i ∈ active t,
          (updates.get i).index = output t G hG ω ∧
          ∀ j ∈ active t,
            (toLex (firstScore t G hG i ω, secondScore i ω) : ENNReal ×ₗ ℝ) ≤
              toLex (firstScore t G hG j ω, secondScore j ω)) :=
    Classical.choose_spec (hchoice t G hG)
  let run : pareto_sampler_run Ω n :=
    { output := output
      output_measurable := fun t G hG ↦ (houtput t G hG).1 }
  refine ⟨run, ?_⟩
  intro t ht G hG hpositive
  have htpos : 0 < t := by
    by_contra htpos
    have htzero : t = 0 := Nat.eq_zero_of_not_pos htpos
    subst t
    have hGzero : G 0 = 0 := (hell G hG).2.2.2.1
    simp [weight_moment, stream_vector, hGzero] at hpositive
  have hactive : (active t).Nonempty := by
    let i : Fin updates.length := ⟨0, htpos.trans_le ht⟩
    refine ⟨i, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, htpos⟩
  refine ⟨ell G hG, hell G hG, ?_⟩
  intro ω
  rcases (houtput t G hG).2 hactive ω with ⟨i, hi, hiindex, hmin⟩
  let p := generated_pareto_tuple updates μ source ω i
  have hp_generated : p ∈ generated_tuples updates μ source ω t := by
    rw [generated_tuples]
    apply Finset.mem_image.mpr
    exact ⟨i, hi, rfl⟩
  have hlevel (j : Fin updates.length) (hj : j ∈ active t) :
      ell G hG (pareto_tuple_coordinates p) ≤
        ell G hG (pareto_tuple_coordinates
          (generated_pareto_tuple updates μ source ω j)) := by
    rcases Prod.Lex.toLex_le_toLex.mp (hmin j hj) with hlt | heq
    · exact hlt.le
    · exact heq.1.le
  have hp_state : p ∈ pareto_state updates μ source ω t := by
    change p ∈ pareto_frontier (generated_tuples updates μ source ω t)
    rw [pareto_frontier]
    refine Finset.mem_filter.mpr ⟨hp_generated, ?_⟩
    intro q hq hqp
    rw [generated_tuples] at hq
    rcases Finset.mem_image.mp hq with ⟨j, hj, rfl⟩
    have hjactive : j ∈ active t := hj
    have hmono := (hell G hG).2.1 hqp
    have hkey := Prod.Lex.toLex_le_toLex.mp (hmin j hjactive)
    have hsum : secondScore i ω ≤ secondScore j ω := by
      rcases hkey with hlt | heq
      · exact (not_lt_of_ge hmono hlt).elim
      · exact heq.2
    change pareto_tuple_coordinates p ≤
      pareto_tuple_coordinates (generated_pareto_tuple updates μ source ω j)
    change source.noise j ω / (updates.get j).increment ≤
        source.noise i ω / (updates.get i).increment ∧
      source.hash (updates.get j).index ω ≤ source.hash (updates.get i).index ω at hqp
    change source.noise i ω / (updates.get i).increment +
        source.hash (updates.get i).index ω ≤
      source.noise j ω / (updates.get j).increment +
        source.hash (updates.get j).index ω at hsum
    change source.noise i ω / (updates.get i).increment ≤
        source.noise j ω / (updates.get j).increment ∧
      source.hash (updates.get i).index ω ≤ source.hash (updates.get j).index ω
    constructor <;> linarith
  refine ⟨p, hp_state, ?_, ?_⟩
  · exact hiindex
  · intro q hq
    have hq_generated : q ∈ generated_tuples updates μ source ω t := by
      change q ∈ pareto_frontier (generated_tuples updates μ source ω t) at hq
      exact (Finset.mem_filter.mp hq).1
    rw [generated_tuples] at hq_generated
    rcases Finset.mem_image.mp hq_generated with ⟨j, hj, rfl⟩
    exact hlevel j hj

@[blueprint "thm:ParetoSampler"
  (statement := /-- For every $d,q\in\mathbb{N}$, there exists a constant $C>0$ such that
  the following holds uniformly over every probability space $(\Omega,\mu)$, every $n\geq2$,
  every insertion-only stream $U$ of at most $n^d$ positive updates on $[n]$, and every valid
  Pareto random source for $U$. There exists a run implementing the Pareto sampler for these
  data. For every $t\leq |U|$, every admissible query function $G$ satisfying $G(x_t)>0$,
  and every $v\in[n]$, this run returns $v_*\in[n]$ with
  \[
    \mathbb P(v_*=v)=\frac{G(x_t(v))}{\sum_{u\in[n]}G(x_t(u))}
  \]
  and, with probability at least $1-n^{-q}$, its maintained state uses at most
  $C(1+\log n)$ words simultaneously for every $t\leq |U|$. -/)
  (proof := /-- Fix $d,q\in\mathbb{N}$. By \cref{lem:pareto-sampler-space-bound}, choose
  $C>0$ uniformly over all probability spaces, universe sizes, streams, and random sources.
  Now fix such data with $n\geq2$ and at most $n^d$ updates. The inequality $0<n$ follows
  from $n\geq2$, so \cref{lem:pareto-sampler-constructed} supplies a run whose query operation
  minimizes the requested level function on the maintained frontier. Its exact sampling law
  at every prefix and for every admissible $G$ of positive moment is
  \cref{lem:pareto-sampler-sampling-correct}. The uniform space estimate already supplied by
  \cref{lem:pareto-sampler-space-bound} bounds the maintained state simultaneously at all
  times outside an event of probability at most $n^{-q}$. -/)
  (title := /-- Universal perfect sampling with logarithmic space -/)
  (latexEnv := "theorem")]
theorem ParetoSampler (d q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure μ] (n : ℕ), 2 ≤ n →
        ∀ (updates : List (incremental_update n))
          (source : pareto_random_source Ω n updates.length μ),
          updates.length ≤ n ^ d →
            ∃ run : pareto_sampler_run Ω n,
              implements_pareto_sampler updates μ source run ∧
              (∀ (t : ℕ), t ≤ updates.length → ∀ (G : ℝ → ℝ)
                (hG : is_admissible_weight G)
                (hpositive : 0 < weight_moment G (stream_vector updates t)) (v : Fin n),
                μ.real {ω | run.output t G hG ω = v} =
                  G (stream_vector updates t v) /
                    weight_moment G (stream_vector updates t)) ∧
              1 - (n : ℝ)⁻¹ ^ q ≤
                μ.real {ω | ∀ t : ℕ, t ≤ updates.length →
                  (pareto_space_words updates μ source ω t : ℝ) ≤
                    C * (1 + Real.log n)} := by
  obtain ⟨C, hC, hspace⟩ := pareto_sampler_space_bound d q
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ n hn updates source hlength
  obtain ⟨run, himpl⟩ := pareto_sampler_constructed μ (by omega) updates source
  exact ⟨run, himpl, pareto_sampler_sampling_correct μ updates source run himpl,
    hspace Ω μ n hn updates source hlength⟩

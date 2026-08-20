import Architect
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:ba-vector"
  (statement := /-- For a dimension $d\in\mathbb N$, the payoff space is the Euclidean space $\mathbb R^d$, represented as functions from $\operatorname{Fin}(d)$ to $\mathbb R$. -/)
  (title := /-- Euclidean payoff vectors -/)
  (latexEnv := "definition")]
abbrev ba_vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

@[blueprint "def:vector-average"
  (statement := /-- Let $T,d\in\mathbb N$ and let $z_t\in\mathbb R^d$ for $t\in\operatorname{Fin}(T)$. Their vector average is
  \[
    \operatorname{avg}_T(z)=\frac1T\sum_{t\in\operatorname{Fin}(T)}z_t,
  \]
  where division by zero is interpreted by the ambient field structure on $\mathbb R$. -/)
  (title := /-- Finite vector averages -/)
  (latexEnv := "definition")]
noncomputable def vector_average {d T : ℕ} (z : Fin T → ba_vector d) : ba_vector d :=
  (T : ℝ)⁻¹ • ∑ t, z t

@[blueprint "def:polar-target"
  (statement := /-- Let $S\subseteq\mathbb R^d$. Its nonpositive polar is
  \[
    S^\circ=\{u\in\mathbb R^d:\langle u,s\rangle\leq0\text{ for every }s\in S\}.
  \] -/)
  (title := /-- The nonpositive polar of a target set -/)
  (latexEnv := "definition")]
def polar_target {d : ℕ} (S : Set (ba_vector d)) : Set (ba_vector d) :=
  {u | ∀ ⦃s⦄, s ∈ S → inner ℝ u s ≤ 0}

@[blueprint "def:normal-at"
  (statement := /-- Let $C\subseteq\mathbb R^d$ and $\theta\in\mathbb R^d$. The normal cone used here is
  \[
    N_C(\theta)=\{n\in\mathbb R^d:\langle n,z-\theta\rangle\leq0\text{ for every }z\in C\}.
  \]
  Membership of $\theta$ in $C$ is imposed separately whenever it is required. -/)
  (title := /-- Normal vectors to a set -/)
  (latexEnv := "definition")]
def normal_at {d : ℕ} (C : Set (ba_vector d)) (θ n : ba_vector d) : Prop :=
  ∀ ⦃z⦄, z ∈ C → inner ℝ n (z - θ) ≤ 0

@[blueprint "def:source-offset"
  (statement := /-- For $p,x,\theta\in\mathbb R^d$, define the offset appearing in the source proof by
  \[
    n(p,x,\theta)=2\lVert p\rVert_2
      \frac{x-\theta}{\lVert x-\theta\rVert_2}.
  \]
  This declaration deliberately retains the source's unguarded quotient; Lean's total division assigns it a value also when $x=\theta$. -/)
  (title := /-- The source normal offset -/)
  (latexEnv := "definition")]
noncomputable def source_offset {d : ℕ}
    (p x θ : ba_vector d) : ba_vector d :=
  (2 * ‖p‖ / ‖x - θ‖) • (x - θ)

@[blueprint "def:blackwell-problem"
  (statement := /-- A bounded conic Blackwell approachability problem in $\mathbb R^d$ consists of action sets $A$ and $B$, a payoff map $f:A\times B\to\mathbb R^d$, a bound $L\geq0$, a nonempty closed convex cone $S$, and a halfspace oracle $\mathcal O_H$. Every payoff has norm at most $L$, and for every $u\in S^\circ$ and $b\in B$ the oracle action satisfies
  \[
    \langle u,f(\mathcal O_H(u),b)\rangle\leq0.
  \]
  The cone axioms are recorded explicitly as closure under addition and multiplication by nonnegative real scalars. -/)
  (title := /-- Bounded conic Blackwell problems -/)
  (latexEnv := "definition")]
structure blackwell_problem (d : ℕ) (A B : Type) where
  payoff : A → B → ba_vector d
  target : Set (ba_vector d)
  bound : ℝ
  bound_nonnegative : 0 ≤ bound
  payoff_bounded : ∀ a b, ‖payoff a b‖ ≤ bound
  target_nonempty : target.Nonempty
  target_closed : IsClosed target
  target_convex : Convex ℝ target
  target_zero : (0 : ba_vector d) ∈ target
  target_add : ∀ ⦃x y⦄, x ∈ target → y ∈ target → x + y ∈ target
  target_smul : ∀ (c : ℝ), 0 ≤ c → ∀ ⦃x⦄, x ∈ target → c • x ∈ target
  halfspace_oracle : ba_vector d → A
  halfspace_condition : ∀ ⦃u⦄, u ∈ polar_target target →
    ∀ b, inner ℝ u (payoff (halfspace_oracle u) b) ≤ 0

@[blueprint "def:geq-to-ba-execution"
  (statement := /-- Fix a bounded conic Blackwell problem, an error function $\operatorname{Err}:\mathbb R\times\mathbb R\times\mathbb N\to\mathbb R$, a horizon $T$, directions $x_t$, learner actions $a_t$, Nature actions $b_t$, and realized extended fields $\bar g_t$. A certified execution of the paper's BA-from-GEQ algorithm supplies projected directions $\theta_t\in S^\circ$ such that $x_t-\theta_t$ satisfies the projection variational inequality, $a_t=\mathcal O_H(\theta_t)$, and
  \[
    \bar g_t(x_t)=f(a_t,b_t)-n(f(a_t,b_t),x_t,\theta_t).
  \]
  It also records the GEQ oracle guarantee
  \[
    \left\lVert\operatorname{avg}_T(\bar g_t(x_t))\right\rVert_2
      \leq \frac{\operatorname{Err}(3L,0,T)}{T}.
  \] -/)
  (title := /-- Certified executions of the BA-from-GEQ algorithm -/)
  (latexEnv := "definition")]
structure geq_to_ba_execution {d : ℕ} {A B : Type}
    (P : blackwell_problem d A B)
    (error : ℝ → ℝ → ℕ → ℝ) (T : ℕ)
    (x : Fin T → ba_vector d) (a : Fin T → A) (b : Fin T → B)
    (barG : Fin T → ba_vector d → ba_vector d) where
  projected : Fin T → ba_vector d
  projected_mem : ∀ t, projected t ∈ polar_target P.target
  projection_inequality : ∀ t ⦃z⦄, z ∈ polar_target P.target →
    inner ℝ (x t - projected t) (z - projected t) ≤ 0
  action_eq : ∀ t, a t = P.halfspace_oracle (projected t)
  field_eq : ∀ t, barG t (x t) =
    P.payoff (a t) (b t) - source_offset (P.payoff (a t) (b t)) (x t) (projected t)
  geq_bound : ‖vector_average (fun t => barG t (x t))‖ ≤
    error (3 * P.bound) 0 T / (T : ℝ)

@[blueprint "lem:source-offset-normal"
  (statement := /-- Let $S\subseteq\mathbb R^d$, let $x\in\mathbb R^d$, and let $\theta\in S^\circ$ satisfy
  \[
    \langle x-\theta,z-\theta\rangle\leq0
    \qquad(z\in S^\circ).
  \]
  Then, for every $p\in\mathbb R^d$, the source offset $n(p,x,\theta)$ belongs to $N_{S^\circ}(\theta)$. -/)
  (proof := /-- By \cref{def:source-offset}, the offset is $c(x-\theta)$, where $c=2\lVert p\rVert_2/\lVert x-\theta\rVert_2$ is nonnegative. For every $z\in S^\circ$, real linearity of the inner product and the assumed projection inequality give
  \[
    \langle c(x-\theta),z-\theta\rangle
      =c\langle x-\theta,z-\theta\rangle\leq0.
  \]
  This is precisely the defining condition in \cref{def:normal-at}. If $x=\theta$, Lean's totalized division makes $c=0$, and the same argument applies. -/)
  (title := /-- Normality of the source offset -/)
  (latexEnv := "lemma")]
lemma source_offset_normal {d : ℕ} {S : Set (ba_vector d)}
    {x θ p : ba_vector d} (hθ : θ ∈ polar_target S)
    (hproj : ∀ ⦃z⦄, z ∈ polar_target S →
      inner ℝ (x - θ) (z - θ) ≤ 0) :
    normal_at (polar_target S) θ (source_offset p x θ) := by
  rintro z hz
  rw [source_offset, real_inner_smul_left]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hproj hz)

@[blueprint "lem:normal-to-polar-lies-in-target"
  (statement := /-- Let $P$ be a bounded conic Blackwell problem on $\mathbb R^d$ with learner and Nature action types $A$ and $B$, and write $S=P.\mathrm{target}$. For every $\theta,n\in\mathbb R^d$, if $\theta\in S^\circ$ and $n\in N_{S^\circ}(\theta)$, then $n\in S$. -/)
  (proof := /-- Let $p\in S$ minimize $\lVert n-p\rVert_2$, whose existence follows from closedness, nonemptiness, and convexity of the target in \cref{def:blackwell-problem}. The variational characterization of this metric projection gives
  \[
    \langle n-p,s-p\rangle\leq0\qquad(s\in S).
  \]
  Since $0,p+p\in S$ by the cone axioms in \cref{def:blackwell-problem}, the two corresponding inequalities imply $\langle n-p,p\rangle=0$. Consequently $\langle n-p,s\rangle\leq0$ for every $s\in S$, so $n-p\in S^\circ$ by \cref{def:polar-target}. Likewise, $0,\theta+\theta\in S^\circ$; applying the assumed normal inequalities from \cref{def:normal-at} at these two points yields $\langle n,\theta\rangle=0$. Applying normality once more at $n-p\in S^\circ$ gives $\langle n,n-p\rangle\leq0$. Symmetry of the real inner product and $\langle n-p,p\rangle=0$ now give
  \[
    0\leq\lVert n-p\rVert_2^2
      =\langle n-p,n-p\rangle
      =\langle n,n-p\rangle\leq0.
  \]
  Hence $n=p$, and therefore $n\in S$. -/)
  (title := /-- Normals to the polar lie in the target cone -/)
  (latexEnv := "lemma")]
lemma normal_to_polar_lies_in_target {d : ℕ} {A B : Type}
    (P : blackwell_problem d A B) {θ n : ba_vector d}
    (hθ : θ ∈ polar_target P.target)
    (hn : normal_at (polar_target P.target) θ n) : n ∈ P.target := by
  obtain ⟨p, hp, hpmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex P.target_nonempty
      P.target_closed.isComplete P.target_convex n
  have hproj : ∀ s ∈ P.target, inner ℝ (n - p) (s - p) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero P.target_convex hp).mp hpmin
  have hp_inner : inner ℝ (n - p) p = 0 := by
    have hzero := hproj 0 P.target_zero
    have hdouble := hproj (p + p) (P.target_add hp hp)
    have hnonneg : 0 ≤ inner ℝ (n - p) p := by
      simpa using hzero
    have hnonpos : inner ℝ (n - p) p ≤ 0 := by
      simpa using hdouble
    exact le_antisymm hnonpos hnonneg
  have hseparator : n - p ∈ polar_target P.target := by
    intro s hs
    have hsproj := hproj s hs
    simpa [inner_sub_right, hp_inner] using hsproj
  have htheta_inner : inner ℝ n θ = 0 := by
    have hzero_polar : (0 : ba_vector d) ∈ polar_target P.target := by
      intro s hs
      simp
    have hdouble_polar : θ + θ ∈ polar_target P.target := by
      intro s hs
      have hθs := hθ hs
      rw [inner_add_left]
      linarith
    have hzero := hn hzero_polar
    have hdouble := hn hdouble_polar
    have hnonneg : 0 ≤ inner ℝ n θ := by
      simpa using hzero
    have hnonpos : inner ℝ n θ ≤ 0 := by
      simpa using hdouble
    exact le_antisymm hnonpos hnonneg
  have hnseparator : inner ℝ n (n - p) ≤ 0 := by
    have hnormal := hn hseparator
    simpa [inner_sub_right, htheta_inner] using hnormal
  have hresidual_nonpos : inner ℝ (n - p) (n - p) ≤ 0 := by
    calc
      inner ℝ (n - p) (n - p) =
          inner ℝ n (n - p) - inner ℝ p (n - p) := by
            rw [inner_sub_left]
      _ = inner ℝ n (n - p) - inner ℝ (n - p) p := by
            rw [real_inner_comm p (n - p)]
      _ = inner ℝ n (n - p) := by rw [hp_inner, sub_zero]
      _ ≤ 0 := hnseparator
  have hresidual_zero : inner ℝ (n - p) (n - p) = 0 :=
    le_antisymm hresidual_nonpos real_inner_self_nonneg
  have hnp : n = p := sub_eq_zero.mp (inner_self_eq_zero.mp hresidual_zero)
  rw [hnp]
  exact hp

@[blueprint "lem:execution-offsets-lie-in-target"
  (statement := /-- In every certified execution of the BA-from-GEQ algorithm, each source offset
  \[
    n_t=n(f(a_t,b_t),x_t,\theta_t)
  \]
  belongs to the target cone $S$. -/)
  (proof := /-- Fix $t$. The projected direction $\theta_t$ lies in $S^\circ$ by the execution certificate. Its projection variational inequality and \cref{lem:source-offset-normal} imply that $n_t\in N_{S^\circ}(\theta_t)$. Applying \cref{lem:normal-to-polar-lies-in-target} yields $n_t\in S$. Since $t$ was arbitrary, the assertion holds for every round. -/)
  (title := /-- Target membership of all execution offsets -/)
  (latexEnv := "lemma")]
lemma execution_offsets_lie_in_target {d T : ℕ} {A B : Type}
    {P : blackwell_problem d A B} {error : ℝ → ℝ → ℕ → ℝ}
    {x : Fin T → ba_vector d} {a : Fin T → A} {b : Fin T → B}
    {barG : Fin T → ba_vector d → ba_vector d}
    (run : geq_to_ba_execution P error T x a b barG) :
    ∀ t, source_offset (P.payoff (a t) (b t)) (x t) (run.projected t) ∈ P.target := by
  intro t
  exact normal_to_polar_lies_in_target P (run.projected_mem t)
    (source_offset_normal (run.projected_mem t) (run.projection_inequality t))

@[blueprint "lem:target-closed-under-vector-average"
  (statement := /-- Let $S$ be the target cone of a bounded conic Blackwell problem and let $T\geq1$. If $z_t\in S$ for every $t\in\operatorname{Fin}(T)$, then $\operatorname{avg}_T(z)\in S$. -/)
  (proof := /-- By \cref{def:blackwell-problem}, the target contains $0$ and is closed under addition, so induction over the finite index set gives $\sum_t z_t\in S$. The inequality $T\geq1$ implies that the real scalar $T^{-1}$ is positive. Applying the target's closure under multiplication by nonnegative real scalars and then \cref{def:vector-average} yields $\operatorname{avg}_T(z)=T^{-1}\sum_t z_t\in S$. -/)
  (title := /-- Averages remain in the target cone -/)
  (latexEnv := "lemma")]
lemma target_closed_under_vector_average {d T : ℕ} {A B : Type}
    (P : blackwell_problem d A B) (hT : 1 ≤ T)
    (z : Fin T → ba_vector d) (hz : ∀ t, z t ∈ P.target) :
    vector_average z ∈ P.target := by
  unfold vector_average
  refine P.target_smul _ (le_of_lt (inv_pos.mpr (by exact_mod_cast (Nat.zero_lt_of_lt hT)))) ?_
  exact Finset.sum_induction z (fun x => x ∈ P.target)
    (fun a b ha hb => P.target_add ha hb) P.target_zero (fun x _ => hz x)

@[blueprint "lem:distance-to-target-le-residual-average"
  (statement := /-- Let $d,T\in\mathbb N$, let $A$ and $B$ be types, and let $P$ be a bounded conic Blackwell problem on $\mathbb R^d$ with action spaces $A$ and $B$ and target cone $S$. Suppose that $T\geq1$, and let $p,n:\operatorname{Fin}(T)\to\mathbb R^d$ satisfy $n_t\in S$ for every $t\in\operatorname{Fin}(T)$. Then
  \[
    d\bigl(\operatorname{avg}_T(p),S\bigr)
      \leq\left\lVert\operatorname{avg}_T(p_t-n_t)\right\rVert_2.
  \] -/)
  (proof := /-- By \cref{lem:target-closed-under-vector-average}, the vector $\bar n=\operatorname{avg}_T(n)$ belongs to $S$. The point-to-set distance is at most the distance to this particular point, so
  \[
    d\bigl(\operatorname{avg}_T(p),S\bigr)
      \leq \lVert\operatorname{avg}_T(p)-\bar n\rVert_2.
  \]
  Unfolding the averages by \cref{def:vector-average}, distributivity of finite sums over subtraction and of scalar multiplication over subtraction gives
  $\operatorname{avg}_T(p)-\bar n=\operatorname{avg}_T(p-n)$, which proves the asserted inequality. -/)
  (title := /-- Distance controlled by an averaged residual -/)
  (latexEnv := "lemma")]
lemma distance_to_target_le_residual_average {d T : ℕ} {A B : Type}
    (P : blackwell_problem d A B) (hT : 1 ≤ T)
    (p n : Fin T → ba_vector d) (hn : ∀ t, n t ∈ P.target) :
    Metric.infDist (vector_average p) P.target ≤
      ‖vector_average (fun t => p t - n t)‖ := by
  simpa [dist_eq_norm, vector_average, Finset.sum_sub_distrib, smul_sub] using
    (Metric.infDist_le_dist_of_mem (x := vector_average p)
      (target_closed_under_vector_average P hT n hn))

@[blueprint "lem:execution-extended-average-identity"
  (statement := /-- Let $d,T\in\mathbb N$, let $A$ and $B$ be types, and fix a bounded conic Blackwell problem $P$, an error function, sequences $(x_t)_{t\in\operatorname{Fin}(T)}$, $(a_t)_{t\in\operatorname{Fin}(T)}$, and $(b_t)_{t\in\operatorname{Fin}(T)}$, and a family of realized extended fields $(\bar g_t)_{t\in\operatorname{Fin}(T)}$. For every certified execution with projected directions $\theta_t$, one has
  \[
    \operatorname{avg}_T(\bar g_t(x_t))
      =\operatorname{avg}_T\bigl(f(a_t,b_t)-n(f(a_t,b_t),x_t,\theta_t)\bigr).
  \] -/)
  (proof := /-- By the field identity in the certified-execution definition, \cref{def:geq-to-ba-execution}, one has $\bar g_t(x_t)=f(a_t,b_t)-n(f(a_t,b_t),x_t,\theta_t)$ for every $t\in\operatorname{Fin}(T)$. Function extensionality therefore identifies the two functions being averaged, and congruence under $\operatorname{avg}_T$ gives the stated equality. -/)
  (title := /-- Average identity for the extended fields -/)
  (latexEnv := "lemma")]
lemma execution_extended_average_identity {d T : ℕ} {A B : Type}
    {P : blackwell_problem d A B} {error : ℝ → ℝ → ℕ → ℝ}
    {x : Fin T → ba_vector d} {a : Fin T → A} {b : Fin T → B}
    {barG : Fin T → ba_vector d → ba_vector d}
    (run : geq_to_ba_execution P error T x a b barG) :
    vector_average (fun t => barG t (x t)) =
      vector_average (fun t => P.payoff (a t) (b t) -
        source_offset (P.payoff (a t) (b t)) (x t) (run.projected t)) := by
  exact congrArg vector_average (funext run.field_eq)

@[blueprint "lem:execution-distance-bound"
  (statement := /-- Let $d,T\in\mathbb N$, let $A$ and $B$ be types, let $P$ be a
  bounded conic Blackwell problem on $\mathbb R^d$ with payoff
  $f:A\to B\to\mathbb R^d$ and target cone $S$, and let
  $\operatorname{Err}:\mathbb R\to\mathbb R\to\mathbb N\to\mathbb R$.
  Fix sequences $x_t\in\mathbb R^d$, $a_t\in A$, and $b_t\in B$, indexed by
  $t\in\operatorname{Fin}(T)$, and realized extended fields
  $\bar g_t:\mathbb R^d\to\mathbb R^d$. If $T\geq1$ and these data admit a
  certified BA-from-GEQ execution, then
  \[
    d\left(\operatorname{avg}_T(f(a_t,b_t)),S\right)
      \leq\left\lVert\operatorname{avg}_T(\bar g_t(x_t))\right\rVert_2.
  \] -/)
  (proof := /-- By \cref{lem:execution-offsets-lie-in-target}, every source offset $n_t$ lies in $S$. Applying \cref{lem:distance-to-target-le-residual-average} with $p_t=f(a_t,b_t)$ bounds the distance by the norm of the average residual $f(a_t,b_t)-n_t$. The identity in \cref{lem:execution-extended-average-identity} identifies this residual average with the average of $\bar g_t(x_t)$, proving the inequality. -/)
  (title := /-- The approachability distance bound for an execution -/)
  (latexEnv := "lemma")]
lemma execution_distance_bound {d T : ℕ} {A B : Type}
    {P : blackwell_problem d A B} {error : ℝ → ℝ → ℕ → ℝ}
    {x : Fin T → ba_vector d} {a : Fin T → A} {b : Fin T → B}
    {barG : Fin T → ba_vector d → ba_vector d}
    (hT : 1 ≤ T) (run : geq_to_ba_execution P error T x a b barG) :
    Metric.infDist (vector_average (fun t => P.payoff (a t) (b t))) P.target ≤
      ‖vector_average (fun t => barG t (x t))‖ := by
  rw [execution_extended_average_identity run]
  exact distance_to_target_le_residual_average P hT
    (fun t => P.payoff (a t) (b t))
    (fun t => source_offset (P.payoff (a t) (b t)) (x t) (run.projected t))
    (execution_offsets_lie_in_target run)

@[blueprint "thm:geq-to-ba"
  (statement := /-- Let $d,T\in\mathbb N$, let $A$ and $B$ be types, let $P$ be a bounded conic Blackwell problem on $\mathbb R^d$ with payoff $f:A\to B\to\mathbb R^d$, target cone $S$, and payoff bound $L$, and let $\operatorname{Err}:\mathbb R\to\mathbb R\to\mathbb N\to\mathbb R$. Assume $T\geq1$. Fix sequences $x_t\in\mathbb R^d$, $a_t\in A$, and $b_t\in B$ indexed by $t\in\operatorname{Fin}(T)$, and realized extended fields $\bar g_t:\mathbb R^d\to\mathbb R^d$. Then every certified BA-from-GEQ execution for these data satisfies
  \[
    d\left(\frac1T\sum_{t=1}^T f(a_t,b_t),S\right)
      \leq\left\lVert\frac1T\sum_{t=1}^T\bar g_t(x_t)\right\rVert_2
      \leq\frac{\operatorname{Err}(3L,0,T)}{T}.
  \] -/)
  (proof := /-- The first inequality is \cref{lem:execution-distance-bound}. The second inequality is the GEQ oracle estimate recorded in the certified execution \cref{def:geq-to-ba-execution}, applied with field bound $3L$, restorative radius $0$, and horizon $T$. Combining the two inequalities proves the asserted chain. -/)
  (title := /-- Blackwell approachability from gradient equilibrium -/)
  (latexEnv := "theorem")]
theorem geq_to_ba {d T : ℕ} {A B : Type}
    (P : blackwell_problem d A B) (error : ℝ → ℝ → ℕ → ℝ)
    (hT : 1 ≤ T) (x : Fin T → ba_vector d) (a : Fin T → A)
    (b : Fin T → B) (barG : Fin T → ba_vector d → ba_vector d)
    (run : geq_to_ba_execution P error T x a b barG) :
    Metric.infDist (vector_average (fun t => P.payoff (a t) (b t))) P.target ≤
        ‖vector_average (fun t => barG t (x t))‖ ∧
      ‖vector_average (fun t => barG t (x t))‖ ≤
        error (3 * P.bound) 0 T / (T : ℝ) := by
  exact ⟨execution_distance_bound hT run, run.geq_bound⟩

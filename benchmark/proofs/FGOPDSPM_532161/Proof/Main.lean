import Architect
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:dynamic-update-mode"
  (statement := /-- A \emph{dynamic update mode} is either incremental, in which every update inserts an edge, or decremental, in which every update deletes an edge. -/)
  (title := /-- Dynamic update modes -/)
  (latexEnv := "definition")]
inductive dynamic_update_mode where
  | incremental
  | decremental

@[blueprint "def:fine-grained-complexity-model"
  (statement := /-- A \emph{fine-grained complexity model} consists of a type of algorithms, a total running-time function depending on the number of vertices, a predicate identifying algorithms that correctly compute Minimum-Weight $4$-Clique on graphs with nonnegative edge weights, and, for each mode in \cref{def:dynamic-update-mode}, a predicate identifying algorithms that correctly maintain the single-source single-target distance on undirected graphs with nonnegative edge weights under every valid update sequence of that mode. The source and target vertices are fixed for each dynamic instance, and the running time is the total time over the complete update sequence. The model also carries the reduction principle used for the conditional lower bound: for either dynamic mode, if a correct shortest-path algorithm has total running time $O(n^{4-\varepsilon})$ for some real $\varepsilon>0$, then there are a correct Minimum-Weight $4$-Clique algorithm and a real $\delta>0$ for which the clique algorithm has running time $O(n^{4-\delta})$. -/)
  (title := /-- Fine-grained computational model -/)
  (latexEnv := "definition")]
structure fine_grained_complexity_model where
  Algorithm : Type
  totalTime : Algorithm → ℕ → ℕ
  computesMinimumWeightFourClique : Algorithm → Prop
  computesDynamicSTSP : dynamic_update_mode → Algorithm → Prop
  dynamicSTSPSubquarticReduction :
    ∀ (mode : dynamic_update_mode) (A : Algorithm) (ε : ℝ),
      computesDynamicSTSP mode A → 0 < ε →
      Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ => (totalTime A n : ℝ))
        (fun n : ℕ => Real.rpow (n : ℝ) (4 - ε)) →
      ∃ B : Algorithm, ∃ δ : ℝ,
        computesMinimumWeightFourClique B ∧ 0 < δ ∧
          Asymptotics.IsBigO Filter.atTop
            (fun n : ℕ => (totalTime B n : ℝ))
            (fun n : ℕ => Real.rpow (n : ℝ) (4 - δ))

@[blueprint "def:runs-in-exponent-time"
  (statement := /-- Let $M$ be a fine-grained complexity model, let $A$ be an algorithm in $M$, and let $c\in\mathbb R$. We say that $A$ \emph{runs in exponent $c$ total time} if its total running-time function is $O(n^c)$ as $n\to\infty$. Here $n^c$ is the real power of the real number corresponding to $n$. -/)
  (title := /-- Running time with a fixed exponent -/)
  (latexEnv := "definition")]
def runs_in_exponent_time (M : fine_grained_complexity_model)
    (A : M.Algorithm) (c : ℝ) : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (fun n : ℕ => (M.totalTime A n : ℝ))
    (fun n : ℕ => Real.rpow (n : ℝ) c)

@[blueprint "def:requires-near-quartic-total-time"
  (statement := /-- Let $M$ be a fine-grained complexity model and let $P$ be a predicate on its algorithms. We say that algorithms satisfying $P$ \emph{require $n^{4-o(1)}$ total time} if, for every such algorithm $A$ and every real $\varepsilon>0$, the total running time of $A$ is not $O(n^{4-\varepsilon})$ in the sense of \cref{def:runs-in-exponent-time}. -/)
  (title := /-- Near-quartic total-time lower bound -/)
  (latexEnv := "definition")]
def requires_near_quartic_total_time (M : fine_grained_complexity_model)
    (P : M.Algorithm → Prop) : Prop :=
  ∀ A, P A → ∀ ε : ℝ, 0 < ε → ¬ runs_in_exponent_time M A (4 - ε)

@[blueprint "def:minimum-weight-four-clique-hypothesis"
  (statement := /-- The \emph{Minimum-Weight $4$-Clique hypothesis} in a fine-grained complexity model $M$ is the assertion that, for every algorithm correctly computing a minimum-weight $4$-clique in an $n$-vertex graph with nonnegative edge weights and every real $\varepsilon>0$, its running time is not $O(n^{4-\varepsilon})$. Equivalently, the corresponding correctness predicate requires $n^{4-o(1)}$ total time in the sense of \cref{def:requires-near-quartic-total-time}. -/)
  (title := /-- The Minimum-Weight $4$-Clique hypothesis -/)
  (latexEnv := "definition")]
def minimum_weight_four_clique_hypothesis
    (M : fine_grained_complexity_model) : Prop :=
  requires_near_quartic_total_time M M.computesMinimumWeightFourClique

@[blueprint "def:dynamic-stsp-near-quartic-lower-bound"
  (statement := /-- Let $M$ be a fine-grained complexity model and let $\mu$ be a dynamic update mode. The \emph{near-quartic dynamic $s$--$t$ shortest-path lower bound in mode $\mu$} asserts that every algorithm correctly maintaining the distance from a fixed source $s$ to a fixed target $t$ on undirected $n$-vertex graphs, under all valid update sequences of mode $\mu$, requires $n^{4-o(1)}$ total time in the sense of \cref{def:requires-near-quartic-total-time}. -/)
  (title := /-- Dynamic $s$--$t$ shortest-path lower bound -/)
  (latexEnv := "definition")]
def dynamic_stsp_near_quartic_lower_bound
    (M : fine_grained_complexity_model) (mode : dynamic_update_mode) : Prop :=
  requires_near_quartic_total_time M (M.computesDynamicSTSP mode)

@[blueprint "lem:incremental-stsp-subquartic-reduction"
  (statement := /-- Let $M$ be a fine-grained complexity model. Suppose that $A$ correctly maintains single-source single-target shortest-path distances on undirected graphs under incremental updates. If $A$ has total running time $O(n^{4-\varepsilon})$ for some real $\varepsilon>0$, then there exist an algorithm $B$ correctly computing Minimum-Weight $4$-Clique and a real $\delta>0$ such that $B$ has running time $O(n^{4-\delta})$. -/)
  (proof := /-- Apply the reduction principle in \cref{def:fine-grained-complexity-model} to the incremental mode, the algorithm $A$, and the exponent saving $\varepsilon$. Its hypotheses are respectively the assumed correctness of $A$, the strict positivity of $\varepsilon$, and the asserted $O(n^{4-\varepsilon})$ running-time bound. The principle therefore supplies an algorithm $B$ and a real number $\delta>0$ such that $B$ correctly computes Minimum-Weight $4$-Clique and runs in time $O(n^{4-\delta})$, which is the required conclusion. -/)
  (title := /-- Incremental shortest paths yield a subquartic clique algorithm -/)
  (latexEnv := "lemma")]
lemma incremental_stsp_subquartic_reduction
    (M : fine_grained_complexity_model) (A : M.Algorithm)
    (hA : M.computesDynamicSTSP dynamic_update_mode.incremental A)
    (ε : ℝ) (hε : 0 < ε)
    (hTime : runs_in_exponent_time M A (4 - ε)) :
    ∃ B : M.Algorithm, ∃ δ : ℝ,
      M.computesMinimumWeightFourClique B ∧ 0 < δ ∧
        runs_in_exponent_time M B (4 - δ) := by
  exact M.dynamicSTSPSubquarticReduction
    dynamic_update_mode.incremental A ε hA hε hTime

@[blueprint "lem:decremental-stsp-subquartic-reduction"
  (statement := /-- Let $M$ be a fine-grained complexity model, let $A$ be an algorithm in $M$, and let $\varepsilon>0$ be real. Suppose that $A$ correctly maintains the distance between a fixed source and a fixed target on undirected graphs with nonnegative edge weights under every valid decremental update sequence, and that its total running time is $O(n^{4-\varepsilon})$. Then there exist an algorithm $B$ in $M$ and a real number $\delta>0$ such that $B$ correctly computes Minimum-Weight $4$-Clique on graphs with nonnegative edge weights and has total running time $O(n^{4-\delta})$. -/)
  (proof := /-- Apply the reduction principle in \cref{def:fine-grained-complexity-model} to the decremental mode, the algorithm $A$, and the exponent saving $\varepsilon$. Its hypotheses are respectively the assumed correctness of $A$, the strict positivity of $\varepsilon$, and the asserted $O(n^{4-\varepsilon})$ running-time bound. The principle therefore supplies an algorithm $B$ and a real number $\delta>0$ such that $B$ correctly computes Minimum-Weight $4$-Clique and runs in time $O(n^{4-\delta})$, which is the required conclusion. -/)
  (title := /-- Decremental shortest paths yield a subquartic clique algorithm -/)
  (latexEnv := "lemma")]
lemma decremental_stsp_subquartic_reduction
    (M : fine_grained_complexity_model) (A : M.Algorithm)
    (hA : M.computesDynamicSTSP dynamic_update_mode.decremental A)
    (ε : ℝ) (hε : 0 < ε)
    (hTime : runs_in_exponent_time M A (4 - ε)) :
    ∃ B : M.Algorithm, ∃ δ : ℝ,
      M.computesMinimumWeightFourClique B ∧ 0 < δ ∧
        runs_in_exponent_time M B (4 - δ) := by
  exact M.dynamicSTSPSubquarticReduction dynamic_update_mode.decremental A ε hA hε hTime

@[blueprint "thm:st-sp-lb"
  (statement := /-- Let $M$ be a fine-grained complexity model in which the Minimum-Weight $4$-Clique hypothesis holds. Then, for each of the incremental and decremental update modes, every algorithm maintaining the single-source single-target shortest-path distance on $n$-vertex undirected graphs requires $n^{4-o(1)}$ total time. -/)
  (proof := /-- Unfold the Minimum-Weight $4$-Clique hypothesis from \cref{def:minimum-weight-four-clique-hypothesis} and the required dynamic lower bound from \cref{def:dynamic-stsp-near-quartic-lower-bound}. Fix an update mode $\mu$, an algorithm $A$ correct for that mode, and a real number $\varepsilon>0$, and suppose for contradiction that $A$ runs in time $O(n^{4-\varepsilon})$. If $\mu$ is incremental, \cref{lem:incremental-stsp-subquartic-reduction} supplies a correct Minimum-Weight $4$-Clique algorithm $B$ and a real $\delta>0$ for which $B$ runs in time $O(n^{4-\delta})$, contradicting the hypothesis. If $\mu$ is decremental, the same contradiction follows from \cref{lem:decremental-stsp-subquartic-reduction}. Hence no such $A$ and $\varepsilon$ exist in either mode, which is precisely the asserted $n^{4-o(1)}$ total-time lower bound. -/)
  (title := /-- Fine-grained lower bound for partially dynamic $s$--$t$ shortest paths -/)
  (latexEnv := "theorem")]
theorem st_sp_lb (M : fine_grained_complexity_model)
    (hClique : minimum_weight_four_clique_hypothesis M) :
    ∀ mode : dynamic_update_mode,
      dynamic_stsp_near_quartic_lower_bound M mode := by
  unfold minimum_weight_four_clique_hypothesis at hClique
  unfold requires_near_quartic_total_time at hClique
  intro mode
  unfold dynamic_stsp_near_quartic_lower_bound
  unfold requires_near_quartic_total_time
  intro A hA ε hε hTime
  cases mode with
  | incremental =>
    obtain ⟨B, δ, hB, hδ, hBTime⟩ :=
      incremental_stsp_subquartic_reduction M A hA ε hε hTime
    exact hClique B hB δ hδ hBTime
  | decremental =>
    obtain ⟨B, δ, hB, hδ, hBTime⟩ :=
      decremental_stsp_subquartic_reduction M A hA ε hε hTime
    exact hClique B hB δ hδ hBTime

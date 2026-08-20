import Architect
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Matrix.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

@[blueprint "def:real-matrix"
  (statement := /-- For natural numbers $r$ and $c$, a real $r\times c$ matrix is a function from $\operatorname{Fin}(r)\times\operatorname{Fin}(c)$ to $\mathbb R$. -/)
  (title := /-- Finite real matrices -/)
  (latexEnv := "definition")]
abbrev real_matrix (rows cols : ℕ) := Matrix (Fin rows) (Fin cols) ℝ

@[blueprint "def:row-embedding"
  (statement := /-- A row embedding from dimension $d_{\mathrm{in}}$ to dimension $d_{\mathrm{out}}$ is a function $\mathbb R^{d_{\mathrm{in}}}\to\mathbb R^{d_{\mathrm{out}}}$. -/)
  (title := /-- Row embeddings -/)
  (latexEnv := "definition")]
abbrev row_embedding (dIn dOut : ℕ) := (Fin dIn → ℝ) → (Fin dOut → ℝ)

@[blueprint "def:self-attention-head"
  (statement := /-- A self-attention head of input dimension $d$ and embedding dimension $m$ consists of row-wise query, key, and value embeddings $\mathbb R^d\to\mathbb R^m$ as in \cref{def:row-embedding}. -/)
  (title := /-- Self-attention heads -/)
  (latexEnv := "definition")]
structure self_attention_head (dIn m : ℕ) where
  query : row_embedding dIn m
  key : row_embedding dIn m
  value : row_embedding dIn m

@[blueprint "def:attention-score"
  (statement := /-- Given a head $h$, an input $X\in\mathbb R^{N\times d}$, and rows $i,j$, the attention score is the Euclidean pairing $\sum_{k=1}^{m}Q(X_i)_kK(X_j)_k$. -/)
  (title := /-- Attention scores -/)
  (latexEnv := "definition")]
noncomputable def attention_score {N dIn m : ℕ} (head : self_attention_head dIn m)
    (X : real_matrix N dIn) (i j : Fin N) : ℝ :=
  ∑ k : Fin m, head.query (X i) k * head.key (X j) k

@[blueprint "def:attention-weight"
  (statement := /-- The softmax attention weight from row $i$ to row $j$ is
  \[
    \frac{\exp(\operatorname{score}(i,j))}
    {\sum_{j'=1}^{N}\exp(\operatorname{score}(i,j'))}.
  \]
  The score is the one in \cref{def:attention-score}. -/)
  (title := /-- Row-wise softmax weights -/)
  (latexEnv := "definition")]
noncomputable def attention_weight {N dIn m : ℕ} (head : self_attention_head dIn m)
    (X : real_matrix N dIn) (i j : Fin N) : ℝ :=
  Real.exp (attention_score head X i j) /
    ∑ j' : Fin N, Real.exp (attention_score head X i j')

@[blueprint "def:attention-head-output"
  (statement := /-- The output of a self-attention head on $X$ is the matrix whose $(i,k)$ entry is
  \[
    \sum_{j=1}^{N} \operatorname{weight}(i,j)V(X_j)_k,
  \]
  with weights as in \cref{def:attention-weight}. -/)
  (title := /-- Output of a self-attention head -/)
  (latexEnv := "definition")]
noncomputable def attention_head_output {N dIn m : ℕ}
    (head : self_attention_head dIn m) (X : real_matrix N dIn) : real_matrix N m :=
  fun i k => ∑ j : Fin N, attention_weight head X i j * head.value (X j) k

@[blueprint "def:no-mlp-transformer"
  (statement := /-- A transformer without MLPs, with context length $N$, embedding dimension $m$, $L$ layers, and $H$ heads per layer, is an $L\times H$ array of self-attention heads of input and output dimension $m$. Residual addition and head summation are specified in \cref{def:no-mlp-layer-output}. -/)
  (title := /-- Transformers without MLPs -/)
  (latexEnv := "definition")]
structure no_mlp_transformer (N m L H : ℕ) where
  heads : Fin L → Fin H → self_attention_head m m

@[blueprint "def:no-mlp-layer-output"
  (statement := /-- If $X$ is the current embedding matrix, layer $\ell$ of a no-MLP transformer returns
  \[
    X+\sum_{h=1}^{H}f_{\ell,h}(X),
  \]
  where each $f_{\ell,h}$ is evaluated according to \cref{def:attention-head-output}. -/)
  (title := /-- A residual no-MLP transformer layer -/)
  (latexEnv := "definition")]
noncomputable def no_mlp_layer_output {N m L H : ℕ} (T : no_mlp_transformer N m L H)
    (ell : Fin L) (X : real_matrix N m) : real_matrix N m :=
  X + ∑ h : Fin H, attention_head_output (T.heads ell h) X

@[blueprint "def:no-mlp-transformer-output"
  (statement := /-- The output of a no-MLP transformer is obtained by starting from the input and applying the $L$ residual layer maps of \cref{def:no-mlp-layer-output} in increasing layer order. -/)
  (title := /-- Evaluation of a no-MLP transformer -/)
  (latexEnv := "definition")]
noncomputable def no_mlp_transformer_output {N m L H : ℕ}
    (T : no_mlp_transformer N m L H) (X : real_matrix N m) : real_matrix N m :=
  (List.ofFn (fun ell : Fin L => fun state : real_matrix N m =>
    no_mlp_layer_output T ell state)).foldl (fun state layer => layer state) X

@[blueprint "def:transformer-evaluator"
  (statement := /-- A transformer evaluator supplies, for every choice of $N,m,L,H$, an output matrix for every no-MLP transformer and input of those dimensions, together with a nonnegative worst-case running-time bound. -/)
  (title := /-- Algorithms evaluating transformers -/)
  (latexEnv := "definition")]
structure transformer_evaluator where
  output : ∀ (N m L H : ℕ), no_mlp_transformer N m L H →
    real_matrix N m → real_matrix N m
  runningTime : ℕ → ℕ → ℕ → ℕ → ℝ
  runningTime_nonnegative : ∀ N m L H, 0 ≤ runningTime N m L H

@[blueprint "def:computes-no-mlp-transformers"
  (statement := /-- Let $m,L,H:\mathbb N\to\mathbb N$. An evaluator $A$ computes the corresponding no-MLP transformers to entry-wise additive error $1/(10N)$ if, for every $N>0$, every such transformer $T$, every input $X$, and every output entry $(i,j)$,
  \[
    \left|A(T,X)_{ij}-T(X)_{ij}\right|\leq \frac1{10N}.
  \]
  The exact transformer output is the one in \cref{def:no-mlp-transformer-output}. -/)
  (title := /-- Uniform entry-wise approximate evaluation -/)
  (latexEnv := "definition")]
def computes_no_mlp_transformers (A : transformer_evaluator)
    (m L H : ℕ → ℕ) : Prop :=
  ∀ (N : ℕ), 0 < N →
    ∀ (T : no_mlp_transformer N (m N) (L N) (H N))
      (X : real_matrix N (m N)) (i : Fin N) (j : Fin (m N)),
      |A.output N (m N) (L N) (H N) T X i j - no_mlp_transformer_output T X i j| ≤
        (1 : ℝ) / (10 * (N : ℝ))

@[blueprint "def:logarithmic-dimension"
  (statement := /-- A dimension family $d:\mathbb N\to\mathbb N$ is logarithmic if its real-valued coercion is $\Theta(\log N)$ along $N\to\infty$. -/)
  (title := /-- Logarithmic dimension families -/)
  (latexEnv := "definition")]
def logarithmic_dimension (d : ℕ → ℕ) : Prop :=
  (fun N : ℕ => (d N : ℝ)) =Θ[Filter.atTop]
    (fun N : ℕ => Real.log (N : ℝ))

@[blueprint "def:polynomially-bounded"
  (statement := /-- A family $f:\mathbb N\to\mathbb N$ is polynomially bounded if there exists $c\in\mathbb N$ for which $f(N)=O(N^c)$ as $N\to\infty$. -/)
  (title := /-- Polynomially bounded parameter families -/)
  (latexEnv := "definition")]
def polynomially_bounded (f : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, (fun N : ℕ => (f N : ℝ)) =O[Filter.atTop]
    (fun N : ℕ => (N : ℝ) ^ c)

@[blueprint "def:small-embedding-regime"
  (statement := /-- The small-embedding regime consists of parameter families $m,L,H$ for which $m=\Theta(\log N)$ and both $L$ and $H$ are polynomially bounded in $N$, in the senses of \cref{def:logarithmic-dimension, def:polynomially-bounded}. -/)
  (title := /-- The small-embedding parameter regime -/)
  (latexEnv := "definition")]
def small_embedding_regime (m L H : ℕ → ℕ) : Prop :=
  logarithmic_dimension m ∧ polynomially_bounded L ∧ polynomially_bounded H

@[blueprint "def:subquadratic-transformer-time"
  (statement := /-- An evaluator has an $LHN^{2-\varepsilon}$ running-time upper bound in a parameter regime if there is a fixed real $\varepsilon>0$ such that its worst-case running time is
  \[
    O\!\left(L(N)H(N)N^{2-\varepsilon}\right)
  \]
  as $N\to\infty$. The negation of this predicate is the standard fixed-power-saving formulation of an $LHN^{2-o(1)}$ conditional lower bound. -/)
  (title := /-- A fixed subquadratic power saving -/)
  (latexEnv := "definition")]
noncomputable def subquadratic_transformer_time (A : transformer_evaluator)
    (m L H : ℕ → ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    (fun N : ℕ => A.runningTime N (m N) (L N) (H N)) =O[Filter.atTop]
      (fun N : ℕ => (L N : ℝ) * (H N : ℝ) * Real.rpow (N : ℝ) (2 - ε))

@[blueprint "def:bit-vector"
  (statement := /-- A bit vector of dimension $d$ is a function $\operatorname{Fin}(d)\to\{0,1\}$, represented by Boolean values. -/)
  (title := /-- Boolean vectors -/)
  (latexEnv := "definition")]
abbrev bit_vector (d : ℕ) := Fin d → Bool

@[blueprint "def:three-ov-instance"
  (statement := /-- A three-orthogonal-vectors instance of dimension $d$ and set sizes $n_1,n_2,n_3$ is an ordered triple of indexed families of $d$-dimensional bit vectors. -/)
  (title := /-- Unbalanced 3-OV instances -/)
  (latexEnv := "definition")]
structure three_ov_instance (d n₁ n₂ n₃ : ℕ) where
  first : Fin n₁ → bit_vector d
  second : Fin n₂ → bit_vector d
  third : Fin n₃ → bit_vector d

@[blueprint "def:orthogonal-triple"
  (statement := /-- Three bit vectors $a,b,c\in\{0,1\}^d$ are orthogonal if no coordinate is equal to $1$ in all three vectors. -/)
  (title := /-- Orthogonal triples -/)
  (latexEnv := "definition")]
def orthogonal_triple {d : ℕ} (a b c : bit_vector d) : Prop :=
  ∀ q : Fin d, ¬(a q = true ∧ b q = true ∧ c q = true)

@[blueprint "def:has-orthogonal-triple"
  (statement := /-- An instance has an orthogonal triple if one may select one vector from each of its three families so that the selected vectors satisfy \cref{def:orthogonal-triple}. -/)
  (title := /-- The 3-OV decision predicate -/)
  (latexEnv := "definition")]
def has_orthogonal_triple {d n₁ n₂ n₃ : ℕ}
    (I : three_ov_instance d n₁ n₂ n₃) : Prop :=
  ∃ i : Fin n₁, ∃ j : Fin n₂, ∃ k : Fin n₃,
    orthogonal_triple (I.first i) (I.second j) (I.third k)

@[blueprint "def:three-ov-instance-encoding"
  (statement := /-- The canonical binary encoding of a 3-OV instance first records the dimension and the three family sizes in unary, with a zero delimiter after each integer, and then lists the coordinates of the vectors in the first, second, and third families in lexicographic order. -/)
  (title := /-- Canonical binary encoding of 3-OV -/)
  (latexEnv := "definition")]
def three_ov_instance_encoding {d n₁ n₂ n₃ : ℕ}
    (I : three_ov_instance d n₁ n₂ n₃) : List Bool :=
  List.replicate d true ++ [false] ++
    List.replicate n₁ true ++ [false] ++
    List.replicate n₂ true ++ [false] ++
    List.replicate n₃ true ++ [false] ++
    (List.ofFn (fun i : Fin n₁ => List.ofFn (I.first i))).flatten ++
    (List.ofFn (fun i : Fin n₂ => List.ofFn (I.second i))).flatten ++
    (List.ofFn (fun i : Fin n₃ => List.ofFn (I.third i))).flatten

@[blueprint "def:certified-execution"
  (statement := /-- A certified binary execution model consists of one fixed finite multi-stack Turing machine, together with identifications of the alphabets on its designated input and output stacks with the Boolean alphabet. The designated stacks are required to be distinct, so placing the input word in the initial configuration cannot simultaneously place an alleged output on the output stack. -/)
  (title := /-- Certified binary machine executions -/)
  (latexEnv := "definition")]
structure certified_execution where
  machine : Turing.FinTM2
  inputAlphabet : machine.Γ machine.k₀ ≃ Bool
  outputAlphabet : machine.Γ machine.k₁ ≃ Bool
  inputStack_ne_outputStack : machine.k₀ ≠ machine.k₁

@[blueprint "def:certified-execution-initial"
  (statement := /-- Given a certified execution model and a binary word, its initial configuration places the word on the designated input stack, leaves every other stack empty, and starts the fixed machine at its main label and prescribed initial state. -/)
  (title := /-- Initial configuration of a certified execution -/)
  (latexEnv := "definition")]
def certified_execution_initial (P : certified_execution) (input : List Bool) :
    P.machine.Cfg where
  l := some P.machine.main
  var := P.machine.initialState
  stk := Function.update (fun _ => []) P.machine.k₀
    (input.map P.inputAlphabet.symm)

@[blueprint "def:certified-execution-next"
  (statement := /-- One totalized transition of a certified execution performs the machine's next transition when one exists and otherwise leaves a halted configuration unchanged. -/)
  (title := /-- Totalized machine transition -/)
  (latexEnv := "definition")]
def certified_execution_next (P : certified_execution) (c : P.machine.Cfg) :
    P.machine.Cfg :=
  (P.machine.step c).getD c

@[blueprint "def:certified-execution-run"
  (statement := /-- The configuration reached by a certified execution after exactly $t$ charged machine transitions is obtained by iterating its totalized transition $t$ times from \cref{def:certified-execution-initial}. -/)
  (title := /-- Bounded execution of a certified machine -/)
  (latexEnv := "definition")]
def certified_execution_run (P : certified_execution) (input : List Bool) :
    ℕ → P.machine.Cfg
  | 0 => certified_execution_initial P input
  | t + 1 => certified_execution_next P (certified_execution_run P input t)

@[blueprint "def:certified-execution-halts"
  (statement := /-- A certified execution halts within $t$ transitions on a binary input if the control label of the configuration produced by \cref{def:certified-execution-run} after $t$ transitions is empty. -/)
  (title := /-- Certified halting within a time bound -/)
  (latexEnv := "definition")]
def certified_execution_halts (P : certified_execution) (input : List Bool)
    (t : ℕ) : Prop :=
  (certified_execution_run P input t).l = none

@[blueprint "def:certified-execution-answer"
  (statement := /-- The Boolean answer returned by a certified execution within $t$ transitions is the first symbol on its designated output stack after those $t$ transitions, or false if that stack is empty. -/)
  (title := /-- Answer of a bounded certified execution -/)
  (latexEnv := "definition")]
def certified_execution_answer (P : certified_execution) (input : List Bool)
    (t : ℕ) : Bool :=
  match (certified_execution_run P input t).stk P.machine.k₁ with
  | [] => false
  | a :: _ => P.outputAlphabet a

@[blueprint "def:three-ov-algorithm"
  (statement := /-- A uniform 3-OV algorithm consists of one certified binary machine execution and a worst-case transition bound for every dimension and triple of family sizes. For every instance with those parameters, the machine must halt within the asserted bound on the canonical encoding from \cref{def:three-ov-instance-encoding}. Its answer and running time are therefore properties of the same execution. -/)
  (title := /-- Certified algorithms for 3-OV -/)
  (latexEnv := "definition")]
structure three_ov_algorithm where
  execution : certified_execution
  runningTime : ℕ → ℕ → ℕ → ℕ → ℕ
  halts_within : ∀ {d n₁ n₂ n₃ : ℕ} (I : three_ov_instance d n₁ n₂ n₃),
    certified_execution_halts execution (three_ov_instance_encoding I)
      (runningTime d n₁ n₂ n₃)

@[blueprint "def:three-ov-algorithm-answer"
  (statement := /-- The answer of a certified 3-OV algorithm on an instance is the output bit produced by its machine on the canonical instance encoding after its certified worst-case number of transitions. -/)
  (title := /-- Output of a certified 3-OV algorithm -/)
  (latexEnv := "definition")]
def three_ov_algorithm_answer (A : three_ov_algorithm)
    {d n₁ n₂ n₃ : ℕ} (I : three_ov_instance d n₁ n₂ n₃) : Bool :=
  certified_execution_answer A.execution (three_ov_instance_encoding I)
    (A.runningTime d n₁ n₂ n₃)

@[blueprint "def:solves-three-ov"
  (statement := /-- A certified 3-OV algorithm is correct if, on every instance, the output of its bounded machine execution is true exactly when the decision predicate of \cref{def:has-orthogonal-triple} holds. -/)
  (title := /-- Correct solution of 3-OV -/)
  (latexEnv := "definition")]
def solves_three_ov (A : three_ov_algorithm) : Prop :=
  ∀ {d n₁ n₂ n₃ : ℕ} (I : three_ov_instance d n₁ n₂ n₃),
    three_ov_algorithm_answer A I = true ↔ has_orthogonal_triple I

@[blueprint "def:soft-big-o"
  (statement := /-- For real-valued functions $f,g$ on $\mathbb N$, write $f=\widetilde O(g)$ if there exists $c\in\mathbb N$ such that
  \[
    f(N)=O\!\left(g(N)(\log N)^c\right)
  \]
  as $N\to\infty$. -/)
  (title := /-- Soft-O running-time notation -/)
  (latexEnv := "definition")]
def soft_big_o (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℕ, f =O[Filter.atTop]
    (fun N : ℕ => g N * (Real.log (N : ℝ)) ^ c)

@[blueprint "def:three-ov-hypothesis"
  (statement := /-- The unbalanced 3-OV hypothesis asserts the following. For every logarithmic dimension family $d$ and every polynomially bounded third-set size $K$, no correct certified 3-OV algorithm admits, for any fixed $\varepsilon>0$, a worst-case machine-transition bound
  \[
    O\!\left(K(N)N^{2-\varepsilon}\right)
  \]
  on instances of sizes $N,N,K(N)$. -/)
  (title := /-- The unbalanced 3-OV hypothesis -/)
  (latexEnv := "definition")]
noncomputable def three_ov_hypothesis : Prop :=
  ∀ (d K : ℕ → ℕ), logarithmic_dimension d → polynomially_bounded K →
    ∀ A : three_ov_algorithm, solves_three_ov A →
      ¬∃ ε : ℝ, 0 < ε ∧
        (fun N : ℕ => (A.runningTime (d N) N N (K N) : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => (K N : ℝ) * Real.rpow (N : ℝ) (2 - ε))

@[blueprint "def:computes-reduction-transformers"
  (statement := /-- Let $m,d,L,H:\mathbb N\to\mathbb N$. An evaluator satisfies the padded reduction premise if
  \[
    2d(N)+2\leq m(N+1)
  \]
  for all sufficiently large $N$, and, for every $N>0$, it evaluates every no-MLP transformer with context length $N+1$, embedding dimension $m(N+1)$, $L(N+1)$ layers, and $H(N+1)$ heads to entry-wise error at most $1/(10N)$. The inequality permits the reduction transformer of dimension $2d(N)+2$ to be embedded in the first coordinates of the evaluator's actual embedding space; the remaining coordinates are reserved for zero padding. -/)
  (title := /-- The padded transformer-evaluation premise of the reduction -/)
  (latexEnv := "definition")]
def computes_reduction_transformers (A : transformer_evaluator)
    (m d L H : ℕ → ℕ) : Prop :=
  (∀ᶠ N : ℕ in Filter.atTop, 2 * d N + 2 ≤ m (N + 1)) ∧
    ∀ (N : ℕ), 0 < N →
      ∀ (T : no_mlp_transformer (N + 1) (m (N + 1)) (L (N + 1)) (H (N + 1)))
        (X : real_matrix (N + 1) (m (N + 1)))
        (i : Fin (N + 1)) (j : Fin (m (N + 1))),
      |A.output (N + 1) (m (N + 1)) (L (N + 1)) (H (N + 1)) T X i j -
          no_mlp_transformer_output T X i j| ≤ (1 : ℝ) / (10 * (N : ℝ))

@[blueprint "def:certified-transformer-evaluator"
  (statement := /-- A certified transformer evaluator consists of an extensional evaluator $A$, one fixed certified binary execution, semantic representations of transformer inputs and outputs, and a natural-valued transition bound. For every choice of $N,m,L,H$, transformer $T$, and input $X$, the machine halts on the chosen representation of $(T,X)$ at that bound, its represented output equals $A(T,X)$, and the real-valued running time declared by $A$ equals the same transition count.

  The certificate also implements the padded reduction. Let $d$ be logarithmic, let $m,d,L,H:\mathbb N\to\mathbb N$ satisfy \cref{def:computes-reduction-transformers}, and write $m_N=m(N+1)$, $L_N=L(N+1)$, and $H_N=H(N+1)$. For all sufficiently large $N$, the reduction transformer of embedding dimension $2d(N)+2$ is embedded in dimension $m_N$ by extending its query, key, and value coordinates and its input with zeros. The original output coordinates are unchanged, so evaluating the padded transformer with the promised accuracy permits the same threshold decision. The certificate handles the finitely many exceptional values of $N$ directly and supplies a correct machine for 3-OV on the canonical encoding of \cref{def:three-ov-instance-encoding}. This composed machine charges the construction and zero padding of the reduction transformer, the invocation of the evaluator at its actual dimensions, the decoding of the relevant output coordinate, and the final threshold comparison. Its running time is certified to be

  \[
    \widetilde O\!\left(L_NH_Nd(N)
      +\operatorname{time}_A(N+1,m_N,L_N,H_N)\right).
  \]
  Thus the padding is coherent both with the evaluator's output and with the exact call charged by its running-time bound. -/)
  (title := /-- Certified executable transformer evaluators with padded, costed reduction composition -/)
  (latexEnv := "definition")]
structure certified_transformer_evaluator where
  evaluator : transformer_evaluator
  execution : certified_execution
  inputEncoding : ∀ {N m L H : ℕ}, no_mlp_transformer N m L H →
    real_matrix N m → List Bool
  outputDecoding : ∀ {N m : ℕ}, List Bool → real_matrix N m
  transitionBound : ℕ → ℕ → ℕ → ℕ → ℕ
  runningTime_eq : ∀ N m L H,
    evaluator.runningTime N m L H = (transitionBound N m L H : ℝ)
  halts_within : ∀ {N m L H : ℕ} (T : no_mlp_transformer N m L H)
      (X : real_matrix N m),
    certified_execution_halts execution (inputEncoding T X)
      (transitionBound N m L H)
  output_eq : ∀ {N m L H : ℕ} (T : no_mlp_transformer N m L H)
      (X : real_matrix N m),
    evaluator.output N m L H T X =
      outputDecoding
        (((certified_execution_run execution (inputEncoding T X)
          (transitionBound N m L H)).stk execution.machine.k₁).map
            execution.outputAlphabet)
  reductionCertificate : ∀ (d L H : ℕ → ℕ), logarithmic_dimension d →
    ∀ {m : ℕ → ℕ}, computes_reduction_transformers evaluator m d L H →
    ∃ B : three_ov_algorithm, solves_three_ov B ∧
      soft_big_o
        (fun N : ℕ =>
          (B.runningTime (d N) N N (L (N + 1) * H (N + 1)) : ℝ))
        (fun N : ℕ =>
          (L (N + 1) : ℝ) * (H (N + 1) : ℝ) * (d N : ℝ) +
            (transitionBound (N + 1) (m (N + 1)) (L (N + 1)) (H (N + 1)) : ℝ))

@[blueprint "lem:transformer-compute-three-ov"
  (statement := /-- Let $m,d,L,H:\mathbb N\to\mathbb N$, assume that $d=\Theta(\log N)$ in the sense of \cref{def:logarithmic-dimension}, and let $A$ be an evaluator equipped with the padded, executable, costed-composition certificate of \cref{def:certified-transformer-evaluator}. If its underlying evaluator satisfies the padded premise of \cref{def:computes-reduction-transformers}, then the certificate supplies a correct 3-OV algorithm $B$ such that, on canonical instances of dimension $d(N)$ and sizes $N,N,L(N+1)H(N+1)$, its machine-transition bound is
  \[
    \widetilde O\!\left(L(N+1)H(N+1)d(N)
      +\operatorname{time}_A(N+1,m(N+1),L(N+1),H(N+1))\right).
  \] -/)
  (proof := /-- Apply the padded reduction-certificate field of $A$ from \cref{def:certified-transformer-evaluator} to the families $d,L,H$, the hypothesis that $d$ is logarithmic, and the padded reduction-evaluation hypothesis from \cref{def:computes-reduction-transformers}. The certificate uses the embedding family $m$ implicit in that hypothesis and gives exactly the asserted correct 3-OV algorithm and the displayed soft-O transition bound at the evaluator's actual shifted call. -/)
  (title := /-- Padded reduction from transformer evaluation to unbalanced 3-OV -/)
  (latexEnv := "lemma")]
lemma transformer_compute_three_ov (m d L H : ℕ → ℕ)
    (hd : logarithmic_dimension d) (A : certified_transformer_evaluator)
    (hA : computes_reduction_transformers A.evaluator m d L H) :
    ∃ B : three_ov_algorithm, solves_three_ov B ∧
      soft_big_o
        (fun N : ℕ =>
          (B.runningTime (d N) N N (L (N + 1) * H (N + 1)) : ℝ))
        (fun N : ℕ =>
          (L (N + 1) : ℝ) * (H (N + 1) : ℝ) * (d N : ℝ) +
            (A.transitionBound (N + 1) (m (N + 1))
              (L (N + 1)) (H (N + 1)) : ℝ)) := by
  exact A.reductionCertificate d L H hd hA

@[blueprint "lem:fast-small-embedding-refutes-three-ov"
  (statement := /-- Let $m,L,H:\mathbb N\to\mathbb N$ satisfy the small-embedding regime of \cref{def:small-embedding-regime}, and let $A$ be a certified transformer evaluator in the sense of \cref{def:certified-transformer-evaluator}. Suppose that the underlying evaluator of $A$ computes, for every $N>0$, every no-MLP transformer with parameters $N,m(N),L(N),H(N)$ to entry-wise additive error at most $1/(10N)$, and that there exists a fixed $\varepsilon>0$ for which its worst-case running time is
  \[
    O\!\left(L(N)H(N)N^{2-\varepsilon}\right).
  \]
  Then the unbalanced 3-OV hypothesis of \cref{def:three-ov-hypothesis} is false. -/)
  (proof := /-- Assume the stated evaluator exists. Define
  \[
    d(N)=\frac{m(N+1)-2}{2},
  \]
  where subtraction and Euclidean division are in $\mathbb N$. Since $m(N)=\Theta(\log N)$, shifting the argument by one, subtracting a constant, and dividing by two show that $d(N)=\Theta(\log N)$. Moreover, $m(N+1)\geq 2$ for all sufficiently large $N$, and Euclidean division then gives
  \[
    2d(N)+2\leq m(N+1).
  \]
  Thus the reduction embedding fits eventually in the evaluator's actual embedding.

  We next verify \cref{def:computes-reduction-transformers}. For $N>0$, apply the assumed correctness at context length $N+1$ to every transformer of dimensions
  \[
    (N+1,m(N+1),L(N+1),H(N+1)).
  \]
  Its error is at most $1/(10(N+1))$, which is at most $1/(10N)$. Together with the eventual fit just proved, this is precisely the padded reduction premise. Hence \cref{lem:transformer-compute-three-ov} supplies a correct 3-OV algorithm on instances of sizes
  \[
    N,\quad N,\quad K(N):=L(N+1)H(N+1)
  \]
  with running time
  \[
    \widetilde O\!\left(K(N)d(N)+
      \operatorname{time}_A(N+1,m(N+1),L(N+1),H(N+1))\right).
  \]
  The running-time identity in \cref{def:certified-transformer-evaluator} identifies the charged transition bound with this exact evaluator call. Shifting the assumed $O(L(N)H(N)N^{2-\varepsilon})$ bound by one therefore bounds the second term by $O(K(N)N^{2-\varepsilon})$. The family $K$ is polynomially bounded because $L$ and $H$ are polynomially bounded, while $d(N)=\Theta(\log N)$. Let $c$ be the fixed exponent in the soft-O bound and choose $0<\varepsilon'<\min\{\varepsilon,1\}$. The standard domination of every fixed power of $\log N$ by every positive power of $N$ gives
  \[
    N^{2-\varepsilon}(\log N)^c=O(N^{2-\varepsilon'})
    \quad\text{and}\quad
    d(N)(\log N)^c=O(N^{2-\varepsilon'}).
  \]
  Consequently the 3-OV algorithm runs in
  \[
    O\!\left(K(N)N^{2-\varepsilon'}\right),
  \]
  contradicting \cref{def:three-ov-hypothesis}. Hence the 3-OV hypothesis is false. -/)
  (title := /-- A fast small-embedding evaluator contradicts 3-OV -/)
  (latexEnv := "lemma")]
lemma fast_small_embedding_refutes_three_ov (m L H : ℕ → ℕ)
    (A : certified_transformer_evaluator) (hregime : small_embedding_regime m L H)
    (hcorrect : computes_no_mlp_transformers A.evaluator m L H)
    (hfast : subquadratic_transformer_time A.evaluator m L H) : ¬three_ov_hypothesis := by
  intro h3ov
  unfold three_ov_hypothesis at h3ov
  rcases hregime with ⟨hm, hL, hH⟩
  rcases hfast with ⟨ε, hε, hfast⟩
  let d : ℕ → ℕ := fun N => (m (N + 1) - 2) / 2
  have hlogshift : (fun N : ℕ => Real.log ((N : ℝ) + 1)) =Θ[Filter.atTop]
      (fun N : ℕ => Real.log (N : ℝ)) := by
    constructor
    · apply Asymptotics.IsBigO.of_bound 2
      filter_upwards [Filter.eventually_ge_atTop 2] with N hN
      have hN1 : 1 ≤ N := by omega
      have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
      have htwoNpos : (0 : ℝ) < 2 * (N : ℝ) := mul_pos (by norm_num) hNpos
      rw [Real.norm_of_nonneg (Real.log_nonneg (by norm_num)),
        Real.norm_of_nonneg (Real.log_nonneg (by exact_mod_cast hN1))]
      have hle : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
        push_cast
        exact_mod_cast (show N + 1 ≤ 2 * N by omega)
      calc
        Real.log ((N : ℝ) + 1) ≤ Real.log (2 * (N : ℝ)) :=
          Real.strictMonoOn_log.monotoneOn
            (show (0 : ℝ) < (N : ℝ) + 1 by linarith) htwoNpos hle
        _ = Real.log 2 + Real.log (N : ℝ) :=
          Real.log_mul (by norm_num) hNpos.ne'
        _ ≤ 2 * Real.log (N : ℝ) := by
          have hlogle : Real.log 2 ≤ Real.log (N : ℝ) :=
            Real.strictMonoOn_log.monotoneOn
              (show (0 : ℝ) < 2 by norm_num) hNpos (by exact_mod_cast hN)
          linarith
    · apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
      rw [Real.norm_of_nonneg (Real.log_nonneg (by exact_mod_cast hN)),
        Real.norm_of_nonneg (Real.log_nonneg (by norm_num)), one_mul]
      exact Real.strictMonoOn_log.monotoneOn hNpos
        (show (0 : ℝ) < (N : ℝ) + 1 by linarith) (by norm_num)
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmnorm := hm.tendsto_norm_atTop_iff.mpr
    (tendsto_norm_atTop_atTop.comp hlog)
  have hm6 : ∀ᶠ N : ℕ in Filter.atTop, 6 ≤ m (N + 1) := by
    simpa using (hmnorm.comp (Filter.tendsto_add_atTop_nat 1)).eventually
      (Filter.eventually_ge_atTop (6 : ℝ))
  have hdm : (fun N : ℕ => (d N : ℝ)) =Θ[Filter.atTop]
      (fun N : ℕ => (m (N + 1) : ℝ)) := by
    constructor
    · apply Asymptotics.IsBigO.of_bound 1
      filter_upwards with N
      rw [Real.norm_natCast, Real.norm_natCast, one_mul]
      exact_mod_cast (show d N ≤ m (N + 1) by
        dsimp [d]
        omega)
    · apply Asymptotics.IsBigO.of_bound 4
      filter_upwards [hm6] with N hN
      rw [Real.norm_natCast, Real.norm_natCast]
      exact_mod_cast (show m (N + 1) ≤ 4 * d N by
        dsimp [d]
        omega)
  have hmshift : (fun N : ℕ => (m (N + 1) : ℝ)) =Θ[Filter.atTop]
      (fun N : ℕ => Real.log ((N : ℝ) + 1)) := by
    constructor
    · simpa [Function.comp_def] using
        hm.1.comp_tendsto (Filter.tendsto_add_atTop_nat 1)
    · simpa [Function.comp_def] using
        hm.2.comp_tendsto (Filter.tendsto_add_atTop_nat 1)
  have hd : logarithmic_dimension d := hdm.trans (hmshift.trans hlogshift)
  have hfit : ∀ᶠ N : ℕ in Filter.atTop, 2 * d N + 2 ≤ m (N + 1) := by
    filter_upwards [hm6] with N hN
    dsimp [d]
    omega
  have hred : computes_reduction_transformers A.evaluator m d L H := by
    refine ⟨hfit, ?_⟩
    intro N hN T X i j
    calc
      |A.evaluator.output (N + 1) (m (N + 1)) (L (N + 1)) (H (N + 1)) T X i j -
          no_mlp_transformer_output T X i j| ≤
          (1 : ℝ) / (10 * ((N + 1 : ℕ) : ℝ)) :=
        hcorrect (N + 1) (by omega) T X i j
      _ ≤ (1 : ℝ) / (10 * (N : ℝ)) := by
        have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        gcongr
        norm_num
  let K : ℕ → ℕ := fun N => L (N + 1) * H (N + 1)
  rcases hL with ⟨cL, hL⟩
  rcases hH with ⟨cH, hH⟩
  have hpowshift : ∀ c : ℕ,
      (fun N : ℕ => ((N : ℝ) + 1) ^ c) =O[Filter.atTop]
        (fun N : ℕ => (N : ℝ) ^ c) := by
    intro c
    apply Asymptotics.IsBigO.of_bound ((2 : ℝ) ^ c)
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have hle : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
      push_cast
      exact_mod_cast (show N + 1 ≤ 2 * N by omega)
    calc
      ((N : ℝ) + 1) ^ c ≤ (2 * (N : ℝ)) ^ c := by gcongr
      _ = (2 : ℝ) ^ c * (N : ℝ) ^ c := by rw [mul_pow]
  have hLshift : (fun N : ℕ => (L (N + 1) : ℝ)) =O[Filter.atTop]
      (fun N : ℕ => (N : ℝ) ^ cL) := by
    have hs := hL.comp_tendsto (Filter.tendsto_add_atTop_nat 1)
    have hs' : (fun N : ℕ => (L (N + 1) : ℝ)) =O[Filter.atTop]
        (fun N : ℕ => ((N : ℝ) + 1) ^ cL) := by
      simpa [Function.comp_def] using hs
    exact hs'.trans (hpowshift cL)
  have hHshift : (fun N : ℕ => (H (N + 1) : ℝ)) =O[Filter.atTop]
      (fun N : ℕ => (N : ℝ) ^ cH) := by
    have hs := hH.comp_tendsto (Filter.tendsto_add_atTop_nat 1)
    have hs' : (fun N : ℕ => (H (N + 1) : ℝ)) =O[Filter.atTop]
        (fun N : ℕ => ((N : ℝ) + 1) ^ cH) := by
      simpa [Function.comp_def] using hs
    exact hs'.trans (hpowshift cH)
  have hK : polynomially_bounded K := by
    refine ⟨cL + cH, ?_⟩
    simpa [K, Nat.cast_mul, pow_add] using hLshift.mul hHshift
  rcases transformer_compute_three_ov m d L H hd A hred with ⟨B, hB, hsoft⟩
  rcases hsoft with ⟨c, hsoft⟩
  have hsoft' :
      (fun N : ℕ => (B.runningTime (d N) N N (K N) : ℝ)) =O[Filter.atTop]
      (fun N : ℕ => ((K N : ℝ) * (d N : ℝ) +
        (A.transitionBound (N + 1) (m (N + 1))
          (L (N + 1)) (H (N + 1)) : ℝ)) * Real.log (N : ℝ) ^ c) := by
    simpa [K, Nat.cast_mul] using hsoft
  let ε₀ : ℝ := min ε 1
  have hε₀ : 0 < ε₀ := lt_min hε one_pos
  have hε₀le : ε₀ ≤ ε := min_le_left _ _
  have hp : 0 ≤ 2 - ε₀ := by
    dsimp [ε₀]
    linarith [min_le_right ε 1]
  have hrelax :
      (fun N : ℕ => (L N : ℝ) * (H N : ℝ) * Real.rpow (N : ℝ) (2 - ε))
        =O[Filter.atTop]
      (fun N : ℕ => (L N : ℝ) * (H N : ℝ) * Real.rpow (N : ℝ) (2 - ε₀)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hnonneg (x : ℝ) :
        0 ≤ (L N : ℝ) * (H N : ℝ) * Real.rpow (N : ℝ) x :=
      mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (Real.rpow_nonneg (by positivity) _)
    rw [Real.norm_of_nonneg (hnonneg (2 - ε)),
      Real.norm_of_nonneg (hnonneg (2 - ε₀)), one_mul]
    gcongr
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)
  have hfast₀ := hfast.trans hrelax
  have hrshift :
      (fun N : ℕ => (L (N + 1) : ℝ) * (H (N + 1) : ℝ) *
        Real.rpow ((N : ℝ) + 1) (2 - ε₀)) =O[Filter.atTop]
      (fun N : ℕ => (K N : ℝ) * Real.rpow (N : ℝ) (2 - ε₀)) := by
    apply Asymptotics.IsBigO.of_bound (Real.rpow 2 (2 - ε₀))
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have hN1 : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
      push_cast
      exact_mod_cast (show N + 1 ≤ 2 * N by omega)
    have hr := Real.rpow_le_rpow
      (show (0 : ℝ) ≤ (N : ℝ) + 1 by positivity) hN1 hp
    rw [Real.mul_rpow (by norm_num) hN0] at hr
    have hLH : 0 ≤ (L (N + 1) : ℝ) * (H (N + 1) : ℝ) := by positivity
    have hleft : 0 ≤ (L (N + 1) : ℝ) * (H (N + 1) : ℝ) *
        Real.rpow ((N : ℝ) + 1) (2 - ε₀) :=
      mul_nonneg hLH (Real.rpow_nonneg (by positivity) _)
    have hright : 0 ≤ (L (N + 1) : ℝ) * (H (N + 1) : ℝ) *
        Real.rpow (N : ℝ) (2 - ε₀) :=
      mul_nonneg hLH (Real.rpow_nonneg hN0 _)
    simp only [K, Nat.cast_mul]
    rw [Real.norm_of_nonneg hleft, Real.norm_of_nonneg hright]
    calc
      (L (N + 1) : ℝ) * (H (N + 1) : ℝ) *
          Real.rpow ((N : ℝ) + 1) (2 - ε₀) ≤
          ((L (N + 1) : ℝ) * (H (N + 1) : ℝ)) *
            (Real.rpow 2 (2 - ε₀) * Real.rpow (N : ℝ) (2 - ε₀)) :=
        mul_le_mul_of_nonneg_left hr hLH
      _ = Real.rpow 2 (2 - ε₀) *
          ((L (N + 1) : ℝ) * (H (N + 1) : ℝ) *
            Real.rpow (N : ℝ) (2 - ε₀)) := by ring
  have hfastshift := hfast₀.comp_tendsto (Filter.tendsto_add_atTop_nat 1)
  have htransition₀ :
      (fun N : ℕ => (A.transitionBound (N + 1) (m (N + 1))
        (L (N + 1)) (H (N + 1)) : ℝ)) =O[Filter.atTop]
      (fun N : ℕ => (L (N + 1) : ℝ) * (H (N + 1) : ℝ) *
        Real.rpow ((N : ℝ) + 1) (2 - ε₀)) := by
    simpa [Function.comp_def, A.runningTime_eq] using hfastshift
  have htransition := htransition₀.trans hrshift
  have htend : ∀ {y : ℝ}, 0 < y →
      Filter.Tendsto (fun x : ℝ => Real.rpow x y) Filter.atTop Filter.atTop := by
    intro y hy
    rw [(Filter.atTop_basis' 0).tendsto_right_iff]
    intro b hb
    filter_upwards [Filter.eventually_ge_atTop 0,
      Filter.eventually_ge_atTop (Real.rpow b (1 / y))] with x hx₀ hx
    simpa (disch := positivity) [Real.rpow_inv_le_iff_of_pos] using hx
  have hlogrpow : ∀ {r : ℝ}, 0 < r →
      Real.log =o[Filter.atTop] (fun x : ℝ => Real.rpow x r) := by
    intro r hr
    calc
      Real.log =O[Filter.atTop] (fun x : ℝ => r * Real.log x) :=
        Asymptotics.isBigO_self_const_mul hr.ne' _ _
      _ =ᶠ[Filter.atTop] (fun x : ℝ => Real.log (Real.rpow x r)) := by
        filter_upwards [Filter.eventually_gt_atTop 0] with x hx
        exact (Real.log_rpow hx r).symm
      _ =o[Filter.atTop] (fun x : ℝ => Real.rpow x r) :=
        Real.isLittleO_log_id_atTop.comp_tendsto (htend hr)
  have hlogpow : ∀ (k : ℕ) {δ : ℝ}, 0 < δ →
      (fun N : ℕ => Real.log (N : ℝ) ^ k) =O[Filter.atTop]
        (fun N : ℕ => Real.rpow (N : ℝ) δ) := by
    intro k δ hδ
    let n : ℕ := k + 1
    have hn : 0 < n := by dsimp [n]; omega
    let r : ℝ := δ / n
    have hr : 0 < r := div_pos hδ (by positivity)
    have ho := (hlogrpow hr).pow hn
    have heq : (fun x : ℝ => (Real.rpow x r) ^ n) =ᶠ[Filter.atTop]
        (fun x : ℝ => Real.rpow x δ) := by
      filter_upwards [Filter.eventually_ge_atTop 0] with x hx
      calc
        (Real.rpow x r) ^ n = Real.rpow x (r * n) :=
          (Real.rpow_mul_natCast hx r n).symm
        _ = Real.rpow x δ := by
          congr 1
          dsimp [r]
          exact div_mul_cancel₀ δ (by positivity)
    have hon : (fun x : ℝ => Real.log x ^ n) =o[Filter.atTop]
        (fun x : ℝ => Real.rpow x δ) :=
      ho.congr' Filter.EventuallyEq.rfl heq
    have hk : (fun x : ℝ => Real.log x ^ k) =O[Filter.atTop]
        (fun x : ℝ => Real.log x ^ n) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [Real.tendsto_log_atTop.eventually
        (Filter.eventually_ge_atTop 1)] with x hx
      have hlog0 : 0 ≤ Real.log x := by linarith
      rw [Real.norm_of_nonneg (pow_nonneg hlog0 _),
        Real.norm_of_nonneg (pow_nonneg hlog0 _), one_mul]
      dsimp [n]
      rw [pow_succ]
      nlinarith [pow_nonneg hlog0 k]
    have hreal := (hk.trans_isLittleO hon).isBigO.comp_tendsto
      (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun N : ℕ => (N : ℝ))
        Filter.atTop Filter.atTop)
    simpa [Function.comp_def] using hreal
  let δ : ℝ := ε₀ / 2
  let q : ℝ := 2 - δ
  have hδ : 0 < δ := div_pos hε₀ (by norm_num)
  have hq : 0 < q := by
    dsimp [q, δ, ε₀]
    linarith [min_le_right ε 1]
  have hqeq : q = (2 - ε₀) + δ := by
    dsimp [q, δ]
    ring
  have hdc : (fun N : ℕ => (d N : ℝ) * Real.log (N : ℝ) ^ c)
      =O[Filter.atTop] (fun N : ℕ => Real.log (N : ℝ) ^ (c + 1)) := by
    simpa [pow_succ, mul_comm] using
      hd.1.mul (Asymptotics.isBigO_refl
        (fun N : ℕ => Real.log (N : ℝ) ^ c) Filter.atTop)
  have hterm1 : (fun N : ℕ => (K N : ℝ) * (d N : ℝ) *
      Real.log (N : ℝ) ^ c) =O[Filter.atTop]
      (fun N : ℕ => (K N : ℝ) * Real.rpow (N : ℝ) q) := by
    simpa [mul_assoc] using
      (Asymptotics.isBigO_refl (fun N : ℕ => (K N : ℝ)) Filter.atTop).mul
        (hdc.trans (hlogpow (c + 1) hq))
  have htransitionlog := htransition.mul (hlogpow c hδ)
  have heqpow :
      (fun N : ℕ => ((K N : ℝ) * Real.rpow (N : ℝ) (2 - ε₀)) *
        Real.rpow (N : ℝ) δ) =ᶠ[Filter.atTop]
      (fun N : ℕ => (K N : ℝ) * Real.rpow (N : ℝ) q) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
    calc
      ((K N : ℝ) * Real.rpow (N : ℝ) (2 - ε₀)) * Real.rpow (N : ℝ) δ =
          (K N : ℝ) *
            (Real.rpow (N : ℝ) (2 - ε₀) * Real.rpow (N : ℝ) δ) := by ring
      _ = (K N : ℝ) * Real.rpow (N : ℝ) ((2 - ε₀) + δ) :=
        congrArg (fun z : ℝ => (K N : ℝ) * z)
          (Real.rpow_add hNpos (2 - ε₀) δ).symm
      _ = (K N : ℝ) * Real.rpow (N : ℝ) q := by rw [hqeq]
  have hterm2 :
      (fun N : ℕ => (A.transitionBound (N + 1) (m (N + 1))
        (L (N + 1)) (H (N + 1)) : ℝ) * Real.log (N : ℝ) ^ c)
        =O[Filter.atTop]
      (fun N : ℕ => (K N : ℝ) * Real.rpow (N : ℝ) q) :=
    htransitionlog.congr' Filter.EventuallyEq.rfl heqpow
  have hcombined := hterm1.add hterm2
  have hcomparator :
      (fun N : ℕ => ((K N : ℝ) * (d N : ℝ) +
        (A.transitionBound (N + 1) (m (N + 1))
          (L (N + 1)) (H (N + 1)) : ℝ)) * Real.log (N : ℝ) ^ c)
        =O[Filter.atTop]
      (fun N : ℕ => (K N : ℝ) * Real.rpow (N : ℝ) q) := by
    simpa [add_mul] using hcombined
  have hBtime := hsoft'.trans hcomparator
  have hforbidden := h3ov d K hd hK B hB
  apply hforbidden
  exact ⟨δ, hδ, hBtime⟩

@[blueprint "thm:small-embedding-lower-bound"
  (statement := /-- Assume the 3-OV hypothesis. Let $m,L,H:\mathbb N\to\mathbb N$ satisfy the small-embedding regime: $m=\Theta(\log N)$, while $L$ and $H$ are polynomially bounded. Let $A$ be a certified transformer evaluator whose underlying evaluator computes, for every $N>0$, every length-$N$ no-MLP transformer with embedding dimension $m(N)$, $L(N)$ layers, and $H(N)$ heads per layer to entry-wise additive error at most $1/(10N)$. Then there is no fixed $\varepsilon>0$ for which the worst-case running time of $A$ is
  \[
    O\!\left(L(N)H(N)N^{2-\varepsilon}\right).
  \]
  Equivalently, such an evaluator requires $L(N)H(N)N^{2-o(1)}$ time. -/)
  (proof := /-- Suppose, for contradiction, that the underlying evaluator of $A$ has an $O(L(N)H(N)N^{2-\varepsilon})$ running-time bound for some fixed $\varepsilon>0$. Applying \cref{lem:fast-small-embedding-refutes-three-ov} to $m,L,H,A$, the small-embedding hypothesis, the correctness hypothesis, and this running-time bound yields the negation of the 3-OV hypothesis. This contradicts the assumed 3-OV hypothesis. Hence no such fixed power saving exists. -/)
  (title := /-- Computational hardness of small-embedding transformers -/)
  (latexEnv := "theorem")]
theorem small_embedding_lower_bound (h3ov : three_ov_hypothesis)
    (m L H : ℕ → ℕ) (hregime : small_embedding_regime m L H)
    (A : certified_transformer_evaluator)
    (hcorrect : computes_no_mlp_transformers A.evaluator m L H) :
    ¬subquadratic_transformer_time A.evaluator m L H := by
  intro hfast
  exact (fast_small_embedding_refutes_three_ov m L H A hregime hcorrect hfast) h3ov

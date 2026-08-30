import Architect
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Block

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

@[blueprint "def:decaying-matrix"
  (statement := /-- For a weight function $f : \mathbb N \to \mathbb R$ and a stream length $n$, the matrix $M_f$ is the $n\times n$ lower-triangular Toeplitz matrix with entry $f(i-j)$ in position $(i,j)$ when $j\leq i$, and zero otherwise. -/)
  (title := /-- The decaying Toeplitz matrix -/)
  (latexEnv := "definition")]
def decaying_matrix (f : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j.1 ≤ i.1 then f (i.1 - j.1) else 0

@[blueprint "def:complex-decaying-matrix"
  (statement := /-- The complexification of $M_f$ is obtained by applying the canonical embedding $\mathbb R\hookrightarrow\mathbb C$ entrywise. -/)
  (title := /-- Complexification of the decaying matrix -/)
  (latexEnv := "definition")]
def complex_decaying_matrix (f : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (decaying_matrix f n i j : ℂ)

@[blueprint "def:decay-polynomial"
  (statement := /-- For $f : \mathbb N\to\mathbb R$ and $n\in\mathbb N$, define
  \[m_{f,n}(z)=\sum_{k=0}^{n-1} f(k)z^k\qquad(z\in\mathbb C).\] -/)
  (title := /-- The decay polynomial -/)
  (latexEnv := "definition")]
def decay_polynomial (f : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k : Fin n, (f k.1 : ℂ) * z ^ k.1

@[blueprint "def:distinguished-root"
  (statement := /-- For a stream length $n$, set $\omega_n=\exp(\pi\iota/n)$. For $n>0$, this is the distinguished $2n$-th root of unity used by the factorization algorithm. -/)
  (title := /-- The distinguished root of unity -/)
  (latexEnv := "definition")]
noncomputable def distinguished_root (n : ℕ) : ℂ :=
  Complex.exp (((Real.pi : ℂ) / (n : ℂ)) * Complex.I)

@[blueprint "def:real-row-p-trace"
  (statement := /-- If $A$ is a real $m\times d$ matrix and $p\in\mathbb N$, define its generalized $p$-trace by
  \[\operatorname{Tr}_p(A)=\left(\sum_{i=0}^{m-1}\left(\sum_{j=0}^{d-1}A_{ij}^2\right)^{p/2}\right)^{1/p},\]
  where all displayed fractional powers are real powers. -/)
  (title := /-- Generalized row trace for real matrices -/)
  (latexEnv := "definition")]
noncomputable def real_row_p_trace {m d : ℕ} (p : ℕ)
    (A : Matrix (Fin m) (Fin d) ℝ) : ℝ :=
  Real.rpow (∑ i : Fin m,
    Real.rpow (∑ j : Fin d, (A i j) ^ 2) ((p : ℝ) / 2)) (1 / (p : ℝ))

@[blueprint "def:complex-row-p-trace"
  (statement := /-- If $A$ is a complex $m\times d$ matrix and $p\in\mathbb N$, define
  \[\operatorname{Tr}^{\mathbb C}_p(A)=\left(\sum_i\left(\sum_j|A_{ij}|^2\right)^{p/2}\right)^{1/p}.\] -/)
  (title := /-- Generalized row trace for complex matrices -/)
  (latexEnv := "definition")]
noncomputable def complex_row_p_trace {m d : ℕ} (p : ℕ)
    (A : Matrix (Fin m) (Fin d) ℂ) : ℝ :=
  Real.rpow (∑ i : Fin m,
    Real.rpow (∑ j : Fin d, ‖A i j‖ ^ 2) ((p : ℝ) / 2)) (1 / (p : ℝ))

@[blueprint "def:real-column-norm"
  (statement := /-- For a real matrix $A$, define $\lVert A\rVert_{1\to2}$ to be the supremum, over its columns, of their Euclidean norms. For a nonempty finite column set this supremum is the maximum column norm. -/)
  (title := /-- Maximum Euclidean column norm -/)
  (latexEnv := "definition")]
noncomputable def real_column_norm {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) : ℝ :=
  sSup (Set.range fun j : Fin d => Real.sqrt (∑ i : Fin m, (A i j) ^ 2))

@[blueprint "def:complex-column-norm"
  (statement := /-- For a complex matrix $A$, define $\lVert A\rVert_{1\to2}$ to be the supremum of the Euclidean norms of its columns. -/)
  (title := /-- Maximum complex Euclidean column norm -/)
  (latexEnv := "definition")]
noncomputable def complex_column_norm {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℂ) : ℝ :=
  sSup (Set.range fun j : Fin d => Real.sqrt (∑ i : Fin m, ‖A i j‖ ^ 2))

@[blueprint "def:real-maximum-row-norm"
  (statement := /-- For a real matrix $A$, define $\operatorname{Tr}_\infty(A)$ as the supremum of the Euclidean norms of its rows. -/)
  (title := /-- Maximum real row norm -/)
  (latexEnv := "definition")]
noncomputable def real_maximum_row_norm {m d : ℕ}
    (A : Matrix (Fin m) (Fin d) ℝ) : ℝ :=
  sSup (Set.range fun i : Fin m => Real.sqrt (∑ j : Fin d, (A i j) ^ 2))

@[blueprint "def:complex-maximum-row-norm"
  (statement := /-- For a complex matrix $A$, define $\operatorname{Tr}^{\mathbb C}_\infty(A)$ as the supremum of the Euclidean norms of its rows. -/)
  (title := /-- Maximum complex row norm -/)
  (latexEnv := "definition")]
noncomputable def complex_maximum_row_norm {m d : ℕ}
    (A : Matrix (Fin m) (Fin d) ℂ) : ℝ :=
  sSup (Set.range fun i : Fin m => Real.sqrt (∑ j : Fin d, ‖A i j‖ ^ 2))

@[blueprint "def:finite-p-factorization-norm"
  (statement := /-- For a real $n\times n$ matrix $M$ and $p\in\mathbb N$, define $\gamma_{(p)}(M)$ as the infimum of $\operatorname{Tr}_p(B)\lVert C\rVert_{1\to2}$ over all finite inner dimensions $d$ and all real factorizations $M=BC$. -/)
  (title := /-- The finite-$p$ factorization norm -/)
  (latexEnv := "definition")]
noncomputable def finite_p_factorization_norm {n : ℕ} (p : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {c : ℝ | ∃ (d : ℕ) (B : Matrix (Fin n) (Fin d) ℝ)
    (C : Matrix (Fin d) (Fin n) ℝ),
    M = B * C ∧ c = real_row_p_trace p B * real_column_norm C}

@[blueprint "def:infinite-factorization-norm"
  (statement := /-- Define $\gamma_{(\infty)}(M)$ as the infimum of $\operatorname{Tr}_\infty(B)\lVert C\rVert_{1\to2}$ over all finite-dimensional real factorizations $M=BC$. -/)
  (title := /-- The infinite factorization norm -/)
  (latexEnv := "definition")]
noncomputable def infinite_factorization_norm {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {c : ℝ | ∃ (d : ℕ) (B : Matrix (Fin n) (Fin d) ℝ)
    (C : Matrix (Fin d) (Fin n) ℝ),
    M = B * C ∧ c = real_maximum_row_norm B * real_column_norm C}

@[blueprint "def:operator-two-factorization-norm"
  (statement := /-- The operator-$2$ factorization norm is, by convention, $\gamma_{\mathrm{op},2}(M):=\gamma_{(\infty)}(M)$. -/)
  (title := /-- Operator-$2$ factorization norm -/)
  (latexEnv := "definition")]
noncomputable def operator_two_factorization_norm {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  infinite_factorization_norm M

@[blueprint "def:frobenius-factorization-norm"
  (statement := /-- The Frobenius factorization norm is, by convention, $\gamma_{\mathrm F}(M):=\gamma_{(2)}(M)$. -/)
  (title := /-- Frobenius factorization norm -/)
  (latexEnv := "definition")]
noncomputable def frobenius_factorization_norm {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  finite_p_factorization_norm 2 M

@[blueprint "def:lower-triangular"
  (statement := /-- A square matrix $L$ is lower triangular when $L_{ij}=0$ for every pair of indices satisfying $i<j$. -/)
  (title := /-- Lower-triangular matrices -/)
  (latexEnv := "definition")]
def lower_triangular {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  L.BlockTriangular OrderDual.toDual

@[blueprint "def:fourier-bound"
  (statement := /-- For $n>0$ and $p\geq2$, the Fourier bound is
  \[\mathcal B_p(f,n)=\frac{1}{2n^{1-1/p}}\sum_{k=0}^{2n-1}\left|m_{f,n}(\omega_n^k)\right|.\] -/)
  (title := /-- The finite-$p$ Fourier bound -/)
  (latexEnv := "definition")]
noncomputable def fourier_bound (f : ℕ → ℝ) (n p : ℕ) : ℝ :=
  (∑ k : Fin (2 * n), ‖decay_polynomial f n (distinguished_root n ^ k.1)‖) /
    (2 * Real.rpow (n : ℝ) (1 - 1 / (p : ℝ)))

@[blueprint "def:operator-fourier-bound"
  (statement := /-- The operator-$2$ specialization of the Fourier bound is
  \[\mathcal B_\infty(f,n)=\frac{1}{2n}\sum_{k=0}^{2n-1}\left|m_{f,n}(\omega_n^k)\right|.\] -/)
  (title := /-- The operator-$2$ Fourier bound -/)
  (latexEnv := "definition")]
noncomputable def operator_fourier_bound (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ k : Fin (2 * n), ‖decay_polynomial f n (distinguished_root n ^ k.1)‖) /
    (2 * (n : ℝ))

@[blueprint "def:frobenius-fourier-bound"
  (statement := /-- The Frobenius specialization of the Fourier bound is
  \[\mathcal B_{\mathrm F}(f,n)=\frac{1}{2\sqrt n}\sum_{k=0}^{2n-1}\left|m_{f,n}(\omega_n^k)\right|.\] -/)
  (title := /-- The Frobenius Fourier bound -/)
  (latexEnv := "definition")]
noncomputable def frobenius_fourier_bound (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ k : Fin (2 * n), ‖decay_polynomial f n (distinguished_root n ^ k.1)‖) /
    (2 * Real.sqrt (n : ℝ))

@[blueprint "def:toeplitz-factorization-output"
  (statement := /-- An output at stream length $n$ consists of two real square matrices $L$ and $R$. -/)
  (title := /-- Output type for the factorization algorithm -/)
  (latexEnv := "definition")]
structure toeplitz_factorization_output (n : ℕ) where
  left : Matrix (Fin n) (Fin n) ℝ
  right : Matrix (Fin n) (Fin n) ℝ

@[blueprint "def:real-arithmetic-expression"
  (statement := /-- A real arithmetic expression is a finite expression formed from register reads, integer constants, $\pi$, oracle queries $f(k)$, the arithmetic operations, square roots, trigonometric functions, and sign tests. These are the exact-real primitives used to model the factorization algorithm. -/)
  (title := /-- Finite real-oracle arithmetic expressions -/)
  (latexEnv := "definition")]
inductive real_arithmetic_expression where
  | register : ℕ → real_arithmetic_expression
  | weight : ℕ → real_arithmetic_expression
  | integer : ℤ → real_arithmetic_expression
  | pi : real_arithmetic_expression
  | neg : real_arithmetic_expression → real_arithmetic_expression
  | add : real_arithmetic_expression → real_arithmetic_expression → real_arithmetic_expression
  | mul : real_arithmetic_expression → real_arithmetic_expression → real_arithmetic_expression
  | div : real_arithmetic_expression → real_arithmetic_expression → real_arithmetic_expression
  | sqrt : real_arithmetic_expression → real_arithmetic_expression
  | sin : real_arithmetic_expression → real_arithmetic_expression
  | cos : real_arithmetic_expression → real_arithmetic_expression
  | branchNonnegative : real_arithmetic_expression → real_arithmetic_expression →
      real_arithmetic_expression → real_arithmetic_expression

@[blueprint "def:real-arithmetic-expression-evaluate"
  (statement := /-- Given an oracle $f:\mathbb N\to\mathbb R$ and a finite list of previously computed register values, evaluation assigns to every real arithmetic expression the real number obtained by carrying out its indicated register reads, primitive operations, and oracle queries. An out-of-range register read returns zero, and a sign test evaluates only its selected branch. -/)
  (title := /-- Evaluation of real-oracle arithmetic expressions -/)
  (latexEnv := "definition")]
noncomputable def real_arithmetic_expression_evaluate (f : ℕ → ℝ) (registers : List ℝ) :
    real_arithmetic_expression → ℝ
  | .register k => registers.getD k 0
  | .weight k => f k
  | .integer z => (z : ℝ)
  | .pi => Real.pi
  | .neg x => -real_arithmetic_expression_evaluate f registers x
  | .add x y =>
      real_arithmetic_expression_evaluate f registers x +
        real_arithmetic_expression_evaluate f registers y
  | .mul x y =>
      real_arithmetic_expression_evaluate f registers x *
        real_arithmetic_expression_evaluate f registers y
  | .div x y =>
      real_arithmetic_expression_evaluate f registers x /
        real_arithmetic_expression_evaluate f registers y
  | .sqrt x => Real.sqrt (real_arithmetic_expression_evaluate f registers x)
  | .sin x => Real.sin (real_arithmetic_expression_evaluate f registers x)
  | .cos x => Real.cos (real_arithmetic_expression_evaluate f registers x)
  | .branchNonnegative c x y =>
      if 0 ≤ real_arithmetic_expression_evaluate f registers c then
        real_arithmetic_expression_evaluate f registers x
      else
        real_arithmetic_expression_evaluate f registers y

@[blueprint "def:real-arithmetic-expression-operation-count"
  (statement := /-- The operation count of a real arithmetic expression is defined structurally: register reads and constants cost no arithmetic operations, an oracle query costs one, each unary or binary primitive costs one in addition to its arguments, and a sign test is charged for its condition and for the more expensive branch. Consequently this count bounds the number of arithmetic primitives used by evaluation for every oracle and register list. -/)
  (title := /-- Structural operation count for arithmetic expressions -/)
  (latexEnv := "definition")]
def real_arithmetic_expression_operation_count : real_arithmetic_expression → ℕ
  | .register _ => 0
  | .weight _ => 1
  | .integer _ => 0
  | .pi => 0
  | .neg x => 1 + real_arithmetic_expression_operation_count x
  | .add x y => 1 + real_arithmetic_expression_operation_count x +
      real_arithmetic_expression_operation_count y
  | .mul x y => 1 + real_arithmetic_expression_operation_count x +
      real_arithmetic_expression_operation_count y
  | .div x y => 1 + real_arithmetic_expression_operation_count x +
      real_arithmetic_expression_operation_count y
  | .sqrt x => 1 + real_arithmetic_expression_operation_count x
  | .sin x => 1 + real_arithmetic_expression_operation_count x
  | .cos x => 1 + real_arithmetic_expression_operation_count x
  | .branchNonnegative c x y => 1 + real_arithmetic_expression_operation_count c +
      max (real_arithmetic_expression_operation_count x)
        (real_arithmetic_expression_operation_count y)

@[blueprint "def:factorization-arithmetic-program"
  (statement := /-- A factorization program of size $n$ is a finite straight-line list of real arithmetic instructions, together with two $n\times n$ matrices of register indices specifying its output. Later instructions may read values placed in registers by earlier instructions, so common intermediate computations are shared. -/)
  (title := /-- Finite arithmetic programs for matrix factorization -/)
  (latexEnv := "definition")]
structure factorization_arithmetic_program (n : ℕ) where
  instructions : List real_arithmetic_expression
  left : Matrix (Fin n) (Fin n) ℕ
  right : Matrix (Fin n) (Fin n) ℕ

@[blueprint "def:factorization-arithmetic-program-evaluate"
  (statement := /-- Evaluating a factorization program against $f:\mathbb N\to\mathbb R$ processes its instruction list from left to right, appending the value of each instruction to the register list. The two output matrices are obtained by reading the designated registers, with an out-of-range register read defined to be zero. -/)
  (title := /-- Evaluation of a factorization arithmetic program -/)
  (latexEnv := "definition")]
noncomputable def factorization_arithmetic_program_evaluate {n : ℕ}
    (P : factorization_arithmetic_program n) (f : ℕ → ℝ) :
    toeplitz_factorization_output n :=
  let registers := P.instructions.foldl
    (fun values instruction =>
      values ++ [real_arithmetic_expression_evaluate f values instruction]) []
  { left := fun i j => registers.getD (P.left i j) 0
    right := fun i j => registers.getD (P.right i j) 0 }

@[blueprint "def:factorization-arithmetic-program-operation-count"
  (statement := /-- The operation count of a factorization program is the sum of the structural counts of its instruction list. It therefore bounds the primitive operations used by the same left-to-right evaluation that produces the output, while counting shared intermediate results only once. -/)
  (title := /-- Operation count of a factorization arithmetic program -/)
  (latexEnv := "definition")]
def factorization_arithmetic_program_operation_count {n : ℕ}
    (P : factorization_arithmetic_program n) : ℕ :=
  (P.instructions.map real_arithmetic_expression_operation_count).sum

@[blueprint "def:natural-list-code"
  (statement := /-- The canonical code of a finite list of natural numbers is defined recursively by
  \[\langle\,\rangle=0,\qquad
    \langle a_0,a_1,\ldots,a_{r-1}\rangle
      =1+\operatorname{pair}(a_0,\langle a_1,\ldots,a_{r-1}\rangle),\]
  where $\operatorname{pair}:\mathbb N^2\to\mathbb N$ is the standard injective pairing function. -/)
  (title := /-- Canonical coding of finite natural-number lists -/)
  (latexEnv := "definition")]
def natural_list_code : List ℕ → ℕ
  | [] => 0
  | a :: entries => Nat.succ (Nat.pair a (natural_list_code entries))

@[blueprint "def:real-arithmetic-expression-code"
  (statement := /-- Each finite real-oracle arithmetic expression has a canonical natural-number code. Distinct constructor tags are paired with the recursively computed codes of all constructor arguments; integer constants use their standard natural-number encoding. -/)
  (title := /-- Canonical coding of arithmetic expressions -/)
  (latexEnv := "definition")]
def real_arithmetic_expression_code : real_arithmetic_expression → ℕ
  | .register k => Nat.pair 0 k
  | .weight k => Nat.pair 1 k
  | .integer z => Nat.pair 2 (Encodable.encode z)
  | .pi => Nat.pair 3 0
  | .neg x => Nat.pair 4 (real_arithmetic_expression_code x)
  | .add x y => Nat.pair 5
      (Nat.pair (real_arithmetic_expression_code x) (real_arithmetic_expression_code y))
  | .mul x y => Nat.pair 6
      (Nat.pair (real_arithmetic_expression_code x) (real_arithmetic_expression_code y))
  | .div x y => Nat.pair 7
      (Nat.pair (real_arithmetic_expression_code x) (real_arithmetic_expression_code y))
  | .sqrt x => Nat.pair 8 (real_arithmetic_expression_code x)
  | .sin x => Nat.pair 9 (real_arithmetic_expression_code x)
  | .cos x => Nat.pair 10 (real_arithmetic_expression_code x)
  | .branchNonnegative c x y => Nat.pair 11
      (Nat.pair (real_arithmetic_expression_code c)
        (Nat.pair (real_arithmetic_expression_code x) (real_arithmetic_expression_code y)))

@[blueprint "def:factorization-arithmetic-program-code"
  (statement := /-- The canonical code of a size-$n$ factorization program records, in order, the codes of its instruction list and the row-major lists of register indices specifying its left and right output matrices. -/)
  (title := /-- Canonical coding of factorization programs -/)
  (latexEnv := "definition")]
def factorization_arithmetic_program_code {n : ℕ}
    (P : factorization_arithmetic_program n) : ℕ :=
  natural_list_code
    [natural_list_code (P.instructions.map real_arithmetic_expression_code),
      natural_list_code (List.ofFn fun i : Fin n =>
        natural_list_code (List.ofFn fun j : Fin n => P.left i j)),
      natural_list_code (List.ofFn fun i : Fin n =>
        natural_list_code (List.ofFn fun j : Fin n => P.right i j))]

@[blueprint "def:uniform-factorization-generator-instruction"
  (statement := /-- A generator instruction acts on natural-number registers. It may write zero, a successor, a predecessor, a paired value, or either component of a paired value; jump unconditionally; branch according to whether a register is zero; or halt. Source and destination registers and jump targets are fixed natural numbers in the finite instruction list. -/)
  (title := /-- Instructions for uniform factorization-program generators -/)
  (latexEnv := "definition")]
inductive uniform_factorization_generator_instruction where
  | zero : ℕ → uniform_factorization_generator_instruction
  | successor : ℕ → ℕ → uniform_factorization_generator_instruction
  | predecessor : ℕ → ℕ → uniform_factorization_generator_instruction
  | pair : ℕ → ℕ → ℕ → uniform_factorization_generator_instruction
  | left : ℕ → ℕ → uniform_factorization_generator_instruction
  | right : ℕ → ℕ → uniform_factorization_generator_instruction
  | jump : ℕ → uniform_factorization_generator_instruction
  | jumpIfZero : ℕ → ℕ → ℕ → uniform_factorization_generator_instruction
  | halt : uniform_factorization_generator_instruction

@[blueprint "def:uniform-factorization-program-generator"
  (statement := /-- A uniform factorization-program generator is one finite register-machine instruction list, independent of the stream length. On input $n$, register $0$ initially contains $n$ and every other register initially contains zero. -/)
  (title := /-- Finite uniform generators for factorization programs -/)
  (latexEnv := "definition")]
structure uniform_factorization_program_generator where
  instructions : List uniform_factorization_generator_instruction

@[blueprint "def:uniform-factorization-program-generator-evaluate"
  (statement := /-- Given a uniform generator $G$, a fuel bound $s$, and an input size $n$, evaluation starts at instruction $0$ with $n$ in register $0$. Each fetched instruction consumes one unit of fuel, updates the registers and program counter according to its syntax, and a halt returns the value in register $0$. Evaluation returns no value if the fuel is exhausted or the counter leaves the finite instruction list. Thus a successful evaluation with fuel $s$ certifies generation in at most $s$ machine steps. -/)
  (title := /-- Fuel-bounded evaluation of a uniform generator -/)
  (latexEnv := "definition")]
def uniform_factorization_program_generator_evaluate
    (G : uniform_factorization_program_generator) (fuel input : ℕ) : Option ℕ :=
  let rec loop : ℕ → ℕ → (ℕ → ℕ) → Option ℕ
    | 0, _, _ => none
    | steps + 1, counter, registers =>
        match G.instructions[counter]? with
        | none => none
        | some .halt => some (registers 0)
        | some (.zero target) =>
            loop steps (counter + 1) (fun r => if r = target then 0 else registers r)
        | some (.successor source target) =>
            loop steps (counter + 1)
              (fun r => if r = target then Nat.succ (registers source) else registers r)
        | some (.predecessor source target) =>
            loop steps (counter + 1)
              (fun r => if r = target then (registers source).pred else registers r)
        | some (.pair left right target) =>
            loop steps (counter + 1)
              (fun r => if r = target then Nat.pair (registers left) (registers right)
                else registers r)
        | some (.left source target) =>
            loop steps (counter + 1)
              (fun r => if r = target then (registers source).unpair.1 else registers r)
        | some (.right source target) =>
            loop steps (counter + 1)
              (fun r => if r = target then (registers source).unpair.2 else registers r)
        | some (.jump target) => loop steps target registers
        | some (.jumpIfZero source zeroTarget nonzeroTarget) =>
            loop steps (if registers source = 0 then zeroTarget else nonzeroTarget) registers
  loop fuel 0 (fun r => if r = 0 then input else 0)

@[blueprint "def:toeplitz-factorization-algorithm"
  (statement := /-- A Toeplitz factorization algorithm is an explicitly specified family $(P_n)_{n\geq0}$, where $P_n$ is a finite real-oracle arithmetic program whose output consists of two $n\times n$ real matrices. -/)
  (title := /-- Toeplitz factorization algorithms -/)
  (latexEnv := "definition")]
structure toeplitz_factorization_algorithm where
  program : (n : ℕ) → factorization_arithmetic_program n

@[blueprint "def:toeplitz-factorization-algorithm-run"
  (statement := /-- The output of a Toeplitz factorization algorithm $A$ on $(f,n)$ is obtained by evaluating its size-$n$ program $P_n$ against the oracle $f:\mathbb N\to\mathbb R$. -/)
  (title := /-- Evaluation of a Toeplitz factorization algorithm -/)
  (latexEnv := "definition")]
noncomputable def toeplitz_factorization_algorithm_run
    (A : toeplitz_factorization_algorithm) (f : ℕ → ℝ) (n : ℕ) :
    toeplitz_factorization_output n :=
  factorization_arithmetic_program_evaluate (A.program n) f

@[blueprint "def:toeplitz-factorization-algorithm-operation-count"
  (statement := /-- The operation count of a Toeplitz factorization algorithm $A$ at stream length $n$ is the structural number of oracle queries and real arithmetic operations in its size-$n$ program $P_n$. -/)
  (title := /-- Structural operation count -/)
  (latexEnv := "definition")]
def toeplitz_factorization_algorithm_operation_count
    (A : toeplitz_factorization_algorithm) (n : ℕ) : ℕ :=
  factorization_arithmetic_program_operation_count (A.program n)

@[blueprint "def:factorization-algorithm-efficient"
  (statement := /-- A Toeplitz factorization algorithm is efficient if there exist constants $C,q\in\mathbb N$, with $C>0$, such that the structural operation count of its size-$n$ program is at most $C(n+1)^q$ for every $n\in\mathbb N$. -/)
  (title := /-- Polynomial-time efficiency -/)
  (latexEnv := "definition")]
def factorization_algorithm_efficient (A : toeplitz_factorization_algorithm) : Prop :=
  ∃ C q : ℕ, 0 < C ∧ ∀ n : ℕ,
    toeplitz_factorization_algorithm_operation_count A n ≤ C * (n + 1) ^ q

@[blueprint "def:factorization-output-valid"
  (statement := /-- An output $(L,R)$ is valid for $(f,n)$ when $M_f=LR$ and $L$ is lower triangular. -/)
  (title := /-- Validity of an algorithm output -/)
  (latexEnv := "definition")]
def factorization_output_valid (f : ℕ → ℝ) (n : ℕ)
    (out : toeplitz_factorization_output n) : Prop :=
  decaying_matrix f n = out.left * out.right ∧ lower_triangular out.left

@[blueprint "lem:fourier-complex-factorization-root"
  (statement := /-- If $n\in\mathbb N$ is positive and $\omega_n=\exp(\pi\iota/n)$, then $|\omega_n|=1$ and $\omega_n^{2n}=1$. -/)
  (proof := /-- Expand $\omega_n$ using \cref{def:distinguished-root}. Its exponent is purely imaginary, so its norm is one. Multiplying the exponent by $2n$ gives $2\pi\iota$ because $n>0$, and Euler's identity gives the asserted power. -/)
  (title := /-- The distinguished root has order dividing $2n$ -/)
  (latexEnv := "lemma")]
lemma fourier_complex_factorization_root (n : ℕ) (hn : 0 < n) :
    ‖distinguished_root n‖ = 1 ∧ distinguished_root n ^ (2 * n) = 1 := by
  constructor
  · simp [distinguished_root, Complex.norm_exp]
  · rw [distinguished_root, ← Complex.exp_nat_mul]
    rw [show ((2 * n : ℕ) : ℂ) * (((Real.pi : ℂ) / (n : ℂ)) * Complex.I) =
        2 * (Real.pi : ℂ) * Complex.I by
      push_cast
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      field_simp [hn0]]
    exact Complex.exp_two_pi_mul_I

@[blueprint "lem:fourier-complex-factorization-root-ne-one"
  (statement := /-- If $n>0$ and $0<t<2n$, then the $t$-th power of $\omega_n$ is not one. -/)
  (proof := /-- By \cref{def:distinguished-root}, equality to one would force $t\pi\iota/n$ to be an integral multiple of $2\pi\iota$. Comparing imaginary parts and using $0<t<2n$ rules out every such integer multiple. -/)
  (title := /-- Nontrivial powers of the distinguished root -/)
  (latexEnv := "lemma")]
lemma fourier_complex_factorization_root_ne_one (n t : ℕ) (hn : 0 < n)
    (ht0 : 0 < t) (htN : t < 2 * n) : distinguished_root n ^ t ≠ 1 := by
  intro he
  rw [distinguished_root, ← Complex.exp_nat_mul] at he
  obtain ⟨z, hz⟩ := Complex.exp_eq_one_iff.mp he
  have him := congrArg Complex.im hz
  norm_num at him
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht0R : (0 : ℝ) < t := by exact_mod_cast ht0
  have htNR : (t : ℝ) < 2 * n := by exact_mod_cast htN
  have hn0R : (n : ℝ) ≠ 0 := ne_of_gt hnR
  field_simp [hn0R] at him
  have hzposR : (0 : ℝ) < z := by nlinarith [Real.pi_pos]
  have hzltR : (z : ℝ) < 1 := by nlinarith [Real.pi_pos]
  have hzpos : (0 : ℤ) < z := by exact_mod_cast hzposR
  have hzlt : z < (1 : ℤ) := by exact_mod_cast hzltR
  omega

@[blueprint "lem:fourier-complex-factorization-sum-zero"
  (statement := /-- If $n>0$ and $0<t<2n$, then the sum of the first $2n$ powers of $\omega_n^t$ is zero. -/)
  (proof := /-- By \cref{lem:fourier-complex-factorization-root}, the ratio $\omega_n^t$ has $(2n)$-th power one, while \cref{lem:fourier-complex-factorization-root-ne-one} shows that the ratio itself is not one. The finite geometric-series identity therefore gives zero. -/)
  (title := /-- Orthogonality of nontrivial Fourier modes -/)
  (latexEnv := "lemma")]
lemma fourier_complex_factorization_sum_zero (n t : ℕ) (hn : 0 < n)
    (ht0 : 0 < t) (htN : t < 2 * n) :
    (∑ k : Fin (2 * n), distinguished_root n ^ (t * k.1)) = 0 := by
  have hroot := (fourier_complex_factorization_root n hn).2
  have hne := fourier_complex_factorization_root_ne_one n t hn ht0 htN
  have hpow : (distinguished_root n ^ t) ^ (2 * n) = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hroot, one_pow]
  have hgeom := geom_sum_mul (distinguished_root n ^ t) (2 * n)
  rw [hpow, sub_self] at hgeom
  have hsum : ∑ k ∈ Finset.range (2 * n), (distinguished_root n ^ t) ^ k = 0 :=
    (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)
  calc
    (∑ k : Fin (2 * n), distinguished_root n ^ (t * k.1)) =
        ∑ k : Fin (2 * n), (distinguished_root n ^ t) ^ k.1 := by
          simp only [pow_mul]
    _ = ∑ k ∈ Finset.range (2 * n), (distinguished_root n ^ t) ^ k :=
      Fin.sum_univ_eq_sum_range _ _
    _ = 0 := hsum

@[blueprint "lem:fourier-complex-factorization-mode-sum"
  (statement := /-- Let $n>0$ and $i,j,r\in\{0,\ldots,n-1\}$. The sum over the $2n$ Fourier modes with exponent $(r+2n-i+j)k$ equals $2n$ when $r+j=i$, and equals zero otherwise. -/)
  (proof := /-- If $r+j=i$, the exponent coefficient is $2n$, so every summand is one by \cref{lem:fourier-complex-factorization-root}. Otherwise the coefficient lies strictly between $0$ and $4n$ and differs from $2n$; reduce it modulo $2n$ with \cref{lem:fourier-complex-factorization-root} and apply \cref{lem:fourier-complex-factorization-sum-zero} to the resulting nontrivial mode. -/)
  (title := /-- Orthogonality in the Toeplitz index range -/)
  (latexEnv := "lemma")]
lemma fourier_complex_factorization_mode_sum (n : ℕ) (hn : 0 < n)
    (i j r : Fin n) :
    (∑ k : Fin (2 * n), distinguished_root n ^
      ((r.1 + (2 * n - i.1 + j.1)) * k.1)) =
      if r.1 + j.1 = i.1 then (2 * n : ℂ) else 0 := by
  by_cases hrij : r.1 + j.1 = i.1
  · rw [if_pos hrij]
    have hcoef : r.1 + (2 * n - i.1 + j.1) = 2 * n := by omega
    simp [hcoef, pow_mul, (fourier_complex_factorization_root n hn).2]
  · rw [if_neg hrij]
    let q := r.1 + (2 * n - i.1 + j.1)
    have hqpos : 0 < q := by dsimp [q]; omega
    have hq_lt : q < 2 * (2 * n) := by dsimp [q]; omega
    have hq_ne : q ≠ 2 * n := by dsimp [q]; omega
    have hq_big : 2 * n < q ∨ q < 2 * n := by omega
    rcases hq_big with hbig | hsmall
    · have hsubpos : 0 < q - 2 * n := by omega
      have hsublt : q - 2 * n < 2 * n := by omega
      have hsum := fourier_complex_factorization_sum_zero n (q - 2 * n) hn hsubpos hsublt
      have hroot := (fourier_complex_factorization_root n hn).2
      change (∑ k : Fin (2 * n), distinguished_root n ^ (q * k.1)) = 0
      rw [show q = (q - 2 * n) + 2 * n by omega]
      simp only [add_mul, pow_add, pow_mul, hroot, one_pow, mul_one]
      simpa only [pow_mul] using hsum
    · exact fourier_complex_factorization_sum_zero n q hn hqpos hsmall

@[blueprint "lem:fourier-complex-factorization-inversion"
  (statement := /-- For $n>0$ and indices $i,j<n$, Fourier inversion of the samples $m_{f,n}(\omega_n^k)$ gives $2n$ times the $(i,j)$ entry of the complexified lower-triangular Toeplitz matrix. -/)
  (proof := /-- Expand the decay polynomial by \cref{def:decay-polynomial}, interchange the two finite sums, and combine powers of $\omega_n$. The inner sum is evaluated by \cref{lem:fourier-complex-factorization-mode-sum}: it vanishes unless the polynomial index $r$ satisfies $r+j=i$, in which case it is $2n$. If $j\leq i$, exactly the term $r=i-j$ remains and equals the entry specified by \cref{def:decaying-matrix,def:complex-decaying-matrix}; if $i<j$, every term vanishes. -/)
  (title := /-- Fourier inversion for the decaying matrix -/)
  (latexEnv := "lemma")]
lemma fourier_complex_factorization_inversion (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (i j : Fin n) :
    (∑ k : Fin (2 * n), decay_polynomial f n (distinguished_root n ^ k.1) *
      distinguished_root n ^ ((2 * n - i.1 + j.1) * k.1)) =
      (2 * n : ℂ) * complex_decaying_matrix f n i j := by
  classical
  calc
    (∑ k : Fin (2 * n), decay_polynomial f n (distinguished_root n ^ k.1) *
        distinguished_root n ^ ((2 * n - i.1 + j.1) * k.1)) =
        ∑ r : Fin n, (f r.1 : ℂ) *
          (∑ k : Fin (2 * n), distinguished_root n ^
            ((r.1 + (2 * n - i.1 + j.1)) * k.1)) := by
      simp only [decay_polynomial, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [show (distinguished_root n ^ k.1) ^ r.1 =
        distinguished_root n ^ (k.1 * r.1) by rw [pow_mul]]
      rw [mul_assoc, ← pow_add]
      congr 1
      congr 1
      ring
    _ = ∑ r : Fin n, (f r.1 : ℂ) *
        (if r.1 + j.1 = i.1 then (2 * n : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [fourier_complex_factorization_mode_sum n hn i j r]
    _ = (2 * n : ℂ) * complex_decaying_matrix f n i j := by
      by_cases hji : j.1 ≤ i.1
      · let r0 : Fin n := ⟨i.1 - j.1, by omega⟩
        rw [Finset.sum_eq_single r0]
        · simp [r0, complex_decaying_matrix, decaying_matrix, hji]
          ring
        · intro r hr hrne
          have hrij : r.1 + j.1 ≠ i.1 := by
            intro h
            apply hrne
            apply Fin.ext
            dsimp [r0]
            omega
          simp [hrij]
        · simp
      · simp [complex_decaying_matrix, decaying_matrix, hji]
        apply Finset.sum_eq_zero
        intro r hr
        have hrij : r.1 + j.1 ≠ i.1 := by omega
        simp [hrij]

@[blueprint "lem:fourier-complex-factorization-polar-split"
  (statement := /-- Every complex number $z$ is a product $ab$ of two complex numbers satisfying $|a|^2=|b|^2=|z|$. -/)
  (proof := /-- Take $a=\sqrt{|z|}$ and $b=\sqrt{|z|}\exp(\arg(z)\iota)$. The polar decomposition of $z$, the nonnegativity of $|z|$, and the unit norm of the purely imaginary exponential give the product and both squared-norm identities. -/)
  (title := /-- Balanced polar splitting -/)
  (latexEnv := "lemma")]
lemma fourier_complex_factorization_polar_split (z : ℂ) :
    ∃ a b : ℂ, a * b = z ∧ ‖a‖ ^ 2 = ‖z‖ ∧ ‖b‖ ^ 2 = ‖z‖ := by
  refine ⟨(Real.sqrt ‖z‖ : ℝ),
    (Real.sqrt ‖z‖ : ℝ) * Complex.exp ((Complex.arg z : ℂ) * Complex.I), ?_, ?_, ?_⟩
  · calc
      ((Real.sqrt ‖z‖ : ℝ) : ℂ) *
          (((Real.sqrt ‖z‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg z : ℂ) * Complex.I)) =
          ((Real.sqrt ‖z‖ * Real.sqrt ‖z‖ : ℝ) : ℂ) *
            Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
              push_cast
              ring
      _ = (‖z‖ : ℂ) * Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
        rw [Real.mul_self_sqrt (norm_nonneg z)]
      _ = z := Complex.norm_mul_exp_arg_mul_I z
  · simp [Real.sq_sqrt (norm_nonneg z)]
  · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    simp [Real.sq_sqrt (norm_nonneg z)]

@[blueprint "lem:fourier-complex-factorization-witness"
  (statement := /-- For every $f:\mathbb N\to\mathbb R$ and positive $n$, there are complex matrices $A\in\mathbb C^{n\times2n}$ and $B\in\mathbb C^{2n\times n}$ with $M_f^{\mathbb C}=AB$ such that every squared row norm of $A$ is the Fourier sum $S=\sum_k|m_{f,n}(\omega_n^k)|$ and every squared column norm of $B$ is $S/(2n)^2$. -/)
  (proof := /-- Apply \cref{lem:fourier-complex-factorization-polar-split} to every Fourier sample, placing the two balanced factors into $A$ and $B$ together with conjugate Fourier phases and the normalization $1/(2n)$. The product identity follows from \cref{lem:fourier-complex-factorization-inversion}. The phases have unit norm by \cref{lem:fourier-complex-factorization-root}, so the two squared-norm formulas follow term by term from the balanced splitting identities. -/)
  (title := /-- A balanced Fourier witness -/)
  (latexEnv := "lemma")]
lemma fourier_complex_factorization_witness (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    ∃ (A : Matrix (Fin n) (Fin (2 * n)) ℂ)
      (B : Matrix (Fin (2 * n)) (Fin n) ℂ),
      complex_decaying_matrix f n = A * B ∧
      (∀ i : Fin n, ∑ k : Fin (2 * n), ‖A i k‖ ^ 2 =
        ∑ k : Fin (2 * n), ‖decay_polynomial f n (distinguished_root n ^ k.1)‖) ∧
      (∀ j : Fin n, ∑ k : Fin (2 * n), ‖B k j‖ ^ 2 =
        (∑ k : Fin (2 * n), ‖decay_polynomial f n (distinguished_root n ^ k.1)‖) /
          (2 * n : ℝ) ^ 2) := by
  classical
  let coeff : Fin (2 * n) → ℂ := fun k =>
    decay_polynomial f n (distinguished_root n ^ k.1)
  choose a b hab ha hb using fun k => fourier_complex_factorization_polar_split (coeff k)
  let A : Matrix (Fin n) (Fin (2 * n)) ℂ := fun i k =>
    a k * distinguished_root n ^ ((2 * n - i.1) * k.1)
  let B : Matrix (Fin (2 * n)) (Fin n) ℂ := fun k j =>
    b k * distinguished_root n ^ (j.1 * k.1) / (2 * n : ℂ)
  refine ⟨A, B, ?_, ?_, ?_⟩
  · ext i j
    rw [Matrix.mul_apply]
    symm
    calc
      ∑ k, A i k * B k j =
          (∑ k : Fin (2 * n), decay_polynomial f n (distinguished_root n ^ k.1) *
            distinguished_root n ^ ((2 * n - i.1 + j.1) * k.1)) /
            (2 * n : ℂ) := by
        simp only [div_eq_mul_inv]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [A, B]
        rw [div_eq_mul_inv]
        rw [show a k * distinguished_root n ^ ((2 * n - i.1) * k.1) *
            (b k * distinguished_root n ^ (j.1 * k.1) * (2 * n : ℂ)⁻¹) =
            (a k * b k) * (distinguished_root n ^ ((2 * n - i.1) * k.1) *
              distinguished_root n ^ (j.1 * k.1)) * (2 * n : ℂ)⁻¹ by ring]
        rw [hab k]
        dsimp [coeff]
        rw [← pow_add]
        congr 2
        ring
      _ = ((2 * n : ℂ) * complex_decaying_matrix f n i j) / (2 * n : ℂ) := by
        rw [fourier_complex_factorization_inversion f n hn i j]
      _ = complex_decaying_matrix f n i j := by
        have hn0 : (2 * n : ℂ) ≠ 0 := by exact_mod_cast (Nat.mul_pos (by omega) hn).ne'
        apply (div_eq_iff hn0).2
        ring
  · intro i
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [A, coeff]
    rw [norm_mul, norm_pow, (fourier_complex_factorization_root n hn).1,
      one_pow, mul_one]
    exact ha k
  · intro j
    calc
      (∑ k : Fin (2 * n), ‖B k j‖ ^ 2) =
          ∑ k : Fin (2 * n), ‖decay_polynomial f n
            (distinguished_root n ^ k.1)‖ / (2 * n : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [B, coeff]
        rw [norm_div, norm_mul, norm_pow,
          (fourier_complex_factorization_root n hn).1, one_pow, mul_one,
          div_pow, hb k]
        norm_num
        rfl
      _ = (∑ k : Fin (2 * n), ‖decay_polynomial f n
            (distinguished_root n ^ k.1)‖) / (2 * n : ℝ) ^ 2 := by
        simp only [div_eq_mul_inv]
        rw [Finset.sum_mul]

@[blueprint "lem:fourier-complex-factorization"
  (statement := /-- Let $f : \mathbb N\to\mathbb R$ and let $n\in\mathbb N$ satisfy $n>0$. There are complex matrices $\widetilde L\in\mathbb C^{n\times 2n}$ and $\widetilde R\in\mathbb C^{2n\times n}$ whose product is the complexification of $M_f$, such that, for every $p\in\mathbb N$ with $p\geq2$,
  \[\operatorname{Tr}^{\mathbb C}_p(\widetilde L)\lVert\widetilde R\rVert_{1\to2}\leq\mathcal B_p(f,n),\]
  and
  \[\operatorname{Tr}^{\mathbb C}_\infty(\widetilde L)\lVert\widetilde R\rVert_{1\to2}\leq\mathcal B_\infty(f,n).\] -/)
  (proof := /-- Take the matrices $A$ and $B$ supplied by \cref{lem:fourier-complex-factorization-witness}, and write $S=\sum_{k=0}^{2n-1}|m_{f,n}(\omega_n^k)|$. Every squared row norm of $A$ is $S$, whereas every squared column norm of $B$ is $S/(2n)^2$. Hence $\lVert B\rVert_{1\to2}=\sqrt S/(2n)$ and $\operatorname{Tr}^{\mathbb C}_\infty(A)=\sqrt S$. For every natural number $p\geq2$, the equality of all $n$ row norms gives $\operatorname{Tr}^{\mathbb C}_p(A)=n^{1/p}\sqrt S$. Multiplying these identities and using $n^{1-1/p}=n/n^{1/p}$ yields the finite-$p$ bound, while the maximum-row identity gives the infinite bound. -/)
  (title := /-- Complex Fourier factorization and norm bounds -/)
  (latexEnv := "lemma")]
lemma fourier_complex_factorization (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    ∃ (A : Matrix (Fin n) (Fin (2 * n)) ℂ)
      (B : Matrix (Fin (2 * n)) (Fin n) ℂ),
      complex_decaying_matrix f n = A * B ∧
      (∀ p : ℕ, 2 ≤ p →
        complex_row_p_trace p A * complex_column_norm B ≤ fourier_bound f n p) ∧
      complex_maximum_row_norm A * complex_column_norm B ≤ operator_fourier_bound f n := by
  classical
  let S : ℝ := ∑ k : Fin (2 * n),
    ‖decay_polynomial f n (distinguished_root n ^ k.1)‖
  obtain ⟨A, B, hAB, hA, hB⟩ := fourier_complex_factorization_witness f n hn
  change (∀ i, ∑ k, ‖A i k‖ ^ 2 = S) at hA
  change (∀ j, ∑ k, ‖B k j‖ ^ 2 = S / (2 * n : ℝ) ^ 2) at hB
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun k hk => norm_nonneg _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hcol : complex_column_norm B = Real.sqrt S / (2 * n : ℝ) := by
    unfold complex_column_norm
    have hf : (fun j : Fin n => Real.sqrt (∑ i : Fin (2 * n), ‖B i j‖ ^ 2)) =
        fun _ => Real.sqrt (S / (2 * n : ℝ) ^ 2) := by
      funext j
      rw [hB j]
    rw [hf]
    simp only [Set.range_const, csSup_singleton]
    rw [Real.sqrt_div hS, Real.sqrt_sq]
    positivity
  have hmax : complex_maximum_row_norm A = Real.sqrt S := by
    unfold complex_maximum_row_norm
    have hf : (fun i : Fin n => Real.sqrt (∑ j : Fin (2 * n), ‖A i j‖ ^ 2)) =
        fun _ => Real.sqrt S := by
      funext i
      rw [hA i]
    rw [hf]
    simp
  have hptrace (p : ℕ) : complex_row_p_trace p A =
      Real.rpow ((n : ℝ) * Real.rpow S ((p : ℝ) / 2)) (1 / (p : ℝ)) := by
    unfold complex_row_p_trace
    congr 2
    simp_rw [hA]
    simp
  have hpTraceSimple (p : ℕ) (hp : 2 ≤ p) : complex_row_p_trace p A =
      Real.rpow (n : ℝ) (1 / (p : ℝ)) * Real.sqrt S := by
    rw [hptrace]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    have hexp : ((p : ℝ) / 2) * (1 / (p : ℝ)) = 1 / 2 := by
      field_simp [hp0]
    calc
      Real.rpow ((n : ℝ) * Real.rpow S ((p : ℝ) / 2)) (1 / (p : ℝ)) =
          Real.rpow (n : ℝ) (1 / (p : ℝ)) *
            Real.rpow (Real.rpow S ((p : ℝ) / 2)) (1 / (p : ℝ)) :=
        Real.mul_rpow (le_of_lt hnR) (Real.rpow_nonneg hS _)
      _ = Real.rpow (n : ℝ) (1 / (p : ℝ)) *
          Real.rpow S (((p : ℝ) / 2) * (1 / (p : ℝ))) := by
        congr 1
        exact (Real.rpow_mul hS _ _).symm
      _ = Real.rpow (n : ℝ) (1 / (p : ℝ)) * Real.rpow S (1 / 2) :=
        congrArg (fun x : ℝ => Real.rpow (n : ℝ) (1 / (p : ℝ)) * Real.rpow S x) hexp
      _ = Real.rpow (n : ℝ) (1 / (p : ℝ)) * Real.sqrt S := by
        congr 1
        exact (Real.sqrt_eq_rpow S).symm
  refine ⟨A, B, hAB, ?_, ?_⟩
  · intro p hp
    rw [hpTraceSimple p hp, hcol]
    unfold fourier_bound
    change Real.rpow (n : ℝ) (1 / (p : ℝ)) * Real.sqrt S *
        (Real.sqrt S / (2 * n : ℝ)) ≤
      S / (2 * Real.rpow (n : ℝ) (1 - 1 / (p : ℝ)))
    have hsqrt : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hS
    have hpowdiff : Real.rpow (n : ℝ) (1 - 1 / (p : ℝ)) =
        (n : ℝ) / Real.rpow (n : ℝ) (1 / (p : ℝ)) := by
      calc
        Real.rpow (n : ℝ) (1 - 1 / (p : ℝ)) =
            Real.rpow (n : ℝ) 1 / Real.rpow (n : ℝ) (1 / (p : ℝ)) :=
          Real.rpow_sub hnR _ _
        _ = (n : ℝ) / Real.rpow (n : ℝ) (1 / (p : ℝ)) := by
          congr 1
          exact Real.rpow_one (n : ℝ)
    rw [hpowdiff]
    have hcost : Real.rpow (n : ℝ) (1 / (p : ℝ)) * Real.sqrt S *
        (Real.sqrt S / (2 * n : ℝ)) =
        Real.rpow (n : ℝ) (1 / (p : ℝ)) * S / (2 * n : ℝ) := by
      calc
        _ = Real.rpow (n : ℝ) (1 / (p : ℝ)) *
            (Real.sqrt S * Real.sqrt S) / (2 * n : ℝ) := by ring
        _ = _ := by rw [hsqrt]
    rw [hcost]
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hnpow0 : Real.rpow (n : ℝ) (1 / (p : ℝ)) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hnR _)
    field_simp [hn0, hnpow0]
    exact le_rfl
  · rw [hmax, hcol]
    unfold operator_fourier_bound
    change Real.sqrt S * (Real.sqrt S / (2 * n : ℝ)) ≤ S / (2 * (n : ℝ))
    rw [show Real.sqrt S * (Real.sqrt S / (2 * n : ℝ)) =
      (Real.sqrt S * Real.sqrt S) / (2 * n : ℝ) by ring,
      Real.mul_self_sqrt hS]

@[blueprint "lem:realification-preserves-factorization-norms"
  (statement := /-- Let $f\colon\mathbb N\to\mathbb R$ and $n\in\mathbb N$ with $n>0$, and suppose that complex matrices $A\in\mathbb C^{n\times2n}$ and $B\in\mathbb C^{2n\times n}$ satisfy $M_f^{\mathbb C}=AB$. Then there are real matrices $\widehat L\in\mathbb R^{n\times4n}$ and $\widehat R\in\mathbb R^{4n\times n}$ satisfying $M_f=\widehat L\widehat R$ and, for every $p\in\mathbb N$,
  \[\operatorname{Tr}_p(\widehat L)=\operatorname{Tr}^{\mathbb C}_p(A),\qquad
    \operatorname{Tr}_\infty(\widehat L)=\operatorname{Tr}^{\mathbb C}_\infty(A),\qquad
    \lVert\widehat R\rVert_{1\to2}=\lVert B\rVert_{1\to2}.\] -/)
  (proof := /-- Identify two disjoint copies of $\{0,\ldots,2n-1\}$ with $\{0,\ldots,4n-1\}$. On the first copy define $\widehat L_{ik}=\operatorname{Re}A_{ik}$ and $\widehat R_{kj}=\operatorname{Re}B_{kj}$, and on the second define $\widehat L_{ik}=-\operatorname{Im}A_{ik}$ and $\widehat R_{kj}=\operatorname{Im}B_{kj}$. For every row of $A$ and every column of $B$, the identity $|z|^2=(\operatorname{Re}z)^2+(\operatorname{Im}z)^2$ identifies the corresponding sums of squares. The definitions in \cref{def:real-row-p-trace,def:complex-row-p-trace,def:real-maximum-row-norm,def:complex-maximum-row-norm,def:real-column-norm,def:complex-column-norm} therefore give all three asserted cost equalities. Finally,
  \[(\widehat L\widehat R)_{ij}=\sum_k\bigl(\operatorname{Re}A_{ik}\operatorname{Re}B_{kj}-\operatorname{Im}A_{ik}\operatorname{Im}B_{kj}\bigr)
    =\operatorname{Re}(AB)_{ij}.]
  By the hypothesis and the definition of the complexification in \cref{def:complex-decaying-matrix}, the last quantity is $(M_f)_{ij}$, proving $M_f=\widehat L\widehat R$. -/)
  (title := /-- Realification preserves factorization costs -/)
  (latexEnv := "lemma")]
lemma realification_preserves_factorization_norms (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (A : Matrix (Fin n) (Fin (2 * n)) ℂ)
    (B : Matrix (Fin (2 * n)) (Fin n) ℂ)
    (hAB : complex_decaying_matrix f n = A * B) :
    ∃ (Lhat : Matrix (Fin n) (Fin (4 * n)) ℝ)
      (Rhat : Matrix (Fin (4 * n)) (Fin n) ℝ),
      decaying_matrix f n = Lhat * Rhat ∧
      (∀ p : ℕ, real_row_p_trace p Lhat = complex_row_p_trace p A) ∧
      real_maximum_row_norm Lhat = complex_maximum_row_norm A ∧
      real_column_norm Rhat = complex_column_norm B := by
  let e : (Fin (2 * n) ⊕ Fin (2 * n)) ≃ Fin (4 * n) :=
    finSumFinEquiv.trans (finCongr (by omega))
  let Lhat : Matrix (Fin n) (Fin (4 * n)) ℝ := fun i k =>
    Sum.elim (fun j => (A i j).re) (fun j => -(A i j).im) (e.symm k)
  let Rhat : Matrix (Fin (4 * n)) (Fin n) ℝ := fun k j =>
    Sum.elim (fun i => (B i j).re) (fun i => (B i j).im) (e.symm k)
  have hrow (i : Fin n) :
      (∑ k : Fin (4 * n), (Lhat i k) ^ 2) =
        ∑ k : Fin (2 * n), ‖A i k‖ ^ 2 := by
    calc
      (∑ k : Fin (4 * n), (Lhat i k) ^ 2) =
          ∑ k : Fin (2 * n) ⊕ Fin (2 * n), (Lhat i (e k)) ^ 2 :=
        (e.sum_comp (fun k => (Lhat i k) ^ 2)).symm
      _ = (∑ k : Fin (2 * n), (A i k).re ^ 2) +
          ∑ k : Fin (2 * n), (-(A i k).im) ^ 2 := by
        simp [Lhat, Fintype.sum_sum_type]
      _ = ∑ k : Fin (2 * n), ‖A i k‖ ^ 2 := by
        simp_rw [Complex.sq_norm, Complex.normSq_apply]
        rw [Finset.sum_add_distrib]
        simp [pow_two]
  have hcol (j : Fin n) :
      (∑ k : Fin (4 * n), (Rhat k j) ^ 2) =
        ∑ k : Fin (2 * n), ‖B k j‖ ^ 2 := by
    calc
      (∑ k : Fin (4 * n), (Rhat k j) ^ 2) =
          ∑ k : Fin (2 * n) ⊕ Fin (2 * n), (Rhat (e k) j) ^ 2 :=
        (e.sum_comp (fun k => (Rhat k j) ^ 2)).symm
      _ = (∑ k : Fin (2 * n), (B k j).re ^ 2) +
          ∑ k : Fin (2 * n), (B k j).im ^ 2 := by
        simp [Rhat, Fintype.sum_sum_type]
      _ = ∑ k : Fin (2 * n), ‖B k j‖ ^ 2 := by
        simp_rw [Complex.sq_norm, Complex.normSq_apply]
        rw [Finset.sum_add_distrib]
        simp [pow_two]
  refine ⟨Lhat, Rhat, ?_, ?_, ?_, ?_⟩
  · ext i j
    have hre := congrArg Complex.re (congr_fun (congr_fun hAB i) j)
    rw [Matrix.mul_apply]
    calc
      decaying_matrix f n i j =
          ∑ k : Fin (2 * n), ((A i k) * (B k j)).re := by
        simpa [complex_decaying_matrix, Matrix.mul_apply] using hre
      _ = ∑ k : Fin (2 * n) ⊕ Fin (2 * n),
          Lhat i (e k) * Rhat (e k) j := by
        simp [Lhat, Rhat, Fintype.sum_sum_type, Complex.mul_re,
          sub_eq_add_neg, Finset.sum_add_distrib]
      _ = ∑ k : Fin (4 * n), Lhat i k * Rhat k j :=
        e.sum_comp (fun k => Lhat i k * Rhat k j)
  · intro p
    unfold real_row_p_trace complex_row_p_trace
    congr 2
    funext i
    rw [hrow i]
  · unfold real_maximum_row_norm complex_maximum_row_norm
    congr 2
    funext i
    rw [hrow i]
  · unfold real_column_norm complex_column_norm
    congr 2
    funext j
    rw [hcol j]

@[blueprint "lem:qr-lower-triangularization-preserves-norms"
  (statement := /-- Let $f:\mathbb N\to\mathbb R$ and $n>0$, and suppose that $M_f=\widehat L\widehat R$, where $\widehat L\in\mathbb R^{n\times4n}$ and $\widehat R\in\mathbb R^{4n\times n}$. There are square real matrices $L,R\in\mathbb R^{n\times n}$ such that $M_f=LR$, the matrix $L$ is lower triangular, and for every $p\in\mathbb N$,
  \[\operatorname{Tr}_p(L)=\operatorname{Tr}_p(\widehat L),\qquad
    \operatorname{Tr}_\infty(L)=\operatorname{Tr}_\infty(\widehat L),\qquad
    \lVert R\rVert_{1\to2}\leq\lVert\widehat R\rVert_{1\to2}.\] -/)
  (proof := /-- Regard the rows $v_0,\ldots,v_{n-1}$ of $\widehat L$ as vectors in $\mathbb R^{4n}$, append $3n$ zero vectors, and apply Gram--Schmidt with orthonormal-basis extension to this ordered family. Denote the resulting orthonormal basis by $(b_t)_{t<4n}$. Its inverse-triangular property gives $\langle b_j,v_i\rangle=0$ whenever $i<j$; it also gives $\langle b_j,v_i\rangle=0$ for every appended index $j\geq n$. Define $Q_{ik}=(b_i)_k$ and $L_{ij}=\langle b_j,v_i\rangle$ for $i,j<n$. Then $L$ is lower triangular in the sense of \cref{def:lower-triangular}, and the orthonormal-basis expansion of each $v_i$ gives $\widehat L=LQ$. Put $R=Q\widehat R$. It follows that $LR=\widehat L\widehat R=M_f$.

  Parseval's identity, together with the vanishing of the appended coordinates, yields
  \[\sum_{j<n}L_{ij}^2=\sum_{k<4n}\widehat L_{ik}^2\]
  for every row $i$. The definitions in \cref{def:real-row-p-trace, def:real-maximum-row-norm} therefore give the asserted finite-$p$ trace equalities and maximum-row-norm equality. For a column $y$ of $\widehat R$, the entries of the corresponding column of $R$ are the first $n$ coordinates of $y$ in the basis $(b_t)$. Discarding the remaining nonnegative squares from Parseval's identity gives
  \[\sum_{i<n}R_{ij}^2\leq\sum_{k<4n}\widehat R_{kj}^2.\]
  Taking square roots and then the supremum over columns, as in \cref{def:real-column-norm}, proves $\lVert R\rVert_{1\to2}\leq\lVert\widehat R\rVert_{1\to2}$. -/)
  (title := /-- QR triangularization with preservation of costs -/)
  (latexEnv := "lemma")]
lemma qr_lower_triangularization_preserves_norms (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (Lhat : Matrix (Fin n) (Fin (4 * n)) ℝ)
    (Rhat : Matrix (Fin (4 * n)) (Fin n) ℝ)
    (hfactor : decaying_matrix f n = Lhat * Rhat) :
    ∃ (L R : Matrix (Fin n) (Fin n) ℝ),
      decaying_matrix f n = L * R ∧ lower_triangular L ∧
      (∀ p : ℕ, real_row_p_trace p L = real_row_p_trace p Lhat) ∧
      real_maximum_row_norm L = real_maximum_row_norm Lhat ∧
      real_column_norm R ≤ real_column_norm Rhat := by
  classical
  let v : Fin n → EuclideanSpace ℝ (Fin (4 * n)) :=
    fun i => WithLp.toLp 2 (Lhat i)
  let g : Fin (n + 3 * n) → EuclideanSpace ℝ (Fin (4 * n)) :=
    Fin.addCases v (fun _ => 0)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (4 * n))) =
      Fintype.card (Fin (n + 3 * n)) := by
    simp
    omega
  let b : OrthonormalBasis (Fin (n + 3 * n)) ℝ
      (EuclideanSpace ℝ (Fin (4 * n))) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis hdim g
  let Q : Matrix (Fin n) (Fin (4 * n)) ℝ :=
    fun i k => b (Fin.castAdd (3 * n) i) k
  let L : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => b.repr (v i) (Fin.castAdd (3 * n) j)
  let R : Matrix (Fin n) (Fin n) ℝ := Q * Rhat
  have htail (i : Fin n) (j : Fin (3 * n)) :
      b.repr (v i) (Fin.natAdd n j) = 0 := by
    have h := InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular'
      hdim g (show Fin.castAdd (3 * n) i < Fin.natAdd n j by
        change (i : ℕ) < n + (j : ℕ)
        omega)
    simpa [b, g] using h
  have hLQ : L * Q = Lhat := by
    ext i k
    have hk := congrArg (fun x : EuclideanSpace ℝ (Fin (4 * n)) => x k)
      (b.sum_repr (v i))
    rw [Fin.sum_univ_add] at hk
    simpa [Matrix.mul_apply, L, Q, v, htail] using hk
  have hrow (i : Fin n) :
      ∑ j : Fin n, (L i j) ^ 2 = ∑ k : Fin (4 * n), (Lhat i k) ^ 2 := by
    have hp := b.sum_sq_norm_inner_right (v i)
    rw [Fin.sum_univ_add, EuclideanSpace.real_norm_sq_eq] at hp
    simpa [← b.repr_apply_apply, L, v, htail] using hp
  have hRcoeff (i j : Fin n) : R i j =
      b.repr (WithLp.toLp 2 (fun k : Fin (4 * n) => Rhat k j))
        (Fin.castAdd (3 * n) i) := by
    rw [b.repr_apply_apply]
    simp [R, Q, Matrix.mul_apply, PiLp.inner_apply, Real.inner_apply, mul_comm]
  have hcol (j : Fin n) :
      ∑ i : Fin n, (R i j) ^ 2 ≤ ∑ k : Fin (4 * n), (Rhat k j) ^ 2 := by
    let y : EuclideanSpace ℝ (Fin (4 * n)) :=
      WithLp.toLp 2 (fun k => Rhat k j)
    calc
      ∑ i : Fin n, (R i j) ^ 2 =
          ∑ i : Fin n, (b.repr y (Fin.castAdd (3 * n) i)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hRcoeff]
      _ ≤ ∑ t : Fin (n + 3 * n), (b.repr y t) ^ 2 := by
            rw [Fin.sum_univ_add]
            exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = ∑ t : Fin (n + 3 * n), ‖inner ℝ (b t) y‖ ^ 2 := by
            congr 1
            funext t
            rw [b.repr_apply_apply]
            simp
      _ = ‖y‖ ^ 2 := b.sum_sq_norm_inner_right y
      _ = ∑ k : Fin (4 * n), (Rhat k j) ^ 2 := by
            simpa [y] using EuclideanSpace.real_norm_sq_eq y
  refine ⟨L, R, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      decaying_matrix f n = Lhat * Rhat := hfactor
      _ = (L * Q) * Rhat := by rw [hLQ]
      _ = L * (Q * Rhat) := Matrix.mul_assoc L Q Rhat
      _ = L * R := by rfl
  · unfold lower_triangular Matrix.BlockTriangular
    intro i j hij
    change b.repr (v i) (Fin.castAdd (3 * n) j) = 0
    have h := InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular'
      hdim g (show Fin.castAdd (3 * n) i < Fin.castAdd (3 * n) j by
        exact hij)
    simpa [b, g] using h
  · intro p
    unfold real_row_p_trace
    congr 2
    funext i
    rw [hrow i]
  · unfold real_maximum_row_norm
    congr 2
    funext i
    rw [hrow i]
  · unfold real_column_norm
    apply csSup_le
    · exact ⟨Real.sqrt (∑ i : Fin n, (R i ⟨0, hn⟩) ^ 2), ⟨⟨0, hn⟩, rfl⟩⟩
    · intro x hx
      rcases hx with ⟨j, rfl⟩
      calc
        Real.sqrt (∑ i : Fin n, (R i j) ^ 2) ≤
            Real.sqrt (∑ k : Fin (4 * n), (Rhat k j) ^ 2) :=
          Real.sqrt_le_sqrt (hcol j)
        _ ≤ sSup (Set.range fun j : Fin n =>
            Real.sqrt (∑ k : Fin (4 * n), (Rhat k j) ^ 2)) :=
          le_csSup (Finite.bddAbove_range _) ⟨j, rfl⟩

@[blueprint "thm:bounded-lower-triangular-factorization"
  (statement := /-- For every $f : \mathbb N\to\mathbb R$ and every $n\in\mathbb N$ with $n>0$, there are matrices $L,R\in\mathbb R^{n\times n}$ such that $M_f=LR$ and $L$ is lower triangular. The same pair satisfies, for every $p\in\mathbb N$ with $p\geq2$,
  \[\operatorname{Tr}_p(L)\lVert R\rVert_{1\to2}\leq\mathcal B_p(f,n),\qquad
    \operatorname{Tr}_\infty(L)\lVert R\rVert_{1\to2}\leq\mathcal B_\infty(f,n).\] -/)
  (proof := /-- Choose $\widetilde L,\widetilde R$ from \cref{lem:fourier-complex-factorization}. By \cref{lem:realification-preserves-factorization-norms}, these factors yield a real rectangular factorization $M_f=\widehat L\widehat R$ whose finite and infinite row costs, as well as its column cost, agree with those of the complex factors. Apply \cref{lem:qr-lower-triangularization-preserves-norms} to obtain $M_f=LR$ with $L$ lower triangular, with the finite and infinite row costs of $L$ equal to those of $\widehat L$, and with $\lVert R\rVert_{1\to2}\leq\lVert\widehat R\rVert_{1\to2}$. By \cref{def:real-row-p-trace}, every finite row cost is nonnegative because it is a real power of a sum of nonnegative real powers of sums of squares. By \cref{def:real-maximum-row-norm}, the maximum row cost is nonnegative because, as $n>0$, its supremum is at least any one of its nonnegative square-root terms. Multiplication by either row cost therefore preserves the column-cost inequality. Substituting the cost equalities and applying the two estimates from \cref{lem:fourier-complex-factorization} proves the asserted finite and infinite inequalities. -/)
  (title := /-- A bounded lower-triangular factorization -/)
  (latexEnv := "theorem")]
theorem bounded_lower_triangular_factorization (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    ∃ out : toeplitz_factorization_output n,
      factorization_output_valid f n out ∧
      (∀ p : ℕ, 2 ≤ p →
        real_row_p_trace p out.left * real_column_norm out.right ≤ fourier_bound f n p) ∧
      real_maximum_row_norm out.left * real_column_norm out.right ≤
        operator_fourier_bound f n := by
  obtain ⟨A, B, hAB, hfinite, hinfinite⟩ :=
    fourier_complex_factorization f n hn
  obtain ⟨Lhat, Rhat, hreal, hpReal, hmaxReal, hcolReal⟩ :=
    realification_preserves_factorization_norms f n hn A B hAB
  obtain ⟨L, R, hfactor, htriangular, hpTriangular, hmaxTriangular,
      hcolTriangular⟩ :=
    qr_lower_triangularization_preserves_norms f n hn Lhat Rhat hreal
  have hp_nonneg (p : ℕ) : 0 ≤ real_row_p_trace p L := by
    exact Real.rpow_nonneg
      (Finset.sum_nonneg fun i _ =>
        Real.rpow_nonneg
          (Finset.sum_nonneg fun j _ => sq_nonneg (L i j)) _) _
  have hmax_nonneg : 0 ≤ real_maximum_row_norm L := by
    unfold real_maximum_row_norm
    let i : Fin n := ⟨0, hn⟩
    calc
      0 ≤ Real.sqrt (∑ j : Fin n, (L i j) ^ 2) := Real.sqrt_nonneg _
      _ ≤ sSup (Set.range fun i : Fin n =>
          Real.sqrt (∑ j : Fin n, (L i j) ^ 2)) :=
        le_csSup (Finite.bddAbove_range _) ⟨i, rfl⟩
  refine ⟨⟨L, R⟩, ⟨hfactor, htriangular⟩, ?_, ?_⟩
  · intro p hp
    calc
      real_row_p_trace p L * real_column_norm R ≤
          real_row_p_trace p L * real_column_norm Rhat :=
        mul_le_mul_of_nonneg_left hcolTriangular (hp_nonneg p)
      _ = complex_row_p_trace p A * complex_column_norm B := by
        rw [hpTriangular p, hpReal p, hcolReal]
      _ ≤ fourier_bound f n p := hfinite p hp
  · calc
      real_maximum_row_norm L * real_column_norm R ≤
          real_maximum_row_norm L * real_column_norm Rhat :=
        mul_le_mul_of_nonneg_left hcolTriangular hmax_nonneg
      _ = complex_maximum_row_norm A * complex_column_norm B := by
        rw [hmaxTriangular, hmaxReal, hcolReal]
      _ ≤ operator_fourier_bound f n := hinfinite

@[blueprint "lem:finite-factorization-norm-le-cost"
  (statement := /-- Let $n,p\in\mathbb N$, and let $M,L,R\in\mathbb R^{n\times n}$
  satisfy $M=LR$. Then
  \[\gamma_{(p)}(M)\leq\operatorname{Tr}_p(L)\lVert R\rVert_{1\to2}.\] -/)
  (proof := /-- The displayed cost belongs to the set over which the infimum in \cref{def:finite-p-factorization-norm} is taken, using the inner dimension $n$ and the given factors. Every element of that nonempty, nonnegative cost set is an upper bound for its infimum, which proves the claim. -/)
  (title := /-- An exhibited factorization bounds $\gamma_{(p)}$ -/)
  (latexEnv := "lemma")]
lemma finite_factorization_norm_le_cost {n p : ℕ}
    (M L R : Matrix (Fin n) (Fin n) ℝ) (hfactor : M = L * R) :
    finite_p_factorization_norm p M ≤ real_row_p_trace p L * real_column_norm R := by
  unfold finite_p_factorization_norm
  apply csInf_le
  · refine ⟨0, ?_⟩
    intro c hc
    rcases hc with ⟨d, B, C, hBC, rfl⟩
    apply mul_nonneg
    · exact Real.rpow_nonneg
        (Finset.sum_nonneg fun i _ =>
          Real.rpow_nonneg
            (Finset.sum_nonneg fun j _ => sq_nonneg (B i j)) _) _
    · apply Real.sSup_nonneg
      intro x hx
      rcases hx with ⟨j, rfl⟩
      exact Real.sqrt_nonneg _
  · exact ⟨n, L, R, hfactor, rfl⟩

@[blueprint "lem:infinite-factorization-norm-le-cost"
  (statement := /-- For every $n\in\mathbb N$ and all real matrices
  $M,L,R\in\mathbb R^{n\times n}$ satisfying $M=LR$, one has
  \[\gamma_{(\infty)}(M)\leq\operatorname{Tr}_\infty(L)\lVert R\rVert_{1\to2}.\] -/)
  (proof := /-- By \cref{def:real-maximum-row-norm,def:real-column-norm}, both
  norms are suprema of nonnegative square roots. If the relevant finite index
  type is empty, the supremum is zero; otherwise, comparison with any indexed
  entry shows that the supremum is nonnegative. Hence every cost in the set
  defining \cref{def:infinite-factorization-norm} is nonnegative, so that set
  is bounded below by zero. The hypothesis $M=LR$, with inner dimension $n$,
  places the displayed cost in the defining set. The infimum is therefore at
  most this cost. -/)
  (title := /-- An exhibited factorization bounds $\gamma_{(\infty)}$ -/)
  (latexEnv := "lemma")]
lemma infinite_factorization_norm_le_cost {n : ℕ}
    (M L R : Matrix (Fin n) (Fin n) ℝ) (hfactor : M = L * R) :
    infinite_factorization_norm M ≤ real_maximum_row_norm L * real_column_norm R := by
  have hrow : ∀ {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ),
      0 ≤ real_maximum_row_norm A := by
    intro m d A
    cases m with
    | zero => simp [real_maximum_row_norm]
    | succ m =>
      unfold real_maximum_row_norm
      calc
        0 ≤ Real.sqrt (∑ j : Fin d, (A 0 j) ^ 2) := Real.sqrt_nonneg _
        _ ≤ sSup (Set.range fun i : Fin (Nat.succ m) =>
            Real.sqrt (∑ j : Fin d, (A i j) ^ 2)) :=
          le_csSup (Finite.bddAbove_range _) ⟨0, rfl⟩
  have hcol : ∀ {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ),
      0 ≤ real_column_norm A := by
    intro m d A
    cases d with
    | zero => simp [real_column_norm]
    | succ d =>
      unfold real_column_norm
      calc
        0 ≤ Real.sqrt (∑ i : Fin m, (A i 0) ^ 2) := Real.sqrt_nonneg _
        _ ≤ sSup (Set.range fun j : Fin (Nat.succ d) =>
            Real.sqrt (∑ i : Fin m, (A i j) ^ 2)) :=
          le_csSup (Finite.bddAbove_range _) ⟨0, rfl⟩
  unfold infinite_factorization_norm
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro c ⟨d, B, C, hBC, rfl⟩
    exact mul_nonneg (hrow B) (hcol C)
  · exact ⟨n, L, R, hfactor, rfl⟩

@[blueprint "def:deterministic-factorization-construction"
  (statement := /-- A deterministic factorization construction consists of a Toeplitz factorization algorithm $A$, a positive constant $C$, and an exponent $q$.  For every size $n$, the structural operation count of $A$ is at most $C(n+1)^q$.  For every $f:\mathbb N\to\mathbb R$ and every positive $n$, the output of $A$ is a valid lower-triangular factorization of $M_f$ satisfying every finite-$p$ Fourier bound and the maximum-row Fourier bound. -/)
  (title := /-- Certified deterministic Fourier--Gram--Schmidt construction -/)
  (latexEnv := "definition")]
structure deterministic_factorization_construction where
  algorithm : toeplitz_factorization_algorithm
  costConstant : ℕ
  costExponent : ℕ
  costConstantPositive : 0 < costConstant
  polynomialCost : ∀ n : ℕ,
    toeplitz_factorization_algorithm_operation_count algorithm n ≤
      costConstant * (n + 1) ^ costExponent
  correct : ∀ (f : ℕ → ℝ) (n : ℕ), 0 < n →
    factorization_output_valid f n
        (toeplitz_factorization_algorithm_run algorithm f n) ∧
      (∀ p : ℕ, 2 ≤ p →
        real_row_p_trace p
              (toeplitz_factorization_algorithm_run algorithm f n).left *
            real_column_norm
              (toeplitz_factorization_algorithm_run algorithm f n).right ≤
          fourier_bound f n p) ∧
      real_maximum_row_norm
            (toeplitz_factorization_algorithm_run algorithm f n).left *
          real_column_norm
            (toeplitz_factorization_algorithm_run algorithm f n).right ≤
        operator_fourier_bound f n

@[blueprint "lem:deterministic-factorization-construction-exists"
  (statement := /-- There exists a certified deterministic Fourier--Gram--Schmidt factorization construction: for every $n\in\mathbb N$ it specifies a finite real-oracle arithmetic program whose evaluation gives the required lower-triangular factorization and all Fourier cost bounds, and there exist constants $C,q\in\mathbb N$, with $C>0$, such that the program's structural operation count is at most $C(n+1)^q$ for every $n$. -/)
  (proof := /-- For $n=0$, take the empty instruction list and the unique empty output matrices.  Fix $n>0$.  Construct the instruction list by a predetermined sequence of bounded loops.  The first block stores $f(0),\ldots,f(n-1)$.  For each $k<2n$, it evaluates $c_k=\cos(\pi k/n)$ and $s_k=\sin(\pi k/n)$, and repeated complex multiplication then evaluates
  \[
    z_k=\sum_{r<n}f(r)(c_k+\iota s_k)^r.
  \]
  Put $\rho_k=\sqrt{(\Re z_k)^2+(\Im z_k)^2}$ and $a_k=\sqrt{\rho_k}$.  A sign branch applied to $-a_k$ sets $b_k=0$ when $a_k=0$ and sets $b_k=z_k/a_k$ otherwise.  Since $a_k\geq0$, these are exactly the two cases, and in both cases $a_kb_k=z_k$ and $|a_k|^2=|b_k|^2=|z_k|$.  The next block evaluates
  \[
    \widetilde L_{ik}=a_k\omega_n^{(2n-i)k},
    \qquad
    \widetilde R_{kj}=\frac{b_k\omega_n^{jk}}{2n}
  \]
  for $i,j<n$ and $k<2n$.  Induction on each multiplication loop proves that evaluation of the emitted registers has precisely these values.  The identities in \cref{lem:fourier-complex-factorization-root,lem:fourier-complex-factorization-inversion} then give $M_f^{\mathbb C}=\widetilde L\widetilde R$ and the asserted finite and maximum-row Fourier estimates.

  Emit next the real and imaginary parts in the fixed order
  \[
    \widehat L=(\Re\widetilde L\mid-\Im\widetilde L),
    \qquad
    \widehat R=\binom{\Re\widetilde R}{\Im\widetilde R}.
  \]
  The entrywise identities of \cref{lem:realification-preserves-factorization-norms} show that evaluation of this block preserves the factorization, every finite row cost, the maximum-row cost, and the column cost.

  The final arithmetic block performs a deterministic Gram--Schmidt procedure.  Process the rows $v_0,\ldots,v_{n-1}$ of $\widehat L$ in order.  At stage $j$, subtract their projections onto $q_0,\ldots,q_{j-1}$.  If the residual has positive squared norm, normalize it; otherwise scan the standard coordinate vectors in increasing order and normalize the first vector whose residual has positive squared norm.  Continue the same scan after stage $n-1$ until $q_0,\ldots,q_{4n-1}$ is an orthonormal basis of $\mathbb R^{4n}$.  Such a coordinate vector exists whenever fewer than $4n$ orthonormal vectors have been stored, for otherwise their proper span would contain every standard basis vector and hence all of $\mathbb R^{4n}$.  Every test is a sign branch on the negative squared norm, so it selects the zero case exactly; every normalization uses only square root and division.  Induction on the stages proves orthonormality and proves that $v_i$ lies in the span of $q_0,\ldots,q_i$.  Consequently the registers
  \[
    L_{ij}=\langle q_j,v_i\rangle,
    \qquad
    R_{ij}=\sum_{t<4n}(q_i)_t\widehat R_{tj}
  \]
  satisfy $L_{ij}=0$ for $i<j$, $\widehat L=LQ$, and $R=Q^{\mathsf T}\widehat R$.  Parseval's identity gives $M_f=LR$ and preserves the row and column costs.  This proves the field called \emph{correct} in \cref{def:deterministic-factorization-construction} directly from evaluation of the constructed program, without identifying its output with an existentially chosen factorization.

  It remains to verify efficiency.  The Fourier, realification, Gram--Schmidt, and output blocks form a fixed finite collection of bounded loop schemes.  Every loop bound is at most a fixed linear function of $n$, and each loop body emits only a fixed finite number of real-oracle arithmetic instructions.  Let $q$ be at least the maximum total nesting depth of these loop schemes, enlarged if necessary to account for the linear recurrences used for complex powers and inner products.  Expanding the structural count in \cref{def:factorization-arithmetic-program-operation-count} then yields a constant $C_0\in\mathbb N$ such that the operation count is at most $C_0(n+1)^q$ for every positive $n$.  Enlarging $C_0$ to a positive constant $C$ that also covers the empty program at $n=0$ proves the field called \emph{polynomialCost}.  The size-indexed program family together with $C$ and $q$ is the required construction. -/)
  (title := /-- Existence of the certified deterministic construction -/)
  (latexEnv := "lemma")]
lemma deterministic_factorization_construction_exists :
    Nonempty deterministic_factorization_construction := by
  classical
  obtain ⟨sumE, hsum0, hsumS⟩ :
      ∃ sumE : (ℕ → real_arithmetic_expression) → ℕ → real_arithmetic_expression,
        (∀ F, sumE F 0 = real_arithmetic_expression.integer 0) ∧
        (∀ F t, sumE F (t + 1) =
          real_arithmetic_expression.add (sumE F t) (F t)) :=
    ⟨fun F t =>
      Nat.rec (motive := fun _ => real_arithmetic_expression)
        (real_arithmetic_expression.integer 0)
        (fun k acc => real_arithmetic_expression.add acc (F k)) t,
      fun _ => rfl, fun _ _ => rfl⟩
  have hsumEval : ∀ (f : ℕ → ℝ) (w : List ℝ) (F : ℕ → real_arithmetic_expression)
      (val : ℕ → ℝ) (t : ℕ),
      (∀ k, k < t → real_arithmetic_expression_evaluate f w (F k) = val k) →
      real_arithmetic_expression_evaluate f w (sumE F t) =
        ∑ k ∈ Finset.range t, val k := by
    intro f w F val t
    induction t with
    | zero =>
      intro _
      rw [hsum0]
      simp [real_arithmetic_expression_evaluate]
    | succ t ih =>
      intro hF
      rw [hsumS, Finset.sum_range_succ, ← ih (fun k hk => hF k (by omega)),
        ← hF t (by omega)]
      simp [real_arithmetic_expression_evaluate]
  have hsumCount : ∀ (F : ℕ → real_arithmetic_expression) (c : ℕ),
      (∀ k, real_arithmetic_expression_operation_count (F k) ≤ c) →
      ∀ t, real_arithmetic_expression_operation_count (sumE F t) ≤ t * (1 + c) := by
    intro F c hF t
    induction t with
    | zero => rw [hsum0]; simp [real_arithmetic_expression_operation_count]
    | succ t ih =>
      rw [hsumS]
      have h1 := hF t
      have h2 : (t + 1) * (1 + c) = t * (1 + c) + (1 + c) := by ring
      simp only [real_arithmetic_expression_operation_count]
      linarith
  obtain ⟨cx, hcx⟩ : ∃ cx : ℕ → ℕ → real_arithmetic_expression, ∀ n m,
      cx n m = .cos (.div (.mul (.integer (m : ℤ)) .pi) (.integer (n : ℤ))) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨sx, hsx⟩ : ∃ sx : ℕ → ℕ → real_arithmetic_expression, ∀ n m,
      sx n m = .sin (.div (.mul (.integer (m : ℤ)) .pi) (.integer (n : ℤ))) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨px, hpx⟩ : ∃ px : ℕ → ℕ → real_arithmetic_expression, ∀ n k,
      px n k = sumE (fun r => .mul (.weight r) (cx n (r * k))) n :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨qx, hqx⟩ : ∃ qx : ℕ → ℕ → real_arithmetic_expression, ∀ n k,
      qx n k = sumE (fun r => .mul (.weight r) (sx n (r * k))) n :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨ax, hax⟩ : ∃ ax : ℕ → ℕ → real_arithmetic_expression, ∀ n k,
      ax n k = .sqrt (.sqrt (.add (.mul (px n k) (px n k)) (.mul (qx n k) (qx n k)))) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨gx, hgx⟩ : ∃ gx : ℕ → ℕ → real_arithmetic_expression, ∀ n k,
      gx n k = .div (.integer 1) (.mul (.integer ((2 * n : ℕ) : ℤ)) (ax n k)) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨vrx, hvrx⟩ : ∃ vrx : ℕ → ℕ → ℕ → real_arithmetic_expression, ∀ n a k,
      vrx n a k =
        if a < n then .mul (ax n k) (cx n (a * k))
        else .mul (gx n k) (.add (.mul (px n k) (cx n ((a - n) * k)))
          (.neg (.mul (qx n k) (sx n ((a - n) * k))))) :=
    ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨vix, hvix⟩ : ∃ vix : ℕ → ℕ → ℕ → real_arithmetic_expression, ∀ n a k,
      vix n a k =
        if a < n then .mul (ax n k) (sx n (a * k))
        else .mul (gx n k) (.add (.mul (px n k) (sx n ((a - n) * k)))
          (.mul (qx n k) (cx n ((a - n) * k)))) :=
    ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨kx, hkx⟩ : ∃ kx : ℕ → ℕ → ℕ → real_arithmetic_expression, ∀ n a b,
      kx n a b = sumE (fun k => .add (.mul (vrx n a k) (vrx n b k))
        (.mul (vix n a k) (vix n b k))) (2 * n) :=
    ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨lx, hlx⟩ : ∃ lx : ℕ → ℕ → ℕ → real_arithmetic_expression, ∀ n a b,
      lx n a b =
        if a < b then .integer 0
        else if a = b then
          .sqrt (.add (.register (a * (2 * n) + a))
            (.neg (sumE (fun k => .mul (.register (2 * n * (2 * n) + a * (2 * n) + k))
              (.register (2 * n * (2 * n) + a * (2 * n) + k))) a)))
        else
          .div (.add (.register (a * (2 * n) + b))
            (.neg (sumE (fun k => .mul (.register (2 * n * (2 * n) + a * (2 * n) + k))
              (.register (2 * n * (2 * n) + b * (2 * n) + k))) b)))
            (.register (2 * n * (2 * n) + b * (2 * n) + b)) :=
    ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨ex, hex⟩ : ∃ ex : ℕ → ℕ → real_arithmetic_expression, ∀ n m,
      ex n m =
        if m < 2 * n * (2 * n) then kx n (m / (2 * n)) (m % (2 * n))
        else lx n ((m - 2 * n * (2 * n)) / (2 * n)) ((m - 2 * n * (2 * n)) % (2 * n)) :=
    ⟨_, fun _ _ => rfl⟩
  have hccount : ∀ n m, real_arithmetic_expression_operation_count (cx n m) = 3 := by
    intro n m
    rw [hcx]
    simp [real_arithmetic_expression_operation_count]
  have hscount : ∀ n m, real_arithmetic_expression_operation_count (sx n m) = 3 := by
    intro n m
    rw [hsx]
    simp [real_arithmetic_expression_operation_count]
  have hpcount : ∀ n k, real_arithmetic_expression_operation_count (px n k) ≤ 6 * n := by
    intro n k
    rw [hpx]
    have h := hsumCount (fun r => .mul (.weight r) (cx n (r * k))) 5 ?_ n
    · calc real_arithmetic_expression_operation_count
            (sumE (fun r => .mul (.weight r) (cx n (r * k))) n) ≤ n * (1 + 5) := h
        _ = 6 * n := by ring
    · intro r
      simp only [real_arithmetic_expression_operation_count, hccount]
      omega
  have hqcount : ∀ n k, real_arithmetic_expression_operation_count (qx n k) ≤ 6 * n := by
    intro n k
    rw [hqx]
    have h := hsumCount (fun r => .mul (.weight r) (sx n (r * k))) 5 ?_ n
    · calc real_arithmetic_expression_operation_count
            (sumE (fun r => .mul (.weight r) (sx n (r * k))) n) ≤ n * (1 + 5) := h
        _ = 6 * n := by ring
    · intro r
      simp only [real_arithmetic_expression_operation_count, hscount]
      omega
  have hacount : ∀ n k, real_arithmetic_expression_operation_count (ax n k) ≤ 24 * n + 5 := by
    intro n k
    rw [hax]
    simp only [real_arithmetic_expression_operation_count]
    have h1 := hpcount n k
    have h2 := hqcount n k
    omega
  have hgcount : ∀ n k, real_arithmetic_expression_operation_count (gx n k) ≤ 24 * n + 7 := by
    intro n k
    rw [hgx]
    simp only [real_arithmetic_expression_operation_count]
    have h1 := hacount n k
    omega
  have hvrcount : ∀ n a k,
      real_arithmetic_expression_operation_count (vrx n a k) ≤ 72 * n + 34 := by
    intro n a k
    rw [hvrx]
    split
    · simp only [real_arithmetic_expression_operation_count]
      have h1 := hacount n k
      have h2 := hccount n (a * k)
      omega
    · simp only [real_arithmetic_expression_operation_count]
      have h1 := hgcount n k
      have h2 := hccount n ((a - n) * k)
      have h3 := hscount n ((a - n) * k)
      have h4 := hpcount n k
      have h5 := hqcount n k
      omega
  have hvicount : ∀ n a k,
      real_arithmetic_expression_operation_count (vix n a k) ≤ 72 * n + 34 := by
    intro n a k
    rw [hvix]
    split
    · simp only [real_arithmetic_expression_operation_count]
      have h1 := hacount n k
      have h2 := hscount n (a * k)
      omega
    · simp only [real_arithmetic_expression_operation_count]
      have h1 := hgcount n k
      have h2 := hccount n ((a - n) * k)
      have h3 := hscount n ((a - n) * k)
      have h4 := hpcount n k
      have h5 := hqcount n k
      omega
  have hkcount : ∀ n a b, real_arithmetic_expression_operation_count (kx n a b) ≤
      2 * n * (288 * n + 140) := by
    intro n a b
    rw [hkx]
    have h := hsumCount (fun k => (.add (.mul (vrx n a k) (vrx n b k))
        (.mul (vix n a k) (vix n b k)) : real_arithmetic_expression))
      (288 * n + 139) ?_ (2 * n)
    · calc real_arithmetic_expression_operation_count
            (sumE (fun k => (.add (.mul (vrx n a k) (vrx n b k))
              (.mul (vix n a k) (vix n b k)) : real_arithmetic_expression)) (2 * n))
            ≤ 2 * n * (1 + (288 * n + 139)) := h
        _ = 2 * n * (288 * n + 140) := by ring
    · intro k
      simp only [real_arithmetic_expression_operation_count]
      have h1 := hvrcount n a k
      have h2 := hvrcount n b k
      have h3 := hvicount n a k
      have h4 := hvicount n b k
      omega
  have hlcount : ∀ n a b, a ≤ 2 * n → b ≤ 2 * n →
      real_arithmetic_expression_operation_count (lx n a b) ≤ 4 * n + 3 := by
    intro n a b ha hb
    rw [hlx]
    have hs : ∀ (c d t : ℕ), t ≤ 2 * n →
        real_arithmetic_expression_operation_count
          (sumE (fun k => (.mul (.register (2 * n * (2 * n) + c * (2 * n) + k))
            (.register (2 * n * (2 * n) + d * (2 * n) + k)) : real_arithmetic_expression)) t)
          ≤ 4 * n := by
      intro c d t ht
      have h := hsumCount (fun k => (.mul (.register (2 * n * (2 * n) + c * (2 * n) + k))
          (.register (2 * n * (2 * n) + d * (2 * n) + k)) : real_arithmetic_expression)) 1 ?_ t
      · calc real_arithmetic_expression_operation_count
              (sumE (fun k => (.mul (.register (2 * n * (2 * n) + c * (2 * n) + k))
                (.register (2 * n * (2 * n) + d * (2 * n) + k)) :
                  real_arithmetic_expression)) t) ≤ t * (1 + 1) := h
          _ ≤ 2 * n * 2 := by omega
          _ = 4 * n := by ring
      · intro k
        simp [real_arithmetic_expression_operation_count]
    split
    · simp [real_arithmetic_expression_operation_count]
    · split
      · simp only [real_arithmetic_expression_operation_count]
        have h := hs a a a ha
        omega
      · simp only [real_arithmetic_expression_operation_count]
        have h := hs a b b hb
        omega
  have hexcount : ∀ n m, m < 2 * (2 * n * (2 * n)) →
      real_arithmetic_expression_operation_count (ex n m) ≤ 1000 * (n + 1) ^ 2 := by
    intro n m hm
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at hm
      · exact h
    have hN : 0 < 2 * n := by omega
    rw [hex]
    split
    · have h := hkcount n (m / (2 * n)) (m % (2 * n))
      have hsq : 1000 * (n + 1) ^ 2 = 1000 * n * n + 2000 * n + 1000 := by ring
      have hle : 2 * n * (288 * n + 140) ≤ 1000 * n * n + 2000 * n + 1000 := by
        nlinarith [Nat.zero_le n]
      omega
    · have ha : (m - 2 * n * (2 * n)) / (2 * n) ≤ 2 * n := by
        apply Nat.le_of_lt_succ
        have : (m - 2 * n * (2 * n)) < 2 * n * (2 * n) := by omega
        calc (m - 2 * n * (2 * n)) / (2 * n) < 2 * n :=
              Nat.div_lt_of_lt_mul (by omega)
          _ < 2 * n + 1 := by omega
      have hb : (m - 2 * n * (2 * n)) % (2 * n) ≤ 2 * n :=
        le_of_lt (Nat.mod_lt _ hN)
      have h := hlcount n _ _ ha hb
      have hsq : 1000 * (n + 1) ^ 2 = 1000 * n * n + 2000 * n + 1000 := by ring
      omega
  have hchol : ∀ (N : ℕ) (K L : ℕ → ℕ → ℝ),
      (∀ a b, K a b = K b a) →
      (∀ x : ℕ → ℝ,
        0 ≤ ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, x a * K a b * x b) →
      (∀ i t, i < t → t < N → L i t = 0) →
      (∀ i, i < N → L i i = Real.sqrt (K i i - ∑ k ∈ Finset.range i, L i k * L i k)) →
      (∀ i t, t < i → i < N →
        L i t = (K i t - ∑ k ∈ Finset.range t, L i k * L t k) / L t t) →
      ∀ a b, a < N → b < N → K a b = ∑ t ∈ Finset.range N, L a t * L b t := by
    intro N K L hsym hpsd hup hdg hoff
    classical
    obtain ⟨Res, hRes⟩ : ∃ Res : ℕ → ℕ → ℕ → ℝ,
        ∀ j a b, Res j a b = K a b - ∑ t ∈ Finset.range j, L a t * L b t :=
      ⟨_, fun _ _ _ => rfl⟩
    have hRs : ∀ j a b, Res j a b = Res j b a := by
      intro j a b
      rw [hRes, hRes, hsym a b]
      congr 1
      exact Finset.sum_congr rfl fun t _ => mul_comm _ _
    have hstep : ∀ j a b, Res (j + 1) a b = Res j a b - L a j * L b j := by
      intro j a b
      rw [hRes, hRes, Finset.sum_range_succ]
      ring
    have main : ∀ j, j ≤ N →
        (∀ a b, a < N → b < N → (a < j ∨ b < j) → Res j a b = 0) ∧
        (∀ x : ℕ → ℝ, 0 ≤ ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
          x a * Res j a b * x b) := by
      intro j
      induction j with
      | zero =>
        intro _
        refine ⟨?_, ?_⟩
        · intro a b _ _ h
          omega
        · intro x
          have : ∀ a b, Res 0 a b = K a b := by
            intro a b
            rw [hRes]
            simp
          simp only [this]
          exact hpsd x
      | succ j ih =>
        intro hjN
        obtain ⟨hz, hp⟩ := ih (by omega)
        have hjltN : j < N := by omega
        have hd0 : 0 ≤ Res j j j := by
          have := hp (fun a => if a = j then 1 else 0)
          simpa [Finset.mem_range, hjltN] using this
        have hLjj : L j j = Real.sqrt (Res j j j) := by
          rw [hdg j hjltN, hRes]
        have htwo : ∀ (u v : ℝ) (a b : ℕ), a < N → b < N →
            0 ≤ u * u * Res j a a + u * v * Res j a b + v * u * Res j b a
              + v * v * Res j b b := by
          intro u v a b ha hb
          have h := hp (fun t => (if t = a then u else 0) + (if t = b then v else 0))
          simp only [add_mul, mul_add, ite_mul, mul_ite, zero_mul, mul_zero,
            Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range, ha, hb,
            if_true] at h
          linarith [h]
        have hshift : ∀ (x : ℕ → ℝ) (s : ℝ),
            0 ≤ (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, x a * Res j a b * x b)
              + s * (∑ a ∈ Finset.range N, x a * Res j a j)
              + s * (∑ b ∈ Finset.range N, Res j j b * x b)
              + s * s * Res j j j := by
          intro x s
          have h := hp (fun t => x t + (if t = j then s else 0))
          simp only [add_mul, mul_add, ite_mul, mul_ite, zero_mul, mul_zero,
            Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range, hjltN,
            if_true] at h
          have e3 : ∀ p : ℕ, (∑ q ∈ Finset.range N,
              if p = j then s * Res j p q * x q else 0)
              = if p = j then s * ∑ q ∈ Finset.range N, Res j j q * x q else 0 := by
            intro p
            by_cases hpj : p = j
            · subst hpj
              simp only [if_true, Finset.mul_sum]
              exact Finset.sum_congr rfl fun q _ => by ring
            · simp [hpj]
          rw [Finset.sum_congr rfl fun p _ => e3 p,
            Finset.sum_ite_eq' (Finset.range N) j] at h
          simp only [Finset.mem_range, hjltN, if_true] at h
          have e1 : ∑ a ∈ Finset.range N, x a * Res j a j * s
              = s * ∑ a ∈ Finset.range N, x a * Res j a j := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun p _ => by ring
          linarith [h]
        have hzerorow : Res j j j = 0 → ∀ a, a < N → Res j a j = 0 := by
          intro hdz a ha
          have hall : ∀ s : ℝ, 0 ≤ Res j a a + 2 * s * Res j a j := by
            intro s
            have h := htwo 1 s a j ha hjltN
            rw [← hRs j a j, hdz] at h
            linarith [h]
          by_contra hc
          have h2 := hall (-(Res j a a + 1) / (2 * Res j a j))
          have h3 : 2 * (-(Res j a a + 1) / (2 * Res j a j)) * Res j a j
              = -(Res j a a + 1) := by
            field_simp
          rw [h3] at h2
          linarith
        have hLcol : ∀ a, a < N → L a j * L j j = Res j a j := by
          intro a ha
          rcases lt_trichotomy a j with hlt | heq | hgt
          · rw [hup a j hlt hjltN, zero_mul, hz a j ha hjltN (Or.inl hlt)]
          · subst heq
            rw [hLjj, Real.mul_self_sqrt hd0]
          · have hL : L a j = Res j a j / L j j := by
              rw [hoff a j hgt ha, hRes]
            rw [hL]
            by_cases hz0 : L j j = 0
            · rw [hz0, div_zero, zero_mul]
              have hdz : Res j j j = 0 := by
                rw [hLjj] at hz0
                rcases Real.sqrt_eq_zero'.1 hz0 with h
                linarith [hd0]
              exact (hzerorow hdz a ha).symm
            · field_simp
        refine ⟨?_, ?_⟩
        · have key : ∀ p q : ℕ, p < N → q < N → p ≤ j → Res (j + 1) p q = 0 := by
            intro p q hpn hqn hpj
            rw [hstep]
            rcases lt_or_eq_of_le hpj with hlt | heq
            · rw [hup p j hlt hjltN, hz p q hpn hqn (Or.inl hlt)]
              ring
            · subst heq
              have h1 : L q p * L p p = Res p q p := hLcol q hqn
              rw [hRs p p q, ← h1]
              ring
          intro a b ha hb hab
          rcases hab with h | h
          · exact key a b ha hb (by omega)
          · rw [hRs (j + 1) a b]
            exact key b a hb ha (by omega)
        · intro x
          rcases eq_or_lt_of_le hd0 with hdz | hdpos
          · have hcolzero : ∀ a, a < N → L a j = 0 := by
              intro a ha
              rcases lt_trichotomy a j with hlt | heq | hgt
              · exact hup a j hlt hjltN
              · subst heq
                rw [hLjj, ← hdz, Real.sqrt_zero]
              · rw [hoff a j hgt ha, ← hRes j a j, hzerorow hdz.symm a ha, zero_div]
            have := hp x
            have heq : ∀ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
                x a * Res (j + 1) a b * x b
                = ∑ b ∈ Finset.range N, x a * Res j a b * x b := by
              intro a ha
              refine Finset.sum_congr rfl fun b hb => ?_
              rw [hstep, hcolzero a (Finset.mem_range.1 ha)]
              ring
            rw [Finset.sum_congr rfl heq]
            exact this
          · have hsq : Real.sqrt (Res j j j) * Real.sqrt (Res j j j) = Res j j j :=
              Real.mul_self_sqrt hd0
            have hsne : Real.sqrt (Res j j j) ≠ 0 := by
              have := Real.sqrt_pos.2 hdpos
              linarith
            have hcolform : ∀ a, a < N → L a j = Res j a j / Real.sqrt (Res j j j) := by
              intro a ha
              have h := hLcol a ha
              rw [hLjj] at h
              rw [eq_div_iff hsne]
              exact h
            have hfac : ∀ (u v : ℕ → ℝ) (r : ℝ),
                (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, u a * v b * r)
                  = (∑ a ∈ Finset.range N, u a) * (∑ b ∈ Finset.range N, v b) * r := by
              intro u v r
              rw [Finset.sum_mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.sum_mul]
            have hexp : ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
                x a * Res (j + 1) a b * x b
                = (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, x a * Res j a b * x b)
                  - (∑ a ∈ Finset.range N, x a * Res j a j)
                    * (∑ b ∈ Finset.range N, Res j j b * x b) * (Res j j j)⁻¹ := by
              have hinner : ∀ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
                  x a * Res (j + 1) a b * x b
                  = (∑ b ∈ Finset.range N, x a * Res j a b * x b)
                    - ∑ b ∈ Finset.range N,
                        (x a * Res j a j) * (Res j j b * x b) * (Res j j j)⁻¹ := by
                intro a ha
                rw [← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun b hb => ?_
                rw [hstep, hcolform a (Finset.mem_range.1 ha),
                  hcolform b (Finset.mem_range.1 hb), hRs j b j]
                have hdd : (Res j a j / Real.sqrt (Res j j j))
                    * (Res j j b / Real.sqrt (Res j j j))
                    = Res j a j * Res j j b * (Res j j j)⁻¹ := by
                  rw [div_mul_div_comm, hsq]
                  ring
                rw [hdd]
                ring
              rw [Finset.sum_congr rfl hinner, Finset.sum_sub_distrib,
                hfac (fun a => x a * Res j a j) (fun b => Res j j b * x b)
                  (Res j j j)⁻¹]
            rw [hexp]
            have hcc : (∑ b ∈ Finset.range N, Res j j b * x b)
                = ∑ a ∈ Finset.range N, x a * Res j a j := by
              refine Finset.sum_congr rfl fun b hb => ?_
              rw [hRs j j b]
              ring
            rw [hcc]
            have h := hshift x
              (-((∑ a ∈ Finset.range N, x a * Res j a j) / Res j j j))
            rw [hcc] at h
            have hdne : Res j j j ≠ 0 := ne_of_gt hdpos
            have hid : (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
                  x a * Res j a b * x b)
                + -((∑ a ∈ Finset.range N, x a * Res j a j) / Res j j j)
                    * (∑ a ∈ Finset.range N, x a * Res j a j)
                + -((∑ a ∈ Finset.range N, x a * Res j a j) / Res j j j)
                    * (∑ a ∈ Finset.range N, x a * Res j a j)
                + -((∑ a ∈ Finset.range N, x a * Res j a j) / Res j j j)
                    * -((∑ a ∈ Finset.range N, x a * Res j a j) / Res j j j)
                    * Res j j j
                = (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, x a * Res j a b * x b)
                  - (∑ a ∈ Finset.range N, x a * Res j a j)
                    * (∑ a ∈ Finset.range N, x a * Res j a j) * (Res j j j)⁻¹ := by
              field_simp
              ring
            rw [hid] at h
            exact h
    have hfin := (main N le_rfl).1
    intro a b ha hb
    have h := hfin a b ha hb (Or.inl ha)
    rw [hRes] at h
    linarith
  obtain ⟨alg, halg⟩ : ∃ alg : toeplitz_factorization_algorithm, ∀ n : ℕ,
      alg.program n = ⟨(List.range (2 * (2 * n * (2 * n)))).map (ex n),
        fun i j => 2 * n * (2 * n) + i.1 * (2 * n) + j.1,
        fun i j => 2 * n * (2 * n) + (n + j.1) * (2 * n) + i.1⟩ :=
    ⟨⟨fun n => ⟨(List.range (2 * (2 * n * (2 * n)))).map (ex n),
      fun i j => 2 * n * (2 * n) + i.1 * (2 * n) + j.1,
      fun i j => 2 * n * (2 * n) + (n + j.1) * (2 * n) + i.1⟩⟩, fun _ => rfl⟩
  refine ⟨⟨alg, 8000, 4, by norm_num, ?_, ?_⟩⟩
  · intro n
    have hcount : toeplitz_factorization_algorithm_operation_count alg n =
        (((List.range (2 * (2 * n * (2 * n)))).map (ex n)).map
          real_arithmetic_expression_operation_count).sum := by
      unfold toeplitz_factorization_algorithm_operation_count
        factorization_arithmetic_program_operation_count
      rw [halg n]
    rw [hcount, List.map_map]
    have hb : ∀ x ∈ (List.range (2 * (2 * n * (2 * n)))).map
        (real_arithmetic_expression_operation_count ∘ ex n), x ≤ 1000 * (n + 1) ^ 2 := by
      intro x hx
      simp only [List.mem_map, List.mem_range, Function.comp_apply] at hx
      obtain ⟨m, hm, rfl⟩ := hx
      exact hexcount n m hm
    have h := List.sum_le_card_nsmul _ _ hb
    simp only [List.length_map, List.length_range, smul_eq_mul] at h
    refine le_trans h ?_
    have hsq : n * n ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
    calc 2 * (2 * n * (2 * n)) * (1000 * (n + 1) ^ 2)
        = 8000 * (n * n) * (n + 1) ^ 2 := by ring
      _ ≤ 8000 * ((n + 1) * (n + 1)) * (n + 1) ^ 2 := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsq)
      _ = 8000 * (n + 1) ^ 4 := by ring
  · intro f n hn
    obtain ⟨W, hWdef⟩ : ∃ W : ℕ → List ℝ, ∀ t, W t =
        ((List.range t).map (ex n)).foldl
          (fun values instruction =>
            values ++ [real_arithmetic_expression_evaluate f values instruction]) [] :=
      ⟨_, fun _ => rfl⟩
    have hW0 : W 0 = [] := by rw [hWdef]; simp
    have hWS : ∀ t, W (t + 1) =
        W t ++ [real_arithmetic_expression_evaluate f (W t) (ex n t)] := by
      intro t
      rw [hWdef, hWdef, List.range_succ, List.map_append, List.foldl_append]
      simp
    have hWlen : ∀ t, (W t).length = t := by
      intro t
      induction t with
      | zero => rw [hW0]; simp
      | succ t ih => rw [hWS]; simp [ih]
    have hWget : ∀ t u, u < t → (W t).getD u 0 =
        real_arithmetic_expression_evaluate f (W u) (ex n u) := by
      intro t
      induction t with
      | zero => intro u hu; omega
      | succ t ih =>
        intro u hu
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with h | h
        · rw [hWS]
          rw [show (W t ++ [real_arithmetic_expression_evaluate f (W t) (ex n t)]).getD u 0
              = (W t).getD u 0 by
            simp [List.getD_eq_getElem?_getD,
              List.getElem?_append_left (by rw [hWlen]; exact h)]]
          exact ih u h
        · subst h
          rw [hWS]
          rw [show (W u ++ [real_arithmetic_expression_evaluate f (W u) (ex n u)]).getD u 0
              = real_arithmetic_expression_evaluate f (W u) (ex n u) by
            have hu : (W u).length = u := hWlen u
            simp [List.getD_eq_getElem?_getD,
              List.getElem?_append_right (by omega : (W u).length ≤ u), hu]]
    have hWstab : ∀ u t, u < t → t ≤ 2 * (2 * n * (2 * n)) →
        (W t).getD u 0 = (W (2 * (2 * n * (2 * n)))).getD u 0 := by
      intro u t h1 h2
      rw [hWget t u h1, hWget (2 * (2 * n * (2 * n))) u (by omega)]
    have hidx : ∀ a b k : ℕ, k < 2 * n → b < a → b * (2 * n) + k < a * (2 * n) + b := by
      intro a b k hk hba
      calc b * (2 * n) + k < b * (2 * n) + 2 * n := by omega
        _ = (b + 1) * (2 * n) := by ring
        _ ≤ a * (2 * n) := Nat.mul_le_mul_right _ (by omega)
        _ ≤ a * (2 * n) + b := by omega
    have hidxT : ∀ a b : ℕ, a < 2 * n → b < 2 * n → a * (2 * n) + b < 2 * n * (2 * n) := by
      intro a b ha hb
      calc a * (2 * n) + b < a * (2 * n) + 2 * n := by omega
        _ = (a + 1) * (2 * n) := by ring
        _ ≤ 2 * n * (2 * n) := Nat.mul_le_mul_right _ (by omega)
    have hdivmod : ∀ a b : ℕ, b < 2 * n →
        (a * (2 * n) + b) / (2 * n) = a ∧ (a * (2 * n) + b) % (2 * n) = b := by
      intro a b hb
      have hN : 0 < 2 * n := by omega
      have hcomm : a * (2 * n) + b = b + a * (2 * n) := by ring
      constructor
      · rw [hcomm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hb]
        omega
      · rw [hcomm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
    obtain ⟨Cv, hCv⟩ : ∃ Cv : ℕ → ℝ, ∀ m,
        Cv m = Real.cos ((m : ℝ) * Real.pi / (n : ℝ)) := ⟨_, fun _ => rfl⟩
    obtain ⟨Sv, hSv⟩ : ∃ Sv : ℕ → ℝ, ∀ m,
        Sv m = Real.sin ((m : ℝ) * Real.pi / (n : ℝ)) := ⟨_, fun _ => rfl⟩
    obtain ⟨Pv, hPv⟩ : ∃ Pv : ℕ → ℝ, ∀ k,
        Pv k = ∑ r ∈ Finset.range n, f r * Cv (r * k) := ⟨_, fun _ => rfl⟩
    obtain ⟨Qv, hQv⟩ : ∃ Qv : ℕ → ℝ, ∀ k,
        Qv k = ∑ r ∈ Finset.range n, f r * Sv (r * k) := ⟨_, fun _ => rfl⟩
    obtain ⟨Av, hAv⟩ : ∃ Av : ℕ → ℝ, ∀ k,
        Av k = Real.sqrt (Real.sqrt (Pv k * Pv k + Qv k * Qv k)) := ⟨_, fun _ => rfl⟩
    obtain ⟨Gv, hGv⟩ : ∃ Gv : ℕ → ℝ, ∀ k,
        Gv k = 1 / (2 * (n : ℝ) * Av k) := ⟨_, fun _ => rfl⟩
    obtain ⟨Vr, hVr⟩ : ∃ Vr : ℕ → ℕ → ℝ, ∀ a k, Vr a k =
        if a < n then Av k * Cv (a * k)
        else Gv k * (Pv k * Cv ((a - n) * k) + -(Qv k * Sv ((a - n) * k))) :=
      ⟨_, fun _ _ => rfl⟩
    obtain ⟨Vi, hVi⟩ : ∃ Vi : ℕ → ℕ → ℝ, ∀ a k, Vi a k =
        if a < n then Av k * Sv (a * k)
        else Gv k * (Pv k * Sv ((a - n) * k) + Qv k * Cv ((a - n) * k)) :=
      ⟨_, fun _ _ => rfl⟩
    obtain ⟨Kv, hKv⟩ : ∃ Kv : ℕ → ℕ → ℝ, ∀ a b, Kv a b =
        ∑ k ∈ Finset.range (2 * n), (Vr a k * Vr b k + Vi a k * Vi b k) :=
      ⟨_, fun _ _ => rfl⟩
    have hecx : ∀ (w : List ℝ) (m : ℕ),
        real_arithmetic_expression_evaluate f w (cx n m) = Cv m := by
      intro w m
      rw [hcx, hCv]
      simp only [real_arithmetic_expression_evaluate]
      push_cast
      ring_nf
    have hesx : ∀ (w : List ℝ) (m : ℕ),
        real_arithmetic_expression_evaluate f w (sx n m) = Sv m := by
      intro w m
      rw [hsx, hSv]
      simp only [real_arithmetic_expression_evaluate]
      push_cast
      ring_nf
    have hepx : ∀ (w : List ℝ) (k : ℕ),
        real_arithmetic_expression_evaluate f w (px n k) = Pv k := by
      intro w k
      rw [hpx, hPv]
      refine hsumEval f w _ (fun r => f r * Cv (r * k)) n ?_
      intro r hr
      simp only [real_arithmetic_expression_evaluate]
      rw [hecx]
    have heqx : ∀ (w : List ℝ) (k : ℕ),
        real_arithmetic_expression_evaluate f w (qx n k) = Qv k := by
      intro w k
      rw [hqx, hQv]
      refine hsumEval f w _ (fun r => f r * Sv (r * k)) n ?_
      intro r hr
      simp only [real_arithmetic_expression_evaluate]
      rw [hesx]
    have heax : ∀ (w : List ℝ) (k : ℕ),
        real_arithmetic_expression_evaluate f w (ax n k) = Av k := by
      intro w k
      rw [hax, hAv]
      simp only [real_arithmetic_expression_evaluate]
      rw [hepx, heqx]
    have hegx : ∀ (w : List ℝ) (k : ℕ),
        real_arithmetic_expression_evaluate f w (gx n k) = Gv k := by
      intro w k
      rw [hgx, hGv]
      simp only [real_arithmetic_expression_evaluate]
      rw [heax]
      push_cast
      ring_nf
    have hevrx : ∀ (w : List ℝ) (a k : ℕ),
        real_arithmetic_expression_evaluate f w (vrx n a k) = Vr a k := by
      intro w a k
      rw [hvrx, hVr]
      split_ifs with h
      · simp only [real_arithmetic_expression_evaluate]
        rw [heax, hecx]
      · simp only [real_arithmetic_expression_evaluate]
        rw [hegx, hepx, hecx, heqx, hesx]
    have hevix : ∀ (w : List ℝ) (a k : ℕ),
        real_arithmetic_expression_evaluate f w (vix n a k) = Vi a k := by
      intro w a k
      rw [hvix, hVi]
      split_ifs with h
      · simp only [real_arithmetic_expression_evaluate]
        rw [heax, hesx]
      · simp only [real_arithmetic_expression_evaluate]
        rw [hegx, hepx, hesx, heqx, hecx]
    have hekx : ∀ (w : List ℝ) (a b : ℕ),
        real_arithmetic_expression_evaluate f w (kx n a b) = Kv a b := by
      intro w a b
      rw [hkx, hKv]
      refine hsumEval f w _ (fun k => Vr a k * Vr b k + Vi a k * Vi b k) (2 * n) ?_
      intro k hk
      simp only [real_arithmetic_expression_evaluate]
      rw [hevrx, hevrx, hevix, hevix]
    have hKreg : ∀ a b, a < 2 * n → b < 2 * n →
        (W (2 * (2 * n * (2 * n)))).getD (a * (2 * n) + b) 0 = Kv a b := by
      intro a b ha hb
      have hlt := hidxT a b ha hb
      rw [hWget _ _ (by omega), hex, if_pos hlt, (hdivmod a b hb).1, (hdivmod a b hb).2,
        hekx]
    obtain ⟨Lv, hLv⟩ : ∃ Lv : ℕ → ℕ → ℝ, ∀ a b, Lv a b =
        (W (2 * (2 * n * (2 * n)))).getD (2 * n * (2 * n) + a * (2 * n) + b) 0 :=
      ⟨_, fun _ _ => rfl⟩
    have hLev : ∀ a b, a < 2 * n → b < 2 * n →
        Lv a b = real_arithmetic_expression_evaluate f
          (W (2 * n * (2 * n) + a * (2 * n) + b)) (lx n a b) := by
      intro a b ha hb
      have hlt := hidxT a b ha hb
      rw [hLv, hWget _ _ (by omega), hex, if_neg (by omega),
        show 2 * n * (2 * n) + a * (2 * n) + b - 2 * n * (2 * n) = a * (2 * n) + b by omega,
        (hdivmod a b hb).1, (hdivmod a b hb).2]
    have hLread : ∀ a b c d : ℕ, a < 2 * n → b < 2 * n →
        c * (2 * n) + d < a * (2 * n) + b →
        (W (2 * n * (2 * n) + a * (2 * n) + b)).getD (2 * n * (2 * n) + c * (2 * n) + d) 0
          = Lv c d := by
      intro a b c d ha hb hlt
      have h1 := hidxT a b ha hb
      rw [hWstab _ _ (by omega) (by omega), hLv]
    have hLup : ∀ a b, a < b → b < 2 * n → Lv a b = 0 := by
      intro a b hab hb
      rw [hLev a b (by omega) hb, hlx, if_pos hab]
      simp [real_arithmetic_expression_evaluate]
    have hLdg : ∀ a, a < 2 * n → Lv a a =
        Real.sqrt (Kv a a - ∑ k ∈ Finset.range a, Lv a k * Lv a k) := by
      intro a ha
      rw [hLev a a ha ha, hlx, if_neg (lt_irrefl a), if_pos rfl]
      simp only [real_arithmetic_expression_evaluate]
      have h1 := hidxT a a ha ha
      have hk1 : (W (2 * n * (2 * n) + a * (2 * n) + a)).getD (a * (2 * n) + a) 0
          = Kv a a := by
        rw [hWstab _ _ (by omega) (by omega)]
        exact hKreg a a ha ha
      have hk2 : real_arithmetic_expression_evaluate f
          (W (2 * n * (2 * n) + a * (2 * n) + a))
          (sumE (fun k => .mul (.register (2 * n * (2 * n) + a * (2 * n) + k))
            (.register (2 * n * (2 * n) + a * (2 * n) + k))) a)
          = ∑ k ∈ Finset.range a, Lv a k * Lv a k := by
        refine hsumEval f _ _ (fun k => Lv a k * Lv a k) a ?_
        intro k hk
        simp only [real_arithmetic_expression_evaluate]
        rw [hLread a a a k ha ha (by omega)]
      rw [hk1, hk2]
      congr 1
    have hLoff : ∀ a b, b < a → a < 2 * n → Lv a b =
        (Kv a b - ∑ k ∈ Finset.range b, Lv a k * Lv b k) / Lv b b := by
      intro a b hba ha
      rw [hLev a b ha (by omega), hlx, if_neg (by omega), if_neg (by omega)]
      simp only [real_arithmetic_expression_evaluate]
      have h1 := hidxT a b ha (by omega)
      have hk1 : (W (2 * n * (2 * n) + a * (2 * n) + b)).getD (a * (2 * n) + b) 0
          = Kv a b := by
        rw [hWstab _ _ (by omega) (by omega)]
        exact hKreg a b ha (by omega)
      have hk2 : real_arithmetic_expression_evaluate f
          (W (2 * n * (2 * n) + a * (2 * n) + b))
          (sumE (fun k => .mul (.register (2 * n * (2 * n) + a * (2 * n) + k))
            (.register (2 * n * (2 * n) + b * (2 * n) + k))) b)
          = ∑ k ∈ Finset.range b, Lv a k * Lv b k := by
        refine hsumEval f _ _ (fun k => Lv a k * Lv b k) b ?_
        intro k hk
        simp only [real_arithmetic_expression_evaluate]
        rw [hLread a b a k ha (by omega) (by omega),
          hLread a b b k ha (by omega) (hidx a b k (by omega) hba)]
      have hk3 : (W (2 * n * (2 * n) + a * (2 * n) + b)).getD
          (2 * n * (2 * n) + b * (2 * n) + b) 0 = Lv b b :=
        hLread a b b b ha (by omega) (hidx a b b (by omega) hba)
      rw [hk1, hk2, hk3]
      congr 1
    have hrunL : ∀ i j : Fin n,
        (toeplitz_factorization_algorithm_run alg f n).left i j = Lv i.1 j.1 := by
      intro i j
      rw [hLv]
      simp only [toeplitz_factorization_algorithm_run,
        factorization_arithmetic_program_evaluate, halg n]
      rw [← hWdef]
    have hrunR : ∀ i j : Fin n,
        (toeplitz_factorization_algorithm_run alg f n).right i j = Lv (n + j.1) i.1 := by
      intro i j
      rw [hLv]
      simp only [toeplitz_factorization_algorithm_run,
        factorization_arithmetic_program_evaluate, halg n]
      rw [← hWdef]
    have hKsym : ∀ a b, Kv a b = Kv b a := by
      intro a b
      rw [hKv, hKv]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hKpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ a ∈ Finset.range (2 * n),
        ∑ b ∈ Finset.range (2 * n), x a * Kv a b * x b := by
      intro x
      have step1 : ∀ a b, x a * Kv a b * x b = ∑ k ∈ Finset.range (2 * n),
          ((x a * Vr a k) * (x b * Vr b k) + (x a * Vi a k) * (x b * Vi b k)) := by
        intro a b
        rw [hKv, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
      have step2 : ∀ a, ∑ b ∈ Finset.range (2 * n), x a * Kv a b * x b
          = ∑ k ∈ Finset.range (2 * n), ∑ b ∈ Finset.range (2 * n),
              ((x a * Vr a k) * (x b * Vr b k) + (x a * Vi a k) * (x b * Vi b k)) := by
        intro a
        rw [Finset.sum_congr rfl (fun b _ => step1 a b), Finset.sum_comm]
      rw [Finset.sum_congr rfl (fun a _ => step2 a), Finset.sum_comm]
      refine Finset.sum_nonneg fun k _ => ?_
      have step3 : ∑ a ∈ Finset.range (2 * n), ∑ b ∈ Finset.range (2 * n),
            ((x a * Vr a k) * (x b * Vr b k) + (x a * Vi a k) * (x b * Vi b k))
          = (∑ a ∈ Finset.range (2 * n), x a * Vr a k) ^ 2
            + (∑ a ∈ Finset.range (2 * n), x a * Vi a k) ^ 2 := by
        rw [pow_two, pow_two, Finset.sum_mul_sum, Finset.sum_mul_sum,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_add_distrib
      rw [step3]
      positivity
    have hfact := hchol (2 * n) Kv Lv hKsym hKpsd hLup hLdg hLoff
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hroot := fourier_complex_factorization_root n hn
    have hpowne : ∀ m : ℕ, distinguished_root n ^ m ≠ 0 := by
      intro m
      refine pow_ne_zero _ ?_
      intro h
      rw [h, norm_zero] at hroot
      exact absurd hroot.1 (by norm_num)
    have hnorm1 : ∀ m : ℕ, ‖distinguished_root n ^ m‖ = 1 := by
      intro m
      rw [norm_pow, hroot.1, one_pow]
    have hconjinv : ∀ m : ℕ, (starRingEnd ℂ) (distinguished_root n ^ m)
        = (distinguished_root n ^ m)⁻¹ := by
      intro m
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hnorm1 m]
      simp
    have hpow : ∀ m : ℕ, distinguished_root n ^ m
        = (Cv m : ℂ) + (Sv m : ℂ) * Complex.I := by
      intro m
      rw [distinguished_root, ← Complex.exp_nat_mul, hCv, hSv,
        show (m : ℂ) * ((Real.pi : ℂ) / (n : ℂ) * Complex.I)
          = (((m : ℝ) * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hCS : ∀ m : ℕ, Cv m * Cv m + Sv m * Sv m = 1 := by
      intro m
      rw [hCv, hSv]
      nlinarith [Real.sin_sq_add_cos_sq ((m : ℝ) * Real.pi / (n : ℝ))]
    obtain ⟨Rv, hRv⟩ : ∃ Rv : ℕ → ℝ, ∀ k,
        Rv k = Real.sqrt (Pv k * Pv k + Qv k * Qv k) := ⟨_, fun _ => rfl⟩
    have hRvnn : ∀ k, 0 ≤ Rv k := by
      intro k
      rw [hRv]
      exact Real.sqrt_nonneg _
    have hAvnn : ∀ k, 0 ≤ Av k := by
      intro k
      rw [hAv]
      exact Real.sqrt_nonneg _
    have hAvsq : ∀ k, Av k * Av k = Rv k := by
      intro k
      rw [hAv, hRv]
      exact Real.mul_self_sqrt (Real.sqrt_nonneg _)
    have hRvsq : ∀ k, Rv k * Rv k = Pv k * Pv k + Qv k * Qv k := by
      intro k
      rw [hRv]
      refine Real.mul_self_sqrt ?_
      exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
    obtain ⟨Zv, hZvdef⟩ : ∃ Zv : ℕ → ℂ, ∀ k,
        Zv k = decay_polynomial f n (distinguished_root n ^ k) := ⟨_, fun _ => rfl⟩
    have hZreim : ∀ k, (Zv k).re = Pv k ∧ (Zv k).im = Qv k := by
      intro k
      have hexp : Zv k = ∑ r ∈ Finset.range n,
          ((f r : ℂ) * ((Cv (r * k) : ℂ) + (Sv (r * k) : ℂ) * Complex.I)) := by
        rw [hZvdef, decay_polynomial,
          Fin.sum_univ_eq_sum_range
            (fun r => (f r : ℂ) * (distinguished_root n ^ k) ^ r) n]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [← pow_mul, mul_comm k r, hpow]
      refine ⟨?_, ?_⟩
      · rw [hexp, Complex.re_sum, hPv]
        exact Finset.sum_congr rfl fun r _ => by simp [Complex.mul_re]
      · rw [hexp, Complex.im_sum, hQv]
        exact Finset.sum_congr rfl fun r _ => by simp [Complex.mul_im]
    have hZv : ∀ k, Zv k = (Pv k : ℂ) + (Qv k : ℂ) * Complex.I := by
      intro k
      rw [← (hZreim k).1, ← (hZreim k).2, Complex.re_add_im]
    have hZnorm : ∀ k, ‖Zv k‖ = Rv k := by
      intro k
      rw [hRv, Complex.norm_def, Complex.normSq_apply, (hZreim k).1, (hZreim k).2]
    obtain ⟨Sv2, hSv2⟩ : ∃ S : ℝ, S = ∑ k ∈ Finset.range (2 * n), Rv k := ⟨_, rfl⟩
    have hSnn : 0 ≤ Sv2 := by
      rw [hSv2]
      exact Finset.sum_nonneg fun k _ => hRvnn k
    have hSfour : Sv2 = ∑ k : Fin (2 * n),
        ‖decay_polynomial f n (distinguished_root n ^ k.1)‖ := by
      rw [hSv2, Fin.sum_univ_eq_sum_range
        (fun k => ‖decay_polynomial f n (distinguished_root n ^ k)‖) (2 * n)]
      exact Finset.sum_congr rfl fun k _ => by rw [← hZvdef, hZnorm]
    obtain ⟨Uc, hUc⟩ : ∃ Uc : ℕ → ℕ → ℂ, ∀ a k,
        Uc a k = (Vr a k : ℂ) + (Vi a k : ℂ) * Complex.I := ⟨_, fun _ _ => rfl⟩
    have hKvre : ∀ a b, Kv a b
        = (∑ k ∈ Finset.range (2 * n), Uc a k * (starRingEnd ℂ) (Uc b k)).re := by
      intro a b
      rw [hKv, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hUc, hUc]
      simp [Complex.mul_re]
    have hUc1 : ∀ i k, i < n → Uc i k
        = (Av k : ℂ) * distinguished_root n ^ (i * k) := by
      intro i k hi
      rw [hUc, hVr, hVi, if_pos hi, if_pos hi, hpow]
      push_cast
      ring
    have hUc2 : ∀ j k, Uc (n + j) k
        = (Gv k : ℂ) * Zv k * distinguished_root n ^ (j * k) := by
      intro j k
      rw [hUc, hVr, hVi, if_neg (by omega), if_neg (by omega),
        show n + j - n = j by omega, hZv, hpow]
      push_cast
      linear_combination (-((Gv k : ℂ) * (Qv k : ℂ) * (Sv (j * k) : ℂ))) * Complex.I_sq
    have hdiagL : ∀ i, i < n → Kv i i = Sv2 := by
      intro i hi
      rw [hKv, hSv2]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hVr, hVi, if_pos hi, if_pos hi]
      linear_combination (Av k * Av k) * hCS (i * k) + hAvsq k
    have hdiagR : ∀ j, Kv (n + j) (n + j) = Sv2 / (2 * (n : ℝ)) ^ 2 := by
      intro j
      rw [hKv, hSv2, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hVr, hVi, if_neg (by omega), if_neg (by omega), show n + j - n = j by omega]
      rcases eq_or_lt_of_le (hRvnn k) with h0 | hpos
      · have hPQ : Pv k * Pv k + Qv k * Qv k = 0 := by
          rw [← hRvsq k, ← h0]
          ring
        have hP0 : Pv k = 0 := by nlinarith [mul_self_nonneg (Pv k), mul_self_nonneg (Qv k)]
        have hQ0 : Qv k = 0 := by nlinarith [mul_self_nonneg (Pv k), mul_self_nonneg (Qv k)]
        rw [hP0, hQ0, ← h0]
        ring
      · have hAvpos : 0 < Av k := by nlinarith [hAvsq k, hAvnn k]
        have hAvne : Av k ≠ 0 := ne_of_gt hAvpos
        have hkey : (Pv k * Cv (j * k) + -(Qv k * Sv (j * k)))
              * (Pv k * Cv (j * k) + -(Qv k * Sv (j * k)))
            + (Pv k * Sv (j * k) + Qv k * Cv (j * k))
              * (Pv k * Sv (j * k) + Qv k * Cv (j * k)) = Rv k * Rv k := by
          linear_combination (Pv k * Pv k + Qv k * Qv k) * hCS (j * k) + (hRvsq k).symm
        have hGvsq : Gv k * Gv k * (Rv k * Rv k) = Rv k / (2 * (n : ℝ)) ^ 2 := by
          rw [hGv, ← hAvsq k]
          field_simp
        linear_combination (Gv k * Gv k) * hkey + hGvsq
    have hAvGv : ∀ k, ((Av k : ℂ) * (Gv k : ℂ)) * (starRingEnd ℂ) (Zv k)
        = (starRingEnd ℂ) (Zv k) / (2 * (n : ℂ)) := by
      intro k
      rcases eq_or_lt_of_le (hRvnn k) with h0 | hpos
      · have hz : Zv k = 0 := by
          rw [← norm_eq_zero, hZnorm, ← h0]
        rw [hz]
        simp
      · have hAvpos : 0 < Av k := by nlinarith [hAvsq k, hAvnn k]
        have hAvne : Av k ≠ 0 := ne_of_gt hAvpos
        have hag : Av k * Gv k = 1 / (2 * (n : ℝ)) := by
          rw [hGv]
          field_simp
        rw [show ((Av k : ℂ) * (Gv k : ℂ)) = ((Av k * Gv k : ℝ) : ℂ) from by push_cast; ring,
          hag]
        push_cast
        ring
    have hpowconj : ∀ i j k : ℕ, i ≤ 2 * n →
        distinguished_root n ^ (i * k) *
            (starRingEnd ℂ) (distinguished_root n ^ (j * k))
          = (starRingEnd ℂ) (distinguished_root n ^ ((2 * n - i + j) * k)) := by
      intro i j k hi
      rw [hconjinv, hconjinv]
      have hmul : distinguished_root n ^ (i * k) *
          distinguished_root n ^ ((2 * n - i + j) * k)
          = distinguished_root n ^ (j * k) := by
        have hsum : i * k + (2 * n - i + j) * k = 2 * n * k + j * k := by
          have h1 : i + (2 * n - i + j) = 2 * n + j := by omega
          calc i * k + (2 * n - i + j) * k = (i + (2 * n - i + j)) * k := by ring
            _ = (2 * n + j) * k := by rw [h1]
            _ = 2 * n * k + j * k := by ring
        rw [← pow_add, hsum, pow_add, pow_mul, hroot.2, one_pow, one_mul]
      rw [← hmul, mul_inv, ← mul_assoc, mul_inv_cancel₀ (hpowne (i * k)), one_mul]
    have hMident : ∀ i j : Fin n, Kv i.1 (n + j.1) = decaying_matrix f n i j := by
      intro i j
      have hterms : ∀ k, Uc i.1 k * (starRingEnd ℂ) (Uc (n + j.1) k)
          = (starRingEnd ℂ) (Zv k * distinguished_root n ^ ((2 * n - i.1 + j.1) * k))
            / (2 * (n : ℂ)) := by
        intro k
        have hc : (starRingEnd ℂ) (Uc (n + j.1) k)
            = (Gv k : ℂ) * (starRingEnd ℂ) (Zv k)
              * (starRingEnd ℂ) (distinguished_root n ^ (j.1 * k)) := by
          rw [hUc2 j.1 k, map_mul, map_mul, Complex.conj_ofReal]
        rw [hUc1 i.1 k i.2, hc]
        have hrearr : (Av k : ℂ) * distinguished_root n ^ (i.1 * k) *
            ((Gv k : ℂ) * (starRingEnd ℂ) (Zv k)
              * (starRingEnd ℂ) (distinguished_root n ^ (j.1 * k)))
            = ((Av k : ℂ) * (Gv k : ℂ)) * (starRingEnd ℂ) (Zv k) *
              (distinguished_root n ^ (i.1 * k) *
                (starRingEnd ℂ) (distinguished_root n ^ (j.1 * k))) := by ring
        rw [hrearr, hAvGv k, hpowconj i.1 j.1 k (by omega), map_mul]
        ring
      have hsum : (∑ k ∈ Finset.range (2 * n),
            Uc i.1 k * (starRingEnd ℂ) (Uc (n + j.1) k))
          = complex_decaying_matrix f n i j := by
        rw [Finset.sum_congr rfl (fun k _ => hterms k), ← Finset.sum_div, ← map_sum]
        have hinv := fourier_complex_factorization_inversion f n hn i j
        rw [Fin.sum_univ_eq_sum_range
          (fun k => decay_polynomial f n (distinguished_root n ^ k) *
            distinguished_root n ^ ((2 * n - i.1 + j.1) * k)) (2 * n)] at hinv
        have hz : ∑ k ∈ Finset.range (2 * n), Zv k *
            distinguished_root n ^ ((2 * n - i.1 + j.1) * k)
            = 2 * (n : ℂ) * complex_decaying_matrix f n i j := by
          simp only [hZvdef]
          exact hinv
        have hnc : (2 * (n : ℂ)) ≠ 0 :=
          mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (by omega))
        rw [hz, map_mul, show (starRingEnd ℂ) (2 * (n : ℂ)) = 2 * (n : ℂ) from by simp [Complex.ext_iff]]
        unfold complex_decaying_matrix
        rw [Complex.conj_ofReal]
        field_simp
        exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (by omega))
      rw [hKvre, hsum]
      unfold complex_decaying_matrix
      simp
    have hprodrow : ∀ a b : ℕ, a < n → b < 2 * n →
        ∑ t ∈ Finset.range n, Lv a t * Lv b t = Kv a b := by
      intro a b ha hb
      rw [hfact a b (by omega) hb]
      refine Finset.sum_subset
        (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_
      intro x hx hx2
      simp only [Finset.mem_range] at hx hx2
      rw [hLup a x (by omega) (by omega), zero_mul]
    have hcolsum : ∀ b : ℕ, b < 2 * n →
        ∑ t ∈ Finset.range n, Lv b t * Lv b t ≤ Kv b b := by
      intro b hb
      rw [hfact b b hb hb]
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_
      intro x _ _
      exact mul_self_nonneg _
    have hrowS : ∀ i : Fin n, ∑ j : Fin n,
        ((toeplitz_factorization_algorithm_run alg f n).left i j) ^ 2 = Sv2 := by
      intro i
      simp only [hrunL, pow_two]
      rw [Fin.sum_univ_eq_sum_range (fun t => Lv i.1 t * Lv i.1 t) n,
        hprodrow i.1 i.1 i.2 (by have hi := i.2; omega), hdiagL i.1 i.2]
    have hcolS : ∀ j : Fin n, ∑ i : Fin n,
        ((toeplitz_factorization_algorithm_run alg f n).right i j) ^ 2
          ≤ Sv2 / (2 * (n : ℝ)) ^ 2 := by
      intro j
      have hsq : ∀ t : ℕ, Lv (n + j.1) t ^ 2 = Lv (n + j.1) t * Lv (n + j.1) t :=
        fun t => pow_two _
      simp only [hrunR, hsq]
      rw [Fin.sum_univ_eq_sum_range (fun t => Lv (n + j.1) t * Lv (n + j.1) t) n,
        ← hdiagR j.1]
      exact hcolsum (n + j.1) (by have hj := j.2; omega)
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    have hcol : real_column_norm (toeplitz_factorization_algorithm_run alg f n).right
        ≤ Real.sqrt Sv2 / (2 * (n : ℝ)) := by
      unfold real_column_norm
      refine csSup_le (Set.range_nonempty _) ?_
      rintro x ⟨j, rfl⟩
      calc Real.sqrt (∑ i : Fin n,
            ((toeplitz_factorization_algorithm_run alg f n).right i j) ^ 2)
          ≤ Real.sqrt (Sv2 / (2 * (n : ℝ)) ^ 2) := Real.sqrt_le_sqrt (hcolS j)
        _ = Real.sqrt Sv2 / (2 * (n : ℝ)) := by
            rw [Real.sqrt_div hSnn, Real.sqrt_sq]
            positivity
    have hmax : real_maximum_row_norm
        (toeplitz_factorization_algorithm_run alg f n).left = Real.sqrt Sv2 := by
      unfold real_maximum_row_norm
      have hf : (fun i : Fin n => Real.sqrt (∑ j : Fin n,
          ((toeplitz_factorization_algorithm_run alg f n).left i j) ^ 2))
          = fun _ => Real.sqrt Sv2 := by
        funext i
        rw [hrowS i]
      rw [hf]
      simp
    have hptrace : ∀ p : ℕ,
        real_row_p_trace p (toeplitz_factorization_algorithm_run alg f n).left
          = Real.rpow ((n : ℝ) * Real.rpow Sv2 ((p : ℝ) / 2)) (1 / (p : ℝ)) := by
      intro p
      unfold real_row_p_trace
      congr 2
      simp_rw [hrowS]
      simp
    have hpTraceSimple : ∀ p : ℕ, 2 ≤ p →
        real_row_p_trace p (toeplitz_factorization_algorithm_run alg f n).left
          = Real.rpow (n : ℝ) (1 / (p : ℝ)) * Real.sqrt Sv2 := by
      intro p hp
      rw [hptrace]
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
      have hexp : ((p : ℝ) / 2) * (1 / (p : ℝ)) = 1 / 2 := by
        field_simp [hp0]
      calc
        Real.rpow ((n : ℝ) * Real.rpow Sv2 ((p : ℝ) / 2)) (1 / (p : ℝ)) =
            Real.rpow (n : ℝ) (1 / (p : ℝ)) *
              Real.rpow (Real.rpow Sv2 ((p : ℝ) / 2)) (1 / (p : ℝ)) :=
          Real.mul_rpow (le_of_lt hnR) (Real.rpow_nonneg hSnn _)
        _ = Real.rpow (n : ℝ) (1 / (p : ℝ)) *
            Real.rpow Sv2 (((p : ℝ) / 2) * (1 / (p : ℝ))) := by
          congr 1
          exact (Real.rpow_mul hSnn _ _).symm
        _ = Real.rpow (n : ℝ) (1 / (p : ℝ)) * Real.rpow Sv2 (1 / 2) :=
          congrArg (fun x : ℝ => Real.rpow (n : ℝ) (1 / (p : ℝ)) * Real.rpow Sv2 x) hexp
        _ = Real.rpow (n : ℝ) (1 / (p : ℝ)) * Real.sqrt Sv2 := by
          congr 1
          exact (Real.sqrt_eq_rpow Sv2).symm
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · ext i j
      rw [Matrix.mul_apply]
      simp only [hrunL, hrunR]
      rw [Fin.sum_univ_eq_sum_range (fun t => Lv i.1 t * Lv (n + j.1) t) n,
        hprodrow i.1 (n + j.1) i.2 (by have hj := j.2; omega), hMident i j]
    · unfold lower_triangular Matrix.BlockTriangular
      intro i j hij
      have hlt : i.1 < j.1 := OrderDual.toDual_lt_toDual.1 hij
      rw [hrunL i j, hLup i.1 j.1 hlt (by have hj := j.2; omega)]
    · intro p hp
      have hTrnn : 0 ≤ real_row_p_trace p
          (toeplitz_factorization_algorithm_run alg f n).left := by
        rw [hpTraceSimple p hp]
        exact mul_nonneg (Real.rpow_nonneg (le_of_lt hnR) _) (Real.sqrt_nonneg _)
      refine le_trans (mul_le_mul_of_nonneg_left hcol hTrnn) ?_
      rw [hpTraceSimple p hp]
      unfold fourier_bound
      rw [← hSfour]
      have hsqrt : Real.sqrt Sv2 * Real.sqrt Sv2 = Sv2 := Real.mul_self_sqrt hSnn
      have hpowdiff : Real.rpow (n : ℝ) (1 - 1 / (p : ℝ)) =
          (n : ℝ) / Real.rpow (n : ℝ) (1 / (p : ℝ)) := by
        calc
          Real.rpow (n : ℝ) (1 - 1 / (p : ℝ)) =
              Real.rpow (n : ℝ) 1 / Real.rpow (n : ℝ) (1 / (p : ℝ)) :=
            Real.rpow_sub hnR _ _
          _ = (n : ℝ) / Real.rpow (n : ℝ) (1 / (p : ℝ)) := by
            congr 1
            exact Real.rpow_one (n : ℝ)
      rw [hpowdiff]
      have hcost : Real.rpow (n : ℝ) (1 / (p : ℝ)) * Real.sqrt Sv2 *
          (Real.sqrt Sv2 / (2 * (n : ℝ))) =
          Real.rpow (n : ℝ) (1 / (p : ℝ)) * Sv2 / (2 * (n : ℝ)) := by
        calc
          _ = Real.rpow (n : ℝ) (1 / (p : ℝ)) *
              (Real.sqrt Sv2 * Real.sqrt Sv2) / (2 * (n : ℝ)) := by ring
          _ = _ := by rw [hsqrt]
      rw [hcost]
      have hnpow0 : Real.rpow (n : ℝ) (1 / (p : ℝ)) ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos hnR _)
      field_simp
      exact le_rfl
    · have hMnn : 0 ≤ real_maximum_row_norm
          (toeplitz_factorization_algorithm_run alg f n).left := by
        rw [hmax]
        positivity
      refine le_trans (mul_le_mul_of_nonneg_left hcol hMnn) ?_
      rw [hmax]
      unfold operator_fourier_bound
      rw [← hSfour, show Real.sqrt Sv2 * (Real.sqrt Sv2 / (2 * (n : ℝ)))
        = (Real.sqrt Sv2 * Real.sqrt Sv2) / (2 * (n : ℝ)) from by ring,
        Real.mul_self_sqrt hSnn]

@[blueprint "lem:efficient-algorithm-realization"
  (statement := /-- There exists a Toeplitz factorization algorithm $A$ and constants $C,q\in\mathbb N$, with $C>0$, such that, for every $n\in\mathbb N$, the structural operation count of the size-$n$ program is at most $C(n+1)^q$.  For every $f:\mathbb N\to\mathbb R$ and every positive $n$, the resulting matrices form a valid factorization and satisfy simultaneously all finite-$p$ Fourier bounds and the maximum-row Fourier bound. -/)
  (proof := /-- Invoke \cref{lem:deterministic-factorization-construction-exists}; the construction certified there is the following one. For $n=0$, let $P_0$ have no instructions and the unique empty output matrices. Suppose that $n>0$. All complex quantities below are represented by pairs of real registers. The program $P_n$ first queries and stores $f(0),\ldots,f(n-1)$. For every $k<2n$, it evaluates
  \[
    c_k=\cos(\pi k/n),\qquad s_k=\sin(\pi k/n),
  \]
  and then evaluates the real and imaginary parts of
  \[
    z_k=\sum_{r<n}f(r)(c_k+\iota s_k)^r
  \]
  by the usual recurrence for complex multiplication. Write
  $\rho_k=\sqrt{(\Re z_k)^2+(\Im z_k)^2}$ and
  $a_k=\sqrt{\rho_k}$. If $a_k=0$, the program sets $b_k=0$; otherwise it sets
  $b_k=z_k/a_k$. This test is expressed by applying
  \cref{def:real-arithmetic-expression} to $-a_k$, since $a_k\geq0$.
  Thus, in both branches,
  \[
    a_kb_k=z_k,\qquad |a_k|^2=|b_k|^2=|z_k|.
  \]
  The program next evaluates, by repeated complex multiplication,
  \[
    \widetilde L_{ik}=a_k\omega_n^{(2n-i)k},\qquad
    \widetilde R_{kj}=\frac{b_k\omega_n^{jk}}{2n}
  \]
  for $i,j<n$ and $k<2n$. The Fourier inversion identity in
  \cref{lem:fourier-complex-factorization-inversion} gives
  $M_f^{\mathbb C}=\widetilde L\widetilde R$, while the unit-modulus
  identity in \cref{lem:fourier-complex-factorization-root} and the two
  displayed identities give the required row- and column-norm calculation.

  The next instruction block writes the real matrices
  \[
    \widehat L=(\Re\widetilde L\mid-\Im\widetilde L),\qquad
    \widehat R=\binom{\Re\widetilde R}{\Im\widetilde R}.
  \]
  The entrywise calculation in
  \cref{lem:realification-preserves-factorization-norms} proves that
  $M_f=\widehat L\widehat R$ and that this operation preserves every
  finite row cost, the maximum row cost, and the column cost.

  It remains to specify the triangularization block without an
  unrecorded choice. Process the rows $v_0,\ldots,v_{n-1}$ of
  $\widehat L$ in order. At stage $j$, subtract from $v_j$ its projections
  onto the previously stored orthonormal vectors. If the squared norm of
  the residual is positive, normalize it and store the result as $q_j$.
  If the residual is zero, scan the standard coordinate vectors in their
  natural order and take the first whose residual after the same
  projections has positive squared norm. After the first $n$ stages,
  continue this scan until $q_0,\ldots,q_{4n-1}$ is an orthonormal basis
  of $\mathbb R^{4n}$. At every deficient stage such a coordinate vector
  exists: otherwise the previously constructed proper orthonormal family
  would span every coordinate vector. All zero tests use
  \texttt{branchNonnegative} on the negative of a squared norm, and all
  normalizations use square root and division, so this is a program in
  \cref{def:factorization-arithmetic-program}. Define
  \[
    L_{ij}=\langle q_j,v_i\rangle,\qquad
    R_{ij}=\sum_{t<4n}(q_i)_t\widehat R_{tj}.
  \]
  The stage invariant puts $v_i$ in the span of
  $q_0,\ldots,q_i$, hence $L_{ij}=0$ for $i<j$ and
  $\widehat L=LQ$. Parseval's identity then proves the factorization and
  cost assertions directly.

  Finally, take the certified record $D$ supplied by
  \cref{lem:deterministic-factorization-construction-exists} and set
  $A=D.\mathit{algorithm}$.  The positive constant
  $D.\mathit{costConstant}$ and exponent $D.\mathit{costExponent}$,
  together with $D.\mathit{polynomialCost}$, prove
  \cref{def:factorization-algorithm-efficient}.  For every
  $f:\mathbb N\to\mathbb R$ and every positive $n$, the assertion
  $D.\mathit{correct}(f,n)$ supplies output validity, all finite-$p$
  Fourier estimates, and the maximum-row Fourier estimate for this same
  algorithm $A$. -/)
  (title := /-- Efficient realization of the bounded factorization -/)
  (latexEnv := "lemma")]
lemma efficient_algorithm_realization :
    ∃ A : toeplitz_factorization_algorithm,
      factorization_algorithm_efficient A ∧
      ∀ (f : ℕ → ℝ) (n : ℕ), 0 < n →
        factorization_output_valid f n (toeplitz_factorization_algorithm_run A f n) ∧
        (∀ p : ℕ, 2 ≤ p →
          real_row_p_trace p (toeplitz_factorization_algorithm_run A f n).left *
              real_column_norm (toeplitz_factorization_algorithm_run A f n).right ≤
            fourier_bound f n p) ∧
        real_maximum_row_norm (toeplitz_factorization_algorithm_run A f n).left *
            real_column_norm (toeplitz_factorization_algorithm_run A f n).right ≤
          operator_fourier_bound f n := by
  obtain ⟨D⟩ := deterministic_factorization_construction_exists
  exact ⟨D.algorithm,
    ⟨D.costConstant, D.costExponent, D.costConstantPositive, D.polynomialCost⟩,
    D.correct⟩

@[blueprint "lem:operator-two-special-case"
  (statement := /-- Let $f:\mathbb N\to\mathbb R$, let $n\in\mathbb N$ be positive, and let
  $L,R\in\mathbb R^{n\times n}$. If $M_f=LR$ and
  $\operatorname{Tr}_\infty(L)\lVert R\rVert_{1\to2}\leq\mathcal B_\infty(f,n)$, then
  \[\gamma_{\mathrm{op},2}(M_f)=\gamma_{(\infty)}(M_f)\leq\mathcal B_\infty(f,n).\] -/)
  (proof := /-- The equality is the convention in \cref{def:operator-two-factorization-norm}. Apply \cref{lem:infinite-factorization-norm-le-cost} to $M_f=LR$, and compose its conclusion with the assumed bound on the maximum-row factorization cost. -/)
  (title := /-- The operator-$2$ special case -/)
  (latexEnv := "lemma")]
lemma operator_two_special_case (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (L R : Matrix (Fin n) (Fin n) ℝ)
    (hfactor : decaying_matrix f n = L * R)
    (hcost : real_maximum_row_norm L * real_column_norm R ≤ operator_fourier_bound f n) :
    operator_two_factorization_norm (decaying_matrix f n) =
        infinite_factorization_norm (decaying_matrix f n) ∧
      operator_two_factorization_norm (decaying_matrix f n) ≤
        operator_fourier_bound f n := by
  exact ⟨rfl, by
    simpa only [operator_two_factorization_norm] using
      (le_trans (infinite_factorization_norm_le_cost (decaying_matrix f n) L R hfactor) hcost)⟩

@[blueprint "lem:frobenius-special-case"
  (statement := /-- Let $f:\mathbb N\to\mathbb R$, let $n\in\mathbb N$ satisfy $n>0$, and let
  $L,R\in\mathbb R^{n\times n}$ satisfy $M_f=LR$. If
  $\operatorname{Tr}_2(L)\lVert R\rVert_{1\to2}\leq\mathcal B_2(f,n)$, then
  \[\gamma_{\mathrm F}(M_f)\leq\frac{1}{2\sqrt n}\sum_{k=0}^{2n-1}|m_{f,n}(\omega_n^k)|.\] -/)
  (proof := /-- Unfold \cref{def:frobenius-factorization-norm} and apply
  \cref{lem:finite-factorization-norm-le-cost} with $p=2$ to the given factorization.
  Compose the resulting inequality with the assumed cost bound. After unfolding
  \cref{def:fourier-bound,def:frobenius-fourier-bound}, the identities
  $1-1/2=1/2$ and $n^{1/2}=\sqrt n$ identify its right-hand side with the
  Frobenius Fourier bound. -/)
  (title := /-- The Frobenius special case -/)
  (latexEnv := "lemma")]
lemma frobenius_special_case (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (L R : Matrix (Fin n) (Fin n) ℝ)
    (hfactor : decaying_matrix f n = L * R)
    (hcost : real_row_p_trace 2 L * real_column_norm R ≤ fourier_bound f n 2) :
    frobenius_factorization_norm (decaying_matrix f n) ≤
      frobenius_fourier_bound f n := by
  unfold frobenius_factorization_norm
  refine (finite_factorization_norm_le_cost (decaying_matrix f n) L R hfactor).trans ?_
  exact hcost.trans_eq (by
    norm_num [fourier_bound, frobenius_fourier_bound, Real.sqrt_eq_rpow])

@[blueprint "thm:main-upper-bound-gamma"
  (statement := /-- Let $f : \mathbb N\to\mathbb R$ and let $n\in\mathbb N$ be positive. There exists an efficient algorithm $A$, given by an explicit family of finite real-oracle arithmetic programs with structural operation count bounded by a fixed polynomial in the stream length. On input $(f,n)$ it produces real matrices $L,R\in\mathbb R^{n\times n}$ such that $M_f=LR$ and $L$ is lower triangular. The same output satisfies, for every integer $p\geq2$,
  \[\gamma_{(p)}(M_f)\leq\operatorname{Tr}_p(L)\lVert R\rVert_{1\to2}
    \leq\frac{1}{2n^{1-1/p}}\sum_{k=0}^{2n-1}|m_{f,n}(\omega_n^k)|.\]
  Moreover,
  \[\gamma_{\mathrm{op},2}(M_f)=\gamma_{(\infty)}(M_f)
    \leq\frac{1}{2n}\sum_{k=0}^{2n-1}|m_{f,n}(\omega_n^k)|\]
  and
  \[\gamma_{\mathrm F}(M_f)\leq\frac{1}{2\sqrt n}\sum_{k=0}^{2n-1}|m_{f,n}(\omega_n^k)|.\] -/)
  (proof := /-- Choose the polynomial-time algorithm supplied by \cref{lem:efficient-algorithm-realization}, and write its output as $(L,R)$. Output validity gives $M_f=LR$ and lower triangularity of $L$, while the algorithm guarantee supplies both asserted factorization-cost bounds. For every $p\geq2$, apply \cref{lem:finite-factorization-norm-le-cost} to obtain the first inequality and compose it with the finite-$p$ output bound. Apply \cref{lem:operator-two-special-case} to the maximum-row output bound and \cref{lem:frobenius-special-case} to the output bound at $p=2$. These statements give the two special conclusions for the same matrices returned by the algorithm. -/)
  (title := /-- Improved upper bounds for decaying-matrix factorization norms -/)
  (latexEnv := "theorem")]
theorem main_upper_bound_gamma (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    ∃ A : toeplitz_factorization_algorithm,
      factorization_algorithm_efficient A ∧
      factorization_output_valid f n (toeplitz_factorization_algorithm_run A f n) ∧
      (∀ p : ℕ, 2 ≤ p →
        finite_p_factorization_norm p (decaying_matrix f n) ≤
            real_row_p_trace p (toeplitz_factorization_algorithm_run A f n).left *
              real_column_norm (toeplitz_factorization_algorithm_run A f n).right ∧
          real_row_p_trace p (toeplitz_factorization_algorithm_run A f n).left *
              real_column_norm (toeplitz_factorization_algorithm_run A f n).right ≤
            fourier_bound f n p) ∧
      operator_two_factorization_norm (decaying_matrix f n) =
          infinite_factorization_norm (decaying_matrix f n) ∧
      operator_two_factorization_norm (decaying_matrix f n) ≤ operator_fourier_bound f n ∧
      frobenius_factorization_norm (decaying_matrix f n) ≤ frobenius_fourier_bound f n := by
  obtain ⟨A, heff, hcorrect⟩ := efficient_algorithm_realization
  obtain ⟨hvalid, hfin, hinf⟩ := hcorrect f n hn
  have hfac : decaying_matrix f n =
      (toeplitz_factorization_algorithm_run A f n).left *
        (toeplitz_factorization_algorithm_run A f n).right := And.left hvalid
  have hspecial := operator_two_special_case f n hn
    (toeplitz_factorization_algorithm_run A f n).left
    (toeplitz_factorization_algorithm_run A f n).right hfac hinf
  refine ⟨A, heff, hvalid, ?_, hspecial.1, hspecial.2,
    frobenius_special_case f n hn
      (toeplitz_factorization_algorithm_run A f n).left
      (toeplitz_factorization_algorithm_run A f n).right hfac (hfin 2 le_rfl)⟩
  intro p hp
  exact ⟨finite_factorization_norm_le_cost (decaying_matrix f n)
      (toeplitz_factorization_algorithm_run A f n).left
      (toeplitz_factorization_algorithm_run A f n).right hfac, hfin p hp⟩

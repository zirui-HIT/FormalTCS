import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Matrix.Basic

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

abbrev real_matrix (rows cols : ℕ) := Matrix (Fin rows) (Fin cols) ℝ

abbrev row_embedding (dIn dOut : ℕ) := (Fin dIn → ℝ) → (Fin dOut → ℝ)

structure self_attention_head (dIn m : ℕ) where
  query : row_embedding dIn m
  key : row_embedding dIn m
  value : row_embedding dIn m

noncomputable def attention_score {N dIn m : ℕ} (head : self_attention_head dIn m)
    (X : real_matrix N dIn) (i j : Fin N) : ℝ :=
  ∑ k : Fin m, head.query (X i) k * head.key (X j) k

noncomputable def attention_weight {N dIn m : ℕ} (head : self_attention_head dIn m)
    (X : real_matrix N dIn) (i j : Fin N) : ℝ :=
  Real.exp (attention_score head X i j) /
    ∑ j' : Fin N, Real.exp (attention_score head X i j')

noncomputable def attention_head_output {N dIn m : ℕ}
    (head : self_attention_head dIn m) (X : real_matrix N dIn) : real_matrix N m :=
  fun i k => ∑ j : Fin N, attention_weight head X i j * head.value (X j) k

structure no_mlp_transformer (N m L H : ℕ) where
  heads : Fin L → Fin H → self_attention_head m m

noncomputable def no_mlp_layer_output {N m L H : ℕ} (T : no_mlp_transformer N m L H)
    (ell : Fin L) (X : real_matrix N m) : real_matrix N m :=
  X + ∑ h : Fin H, attention_head_output (T.heads ell h) X

noncomputable def no_mlp_transformer_output {N m L H : ℕ}
    (T : no_mlp_transformer N m L H) (X : real_matrix N m) : real_matrix N m :=
  (List.ofFn (fun ell : Fin L => fun state : real_matrix N m =>
    no_mlp_layer_output T ell state)).foldl (fun state layer => layer state) X

structure transformer_evaluator where
  output : ∀ (N m L H : ℕ), no_mlp_transformer N m L H →
    real_matrix N m → real_matrix N m
  runningTime : ℕ → ℕ → ℕ → ℕ → ℝ
  runningTime_nonnegative : ∀ N m L H, 0 ≤ runningTime N m L H

def computes_no_mlp_transformers (A : transformer_evaluator)
    (m L H : ℕ → ℕ) : Prop :=
  ∀ (N : ℕ), 0 < N →
    ∀ (T : no_mlp_transformer N (m N) (L N) (H N))
      (X : real_matrix N (m N)) (i : Fin N) (j : Fin (m N)),
      |A.output N (m N) (L N) (H N) T X i j - no_mlp_transformer_output T X i j| ≤
        (1 : ℝ) / (10 * (N : ℝ))

def logarithmic_dimension (d : ℕ → ℕ) : Prop :=
  (fun N : ℕ => (d N : ℝ)) =Θ[Filter.atTop]
    (fun N : ℕ => Real.log (N : ℝ))

def polynomially_bounded (f : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, (fun N : ℕ => (f N : ℝ)) =O[Filter.atTop]
    (fun N : ℕ => (N : ℝ) ^ c)

def small_embedding_regime (m L H : ℕ → ℕ) : Prop :=
  logarithmic_dimension m ∧ polynomially_bounded L ∧ polynomially_bounded H

noncomputable def subquadratic_transformer_time (A : transformer_evaluator)
    (m L H : ℕ → ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    (fun N : ℕ => A.runningTime N (m N) (L N) (H N)) =O[Filter.atTop]
      (fun N : ℕ => (L N : ℝ) * (H N : ℝ) * Real.rpow (N : ℝ) (2 - ε))

abbrev bit_vector (d : ℕ) := Fin d → Bool

structure three_ov_instance (d n₁ n₂ n₃ : ℕ) where
  first : Fin n₁ → bit_vector d
  second : Fin n₂ → bit_vector d
  third : Fin n₃ → bit_vector d

def orthogonal_triple {d : ℕ} (a b c : bit_vector d) : Prop :=
  ∀ q : Fin d, ¬(a q = true ∧ b q = true ∧ c q = true)

def has_orthogonal_triple {d n₁ n₂ n₃ : ℕ}
    (I : three_ov_instance d n₁ n₂ n₃) : Prop :=
  ∃ i : Fin n₁, ∃ j : Fin n₂, ∃ k : Fin n₃,
    orthogonal_triple (I.first i) (I.second j) (I.third k)

def three_ov_instance_encoding {d n₁ n₂ n₃ : ℕ}
    (I : three_ov_instance d n₁ n₂ n₃) : List Bool :=
  List.replicate d true ++ [false] ++
    List.replicate n₁ true ++ [false] ++
    List.replicate n₂ true ++ [false] ++
    List.replicate n₃ true ++ [false] ++
    (List.ofFn (fun i : Fin n₁ => List.ofFn (I.first i))).flatten ++
    (List.ofFn (fun i : Fin n₂ => List.ofFn (I.second i))).flatten ++
    (List.ofFn (fun i : Fin n₃ => List.ofFn (I.third i))).flatten

structure certified_execution where
  machine : Turing.FinTM2
  inputAlphabet : machine.Γ machine.k₀ ≃ Bool
  outputAlphabet : machine.Γ machine.k₁ ≃ Bool
  inputStack_ne_outputStack : machine.k₀ ≠ machine.k₁

def certified_execution_initial (P : certified_execution) (input : List Bool) :
    P.machine.Cfg where
  l := some P.machine.main
  var := P.machine.initialState
  stk := Function.update (fun _ => []) P.machine.k₀
    (input.map P.inputAlphabet.symm)

def certified_execution_next (P : certified_execution) (c : P.machine.Cfg) :
    P.machine.Cfg :=
  (P.machine.step c).getD c

def certified_execution_run (P : certified_execution) (input : List Bool) :
    ℕ → P.machine.Cfg
  | 0 => certified_execution_initial P input
  | t + 1 => certified_execution_next P (certified_execution_run P input t)

def certified_execution_halts (P : certified_execution) (input : List Bool)
    (t : ℕ) : Prop :=
  (certified_execution_run P input t).l = none

def certified_execution_answer (P : certified_execution) (input : List Bool)
    (t : ℕ) : Bool :=
  match (certified_execution_run P input t).stk P.machine.k₁ with
  | [] => false
  | a :: _ => P.outputAlphabet a

structure three_ov_algorithm where
  execution : certified_execution
  runningTime : ℕ → ℕ → ℕ → ℕ → ℕ
  halts_within : ∀ {d n₁ n₂ n₃ : ℕ} (I : three_ov_instance d n₁ n₂ n₃),
    certified_execution_halts execution (three_ov_instance_encoding I)
      (runningTime d n₁ n₂ n₃)

def three_ov_algorithm_answer (A : three_ov_algorithm)
    {d n₁ n₂ n₃ : ℕ} (I : three_ov_instance d n₁ n₂ n₃) : Bool :=
  certified_execution_answer A.execution (three_ov_instance_encoding I)
    (A.runningTime d n₁ n₂ n₃)

def solves_three_ov (A : three_ov_algorithm) : Prop :=
  ∀ {d n₁ n₂ n₃ : ℕ} (I : three_ov_instance d n₁ n₂ n₃),
    three_ov_algorithm_answer A I = true ↔ has_orthogonal_triple I

def soft_big_o (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℕ, f =O[Filter.atTop]
    (fun N : ℕ => g N * (Real.log (N : ℝ)) ^ c)

noncomputable def three_ov_hypothesis : Prop :=
  ∀ (d K : ℕ → ℕ), logarithmic_dimension d → polynomially_bounded K →
    ∀ A : three_ov_algorithm, solves_three_ov A →
      ¬∃ ε : ℝ, 0 < ε ∧
        (fun N : ℕ => (A.runningTime (d N) N N (K N) : ℝ)) =O[Filter.atTop]
          (fun N : ℕ => (K N : ℝ) * Real.rpow (N : ℝ) (2 - ε))

def computes_reduction_transformers (A : transformer_evaluator)
    (m d L H : ℕ → ℕ) : Prop :=
  (∀ᶠ N : ℕ in Filter.atTop, 2 * d N + 2 ≤ m (N + 1)) ∧
    ∀ (N : ℕ), 0 < N →
      ∀ (T : no_mlp_transformer (N + 1) (m (N + 1)) (L (N + 1)) (H (N + 1)))
        (X : real_matrix (N + 1) (m (N + 1)))
        (i : Fin (N + 1)) (j : Fin (m (N + 1))),
      |A.output (N + 1) (m (N + 1)) (L (N + 1)) (H (N + 1)) T X i j -
          no_mlp_transformer_output T X i j| ≤ (1 : ℝ) / (10 * (N : ℝ))

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

theorem small_embedding_lower_bound (h3ov : three_ov_hypothesis)
    (m L H : ℕ → ℕ) (hregime : small_embedding_regime m L H)
    (A : certified_transformer_evaluator)
    (hcorrect : computes_no_mlp_transformers A.evaluator m L H) :
    ¬subquadratic_transformer_time A.evaluator m L H := by sorry

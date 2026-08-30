import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.ZMod.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators
open Filter

universe u v

def canonical_set (m : ℕ) : Set (ZMod m) :=
  {x | x ^ 2 = x}

def is_decoding_polynomial {F : Type u} [Field F]
    (m : ℕ) (S : Set (ZMod m)) (P : Polynomial F) : Prop :=
  ∃ ζ : F,
    IsPrimitiveRoot ζ m ∧
      Polynomial.eval 1 P = 1 ∧
      ∀ s : ZMod m, s ∈ S → s ≠ 0 →
        Polynomial.eval (ζ ^ s.val) P = 0

def has_sparse_canonical_decoder {F : Type u} [Field F]
    (m t : ℕ) : Prop :=
  ∃ P : Polynomial F,
    is_decoding_polynomial m (canonical_set m) P ∧ P.support.card ≤ t

structure one_round_pir_scheme (servers databaseSize : ℕ) where
  Query : Type
  Answer : Type
  queryBits : ℕ
  answerBits : ℕ
  encodeQuery : Query ↪ (Fin queryBits → Bool)
  encodeAnswer : Answer ↪ (Fin answerBits → Bool)
  query : Fin databaseSize → PMF (Fin servers → Query)
  answer : (Fin databaseSize → Bool) → Fin servers → Query → Answer
  reconstruct : Fin databaseSize → (Fin servers → Answer) → Bool
  correctness :
    ∀ database index,
      PMF.map
          (fun queries =>
            reconstruct index
              (fun server => answer database server (queries server)))
          (query index) =
        PMF.pure (database index)
  privacy :
    ∀ server (i j : Fin databaseSize),
      PMF.map (fun queries => queries server) (query i) =
        PMF.map (fun queries => queries server) (query j)

def pir_communication {t n : ℕ}
    (scheme : one_round_pir_scheme t n) : ℕ :=
  t * (scheme.queryBits + scheme.answerBits)

def has_target_communication_rate (t r : ℕ) : Prop :=
  ∃ schemes : (n : ℕ) → one_round_pir_scheme t n,
    ∃ d : ℕ,
      Asymptotics.IsBigO atTop
        (fun n : ℕ => Real.log ((pir_communication (schemes n) : ℕ) : ℝ))
        (fun n : ℕ =>
          Real.rpow (Real.log (n : ℝ)) (1 / ((r + 1 : ℕ) : ℝ)) *
            (Real.log (Real.log (n : ℝ))) ^ d)

theorem main
    {F : Type u} [Field F] {m r p t : ℕ}
    [CharP F p]
    (hm : 0 < m)
    (hr : m.primeFactors.card = r)
    (hp : p.Prime)
    (hcoprime : ¬p ∣ m)
    (hdecoder : has_sparse_canonical_decoder (F := F) m t) :
    has_target_communication_rate t r := by sorry

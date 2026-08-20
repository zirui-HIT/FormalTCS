import Mathlib.Computability.Partrec

structure computational_model (D : Type*) where
  compute : D →. D
  evaluator : D → ℕ → Option D
  runningTime : D → ℕ
  evaluator_correct :
    ∀ x y, compute x = pure y ↔ ∃ t, evaluator x t = some y
  runningTime_spec :
    ∀ x y, compute x = pure y →
      evaluator x (runningTime x) = some y ∧
        ∀ t, t < runningTime x → evaluator x t = none

abbrev time_bound_observation (D : Type*) :=
  D × D × ℕ

def model_domain {D : Type*} (M : computational_model D) : Set D :=
  {x | (M.compute x).Dom}

def encoded_partrec {A B : Type*} [Primcodable A] [Primcodable B]
    (f : A →. B) : Prop :=
  Nat.Partrec fun n =>
    Part.bind (Encodable.decode (α := A) n) fun a =>
      (f a).map Encodable.encode

def effective_evaluator {A B : Type*} [Primcodable A] [Primcodable B]
    (eval : A → ℕ → Option B) : Prop :=
  encoded_partrec fun p : A × ℕ => pure (eval p.1 p.2)

structure representation_system (D : Type*) [Primcodable D] where
  semantics : ℕ → D →. D
  evaluator : ℕ → D → ℕ → Option D
  simulationTime : ℕ → D → ℕ
  evaluator_effective :
    effective_evaluator fun p : ℕ × D => evaluator p.1 p.2
  evaluator_correct :
    ∀ code x y, semantics code x = pure y ↔
      ∃ t, evaluator code x t = some y
  simulationTime_spec :
    ∀ code x y, semantics code x = pure y →
      evaluator code x (simulationTime code x) = some y ∧
        ∀ t, t < simulationTime code x → evaluator code x t = none

def general_recursive_models (D : Type*) [Primcodable D] :
    Set (computational_model D) :=
  {M | encoded_partrec M.compute ∧ effective_evaluator M.evaluator}

def valid_time_bound_observation {D : Type*}
    (M : computational_model D)
    (atb : computational_model D → D → ℕ)
    (o : time_bound_observation D) : Prop :=
  M.compute o.1 = pure o.2.1 ∧ o.2.2 = atb M o.1

def enumerates_time_bound_observations {D : Type*}
    (M : computational_model D)
    (atb : computational_model D → D → ℕ)
    (I : Set D)
    (w : ℕ → time_bound_observation D) : Prop :=
  (∀ n, (w n).1 ∈ I ∧ valid_time_bound_observation M atb (w n)) ∧
    ∀ x ∈ I, ∃ n, (w n).1 = x

structure learning_algorithm (D : Type*) [Primcodable D] where
  run : List (time_bound_observation D) → ℕ
  computable_run :
    encoded_partrec (run : List (time_bound_observation D) →. ℕ)

def representation_correct_on {D : Type*} [Primcodable D]
    (representations : representation_system D)
    (code : ℕ)
    (M : computational_model D)
    (I : Set D) : Prop :=
  ∀ x ∈ I, representations.semantics code x = M.compute x

def solves_time_bound_learning_problem {D : Type*} [Primcodable D]
    (representations : representation_system D)
    (atb : computational_model D → D → ℕ)
    (L : learning_algorithm D) : Prop :=
  ∀ M ∈ general_recursive_models D,
    ∀ I : Set D, I ⊆ model_domain M →
      ∀ w : ℕ → time_bound_observation D,
        enumerates_time_bound_observations M atb I w →
          ∃ tstar code : ℕ, ∀ t : ℕ, tstar ≤ t →
            L.run ((List.range t).map w) = code ∧
              representation_correct_on representations code M I

def is_time_bound_observation_map {D : Type*} [Primcodable D]
    (atb : computational_model D → D → ℕ) : Prop :=
  ∀ M ∈ general_recursive_models D,
    ∃ c : ℕ, 0 < c ∧
      ∀ x ∈ model_domain M, M.runningTime x ≤ c * atb M x

def q_extended_church_turing_thesis {D : Type*} [Primcodable D]
    (representations : representation_system D)
    (q : ℕ → ℕ) : Prop :=
  Computable q ∧ Monotone q ∧
    ∀ M ∈ general_recursive_models D,
      ∃ code : ℕ, representations.semantics code = M.compute ∧
        ∀ x ∈ model_domain M,
          representations.simulationTime code x ≤ q (M.runningTime x)

theorem universal_tbo_learning {D : Type*} [Primcodable D]
    (representations : representation_system D)
    (q : ℕ → ℕ)
    (atb : computational_model D → D → ℕ)
    (hqECTT :
      q_extended_church_turing_thesis representations q)
    (hatb : is_time_bound_observation_map atb) :
    ∃ L : learning_algorithm D,
      solves_time_bound_learning_problem representations atb L := by sorry

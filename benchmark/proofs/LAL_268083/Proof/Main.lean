import Architect
import Mathlib.Computability.Partrec

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:computational-model"
  (statement := /-- A computational model over a domain $D$ consists of a
  partial function $f_M:D\partialto D$, a step-indexed evaluator
  $E_M:D\times\mathbb N\to D\cup\{\bot\}$, and a running-time function
  $t_M:D\to\mathbb N$.  For every $x,y\in D$, one has $f_M(x)=y$ if and only
  if $E_M(x,s)=y$ for some $s$.  Whenever $f_M(x)=y$, the integer $t_M(x)$ is
  the first such stage: $E_M(x,t_M(x))=y$ and
  $E_M(x,s)=\bot$ for every $s<t_M(x)$. -/)
  (title := /-- Computational model -/)
  (latexEnv := "definition")]
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

@[blueprint "def:time-bound-observation"
  (statement := /-- A time-bound observation over $D$ is a triple $(x,y,b)$,
  recording an input, an output, and a natural-number time bound. -/)
  (title := /-- Time-bound observation -/)
  (latexEnv := "definition")]
abbrev time_bound_observation (D : Type*) :=
  D × D × ℕ

@[blueprint "def:model-domain"
  (statement := /-- The domain $D_M$ of a computational model $M$ is the set of
  inputs on which its partial function is defined. -/)
  (title := /-- Domain of a computational model -/)
  (latexEnv := "definition")]
def model_domain {D : Type*} (M : computational_model D) : Set D :=
  {x | (M.compute x).Dom}

@[blueprint "def:encoded-partrec"
  (statement := /-- Let $A$ and $B$ be effectively enumerable types equipped
  with fixed primitive-recursive codings in $\mathbb N$.  A partial map
  $f:A\partialto B$ is partial recursive relative to these codings if the
  partial map on natural-number codes obtained by decoding the input, applying
  $f$, and encoding the output is partial recursive. -/)
  (title := /-- Partial recursiveness on enumerable types -/)
  (latexEnv := "definition")]
def encoded_partrec {A B : Type*} [Primcodable A] [Primcodable B]
    (f : A →. B) : Prop :=
  Nat.Partrec fun n =>
    Part.bind (Encodable.decode (α := A) n) fun a =>
      (f a).map Encodable.encode

@[blueprint "def:effective-evaluator"
  (statement := /-- Let $A$ and $B$ be effectively enumerable types with fixed
  primitive-recursive codings.  A step-indexed evaluator
  $E:A\times\mathbb N\to B\cup\{\bot\}$ is effective if the total map
  $(a,t)\mapsto E(a,t)$, including its distinguished non-halting value
  $\bot$, is recursive relative to these encodings in the sense of
  \cref{def:encoded-partrec}. -/)
  (title := /-- Effective step-indexed evaluators -/)
  (latexEnv := "definition")]
def effective_evaluator {A B : Type*} [Primcodable A] [Primcodable B]
    (eval : A → ℕ → Option B) : Prop :=
  encoded_partrec fun p : A × ℕ => pure (eval p.1 p.2)

@[blueprint "def:representation-system"
  (statement := /-- A representation system on an effectively enumerable
  domain $D$ with a fixed primitive-recursive coding assigns to every code
  $r\in\mathbb N$ a partial function
  $\mathfrak S(r):D\partialto D$.  It is equipped with an effective
  step-indexed evaluator $E_{\mathfrak S}$ and a running-time function
  $T:\mathbb N\times D\to\mathbb N$.  For all $r\in\mathbb N$ and
  $x,y\in D$, the equality $\mathfrak S(r)(x)=y$ holds if and only if
  $E_{\mathfrak S}(r,x,s)=y$ for some $s$; whenever this equality holds,
  $T(r,x)$ is the first such stage. -/)
  (title := /-- Effective representation systems -/)
  (latexEnv := "definition")]
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

@[blueprint "def:general-recursive-models"
  (statement := /-- Fix an effectively enumerable domain $D$ and a
  primitive-recursive coding of $D$ in $\mathbb N$.  The class
  $\mathcal M_D$ consists of precisely those
  computational models whose partial functions are recursive relative to this
  encoding in the sense of \cref{def:encoded-partrec} and whose certified
  step-indexed evaluators are effective in the sense of
  \cref{def:effective-evaluator}. -/)
  (title := /-- Models of general recursive functions -/)
  (latexEnv := "definition")]
def general_recursive_models (D : Type*) [Primcodable D] :
    Set (computational_model D) :=
  {M | encoded_partrec M.compute ∧ effective_evaluator M.evaluator}

@[blueprint "def:valid-time-bound-observation"
  (statement := /-- Let $M$ be a computational model and let
  $a_{\mathrm{tb}}$ be an observation map.  A triple $(x,y,b)$ is valid when
  $M(x)$ is defined with value $y$ and
  $b=a_{\mathrm{tb}}(M,x)$. -/)
  (title := /-- Validity of a time-bound observation -/)
  (latexEnv := "definition")]
def valid_time_bound_observation {D : Type*}
    (M : computational_model D)
    (atb : computational_model D → D → ℕ)
    (o : time_bound_observation D) : Prop :=
  M.compute o.1 = pure o.2.1 ∧ o.2.2 = atb M o.1

@[blueprint "def:enumerates-time-bound-observations"
  (statement := /-- A stream $w:\mathbb N\to D\times D\times\mathbb N$
  enumerates the time-bound observations of $M$ on an input source $I$ when
  every term of the stream is a valid observation with input in $I$, and every
  $x\in I$ occurs as the input of some term of the stream. -/)
  (title := /-- Enumeration of restricted observations -/)
  (latexEnv := "definition")]
def enumerates_time_bound_observations {D : Type*}
    (M : computational_model D)
    (atb : computational_model D → D → ℕ)
    (I : Set D)
    (w : ℕ → time_bound_observation D) : Prop :=
  (∀ n, (w n).1 ∈ I ∧ valid_time_bound_observation M atb (w n)) ∧
    ∀ x ∈ I, ∃ n, (w n).1 = x

@[blueprint "def:learning-algorithm"
  (statement := /-- Fix an effectively enumerable domain $D$ and a
  primitive-recursive coding of $D$ in $\mathbb N$.  A learning algorithm on
  $D$ is a map from finite lists of
  time-bound observations to natural-number representation codes whose induced
  map on encoded lists is partial recursive in the sense of
  \cref{def:encoded-partrec}. -/)
  (title := /-- Learning algorithm -/)
  (latexEnv := "definition")]
structure learning_algorithm (D : Type*) [Primcodable D] where
  run : List (time_bound_observation D) → ℕ
  computable_run :
    encoded_partrec (run : List (time_bound_observation D) →. ℕ)

@[blueprint "def:representation-correct-on"
  (statement := /-- Relative to an effective representation system with
  semantics $\mathfrak S$, a representation code $r$ is correct for $M$ on
  $I$ when
  $\mathfrak S(r)(x)=f_M(x)$ for every $x\in I$. -/)
  (title := /-- Correctness on an input source -/)
  (latexEnv := "definition")]
def representation_correct_on {D : Type*} [Primcodable D]
    (representations : representation_system D)
    (code : ℕ)
    (M : computational_model D)
    (I : Set D) : Prop :=
  ∀ x ∈ I, representations.semantics code x = M.compute x

@[blueprint "def:solves-time-bound-learning-problem"
  (statement := /-- A learner $L$ solves the
  $(\mathcal M_D,a_{\mathrm{tb}})$--learning problem when, for every
  $M\in\mathcal M_D$, every input source $I\subseteq D_M$, and every
  surjective stream of valid time-bound observations on $I$, there are a finite
  stage $t^\star$ and a representation code $r$ such that at every
  $t\geq t^\star$ the learner returns $r$, and $\mathfrak S(r)$ agrees with
  $f_M$ on $I$. -/)
  (title := /-- The time-bound-observation learning problem -/)
  (latexEnv := "definition")]
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

@[blueprint "def:is-time-bound-observation-map"
  (statement := /-- An observation map $a_{\mathrm{tb}}$ is time-bounding when,
  for every $M\in\mathcal M_D$, there is a positive model-dependent constant
  $c_M$ such that
  $t_M(x)\leq c_M a_{\mathrm{tb}}(M,x)$ for every $x\in D_M$. -/)
  (title := /-- Time-bound observation maps -/)
  (latexEnv := "definition")]
def is_time_bound_observation_map {D : Type*} [Primcodable D]
    (atb : computational_model D → D → ℕ) : Prop :=
  ∀ M ∈ general_recursive_models D,
    ∃ c : ℕ, 0 < c ∧
      ∀ x ∈ model_domain M, M.runningTime x ≤ c * atb M x

@[blueprint "def:q-extended-church-turing-thesis"
  (statement := /-- Fix an enumerable domain $D$, an effective representation
  system with semantics $\mathfrak S$ and certified running time $T$, and a
  function $q:\mathbb N\to\mathbb N$.  The $q$-Extended Church--Turing
  Thesis asserts that $q$ is computable and monotone and that every
  $M\in\mathcal M_D$ has a code $r$ satisfying
  $\mathfrak S(r)=f_M$ and
  $T(r,x)\leq q(t_M(x))$ for every $x\in D_M$. -/)
  (title := /-- The $q$-Extended Church--Turing Thesis -/)
  (latexEnv := "definition")]
def q_extended_church_turing_thesis {D : Type*} [Primcodable D]
    (representations : representation_system D)
    (q : ℕ → ℕ) : Prop :=
  Computable q ∧ Monotone q ∧
    ∀ M ∈ general_recursive_models D,
      ∃ code : ℕ, representations.semantics code = M.compute ∧
        ∀ x ∈ model_domain M,
          representations.simulationTime code x ≤ q (M.runningTime x)

@[blueprint "thm:universal-tbo-learning"
  (statement := /-- Let $D$ be an effectively enumerable domain equipped with
  a fixed primitive-recursive coding, let $(\mathfrak S,T)$ be an effective
  representation system on $D$, let $q:\mathbb N\to\mathbb N$, and let
  $a_{\mathrm{tb}}$ assign a natural number to each model--input pair.
  Suppose that the $q$-Extended Church--Turing Thesis holds and that, for every
  $M\in\mathcal M_D$, there is a positive constant $c_M$ such that
  $t_M(x)\leq c_Ma_{\mathrm{tb}}(M,x)$ for every $x\in D_M$.  Then there
  exists a learning algorithm $L$, computable on encoded finite observation
  lists, with the following property.  For every $M\in\mathcal M_D$, every
  $I\subseteq D_M$, and every stream $w$ enumerating the valid
  $a_{\mathrm{tb}}$-observations on $I$, there exist a stage $t^\star$ and a
  code $r$ such that, for every $t\geq t^\star$, the learner applied to the
  first $t$ observations returns $r$, and $\mathfrak S(r)(x)=f_M(x)$ for
  every $x\in I$. -/)
  (proof := /-- Encode a candidate representation code $r$ and a positive-time
  multiplier $c$ by a single natural number.  Given an observation $(x,y,b)$,
  call $(r,c)$ compatible with it when the effective evaluator of
  $\mathfrak S(r)$ returns $y$ at some stage at most $q(cb)$.  On a finite list
  of observations, the learner returns the code component of the least
  compatible encoded pair whose index is at most the list length; a computable
  fallback index ensures that this bounded search is always defined.  The
  computability of $q$ from \cref{def:q-extended-church-turing-thesis}, the
  effectiveness of the representation evaluator from
  \cref{def:representation-system}, finite Boolean recursion, and partial
  recursive minimization show that this learner satisfies the computability
  requirement in \cref{def:learning-algorithm}.

  Fix $M\in\mathcal M_D$, a set $I\subseteq D_M$, and a stream enumerating the
  valid observations on $I$.  By
  \cref{def:q-extended-church-turing-thesis}, choose a code $r_0$ representing
  $M$ whose simulation time is at most $q(t_M(x))$.  By
  \cref{def:is-time-bound-observation-map}, choose $c_0>0$ with
  $t_M(x)\leq c_0a_{\mathrm{tb}}(M,x)$ on $D_M$.  Monotonicity of $q$ implies
  that $(r_0,c_0)$ is compatible with every observation in the stream.  Hence
  a least encoded pair $(r_\star,c_\star)$ compatible with every stream entry
  exists.  Every smaller pair fails on some entry; since there are only
  finitely many smaller pairs, one finite stage contains a failure witness for
  all of them.  Once the list length also exceeds the index of
  $(r_\star,c_\star)$, the learner therefore returns $r_\star$ forever.

  Finally, for each $x\in I$, surjectivity of the observation stream supplies
  an entry $(x,y,a_{\mathrm{tb}}(M,x))$.  Compatibility gives an evaluator
  stage returning $y$, so evaluator correctness in
  \cref{def:representation-system} yields
  $\mathfrak S(r_\star)(x)=y$; validity of the observation gives
  $f_M(x)=y$.  Thus $r_\star$ is correct on $I$ in the sense of
  \cref{def:representation-correct-on}, and the stabilization just proved is
  precisely the condition in \cref{def:solves-time-bound-learning-problem}. -/)
  (title := /-- Universal TBO-Learning -/)
  (latexEnv := "theorem")]
theorem universal_tbo_learning {D : Type*} [Primcodable D]
    (representations : representation_system D)
    (q : ℕ → ℕ)
    (atb : computational_model D → D → ℕ)
    (hqECTT :
      q_extended_church_turing_thesis representations q)
    (hatb : is_time_bound_observation_map atb) :
    ∃ L : learning_algorithm D,
      solves_time_bound_learning_problem representations atb L := by
  rcases hqECTT with ⟨hqcomp, hqmono, hrepr⟩
  letI := Encodable.decidableEqOfEncodable D
  have heval : Computable (fun p : (ℕ × D) × ℕ =>
      representations.evaluator p.1.1 p.1.2 p.2) :=
    representations.evaluator_effective
  let accepts (code : ℕ) (o : time_bound_observation D) (s : ℕ) : Bool :=
    decide (representations.evaluator code o.1 s = some o.2.1)
  have haccepts : Computable (fun p : (ℕ × time_bound_observation D) × ℕ =>
      accepts p.1.1 p.1.2 p.2) := by
    let hcode : Computable (fun p : (ℕ × time_bound_observation D) × ℕ => p.1.1) :=
      Computable.fst.comp Computable.fst
    let ho : Computable (fun p : (ℕ × time_bound_observation D) × ℕ => p.1.2) :=
      Computable.snd.comp Computable.fst
    let hx : Computable (fun p : (ℕ × time_bound_observation D) × ℕ => p.1.2.1) :=
      Computable.fst.comp ho
    let hy : Computable (fun p : (ℕ × time_bound_observation D) × ℕ => p.1.2.2.1) :=
      Computable.fst.comp (Computable.snd.comp ho)
    let hs : Computable (fun p : (ℕ × time_bound_observation D) × ℕ => p.2) :=
      Computable.snd
    exact (Primrec.eq.decide.to_comp.comp
      (heval.comp ((hcode.pair hx).pair hs))
      (Computable.option_some.comp hy)).of_eq (by
        intro p
        simp [accepts])
  let witness (code c : ℕ) (o : time_bound_observation D) : Bool :=
    Nat.rec false (fun s acc => acc || accepts code o s) (q (c * o.2.2) + 1)
  have hwitness : Computable (fun p : (ℕ × ℕ) × time_bound_observation D =>
      witness p.1.1 p.1.2 p.2) := by
    let hcode : Computable (fun p : (ℕ × ℕ) × time_bound_observation D => p.1.1) :=
      Computable.fst.comp Computable.fst
    let hc : Computable (fun p : (ℕ × ℕ) × time_bound_observation D => p.1.2) :=
      Computable.snd.comp Computable.fst
    let ho : Computable (fun p : (ℕ × ℕ) × time_bound_observation D => p.2) :=
      Computable.snd
    let hb : Computable (fun p : (ℕ × ℕ) × time_bound_observation D => p.2.2.2) :=
      Computable.snd.comp (Computable.snd.comp ho)
    let hcount : Computable (fun p : (ℕ × ℕ) × time_bound_observation D =>
        q (p.1.2 * p.2.2.2) + 1) :=
      Computable.succ.comp (hqcomp.comp (Primrec.nat_mul.to_comp.comp hc hb))
    let hstep : Computable₂ (fun p : (ℕ × ℕ) × time_bound_observation D =>
        fun z : ℕ × Bool => z.2 || accepts p.1.1 p.2 z.1) := by
      let hcode' : Computable (fun z : ((ℕ × ℕ) × time_bound_observation D) ×
          (ℕ × Bool) => z.1.1.1) := hcode.comp Computable.fst
      let ho' : Computable (fun z : ((ℕ × ℕ) × time_bound_observation D) ×
          (ℕ × Bool) => z.1.2) := ho.comp Computable.fst
      let hs : Computable (fun z : ((ℕ × ℕ) × time_bound_observation D) ×
          (ℕ × Bool) => z.2.1) := Computable.fst.comp Computable.snd
      let hacc : Computable (fun z : ((ℕ × ℕ) × time_bound_observation D) ×
          (ℕ × Bool) => z.2.2) := Computable.snd.comp Computable.snd
      exact (Primrec.or.to_comp.comp hacc
        (haccepts.comp ((hcode'.pair ho').pair hs))).to₂.of_eq (by
          rintro ⟨p, z⟩
          rfl)
    exact (Computable.nat_rec hcount (Computable.const false) hstep).of_eq (by
      intro p
      simp [witness])
  let consistent (obs : List (time_bound_observation D)) (n : ℕ) : Bool :=
    let codeConstant := Nat.unpair n
    Nat.rec true (fun i acc =>
      acc && ((obs[i]?).map (fun o => witness codeConstant.1 codeConstant.2 o) |>.getD true))
      obs.length
  have hconsistent : Computable (fun p : List (time_bound_observation D) × ℕ =>
      consistent p.1 p.2) := by
    let hcount : Computable (fun p : List (time_bound_observation D) × ℕ => p.1.length) :=
      Computable.list_length.comp Computable.fst
    let hstep : Computable₂ (fun p : List (time_bound_observation D) × ℕ =>
        fun z : ℕ × Bool => z.2 &&
          ((p.1[z.1]?).map (fun o => witness (Nat.unpair p.2).1 (Nat.unpair p.2).2 o)
            |>.getD true)) := by
      let hobs : Computable (fun z : (List (time_bound_observation D) × ℕ) ×
          (ℕ × Bool) => z.1.1) := Computable.fst.comp Computable.fst
      let hn : Computable (fun z : (List (time_bound_observation D) × ℕ) ×
          (ℕ × Bool) => z.1.2) := Computable.snd.comp Computable.fst
      let hi : Computable (fun z : (List (time_bound_observation D) × ℕ) ×
          (ℕ × Bool) => z.2.1) := Computable.fst.comp Computable.snd
      let hacc : Computable (fun z : (List (time_bound_observation D) × ℕ) ×
          (ℕ × Bool) => z.2.2) := Computable.snd.comp Computable.snd
      let hget := Computable.list_getElem?.comp hobs hi
      let hsome : Computable₂ (fun z : (List (time_bound_observation D) × ℕ) ×
          (ℕ × Bool) => fun o : time_bound_observation D =>
            z.2.2 && witness (Nat.unpair z.1.2).1 (Nat.unpair z.1.2).2 o) := by
        let hacc' : Computable (fun u : ((List (time_bound_observation D) × ℕ) ×
            (ℕ × Bool)) × time_bound_observation D => u.1.2.2) :=
          hacc.comp Computable.fst
        let hn' : Computable (fun u : ((List (time_bound_observation D) × ℕ) ×
            (ℕ × Bool)) × time_bound_observation D => u.1.1.2) :=
          hn.comp Computable.fst
        let hp : Computable (fun u : ((List (time_bound_observation D) × ℕ) ×
            (ℕ × Bool)) × time_bound_observation D => Nat.unpair u.1.1.2) :=
          Computable.unpair.comp hn'
        let hcode : Computable (fun u : ((List (time_bound_observation D) × ℕ) ×
            (ℕ × Bool)) × time_bound_observation D => (Nat.unpair u.1.1.2).1) :=
          Computable.fst.comp hp
        let hc : Computable (fun u : ((List (time_bound_observation D) × ℕ) ×
            (ℕ × Bool)) × time_bound_observation D => (Nat.unpair u.1.1.2).2) :=
          Computable.snd.comp hp
        let ho : Computable (fun u : ((List (time_bound_observation D) × ℕ) ×
            (ℕ × Bool)) × time_bound_observation D => u.2) := Computable.snd
        exact (Primrec.and.to_comp.comp hacc'
          (hwitness.comp ((hcode.pair hc).pair ho))).to₂.of_eq (by
            rintro ⟨z, o⟩
            rfl)
      exact (Computable.option_casesOn hget hacc hsome).to₂.of_eq (by
        rintro ⟨p, z⟩
        cases h : p.1[z.1]? <;> simp [h])
    exact (Computable.nat_rec hcount (Computable.const true) hstep).of_eq (by
      intro p
      simp [consistent])
  let eligible (obs : List (time_bound_observation D)) (n : ℕ) : Bool :=
    decide (n = obs.length + 1) || (decide (n ≤ obs.length) && consistent obs n)
  have heligible : Computable (fun p : List (time_bound_observation D) × ℕ =>
      eligible p.1 p.2) := by
    let hobs : Computable (fun p : List (time_bound_observation D) × ℕ => p.1) :=
      Computable.fst
    let hn : Computable (fun p : List (time_bound_observation D) × ℕ => p.2) :=
      Computable.snd
    let hlen : Computable (fun p : List (time_bound_observation D) × ℕ => p.1.length) :=
      Computable.list_length.comp hobs
    let hsucc : Computable (fun p : List (time_bound_observation D) × ℕ =>
        p.1.length + 1) := Computable.succ.comp hlen
    exact (Primrec.or.to_comp.comp
      (Primrec.eq.decide.to_comp.comp hn hsucc)
      (Primrec.and.to_comp.comp
        (Primrec.nat_le.decide.to_comp.comp hn hlen) hconsistent)).of_eq (by
          intro p
          simp [eligible])
  let eligibleProp (obs : List (time_bound_observation D)) (n : ℕ) : Prop :=
    eligible obs n
  have hexists (obs : List (time_bound_observation D)) : ∃ n, eligibleProp obs n := by
    refine ⟨obs.length + 1, ?_⟩
    simp [eligibleProp, eligible]
  let chosen (obs : List (time_bound_observation D)) : ℕ := Nat.find (hexists obs)
  have hchosen : Computable chosen := by
    have hrfind : Partrec (fun obs : List (time_bound_observation D) =>
        Nat.rfind fun n => Part.some (eligible obs n)) :=
      Partrec.rfind heligible.to₂.partrec₂
    refine hrfind.of_eq_tot fun obs => ?_
    simp +contextual [chosen, eligibleProp, Nat.find_spec]
    exact Nat.find_spec (hexists obs)
  let learner : learning_algorithm D :=
    { run := fun obs => (Nat.unpair (chosen obs)).1
      computable_run := Computable.fst.comp (Computable.unpair.comp hchosen) }
  refine ⟨learner, ?_⟩
  have hwitness_iff (code c : ℕ) (o : time_bound_observation D) :
      witness code c o = true ↔ ∃ s ≤ q (c * o.2.2),
        representations.evaluator code o.1 s = some o.2.1 := by
    have hscan : ∀ k : ℕ,
        Nat.rec false (fun s acc => acc || accepts code o s) k = true ↔
          ∃ s < k, accepts code o s = true := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          simp only [Nat.rec_add_one, Bool.or_eq_true, ih]
          constructor
          · rintro (⟨s, hs, ha⟩ | ha)
            · exact ⟨s, Nat.lt.step hs, ha⟩
            · exact ⟨k, Nat.lt_succ_self k, ha⟩
          · rintro ⟨s, hs, ha⟩
            by_cases hsk : s < k
            · exact Or.inl ⟨s, hsk, ha⟩
            · right
              have : s = k := by omega
              simpa [this] using ha
    change Nat.rec false (fun s acc => acc || accepts code o s)
      (q (c * o.2.2) + 1) = true ↔ _
    rw [hscan (q (c * o.2.2) + 1)]
    constructor
    · rintro ⟨s, hs, ha⟩
      refine ⟨s, by omega, ?_⟩
      simpa [accepts] using ha
    · rintro ⟨s, hs, ha⟩
      refine ⟨s, by omega, ?_⟩
      simp [accepts, ha]
  have hconsistent_iff (obs : List (time_bound_observation D)) (n : ℕ) :
      consistent obs n = true ↔
        ∀ i < obs.length,
          ((obs[i]?).map (fun o =>
            witness (Nat.unpair n).1 (Nat.unpair n).2 o) |>.getD true) = true := by
    have hscan : ∀ k : ℕ,
        Nat.rec true (fun i acc => acc &&
          ((obs[i]?).map (fun o =>
            witness (Nat.unpair n).1 (Nat.unpair n).2 o) |>.getD true)) k = true ↔
          ∀ i < k, ((obs[i]?).map (fun o =>
            witness (Nat.unpair n).1 (Nat.unpair n).2 o) |>.getD true) = true := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          simp only [Nat.rec_add_one, Bool.and_eq_true, ih]
          constructor
          · rintro ⟨hall, hk⟩ i hi
            by_cases hik : i < k
            · exact hall i hik
            · have : i = k := by omega
              simpa [this] using hk
          · intro hall
            exact ⟨fun i hi => hall i (Nat.lt.step hi),
              hall k (Nat.lt_succ_self k)⟩
    simpa [consistent] using hscan obs.length
  intro M hM I hI w hw
  rcases hw with ⟨hwvalid, hwsurj⟩
  rcases hrepr M hM with ⟨code₀, hcode₀, htime₀⟩
  rcases hatb M hM with ⟨c₀, hc₀, hatb₀⟩
  classical
  let n₀ := Nat.pair code₀ c₀
  have hn₀ (k : ℕ) : witness (Nat.unpair n₀).1 (Nat.unpair n₀).2 (w k) = true := by
    rw [hwitness_iff]
    have hvalid := (hwvalid k).2
    rcases hvalid with ⟨hcompute, hbound⟩
    have hdom : (w k).1 ∈ model_domain M := by
      simp [model_domain, hcompute]
    have hsem : representations.semantics code₀ (w k).1 = pure (w k).2.1 := by
      rw [hcode₀]
      exact hcompute
    have hsim := (representations.simulationTime_spec code₀ (w k).1 (w k).2.1 hsem).1
    refine ⟨representations.simulationTime code₀ (w k).1, ?_, ?_⟩
    rw [show (Nat.unpair n₀).2 = c₀ by simp [n₀], hbound]
    exact (htime₀ (w k).1 hdom).trans
      (hqmono (hatb₀ (w k).1 hdom))
    simpa [n₀] using hsim
  let persistent (n : ℕ) : Prop :=
    ∀ k, witness (Nat.unpair n).1 (Nat.unpair n).2 (w k) = true
  have hpersistent : ∃ n, persistent n := ⟨n₀, hn₀⟩
  let nstar := Nat.find hpersistent
  have hnstar : persistent nstar := by
    simpa [nstar] using Nat.find_spec hpersistent
  have hnstar_le : nstar ≤ n₀ := by
    simpa [nstar] using Nat.find_min' hpersistent hn₀
  have hfail : ∀ n < nstar, ∃ k,
      witness (Nat.unpair n).1 (Nat.unpair n).2 (w k) = false := by
    intro n hn
    have hnot : ¬persistent n :=
      Nat.find_min hpersistent (by simpa [nstar] using hn)
    by_contra hnone
    apply hnot
    intro k
    apply Bool.eq_true_of_not_eq_false
    intro hk
    exact hnone ⟨k, hk⟩
  have hboundedFailures : ∀ N : ℕ,
      (∀ n < N, ∃ k,
        witness (Nat.unpair n).1 (Nat.unpair n).2 (w k) = false) →
      ∃ T, ∀ n < N, ∃ k < T,
        witness (Nat.unpair n).1 (Nat.unpair n).2 (w k) = false := by
    intro N hN
    induction N with
    | zero => exact ⟨0, by omega⟩
    | succ N ih =>
        obtain ⟨T, hT⟩ := ih (fun n hn => hN n (Nat.lt.step hn))
        obtain ⟨k, hk⟩ := hN N (Nat.lt_succ_self N)
        refine ⟨max T (k + 1), ?_⟩
        intro n hn
        by_cases hlt : n < N
        · obtain ⟨j, hj, hjfalse⟩ := hT n hlt
          exact ⟨j, hj.trans_le (Nat.le_max_left _ _), hjfalse⟩
        · have hne : n = N := by omega
          subst n
          exact ⟨k, (Nat.lt_succ_self k).trans_le (Nat.le_max_right _ _), hk⟩
  obtain ⟨T, hT⟩ := hboundedFailures nstar hfail
  let codeStar := (Nat.unpair nstar).1
  have hcorrect : representation_correct_on representations codeStar M I := by
    intro x hx
    obtain ⟨k, hk⟩ := hwsurj x hx
    have hwit := hnstar k
    rw [hwitness_iff] at hwit
    obtain ⟨s, hs, hevalout⟩ := hwit
    have hsem : representations.semantics codeStar (w k).1 = pure (w k).2.1 :=
      (representations.evaluator_correct codeStar (w k).1 (w k).2.1).2 ⟨s, hevalout⟩
    have hcompute := (hwvalid k).2.1
    rw [← hk, hsem, hcompute]
  refine ⟨max T nstar, codeStar, ?_⟩
  intro t ht
  have hTt : T ≤ t := (Nat.le_max_left T nstar).trans ht
  have hnstart : nstar ≤ t := (Nat.le_max_right T nstar).trans ht
  let obs := (List.range t).map w
  have hlen : obs.length = t := by simp [obs]
  have hstarCons : consistent obs nstar = true := by
    apply (hconsistent_iff obs nstar).2
    intro i hi
    have hit : i < t := by simpa [hlen] using hi
    have hget : obs[i]? = some (w i) := by
      simp [obs, hit]
    rw [hget]
    simp [hnstar i]
  have hfalseCons : ∀ n < nstar, consistent obs n = false := by
    intro n hn
    obtain ⟨k, hkT, hkfalse⟩ := hT n hn
    have hkt : k < t := hkT.trans_le hTt
    have hklen : k < obs.length := by simpa [hlen] using hkt
    have hget : obs[k]? = some (w k) := by
      simp [obs, hkt]
    apply Bool.eq_false_of_not_eq_true
    intro hcons
    have hall := (hconsistent_iff obs n).1 hcons k hklen
    rw [hget] at hall
    simp [hkfalse] at hall
  have helstar : eligibleProp obs nstar := by
    simp [eligibleProp, eligible, hlen, hnstart, hstarCons]
  have hellower : ∀ n < nstar, ¬eligibleProp obs n := by
    intro n hn
    have hnt : n < t + 1 := by omega
    simp [eligibleProp, eligible, hlen, hfalseCons n hn]
    omega
  have hchosen_eq : chosen obs = nstar := by
    apply Nat.le_antisymm
    · simpa [chosen] using Nat.find_min' (hexists obs) helstar
    · by_contra hnot
      have hlt : chosen obs < nstar := by omega
      have hspec : eligibleProp obs (chosen obs) := by
        simpa [chosen] using Nat.find_spec (hexists obs)
      exact (hellower (chosen obs) hlt) hspec
  constructor
  · change learner.run obs = codeStar
    simp [learner, hchosen_eq, codeStar]
  · exact hcorrect

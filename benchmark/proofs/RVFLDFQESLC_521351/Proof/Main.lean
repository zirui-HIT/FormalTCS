import Architect
import Mathlib.Algebra.Field.ZMod
import Mathlib.InformationTheory.Hamming
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option linter.all false
set_option maxHeartbeats 500000

noncomputable section

@[blueprint "def:binary-word"
  (statement := /-- For a natural number $n$, a binary word of length $n$ is a function from the coordinate set $\operatorname{Fin}(n)$ to the binary field $\mathbb{F}_2 = \mathbb{Z}/2\mathbb{Z}$. -/)
  (title := /-- Binary words -/)
  (latexEnv := "definition")]
abbrev binary_word (n : ℕ) := Fin n → ZMod 2

@[blueprint "def:binary-linear-code"
  (statement := /-- A binary linear code with message length $k$ and blocklength $n$ consists of an injective $\mathbb{F}_2$-linear encoding map from the binary words of length $k$ to the binary words of length $n$. -/)
  (title := /-- Binary linear codes -/)
  (latexEnv := "definition")]
structure binary_linear_code (k n : ℕ) where
  encode : binary_word k →ₗ[ZMod 2] binary_word n
  injective : Function.Injective encode

@[blueprint "def:binary-oracle-tree"
  (statement := /-- Let $n$ be a natural number and let $A$ be an output type. A deterministic adaptive binary oracle tree either returns an element of $A$, or queries one coordinate in $\operatorname{Fin}(n)$ and continues along one of two subtrees according as the oracle symbol is zero or one. -/)
  (title := /-- Deterministic adaptive binary oracle trees -/)
  (latexEnv := "definition")]
inductive binary_oracle_tree (n : ℕ) (A : Type) where
  | output : A → binary_oracle_tree n A
  | query : Fin n → binary_oracle_tree n A → binary_oracle_tree n A →
      binary_oracle_tree n A

@[blueprint "def:binary-oracle-tree-eval"
  (statement := /-- Given a binary oracle word $y$, evaluation of a deterministic adaptive oracle tree follows the zero branch when the queried symbol of $y$ is zero and the one branch otherwise, and returns the output at the reached leaf. -/)
  (title := /-- Evaluation of an adaptive oracle tree -/)
  (latexEnv := "definition")]
def binary_oracle_tree_eval {n : ℕ} {A : Type} (y : binary_word n) :
    binary_oracle_tree n A → A
  | .output a => a
  | .query i zeroBranch oneBranch =>
      if y i = 0 then
        binary_oracle_tree_eval y zeroBranch
      else
        binary_oracle_tree_eval y oneBranch

@[blueprint "def:binary-oracle-tree-depth"
  (statement := /-- The depth of a deterministic adaptive oracle tree is zero at an output leaf and is one plus the maximum of the depths of the two branches at a query node. Thus its depth is the largest number of oracle queries on any execution path. -/)
  (title := /-- Query depth of an adaptive oracle tree -/)
  (latexEnv := "definition")]
def binary_oracle_tree_depth {n : ℕ} {A : Type} : binary_oracle_tree n A → ℕ
  | .output _ => 0
  | .query _ zeroBranch oneBranch =>
      1 + max (binary_oracle_tree_depth zeroBranch) (binary_oracle_tree_depth oneBranch)

@[blueprint "def:randomized-adaptive-decoder"
  (statement := /-- A randomized adaptive decoder for binary words of length $n$, indexed by $m$ target positions and with output type $A$, assigns to each target position a discrete probability distribution on deterministic adaptive binary oracle trees with outputs in $A$. -/)
  (title := /-- Randomized adaptive oracle decoders -/)
  (latexEnv := "definition")]
abbrev randomized_adaptive_decoder (n m : ℕ) (A : Type) :=
  Fin m → PMF (binary_oracle_tree n A)

@[blueprint "def:randomized-adaptive-decoder-output"
  (statement := /-- For a randomized adaptive decoder $D$, an oracle word $y$, and a target position $i$, the output distribution is the push-forward of $D(i)$ under evaluation against $y$ as defined in \cref{def:binary-oracle-tree-eval}. -/)
  (title := /-- Output distribution of a randomized adaptive decoder -/)
  (latexEnv := "definition")]
def randomized_adaptive_decoder_output {n m : ℕ} {A : Type}
    (D : randomized_adaptive_decoder n m A) (y : binary_word n) (i : Fin m) : PMF A :=
  PMF.map (binary_oracle_tree_eval y) (D i)

@[blueprint "def:decoder-uses-at-most-queries"
  (statement := /-- A randomized adaptive decoder uses at most $q$ queries if, for every target position, every deterministic oracle tree in the support of the corresponding distribution has depth at most $q$, where depth is as in \cref{def:binary-oracle-tree-depth}. -/)
  (title := /-- Uniform query bound -/)
  (latexEnv := "definition")]
def decoder_uses_at_most_queries {n m q : ℕ} {A : Type}
    (D : randomized_adaptive_decoder n m A) : Prop :=
  ∀ i tree, tree ∈ (D i).support → binary_oracle_tree_depth tree ≤ q

@[blueprint "def:binary-decoding-error"
  (statement := /-- For a probability mass function $p$ on the binary field and a prescribed correct bit $a$, the decoding error is the total mass that $p$ assigns to symbols different from $a$. -/)
  (title := /-- Binary decoding error -/)
  (latexEnv := "definition")]
def binary_decoding_error (p : PMF (ZMod 2)) (a : ZMod 2) : ENNReal :=
  ∑' z, if z = a then 0 else p z

@[blueprint "def:binary-relaxed-decoding-error"
  (statement := /-- For a probability mass function $p$ on a binary symbol augmented by the abort symbol $\bot$, and for a prescribed correct bit $a$, the relaxed decoding error is the total mass assigned to outputs other than $a$ and $\bot$. -/)
  (title := /-- Binary relaxed decoding error -/)
  (latexEnv := "definition")]
def binary_relaxed_decoding_error (p : PMF (Option (ZMod 2))) (a : ZMod 2) : ENNReal :=
  ∑' z, if z = some a ∨ z = none then 0 else p z

@[blueprint "def:within-relative-hamming-radius"
  (statement := /-- Let $C$ be a binary linear code of blocklength $n$. A received word $y$ lies within relative Hamming radius $\delta$ of the encoding of a message $b$ if $\Delta(y,C(b)) \leq \delta n$, where $\Delta$ is Hamming distance. -/)
  (title := /-- Relative Hamming balls about codewords -/)
  (latexEnv := "definition")]
def within_relative_hamming_radius {k n : ℕ} (C : binary_linear_code k n)
    (δ : ℝ) (b : binary_word k) (y : binary_word n) : Prop :=
  (hammingDist y (C.encode b) : ℝ) ≤ δ * (n : ℝ)

@[blueprint "def:is-binary-rldc"
  (statement := /-- A binary linear code $C$ is a $(q,\delta,c,s)$-relaxed locally decodable code if there exists a possibly adaptive randomized decoder which makes at most $q$ queries, returns each requested message bit with probability at least $c$ on every uncorrupted codeword, and, for every received word within relative Hamming distance $\delta$ of a codeword, returns neither the requested bit nor $\bot$ with probability at most $s$. -/)
  (title := /-- Binary relaxed locally decodable codes -/)
  (latexEnv := "definition")]
def is_binary_rldc {k n : ℕ} (C : binary_linear_code k n)
    (q : ℕ) (δ c s : ℝ) : Prop :=
  ∃ D : randomized_adaptive_decoder n k (Option (ZMod 2)),
    decoder_uses_at_most_queries (q := q) D ∧
      (∀ b i,
        randomized_adaptive_decoder_output D (C.encode b) i (some (b i)) ≥
          ENNReal.ofReal c) ∧
      (∀ b i y,
        within_relative_hamming_radius C δ b y →
          binary_relaxed_decoding_error
              (randomized_adaptive_decoder_output D y i) (b i) ≤ ENNReal.ofReal s)

@[blueprint "def:is-binary-ldc"
  (statement := /-- A binary linear code $C$ is a $(q,\delta,c,s)$-locally decodable code if there exists a possibly adaptive randomized decoder which makes at most $q$ queries, returns each requested message bit with probability at least $c$ on every uncorrupted codeword, and has decoding error at most $s$ on every word within relative Hamming distance $\delta$ of a codeword. -/)
  (title := /-- Binary locally decodable codes -/)
  (latexEnv := "definition")]
def is_binary_ldc {k n : ℕ} (C : binary_linear_code k n)
    (q : ℕ) (δ c s : ℝ) : Prop :=
  ∃ D : randomized_adaptive_decoder n k (ZMod 2),
    decoder_uses_at_most_queries (q := q) D ∧
      (∀ b i,
        randomized_adaptive_decoder_output D (C.encode b) i (b i) ≥ ENNReal.ofReal c) ∧
      (∀ b i y,
        within_relative_hamming_radius C δ b y →
          binary_decoding_error (randomized_adaptive_decoder_output D y i) (b i) ≤
            ENNReal.ofReal s)

@[blueprint "def:is-binary-rlcc"
  (statement := /-- A binary linear code $C$ is a $(q,\delta,c,s)$-relaxed locally correctable code if there exists a possibly adaptive randomized decoder, indexed by codeword coordinates, which makes at most $q$ queries, returns the requested codeword symbol with probability at least $c$ on every uncorrupted codeword, and, within relative Hamming radius $\delta$, returns neither that symbol nor $\bot$ with probability at most $s$. -/)
  (title := /-- Binary relaxed locally correctable codes -/)
  (latexEnv := "definition")]
def is_binary_rlcc {k n : ℕ} (C : binary_linear_code k n)
    (q : ℕ) (δ c s : ℝ) : Prop :=
  ∃ D : randomized_adaptive_decoder n n (Option (ZMod 2)),
    decoder_uses_at_most_queries (q := q) D ∧
      (∀ b u,
        randomized_adaptive_decoder_output D (C.encode b) u (some (C.encode b u)) ≥
          ENNReal.ofReal c) ∧
      (∀ b u y,
        within_relative_hamming_radius C δ b y →
          binary_relaxed_decoding_error
              (randomized_adaptive_decoder_output D y u) (C.encode b u) ≤ ENNReal.ofReal s)

@[blueprint "def:is-binary-lcc"
  (statement := /-- A binary linear code $C$ is a $(q,\delta,c,s)$-locally correctable code if there exists a possibly adaptive randomized decoder, indexed by codeword coordinates, which makes at most $q$ queries, returns the requested codeword symbol with probability at least $c$ on every uncorrupted codeword, and has error at most $s$ within relative Hamming radius $\delta$. -/)
  (title := /-- Binary locally correctable codes -/)
  (latexEnv := "definition")]
def is_binary_lcc {k n : ℕ} (C : binary_linear_code k n)
    (q : ℕ) (δ c s : ℝ) : Prop :=
  ∃ D : randomized_adaptive_decoder n n (ZMod 2),
    decoder_uses_at_most_queries (q := q) D ∧
      (∀ b u,
        randomized_adaptive_decoder_output D (C.encode b) u (C.encode b u) ≥
          ENNReal.ofReal c) ∧
      (∀ b u y,
        within_relative_hamming_radius C δ b y →
          binary_decoding_error (randomized_adaptive_decoder_output D y u) (C.encode b u) ≤
            ENNReal.ofReal s)

@[blueprint "def:binary-soundness-threshold"
  (statement := /-- For a natural query bound $q$, define the binary soundness threshold by $s(q) = 2^{-\lfloor q/2\rfloor}$. Since $q$ is a natural number, this is the reciprocal of $2^{q/2}$, where the division in the exponent is natural-number division. -/)
  (title := /-- Binary soundness threshold -/)
  (latexEnv := "definition")]
def binary_soundness_threshold (q : ℕ) : ℝ :=
  ((2 : ℝ) ^ (q / 2))⁻¹

@[blueprint "def:binary-oracle-tree-transcript"
  (statement := /-- For a binary oracle word $y$ and a deterministic adaptive oracle tree $T$, the transcript is the ordered list of queried coordinates together with the answers read from $y$ along the unique execution path of $T$ on $y$. -/)
  (title := /-- Transcripts of adaptive binary oracle trees -/)
  (latexEnv := "definition")]
def binary_oracle_tree_transcript {n : ℕ} {A : Type}
    (y : binary_word n) : binary_oracle_tree n A → List (Fin n × ZMod 2)
  | .output _ => []
  | .query u zeroBranch oneBranch =>
      (u, y u) ::
        if y u = 0 then
          binary_oracle_tree_transcript y zeroBranch
        else
          binary_oracle_tree_transcript y oneBranch

@[blueprint "def:adaptive-switching-state"
  (statement := /-- Fix a binary linear code $C$, a message coordinate $i$, and a hitting set $H$. An adaptive switching state with $m$ record slots consists of a finite active set of records and one shared partial error $\eta$ with finite domain $K\subseteq H$. Each active record specifies a deterministic tree, a charged message, a nonnegative mass, and an $H$-supported continuation error extending $\eta$. The execution under the shared error and the execution under the continuation have identical transcripts through the common level, while the continuation reaches the nonabort value opposite to the charged message bit. The projection of active records to their tree-message charges is injective. -/)
  (title := /-- Common-error switching states -/)
  (latexEnv := "definition")]
structure adaptive_switching_state {k n m : ℕ}
    (C : binary_linear_code k n) (i : Fin k) (H : Finset (Fin n)) where
  domain : Finset (Fin n)
  domain_subset_hitting_set : ∀ u, u ∈ domain → u ∈ H
  shared_error : binary_word n
  shared_error_vanishes_off_domain : ∀ u, u ∉ domain → shared_error u = 0
  active : Finset (Fin m)
  tree : Fin m → binary_oracle_tree n (Option (ZMod 2))
  origin : Fin m → binary_word k
  level : ℕ
  continuation_error : Fin m → binary_word n
  continuation_supported_on_hitting_set :
    ∀ r, r ∈ active → ∀ u, continuation_error r u ≠ 0 → u ∈ H
  continuation_extends_shared_error :
    ∀ r, r ∈ active → ∀ u, u ∈ domain → continuation_error r u = shared_error u
  continuation : Fin m → List (Fin n × ZMod 2)
  continuation_is_suffix :
    ∀ r, r ∈ active →
      continuation r =
        (binary_oracle_tree_transcript
          (C.encode (origin r) + continuation_error r) (tree r)).drop level
  shared_prefix :
    ∀ r, r ∈ active →
      (binary_oracle_tree_transcript
        (C.encode (origin r) + shared_error) (tree r)).take level =
      (binary_oracle_tree_transcript
        (C.encode (origin r) + continuation_error r) (tree r)).take level
  continuation_is_wrong :
    ∀ r, r ∈ active →
      binary_oracle_tree_eval
        (C.encode (origin r) + continuation_error r) (tree r) =
          some (origin r i + 1)
  weight : Fin m → ENNReal
  charge_injective :
    Set.InjOn (fun r => (tree r, origin r)) (↑active : Set (Fin m))

@[blueprint "def:adaptive-switching-mass"
  (statement := /-- The certified mass of a switching state is the sum of the record weights over its finite active set. -/)
  (title := /-- Certified mass of a switching state -/)
  (latexEnv := "definition")]
def adaptive_switching_mass {k n m : ℕ} {C : binary_linear_code k n}
    {i : Fin k} {H : Finset (Fin n)}
    (S : adaptive_switching_state (m := m) C i H) : ENNReal :=
  ∑ r ∈ S.active, S.weight r

@[blueprint "def:adaptive-switching-new-coordinates"
  (statement := /-- For a switching state and a block length $\ell$, the common new-coordinate domain is the union, over all active records, of the coordinates in $H\setminus K$ occurring among the first $\ell$ entries of that record's specified continuation. In particular, shared coordinates occur only once in this union. -/)
  (title := /-- Common domain of newly queried coordinates -/)
  (latexEnv := "definition")]
def adaptive_switching_new_coordinates {k n m : ℕ} {C : binary_linear_code k n}
    {i : Fin k} {H : Finset (Fin n)}
    (S : adaptive_switching_state (m := m) C i H) (blockLength : ℕ) :
    Finset (Fin n) :=
  S.active.biUnion fun r =>
    (((S.continuation r).take blockLength).map Prod.fst).toFinset.filter
      fun u => u ∈ H ∧ u ∉ S.domain

@[blueprint "def:adaptive-switching-carry-balance"
  (statement := /-- Fix a common-error switching state $\mathcal S$ and a block length $\ell$, and put $U=U_\ell(\mathcal S)$ for the new common-coordinate set of \cref{def:adaptive-switching-new-coordinates}. An augmented pair $(r,e)$ is admissible if $r$ is active and $e$ extends the old shared error on $K$ and vanishes off $K\cup U$. The state is carry-balanced for blocks of length $\ell$ if there is a weight-preserving involution on all admissible augmented pairs which preserves activity, extension of the shared error, and support in $K\cup U$, and such that every orbit contains an augmented pair whose tree, evaluated on its own charged codeword plus its error, has the nonabort value opposite to its charged message bit. This requirement applies to every admissible pair, including pairs whose execution leaves the record's specified continuation at an adaptive query. -/)
  (title := /-- Carry balance for all switching records -/)
  (latexEnv := "definition")]
def adaptive_switching_carry_balance {k n m : ℕ} {C : binary_linear_code k n}
    {i : Fin k} {H : Finset (Fin n)}
    (S : adaptive_switching_state (m := m) C i H) (blockLength : ℕ) : Prop :=
  ∃ τ : (Fin m × binary_word n) → Fin m × binary_word n,
    Function.Involutive τ ∧
      ∀ r e,
        r ∈ S.active →
        (∀ u, u ∈ S.domain → e u = S.shared_error u) →
        (∀ u, u ∉ S.domain ∪ adaptive_switching_new_coordinates S blockLength →
          e u = 0) →
        (τ (r, e)).1 ∈ S.active ∧
        (∀ u, u ∈ S.domain → (τ (r, e)).2 u = S.shared_error u) ∧
        (∀ u, u ∉ S.domain ∪ adaptive_switching_new_coordinates S blockLength →
          (τ (r, e)).2 u = 0) ∧
        S.weight (τ (r, e)).1 = S.weight r ∧
        (binary_oracle_tree_eval (C.encode (S.origin r) + e) (S.tree r) =
            some (S.origin r i + 1) ∨
          binary_oracle_tree_eval
              (C.encode (S.origin (τ (r, e)).1) + (τ (r, e)).2)
              (S.tree (τ (r, e)).1) =
            some (S.origin (τ (r, e)).1 i + 1))

@[blueprint "lem:adaptive-switching-block"
  (statement := /-- Let $C\colon\mathbb F_2^k\to\mathbb F_2^n$ be a binary linear code, fix a message coordinate $i$, and let $H\subseteq[n]$ meet every set of at most $d$ coordinates representing the functional $b\mapsto b_i$ on codewords. Let $\mathcal S$ be a common-error switching state whose active trees have depth at most $d$ and compute $b_i$ on every codeword. Assume that $\mathcal S$ is carry-balanced for every admissible pair in its next two-query block in the sense of \cref{def:adaptive-switching-carry-balance}. If two further queries remain, then there are a switching state $\mathcal S'$ and a map $\jmath$ from its record slots to those of $\mathcal S$ such that: the new common domain is exactly the old domain together with the union of all $H$-coordinates occurring in the next two positions of the specified continuations; the new shared error extends the old one; $\jmath$ is injective on active records and preserves their trees and weights; the common level advances by two; and the certified mass of $\mathcal S'$ is at least half that of $\mathcal S$. Moreover, every retained record has a message difference $v$ for which its charged origin is the origin of its $\jmath$-predecessor translated by $v$. Either $v=0$, or $v_i=1$ and $C(v)$ vanishes both on the old common domain and on every coordinate outside $H$ occurring in the next two positions of that predecessor's specified continuation. -/)
  (proof := /-- Put $K=\mathcal S.\mathrm{domain}$ and let $U$ be the common new-coordinate set of \cref{def:adaptive-switching-new-coordinates}. Thus $K'=K\cup U$ is fixed before any record is retained. Identify an assignment $\xi\colon U\to\mathbb F_2$ with the unique full error $e_\xi$ which extends the old shared error on $K$, equals $\xi$ on $U$, and vanishes off $K'$. These are precisely the admissible errors occurring in \cref{def:adaptive-switching-carry-balance}.

Form the finite augmented table of all pairs $(r,e_\xi)$, where $r$ is active and $\xi$ ranges over all assignments on $U$, and give each pair weight $\mathcal S.\mathrm{weight}(r)$. Apply the involution in \cref{def:adaptive-switching-carry-balance} to this entire table. Its preservation clauses keep every image inside the table and give the two members of each orbit equal weight. Its certification clause says that each orbit contains a pair whose tree, on its charged codeword plus its own error, returns the nonabort value opposite to its charged bit. Retain every certified element of a singleton orbit and one certified element of each two-element orbit. The retained weight in each orbit is at least half of its total weight.

Let $\Xi$ be the finite set of assignments on $U$. Before selection, each $\xi\in\Xi$ contributes exactly \cref{def:adaptive-switching-mass}; hence the total table weight is $|\Xi|$ times that mass. The preceding orbit estimate gives retained total weight at least $|\Xi|/2$ times the mass. Partitioning the retained table by its error assignment and averaging therefore yields an assignment $\xi_*$ for which the retained record weight is at least one half of \cref{def:adaptive-switching-mass}.

Fix $e_*=e_{\xi_*}$. Let the active records of $\mathcal S'$ be those $r$ for which $(r,e_*)$ was retained, and keep their trees, charged origins, and weights unchanged. Set the new domain to $K'$, the new shared error and every retained continuation error to $e_*$, and the new level to $\mathcal S.\mathrm{level}+2$. The old domain and $U$ are contained in $H$, so $e_*$ is supported on $H$; by construction it extends the old shared error on $K$. Since the shared and continuation errors now coincide, their transcripts agree through the new level. Define each continuation to be the suffix, after that level, of its actual transcript. The defining certification of the retained pair gives the required wrong nonabort terminal value. The charge map remains injective because the active set was only restricted.

Take $\jmath$ to be the identity on record slots. It is injective on the new active set and preserves each retained tree and weight. For every retained record choose $v=0$; then its new origin is its predecessor's origin plus $v$, so the first alternative in the asserted origin relation holds. The definitions give the domain, extension, and level identities, while the choice of $\xi_*$ gives the required mass inequality. At no point is an execution assumed to follow its record's specified continuation after an adaptive branch divergence; that case is covered directly by the all-record involution hypothesis. -/)
  (title := /-- The common two-query switching transition -/)
  (latexEnv := "lemma")]
lemma adaptive_switching_block {k n m d : ℕ}
    (C : binary_linear_code k n) (i : Fin k) (H : Finset (Fin n))
    (S : adaptive_switching_state (m := m) C i H)
    (hdepth : ∀ r, r ∈ S.active →
      binary_oracle_tree_depth (S.tree r) ≤ d)
    (hcorrect : ∀ r, r ∈ S.active → ∀ b,
      binary_oracle_tree_eval (C.encode b) (S.tree r) = some (b i))
    (hhits : ∀ A : Finset (Fin n), A.card ≤ d →
      (∀ b, (∑ u ∈ A, C.encode b u) = b i) →
        ∃ u ∈ A, u ∈ H)
    (hcarry_balance : adaptive_switching_carry_balance S 2)
    (hqueries_remaining : S.level + 2 ≤ d) :
    ∃ (S' : adaptive_switching_state (m := m) C i H) (j : Fin m → Fin m),
      S'.domain = S.domain ∪ adaptive_switching_new_coordinates S 2 ∧
      S'.level = S.level + 2 ∧
      (∀ u, u ∈ S.domain → S'.shared_error u = S.shared_error u) ∧
      Set.InjOn j (↑S'.active : Set (Fin m)) ∧
      (∀ r, r ∈ S'.active →
        j r ∈ S.active ∧
        S'.tree r = S.tree (j r) ∧
        S'.weight r = S.weight (j r) ∧
        ∃ v : binary_word k,
          S'.origin r = S.origin (j r) + v ∧
          (v = 0 ∨
            (v i = 1 ∧
              ∀ u, u ∈ S.domain ∨
                (u ∉ H ∧
                  u ∈
                    (((S.continuation (j r)).take 2).map Prod.fst).toFinset) →
                C.encode v u = 0))) ∧
      adaptive_switching_mass S' ≥ adaptive_switching_mass S / 2 := by
  classical
  obtain ⟨e₀, he₀dom, he₀off, hmass⟩ :
      ∃ e₀ : binary_word n,
        (∀ u, u ∈ S.domain → e₀ u = S.shared_error u) ∧
        (∀ u, u ∉ S.domain ∪ adaptive_switching_new_coordinates S 2 → e₀ u = 0) ∧
        adaptive_switching_mass S / 2 ≤
          ∑ r ∈ S.active.filter (fun r =>
              binary_oracle_tree_eval (C.encode (S.origin r) + e₀) (S.tree r) =
                some (S.origin r i + 1)), S.weight r := by
    obtain ⟨τ, hτinv, hτ⟩ := hcarry_balance
    set U := adaptive_switching_new_coordinates S 2 with hUdef
    set E : Finset (binary_word n) :=
      Finset.univ.filter (fun e => (∀ u, u ∈ S.domain → e u = S.shared_error u) ∧
        (∀ u, u ∉ S.domain ∪ U → e u = 0)) with hEdef
    have hmemE : ∀ e : binary_word n, e ∈ E ↔
        ((∀ u, u ∈ S.domain → e u = S.shared_error u) ∧
          (∀ u, u ∉ S.domain ∪ U → e u = 0)) := by
      intro e
      simp [hEdef]
    have hEne : E.Nonempty := by
      refine ⟨fun u => if u ∈ S.domain then S.shared_error u else 0, ?_⟩
      rw [hmemE]
      refine ⟨fun u hu => by simp [hu], fun u hu => ?_⟩
      have hu' : u ∉ S.domain := fun h => hu (Finset.mem_union_left _ h)
      simp [hu']
    set g : binary_word n → ENNReal := fun e =>
      ∑ r ∈ S.active.filter (fun r =>
          binary_oracle_tree_eval (C.encode (S.origin r) + e) (S.tree r) =
            some (S.origin r i + 1)), S.weight r with hgdef
    set Tab : Finset (Fin m × binary_word n) := S.active ×ˢ E with hTabdef
    set Rab : Finset (Fin m × binary_word n) :=
      Tab.filter (fun p =>
        binary_oracle_tree_eval (C.encode (S.origin p.1) + p.2) (S.tree p.1) =
          some (S.origin p.1 i + 1)) with hRabdef
    have hTabsum : ∑ p ∈ Tab, S.weight p.1 =
        (E.card : ENNReal) * adaptive_switching_mass S := by
      rw [hTabdef, Finset.sum_product, adaptive_switching_mass, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro r _
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hRabsum : ∑ p ∈ Rab, S.weight p.1 = ∑ e ∈ E, g e := by
      rw [hRabdef, Finset.sum_filter, hTabdef, Finset.sum_product,
        Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro e _
      simp only [hgdef, Finset.sum_filter]
    have hsub : Tab ⊆ Rab ∪ Rab.image τ := by
      intro p hp
      have hp' := Finset.mem_product.mp hp
      have hpe := (hmemE p.2).mp hp'.2
      obtain ⟨h1, h2, h3, h4, h5⟩ := hτ p.1 p.2 hp'.1 hpe.1 hpe.2
      rcases h5 with hc | hc
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hc⟩)
      · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨τ p, ?_, hτinv p⟩)
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, ?_⟩, hc⟩
        exact (hmemE _).mpr ⟨h2, h3⟩
    have himgsum : ∑ p ∈ Rab.image τ, S.weight p.1 = ∑ p ∈ Rab, S.weight p.1 := by
      rw [Finset.sum_image (fun x _ y _ hxy => hτinv.injective hxy)]
      refine Finset.sum_congr rfl ?_
      intro p hp
      have hp' := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      have hpe := (hmemE p.2).mp hp'.2
      obtain ⟨_, _, _, h4, _⟩ := hτ p.1 p.2 hp'.1 hpe.1 hpe.2
      exact h4
    have hkey : (E.card : ENNReal) * adaptive_switching_mass S ≤ 2 * ∑ e ∈ E, g e := by
      have hstep : ∑ p ∈ Tab, S.weight p.1 ≤ ∑ p ∈ Rab ∪ Rab.image τ, S.weight p.1 :=
        Finset.sum_le_sum_of_subset hsub
      have hsplit : ∑ p ∈ Rab ∪ Rab.image τ, S.weight p.1 ≤
          (∑ p ∈ Rab, S.weight p.1) + ∑ p ∈ Rab.image τ, S.weight p.1 := by
        rw [← Finset.union_sdiff_self_eq_union,
          Finset.sum_union Finset.disjoint_sdiff]
        exact add_le_add le_rfl (Finset.sum_le_sum_of_subset Finset.sdiff_subset)
      rw [← hTabsum, ← hRabsum, two_mul]
      exact hstep.trans (by rw [himgsum] at hsplit; exact hsplit)
    obtain ⟨e₀, he₀E, he₀max⟩ := E.exists_max_image g hEne
    have hcard : (E.card : ENNReal) ≠ 0 := by
      simpa using Finset.card_ne_zero_of_mem he₀E
    have hsumle : ∑ e ∈ E, g e ≤ (E.card : ENNReal) * g e₀ := by
      calc ∑ e ∈ E, g e ≤ ∑ _e ∈ E, g e₀ := Finset.sum_le_sum (fun e he => he₀max e he)
        _ = (E.card : ENNReal) * g e₀ := by
            simp [Finset.sum_const, nsmul_eq_mul]
    have hfinal : adaptive_switching_mass S ≤ 2 * g e₀ := by
      have h := hkey.trans (mul_le_mul_left' hsumle 2)
      rw [show (2 : ENNReal) * ((E.card : ENNReal) * g e₀)
            = (E.card : ENNReal) * (2 * g e₀) by ring] at h
      exact (ENNReal.mul_le_mul_iff_right hcard (by simp)).mp h
    refine ⟨e₀, ((hmemE e₀).mp he₀E).1, ((hmemE e₀).mp he₀E).2, ?_⟩
    exact ENNReal.div_le_of_le_mul (by rw [mul_comm] at hfinal; exact hfinal)
  have hsubset : S.active.filter (fun r =>
      binary_oracle_tree_eval (C.encode (S.origin r) + e₀) (S.tree r) =
        some (S.origin r i + 1)) ⊆ S.active := Finset.filter_subset _ _
  have hHnew : ∀ u, u ∈ S.domain ∪ adaptive_switching_new_coordinates S 2 → u ∈ H := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact S.domain_subset_hitting_set u hu
    · rw [adaptive_switching_new_coordinates] at hu
      obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp hu
      exact ((Finset.mem_filter.mp hr).2).1
  refine ⟨{ domain := S.domain ∪ adaptive_switching_new_coordinates S 2
            domain_subset_hitting_set := hHnew
            shared_error := e₀
            shared_error_vanishes_off_domain := he₀off
            active := S.active.filter (fun r =>
              binary_oracle_tree_eval (C.encode (S.origin r) + e₀) (S.tree r) =
                some (S.origin r i + 1))
            tree := S.tree
            origin := S.origin
            level := S.level + 2
            continuation_error := fun _ => e₀
            continuation_supported_on_hitting_set := ?_
            continuation_extends_shared_error := fun _ _ _ _ => rfl
            continuation := fun r =>
              (binary_oracle_tree_transcript (C.encode (S.origin r) + e₀)
                (S.tree r)).drop (S.level + 2)
            continuation_is_suffix := fun _ _ => rfl
            shared_prefix := fun _ _ => rfl
            continuation_is_wrong := ?_
            weight := S.weight
            charge_injective := ?_ }, id, rfl, rfl, he₀dom, Set.injOn_id _, ?_, ?_⟩
  · intro r _ u hu
    refine hHnew u ?_
    by_contra hcon
    exact hu (he₀off u hcon)
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · exact S.charge_injective.mono (by
      intro r hr
      exact hsubset hr)
  · intro r hr
    refine ⟨hsubset hr, rfl, rfl, 0, by simp, Or.inl rfl⟩
  · exact hmass

@[blueprint "lem:adaptive-binary-hitting-attack"
  (statement := /-- Let $q,k,n$ be natural numbers, let $C\colon\mathbb F_2^k\to\mathbb F_2^n$ be a binary linear code, let $D$ be a possibly adaptive randomized relaxed decoder of depth at most $q$, fix a message coordinate $i$, and let $H\subseteq[n]$. Assume that $D$ has perfect completeness at $i$. Suppose, moreover, that $H$ meets every set $S\subseteq[n]$ with $|S|\leq q$ for which
\[
 b_i=\sum_{u\in S}C(b)_u\qquad\text{for every }b\in\mathbb F_2^k.
\]
Then there are a message $b$ and an error vector $e$ supported on $H$ such that the nonabort wrong-output probability of $D^{C(b)+e}(i)$ is at least $2^{-\lfloor q/2\rfloor}$. The same message $b$ and error vector $e$ apply to the whole distribution of deterministic trees defining $D(i)$. -/)
  (proof := /-- Put $V=C(\mathbb F_2^k)$, and let $\lambda\colon V\to\mathbb F_2$ be determined by $\lambda(C(b))=b_i$.  Injectivity in \cref{def:binary-linear-code} makes $\lambda$ well-defined; it is nonzero because $i$ is a coordinate of the message space.  Perfect completeness and finiteness imply the following pointwise assertion: every deterministic tree having positive mass in $D(i)$ returns $\lambda(x)$, and not $\bot$, for every $x\in V$.  Indeed, failure at one $x$ would contribute positive mass to an event whose probability is zero.  Repeated queries on a root-to-leaf path may be deleted without changing the computed function or increasing the depth in \cref{def:binary-oracle-tree-depth}.

We derive the following finite switching lemma by a global backward induction; its local two-query estimate is the orbit count of \cref{lem:adaptive-switching-block}, but the induction will not assert that the successor of a block inherits carry balance.  Let $V\leq\mathbb F_2^n$, let $\lambda\colon V\to\mathbb F_2$ be nonzero, and let $\nu$ be a finite distribution of deterministic binary oracle trees of depth at most $d$, with output alphabet $\mathbb F_2\cup\{\bot\}$.  Assume that every tree in the support of $\nu$ agrees pointwise with $\lambda$ on $V$.  If $H\subseteq[n]$ meets every set $S$ of at most $d$ coordinates satisfying
\[
  \lambda(x)=\sum_{u\in S}x_u\qquad(x\in V),                         \tag{1}
\]
then there are $x\in V$ and $e\in\mathbb F_2^n$, with $e$ supported on $H$, such that
\[
  \Pr_{T\sim\nu}[T(x+e)=1+\lambda(x)]\geq 2^{-\lfloor d/2\rfloor}. \tag{2}
\]

We prove the switching lemma with one global corruption throughout.  Put
\[
 \Omega_H=\{e\in\mathbb F_2^n:e_u=0\text{ for }u\notin H\}
\]
and equip this finite vector space with its uniform measure.  For a tree $T$ and $a\in V$, let
\[
 T^a(y)=T(y+a)+\lambda(a),
\]
where addition by $\lambda(a)$ interchanges the two nonabort outputs and fixes $\bot$.  Let $\bar\nu$ be the average, over uniform $a\in V$, of the push-forwards of $\nu$ under $T\mapsto T^a$.  The identities $(T^a)^v=T^{a+v}$ and
$T^a(x)=\lambda(x)$ for $x\in V$ show respectively that $\bar\nu$ is invariant under every translation $T\mapsto T^v$, $v\in V$, and that every tree in its support agrees with $\lambda$ on $V$.  Moreover,
\[
 \Pr_{R\sim\bar\nu}[R(e)=1]
 =\frac1{|V|}\sum_{a\in V}
   \Pr_{T\sim\nu}[T(a+e)=1+\lambda(a)].                         \tag{3}
\]
Consequently it suffices to find $e\in\Omega_H$ for which the left-hand side of (3) is at least $2^{-\lfloor d/2\rfloor}$.

We prove the switching lemma by a finite backward induction in which no
coordinate of the error is fixed before all later query blocks have been
examined.  This point is essential for adaptive trees.  Fix total orders on
all finite sets below.  A complete charged execution is a tuple
$(R,x,e,\tau)$, where $R$ is in the support of $\bar\nu$, $x\in V$,
$e\in\Omega_H$, and $\tau$ is the complete transcript of $R$ on $x+e$.
Its weight is $\bar\nu(R)/|V|$, and it is certified when its terminal value
is $1+\lambda(x)$.  For a family of charged executions and a set
$J\subseteq H$, its fibre value is the maximum, over assignments
$\eta\colon J\to\mathbb F_2$, of the total weight of certified executions
whose errors restrict to $\eta$ on $J$.  Coordinates outside $J$ remain
part of the entries and are not averaged or discarded.

For completeness, we give the backward-induction step.  Let $A$ be the set
of coordinates outside $H$ appearing in a fixed complete continuation.
Then $|A|\leq d$.  If every $v\in V$ vanishing on $A$ also satisfies
$\lambda(v)=0$, linear algebra makes $\lambda$ a sum of coordinate
functionals from a subset of $A$.  This contradicts (1), since
$A\cap H=\varnothing$.  Hence there is a canonically chosen vector
$v_A\in V$ such that
\[
 \lambda(v_A)=1,\qquad (v_A)_u=0\quad(u\in A).                \tag{4}
\]
On the full table define
\[
 (R,x,e,\tau)\longmapsto
 (R,x+v_A,e+\widetilde{C(v_A)|_H},\tau),                       \tag{5}
\]
where the tilde denotes extension by zero from $H$ to $[n]$.
At a queried coordinate outside $H$, (4) leaves the answer unchanged; at a
queried coordinate in $H$, the two added copies of $C(v_A)_u$ cancel.
Thus (5) preserves the complete transcript and its nonabort terminal
value, reverses the charged value of $\lambda$, preserves weight, and is an
involution.  Exactly one member of each nonabort two-element orbit is
certified.

Partition the query positions, starting at the root when $d$ is even and
after the first position when $d$ is odd, into consecutive pairs.  Process
these pairs from the leaves toward the root.  At a boundary keep all four
assignments to the two answers, with repetitions identified when a
coordinate is queried twice, and apply (5) separately to each complete
continuation below that boundary.  Pair equal continuation terms and apply
the all-record orbit selection of \cref{lem:adaptive-switching-block}, with
the unexposed coordinates of the complete errors retained as passive fibre
data.  The strengthened carry-balance requirement of
\cref{def:adaptive-switching-carry-balance} holds because (5) is defined on
every charged execution, including executions which leave a previously
specified continuation.  The resulting half-orbit estimate is equivalently
\[
 \max\{a+c,b+d\}\geq
 \tfrac12\bigl(\max\{a,b\}+\max\{c,d\}\bigr)
                                                                    \tag{6}
\]
for nonnegative $a,b,c,d$.  Thus the fibre value before the pair is at least
one half of the sum of the fibre values of its children.

We justify that (6) can be applied at every boundary.  All continuations
below that boundary have already been separated in the backward induction,
so (5) may change an $H$-coordinate queried either before or after the
boundary without leaving the table: it merely sends the entry to the fibre
with the correspondingly changed restriction.  Consequently the
translation used for a continuation is never required to vanish on a
previously fixed common domain.  If a record is unswitchable relative to
the next two positions alone, (4) still supplies the switch after the
outside-$H$ coordinates in its entire continuation are included.  Thus a
record which first becomes blocked at a later boundary is handled at that
later boundary directly; no involution is transported from an earlier
boundary.

Iterating (6) over the $\lfloor d/2\rfloor$ pairs gives a full error
$e\in\Omega_H$ whose certified weight is at least
$2^{-\lfloor d/2\rfloor}$.  When $d$ is odd, the unpaired first query is
lossless: before its answer is selected, (5) pairs the two charged
orientations and the two corresponding error restrictions, and both
children occur in the backward table.  Therefore the same bound holds for
all $d$.  By the definition of certified weight, the selected error
satisfies
\[
 2^{-\lfloor d/2\rfloor}
 \leq \frac1{|V|}\sum_{x\in V}
   \Pr_{R\sim\bar\nu}[R(x+e)=1+\lambda(x)].
\]
Translation invariance of $\bar\nu$ makes the right-hand side equal to
$\Pr_{R\sim\bar\nu}[R(e)=1]$, since the summand indexed by $x$ is the
probability of $(R^x)(e)=1$.  Formula (3) now shows that the average, over
$a\in V$, of the original wrong-output probabilities is at least
$2^{-\lfloor d/2\rfloor}$.  Choosing one such $a$ proves (2) with $x=a$
and with this same global vector $e$.

Apply the lemma with $d=q$ and with the distribution of trees defining $D(i)$.  Its hitting assumption is exactly the hypothesis on $H$.  We obtain an origin $x=C(b)$ and an $H$-supported error $e$ for which the common wrong-output probability is at least $2^{-\lfloor q/2\rfloor}$.  By \cref{def:binary-relaxed-decoding-error}, this is the asserted relaxed decoding error; by \cref{def:binary-soundness-threshold}, the displayed lower bound is precisely the required threshold. -/)
  (title := /-- A common-corruption attack on adaptive binary decision trees -/)
  (latexEnv := "lemma")]
lemma adaptive_binary_hitting_attack {k n q : ℕ}
    (C : binary_linear_code k n)
    (D : randomized_adaptive_decoder n k (Option (ZMod 2)))
    (i : Fin k) (H : Finset (Fin n))
    (hqueries : decoder_uses_at_most_queries (q := q) D)
    (hcomplete : ∀ b,
      randomized_adaptive_decoder_output D (C.encode b) i (some (b i)) ≥
        ENNReal.ofReal 1)
    (hhits : ∀ S : Finset (Fin n), S.card ≤ q →
      (∀ b, (∑ u ∈ S, C.encode b u) = b i) →
        ∃ u ∈ S, u ∈ H) :
    ∃ b e, (∀ u, e u ≠ 0 → u ∈ H) ∧
      binary_relaxed_decoding_error
          (randomized_adaptive_decoder_output D (C.encode b + e) i) (b i) ≥
        ENNReal.ofReal (binary_soundness_threshold q) := by
  classical
  have hzz : ∀ x : ZMod 2, x + x = 0 := by decide
  have hone : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  have hzer : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
  have hne1 : ∀ y : ZMod 2, y + 1 ≠ y := by decide
  have hflip : ∀ y z : ZMod 2, y ≠ z → y + 1 = z := by decide
  have hvv : ∀ v : binary_word k, v + v = 0 := by
    intro v; funext j; exact hzz (v j)
  have hcoset : ∀ (Z : Submodule (ZMod 2) (binary_word k)) (b₀ : binary_word k),
      (Finset.univ.filter (fun x : binary_word k => x - b₀ ∈ Z)).card
        = (Finset.univ.filter (fun z : binary_word k => z ∈ Z)).card := by
    intro Z b₀
    refine Finset.card_nbij' (fun x => x - b₀) (fun z => z + b₀) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx ⊢
      exact hx
    · intro z hz
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hz ⊢
      simpa using hz
    · intro x hx; simp
    · intro z hz; simp
  have hsplit : ∀ (Z : Submodule (ZMod 2) (binary_word k)) (b₀ : binary_word k)
      (g : binary_word k →ₗ[ZMod 2] ZMod 2) (v : binary_word k), v ∈ Z → g v = 1 →
      ∀ ℓ : ZMod 2,
      2 * (Finset.univ.filter (fun x : binary_word k => x - b₀ ∈ Z ∧ g x = ℓ)).card
        = (Finset.univ.filter (fun z : binary_word k => z ∈ Z)).card := by
    intro Z b₀ g v hvZ hgv ℓ
    have key : ∀ ℓ' : ZMod 2,
        (Finset.univ.filter (fun x : binary_word k => x - b₀ ∈ Z ∧ g x = ℓ')).card
          = (Finset.univ.filter (fun x : binary_word k => x - b₀ ∈ Z ∧ ¬ g x = ℓ')).card := by
      intro ℓ'
      refine Finset.card_nbij' (fun x => x + v) (fun x => x + v) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx ⊢
        refine ⟨?_, ?_⟩
        · have hr : x + v - b₀ = (x - b₀) + v := by ring
          rw [hr]
          exact Submodule.add_mem _ hx.1 hvZ
        · rw [map_add, hx.2, hgv]
          exact hne1 ℓ'
      · intro x hx
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx ⊢
        refine ⟨?_, ?_⟩
        · have hr : x + v - b₀ = (x - b₀) + v := by ring
          rw [hr]
          exact Submodule.add_mem _ hx.1 hvZ
        · rw [map_add, hgv]
          exact hflip _ _ hx.2
      · intro x hx
        have hr : x + v + v = x := by rw [add_assoc, hvv v, add_zero]
        exact hr
      · intro x hx
        have hr : x + v + v = x := by rw [add_assoc, hvv v, add_zero]
        exact hr
    have hpart : (Finset.univ.filter (fun x : binary_word k => x - b₀ ∈ Z ∧ g x = ℓ)).card
        + (Finset.univ.filter (fun x : binary_word k => x - b₀ ∈ Z ∧ ¬ g x = ℓ)).card
        = (Finset.univ.filter (fun x : binary_word k => x - b₀ ∈ Z)).card := by
      rw [show (Finset.univ.filter (fun x : binary_word k => x - b₀ ∈ Z ∧ g x = ℓ))
            = ((Finset.univ.filter (fun x : binary_word k => x - b₀ ∈ Z)).filter
                (fun x => g x = ℓ)) from by rw [Finset.filter_filter],
        show (Finset.univ.filter (fun x : binary_word k => x - b₀ ∈ Z ∧ ¬ g x = ℓ))
            = ((Finset.univ.filter (fun x : binary_word k => x - b₀ ∈ Z)).filter
                (fun x => ¬ g x = ℓ)) from by rw [Finset.filter_filter]]
      exact Finset.card_filter_add_card_filter_not _
    rw [← hcoset Z b₀, ← hpart, ← key ℓ]
    ring
  have hhalf : ∀ (Z : Submodule (ZMod 2) (binary_word k))
      (g : binary_word k →ₗ[ZMod 2] ZMod 2) (v : binary_word k) (m : ℕ), v ∈ Z → g v = 1 →
      (Finset.univ.filter (fun z : binary_word k => z ∈ Z)).card = 2 ^ m →
      1 ≤ m ∧ (Finset.univ.filter (fun z : binary_word k => z ∈ Z ⊓ LinearMap.ker g)).card
          = 2 ^ (m - 1) := by
    intro Z g v m hvZ hgv hcard
    have hset : (Finset.univ.filter (fun x : binary_word k => x - 0 ∈ Z ∧ g x = 0))
        = (Finset.univ.filter (fun z : binary_word k => z ∈ Z ⊓ LinearMap.ker g)) := by
      apply Finset.filter_congr
      intro x _
      simp [Submodule.mem_inf, LinearMap.mem_ker]
    have h2 := hsplit Z 0 g v hvZ hgv 0
    rw [hset, hcard] at h2
    have hpos : 1 ≤ (Finset.univ.filter (fun z : binary_word k => z ∈ Z ⊓ LinearMap.ker g)).card := by
      refine Finset.card_pos.mpr ⟨0, ?_⟩
      simp
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · rw [hm0] at h2; omega
      · exact hm0
    refine ⟨hm, ?_⟩
    have h3 : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h3] at h2
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  have harA : ∀ M N x y z : ℕ, 2 ^ x ≤ 2 * M * 2 ^ y → M ≤ N → y ≤ z →
      2 ^ x ≤ 2 * N * 2 ^ z := by
    intro M N x y z h1 h2 h3
    exact le_trans h1 (Nat.mul_le_mul (Nat.mul_le_mul_left 2 h2)
      (Nat.pow_le_pow_right (by norm_num) h3))
  have harB : ∀ M N x y z w : ℕ, 2 ^ x ≤ 2 * M * 2 ^ y → M ≤ N → y + 1 ≤ z → x + 1 = w →
      2 ^ w ≤ 2 * N * 2 ^ z := by
    intro M N x y z w h1 h2 h3 h4
    calc 2 ^ w = 2 * 2 ^ x := by rw [← h4, pow_succ']
      _ ≤ 2 * (2 * M * 2 ^ y) := Nat.mul_le_mul_left 2 h1
      _ = M * (2 * 2 ^ y) * 2 := by ring
      _ ≤ N * 2 ^ z * 2 := Nat.mul_le_mul_right 2 (Nat.mul_le_mul h2
          (by rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) h3))
      _ = 2 * N * 2 ^ z := by ring
  have harC : ∀ M M' N x y z w : ℕ, 2 ^ x ≤ 2 * M * 2 ^ y → 2 ^ x ≤ 2 * M' * 2 ^ y →
      M + M' ≤ N → y ≤ z → x + 1 = w → 2 ^ w ≤ 2 * N * 2 ^ z := by
    intro M M' N x y z w h1 h2 h3 h4 h5
    calc 2 ^ w = 2 ^ x + 2 ^ x := by rw [← h5, pow_succ']; ring
      _ ≤ 2 * M * 2 ^ y + 2 * M' * 2 ^ y := Nat.add_le_add h1 h2
      _ = 2 * (M + M') * 2 ^ y := by ring
      _ ≤ 2 * N * 2 ^ z := Nat.mul_le_mul (Nat.mul_le_mul_left 2 h3)
          (Nat.pow_le_pow_right (by norm_num) h4)
  have harD : ∀ X Y a b z : ℕ, 2 * X = 2 ^ a → 2 * Y = 2 ^ b → 1 ≤ z →
      2 ^ (a + b) ≤ 2 * (X * Y) * 2 ^ z := by
    intro X Y a b z h1 h2 h3
    calc 2 ^ (a + b) = (2 * X) * (2 * Y) := by rw [h1, h2, pow_add]
      _ = 2 * (X * Y) * 2 ^ 1 := by ring
      _ ≤ 2 * (X * Y) * 2 ^ z := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) h3)
  have harE : ∀ X Y a b z : ℕ, 2 * X = 2 ^ a → Y = 2 ^ b →
      2 ^ (a + b) ≤ 2 * (X * Y) * 2 ^ z := by
    intro X Y a b z h1 h2
    calc 2 ^ (a + b) = (2 * X) * Y := by rw [h1, h2, pow_add]
      _ = 2 * (X * Y) * 1 := by ring
      _ ≤ 2 * (X * Y) * 2 ^ z := Nat.mul_le_mul_left _ Nat.one_le_two_pow
  have hvalid : ∀ T ∈ (D i).support, ∀ m : binary_word k,
      binary_oracle_tree_eval (C.encode m) T = some (m i) := by
    intro T hT m
    have h1 : randomized_adaptive_decoder_output D (C.encode m) i (some (m i)) = 1 := by
      refine le_antisymm (PMF.coe_le_one _ _) ?_
      have := hcomplete m
      simpa using this
    have h2 := (PMF.apply_eq_one_iff _ _).mp h1
    have h3 : binary_oracle_tree_eval (C.encode m) T ∈
        (randomized_adaptive_decoder_output D (C.encode m) i).support := by
      rw [randomized_adaptive_decoder_output, PMF.mem_support_map_iff]
      exact ⟨T, hT, rfl⟩
    rw [h2] at h3
    simpa using h3
  have hswitch : ∀ A : Finset (Fin n), A.card ≤ q → (∀ u ∈ A, u ∉ H) →
      ∃ v : binary_word k, v i = 1 ∧ ∀ u ∈ A, C.encode v u = 0 := by
    intro A hcard hHA
    by_contra hcon
    have hzero : ∀ z : binary_word k, (∀ u ∈ A, C.encode z u = 0) → z i = 0 := by
      intro z hz; by_contra hzi; exact hcon ⟨z, hone _ hzi, hz⟩
    set ψ : Fin n → Module.Dual (ZMod 2) (binary_word k) := fun u =>
      (LinearMap.proj u : binary_word n →ₗ[ZMod 2] ZMod 2).comp C.encode with hψdef
    have hψ : ∀ (u : Fin n) (z : binary_word k), ψ u z = C.encode z u := by
      intro u z; rw [hψdef]; rfl
    have hlam : (LinearMap.proj i : binary_word k →ₗ[ZMod 2] ZMod 2) ∈
        Submodule.span (ZMod 2) (Set.range (fun u : {x // x ∈ A} => ψ u.1)) := by
      have hfd : (Submodule.dualCoannihilator
          (Submodule.span (ZMod 2) (Set.range (fun u : {x // x ∈ A} => ψ u.1)))).dualAnnihilator
          = Submodule.span (ZMod 2) (Set.range (fun u : {x // x ∈ A} => ψ u.1)) :=
        Subspace.dualCoannihilator_dualAnnihilator_eq
      rw [← hfd, Submodule.mem_dualAnnihilator]
      intro x hx
      rw [Submodule.mem_dualCoannihilator] at hx
      have hxA : ∀ u ∈ A, C.encode x u = 0 := by
        intro u hu
        have hmem : ψ u ∈ Submodule.span (ZMod 2) (Set.range (fun u : {x // x ∈ A} => ψ u.1)) :=
          Submodule.subset_span ⟨⟨u, hu⟩, rfl⟩
        have := hx (ψ u) hmem
        rwa [hψ] at this
      have := hzero x hxA
      simpa using this
    rw [Submodule.mem_span_range_iff_exists_fun] at hlam
    obtain ⟨c, hc⟩ := hlam
    refine absurd (hhits ((A.attach.filter (fun u => c u = 1)).image Subtype.val) ?_ ?_) ?_
    · refine le_trans (le_trans (Finset.card_image_le) ?_) hcard
      exact le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_attach))
    · intro b
      have happ := LinearMap.congr_fun hc b
      have e0 : ∑ u : {x // x ∈ A}, (c u • ψ u.1) b = b i := by simpa using happ
      rw [Finset.sum_image (by intro x hx y hy hxy; exact Subtype.ext hxy)]
      rw [← e0, ← Finset.attach_eq_univ,
        ← Finset.sum_filter_add_sum_filter_not A.attach (fun u => c u = 1)]
      have e2 : ∑ u ∈ A.attach.filter (fun u => ¬ c u = 1), (c u • ψ u.1) b = 0 := by
        refine Finset.sum_eq_zero ?_
        intro u hu
        have := hzer _ ((Finset.mem_filter.mp hu).2)
        simp [this]
      rw [e2, add_zero]
      refine Finset.sum_congr rfl ?_
      intro u hu
      have hcu := (Finset.mem_filter.mp hu).2
      rw [hcu]; simp [hψ]
    · rintro ⟨u, huS, huH⟩
      obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp huS
      exact hHA u (hvu ▸ v.2) huH
  obtain ⟨Y, hY⟩ : ∃ Y : binary_word k × binary_word k → binary_word n,
      ∀ (p : binary_word k × binary_word k) (u : Fin n),
        Y p u = if u ∈ H then C.encode p.2 u else C.encode p.1 u :=
    ⟨fun p u => if u ∈ H then C.encode p.2 u else C.encode p.1 u, fun _ _ => rfl⟩
  have hsucA : ∀ x y : ℕ, 1 ≤ x → x - 1 + y + 1 = x + y := by
    intro x y h
    omega
  have hsucB : ∀ x y : ℕ, 1 ≤ y → x + (y - 1) + 1 = x + y := by
    intro x y h
    omega
  have hps0 : ∀ a b t d : ℕ, t < a → t < b →
      1 ≤ min (b - t + d) (min (a - t + d) ((a + b - 2 * t + d) / 2)) := by
    intro a b t d h1 h2
    exact le_min (by omega) (le_min (by omega) (by omega))
  have hps1 : ∀ a b t d : ℕ, t ≤ a → t ≤ b → 1 ≤ b → 1 ≤ t → 1 ≤ d →
      min (b - 1 - (t - 1) + (d - 1))
          (min (a - (t - 1) + (d - 1)) ((a + (b - 1) - 2 * (t - 1) + (d - 1)) / 2))
        ≤ min (b - t + d) (min (a - t + d) ((a + b - 2 * t + d) / 2)) := by
    intro a b t d h1 h2 h3 h4 h5
    exact min_le_min (by omega) (min_le_min (by omega) (by omega))
  have hps2 : ∀ a b t d : ℕ, t ≤ a → t ≤ b → 1 ≤ a → 1 ≤ t → 1 ≤ d →
      min (b - (t - 1) + (d - 1))
          (min (a - 1 - (t - 1) + (d - 1)) ((a - 1 + b - 2 * (t - 1) + (d - 1)) / 2))
        ≤ min (b - t + d) (min (a - t + d) ((a + b - 2 * t + d) / 2)) := by
    intro a b t d h1 h2 h3 h4 h5
    exact min_le_min (by omega) (min_le_min (by omega) (by omega))
  have hps3 : ∀ a b t d : ℕ, t ≤ a → t ≤ b - 1 → 1 ≤ b → 1 ≤ d →
      min (b - 1 - t + (d - 1))
          (min (a - t + (d - 1)) ((a + (b - 1) - 2 * t + (d - 1)) / 2)) + 1
        ≤ min (b - t + d) (min (a - t + d) ((a + b - 2 * t + d) / 2)) := by
    intro a b t d h1 h2 h3 h4
    refine le_min ?_ (le_min ?_ ?_)
    · exact le_trans (Nat.add_le_add_right (min_le_left _ _) 1) (by omega)
    · exact le_trans (Nat.add_le_add_right (le_trans (min_le_right _ _) (min_le_left _ _)) 1)
        (by omega)
    · exact le_trans (Nat.add_le_add_right (le_trans (min_le_right _ _) (min_le_right _ _)) 1)
        (by omega)
  have hps4 : ∀ a b t d : ℕ, t ≤ a - 1 → t ≤ b → 1 ≤ a → 1 ≤ d →
      min (b - t + (d - 1))
          (min (a - 1 - t + (d - 1)) ((a - 1 + b - 2 * t + (d - 1)) / 2)) + 1
        ≤ min (b - t + d) (min (a - t + d) ((a + b - 2 * t + d) / 2)) := by
    intro a b t d h1 h2 h3 h4
    refine le_min ?_ (le_min ?_ ?_)
    · exact le_trans (Nat.add_le_add_right (min_le_left _ _) 1) (by omega)
    · exact le_trans (Nat.add_le_add_right (le_trans (min_le_right _ _) (min_le_left _ _)) 1)
        (by omega)
    · exact le_trans (Nat.add_le_add_right (le_trans (min_le_right _ _) (min_le_right _ _)) 1)
        (by omega)
  have hps5 : ∀ a b t d : ℕ, 1 ≤ d →
      min (b - t + (d - 1)) (min (a - t + (d - 1)) ((a + b - 2 * t + (d - 1)) / 2))
        ≤ min (b - t + d) (min (a - t + d) ((a + b - 2 * t + d) / 2)) := by
    intro a b t d h1
    exact min_le_min (by omega) (min_le_min (by omega) (by omega))
  have key : ∀ (T : binary_oracle_tree n (Option (ZMod 2)))
      (Z₁ Z₂ : Submodule (ZMod 2) (binary_word k)) (b₀ c₀ : binary_word k)
      (A : Finset (Fin n)) (a b t d : ℕ),
      (∀ u ∈ A, u ∉ H) → A.card + d ≤ q → binary_oracle_tree_depth T ≤ d →
      (∀ z : binary_word k, z ∈ Z₁ ↔ ∀ u ∈ A, C.encode z u = 0) →
      (Finset.univ.filter (fun z : binary_word k => z ∈ Z₁)).card = 2 ^ a →
      (Finset.univ.filter (fun z : binary_word k => z ∈ Z₂)).card = 2 ^ b →
      (Finset.univ.filter (fun z : binary_word k => z ∈ Z₁ ⊓ Z₂)).card = 2 ^ t →
      (∃ m : binary_word k, m - b₀ ∈ Z₁ ∧ m - c₀ ∈ Z₂) →
      (∀ m : binary_word k, m - b₀ ∈ Z₁ → m - c₀ ∈ Z₂ →
          binary_oracle_tree_eval (C.encode m) T = some (m i)) →
      2 ^ (a + b) ≤ 2 * (Finset.univ.filter (fun p : binary_word k × binary_word k =>
          p.1 - b₀ ∈ Z₁ ∧ p.2 - c₀ ∈ Z₂ ∧ p.1 i ≠ p.2 i ∧
          binary_oracle_tree_eval (Y p) T = some (p.2 i))).card
        * 2 ^ (min (b - t + d) (min (a - t + d) ((a + b - 2 * t + d) / 2))) := by
    intro T
    induction T with
    | output o =>
      intro Z₁ Z₂ b₀ c₀ A a b t d hHA hAq hdep hZ₁ hcZ₁ hcZ₂ hcZ₁₂ hnem hval
      obtain ⟨m₀, hm₁, hm₂⟩ := hnem
      have hout : o = some (m₀ i) := by
        have h := hval m₀ hm₁ hm₂
        simpa [binary_oracle_tree_eval] using h
      have hlam0 : ∀ z : binary_word k, z ∈ Z₁ ⊓ Z₂ → z i = 0 := by
        intro z hz
        have hz1 : z ∈ Z₁ := (Submodule.mem_inf.mp hz).1
        have hz2 : z ∈ Z₂ := (Submodule.mem_inf.mp hz).2
        have h1 : m₀ + z - b₀ ∈ Z₁ := by
          have hr : m₀ + z - b₀ = (m₀ - b₀) + z := by ring
          rw [hr]; exact Submodule.add_mem _ hm₁ hz1
        have h2 : m₀ + z - c₀ ∈ Z₂ := by
          have hr : m₀ + z - c₀ = (m₀ - c₀) + z := by ring
          rw [hr]; exact Submodule.add_mem _ hm₂ hz2
        have h3 := hval (m₀ + z) h1 h2
        rw [show binary_oracle_tree_eval (C.encode (m₀ + z))
            (binary_oracle_tree.output o) = o from rfl, hout] at h3
        have h4 : m₀ i = m₀ i + z i := by
          have := Option.some_injective _ h3
          simpa using this
        have h5 : (0 : ZMod 2) = z i := by
          have := add_left_cancel (a := m₀ i) (b := 0) (c := z i) (by simpa using h4)
          exact this
        exact h5.symm
      obtain ⟨v, hvi, hvA⟩ := hswitch A (by omega) hHA
      have hvZ₁ : v ∈ Z₁ := (hZ₁ v).mpr hvA
      have hta : t < a := by
        have hsub : (Finset.univ.filter (fun z : binary_word k => z ∈ Z₁ ⊓ Z₂))
            ⊂ (Finset.univ.filter (fun z : binary_word k => z ∈ Z₁)) := by
          refine ⟨?_, ?_⟩
          · intro z hz
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
            exact (Submodule.mem_inf.mp hz).1
          · intro hsubset
            have hv2 : v ∈ Z₁ ⊓ Z₂ := by
              have := hsubset (by simp [hvZ₁] : v ∈ Finset.univ.filter
                (fun z : binary_word k => z ∈ Z₁))
              simpa using this
            have := hlam0 v hv2
            rw [hvi] at this
            exact absurd this (by decide)
        have hlt := Finset.card_lt_card hsub
        rw [hcZ₁, hcZ₁₂] at hlt
        exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
      have hprod : (Finset.univ.filter (fun p : binary_word k × binary_word k =>
            p.1 - b₀ ∈ Z₁ ∧ p.2 - c₀ ∈ Z₂ ∧ p.1 i ≠ p.2 i ∧
            binary_oracle_tree_eval (Y p) (binary_oracle_tree.output o) = some (p.2 i)))
          = (Finset.univ.filter (fun x : binary_word k => x - b₀ ∈ Z₁ ∧ x i = m₀ i + 1))
              ×ˢ (Finset.univ.filter (fun y : binary_word k => y - c₀ ∈ Z₂ ∧ y i = m₀ i)) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
          show ∀ y : binary_word n, binary_oracle_tree_eval y
            (binary_oracle_tree.output o) = o from fun _ => rfl, hout]
        constructor
        · rintro ⟨h1, h2, h3, h4⟩
          have h5 : p.2 i = m₀ i := (Option.some_injective _ h4).symm
          refine ⟨⟨h1, ?_⟩, h2, h5⟩
          rw [← h5]
          exact (hflip _ _ (Ne.symm h3)).symm
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩
          refine ⟨h1, h3, ?_, ?_⟩
          · rw [h2, h4]
            exact hne1 _
          · rw [h4]
            rfl
      rw [hprod, Finset.card_product]
      have hX := hsplit Z₁ b₀ (LinearMap.proj i) v hvZ₁ (by simpa using hvi) (m₀ i + 1)
      have hXc : 2 * (Finset.univ.filter (fun x : binary_word k =>
          x - b₀ ∈ Z₁ ∧ x i = m₀ i + 1)).card = 2 ^ a := by
        rw [← hcZ₁]
        simpa using hX
      by_cases hδ : ∃ w : binary_word k, w ∈ Z₂ ∧ w i = 1
      · obtain ⟨w, hwZ₂, hwi⟩ := hδ
        have hYc : 2 * (Finset.univ.filter (fun y : binary_word k =>
            y - c₀ ∈ Z₂ ∧ y i = m₀ i)).card = 2 ^ b := by
          rw [← hcZ₂]
          simpa using hsplit Z₂ c₀ (LinearMap.proj i) w hwZ₂ (by simpa using hwi) (m₀ i)
        have htb : t < b := by
          have hsub : (Finset.univ.filter (fun z : binary_word k => z ∈ Z₁ ⊓ Z₂))
              ⊂ (Finset.univ.filter (fun z : binary_word k => z ∈ Z₂)) := by
            refine ⟨?_, ?_⟩
            · intro z hz
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
              exact (Submodule.mem_inf.mp hz).2
            · intro hsubset
              have hw2 : w ∈ Z₁ ⊓ Z₂ := by
                have := hsubset (by simp [hwZ₂] : w ∈ Finset.univ.filter
                  (fun z : binary_word k => z ∈ Z₂))
                simpa using this
              have := hlam0 w hw2
              rw [hwi] at this
              exact absurd this (by decide)
          have hlt := Finset.card_lt_card hsub
          rw [hcZ₂, hcZ₁₂] at hlt
          exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
        have hΨ := hps0 a b t d hta htb
        exact harD _ _ a b _ hXc hYc hΨ
      · have hz2 : ∀ z : binary_word k, z ∈ Z₂ → z i = 0 := by
          intro z hzZ
          by_contra hzi
          exact hδ ⟨z, hzZ, hone _ hzi⟩
        have hYset : (Finset.univ.filter (fun y : binary_word k => y - c₀ ∈ Z₂ ∧ y i = m₀ i))
            = (Finset.univ.filter (fun y : binary_word k => y - c₀ ∈ Z₂)) := by
          apply Finset.filter_congr
          intro y _
          constructor
          · exact fun h => h.1
          · intro h
            refine ⟨h, ?_⟩
            have h1 := hz2 _ h
            have h2 := hz2 _ hm₂
            have h3 : y i - c₀ i = 0 := by simpa using h1
            have h4 : m₀ i - c₀ i = 0 := by simpa using h2
            have : y i = c₀ i := by
              have := sub_eq_zero.mp h3
              exact this
            have h5 : m₀ i = c₀ i := sub_eq_zero.mp h4
            rw [this, h5]
        have hYc : (Finset.univ.filter (fun y : binary_word k =>
            y - c₀ ∈ Z₂ ∧ y i = m₀ i)).card = 2 ^ b := by
          rw [hYset, hcoset, hcZ₂]
        exact harE _ _ a b _ hXc hYc
    | query u T₀ T₁ ih₀ ih₁ =>
      intro Z₁ Z₂ b₀ c₀ A a b t d hHA hAq hdep hZ₁ hcZ₁ hcZ₂ hcZ₁₂ hnem hval
      obtain ⟨m₀, hm₁, hm₂⟩ := hnem
      have hdepu : 1 + max (binary_oracle_tree_depth T₀) (binary_oracle_tree_depth T₁) ≤ d := by
        simpa [binary_oracle_tree_depth] using hdep
      have hd1 : 1 ≤ d := by omega
      have hdep0 : binary_oracle_tree_depth T₀ ≤ d - 1 := by omega
      have hdep1 : binary_oracle_tree_depth T₁ ≤ d - 1 := by omega
      obtain ⟨Tb, hTb0, hTb1⟩ : ∃ Tb : ZMod 2 → binary_oracle_tree n (Option (ZMod 2)),
          Tb 0 = T₀ ∧ Tb 1 = T₁ :=
        ⟨fun β => if β = 0 then T₀ else T₁, by simp, by simp⟩
      have hβ : ∀ β : ZMod 2, β = 0 ∨ β = 1 := by decide
      have hdepb : ∀ β : ZMod 2, binary_oracle_tree_depth (Tb β) ≤ d - 1 := by
        intro β
        rcases hβ β with h | h
        · rw [h, hTb0]; exact hdep0
        · rw [h, hTb1]; exact hdep1
      have hevalb : ∀ (y : binary_word n) (β : ZMod 2), y u = β →
          binary_oracle_tree_eval y (binary_oracle_tree.query u T₀ T₁)
            = binary_oracle_tree_eval y (Tb β) := by
        intro y β hyu
        rcases hβ β with h | h
        · rw [h, hTb0]
          simp only [binary_oracle_tree_eval]
          rw [if_pos (by rw [hyu, h])]
        · rw [h, hTb1]
          simp only [binary_oracle_tree_eval]
          rw [if_neg (by rw [hyu, h]; decide)]
      have hih : ∀ (β : ZMod 2) (W₁ W₂ : Submodule (ZMod 2) (binary_word k))
          (b₁ c₁ : binary_word k) (A' : Finset (Fin n)) (a' b' t' d' : ℕ),
          (∀ w ∈ A', w ∉ H) → A'.card + d' ≤ q → binary_oracle_tree_depth (Tb β) ≤ d' →
          (∀ z : binary_word k, z ∈ W₁ ↔ ∀ w ∈ A', C.encode z w = 0) →
          (Finset.univ.filter (fun z : binary_word k => z ∈ W₁)).card = 2 ^ a' →
          (Finset.univ.filter (fun z : binary_word k => z ∈ W₂)).card = 2 ^ b' →
          (Finset.univ.filter (fun z : binary_word k => z ∈ W₁ ⊓ W₂)).card = 2 ^ t' →
          (∃ m : binary_word k, m - b₁ ∈ W₁ ∧ m - c₁ ∈ W₂) →
          (∀ m : binary_word k, m - b₁ ∈ W₁ → m - c₁ ∈ W₂ →
              binary_oracle_tree_eval (C.encode m) (Tb β) = some (m i)) →
          2 ^ (a' + b') ≤ 2 * (Finset.univ.filter (fun p : binary_word k × binary_word k =>
              p.1 - b₁ ∈ W₁ ∧ p.2 - c₁ ∈ W₂ ∧ p.1 i ≠ p.2 i ∧
              binary_oracle_tree_eval (Y p) (Tb β) = some (p.2 i))).card
            * 2 ^ (min (b' - t' + d') (min (a' - t' + d') ((a' + b' - 2 * t' + d') / 2))) := by
        intro β
        rcases hβ β with h | h
        · rw [h, hTb0]; exact ih₀
        · rw [h, hTb1]; exact ih₁
      set g : binary_word k →ₗ[ZMod 2] ZMod 2 :=
        (LinearMap.proj u : binary_word n →ₗ[ZMod 2] ZMod 2).comp C.encode with hgdef
      have hg : ∀ z : binary_word k, g z = C.encode z u := by
        intro z; rw [hgdef]; rfl
      have htab : t ≤ a ∧ t ≤ b := by
        constructor
        · have h1 : (Finset.univ.filter (fun z : binary_word k => z ∈ Z₁ ⊓ Z₂)).card
              ≤ (Finset.univ.filter (fun z : binary_word k => z ∈ Z₁)).card := by
            refine Finset.card_le_card ?_
            intro z hz
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
            exact (Submodule.mem_inf.mp hz).1
          rw [hcZ₁, hcZ₁₂] at h1
          exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
        · have h1 : (Finset.univ.filter (fun z : binary_word k => z ∈ Z₁ ⊓ Z₂)).card
              ≤ (Finset.univ.filter (fun z : binary_word k => z ∈ Z₂)).card := by
            refine Finset.card_le_card ?_
            intro z hz
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
            exact (Submodule.mem_inf.mp hz).2
          rw [hcZ₂, hcZ₁₂] at h1
          exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
      by_cases huH : u ∈ H
      · have hYu : ∀ p : binary_word k × binary_word k, Y p u = g p.2 := by
          intro p
          rw [hY, if_pos huH, hg]
        have hA'q : A.card + (d - 1) ≤ q := by omega
        have hsubF : ∀ (Z : Submodule (ZMod 2) (binary_word k)) (c₁ : binary_word k) (β : ZMod 2),
            Z ≤ Z₂ → (∀ z : binary_word k, z ∈ Z → g z = 0) → c₁ - c₀ ∈ Z₂ → g c₁ = β →
            (Finset.univ.filter (fun p : binary_word k × binary_word k =>
                p.1 - b₀ ∈ Z₁ ∧ p.2 - c₁ ∈ Z ∧ p.1 i ≠ p.2 i ∧
                binary_oracle_tree_eval (Y p) (Tb β) = some (p.2 i)))
              ⊆ (Finset.univ.filter (fun p : binary_word k × binary_word k =>
                p.1 - b₀ ∈ Z₁ ∧ p.2 - c₀ ∈ Z₂ ∧ p.1 i ≠ p.2 i ∧
                binary_oracle_tree_eval (Y p)
                  (binary_oracle_tree.query u T₀ T₁) = some (p.2 i))) := by
          intro Z c₁ β hZle hZg hc₁ hgc₁ p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          obtain ⟨h1, h2, h3, h4⟩ := hp
          have hgp : g p.2 = β := by
            have h5 : g (p.2 - c₁) = 0 := hZg _ h2
            rw [map_sub, hgc₁, sub_eq_zero] at h5
            exact h5
          refine ⟨h1, ?_, h3, ?_⟩
          · have hr : p.2 - c₀ = (p.2 - c₁) + (c₁ - c₀) := by ring
            rw [hr]
            exact Submodule.add_mem _ (hZle h2) hc₁
          · rw [hevalb (Y p) β (by rw [hYu p, hgp])]
            exact h4
        have hvalchild : ∀ (Z : Submodule (ZMod 2) (binary_word k)) (c₁ : binary_word k)
            (β : ZMod 2),
            Z ≤ Z₂ → (∀ z : binary_word k, z ∈ Z → g z = 0) → c₁ - c₀ ∈ Z₂ → g c₁ = β →
            ∀ m : binary_word k, m - b₀ ∈ Z₁ → m - c₁ ∈ Z →
              binary_oracle_tree_eval (C.encode m) (Tb β) = some (m i) := by
          intro Z c₁ β hZle hZg hc₁ hgc₁ m hmb hmz
          have hgm : g m = β := by
            have h5 : g (m - c₁) = 0 := hZg _ hmz
            rw [map_sub, hgc₁, sub_eq_zero] at h5
            exact h5
          have hmZ₂ : m - c₀ ∈ Z₂ := by
            have hr : m - c₀ = (m - c₁) + (c₁ - c₀) := by ring
            rw [hr]
            exact Submodule.add_mem _ (hZle hmz) hc₁
          have h := hval m hmb hmZ₂
          rw [hevalb (C.encode m) β (by rw [← hg m, hgm])] at h
          exact h
        by_cases hg1 : ∃ z : binary_word k, z ∈ Z₂ ∧ g z = 1
        · obtain ⟨v, hvZ, hgv⟩ := hg1
          obtain ⟨hb1, hcard2⟩ := hhalf Z₂ g v b hvZ hgv hcZ₂
          by_cases hg2 : ∃ z : binary_word k, z ∈ Z₁ ⊓ Z₂ ∧ g z = 1
          · obtain ⟨w, hwZ, hgw⟩ := hg2
            obtain ⟨ht1, hcard12'⟩ := hhalf (Z₁ ⊓ Z₂) g w t hwZ hgw hcZ₁₂
            have hwZ₁ : w ∈ Z₁ := (Submodule.mem_inf.mp hwZ).1
            have hwZ₂ : w ∈ Z₂ := (Submodule.mem_inf.mp hwZ).2
            have hcard12 : (Finset.univ.filter (fun z : binary_word k =>
                z ∈ Z₁ ⊓ (Z₂ ⊓ LinearMap.ker g))).card = 2 ^ (t - 1) := by
              rw [show Z₁ ⊓ (Z₂ ⊓ LinearMap.ker g) = (Z₁ ⊓ Z₂) ⊓ LinearMap.ker g from
                (inf_assoc _ _ _).symm]
              exact hcard12'
            have hZle : Z₂ ⊓ LinearMap.ker g ≤ Z₂ := inf_le_left
            have hZg : ∀ z : binary_word k, z ∈ Z₂ ⊓ LinearMap.ker g → g z = 0 := by
              intro z hz
              exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hz).2
            have hmw₁ : m₀ + w - b₀ ∈ Z₁ := by
              have hr : m₀ + w - b₀ = (m₀ - b₀) + w := by ring
              rw [hr]
              exact Submodule.add_mem _ hm₁ hwZ₁
            have hmw₂ : m₀ + w - c₀ ∈ Z₂ := by
              have hr : m₀ + w - c₀ = (m₀ - c₀) + w := by ring
              rw [hr]
              exact Submodule.add_mem _ hm₂ hwZ₂
            have hgmw : g (m₀ + w) = g m₀ + 1 := by rw [map_add, hgw]
            have hIH₀ := hih (g m₀) Z₁ (Z₂ ⊓ LinearMap.ker g) b₀ m₀ A
              a (b - 1) (t - 1) (d - 1) hHA hA'q (hdepb _) hZ₁ hcZ₁ hcard2 hcard12
              ⟨m₀, hm₁, by simp⟩
              (hvalchild _ m₀ (g m₀) hZle hZg hm₂ rfl)
            have hIH₁ := hih (g m₀ + 1) Z₁ (Z₂ ⊓ LinearMap.ker g) b₀ (m₀ + w) A
              a (b - 1) (t - 1) (d - 1) hHA hA'q (hdepb _) hZ₁ hcZ₁ hcard2 hcard12
              ⟨m₀ + w, hmw₁, by simp⟩
              (hvalchild _ (m₀ + w) (g m₀ + 1) hZle hZg hmw₂ hgmw)
            have hdisj : Disjoint
                (Finset.univ.filter (fun p : binary_word k × binary_word k =>
                  p.1 - b₀ ∈ Z₁ ∧ p.2 - m₀ ∈ Z₂ ⊓ LinearMap.ker g ∧ p.1 i ≠ p.2 i ∧
                  binary_oracle_tree_eval (Y p) (Tb (g m₀)) = some (p.2 i)))
                (Finset.univ.filter (fun p : binary_word k × binary_word k =>
                  p.1 - b₀ ∈ Z₁ ∧ p.2 - (m₀ + w) ∈ Z₂ ⊓ LinearMap.ker g ∧ p.1 i ≠ p.2 i ∧
                  binary_oracle_tree_eval (Y p) (Tb (g m₀ + 1)) = some (p.2 i))) := by
              rw [Finset.disjoint_left]
              intro p hp0 hp1
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp0 hp1
              have e0 : g p.2 = g m₀ := by
                have h5 : g (p.2 - m₀) = 0 := hZg _ hp0.2.1
                rw [map_sub, sub_eq_zero] at h5
                exact h5
              have e1 : g p.2 = g m₀ + 1 := by
                have h5 : g (p.2 - (m₀ + w)) = 0 := hZg _ hp1.2.1
                rw [map_sub, hgmw, sub_eq_zero] at h5
                exact h5
              rw [e0] at e1
              exact hne1 (g m₀) e1.symm
            have hsum := le_trans (le_of_eq (Finset.card_union_of_disjoint hdisj).symm)
              (Finset.card_le_card (Finset.union_subset
                (hsubF _ m₀ (g m₀) hZle hZg hm₂ rfl)
                (hsubF _ (m₀ + w) (g m₀ + 1) hZle hZg hmw₂ hgmw)))
            have hΨ := hps1 a b t d htab.1 htab.2 hb1 ht1 hd1
            exact harC _ _ _ _ _ _ _ hIH₀ hIH₁ hsum hΨ (hsucB a b hb1)
          · have hg2' : ∀ z : binary_word k, z ∈ Z₁ ⊓ Z₂ → g z = 0 := by
              intro z hz
              by_contra hzg
              exact hg2 ⟨z, hz, hone _ hzg⟩
            have hZeq2 : Z₁ ⊓ (Z₂ ⊓ LinearMap.ker g) = Z₁ ⊓ Z₂ := by
              refine le_antisymm (inf_le_inf_left _ inf_le_left) ?_
              intro z hz
              exact Submodule.mem_inf.mpr
                ⟨(Submodule.mem_inf.mp hz).1,
                  Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hz).2,
                    LinearMap.mem_ker.mpr (hg2' z hz)⟩⟩
            have hcard12 : (Finset.univ.filter (fun z : binary_word k =>
                z ∈ Z₁ ⊓ (Z₂ ⊓ LinearMap.ker g))).card = 2 ^ t := by
              rw [hZeq2]; exact hcZ₁₂
            have htb1 : t ≤ b - 1 := by
              have h1 : (Finset.univ.filter (fun z : binary_word k => z ∈ Z₁ ⊓ Z₂)).card
                  ≤ (Finset.univ.filter (fun z : binary_word k =>
                    z ∈ Z₂ ⊓ LinearMap.ker g)).card := by
                refine Finset.card_le_card ?_
                intro z hz
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
                rw [← hZeq2] at hz
                exact (Submodule.mem_inf.mp hz).2
              rw [hcard2, hcZ₁₂] at h1
              exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
            have hZle : Z₂ ⊓ LinearMap.ker g ≤ Z₂ := inf_le_left
            have hZg : ∀ z : binary_word k, z ∈ Z₂ ⊓ LinearMap.ker g → g z = 0 := by
              intro z hz
              exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hz).2
            have hIH := hih (g m₀) Z₁ (Z₂ ⊓ LinearMap.ker g) b₀ m₀ A
              a (b - 1) t (d - 1) hHA hA'q (hdepb _) hZ₁ hcZ₁ hcard2 hcard12
              ⟨m₀, hm₁, by simp⟩
              (hvalchild _ m₀ (g m₀) hZle hZg hm₂ rfl)
            have hc := Finset.card_le_card (hsubF (Z₂ ⊓ LinearMap.ker g) m₀ (g m₀)
              hZle hZg hm₂ rfl)
            have hΨ := hps3 a b t d htab.1 htb1 hb1 hd1
            exact harB _ _ _ _ _ _ hIH hc hΨ (hsucB a b hb1)
        · have hg1' : ∀ z : binary_word k, z ∈ Z₂ → g z = 0 := by
            intro z hz
            by_contra hzg
            exact hg1 ⟨z, hz, hone _ hzg⟩
          have hZeq : Z₂ ⊓ LinearMap.ker g = Z₂ := by
            refine le_antisymm inf_le_left ?_
            intro z hz
            exact Submodule.mem_inf.mpr ⟨hz, LinearMap.mem_ker.mpr (hg1' z hz)⟩
          have hcard2 : (Finset.univ.filter (fun z : binary_word k =>
              z ∈ Z₂ ⊓ LinearMap.ker g)).card = 2 ^ b := by rw [hZeq]; exact hcZ₂
          have hcard12 : (Finset.univ.filter (fun z : binary_word k =>
              z ∈ Z₁ ⊓ (Z₂ ⊓ LinearMap.ker g))).card = 2 ^ t := by rw [hZeq]; exact hcZ₁₂
          have hZle : Z₂ ⊓ LinearMap.ker g ≤ Z₂ := inf_le_left
          have hZg : ∀ z : binary_word k, z ∈ Z₂ ⊓ LinearMap.ker g → g z = 0 := by
            intro z hz
            exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hz).2
          have hIH := hih (g c₀) Z₁ (Z₂ ⊓ LinearMap.ker g) b₀ c₀ A
            a b t (d - 1) hHA hA'q (hdepb _) hZ₁ hcZ₁ hcard2 hcard12
            ⟨m₀, hm₁, Submodule.mem_inf.mpr ⟨hm₂, LinearMap.mem_ker.mpr (hg1' _ hm₂)⟩⟩
            (hvalchild _ c₀ (g c₀) hZle hZg (by simp) rfl)
          have hc := Finset.card_le_card (hsubF (Z₂ ⊓ LinearMap.ker g) c₀ (g c₀)
            hZle hZg (by simp) rfl)
          have hΨ := hps5 a b t d hd1
          exact le_trans hIH (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hc)
            (Nat.pow_le_pow_right (by norm_num) hΨ))
      · have hYu : ∀ p : binary_word k × binary_word k, Y p u = g p.1 := by
          intro p
          rw [hY, if_neg huH, hg]
        have hHA' : ∀ w ∈ insert u A, w ∉ H := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact huH
          · exact hHA w hw
        have hA'q : (insert u A).card + (d - 1) ≤ q := by
          have := Finset.card_insert_le u A
          omega
        have hZ₁' : ∀ z : binary_word k,
            z ∈ Z₁ ⊓ LinearMap.ker g ↔ ∀ w ∈ insert u A, C.encode z w = 0 := by
          intro z
          rw [Submodule.mem_inf, LinearMap.mem_ker, hg z, hZ₁ z]
          constructor
          · rintro ⟨hA, hu0⟩ w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hu0
            · exact hA w hw
          · intro h
            exact ⟨fun w hw => h w (Finset.mem_insert_of_mem hw), h u (Finset.mem_insert_self u A)⟩
        have hsubF : ∀ (Z : Submodule (ZMod 2) (binary_word k)) (b₁ : binary_word k) (β : ZMod 2),
            Z ≤ Z₁ → (∀ z : binary_word k, z ∈ Z → g z = 0) → b₁ - b₀ ∈ Z₁ → g b₁ = β →
            (Finset.univ.filter (fun p : binary_word k × binary_word k =>
                p.1 - b₁ ∈ Z ∧ p.2 - c₀ ∈ Z₂ ∧ p.1 i ≠ p.2 i ∧
                binary_oracle_tree_eval (Y p) (Tb β) = some (p.2 i)))
              ⊆ (Finset.univ.filter (fun p : binary_word k × binary_word k =>
                p.1 - b₀ ∈ Z₁ ∧ p.2 - c₀ ∈ Z₂ ∧ p.1 i ≠ p.2 i ∧
                binary_oracle_tree_eval (Y p)
                  (binary_oracle_tree.query u T₀ T₁) = some (p.2 i))) := by
          intro Z b₁ β hZle hZg hb₁ hgb₁ p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          obtain ⟨h1, h2, h3, h4⟩ := hp
          have hgp : g p.1 = β := by
            have h5 : g (p.1 - b₁) = 0 := hZg _ h1
            rw [map_sub, hgb₁, sub_eq_zero] at h5
            exact h5
          refine ⟨?_, h2, h3, ?_⟩
          · have hr : p.1 - b₀ = (p.1 - b₁) + (b₁ - b₀) := by ring
            rw [hr]
            exact Submodule.add_mem _ (hZle h1) hb₁
          · rw [hevalb (Y p) β (by rw [hYu p, hgp])]
            exact h4
        have hvalchild : ∀ (Z : Submodule (ZMod 2) (binary_word k)) (b₁ : binary_word k)
            (β : ZMod 2),
            Z ≤ Z₁ → (∀ z : binary_word k, z ∈ Z → g z = 0) → b₁ - b₀ ∈ Z₁ → g b₁ = β →
            ∀ m : binary_word k, m - b₁ ∈ Z → m - c₀ ∈ Z₂ →
              binary_oracle_tree_eval (C.encode m) (Tb β) = some (m i) := by
          intro Z b₁ β hZle hZg hb₁ hgb₁ m hmz hmc
          have hgm : g m = β := by
            have h5 : g (m - b₁) = 0 := hZg _ hmz
            rw [map_sub, hgb₁, sub_eq_zero] at h5
            exact h5
          have hmZ₁ : m - b₀ ∈ Z₁ := by
            have hr : m - b₀ = (m - b₁) + (b₁ - b₀) := by ring
            rw [hr]
            exact Submodule.add_mem _ (hZle hmz) hb₁
          have h := hval m hmZ₁ hmc
          rw [hevalb (C.encode m) β (by rw [← hg m, hgm])] at h
          exact h
        by_cases hg1 : ∃ z : binary_word k, z ∈ Z₁ ∧ g z = 1
        · obtain ⟨v, hvZ, hgv⟩ := hg1
          obtain ⟨ha1, hcard1⟩ := hhalf Z₁ g v a hvZ hgv hcZ₁
          by_cases hg2 : ∃ z : binary_word k, z ∈ Z₁ ⊓ Z₂ ∧ g z = 1
          · obtain ⟨w, hwZ, hgw⟩ := hg2
            obtain ⟨ht1, hcard12'⟩ := hhalf (Z₁ ⊓ Z₂) g w t hwZ hgw hcZ₁₂
            have hwZ₁ : w ∈ Z₁ := (Submodule.mem_inf.mp hwZ).1
            have hwZ₂ : w ∈ Z₂ := (Submodule.mem_inf.mp hwZ).2
            have hcard12 : (Finset.univ.filter (fun z : binary_word k =>
                z ∈ (Z₁ ⊓ LinearMap.ker g) ⊓ Z₂)).card = 2 ^ (t - 1) := by
              rw [show (Z₁ ⊓ LinearMap.ker g) ⊓ Z₂ = (Z₁ ⊓ Z₂) ⊓ LinearMap.ker g from
                inf_right_comm _ _ _]
              exact hcard12'
            have hZle : Z₁ ⊓ LinearMap.ker g ≤ Z₁ := inf_le_left
            have hZg : ∀ z : binary_word k, z ∈ Z₁ ⊓ LinearMap.ker g → g z = 0 := by
              intro z hz
              exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hz).2
            have hmw₁ : m₀ + w - b₀ ∈ Z₁ := by
              have hr : m₀ + w - b₀ = (m₀ - b₀) + w := by ring
              rw [hr]
              exact Submodule.add_mem _ hm₁ hwZ₁
            have hmw₂ : m₀ + w - c₀ ∈ Z₂ := by
              have hr : m₀ + w - c₀ = (m₀ - c₀) + w := by ring
              rw [hr]
              exact Submodule.add_mem _ hm₂ hwZ₂
            have hgmw : g (m₀ + w) = g m₀ + 1 := by rw [map_add, hgw]
            have hIH₀ := hih (g m₀) (Z₁ ⊓ LinearMap.ker g) Z₂ m₀ c₀ (insert u A)
              (a - 1) b (t - 1) (d - 1) hHA' hA'q (hdepb _) hZ₁' hcard1 hcZ₂ hcard12
              ⟨m₀, by simp, hm₂⟩
              (hvalchild _ m₀ (g m₀) hZle hZg hm₁ rfl)
            have hIH₁ := hih (g m₀ + 1) (Z₁ ⊓ LinearMap.ker g) Z₂ (m₀ + w) c₀ (insert u A)
              (a - 1) b (t - 1) (d - 1) hHA' hA'q (hdepb _) hZ₁' hcard1 hcZ₂ hcard12
              ⟨m₀ + w, by simp, hmw₂⟩
              (hvalchild _ (m₀ + w) (g m₀ + 1) hZle hZg hmw₁ hgmw)
            have hdisj : Disjoint
                (Finset.univ.filter (fun p : binary_word k × binary_word k =>
                  p.1 - m₀ ∈ Z₁ ⊓ LinearMap.ker g ∧ p.2 - c₀ ∈ Z₂ ∧ p.1 i ≠ p.2 i ∧
                  binary_oracle_tree_eval (Y p) (Tb (g m₀)) = some (p.2 i)))
                (Finset.univ.filter (fun p : binary_word k × binary_word k =>
                  p.1 - (m₀ + w) ∈ Z₁ ⊓ LinearMap.ker g ∧ p.2 - c₀ ∈ Z₂ ∧ p.1 i ≠ p.2 i ∧
                  binary_oracle_tree_eval (Y p) (Tb (g m₀ + 1)) = some (p.2 i))) := by
              rw [Finset.disjoint_left]
              intro p hp0 hp1
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp0 hp1
              have e0 : g p.1 = g m₀ := by
                have h5 : g (p.1 - m₀) = 0 := hZg _ hp0.1
                rw [map_sub, sub_eq_zero] at h5
                exact h5
              have e1 : g p.1 = g m₀ + 1 := by
                have h5 : g (p.1 - (m₀ + w)) = 0 := hZg _ hp1.1
                rw [map_sub, hgmw, sub_eq_zero] at h5
                exact h5
              rw [e0] at e1
              exact hne1 (g m₀) e1.symm
            have hsum := le_trans (le_of_eq (Finset.card_union_of_disjoint hdisj).symm)
              (Finset.card_le_card (Finset.union_subset
                (hsubF _ m₀ (g m₀) hZle hZg hm₁ rfl)
                (hsubF _ (m₀ + w) (g m₀ + 1) hZle hZg hmw₁ hgmw)))
            have hΨ := hps2 a b t d htab.1 htab.2 ha1 ht1 hd1
            exact harC _ _ _ _ _ _ _ hIH₀ hIH₁ hsum hΨ (hsucA a b ha1)
          · have hg2' : ∀ z : binary_word k, z ∈ Z₁ ⊓ Z₂ → g z = 0 := by
              intro z hz
              by_contra hzg
              exact hg2 ⟨z, hz, hone _ hzg⟩
            have hZeq2 : (Z₁ ⊓ LinearMap.ker g) ⊓ Z₂ = Z₁ ⊓ Z₂ := by
              refine le_antisymm (inf_le_inf_right _ inf_le_left) ?_
              intro z hz
              exact Submodule.mem_inf.mpr
                ⟨Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hz).1,
                  LinearMap.mem_ker.mpr (hg2' z hz)⟩, (Submodule.mem_inf.mp hz).2⟩
            have hcard12 : (Finset.univ.filter (fun z : binary_word k =>
                z ∈ (Z₁ ⊓ LinearMap.ker g) ⊓ Z₂)).card = 2 ^ t := by
              rw [hZeq2]; exact hcZ₁₂
            have hta1 : t ≤ a - 1 := by
              have h1 : (Finset.univ.filter (fun z : binary_word k => z ∈ Z₁ ⊓ Z₂)).card
                  ≤ (Finset.univ.filter (fun z : binary_word k =>
                    z ∈ Z₁ ⊓ LinearMap.ker g)).card := by
                refine Finset.card_le_card ?_
                intro z hz
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
                rw [← hZeq2] at hz
                exact (Submodule.mem_inf.mp hz).1
              rw [hcard1, hcZ₁₂] at h1
              exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
            have hZle : Z₁ ⊓ LinearMap.ker g ≤ Z₁ := inf_le_left
            have hZg : ∀ z : binary_word k, z ∈ Z₁ ⊓ LinearMap.ker g → g z = 0 := by
              intro z hz
              exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hz).2
            have hIH := hih (g m₀) (Z₁ ⊓ LinearMap.ker g) Z₂ m₀ c₀ (insert u A)
              (a - 1) b t (d - 1) hHA' hA'q (hdepb _) hZ₁' hcard1 hcZ₂ hcard12
              ⟨m₀, by simp, hm₂⟩
              (hvalchild _ m₀ (g m₀) hZle hZg hm₁ rfl)
            have hc := Finset.card_le_card (hsubF (Z₁ ⊓ LinearMap.ker g) m₀ (g m₀)
              hZle hZg hm₁ rfl)
            have hΨ := hps4 a b t d hta1 htab.2 ha1 hd1
            exact harB _ _ _ _ _ _ hIH hc hΨ (hsucA a b ha1)
        · have hg1' : ∀ z : binary_word k, z ∈ Z₁ → g z = 0 := by
            intro z hz
            by_contra hzg
            exact hg1 ⟨z, hz, hone _ hzg⟩
          have hZeq : Z₁ ⊓ LinearMap.ker g = Z₁ := by
            refine le_antisymm inf_le_left ?_
            intro z hz
            exact Submodule.mem_inf.mpr ⟨hz, LinearMap.mem_ker.mpr (hg1' z hz)⟩
          have hcard1 : (Finset.univ.filter (fun z : binary_word k =>
              z ∈ Z₁ ⊓ LinearMap.ker g)).card = 2 ^ a := by rw [hZeq]; exact hcZ₁
          have hcard12 : (Finset.univ.filter (fun z : binary_word k =>
              z ∈ (Z₁ ⊓ LinearMap.ker g) ⊓ Z₂)).card = 2 ^ t := by rw [hZeq]; exact hcZ₁₂
          have hZle : Z₁ ⊓ LinearMap.ker g ≤ Z₁ := inf_le_left
          have hZg : ∀ z : binary_word k, z ∈ Z₁ ⊓ LinearMap.ker g → g z = 0 := by
            intro z hz
            exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hz).2
          have hIH := hih (g b₀) (Z₁ ⊓ LinearMap.ker g) Z₂ b₀ c₀ (insert u A)
            a b t (d - 1) hHA' hA'q (hdepb _) hZ₁' hcard1 hcZ₂ hcard12
            ⟨m₀, Submodule.mem_inf.mpr ⟨hm₁, LinearMap.mem_ker.mpr (hg1' _ hm₁)⟩, hm₂⟩
            (hvalchild _ b₀ (g b₀) hZle hZg (by simp) rfl)
          have hc := Finset.card_le_card (hsubF (Z₁ ⊓ LinearMap.ker g) b₀ (g b₀)
            hZle hZg (by simp) rfl)
          have hΨ := hps5 a b t d hd1
          exact le_trans hIH (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hc)
            (Nat.pow_le_pow_right (by norm_num) hΨ))
  have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : binary_word k, v₀ i = 1 :=
    ⟨fun j => if j = i then 1 else 0, by simp⟩
  have htopcard : (Finset.univ.filter (fun z : binary_word k =>
      z ∈ (⊤ : Submodule (ZMod 2) (binary_word k)))).card = 2 ^ k := by
    rw [Finset.filter_true_of_mem (fun z _ => Submodule.mem_top), Finset.card_univ]
    simp [ZMod.card]
  have htopcard2 : (Finset.univ.filter (fun z : binary_word k =>
      z ∈ (⊤ : Submodule (ZMod 2) (binary_word k)) ⊓ ⊤)).card = 2 ^ k := by
    rw [inf_idem]
    exact htopcard
  set S : Finset (binary_word k × binary_word k) :=
    Finset.univ.filter (fun p : binary_word k × binary_word k => p.1 i ≠ p.2 i) with hSdef
  have hSne : S.Nonempty := by
    refine ⟨(0, v₀), ?_⟩
    rw [hSdef]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hv₀]
    simp
  have hScard : 2 * S.card = 2 ^ (k + k) := by
    have h1 : S.card = (Finset.univ.filter (fun p : binary_word k × binary_word k =>
        ¬ p.1 i ≠ p.2 i)).card := by
      rw [hSdef]
      refine Finset.card_nbij' (fun p => (p.1, p.2 + v₀)) (fun p => (p.1, p.2 + v₀)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hp ⊢
        intro hcon
        apply hcon
        show p.1 i = p.2 i + v₀ i
        rw [hv₀]
        exact (hflip _ _ (Ne.symm hp)).symm
      · intro p hp
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hp ⊢
        show p.1 i ≠ p.2 i + v₀ i
        rw [hv₀]
        have hpe : p.1 i = p.2 i := by
          by_contra hc
          exact hp hc
        rw [hpe]
        exact Ne.symm (hne1 (p.2 i))
      · intro p hp
        show (p.1, p.2 + v₀ + v₀) = p
        rw [add_assoc, hvv v₀, add_zero]
      · intro p hp
        show (p.1, p.2 + v₀ + v₀) = p
        rw [add_assoc, hvv v₀, add_zero]
    have h2 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (binary_word k × binary_word k)))
      (fun p : binary_word k × binary_word k => p.1 i ≠ p.2 i)
    rw [← hSdef, ← h1, Finset.card_univ] at h2
    have h3 : Fintype.card (binary_word k × binary_word k) = 2 ^ (k + k) := by
      simp [ZMod.card, pow_add]
    rw [h3] at h2
    omega
  have hthr : ENNReal.ofReal (binary_soundness_threshold q) * 2 ^ (q / 2) = 1 := by
    rw [binary_soundness_threshold, ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    exact ENNReal.inv_mul_cancel (by simp) (by simp)
  have hNT : ∀ T ∈ (D i).support,
      (S.card : ENNReal) * ENNReal.ofReal (binary_soundness_threshold q)
        ≤ ((S.filter (fun p : binary_word k × binary_word k =>
            binary_oracle_tree_eval (Y p) T = some (p.2 i))).card : ENNReal) := by
    intro T hT
    have hk := key T ⊤ ⊤ 0 0 ∅ k k k q (by simp) (by simp) (hqueries i T hT)
      (by simp) htopcard htopcard htopcard2 ⟨0, by simp, by simp⟩
      (fun m _ _ => hvalid T hT m)
    have hfe : (Finset.univ.filter (fun p : binary_word k × binary_word k =>
          p.1 - 0 ∈ (⊤ : Submodule (ZMod 2) (binary_word k)) ∧
          p.2 - 0 ∈ (⊤ : Submodule (ZMod 2) (binary_word k)) ∧ p.1 i ≠ p.2 i ∧
          binary_oracle_tree_eval (Y p) T = some (p.2 i)))
        = S.filter (fun p : binary_word k × binary_word k =>
          binary_oracle_tree_eval (Y p) T = some (p.2 i)) := by
      rw [hSdef, Finset.filter_filter]
      apply Finset.filter_congr
      intro p _
      simp
    rw [hfe, show min (k - k + q) (min (k - k + q) ((k + k - 2 * k + q) / 2)) = q / 2 from by
      omega] at hk
    have hnat : S.card ≤ (S.filter (fun p : binary_word k × binary_word k =>
        binary_oracle_tree_eval (Y p) T = some (p.2 i))).card * 2 ^ (q / 2) := by
      have h4 : 2 * S.card ≤ 2 * ((S.filter (fun p : binary_word k × binary_word k =>
          binary_oracle_tree_eval (Y p) T = some (p.2 i))).card * 2 ^ (q / 2)) := by
        rw [hScard]
        calc 2 ^ (k + k) ≤ 2 * (S.filter (fun p : binary_word k × binary_word k =>
              binary_oracle_tree_eval (Y p) T = some (p.2 i))).card * 2 ^ (q / 2) := hk
          _ = 2 * ((S.filter (fun p : binary_word k × binary_word k =>
              binary_oracle_tree_eval (Y p) T = some (p.2 i))).card * 2 ^ (q / 2)) := by ring
      exact Nat.le_of_mul_le_mul_left h4 (by norm_num)
    calc (S.card : ENNReal) * ENNReal.ofReal (binary_soundness_threshold q)
        ≤ (((S.filter (fun p : binary_word k × binary_word k =>
            binary_oracle_tree_eval (Y p) T = some (p.2 i))).card * 2 ^ (q / 2) : ℕ) : ENNReal)
          * ENNReal.ofReal (binary_soundness_threshold q) := by
          exact mul_le_mul_right' (Nat.cast_le.mpr hnat) _
      _ = ((S.filter (fun p : binary_word k × binary_word k =>
            binary_oracle_tree_eval (Y p) T = some (p.2 i))).card : ENNReal)
          * (ENNReal.ofReal (binary_soundness_threshold q) * 2 ^ (q / 2)) := by
          push_cast
          ring
      _ = ((S.filter (fun p : binary_word k × binary_word k =>
            binary_oracle_tree_eval (Y p) T = some (p.2 i))).card : ENNReal) := by
          rw [hthr, mul_one]
  have hbig : (S.card : ENNReal) * ENNReal.ofReal (binary_soundness_threshold q)
      ≤ ∑ p ∈ S, (randomized_adaptive_decoder_output D (Y p) i) (some (p.2 i)) := by
    have hterm : ∀ p : binary_word k × binary_word k,
        (randomized_adaptive_decoder_output D (Y p) i) (some (p.2 i))
          = ∑' T, if binary_oracle_tree_eval (Y p) T = some (p.2 i) then (D i) T else 0 := by
      intro p
      rw [randomized_adaptive_decoder_output, PMF.map_apply]
      refine tsum_congr ?_
      intro T
      by_cases hcase : binary_oracle_tree_eval (Y p) T = some (p.2 i)
      · rw [if_pos hcase.symm, if_pos hcase]
      · rw [if_neg (fun hc => hcase hc.symm), if_neg hcase]
    rw [Finset.sum_congr rfl (fun p _ => hterm p),
      ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    have hstep : ∀ T : binary_oracle_tree n (Option (ZMod 2)),
        (S.card : ENNReal) * ENNReal.ofReal (binary_soundness_threshold q) * (D i) T
          ≤ ∑ p ∈ S, if binary_oracle_tree_eval (Y p) T = some (p.2 i) then (D i) T else 0 := by
      intro T
      have hsumc : (∑ p ∈ S, if binary_oracle_tree_eval (Y p) T = some (p.2 i)
            then (D i) T else 0)
          = ((S.filter (fun p : binary_word k × binary_word k =>
            binary_oracle_tree_eval (Y p) T = some (p.2 i))).card : ENNReal) * (D i) T := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rw [hsumc]
      by_cases hT : T ∈ (D i).support
      · exact mul_le_mul_right' (hNT T hT) _
      · have hz : (D i) T = 0 := by
          simpa [PMF.mem_support_iff] using hT
        rw [hz]
        simp
    calc (S.card : ENNReal) * ENNReal.ofReal (binary_soundness_threshold q)
        = (S.card : ENNReal) * ENNReal.ofReal (binary_soundness_threshold q)
            * ∑' T, (D i) T := by rw [PMF.tsum_coe, mul_one]
      _ = ∑' T, (S.card : ENNReal) * ENNReal.ofReal (binary_soundness_threshold q)
            * (D i) T := by rw [ENNReal.tsum_mul_left]
      _ ≤ ∑' T, ∑ p ∈ S, if binary_oracle_tree_eval (Y p) T = some (p.2 i)
            then (D i) T else 0 := ENNReal.tsum_le_tsum hstep
  obtain ⟨p, hpS, hple⟩ : ∃ p ∈ S, ENNReal.ofReal (binary_soundness_threshold q)
      ≤ (randomized_adaptive_decoder_output D (Y p) i) (some (p.2 i)) := by
    by_contra hcon
    have hall : ∀ p ∈ S, (randomized_adaptive_decoder_output D (Y p) i) (some (p.2 i))
        < ENNReal.ofReal (binary_soundness_threshold q) := by
      intro p hp
      exact lt_of_not_ge (fun h => hcon ⟨p, hp, h⟩)
    obtain ⟨p₀, hp₀, hmax⟩ := S.exists_max_image
      (fun p => (randomized_adaptive_decoder_output D (Y p) i) (some (p.2 i))) hSne
    have hlt : (S.card : ENNReal) * (randomized_adaptive_decoder_output D (Y p₀) i)
          (some (p₀.2 i))
        < (S.card : ENNReal) * ENNReal.ofReal (binary_soundness_threshold q) := by
      refine ENNReal.mul_lt_mul_right ?_ ?_ (hall p₀ hp₀)
      · simp only [ne_eq, Nat.cast_eq_zero]
        exact Finset.card_ne_zero_of_mem hp₀
      · exact ENNReal.natCast_ne_top _
    have hle2 : ∑ p ∈ S, (randomized_adaptive_decoder_output D (Y p) i) (some (p.2 i))
        ≤ (S.card : ENNReal) * (randomized_adaptive_decoder_output D (Y p₀) i)
          (some (p₀.2 i)) := by
      calc ∑ p ∈ S, (randomized_adaptive_decoder_output D (Y p) i) (some (p.2 i))
          ≤ ∑ _p ∈ S, (randomized_adaptive_decoder_output D (Y p₀) i) (some (p₀.2 i)) :=
            Finset.sum_le_sum (fun p hp => hmax p hp)
        _ = (S.card : ENNReal) * (randomized_adaptive_decoder_output D (Y p₀) i)
            (some (p₀.2 i)) := by rw [Finset.sum_const, nsmul_eq_mul]
    exact absurd (lt_of_le_of_lt (le_trans hbig hle2) hlt) (lt_irrefl _)
  have hpne : p.1 i ≠ p.2 i := by
    rw [hSdef] at hpS
    simpa using (Finset.mem_filter.mp hpS).2
  refine ⟨p.1, fun u => if u ∈ H then C.encode p.2 u - C.encode p.1 u else 0, ?_, ?_⟩
  · intro u hu
    by_contra huH
    simp only [if_neg huH] at hu
    exact hu rfl
  · have hYeq : C.encode p.1 + (fun u => if u ∈ H then C.encode p.2 u - C.encode p.1 u else 0)
        = Y p := by
      funext u
      rw [hY p u]
      by_cases huH : u ∈ H
      · simp only [Pi.add_apply, if_pos huH]
        ring
      · simp only [Pi.add_apply, if_neg huH]
        ring
    rw [hYeq]
    have hterm : ¬ (some (p.2 i) = some (p.1 i) ∨ some (p.2 i) = (none : Option (ZMod 2))) := by
      rintro (h | h)
      · exact hpne (Option.some_injective _ h).symm
      · exact Option.some_ne_none (p.2 i) h
    have h2 := ENNReal.le_tsum (f := fun z : Option (ZMod 2) =>
      if z = some (p.1 i) ∨ z = none then 0
      else (randomized_adaptive_decoder_output D (Y p) i) z) (some (p.2 i))
    rw [if_neg hterm] at h2
    exact le_trans hple h2

@[blueprint "lem:adaptive-binary-rldc-smoothing"
  (statement := /-- Let $q,k,n$ be natural numbers, let $\delta,s,\alpha$ be real numbers with $0 \leq \delta \leq 1$, $0 \leq s \leq 1$, and $0 \leq \alpha \leq 1$, and suppose that $q>0$ and $\alpha\delta>0$. Let $C \colon \mathbb{F}_2^k \to \mathbb{F}_2^n$ be a binary linear code which is a $(q,\delta,1,s)$-RLDC with a possibly adaptive decoder, and assume $s \leq (1-\alpha)s(q)$, where $s(q)$ is the binary soundness threshold of \cref{def:binary-soundness-threshold}. Then there is a possibly adaptive randomized decoder $L$ with binary output which makes at most $q$ queries, has perfect completeness on every codeword, and has the following strong soundness property: for every $\rho\geq 0$ satisfying $q\rho\leq\alpha\delta$, every message $b$, every message coordinate $i$, and every word $y$ at relative Hamming distance at most $\rho$ from $C(b)$, the probability that $L^y(i)\neq b_i$ is at most $q\rho/(\alpha\delta)$. -/)
  (proof := /-- Let $D$ be the relaxed decoder supplied by \cref{def:is-binary-rldc}, and put $V=C(\mathbb F_2^k)\leq\mathbb F_2^n$.  For each message coordinate $i$, injectivity of the encoder in \cref{def:binary-linear-code} defines a nonzero linear functional
\[
  \lambda_i\colon V\longrightarrow\mathbb F_2,\qquad
  \lambda_i(C(b))=b_i.
\]
Perfect completeness has the following pointwise consequence: every deterministic tree in the support of $D(i)$ returns $\lambda_i(x)$, rather than $\bot$, on every $x\in V$.  Indeed, there are only finitely many codewords, and for each of them the total mass of trees giving any other answer is zero.

Define
\[
 \mathcal R(\lambda)=
 \left\{S\subseteq[n]: |S|\leq q\ \text{and}\
   \lambda(x)=\sum_{u\in S}x_u\ \text{for every }x\in V\right\}.
\]
Suppose that $H$ meets every set in $\mathcal R(\lambda_i)$ and $|H|\leq\delta n$. Apply \cref{lem:adaptive-binary-hitting-attack} to $D$, $i$, and $H$. It gives one message $b$ and one error vector $e$ supported on $H$ for which the relaxed decoding error at $C(b)+e$ is at least $2^{-\lfloor q/2\rfloor}$. Since $|H|\leq\delta n$, this word lies within relative Hamming radius $\delta$ of $C(b)$, so relaxed soundness bounds the same error by $s$. On the other hand, $\alpha\delta>0$, together with the nonnegativity assumptions, gives $\alpha>0$, while \cref{def:binary-soundness-threshold} gives
\[
 s\leq(1-\alpha)2^{-\lfloor q/2\rfloor}
   <2^{-\lfloor q/2\rfloor},
\]
a contradiction.  Consequently every transversal of the finite hypergraph $\mathcal R(\lambda_i)$ has cardinality strictly greater than $\delta n$, and in particular at least $\alpha\delta n$.

We next pass from this transversal bound to a smooth distribution of representations.  Let $\tau^*$ be the fractional transversal number of $\mathcal R(\lambda_i)$.  Since every hyperedge has size at most $q$, a maximal family of pairwise disjoint hyperedges has a union which is a transversal, and linear-programming duality gives
\[
 \tau(\mathcal R(\lambda_i))\leq q\tau^*.
\]
Thus $\tau^*\geq\alpha\delta n/q$.  The dual fractional matching, normalized to have total mass one, is a probability distribution $\mu_i$ on $\mathcal R(\lambda_i)$ satisfying
\[
  \Pr_{S\sim\mu_i}[u\in S]\leq \frac{q}{\alpha\delta n}
  \qquad\text{for every }u\in[n].                                  \tag{2}
\]
This construction uses the entire family of linear representations, not a fixed completion of each relaxed tree.  In particular, for the length-two repetition code the family contains both $\{1\}$ and $\{2\}$; neither singleton is a transversal, and mixing these two representations is consistent with (2).

For each $i$, define $L(i)$ by sampling $S$ according to $\mu_i$, querying the coordinates in $S$, and returning their sum in $\mathbb F_2$.  This is a nonadaptive decoder, hence a possibly adaptive decoder in the sense of \cref{def:randomized-adaptive-decoder}, and it makes at most $q$ queries.  The defining identity for $\mathcal R(\lambda_i)$ gives perfect completeness.  If $y$ differs from $C(b)$ on the coordinate set $F$, an erroneous parity requires $S\cap F\neq\varnothing$.  Therefore (2) and the union bound give
\[
 \Pr[L^y(i)\neq b_i]
 \leq \sum_{u\in F}\Pr[u\in S]
 \leq \frac{q|F|}{\alpha\delta n}
 \leq \frac{q\rho}{\alpha\delta}
\]
whenever $\Delta(y,C(b))\leq\rho n$.  If $n=0$, injectivity forces $k=0$, so the decoder has no target coordinates and all three conclusions are vacuous.  This proves the asserted statement for every $i$ and every admissible $\rho$. -/)
  (title := /-- Smoothing and completion of an adaptive binary relaxed decoder -/)
  (latexEnv := "lemma")]
lemma adaptive_binary_rldc_smoothing {k n q : ℕ} {δ s α : ℝ}
    (C : binary_linear_code k n)
    (hδ_nonnegative : 0 ≤ δ) (hδ_at_most_one : δ ≤ 1)
    (hs_nonnegative : 0 ≤ s) (hs_at_most_one : s ≤ 1)
    (hα_nonnegative : 0 ≤ α) (hα_at_most_one : α ≤ 1)
    (hq_positive : 0 < q) (hαδ_positive : 0 < α * δ)
    (hRLDC : is_binary_rldc C q δ 1 s)
    (hthreshold : s ≤ (1 - α) * binary_soundness_threshold q) :
    ∃ L : randomized_adaptive_decoder n k (ZMod 2),
      decoder_uses_at_most_queries (q := q) L ∧
        (∀ b i,
          randomized_adaptive_decoder_output L (C.encode b) i (b i) ≥
            ENNReal.ofReal 1) ∧
        (∀ ρ : ℝ, 0 ≤ ρ → (q : ℝ) * ρ ≤ α * δ →
          ∀ b i y,
            within_relative_hamming_radius C ρ b y →
              binary_decoding_error
                  (randomized_adaptive_decoder_output L y i) (b i) ≤
                ENNReal.ofReal ((q : ℝ) * ρ / (α * δ))) := by
  classical
  obtain ⟨D, hDq, hDc, hDs⟩ := hRLDC
  have hZMod : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_positive
  have hα_pos : 0 < α := by
    rcases eq_or_lt_of_le hα_nonnegative with h | h
    · exfalso
      rw [← h, zero_mul] at hαδ_positive
      exact lt_irrefl 0 hαδ_positive
    · exact h
  have hδ_pos : 0 < δ := by
    rcases eq_or_lt_of_le hδ_nonnegative with h | h
    · exfalso
      rw [← h, mul_zero] at hαδ_positive
      exact lt_irrefl 0 hαδ_positive
    · exact h
  have hthr_pos : 0 < binary_soundness_threshold q := by
    rw [binary_soundness_threshold]
    positivity
  have hs_lt : s < binary_soundness_threshold q := by
    nlinarith [mul_pos hα_pos hthr_pos]
  have herrformula : ∀ (p : PMF (ZMod 2)) (a : ZMod 2),
      binary_decoding_error p a = p (a + 1) := by
    intro p a
    have huniv : (Finset.univ : Finset (ZMod 2)) = {a, a + 1} := by revert a; decide
    have hne : a ≠ a + 1 := by revert a; decide
    rw [binary_decoding_error, tsum_fintype, huniv, Finset.sum_pair hne, if_pos rfl,
      if_neg (fun hcon => hne hcon.symm), zero_add]
  set mkTree : List (Fin n) → ZMod 2 → binary_oracle_tree n (ZMod 2) :=
    fun l => List.rec (motive := fun _ => ZMod 2 → binary_oracle_tree n (ZMod 2))
      (fun acc => binary_oracle_tree.output acc)
      (fun u _ ih acc => binary_oracle_tree.query u (ih acc) (ih (acc + 1))) l with hmkTree
  have hmknil : ∀ acc : ZMod 2, mkTree [] acc = binary_oracle_tree.output acc :=
    fun _ => rfl
  have hmkcons : ∀ (u : Fin n) (l : List (Fin n)) (acc : ZMod 2),
      mkTree (u :: l) acc =
        binary_oracle_tree.query u (mkTree l acc) (mkTree l (acc + 1)) :=
    fun _ _ _ => rfl
  have hmkdepth : ∀ (l : List (Fin n)) (acc : ZMod 2),
      binary_oracle_tree_depth (mkTree l acc) = l.length := by
    intro l
    induction l with
    | nil => intro acc; rw [hmknil]; rfl
    | cons u l ih =>
        intro acc
        rw [hmkcons]
        simp only [binary_oracle_tree_depth, ih, Nat.max_self, List.length_cons]
        omega
  have hmkeval : ∀ (l : List (Fin n)) (acc : ZMod 2) (yy : binary_word n),
      binary_oracle_tree_eval yy (mkTree l acc) = acc + (l.map yy).sum := by
    intro l
    induction l with
    | nil =>
        intro acc yy
        rw [hmknil]
        simp [binary_oracle_tree_eval]
    | cons u l ih =>
        intro acc yy
        rw [hmkcons]
        by_cases h : yy u = 0
        · have hbranch : binary_oracle_tree_eval yy
              (binary_oracle_tree.query u (mkTree l acc) (mkTree l (acc + 1))) =
              binary_oracle_tree_eval yy (mkTree l acc) := by
            simp only [binary_oracle_tree_eval]
            rw [if_pos h]
          rw [hbranch, ih]
          simp [h]
        · have hbranch : binary_oracle_tree_eval yy
              (binary_oracle_tree.query u (mkTree l acc) (mkTree l (acc + 1))) =
              binary_oracle_tree_eval yy (mkTree l (acc + 1)) := by
            simp only [binary_oracle_tree_eval]
            rw [if_neg h]
          rw [hbranch, ih]
          simp only [List.map_cons, List.sum_cons, hZMod (yy u) h]
          ring
  have hnotrans : ∀ (i : Fin k) (H : Finset (Fin n)),
      (∀ Sset : Finset (Fin n), Sset.card ≤ q →
        (∀ b, (∑ u ∈ Sset, C.encode b u) = b i) → ∃ u ∈ Sset, u ∈ H) →
      δ * (n : ℝ) < (H.card : ℝ) := by
    intro i H hhits
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨b, e, hesupp, herr⟩ :=
      adaptive_binary_hitting_attack C D i H hDq (fun b => hDc b i) hhits
    have hdist : within_relative_hamming_radius C δ b (C.encode b + e) := by
      rw [within_relative_hamming_radius]
      refine le_trans ?_ hcon
      have hsub : (Finset.univ.filter
          fun u => (C.encode b + e) u ≠ C.encode b u) ⊆ H := by
        intro u hu
        refine hesupp u ?_
        intro he0
        exact (Finset.mem_filter.mp hu).2 (by simp [he0])
      have hcards := Finset.card_le_card hsub
      rw [hammingDist]
      exact_mod_cast hcards
    have hbound := hDs b i (C.encode b + e) hdist
    have hchain := le_trans herr hbound
    have hlt : ENNReal.ofReal s < ENNReal.ofReal (binary_soundness_threshold q) :=
      (ENNReal.ofReal_lt_ofReal_iff hthr_pos).mpr hs_lt
    exact absurd hchain (not_le.mpr hlt)
  have hmain : ∀ i : Fin k, ∃ F : Finset (Finset (Fin n)),
      F.Nonempty ∧
      (∀ Sset ∈ F, Sset.card ≤ q) ∧
      (∀ Sset ∈ F, ∀ b, (∑ u ∈ Sset, C.encode b u) = b i) ∧
      (∀ S1 ∈ F, ∀ S2 ∈ F, S1 ≠ S2 → Disjoint S1 S2) ∧
      α * δ * (n : ℝ) < (q : ℝ) * (F.card : ℝ) := by
    intro i
    set Rep : Finset (Finset (Fin n)) :=
      Finset.univ.filter (fun Sset => Sset.card ≤ q ∧
        ∀ b, (∑ u ∈ Sset, C.encode b u) = b i) with hRepdef
    have hmemRep : ∀ Sset : Finset (Fin n), Sset ∈ Rep ↔
        (Sset.card ≤ q ∧ ∀ b, (∑ u ∈ Sset, C.encode b u) = b i) := by
      intro Sset
      simp [hRepdef]
    have hRepne : ∀ Sset ∈ Rep, Sset.Nonempty := by
      intro Sset hSset
      rcases Finset.eq_empty_or_nonempty Sset with h | h
      · exfalso
        have hz := ((hmemRep Sset).mp hSset).2 (Pi.single i 1)
        rw [h] at hz
        simp at hz
      · exact h
    set Pack : Finset (Finset (Finset (Fin n))) :=
      Finset.univ.filter (fun G => (∀ Sset ∈ G, Sset ∈ Rep) ∧
        ∀ S1 ∈ G, ∀ S2 ∈ G, S1 ≠ S2 → Disjoint S1 S2) with hPackdef
    have hmemPack : ∀ G : Finset (Finset (Fin n)), G ∈ Pack ↔
        ((∀ Sset ∈ G, Sset ∈ Rep) ∧
          ∀ S1 ∈ G, ∀ S2 ∈ G, S1 ≠ S2 → Disjoint S1 S2) := by
      intro G
      simp [hPackdef]
    have hPackne : Pack.Nonempty := ⟨∅, (hmemPack ∅).mpr ⟨by simp, by simp⟩⟩
    obtain ⟨F, hFPack, hFmax⟩ := Pack.exists_max_image (fun G => G.card) hPackne
    obtain ⟨hFRep, hFdisj⟩ := (hmemPack F).mp hFPack
    have htrans : ∀ Sset : Finset (Fin n), Sset.card ≤ q →
        (∀ b, (∑ u ∈ Sset, C.encode b u) = b i) →
        ∃ u ∈ Sset, u ∈ F.biUnion id := by
      intro Sset hcard hrep
      by_contra hcon0
      have hcon : ∀ u ∈ Sset, u ∉ F.biUnion id := by
        intro u hu hmem
        exact hcon0 ⟨u, hu, hmem⟩
      have hSsetRep : Sset ∈ Rep := (hmemRep Sset).mpr ⟨hcard, hrep⟩
      have hSsetnotF : Sset ∉ F := by
        intro hmem
        obtain ⟨u, hu⟩ := hRepne Sset hSsetRep
        exact hcon u hu (Finset.mem_biUnion.mpr ⟨Sset, hmem, hu⟩)
      have hdisjnew : ∀ S' ∈ F, Disjoint Sset S' := by
        intro S' hS'
        rw [Finset.disjoint_left]
        intro u hu hu'
        exact hcon u hu (Finset.mem_biUnion.mpr ⟨S', hS', hu'⟩)
      have hins : insert Sset F ∈ Pack := by
        refine (hmemPack _).mpr ⟨?_, ?_⟩
        · intro S' hS'
          rcases Finset.mem_insert.mp hS' with h | h
          · rw [h]; exact hSsetRep
          · exact hFRep S' h
        · intro S1 h1 S2 h2 hne
          rcases Finset.mem_insert.mp h1 with h1' | h1' <;>
            rcases Finset.mem_insert.mp h2 with h2' | h2'
          · exact absurd (h1'.trans h2'.symm) hne
          · rw [h1']; exact hdisjnew S2 h2'
          · rw [h2']; exact (hdisjnew S1 h1').symm
          · exact hFdisj S1 h1' S2 h2' hne
      have hmaxi := hFmax _ hins
      rw [Finset.card_insert_of_notMem hSsetnotF] at hmaxi
      omega
    have hUcard : δ * (n : ℝ) < ((F.biUnion id).card : ℝ) := hnotrans i _ htrans
    have hUle : (F.biUnion id).card ≤ q * F.card := by
      refine le_trans Finset.card_biUnion_le ?_
      calc ∑ Sset ∈ F, (id Sset).card ≤ ∑ _Sset ∈ F, q :=
            Finset.sum_le_sum
              (fun Sset hSset => ((hmemRep Sset).mp (hFRep Sset hSset)).1)
        _ = q * F.card := by simp [Finset.sum_const, mul_comm]
    have hFne : F.Nonempty := by
      rcases Finset.eq_empty_or_nonempty F with h | h
      · exfalso
        rw [h] at hUcard
        simp at hUcard
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      · exact h
    have hcast : ((F.biUnion id).card : ℝ) ≤ (q : ℝ) * (F.card : ℝ) := by
      exact_mod_cast hUle
    refine ⟨F, hFne, ?_, ?_, hFdisj, ?_⟩
    · intro Sset hSset
      exact ((hmemRep Sset).mp (hFRep Sset hSset)).1
    · intro Sset hSset
      exact ((hmemRep Sset).mp (hFRep Sset hSset)).2
    · nlinarith [Nat.cast_nonneg (α := ℝ) n,
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hα_at_most_one) hδ_nonnegative)
          (Nat.cast_nonneg (α := ℝ) n)]
  choose F hFne hFcard hFrep hFdisj hFbound using hmain
  have hFcardpos : ∀ i : Fin k, 0 < (F i).card := fun i => Finset.card_pos.mpr (hFne i)
  have hunifsum : ∀ i : Fin k,
      ∑ Sset ∈ F i, (if Sset ∈ F i then (((F i).card : ENNReal))⁻¹ else 0) = 1 := by
    intro i
    rw [Finset.sum_congr rfl (fun Sset hS => if_pos hS), Finset.sum_const, nsmul_eq_mul]
    refine ENNReal.mul_inv_cancel ?_ (by simp)
    simpa using (hFcardpos i).ne'
  have hunifzero : ∀ (i : Fin k) (Sset : Finset (Fin n)), Sset ∉ F i →
      (if Sset ∈ F i then (((F i).card : ENNReal))⁻¹ else 0) = 0 := by
    intro i Sset h
    simp [h]
  obtain ⟨unif, hunifsupp, hunifapply, hunifvanish⟩ :
      ∃ unif : Fin k → PMF (Finset (Fin n)),
        (∀ (i : Fin k) (Sset : Finset (Fin n)),
          Sset ∈ (unif i).support → Sset ∈ F i) ∧
        (∀ (i : Fin k) (Sset : Finset (Fin n)),
          Sset ∈ F i → unif i Sset = (((F i).card : ENNReal))⁻¹) ∧
        (∀ (i : Fin k) (Sset : Finset (Fin n)),
          Sset ∉ F i → unif i Sset = 0) := by
    refine ⟨fun i => PMF.ofFinset
      (fun Sset => if Sset ∈ F i then (((F i).card : ENNReal))⁻¹ else 0) (F i)
      (hunifsum i) (hunifzero i), ?_, ?_, ?_⟩
    · intro i Sset hS
      exact ((PMF.mem_support_ofFinset_iff _ _ Sset).mp hS).1
    · intro i Sset hS
      simp [hS]
    · intro i Sset hS
      simp [hS]
  refine ⟨fun i => PMF.map (fun Sset => mkTree Sset.toList 0) (unif i), ?_, ?_, ?_⟩
  · intro i tree htree
    rw [PMF.support_map] at htree
    obtain ⟨Sset, hS, hst⟩ := htree
    rw [← hst, hmkdepth, Finset.length_toList]
    exact hFcard i Sset (hunifsupp i Sset hS)
  · intro b i
    have hmap : PMF.map (binary_oracle_tree_eval (C.encode b))
        (PMF.map (fun Sset => mkTree Sset.toList 0) (unif i)) =
        PMF.map (fun Sset =>
          binary_oracle_tree_eval (C.encode b) (mkTree Sset.toList 0)) (unif i) := by
      rw [PMF.map_comp]
      rfl
    rw [randomized_adaptive_decoder_output, hmap, PMF.map_apply]
    rw [ge_iff_le, ENNReal.ofReal_one, ← PMF.tsum_coe (unif i)]
    refine ENNReal.tsum_le_tsum ?_
    intro Sset
    by_cases hS : Sset ∈ F i
    · have hval : binary_oracle_tree_eval (C.encode b) (mkTree Sset.toList 0) = b i := by
        rw [hmkeval, zero_add, Finset.sum_map_toList]
        exact hFrep i Sset hS b
      exact le_of_eq (if_pos hval.symm).symm
    · rw [hunifvanish i Sset hS]
      simp
  · intro ρ hρ hqρ b i y hy
    have hmap : PMF.map (binary_oracle_tree_eval y)
        (PMF.map (fun Sset => mkTree Sset.toList 0) (unif i)) =
        PMF.map (fun Sset =>
          binary_oracle_tree_eval y (mkTree Sset.toList 0)) (unif i) := by
      rw [PMF.map_comp]
      rfl
    rw [randomized_adaptive_decoder_output, hmap, herrformula, PMF.map_apply]
    set Err : Finset (Fin n) := Finset.univ.filter (fun u => y u ≠ C.encode b u)
      with hErrdef
    set Bad : Finset (Finset (Fin n)) :=
      (F i).filter (fun Sset => ∃ u ∈ Sset, u ∈ Err) with hBaddef
    have hErrcard : hammingDist y (C.encode b) = Err.card := by
      rw [hammingDist, hErrdef]
    have hErrρ : (Err.card : ℝ) ≤ ρ * (n : ℝ) := by
      rw [within_relative_hamming_radius, hErrcard] at hy
      exact hy
    have hBadErr : Bad.card ≤ Err.card := by
      rcases Finset.eq_empty_or_nonempty Bad with hBe | hBn
      · rw [hBe]
        simp
      · obtain ⟨S0, hS0⟩ := hBn
        obtain ⟨u0, hu0S, hu0E⟩ := (Finset.mem_filter.mp hS0).2
        have hchoice : ∀ Sset : Finset (Fin n), ∃ u : Fin n,
            Sset ∈ Bad → (u ∈ Sset ∧ u ∈ Err) := by
          intro Sset
          by_cases h : Sset ∈ Bad
          · obtain ⟨u, hu1, hu2⟩ := (Finset.mem_filter.mp h).2
            exact ⟨u, fun _ => ⟨hu1, hu2⟩⟩
          · exact ⟨u0, fun hc => absurd hc h⟩
        choose pick hpick using hchoice
        refine Finset.card_le_card_of_injOn pick
          (fun Sset hSset => (hpick Sset hSset).2) ?_
        intro S1 h1 S2 h2 heq
        by_contra hne
        have h1' : S1 ∈ Bad := Finset.mem_coe.mp h1
        have h2' : S2 ∈ Bad := Finset.mem_coe.mp h2
        have hd := hFdisj i S1 (Finset.mem_filter.mp h1').1 S2
          (Finset.mem_filter.mp h2').1 hne
        rw [Finset.disjoint_left] at hd
        have hmem2 : pick S1 ∈ S2 := by
          rw [heq]
          exact (hpick S2 h2').1
        exact hd (hpick S1 h1').1 hmem2
    refine le_trans (ENNReal.tsum_le_tsum
      (g := fun Sset : Finset (Fin n) =>
        if Sset ∈ Bad then (((F i).card : ENNReal))⁻¹ else 0) ?_) ?_
    · intro Sset
      by_cases hS : Sset ∈ F i
      · by_cases hb : b i + 1 = binary_oracle_tree_eval y (mkTree Sset.toList 0)
        · have hBadmem : Sset ∈ Bad := by
            by_contra hcon
            have hnone : ∀ u ∈ Sset, u ∉ Err := by
              intro u hu hue
              exact hcon (Finset.mem_filter.mpr ⟨hS, ⟨u, hu, hue⟩⟩)
            have hsum : (∑ u ∈ Sset, y u) = ∑ u ∈ Sset, C.encode b u := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              by_contra hcon2
              exact hnone u hu (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hcon2⟩)
            have hval : binary_oracle_tree_eval y (mkTree Sset.toList 0) = b i := by
              rw [hmkeval, zero_add, Finset.sum_map_toList, hsum]
              exact hFrep i Sset hS b
            rw [hval] at hb
            have hne1 : ∀ z : ZMod 2, z + 1 ≠ z := by decide
            exact hne1 (b i) hb
          rw [if_pos hb, if_pos hBadmem]
          exact le_of_eq (hunifapply i Sset hS)
        · rw [if_neg hb]
          simp
      · rw [hunifvanish i Sset hS]
        simp
    rw [tsum_fintype, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul]
    have htpos : (0 : ℝ) < ((F i).card : ℝ) := by exact_mod_cast hFcardpos i
    have hreal : (Bad.card : ℝ) / ((F i).card : ℝ) ≤ (q : ℝ) * ρ / (α * δ) := by
      rw [div_le_div_iff₀ htpos hαδ_positive]
      have hBadErrR : (Bad.card : ℝ) ≤ ρ * (n : ℝ) :=
        le_trans (by exact_mod_cast hBadErr) hErrρ
      have h2 : ρ * (α * δ * (n : ℝ)) ≤ ρ * ((q : ℝ) * ((F i).card : ℝ)) :=
        mul_le_mul_of_nonneg_left (le_of_lt (hFbound i)) hρ
      nlinarith [mul_le_mul_of_nonneg_right hBadErrR (le_of_lt hαδ_positive)]
    calc (Bad.card : ENNReal) * (((F i).card : ENNReal))⁻¹
        = ENNReal.ofReal ((Bad.card : ℝ) / ((F i).card : ℝ)) := by
          rw [ENNReal.ofReal_div_of_pos htpos, ENNReal.ofReal_natCast,
            ENNReal.ofReal_natCast, ENNReal.div_eq_inv_mul, mul_comm]
      _ ≤ ENNReal.ofReal ((q : ℝ) * ρ / (α * δ)) := ENNReal.ofReal_le_ofReal hreal

@[blueprint "thm:rldc-soundness-threshold"
  (statement := /-- Let $q,k,n$ be natural numbers, let $\delta,s,\alpha$ be real numbers satisfying $0 \leq \delta \leq 1$, $0 \leq s \leq 1$, and $0 \leq \alpha \leq 1$, and let $C \colon \mathbb{F}_2^k \to \mathbb{F}_2^n$ be a binary linear code. Assume that $C$ is a $(q,\delta,1,s)$-RLDC with a possibly adaptive decoder in the sense of \cref{def:is-binary-rldc}, and that $s \leq (1-\alpha)s(q)$ for the threshold $s(q)$ of \cref{def:binary-soundness-threshold}. Then, for every real $\varepsilon>0$, the code $C$ is a $(q,\alpha\delta\varepsilon/q,1,\varepsilon)$-LDC in the sense of \cref{def:is-binary-ldc}. -/)
  (proof := /-- If $q=0$ or $\alpha\delta=0$, the requested radius is zero. Replace every $\bot$-leaf of the relaxed decoder by zero. Perfect completeness ensures that the resulting decoder is correct on every codeword, which proves the assertion at radius zero. The same completion works when $\varepsilon\geq 1$, since the error probability of any binary-valued decoder is at most one.

It remains to consider $q>0$, $\alpha\delta>0$, and $0<\varepsilon<1$. Apply \cref{lem:adaptive-binary-rldc-smoothing} and set $\rho=\alpha\delta\varepsilon/q$. Then $\rho\geq0$ and
\[
 q\rho=\alpha\delta\varepsilon\leq\alpha\delta.
\]
The strong soundness estimate of that lemma is
\[
 \Pr[L^y(i)\neq b_i]
 \leq \frac{q\rho}{\alpha\delta}
 =\varepsilon
\]
whenever $y$ is within relative Hamming distance $\rho$ of $C(b)$. The decoder supplied there still makes at most $q$ queries and has perfect completeness, so it witnesses \cref{def:is-binary-ldc} with the required parameters. -/)
  (title := /-- Soundness error threshold for binary relaxed local decoding -/)
  (latexEnv := "theorem")]
theorem rldc_soundness_threshold {k n q : ℕ} {δ s α : ℝ}
    (C : binary_linear_code k n)
    (hδ_nonnegative : 0 ≤ δ) (hδ_at_most_one : δ ≤ 1)
    (hs_nonnegative : 0 ≤ s) (hs_at_most_one : s ≤ 1)
    (hα_nonnegative : 0 ≤ α) (hα_at_most_one : α ≤ 1)
    (hRLDC : is_binary_rldc C q δ 1 s)
    (hthreshold : s ≤ (1 - α) * binary_soundness_threshold q)
    (ε : ℝ) (hε : 0 < ε) :
    is_binary_ldc C q (α * δ * ε / (q : ℝ)) 1 ε := by
  classical
  have herr_le_one : ∀ (p : PMF (ZMod 2)) (a : ZMod 2), binary_decoding_error p a ≤ 1 := by
    intro p a
    rw [binary_decoding_error]
    calc ∑' z, (if z = a then 0 else p z) ≤ ∑' z, p z :=
          ENNReal.tsum_le_tsum (fun z => by split; exacts [bot_le, le_rfl])
      _ = 1 := p.tsum_coe
  have herr_zero : ∀ (p : PMF (ZMod 2)) (a : ZMod 2), 1 ≤ p a →
      binary_decoding_error p a = 0 := by
    intro p a ha
    have hpa : p a = 1 := le_antisymm (PMF.coe_le_one p a) ha
    have hsupp : p.support = {a} := (PMF.apply_eq_one_iff p a).mp hpa
    have hzero : ∀ z : ZMod 2, z ≠ a → p z = 0 := by
      intro z hz
      refine (PMF.apply_eq_zero_iff p z).mpr ?_
      rw [hsupp]
      simpa using hz
    rw [binary_decoding_error]
    refine ENNReal.tsum_eq_zero.mpr ?_
    intro z
    by_cases hz : z = a
    · simp [hz]
    · simp [hz, hzero z hz]
  obtain ⟨D, hDq, hDc, hDs⟩ := hRLDC
  set conv : binary_oracle_tree n (Option (ZMod 2)) → binary_oracle_tree n (ZMod 2) :=
    fun t => binary_oracle_tree.rec (fun a => .output (a.getD 0))
      (fun u _ _ t0 t1 => .query u t0 t1) t with hconv
  have hconvout : ∀ a : Option (ZMod 2),
      conv (binary_oracle_tree.output a) = binary_oracle_tree.output (a.getD 0) := by
    intro a; rfl
  have hconvquery : ∀ (u : Fin n) (z o : binary_oracle_tree n (Option (ZMod 2))),
      conv (binary_oracle_tree.query u z o) =
        binary_oracle_tree.query u (conv z) (conv o) := by
    intro u z o; rfl
  have hdepth : ∀ t : binary_oracle_tree n (Option (ZMod 2)),
      binary_oracle_tree_depth (conv t) = binary_oracle_tree_depth t := by
    intro t
    induction t with
    | output a => rw [hconvout]; rfl
    | query u z o ihz iho =>
        rw [hconvquery]
        simp only [binary_oracle_tree_depth, ihz, iho]
  have hev : ∀ (y : binary_word n) (t : binary_oracle_tree n (Option (ZMod 2))),
      binary_oracle_tree_eval y (conv t) = (binary_oracle_tree_eval y t).getD 0 := by
    intro y t
    induction t with
    | output a => rw [hconvout]; rfl
    | query u z o ihz iho =>
        rw [hconvquery]
        by_cases h : y u = 0
        · simp only [binary_oracle_tree_eval, h, if_pos, ihz, if_true]
        · simp only [binary_oracle_tree_eval, h, if_false, iho]
  set L : randomized_adaptive_decoder n k (ZMod 2) :=
    fun i => PMF.map conv (D i) with hL
  have hLq : decoder_uses_at_most_queries (q := q) L := by
    intro i tree htree
    have htree' : tree ∈ (PMF.map conv (D i)).support := htree
    rw [PMF.support_map] at htree'
    obtain ⟨t, ht, htq⟩ := htree'
    rw [← htq, hdepth]
    exact hDq i t ht
  have hLc : ∀ (b : binary_word k) (i : Fin k),
      randomized_adaptive_decoder_output L (C.encode b) i (b i) ≥ ENNReal.ofReal 1 := by
    intro b i
    have h := hDc b i
    rw [randomized_adaptive_decoder_output, PMF.map_apply] at h
    rw [hL, randomized_adaptive_decoder_output, PMF.map_comp, PMF.map_apply]
    refine le_trans h (ENNReal.tsum_le_tsum ?_)
    intro t
    by_cases h1 : some (b i) = binary_oracle_tree_eval (C.encode b) t
    · rw [if_pos h1, if_pos (show b i = (Function.comp
        (binary_oracle_tree_eval (C.encode b)) conv) t from by
          simp [Function.comp, hev, ← h1])]
    · rw [if_neg h1]
      exact bot_le
  rcases le_or_gt 1 ε with hε1 | hε1
  · refine ⟨L, hLq, hLc, ?_⟩
    intro b i y _
    refine le_trans (herr_le_one _ _) ?_
    simpa using ENNReal.ofReal_le_ofReal hε1
  · rcases eq_or_lt_of_le (mul_nonneg hα_nonnegative hδ_nonnegative) with hαδ | hαδ
    · refine ⟨L, hLq, hLc, ?_⟩
      intro b i y hy
      rw [within_relative_hamming_radius, show α * δ * ε / (q : ℝ) = 0 by
        rw [show α * δ * ε = 0 by rw [← hαδ]; ring]; simp] at hy
      have hy0 : hammingDist y (C.encode b) = 0 := by
        have := Nat.cast_nonneg (α := ℝ) (hammingDist y (C.encode b))
        simp only [zero_mul] at hy
        exact Nat.cast_eq_zero.mp (le_antisymm hy this)
      have hyeq : y = C.encode b := by
        have := hammingDist_eq_zero.mp hy0
        exact this
      rw [hyeq, herr_zero _ _ (by simpa using hLc b i)]
      exact bot_le
    · rcases Nat.eq_zero_or_pos q with hq | hq
      · refine ⟨L, hLq, hLc, ?_⟩
        intro b i y hy
        rw [within_relative_hamming_radius, hq] at hy
        simp only [Nat.cast_zero, div_zero, zero_mul] at hy
        have hy0 : hammingDist y (C.encode b) = 0 :=
          Nat.cast_eq_zero.mp
            (le_antisymm hy (Nat.cast_nonneg (α := ℝ) (hammingDist y (C.encode b))))
        rw [hammingDist_eq_zero.mp hy0, herr_zero _ _ (by simpa using hLc b i)]
        exact bot_le
      · have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
        obtain ⟨L', hL'q, hL'c, hL's⟩ :=
          adaptive_binary_rldc_smoothing C hδ_nonnegative hδ_at_most_one
            hs_nonnegative hs_at_most_one hα_nonnegative hα_at_most_one hq hαδ
            ⟨D, hDq, hDc, hDs⟩ hthreshold
        refine ⟨L', hL'q, hL'c, ?_⟩
        intro b i y hy
        have hρ : (0 : ℝ) ≤ α * δ * ε / (q : ℝ) := by positivity
        have hqρ : (q : ℝ) * (α * δ * ε / (q : ℝ)) ≤ α * δ := by
          rw [mul_div_cancel₀ _ (ne_of_gt hqR)]
          nlinarith [hαδ, hε1.le, hε]
        have hval : (q : ℝ) * (α * δ * ε / (q : ℝ)) / (α * δ) = ε := by
          rw [mul_div_cancel₀ _ (ne_of_gt hqR), mul_comm (α * δ) ε, mul_div_assoc,
            div_self (ne_of_gt hαδ), mul_one]
        have := hL's (α * δ * ε / (q : ℝ)) hρ hqρ b i y hy
        rwa [hval] at this

@[blueprint "lem:binary-linear-code-information-set-containing-coordinate"
  (statement := /-- Let $C \colon \mathbb{F}_2^k \to \mathbb{F}_2^n$ be a binary linear code and let $u$ be a codeword coordinate whose induced linear functional on messages is nonzero. Then there are a linear automorphism $e$ of the message space, a map $\sigma \colon \operatorname{Fin}(k) \to \operatorname{Fin}(n)$, and an index $i$ such that the coordinates indexed by $\sigma$ recover every coordinate of $e$, while the coordinate indexed by $\sigma(i)$ agrees with coordinate $u$ on every codeword. -/)
  (proof := /-- The coordinate functionals of the encoder span the dual message space because the encoder is injective and hence its dual map is surjective. Extend the nonzero functional at $u$ to a basis contained in this spanning family and reindex that basis by $\operatorname{Fin}(k)$. Evaluation on the resulting basis is an injective linear endomorphism of $\mathbb{F}_2^k$, hence a linear automorphism. Choosing, for each basis vector, a codeword coordinate that realizes it gives $\sigma$; the basis vector extending the functional at $u$ supplies $i$ and the two asserted identities. -/)
  (title := /-- An information set containing a prescribed nonzero coordinate -/)
  (latexEnv := "lemma")]
lemma binary_linear_code_information_set_containing_coordinate {k n : ℕ}
    (C : binary_linear_code k n) (u : Fin n)
    (hu : C.encode.dualMap ((Pi.basisFun (ZMod 2) (Fin n)).dualBasis u) ≠ 0) :
    ∃ (e : binary_word k ≃ₗ[ZMod 2] binary_word k) (σ : Fin k → Fin n) (i : Fin k),
      (∀ b, C.encode b (σ i) = C.encode b u) ∧
      (∀ b j, C.encode (e.symm b) (σ j) = b j) := by
  let d : Module.Basis (Fin n) (ZMod 2) (Module.Dual (ZMod 2) (binary_word n)) :=
    (Pi.basisFun (ZMod 2) (Fin n)).dualBasis
  let row : Fin n → Module.Dual (ZMod 2) (binary_word k) :=
    fun v => C.encode.dualMap (d v)
  have hspan : Submodule.span (ZMod 2) (Set.range row) = ⊤ := by
    have hrange : Set.range row = C.encode.dualMap '' Set.range d := by
      ext φ
      simp [row]
    rw [hrange, ← LinearMap.map_span, d.span_eq]
    simpa only [Submodule.map_top] using
      C.encode.dualMap.range_eq_top_of_surjective
        (C.encode.dualMap_surjective_of_injective C.injective)
  have hrow : row u ≠ 0 := by
    simpa [row, d] using hu
  have hs : LinearIndepOn (ZMod 2) id {row u} :=
    LinearIndepOn.singleton hrow
  have hst : {row u} ⊆ Set.range row := by
    intro φ hφ
    simp only [Set.mem_singleton_iff] at hφ
    exact ⟨u, hφ.symm⟩
  have ht : ⊤ ≤ Submodule.span (ZMod 2) (Set.range row) := hspan.ge
  let B₀ := Module.Basis.extendLe hs hst ht
  let d' : Module.Basis (Fin k) (ZMod 2) (Module.Dual (ZMod 2) (binary_word k)) :=
    (Pi.basisFun (ZMod 2) (Fin k)).dualBasis
  let B := B₀.reindex (B₀.indexEquiv d')
  have hBsub : Set.range B ⊆ Set.range row := by
    change Set.range (B₀.reindex (B₀.indexEquiv d')) ⊆ Set.range row
    rw [Module.Basis.range_reindex]
    exact Module.Basis.extendLe_subset hs hst ht
  have hBcontains : row u ∈ Set.range B := by
    change row u ∈ Set.range (B₀.reindex (B₀.indexEquiv d'))
    rw [Module.Basis.range_reindex]
    exact Module.Basis.subset_extendLe hs hst ht (Set.mem_singleton (row u))
  have hchoice : ∀ j : Fin k, ∃ v : Fin n, B j = row v := by
    intro j
    rcases hBsub ⟨j, rfl⟩ with ⟨v, hv⟩
    exact ⟨v, hv.symm⟩
  choose σ hσ using hchoice
  rcases hBcontains with ⟨i, hi⟩
  let f : binary_word k →ₗ[ZMod 2] binary_word k :=
    { toFun := fun b j => B j b
      map_add' := by
        intro x y
        ext j
        exact (B j).map_add x y
      map_smul' := by
        intro a x
        ext j
        exact (B j).map_smul a x }
  have hf_injective : Function.Injective f := by
    intro x y hxy
    apply (Pi.basisFun (ZMod 2) (Fin k)).eval_injective
    apply B.ext
    intro j
    exact congrFun hxy j
  have hf_surjective : Function.Surjective f :=
    LinearMap.injective_iff_surjective.mp hf_injective
  let e : binary_word k ≃ₗ[ZMod 2] binary_word k :=
    LinearEquiv.ofBijective f ⟨hf_injective, hf_surjective⟩
  refine ⟨e, σ, i, ?_, ?_⟩
  · intro b
    have hrows : row (σ i) = row u := by
      rw [← hσ i, hi]
    simpa [row, d] using LinearMap.congr_fun hrows b
  · intro b j
    have hfb : f (e.symm b) = b := by
      exact e.apply_symm_apply b
    have hcoord := congrFun hfb j
    change B j (e.symm b) = b j at hcoord
    rw [show B j = row (σ j) from hσ j] at hcoord
    simpa [f, row, d] using hcoord

@[blueprint "lem:binary-rlcc-nonzero-coordinate-full-decoder"
  (statement := /-- Let $C$ be a binary $(q,\delta,1,s)$-RLCC satisfying the binary soundness-threshold hypothesis. For every codeword coordinate $u$ whose induced message functional is nonzero and every $\varepsilon>0$, there is a randomized adaptive decoder for coordinate $u$ which uses at most $q$ queries, has perfect completeness, and has error at most $\varepsilon$ within relative radius $\alpha\delta\varepsilon/q$. -/)
  (proof := /-- Apply \cref{lem:binary-linear-code-information-set-containing-coordinate} to extend the functional at $u$ to an information set. Reparameterize the message space by the associated automorphism and restrict the RLCC decoder to the selected codeword coordinates; the information-set identities make this a relaxed local decoder for the reparameterized code. Apply \cref{thm:rldc-soundness-threshold}, then select the decoded message coordinate corresponding to $u$ and transport completeness and soundness back through the reparameterization. -/)
  (title := /-- Full decoding of a nonzero RLCC coordinate -/)
  (latexEnv := "lemma")]
lemma binary_rlcc_nonzero_coordinate_full_decoder {k n q : ℕ} {δ s α : ℝ}
    (C : binary_linear_code k n)
    (hδ_nonnegative : 0 ≤ δ) (hδ_at_most_one : δ ≤ 1)
    (hs_nonnegative : 0 ≤ s) (hs_at_most_one : s ≤ 1)
    (hα_nonnegative : 0 ≤ α) (hα_at_most_one : α ≤ 1)
    (hRLCC : is_binary_rlcc C q δ 1 s)
    (hthreshold : s ≤ (1 - α) * binary_soundness_threshold q)
    (ε : ℝ) (hε : 0 < ε) (u : Fin n)
    (hu : C.encode.dualMap ((Pi.basisFun (ZMod 2) (Fin n)).dualBasis u) ≠ 0) :
    ∃ Du : PMF (binary_oracle_tree n (ZMod 2)),
      (∀ tree, tree ∈ Du.support → binary_oracle_tree_depth tree ≤ q) ∧
      (∀ b,
        PMF.map (binary_oracle_tree_eval (C.encode b)) Du (C.encode b u) ≥
          ENNReal.ofReal 1) ∧
      (∀ b y,
        within_relative_hamming_radius C (α * δ * ε / (q : ℝ)) b y →
          binary_decoding_error (PMF.map (binary_oracle_tree_eval y) Du) (C.encode b u) ≤
            ENNReal.ofReal ε) := by
  obtain ⟨e, σ, i, htarget, hcoord⟩ :=
    binary_linear_code_information_set_containing_coordinate C u hu
  let C' : binary_linear_code k n :=
    { encode := C.encode.comp e.symm.toLinearMap
      injective := C.injective.comp e.symm.injective }
  obtain ⟨D, hDqueries, hDcomplete, hDsound⟩ := hRLCC
  have hRLDC' : is_binary_rldc C' q δ 1 s := by
    refine ⟨fun j => D (σ j), ?_, ?_, ?_⟩
    · intro j tree htree
      exact hDqueries (σ j) tree htree
    · intro b j
      simpa [C', randomized_adaptive_decoder_output, hcoord b j] using
        hDcomplete (e.symm b) (σ j)
    · intro b j y hy
      have hy' : within_relative_hamming_radius C δ (e.symm b) y := by
        simpa [within_relative_hamming_radius, C'] using hy
      simpa [C', randomized_adaptive_decoder_output, hcoord b j] using
        hDsound (e.symm b) (σ j) y hy'
  obtain ⟨L, hLqueries, hLcomplete, hLsound⟩ :=
    rldc_soundness_threshold C' hδ_nonnegative hδ_at_most_one hs_nonnegative
      hs_at_most_one hα_nonnegative hα_at_most_one hRLDC' hthreshold ε hε
  refine ⟨L i, ?_, ?_, ?_⟩
  · intro tree htree
    exact hLqueries i tree htree
  · intro b
    have hbit : e b i = C.encode b u := by
      rw [← htarget b, ← hcoord (e b) i]
      simp
    simpa [C', randomized_adaptive_decoder_output, hbit] using hLcomplete (e b) i
  · intro b y hy
    have hy' :
        within_relative_hamming_radius C' (α * δ * ε / (q : ℝ)) (e b) y := by
      simpa [within_relative_hamming_radius, C'] using hy
    have hbit : e b i = C.encode b u := by
      rw [← htarget b, ← hcoord (e b) i]
      simp
    simpa [randomized_adaptive_decoder_output, hbit] using hLsound (e b) i y hy'

@[blueprint "lem:binary-zero-coordinate-full-decoder"
  (statement := /-- Let $C$ be a binary linear code and let $u$ be a codeword coordinate whose induced linear functional on messages is zero. For every natural query bound $q$ and all real parameters $\rho$ and $\varepsilon$, there is a decoder for coordinate $u$ using at most $q$ queries, with perfect completeness and error at most $\operatorname{ofReal}(\varepsilon)$ throughout the radius-$\rho$ Hamming balls. -/)
  (proof := /-- The vanishing coordinate functional implies that coordinate $u$ equals zero on every codeword. Use the deterministic depth-zero oracle tree that always outputs zero. Its output is therefore correct on every uncorrupted codeword and, independently of the received word, has decoding error zero, which is at most the nonnegative extended real number $\operatorname{ofReal}(\varepsilon)$. -/)
  (title := /-- Constant decoding of a zero code coordinate -/)
  (latexEnv := "lemma")]
lemma binary_zero_coordinate_full_decoder {k n q : ℕ} (C : binary_linear_code k n)
    (u : Fin n)
    (hu : C.encode.dualMap ((Pi.basisFun (ZMod 2) (Fin n)).dualBasis u) = 0)
    (ρ ε : ℝ) :
    ∃ Du : PMF (binary_oracle_tree n (ZMod 2)),
      (∀ tree, tree ∈ Du.support → binary_oracle_tree_depth tree ≤ q) ∧
      (∀ b,
        PMF.map (binary_oracle_tree_eval (C.encode b)) Du (C.encode b u) ≥
          ENNReal.ofReal 1) ∧
      (∀ b y,
        within_relative_hamming_radius C ρ b y →
          binary_decoding_error (PMF.map (binary_oracle_tree_eval y) Du) (C.encode b u) ≤
            ENNReal.ofReal ε) := by
  have hzero : ∀ b, C.encode b u = 0 := by
    intro b
    have hb := LinearMap.congr_fun hu b
    simpa using hb
  refine ⟨PMF.pure (.output 0), ?_, ?_, ?_⟩
  · intro tree htree
    have htree' : tree = binary_oracle_tree.output 0 := by
      simpa only [PMF.support_pure, Set.mem_singleton_iff] using htree
    rw [htree']
    simp [binary_oracle_tree_depth]
  · intro b
    rw [hzero b]
    have hmap : PMF.map (binary_oracle_tree_eval (C.encode b))
        (PMF.pure (binary_oracle_tree.output (0 : ZMod 2))) =
          PMF.pure (0 : ZMod 2) := by
      simpa [binary_oracle_tree_eval] using
        (PMF.pure_map (f := binary_oracle_tree_eval (C.encode b))
          (binary_oracle_tree.output (0 : ZMod 2)))
    calc
      (PMF.map (binary_oracle_tree_eval (C.encode b))
          (PMF.pure (binary_oracle_tree.output (0 : ZMod 2)))) 0 =
          (PMF.pure (0 : ZMod 2)) 0 :=
        congrArg (fun p : PMF (ZMod 2) => p 0) hmap
      _ = 1 := by simp
      _ ≥ ENNReal.ofReal 1 := by simp
  · intro b y _
    rw [hzero b]
    have hmap : PMF.map (binary_oracle_tree_eval y)
        (PMF.pure (binary_oracle_tree.output (0 : ZMod 2))) =
          PMF.pure (0 : ZMod 2) := by
      simpa [binary_oracle_tree_eval] using
        (PMF.pure_map (f := binary_oracle_tree_eval y)
          (binary_oracle_tree.output (0 : ZMod 2)))
    calc
      binary_decoding_error (PMF.map (binary_oracle_tree_eval y)
          (PMF.pure (binary_oracle_tree.output (0 : ZMod 2)))) 0 =
          binary_decoding_error (PMF.pure (0 : ZMod 2)) 0 :=
        congrArg (fun p : PMF (ZMod 2) => binary_decoding_error p 0) hmap
      _ = 0 := by simp [binary_decoding_error, PMF.pure_apply]
      _ ≤ ENNReal.ofReal ε := bot_le

@[blueprint "thm:rlcc-soundness-threshold"
  (statement := /-- Let $q,k,n$ be natural numbers, let $\delta,s,\alpha$ be real numbers satisfying $0 \leq \delta \leq 1$, $0 \leq s \leq 1$, and $0 \leq \alpha \leq 1$, and let $C \colon \mathbb{F}_2^k \to \mathbb{F}_2^n$ be a binary linear code. Assume that $C$ is a $(q,\delta,1,s)$-RLCC with a possibly adaptive decoder in the sense of \cref{def:is-binary-rlcc}, and that $s \leq (1-\alpha)s(q)$ for the threshold $s(q)$ of \cref{def:binary-soundness-threshold}. Then, for every real $\varepsilon>0$, the code $C$ is a $(q,\alpha\delta\varepsilon/q,1,\varepsilon)$-LCC in the sense of \cref{def:is-binary-lcc}. -/)
  (proof := /-- For each codeword coordinate $u$, consider its induced linear functional on the message space. If it is nonzero, \cref{lem:binary-rlcc-nonzero-coordinate-full-decoder} supplies a $q$-query full decoder with perfect completeness and error at most $\varepsilon$ in radius $\alpha\delta\varepsilon/q$. If the functional is zero, \cref{lem:binary-zero-coordinate-full-decoder} supplies the depth-zero decoder that constantly outputs zero, with the same guarantees. Choose the appropriate decoder for every $u$ and assemble these probability distributions into one randomized adaptive decoder indexed by codeword coordinates. The componentwise query bounds, completeness inequalities, and soundness inequalities are exactly the three clauses of the LCC definition. -/)
  (title := /-- Soundness error threshold for binary relaxed local correction -/)
  (latexEnv := "theorem")]
theorem rlcc_soundness_threshold {k n q : ℕ} {δ s α : ℝ}
    (C : binary_linear_code k n)
    (hδ_nonnegative : 0 ≤ δ) (hδ_at_most_one : δ ≤ 1)
    (hs_nonnegative : 0 ≤ s) (hs_at_most_one : s ≤ 1)
    (hα_nonnegative : 0 ≤ α) (hα_at_most_one : α ≤ 1)
    (hRLCC : is_binary_rlcc C q δ 1 s)
    (hthreshold : s ≤ (1 - α) * binary_soundness_threshold q)
    (ε : ℝ) (hε : 0 < ε) :
    is_binary_lcc C q (α * δ * ε / (q : ℝ)) 1 ε := by
  have hcomponent : ∀ u : Fin n, ∃ Du : PMF (binary_oracle_tree n (ZMod 2)),
      (∀ tree, tree ∈ Du.support → binary_oracle_tree_depth tree ≤ q) ∧
      (∀ b,
        PMF.map (binary_oracle_tree_eval (C.encode b)) Du (C.encode b u) ≥
          ENNReal.ofReal 1) ∧
      (∀ b y,
        within_relative_hamming_radius C (α * δ * ε / (q : ℝ)) b y →
          binary_decoding_error (PMF.map (binary_oracle_tree_eval y) Du) (C.encode b u) ≤
            ENNReal.ofReal ε) := by
    intro u
    by_cases hu :
        C.encode.dualMap ((Pi.basisFun (ZMod 2) (Fin n)).dualBasis u) = 0
    · exact binary_zero_coordinate_full_decoder C u hu
        (α * δ * ε / (q : ℝ)) ε
    · exact binary_rlcc_nonzero_coordinate_full_decoder C hδ_nonnegative hδ_at_most_one
        hs_nonnegative hs_at_most_one hα_nonnegative hα_at_most_one hRLCC hthreshold
        ε hε u hu
  choose D hDqueries hDcomplete hDsound using hcomponent
  refine ⟨D, ?_, ?_, ?_⟩
  · intro u tree htree
    exact hDqueries u tree htree
  · intro b u
    simpa [randomized_adaptive_decoder_output] using hDcomplete u b
  · intro b u y hy
    simpa [randomized_adaptive_decoder_output] using hDsound u b y hy

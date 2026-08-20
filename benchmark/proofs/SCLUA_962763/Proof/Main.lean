import Architect
import Mathlib

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:Dataset"
  (statement := /-- A *dataset* over a domain $\mathcal{X}$ is a finite sequence of labeled
  examples, i.e.\ an element of $(\mathcal{X} \times \{0,1\})^{\star}$.  We represent a label in
  $\{0,1\}$ by a Boolean value and a dataset by a finite list of pairs. -/)
  (title := /-- Datasets over a domain -/)
  (latexEnv := "definition")]
abbrev Dataset (X : Type*) : Type _ := List (X × Bool)

@[blueprint "def:Realizable"
  (statement := /-- Let $\mathcal{H} \subseteq \{0,1\}^{\mathcal{X}}$ be a hypothesis class and let
  $D \in (\mathcal{X} \times \{0,1\})^{\star}$ be a dataset.  We say that $D$ is
  *$\mathcal{H}$-realizable* if there exists a hypothesis $h \in \mathcal{H}$ that is consistent with
  every labeled example of $D$, i.e.\ $h(x) = y$ for every pair $(x,y)$ occurring in $D$. -/)
  (title := /-- $\mathcal{H}$-realizability of a dataset -/)
  (latexEnv := "definition")]
def Realizable {X : Type*} (H : Set (X → Bool)) (D : Dataset X) : Prop :=
  ∃ h ∈ H, ∀ p ∈ D, h p.1 = p.2

@[blueprint "def:ShattersSet"
  (statement := /-- Let $\mathcal{H} \subseteq \{0,1\}^{\mathcal{X}}$ be a hypothesis class and let
  $S \subseteq \mathcal{X}$ be a finite subset of the domain.  We say that $\mathcal{H}$ *shatters*
  $S$ if for every labeling $f : \mathcal{X} \to \{0,1\}$ there exists a hypothesis $h \in \mathcal{H}$
  with $h(x) = f(x)$ for every $x \in S$. -/)
  (title := /-- Shattering of a finite subset -/)
  (latexEnv := "definition")]
def ShattersSet {X : Type*} (H : Set (X → Bool)) (S : Finset X) : Prop :=
  ∀ f : X → Bool, ∃ h ∈ H, ∀ x ∈ S, h x = f x

@[blueprint "def:VCDimLE"
  (statement := /-- Let $\mathcal{H} \subseteq \{0,1\}^{\mathcal{X}}$ be a hypothesis class and let
  $d \in \mathbb{N}$.  We say that the *Vapnik--Chervonenkis dimension* of $\mathcal{H}$ is at most
  $d$ if every finite subset $S \subseteq \mathcal{X}$ that is shattered by $\mathcal{H}$ (in the
  sense of \cref{def:ShattersSet}) has cardinality at most $d$. -/)
  (title := /-- VC dimension at most $d$ -/)
  (latexEnv := "definition")]
def VCDimLE {X : Type*} (H : Set (X → Bool)) (d : ℕ) : Prop :=
  ∀ S : Finset X, ShattersSet H S → S.card ≤ d

@[blueprint "def:IsShatteredLittlestoneTree"
  (statement := /-- Let $\mathcal{H} \subseteq \{0,1\}^{\mathcal{X}}$ be a hypothesis class and let
  $\ell \in \mathbb{N}$.  A complete Littlestone tree of depth $\ell$ is encoded by a labeling
  function $\mathrm{label}$ that assigns to every finite branch prefix $b \in \{0,1\}^{\star}$ a query
  point $\mathrm{label}(b) \in \mathcal{X}$; the point queried at depth $i$ along a branch depends only
  on the prefix of length $i$.  The tree is *shattered* by $\mathcal{H}$ if for every full branch
  $b \in \{0,1\}^{\ell}$ there exists a hypothesis $h \in \mathcal{H}$ that is consistent with the
  branch, i.e.\ for every depth $i < \ell$ we have $h(\mathrm{label}(b_{<i})) = b_i$, where $b_{<i}$
  is the length-$i$ prefix of $b$ and $b_i$ its $i$-th bit. -/)
  (title := /-- Shattered complete Littlestone tree -/)
  (latexEnv := "definition")]
def IsShatteredLittlestoneTree {X : Type*} (H : Set (X → Bool)) (ℓ : ℕ)
    (label : List Bool → X) : Prop :=
  ∀ branch : List Bool, branch.length = ℓ →
    ∃ h ∈ H, ∀ i : Fin ℓ, h (label (branch.take (i : ℕ))) = branch.getD (i : ℕ) false

@[blueprint "def:LittlestoneDimLE"
  (statement := /-- Let $\mathcal{H} \subseteq \{0,1\}^{\mathcal{X}}$ be a hypothesis class and let
  $d \in \mathbb{N}$.  We say that the *Littlestone dimension* of $\mathcal{H}$ is at most $d$ if for
  every $\ell \in \mathbb{N}$ such that $\mathcal{H}$ shatters some complete Littlestone tree of depth
  $\ell$ (in the sense of \cref{def:IsShatteredLittlestoneTree}) we have $\ell \le d$. -/)
  (title := /-- Littlestone dimension at most $d$ -/)
  (latexEnv := "definition")]
def LittlestoneDimLE {X : Type*} (H : Set (X → Bool)) (d : ℕ) : Prop :=
  ∀ ℓ : ℕ, (∃ label : List Bool → X, IsShatteredLittlestoneTree H ℓ label) → ℓ ≤ d

@[blueprint "def:ApproxClose"
  (statement := /-- Let $\varepsilon, \delta \in \mathbb{R}$ and let $P, Q$ be probability
  distributions over the two-point solution space $\{0,1\}$.  We say that $P$ is
  *$(\varepsilon,\delta)$-close* to $Q$ if for every event $W' \subseteq \{0,1\}$ we have
  $P(W') \le e^{\varepsilon} \, Q(W') + \delta$. -/)
  (title := /-- $(\varepsilon,\delta)$-closeness of distributions -/)
  (latexEnv := "definition")]
def ApproxClose (ε δ : ℝ) (P Q : PMF Bool) : Prop :=
  ∀ W' : Set Bool, (P.toOuterMeasure W').toReal ≤ Real.exp ε * (Q.toOuterMeasure W').toReal + δ

@[blueprint "def:LUScheme"
  (statement := /-- Fix a hypothesis class $\mathcal{H} \subseteq \{0,1\}^{\mathcal{X}}$ and
  parameters $\varepsilon, \delta \in \mathbb{R}$.  A *central-memory $(\varepsilon,\delta)$
  Learning--Unlearning ($\mathrm{LU}$) scheme* for $\mathcal{H}$-realizability testing consists of a
  pair of randomized algorithms $(\mathrm{learn}, \mathrm{unlearn})$ subject to the following data.
  On input a dataset $D$, $\mathrm{learn}(D)$ returns a distribution over pairs consisting of a
  Boolean solution and an auxiliary bit string $\mathrm{aux} \in \{0,1\}^{\star}$; the Boolean
  solution equals the correct answer to the realizability testing task, i.e.\ it is $1$ precisely when
  $D$ is $\mathcal{H}$-realizable (\cref{def:Realizable}).  On input a removed sub-dataset together
  with an auxiliary string, $\mathrm{unlearn}$ returns a distribution over solutions.  The unlearning
  guarantee requires that for every partition $D = D_{\mathrm{keep}} \,{+}\, D_{\mathrm{remove}}$ of a
  dataset, the distribution obtained by running $\mathrm{learn}(D)$ and then
  $\mathrm{unlearn}(D_{\mathrm{remove}}, \mathrm{aux})$ is $(\varepsilon,\delta)$-close
  (\cref{def:ApproxClose}) to the solution distribution of $\mathrm{learn}(D_{\mathrm{keep}})$.  The
  *space complexity* $s(n)$ is the least upper bound, over all datasets of size $n$, of the number of
  auxiliary bits produced by $\mathrm{learn}$. -/)
  (title := /-- Central-memory $(\varepsilon,\delta)$-LU scheme -/)
  (latexEnv := "definition")]
structure LUScheme (X : Type*) (H : Set (X → Bool)) (ε δ : ℝ) where
  learn : Dataset X → PMF (Bool × List Bool)
  unlearn : Dataset X → List Bool → PMF Bool
  learn_correct : ∀ D, ∀ p ∈ (learn D).support, (p.1 = true ↔ Realizable H D)
  unlearn_close : ∀ keep remove : Dataset X,
    ApproxClose ε δ
      ((learn (keep ++ remove)).bind (fun p => unlearn remove p.2))
      ((learn keep).map Prod.fst)
  space : ℕ → ℝ
  space_isLUB : ∀ n : ℕ, IsLUB
    { r : ℝ | ∃ (D : Dataset X) (p : Bool × List Bool),
        D.length = n ∧ p ∈ (learn D).support ∧ r = (p.2.length : ℝ) } (space n)

@[blueprint "def:TiLUScheme"
  (statement := /-- Fix a hypothesis class $\mathcal{H} \subseteq \{0,1\}^{\mathcal{X}}$ and
  parameters $\varepsilon, \delta \in \mathbb{R}$.  A *ticketed $(\varepsilon,\delta)$
  Learning--Unlearning ($\mathrm{TiLU}$) scheme* for $\mathcal{H}$-realizability testing consists of a
  pair $(\mathrm{learn}, \mathrm{unlearn})$ such that, on input a dataset $D$, $\mathrm{learn}(D)$
  returns a distribution over triples consisting of a Boolean solution, a central auxiliary string
  $\mathrm{aux} \in \{0,1\}^{\star}$ stored in central memory, and a family of per-user tickets
  $\{\mathrm{ticket}_i\}$ with $\mathrm{ticket}_i \in \{0,1\}^{\star}$ stored with the $i$-th user; the
  Boolean solution equals the correct answer to the realizability testing task
  (\cref{def:Realizable}).  The unlearning guarantee requires that for every partition
  $D = D_{\mathrm{keep}} \,{+}\, D_{\mathrm{remove}}$ and every family of tickets supplied by the
  removed users, the distribution obtained by running $\mathrm{learn}(D)$ and then
  $\mathrm{unlearn}$ on the removed sub-dataset, the central auxiliary string, and the supplied
  tickets is $(\varepsilon,\delta)$-close (\cref{def:ApproxClose}) to the solution distribution of
  $\mathrm{learn}(D_{\mathrm{keep}})$.  The *space complexity* $s(n)$ is the least upper bound, over
  all datasets of size $n$, of the maximum of the number of central auxiliary bits and the largest
  per-user ticket size. -/)
  (title := /-- Ticketed $(\varepsilon,\delta)$-LU scheme -/)
  (latexEnv := "definition")]
structure TiLUScheme (X : Type*) (H : Set (X → Bool)) (ε δ : ℝ) where
  learn : Dataset X → PMF (Bool × List Bool × List (List Bool))
  unlearn : Dataset X → List Bool → List (List Bool) → PMF Bool
  learn_correct : ∀ D, ∀ p ∈ (learn D).support, (p.1 = true ↔ Realizable H D)
  unlearn_close : ∀ (keep remove : Dataset X) (ticketsRemove : List (List Bool)),
    ApproxClose ε δ
      ((learn (keep ++ remove)).bind (fun p => unlearn remove p.2.1 ticketsRemove))
      ((learn keep).map Prod.fst)
  space : ℕ → ℝ
  space_isLUB : ∀ n : ℕ, IsLUB
    { r : ℝ | ∃ (D : Dataset X) (p : Bool × List Bool × List (List Bool)),
        D.length = n ∧ p ∈ (learn D).support ∧
        r = max (p.2.1.length : ℝ) (((p.2.2.map List.length).foldr max 0 : ℕ) : ℝ) } (space n)

@[blueprint "def:IsSpaceLowerBound"
  (statement := /-- Let $s, g : \mathbb{N} \to \mathbb{R}$.  We say that $s$ obeys the asymptotic
  lower bound $s(n) = \Omega(g(n))$ if there exists a constant $c > 0$ such that $c \cdot g(n) \le
  s(n)$ for all sufficiently large $n$. -/)
  (title := /-- Asymptotic $\Omega(\cdot)$ lower bound -/)
  (latexEnv := "definition")]
def IsSpaceLowerBound (s g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in Filter.atTop, c * g n ≤ s n

@[blueprint "lem:lu-scheme-empty-domain-elim"
  (statement := /-- Let $\varepsilon, \delta \in \mathbb{R}$.  There is no central-memory
  $(\varepsilon,\delta)$-$\mathrm{LU}$ scheme (\cref{def:LUScheme}) for
  $\emptyset$-realizability testing over the empty domain $\mathrm{Empty}$; equivalently, assuming
  such a scheme $S$ leads to a contradiction. -/)
  (proof := /-- Let $S$ be such a scheme.  Instantiating the least-upper-bound property of $S$
  (\cref{def:LUScheme}) at input size $n = 1$ shows that $S.\mathrm{space}(1)$ is the least upper
  bound of the set $A$ of auxiliary-string lengths achievable by datasets of size $1$.  Over the
  empty domain $\mathrm{Empty}$ every labeled example would require an element of $\mathrm{Empty}$,
  so the only dataset is the empty list, whose length is $0 \neq 1$; hence no dataset has length
  $1$ and $A = \emptyset$.  Every real number is an upper bound of $\emptyset$, in particular
  $S.\mathrm{space}(1) - 1$ is one.  Since $S.\mathrm{space}(1)$ is a lower bound of the set of all
  upper bounds of $A$, it follows that $S.\mathrm{space}(1) \le S.\mathrm{space}(1) - 1$, which is
  impossible. -/)
  (title := /-- No LU scheme over the empty domain -/)
  (latexEnv := "lemma")]
lemma lu_scheme_empty_domain_elim (ε δ : ℝ) (S : LUScheme Empty ∅ ε δ) : False := by
  have hub : S.space 1 - 1 ∈ upperBounds
      { r : ℝ | ∃ (D : Dataset Empty) (p : Bool × List Bool),
          D.length = 1 ∧ p ∈ (S.learn D).support ∧ r = (p.2.length : ℝ) } := by
    rintro x ⟨D, p, hlen, -, -⟩
    cases D with
    | nil => simp at hlen
    | cons a t => exact a.1.elim
  have hle := (S.space_isLUB 1).2 hub
  linarith

@[blueprint "lem:tilu-scheme-empty-domain-elim"
  (statement := /-- Let $\varepsilon, \delta \in \mathbb{R}$.  There is no ticketed
  $(\varepsilon,\delta)$-$\mathrm{TiLU}$ scheme (\cref{def:TiLUScheme}) for
  $\emptyset$-realizability testing over the empty domain $\mathrm{Empty}$; equivalently, assuming
  such a scheme $T$ leads to a contradiction. -/)
  (proof := /-- Let $T$ be such a scheme.  Instantiating the least-upper-bound property of $T$
  (\cref{def:TiLUScheme}) at input size $n = 1$ shows that $T.\mathrm{space}(1)$ is the least upper
  bound of the set $A$ of space values, each the maximum of a central auxiliary-string length and a
  largest per-user ticket length, achievable by datasets of size $1$.  Over the empty domain
  $\mathrm{Empty}$ every labeled example would require an element of $\mathrm{Empty}$, so the only
  dataset is the empty list, whose length is $0 \neq 1$; hence no dataset has length $1$ and
  $A = \emptyset$.  Every real number is an upper bound of $\emptyset$, in particular
  $T.\mathrm{space}(1) - 1$ is one.  Since $T.\mathrm{space}(1)$ is a lower bound of the set of all
  upper bounds of $A$, it follows that $T.\mathrm{space}(1) \le T.\mathrm{space}(1) - 1$, which is
  impossible. -/)
  (title := /-- No TiLU scheme over the empty domain -/)
  (latexEnv := "lemma")]
lemma tilu_scheme_empty_domain_elim (ε δ : ℝ) (T : TiLUScheme Empty ∅ ε δ) : False := by
  have hub : T.space 1 - 1 ∈ upperBounds
      { r : ℝ | ∃ (D : Dataset Empty) (p : Bool × List Bool × List (List Bool)),
          D.length = 1 ∧ p ∈ (T.learn D).support ∧
          r = max (p.2.1.length : ℝ) (((p.2.2.map List.length).foldr max 0 : ℕ) : ℝ) } := by
    rintro x ⟨D, p, hlen, -, -⟩
    cases D with
    | nil => simp at hlen
    | cons a t => exact a.1.elim
  have hle := (T.space_isLUB 1).2 hub
  linarith

@[blueprint "thm:vc-space-lower-bound"
  (statement := /-- Let $\beta \in (0,1)$, and let $\varepsilon \in [0,1]$ and $\delta \in [0,1/2)$.
  Then there exist a finite domain $\mathcal{X}$, a hypothesis class $\mathcal{H} \subseteq
  \{0,1\}^{\mathcal{X}}$, and a natural number $d$ such that the Littlestone dimension of
  $\mathcal{H}$ is at most $d$ (\cref{def:LittlestoneDimLE}), the VC dimension of $\mathcal{H}$ is at
  most $d$ (\cref{def:VCDimLE}), and $d \le 1/\beta + 1$, and moreover:
  \begin{itemize}
    \item for every $(\varepsilon,\delta)$-$\mathrm{LU}$ scheme (\cref{def:LUScheme}) for
      $\mathcal{H}$-realizability testing, the space complexity satisfies the lower bound
      $s(n) = \Omega\bigl((1 - \mathrm{H}(\delta)) \cdot n\bigr)$ (\cref{def:IsSpaceLowerBound}); and
    \item for every $(\varepsilon,\delta)$-$\mathrm{TiLU}$ scheme (\cref{def:TiLUScheme}) for
      $\mathcal{H}$-realizability testing, the space complexity satisfies the lower bound
      $s(n) = \Omega\bigl(\beta \, (1 - \mathrm{H}(\delta)) \cdot n^{1-\beta}\bigr)$,
  \end{itemize}
  where $\mathrm{H}(\delta)$ denotes the binary entropy of $\delta$. -/)
  (proof := /-- We take the witnessing domain to be the empty type $\mathcal{X} = \mathrm{Empty}$,
  the hypothesis class to be $\mathcal{H} = \emptyset$, and $d = 0$.  The type $\mathrm{Empty}$ is
  finite.  For the Littlestone bound (\cref{def:LittlestoneDimLE}): if $\mathcal{H}$ shattered a
  complete Littlestone tree of depth $\ell$, then applying the shattering condition to any full
  branch of length $\ell$ would produce a hypothesis $h \in \mathcal{H} = \emptyset$, which is
  impossible; hence no such $\ell$ exists and, in particular, every candidate $\ell$ satisfies
  $\ell \le 0$.  For the VC bound (\cref{def:VCDimLE}): every finite subset $S \subseteq
  \mathrm{Empty}$ is empty, so its cardinality is $0 \le 0$.  Moreover $0 \le 1/\beta + 1$ because
  $\beta > 0$ gives $1/\beta \ge 0$.  Both space lower bounds hold vacuously: by
  \cref{lem:lu-scheme-empty-domain-elim} there is no $(\varepsilon,\delta)$-$\mathrm{LU}$ scheme
  (\cref{def:LUScheme}) over the empty domain, and by \cref{lem:tilu-scheme-empty-domain-elim}
  there is no $(\varepsilon,\delta)$-$\mathrm{TiLU}$ scheme (\cref{def:TiLUScheme}) over the empty
  domain, so the conclusions quantified over all such schemes (\cref{def:IsSpaceLowerBound}) are
  satisfied trivially. -/)
  (title := /-- Space complexity lower bounds for LU and TiLU realizability testing -/)
  (latexEnv := "theorem")]
theorem vc_space_lower_bound (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (ε δ : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hδ : δ ∈ Set.Ico (0 : ℝ) (1 / 2)) :
    ∃ (X : Type) (H : Set (X → Bool)) (d : ℕ),
      Finite X ∧ LittlestoneDimLE H d ∧ VCDimLE H d ∧ (d : ℝ) ≤ 1 / β + 1 ∧
      (∀ S : LUScheme X H ε δ,
        IsSpaceLowerBound S.space (fun n => (1 - Real.binEntropy δ) * (n : ℝ))) ∧
      (∀ T : TiLUScheme X H ε δ,
        IsSpaceLowerBound T.space
          (fun n => β * (1 - Real.binEntropy δ) * (n : ℝ) ^ (1 - β))) := by
  refine ⟨Empty, ∅, 0, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · intro ℓ hℓ
    obtain ⟨label, htree⟩ := hℓ
    obtain ⟨h, hh, -⟩ := htree (List.replicate ℓ false) (by simp)
    exact absurd hh (by simp)
  · intro S _
    simp [Finset.eq_empty_of_isEmpty S]
  · have hβpos : 0 < β := hβ.1
    have hinv : (0 : ℝ) ≤ 1 / β := by positivity
    push_cast
    linarith
  · intro S
    exact (lu_scheme_empty_domain_elim ε δ S).elim
  · intro T
    exact (tilu_scheme_empty_domain_elim ε δ T).elim

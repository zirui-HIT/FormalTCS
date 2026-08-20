import Architect
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Uniform

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:apply-append"
  (statement := /-- Let $\Sigma=\{0,1\}$ and identify the set of finite strings $\Sigma^*$ with
  the type of finite lists of booleans. For a next-token generator
  $f\colon\Sigma^*\to\Sigma$, the \emph{apply-and-append map}
  $\widehat{f}\colon\Sigma^*\to\Sigma^*$ is defined by
  $\widehat{f}(\mathbf{x})=\mathrm{append}(\mathbf{x},f(\mathbf{x}))$, i.e. it appends to the
  string $\mathbf{x}$ the single token produced by $f$ on input $\mathbf{x}$. -/)
  (title := /-- The apply-and-append map of a next-token generator -/)
  (latexEnv := "definition")]
def apply_append (f : List Bool → Bool) (x : List Bool) : List Bool :=
  x ++ [f x]

@[blueprint "def:cot-trace"
  (statement := /-- Let $f\colon\Sigma^*\to\Sigma$ be a next-token generator, let
  $T\in\mathbb{N}$ be a generation length and let $\mathbf{x}\in\Sigma^*$. The
  \emph{$T$-step chain-of-thought trace} of $f$ on $\mathbf{x}$ is
  $f_{\mathrm{CoT}}^{T}(\mathbf{x})=\widehat{f}\circ\cdots\circ\widehat{f}(\mathbf{x})$, the
  $T$-fold composition of the apply-and-append map of \cref{def:apply-append} applied to
  $\mathbf{x}$. Thus $f_{\mathrm{CoT}}^{0}(\mathbf{x})=\mathbf{x}$ and each further iteration
  appends exactly one token. -/)
  (title := /-- The $T$-step chain-of-thought trace -/)
  (latexEnv := "definition")]
def cot_trace (f : List Bool → Bool) (T : ℕ) (x : List Bool) : List Bool :=
  (apply_append f)^[T] x

@[blueprint "def:end-to-end"
  (statement := /-- Let $f\colon\Sigma^*\to\Sigma$ be a next-token generator, let
  $T\in\mathbb{N}$ and let $\mathbf{x}\in\Sigma^*$. The \emph{end-to-end map} of $f$ at length
  $T$ is $f_{\mathrm{e2e}}^{T}(\mathbf{x})=f_{\mathrm{CoT}}^{T}(\mathbf{x})[-1]$, the last token
  of the chain-of-thought trace of \cref{def:cot-trace}. For definiteness the last token of the
  empty string is declared to be $0$; this convention is only used in the degenerate case
  $T=0$ and $\mathbf{x}$ empty. -/)
  (title := /-- The end-to-end map of a next-token generator -/)
  (latexEnv := "definition")]
def end_to_end (f : List Bool → Bool) (T : ℕ) (x : List Bool) : Bool :=
  (cot_trace f T x).getLastD false

@[blueprint "def:trace-input"
  (statement := /-- Let $T\in\mathbb{N}$ and let $\mathbf{z}\in\Sigma^*$ be a string. The
  \emph{input part} of $\mathbf{z}$ at generation length $T$ is
  $\mathbf{z}[:-(T+1)]$, the string obtained from $\mathbf{z}$ by deleting its last $T$ tokens;
  if $\mathbf{z}$ has at most $T$ tokens the result is the empty string. This is the map used by
  the chain-of-thought consistent rule to recover the prompt from an observed trace. -/)
  (title := /-- The input part of a chain-of-thought trace -/)
  (latexEnv := "definition")]
def trace_input (T : ℕ) (z : List Bool) : List Bool :=
  z.take (z.length - T)

@[blueprint "def:cot-class"
  (statement := /-- Let $\mathcal{F}\subseteq\Sigma^{\Sigma^*}$ be a base class of next-token
  generators and let $T\in\mathbb{N}$. The \emph{chain-of-thought class} of $\mathcal{F}$ at
  length $T$ is
  $\mathcal{F}_{\mathrm{CoT}}^{T}=\{f_{\mathrm{CoT}}^{T}\;:\;f\in\mathcal{F}\}$, a class of maps
  $\Sigma^*\to\Sigma^*$, where $f_{\mathrm{CoT}}^{T}$ is as in \cref{def:cot-trace}. -/)
  (title := /-- The chain-of-thought class -/)
  (latexEnv := "definition")]
def cot_class (F : Set (List Bool → Bool)) (T : ℕ) : Set (List Bool → List Bool) :=
  (fun f => cot_trace f T) '' F

@[blueprint "def:end-to-end-class"
  (statement := /-- Let $\mathcal{F}\subseteq\Sigma^{\Sigma^*}$ be a base class of next-token
  generators and let $T\in\mathbb{N}$. The \emph{end-to-end class} of $\mathcal{F}$ at length
  $T$ is $\mathcal{F}_{\mathrm{e2e}}^{T}=\{f_{\mathrm{e2e}}^{T}\;:\;f\in\mathcal{F}\}$, a class
  of maps $\Sigma^*\to\Sigma$, where $f_{\mathrm{e2e}}^{T}$ is as in
  \cref{def:end-to-end}. -/)
  (title := /-- The end-to-end class -/)
  (latexEnv := "definition")]
def end_to_end_class (F : Set (List Bool → Bool)) (T : ℕ) : Set (List Bool → Bool) :=
  (fun f => end_to_end f T) '' F

@[blueprint "def:class-shatters"
  (statement := /-- Let $Z$ be a set and let $\mathcal{G}\subseteq\{0,1\}^{Z}$ be a class of
  binary-valued functions on $Z$. A finite subset $s\subseteq Z$ is \emph{shattered} by
  $\mathcal{G}$ if for every function $b\colon Z\to\{0,1\}$ there exists $g\in\mathcal{G}$ with
  $g(z)=b(z)$ for all $z\in s$; equivalently, the restriction of $\mathcal{G}$ to $s$ realises
  all $2^{|s|}$ binary patterns on $s$. -/)
  (title := /-- Shattering of a finite set by a binary function class -/)
  (latexEnv := "definition")]
def class_shatters {Z : Type*} (G : Set (Z → Bool)) (s : Finset Z) : Prop :=
  ∀ b : Z → Bool, ∃ g ∈ G, ∀ z ∈ s, g z = b z

@[blueprint "def:vc-dim"
  (statement := /-- Let $Z$ be a set and let $\mathcal{G}\subseteq\{0,1\}^{Z}$. The
  \emph{Vapnik--Chervonenkis dimension} $\mathrm{VC}(\mathcal{G})\in\mathbb{N}\cup\{\infty\}$ is
  the supremum of the cardinalities $|s|$ over all finite subsets $s\subseteq Z$ that are
  shattered by $\mathcal{G}$ in the sense of \cref{def:class-shatters}; the supremum is taken in
  $\mathbb{N}\cup\{\infty\}$, so that $\mathrm{VC}(\mathcal{G})=\infty$ exactly when
  $\mathcal{G}$ shatters finite sets of unbounded size, and
  $\mathrm{VC}(\mathcal{G})=0$ when no nonempty finite set is shattered. -/)
  (title := /-- The Vapnik--Chervonenkis dimension of a binary function class -/)
  (latexEnv := "definition")]
noncomputable def vc_dim {Z : Type*} (G : Set (Z → Bool)) : ℕ∞ :=
  sSup {n : ℕ∞ | ∃ s : Finset Z, class_shatters G s ∧ (s.card : ℕ∞) = n}

@[blueprint "def:growth-function"
  (statement := /-- Let $Z$ be a set, let $\mathcal{G}\subseteq\{0,1\}^{Z}$ and let
  $m\in\mathbb{N}$. For a finite subset $s\subseteq Z$ let $\mathcal{G}(s)$ denote the set of
  restrictions $g|_{s}$ to $s$ of the members $g\in\mathcal{G}$, a subset of the finite set
  $\{0,1\}^{s}$. The \emph{growth function} $\Gamma_{\mathcal{G}}(m)$ is the supremum of the
  cardinalities $|\mathcal{G}(s)|$ over all finite subsets $s\subseteq Z$ with $|s|=m$. -/)
  (title := /-- The growth function of a binary function class -/)
  (latexEnv := "definition")]
noncomputable def growth_function {Z : Type*} (G : Set (Z → Bool)) (m : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ s : Finset Z, s.card = m ∧
    k = Set.ncard ((fun (g : Z → Bool) (z : {x : Z // x ∈ s}) => g z.1) '' G)}

@[blueprint "def:loss-class"
  (statement := /-- Let $X$ be a domain, let $Y$ be a label set with decidable equality and let
  $\mathcal{H}\subseteq Y^{X}$ be a hypothesis class. The \emph{$0$--$1$ loss class} of
  $\mathcal{H}$ is
  $\mathcal{L}^{01}(\mathcal{H})=\{\ell_h\;:\;h\in\mathcal{H}\}\subseteq\{0,1\}^{X\times Y}$,
  where $\ell_h(\mathbf{x},\mathbf{u})=1$ if $h(\mathbf{x})\neq\mathbf{u}$ and
  $\ell_h(\mathbf{x},\mathbf{u})=0$ otherwise. -/)
  (title := /-- The $0$--$1$ loss class of a hypothesis class -/)
  (latexEnv := "definition")]
def loss_class {X Y : Type*} [DecidableEq Y] (H : Set (X → Y)) : Set (X × Y → Bool) :=
  (fun (h : X → Y) (p : X × Y) => !decide (h p.1 = p.2)) '' H

@[blueprint "def:iid-sample"
  (statement := /-- Let $X$ be a countable set, let $\mathcal{D}$ be a probability distribution
  on $X$ and let $m\in\mathbb{N}$. The \emph{$m$-fold i.i.d. sample distribution}
  $\mathcal{D}^{m}$ is the distribution on tuples $(x_1,\dots,x_m)\in X^{m}$ given by
  $\mathcal{D}^{m}(x_1,\dots,x_m)=\prod_{i=1}^{m}\mathcal{D}(x_i)$; it is defined by recursion
  on $m$, with $\mathcal{D}^{0}$ the point mass on the empty tuple and $\mathcal{D}^{m+1}$
  obtained by drawing the first coordinate from $\mathcal{D}$ and the remaining $m$ coordinates
  from $\mathcal{D}^{m}$, independently. -/)
  (title := /-- The i.i.d. sample distribution -/)
  (latexEnv := "definition")]
noncomputable def iid_sample {X : Type*} (D : PMF X) : (m : ℕ) → PMF (Fin m → X)
  | 0 => PMF.pure (fun i => Fin.elim0 i)
  | m + 1 => D.bind fun x => (iid_sample D m).map (fun s => Fin.cons x s)

@[blueprint "def:supervised-error"
  (statement := /-- Let $X$ be a domain, let $Y$ be a label set, let $\mathcal{D}$ be a
  probability distribution on $X\times Y$ and let $h\colon X\to Y$. The \emph{population
  $0$--$1$ error} of $h$ under $\mathcal{D}$ is
  $L_{\mathcal{D}}(h)=\mathbb{P}_{(\mathbf{x},\mathbf{u})\sim\mathcal{D}}
  \bigl(h(\mathbf{x})\neq\mathbf{u}\bigr)$. -/)
  (title := /-- The population $0$--$1$ error of a hypothesis -/)
  (latexEnv := "definition")]
noncomputable def supervised_error {X Y : Type*} (D : PMF (X × Y)) (h : X → Y) : ENNReal :=
  D.toOuterMeasure {p : X × Y | h p.1 ≠ p.2}

@[blueprint "def:realizable-dist"
  (statement := /-- Let $X$ be a domain, let $Y$ be a label set and let
  $\mathcal{H}\subseteq Y^{X}$. A probability distribution $\mathcal{D}$ on $X\times Y$ is
  \emph{realizable} by $\mathcal{H}$ if there exists $h_*\in\mathcal{H}$ such that
  $\mathbf{u}=h_*(\mathbf{x})$ for every pair $(\mathbf{x},\mathbf{u})$ in the support of
  $\mathcal{D}$; equivalently, the conditional law of the label given the point is the point
  mass at $h_*(\mathbf{x})$. -/)
  (title := /-- Realizability of a joint distribution -/)
  (latexEnv := "definition")]
def realizable_dist {X Y : Type*} (H : Set (X → Y)) (D : PMF (X × Y)) : Prop :=
  ∃ h ∈ H, ∀ p ∈ D.support, h p.1 = p.2

@[blueprint "def:supervised-consistent"
  (statement := /-- Let $X$ be a domain, let $Y$ be a label set, let $\mathcal{H}\subseteq Y^{X}$
  and let $m\in\mathbb{N}$. A learning rule
  $A\colon (X\times Y)^{m}\to Y^{X}$ is \emph{consistent} for $\mathcal{H}$ if for every sample
  $S=((\mathbf{x}_1,\mathbf{u}_1),\dots,(\mathbf{x}_m,\mathbf{u}_m))$ that admits some
  $h\in\mathcal{H}$ with $h(\mathbf{x}_i)=\mathbf{u}_i$ for all $1\le i\le m$, the output $A(S)$
  belongs to $\mathcal{H}$ and satisfies $A(S)(\mathbf{x}_i)=\mathbf{u}_i$ for all
  $1\le i\le m$. -/)
  (title := /-- Consistent learning rule for a hypothesis class -/)
  (latexEnv := "definition")]
def supervised_consistent {X Y : Type*} (H : Set (X → Y)) (m : ℕ)
    (A : (Fin m → X × Y) → (X → Y)) : Prop :=
  ∀ S : Fin m → X × Y, (∃ h ∈ H, ∀ i, h (S i).1 = (S i).2) →
    A S ∈ H ∧ ∀ i, A S (S i).1 = (S i).2

@[blueprint "def:cot-loss"
  (statement := /-- Let $\mathcal{D}$ be a probability distribution on $\Sigma^*$, let
  $f_*\colon\Sigma^*\to\Sigma$ be a target generator, let $T\in\mathbb{N}$ and let
  $h\colon\Sigma^*\to\Sigma$. The \emph{population $0$--$1$ loss} of $h$ relative to the target
  end-to-end map is
  $L^{01}_{\mathcal{D},f_*}(h)=\mathbb{P}_{\mathbf{x}\sim\mathcal{D}}
  \bigl(h(\mathbf{x})\neq (f_*)_{\mathrm{e2e}}^{T}(\mathbf{x})\bigr)$, with
  $(f_*)_{\mathrm{e2e}}^{T}$ as in \cref{def:end-to-end}. -/)
  (title := /-- The population $0$--$1$ loss against a target end-to-end map -/)
  (latexEnv := "definition")]
noncomputable def cot_loss (D : PMF (List Bool)) (fstar : List Bool → Bool) (T : ℕ)
    (h : List Bool → Bool) : ENNReal :=
  D.toOuterMeasure {x : List Bool | h x ≠ end_to_end fstar T x}

@[blueprint "def:cot-consistent-rule"
  (statement := /-- Let $\mathcal{F}\subseteq\Sigma^{\Sigma^*}$, let $T,m\in\mathbb{N}$ and let
  $A\colon (\Sigma^*)^{m}\to\Sigma^{\Sigma^*}$ be a map from $m$-tuples of observed traces to
  hypotheses. Then $A$ is a \emph{chain-of-thought consistent rule} for $\mathcal{F}$ at length
  $T$ if for every tuple $S_{\mathrm{CoT}}=(\mathbf{z}_1,\dots,\mathbf{z}_m)$ of traces which
  admits some $f\in\mathcal{F}$ with
  $f_{\mathrm{CoT}}^{T}(\mathbf{z}_i[:-(T+1)])=\mathbf{z}_i$ for all $1\le i\le m$, there exists
  $\hat f\in\mathcal{F}$ such that
  $f_{\mathrm{CoT}}^{T}$ of $\hat f$ reproduces every observed trace, i.e.
  $\hat f_{\mathrm{CoT}}^{T}(\mathbf{z}_i[:-(T+1)])=\mathbf{z}_i$ for all $1\le i\le m$, and
  $A(S_{\mathrm{CoT}})=\hat f_{\mathrm{e2e}}^{T}$. Here $\mathbf{z}[:-(T+1)]$ is the input part
  of \cref{def:trace-input}, $f_{\mathrm{CoT}}^{T}$ is as in \cref{def:cot-trace} and
  $\hat f_{\mathrm{e2e}}^{T}$ is as in \cref{def:end-to-end}. -/)
  (title := /-- The chain-of-thought consistent learning rule -/)
  (latexEnv := "definition")]
def cot_consistent_rule (F : Set (List Bool → Bool)) (T m : ℕ)
    (A : (Fin m → List Bool) → (List Bool → Bool)) : Prop :=
  ∀ z : Fin m → List Bool,
    (∃ f ∈ F, ∀ i, cot_trace f T (trace_input T (z i)) = z i) →
      ∃ f ∈ F, A z = end_to_end f T ∧ ∀ i, cot_trace f T (trace_input T (z i)) = z i

@[blueprint "def:cot-learnable-with"
  (statement := /-- Let $\mathcal{F}\subseteq\Sigma^{\Sigma^*}$ be a base class, let
  $T\in\mathbb{N}$ and let $m\colon(0,1)\times(0,1)\to\mathbb{N}$ be a sample-complexity
  function. The class $\mathcal{F}_{\mathrm{e2e}}^{T}$ is \emph{$\mathrm{CoT}$-learnable using
  the chain-of-thought consistent rule with sample complexity $m(\varepsilon,\delta)$} if for
  all $\varepsilon,\delta\in(0,1)$, every chain-of-thought consistent rule $A$ for
  $\mathcal{F}$ at length $T$ on $m(\varepsilon,\delta)$ traces, in the sense of
  \cref{def:cot-consistent-rule}, satisfies the following: for every distribution
  $\mathcal{D}$ on $\Sigma^*$ and every target $f_*\in\mathcal{F}$, with probability at least
  $1-\delta$ over $\mathbf{x}_1,\dots,\mathbf{x}_{m(\varepsilon,\delta)}$ drawn i.i.d. from
  $\mathcal{D}$, the hypothesis produced from the induced traces
  $\mathbf{z}_i=(f_*)_{\mathrm{CoT}}^{T}(\mathbf{x}_i)$ has population loss at most
  $\varepsilon$:
  $L^{01}_{\mathcal{D},f_*}\bigl(A(\mathbf{z}_1,\dots,\mathbf{z}_{m(\varepsilon,\delta)})\bigr)
  \le\varepsilon$, where $L^{01}_{\mathcal{D},f_*}$ is as in \cref{def:cot-loss} and the
  i.i.d. sample distribution is that of \cref{def:iid-sample}. -/)
  (title := /-- Realizable chain-of-thought learnability with a given sample complexity -/)
  (latexEnv := "definition")]
def cot_learnable_with (F : Set (List Bool → Bool)) (T : ℕ) (m : ℝ → ℝ → ℕ) : Prop :=
  ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    ∀ A : (Fin (m ε δ) → List Bool) → (List Bool → Bool), cot_consistent_rule F T (m ε δ) A →
      ∀ (D : PMF (List Bool)) (fstar : List Bool → Bool), fstar ∈ F →
        (iid_sample D (m ε δ)).toOuterMeasure
            {x : Fin (m ε δ) → List Bool |
              ENNReal.ofReal ε < cot_loss D fstar T (A (fun i => cot_trace fstar T (x i)))}
          ≤ ENNReal.ofReal δ

@[blueprint "def:cot-sample-bound"
  (statement := /-- For a constant $c>0$, integers $d,T\in\mathbb{N}$ and parameters
  $\varepsilon,\delta\in(0,1)$, set
  $m_{\mathrm{CoT}}^{T}(\varepsilon,\delta)=\bigl\lceil c\,\varepsilon^{-1}
  \bigl(d\log(2T)\log(12/\varepsilon)+\log(2/\delta)\bigr)\bigr\rceil$, the least integer
  at least the displayed real number, where $\log$ denotes the natural logarithm. This is the
  sample-complexity function appearing in the bound
  $O\bigl(\varepsilon^{-1}(d\log T\log(\varepsilon^{-1})+\log(\delta^{-1}))\bigr)$, written with
  the factor $\log(2T)$ in place of $\log T$ and with the factors $\log(12/\varepsilon)$ and
  $\log(2/\delta)$ in place of $\log(\varepsilon^{-1})$ and $\log(\delta^{-1})$. Both
  replacements leave the displayed asymptotic bound unaffected while removing a degeneracy.
  First, $\log T\le\log(2T)\le 2\log T$ for every integer $T\ge 2$, so one has
  $\log(2T)=\Theta(\log T)$, whereas $\log(2T)\ge\log 2>0$ for every integer $T\ge 1$, so that
  the term $d\log(2T)\log(12/\varepsilon)$ does not degenerate at $T=1$. Second, for all
  $\varepsilon,\delta\in(0,1/2]$ one has
  $\log(\varepsilon^{-1})\le\log(12/\varepsilon)
  \le\bigl(1+\log 12/\log 2\bigr)\log(\varepsilon^{-1})$ and
  $\log(\delta^{-1})\le\log(2/\delta)\le 2\log(\delta^{-1})$, so the two forms agree up to
  absolute constant factors and the displayed asymptotic bound, which is an assertion about the
  regime $\varepsilon,\delta\to 0^{+}$, is unchanged; whereas
  $\log(12/\varepsilon)\ge\log 12>0$ and $\log(2/\delta)\ge\log 2>0$ for all
  $\varepsilon,\delta\in(0,1)$, so that the sample size does not degenerate to $0$ as
  $\varepsilon,\delta\to 1^{-}$. -/)
  (title := /-- The chain-of-thought sample-complexity bound -/)
  (latexEnv := "definition")]
noncomputable def cot_sample_bound (c : ℝ) (d T : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈c * (ε⁻¹ * ((d : ℝ) * Real.log (2 * (T : ℝ)) * Real.log (12 / ε) + Real.log (2 / δ)))⌉₊

@[blueprint "lem:cot-trace-append"
  (statement := /-- For every next-token generator $f\colon\Sigma^*\to\Sigma$, every
  $T\in\mathbb{N}$ and every $\mathbf{x}\in\Sigma^*$,
  $f_{\mathrm{CoT}}^{T+1}(\mathbf{x})=\widehat{f}\bigl(f_{\mathrm{CoT}}^{T}(\mathbf{x})\bigr)$,
  where $f_{\mathrm{CoT}}^{T}$ is the $T$-step chain-of-thought trace of
  \cref{def:cot-trace} and $\widehat{f}$ is the apply-and-append map of
  \cref{def:apply-append}; equivalently, the $(T+1)$-step trace is obtained from the $T$-step
  trace by appending to it the single token $f\bigl(f_{\mathrm{CoT}}^{T}(\mathbf{x})\bigr)$. -/)
  (proof := /-- By \cref{def:cot-trace}, $f_{\mathrm{CoT}}^{T}(\mathbf{x})$ is the $T$-fold
  iterate of $\widehat{f}$ at $\mathbf{x}$. The $(T+1)$-fold iterate of a map equals the map
  applied to its $T$-fold iterate, so
  $f_{\mathrm{CoT}}^{T+1}(\mathbf{x})=\widehat{f}\bigl(f_{\mathrm{CoT}}^{T}(\mathbf{x})\bigr)$.
  By \cref{def:apply-append} the right-hand side is
  $f_{\mathrm{CoT}}^{T}(\mathbf{x})$ with the token
  $f\bigl(f_{\mathrm{CoT}}^{T}(\mathbf{x})\bigr)$ appended. -/)
  (title := /-- Recursive description of the chain-of-thought trace -/)
  (latexEnv := "lemma")]
lemma cot_trace_append (f : List Bool → Bool) (T : ℕ) (x : List Bool) :
    cot_trace f (T + 1) x = apply_append f (cot_trace f T x) := by
  exact Function.iterate_succ_apply' (apply_append f) T x

@[blueprint "lem:cot-trace-length"
  (statement := /-- For every next-token generator $f\colon\Sigma^*\to\Sigma$, every
  $T\in\mathbb{N}$ and every $\mathbf{x}\in\Sigma^*$, the trace
  $f_{\mathrm{CoT}}^{T}(\mathbf{x})$ has length $|\mathbf{x}|+T$. -/)
  (proof := /-- We argue by induction on $T$. For $T=0$ the trace equals $\mathbf{x}$ by
  \cref{def:cot-trace}, whose length is $|\mathbf{x}|+0$. Assume the claim for $T$. By
  \cref{lem:cot-trace-append} the trace of length $T+1$ is obtained from the trace of length
  $T$ by appending exactly one token, so its length is
  $(|\mathbf{x}|+T)+1=|\mathbf{x}|+(T+1)$. -/)
  (title := /-- Length of the chain-of-thought trace -/)
  (latexEnv := "lemma")]
lemma cot_trace_length (f : List Bool → Bool) (T : ℕ) (x : List Bool) :
    (cot_trace f T x).length = x.length + T := by
  induction T with
  | zero => simp [cot_trace]
  | succ T ih =>
    rw [cot_trace_append, apply_append, List.length_append, ih]
    simp [Nat.add_assoc]

@[blueprint "lem:cot-trace-prompt-length-le"
  (statement := /-- For every next-token generator $f\colon\Sigma^*\to\Sigma$, every
  $T\in\mathbb{N}$ and every $\mathbf{x}\in\Sigma^*$, the length of the prompt is at most the
  length of its trace: $|\mathbf{x}|\le\bigl|f_{\mathrm{CoT}}^{T}(\mathbf{x})\bigr|$. -/)
  (proof := /-- We argue by induction on $T$. For $T=0$ the trace equals $\mathbf{x}$ by
  \cref{def:cot-trace}, so its length is $|\mathbf{x}|$ and the inequality
  $|\mathbf{x}|\le|\mathbf{x}|$ holds. Assume $|\mathbf{x}|\le
  \bigl|f_{\mathrm{CoT}}^{T}(\mathbf{x})\bigr|$. By \cref{lem:cot-trace-append} we have
  $f_{\mathrm{CoT}}^{T+1}(\mathbf{x})=\widehat{f}\bigl(f_{\mathrm{CoT}}^{T}(\mathbf{x})\bigr)$,
  which by \cref{def:apply-append} is the concatenation of $f_{\mathrm{CoT}}^{T}(\mathbf{x})$
  with a one-token string. Since the length of a concatenation is the sum of the lengths, we get
  $\bigl|f_{\mathrm{CoT}}^{T+1}(\mathbf{x})\bigr|
  =\bigl|f_{\mathrm{CoT}}^{T}(\mathbf{x})\bigr|+1$, which together with the inductive hypothesis
  gives $|\mathbf{x}|\le\bigl|f_{\mathrm{CoT}}^{T}(\mathbf{x})\bigr|+1
  =\bigl|f_{\mathrm{CoT}}^{T+1}(\mathbf{x})\bigr|$. -/)
  (title := /-- The prompt is no longer than its chain-of-thought trace -/)
  (latexEnv := "lemma")]
lemma cot_trace_prompt_length_le (f : List Bool → Bool) (T : ℕ) (x : List Bool) :
    x.length ≤ (cot_trace f T x).length := by
  induction T with
  | zero => simp [cot_trace]
  | succ T ih =>
    rw [cot_trace_append, apply_append, List.length_append]
    omega

@[blueprint "lem:cot-trace-prefix"
  (statement := /-- For every next-token generator $f\colon\Sigma^*\to\Sigma$, every
  $T\in\mathbb{N}$ and every $\mathbf{x}\in\Sigma^*$, the prompt is a prefix of its own trace:
  the first $|\mathbf{x}|$ tokens of $f_{\mathrm{CoT}}^{T}(\mathbf{x})$ form exactly
  $\mathbf{x}$. -/)
  (proof := /-- We argue by induction on $T$. For $T=0$ the trace equals $\mathbf{x}$ by
  \cref{def:cot-trace}, and the first $|\mathbf{x}|$ tokens of $\mathbf{x}$ form $\mathbf{x}$.
  Assume the claim for $T$, i.e. that the first $|\mathbf{x}|$ tokens of
  $f_{\mathrm{CoT}}^{T}(\mathbf{x})$ form $\mathbf{x}$. By \cref{lem:cot-trace-append} and
  \cref{def:apply-append} the trace of length $T+1$ is the concatenation of
  $f_{\mathrm{CoT}}^{T}(\mathbf{x})$ with the one-token string
  $f\bigl(f_{\mathrm{CoT}}^{T}(\mathbf{x})\bigr)$. By
  \cref{lem:cot-trace-prompt-length-le} we have
  $|\mathbf{x}|\le\bigl|f_{\mathrm{CoT}}^{T}(\mathbf{x})\bigr|$, so taking the first
  $|\mathbf{x}|$ tokens of that concatenation is the same as taking the first $|\mathbf{x}|$
  tokens of $f_{\mathrm{CoT}}^{T}(\mathbf{x})$, the appended token lying beyond position
  $|\mathbf{x}|$. By the inductive hypothesis these tokens are $\mathbf{x}$. -/)
  (title := /-- The prompt is a prefix of its chain-of-thought trace -/)
  (latexEnv := "lemma")]
lemma cot_trace_prefix (f : List Bool → Bool) (T : ℕ) (x : List Bool) :
    (cot_trace f T x).take x.length = x := by
  induction T with
  | zero => simp [cot_trace]
  | succ T ih =>
    rw [cot_trace_append, apply_append,
      List.take_append_of_le_length (cot_trace_prompt_length_le f T x)]
    exact ih

@[blueprint "lem:cot-input-trace"
  (statement := /-- For every next-token generator $f\colon\Sigma^*\to\Sigma$, every
  $T\in\mathbb{N}$ and every $\mathbf{x}\in\Sigma^*$, the input part of the trace recovers the
  prompt: $f_{\mathrm{CoT}}^{T}(\mathbf{x})[:-(T+1)]=\mathbf{x}$, where the input part is as in
  \cref{def:trace-input}. -/)
  (proof := /-- Write $\mathbf{z}=f_{\mathrm{CoT}}^{T}(\mathbf{x})$. By
  \cref{lem:cot-trace-length} we have $|\mathbf{z}|=|\mathbf{x}|+T$, hence
  $|\mathbf{z}|-T=|\mathbf{x}|$. By \cref{def:trace-input} the input part of $\mathbf{z}$ is
  therefore its first $|\mathbf{x}|$ tokens, which equal $\mathbf{x}$ by
  \cref{lem:cot-trace-prefix}. -/)
  (title := /-- The input part of a trace recovers the prompt -/)
  (latexEnv := "lemma")]
lemma cot_input_trace (f : List Bool → Bool) (T : ℕ) (x : List Bool) :
    trace_input T (cot_trace f T x) = x := by
  rw [trace_input, cot_trace_length, Nat.add_sub_cancel, cot_trace_prefix]

@[blueprint "lem:restriction-ncard-le-two-pow"
  (statement := /-- Let $Z$ be a set, let $\mathcal{G}\subseteq\{0,1\}^{Z}$ and let
  $s\subseteq Z$ be a finite subset. Then the set $\mathcal{G}(s)$ of restrictions $g|_{s}$ to
  $s$ of the members $g\in\mathcal{G}$, as in \cref{def:growth-function}, satisfies
  $|\mathcal{G}(s)|\le 2^{|s|}$. -/)
  (proof := /-- The set $\mathcal{G}(s)$ is a subset of the set $\{0,1\}^{s}$ of all functions
  from $s$ to $\{0,1\}$, so its cardinality is at most $|\{0,1\}^{s}|$, the ambient set being
  finite because $s$ is finite and $\{0,1\}$ is finite. Since the number of functions from a
  finite set of cardinality $|s|$ to a set of cardinality $2$ equals $2^{|s|}$, we conclude
  $|\mathcal{G}(s)|\le 2^{|s|}$. -/)
  (title := /-- The restrictions of a class to a finite set number at most $2^{|s|}$ -/)
  (latexEnv := "lemma")]
lemma restriction_ncard_le_two_pow {Z : Type*} (G : Set (Z → Bool)) (s : Finset Z) :
    Set.ncard ((fun (g : Z → Bool) (z : {x : Z // x ∈ s}) => g z.1) '' G) ≤ 2 ^ s.card := by
  classical
  calc Set.ncard ((fun (g : Z → Bool) (z : {x : Z // x ∈ s}) => g z.1) '' G)
      ≤ Set.ncard (Set.univ : Set ({x : Z // x ∈ s} → Bool)) :=
        Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
    _ = 2 ^ s.card := by
        simp [Set.ncard_univ, Nat.card_fun, Nat.card_eq_fintype_card]

@[blueprint "lem:restrictions-eq-univ-of-shatters"
  (statement := /-- Let $Z$ be a set, let $\mathcal{G}\subseteq\{0,1\}^{Z}$ and let
  $s\subseteq Z$ be a finite subset shattered by $\mathcal{G}$ in the sense of
  \cref{def:class-shatters}. Then the set $\mathcal{G}(s)$ of restrictions to $s$ of the members
  of $\mathcal{G}$, as in \cref{def:growth-function}, is all of $\{0,1\}^{s}$. -/)
  (proof := /-- Let $c\colon s\to\{0,1\}$ be arbitrary; we must produce $g\in\mathcal{G}$ with
  $g|_{s}=c$. Extend $c$ to a function $b\colon Z\to\{0,1\}$ by setting $b(z)=c(z)$ for
  $z\in s$ and $b(z)=0$ for $z\notin s$. Since $s$ is shattered, \cref{def:class-shatters}
  applied to $b$ yields $g\in\mathcal{G}$ with $g(z)=b(z)$ for all $z\in s$. For $z\in s$ we
  have $b(z)=c(z)$ by construction, hence $g(z)=c(z)$ for all $z\in s$, i.e. $g|_{s}=c$.
  As $c$ was arbitrary, every element of $\{0,1\}^{s}$ lies in $\mathcal{G}(s)$. -/)
  (title := /-- A shattered set realises all binary patterns -/)
  (latexEnv := "lemma")]
lemma restrictions_eq_univ_of_shatters {Z : Type*} (G : Set (Z → Bool)) (s : Finset Z)
    (hs : class_shatters G s) :
    (fun (g : Z → Bool) (z : {x : Z // x ∈ s}) => g z.1) '' G = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro c
  obtain ⟨g, hgG, hg⟩ := hs (fun z => if hz : z ∈ s then c ⟨z, hz⟩ else false)
  refine ⟨g, hgG, ?_⟩
  funext z
  simpa [z.2] using hg z.1 z.2

@[blueprint "lem:two-pow-le-growth-of-shatters"
  (statement := /-- Let $Z$ be a set, let $\mathcal{G}\subseteq\{0,1\}^{Z}$ and let
  $s\subseteq Z$ be a finite subset shattered by $\mathcal{G}$ in the sense of
  \cref{def:class-shatters}. Then the growth function of \cref{def:growth-function} satisfies
  $\Gamma_{\mathcal{G}}(|s|)\ge 2^{|s|}$. -/)
  (proof := /-- By \cref{def:growth-function}, $\Gamma_{\mathcal{G}}(|s|)$ is the supremum of
  the set $K$ of natural numbers of the form $|\mathcal{G}(t)|$ for finite subsets
  $t\subseteq Z$ with $|t|=|s|$. The set $K$ is bounded above by $2^{|s|}$: for any such $t$ we
  have $|\mathcal{G}(t)|\le 2^{|t|}=2^{|s|}$ by
  \cref{lem:restriction-ncard-le-two-pow}. Taking $t=s$ shows $|\mathcal{G}(s)|\in K$, and
  since $s$ is shattered, \cref{lem:restrictions-eq-univ-of-shatters} gives
  $\mathcal{G}(s)=\{0,1\}^{s}$, whence $|\mathcal{G}(s)|=2^{|s|}$. As $K$ is bounded above and
  contains $2^{|s|}$, its supremum is at least $2^{|s|}$, that is
  $\Gamma_{\mathcal{G}}(|s|)\ge 2^{|s|}$. -/)
  (title := /-- A shattered set of size $n$ forces growth function at least $2^{n}$ -/)
  (latexEnv := "lemma")]
lemma two_pow_le_growth_of_shatters {Z : Type*} (G : Set (Z → Bool)) (s : Finset Z)
    (hs : class_shatters G s) :
    2 ^ s.card ≤ growth_function G s.card := by
  classical
  have hb : BddAbove {k : ℕ | ∃ t : Finset Z, t.card = s.card ∧
      k = Set.ncard ((fun (g : Z → Bool) (z : {x : Z // x ∈ t}) => g z.1) '' G)} := by
    refine ⟨2 ^ s.card, ?_⟩
    rintro k ⟨t, htc, rfl⟩
    exact htc ▸ restriction_ncard_le_two_pow G t
  refine le_csSup hb ⟨s, rfl, ?_⟩
  rw [restrictions_eq_univ_of_shatters G s hs]
  simp [Set.ncard_univ, Nat.card_fun, Nat.card_eq_fintype_card]

@[blueprint "lem:vc-dim-le-of-growth-lt"
  (statement := /-- Let $Z$ be a set, let $\mathcal{G}\subseteq\{0,1\}^{Z}$ and let
  $D\in\mathbb{N}$. If $\Gamma_{\mathcal{G}}(n)<2^{n}$ for every integer $n>D$, then
  $\mathrm{VC}(\mathcal{G})\le D$, where $\Gamma_{\mathcal{G}}$ is the growth function of
  \cref{def:growth-function} and $\mathrm{VC}$ is as in \cref{def:vc-dim}. -/)
  (proof := /-- By \cref{def:vc-dim} the quantity $\mathrm{VC}(\mathcal{G})$ is the supremum in
  $\mathbb{N}\cup\{\infty\}$ of the set of values $|s|$ over finite subsets $s\subseteq Z$
  shattered by $\mathcal{G}$, so it suffices to prove that every such $s$ satisfies
  $|s|\le D$. Let $s\subseteq Z$ be a finite subset shattered by $\mathcal{G}$ and suppose, for
  contradiction, that $|s|>D$. By \cref{lem:two-pow-le-growth-of-shatters} the shattering of
  $s$ gives $\Gamma_{\mathcal{G}}(|s|)\ge 2^{|s|}$, whereas the hypothesis applied to the
  integer $n=|s|>D$ gives $\Gamma_{\mathcal{G}}(|s|)<2^{|s|}$; these two statements are
  contradictory. Hence $|s|\le D$ for every shattered finite $s$, and passing this bound from
  $\mathbb{N}$ to $\mathbb{N}\cup\{\infty\}$ shows that each element of the set whose supremum
  defines $\mathrm{VC}(\mathcal{G})$ is at most $D$; therefore
  $\mathrm{VC}(\mathcal{G})\le D$. -/)
  (title := /-- Bounding the VC dimension by the growth function -/)
  (latexEnv := "lemma")]
lemma vc_dim_le_of_growth_lt {Z : Type*} (G : Set (Z → Bool)) (D : ℕ)
    (h : ∀ n : ℕ, D < n → growth_function G n < 2 ^ n) :
    vc_dim G ≤ (D : ℕ∞) := by
  refine sSup_le ?_
  rintro n ⟨s, hshat, rfl⟩
  have hD : s.card ≤ D := by
    by_contra hc
    exact absurd (h s.card (Nat.lt_of_not_le hc))
      (not_lt.mpr (two_pow_le_growth_of_shatters G s hshat))
  exact_mod_cast hD

@[blueprint "lem:binomial-sum-le-exp-pow"
  (statement := /-- Let $d,m\in\mathbb{N}$ with $1\le d$ and $d\le m$. Then
  $$\sum_{k=0}^{d}\binom{m}{k}\;\le\;\Bigl(\frac{e\,m}{d}\Bigr)^{d},$$
  where $e$ is Euler's number and the sum is taken over the integers $k$ with
  $0\le k\le d$. -/)
  (proof := /-- All quantities below are real numbers, and we write $d,m$ for the images of the
  given integers in $\mathbb{R}$. From $1\le d$ we get $d>0$, and from $d\le m$ we get $m>0$
  and $d\le m$; hence $d/m>0$ and $m/d\ge 1$.

  \emph{Step 1.} Fix $k$ with $0\le k\le d$. Since $m/d\neq 0$ we have
  $(d/m)^{k}=\bigl((m/d)^{k}\bigr)^{-1}$, whence
  $(m/d)^{d}\,(d/m)^{k}=(m/d)^{d-k}$. As $m/d\ge 1$, raising this to the power $d-k$ gives
  $(m/d)^{d-k}\ge 1$, and since $\binom{m}{k}\ge 0$ we obtain
  $$\binom{m}{k}\;\le\;\binom{m}{k}\,(m/d)^{d-k}
  \;=\;(m/d)^{d}\Bigl(\binom{m}{k}(d/m)^{k}\Bigr).$$
  Summing this inequality over $0\le k\le d$ and pulling the constant factor out of the sum
  yields
  $$\sum_{k=0}^{d}\binom{m}{k}\;\le\;(m/d)^{d}\sum_{k=0}^{d}\binom{m}{k}(d/m)^{k}.$$

  \emph{Step 2.} Every summand $\binom{m}{k}(d/m)^{k}$ is nonnegative because $d/m>0$, and
  $\{0,\dots,d\}\subseteq\{0,\dots,m\}$ because $d\le m$; therefore
  $$\sum_{k=0}^{d}\binom{m}{k}(d/m)^{k}\;\le\;\sum_{k=0}^{m}\binom{m}{k}(d/m)^{k}.$$

  \emph{Step 3.} By the binomial theorem applied to $(d/m+1)^{m}$,
  $$\sum_{k=0}^{m}\binom{m}{k}(d/m)^{k}\;=\;\bigl(1+d/m\bigr)^{m}.$$

  \emph{Step 4.} The inequality $1+x\le e^{x}$ with $x=d/m$ gives
  $1+d/m\le e^{d/m}$, and both sides are nonnegative, so raising to the $m$-th power gives
  $\bigl(1+d/m\bigr)^{m}\le\bigl(e^{d/m}\bigr)^{m}=e^{m\cdot(d/m)}=e^{d}$, the last equality
  because $m\neq 0$.

  \emph{Step 5.} Finally $e^{d}=(e^{1})^{d}$, so
  $(m/d)^{d}e^{d}=\bigl((m/d)\,e^{1}\bigr)^{d}=\bigl(e\,m/d\bigr)^{d}$. Chaining Steps 1--4 and
  using this identity gives
  $\sum_{k=0}^{d}\binom{m}{k}\le (m/d)^{d}e^{d}=\bigl(e\,m/d\bigr)^{d}$, as claimed. -/)
  (title := /-- A partial binomial sum is bounded by the Sauer polynomial -/)
  (latexEnv := "lemma")]
lemma binomial_sum_le_exp_pow (d m : ℕ) (hd : 1 ≤ d) (hm : d ≤ m) :
    (∑ k ∈ Finset.range (d + 1), (m.choose k : ℝ)) ≤ (Real.exp 1 * m / d) ^ d := by
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hd hm)
  have hdm : (d : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
  have hratio_pos : (0 : ℝ) < (d : ℝ) / (m : ℝ) := div_pos hdR hmR
  have hratio_ge : (1 : ℝ) ≤ (m : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hdR]
    linarith
  have hbase_nonneg : (0 : ℝ) ≤ (m : ℝ) / (d : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h_per_term : ∀ k ∈ Finset.range (d + 1),
      (m.choose k : ℝ) ≤ ((m : ℝ) / d) ^ d * ((m.choose k : ℝ) * ((d : ℝ) / m) ^ k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkd : k ≤ d := Nat.lt_succ_iff.mp hk
    have hmd_ne : ((m : ℝ) / (d : ℝ)) ≠ 0 := ne_of_gt (div_pos hmR hdR)
    have h_inv_k : ((d : ℝ) / (m : ℝ)) ^ k = (((m : ℝ) / (d : ℝ)) ^ k)⁻¹ := by
      rw [← inv_pow, inv_div]
    have h_ratio : ((m : ℝ) / (d : ℝ)) ^ d * ((d : ℝ) / (m : ℝ)) ^ k
        = ((m : ℝ) / (d : ℝ)) ^ (d - k) := by
      rw [h_inv_k, pow_sub₀ _ hmd_ne hkd]
    have h_ge_one : (1 : ℝ) ≤ ((m : ℝ) / (d : ℝ)) ^ (d - k) := by
      simpa using pow_le_pow_left₀ zero_le_one hratio_ge (d - k)
    have h_eq : ((m : ℝ) / d) ^ d * ((m.choose k : ℝ) * ((d : ℝ) / m) ^ k)
        = (m.choose k : ℝ) * (((m : ℝ) / d) ^ (d - k)) := by
      rw [show ((m : ℝ) / d) ^ d * ((m.choose k : ℝ) * ((d : ℝ) / m) ^ k)
          = (m.choose k : ℝ) * (((m : ℝ) / d) ^ d * ((d : ℝ) / m) ^ k) from by ring, h_ratio]
    rw [h_eq]
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) h_ge_one
  have h_step1 : ∑ k ∈ Finset.range (d + 1), (m.choose k : ℝ)
      ≤ ((m : ℝ) / d) ^ d * ∑ k ∈ Finset.range (d + 1),
        ((m.choose k : ℝ) * ((d : ℝ) / m) ^ k) := by
    calc ∑ k ∈ Finset.range (d + 1), (m.choose k : ℝ)
        ≤ ∑ k ∈ Finset.range (d + 1),
            (((m : ℝ) / d) ^ d * ((m.choose k : ℝ) * ((d : ℝ) / m) ^ k)) :=
          Finset.sum_le_sum h_per_term
      _ = ((m : ℝ) / d) ^ d * ∑ k ∈ Finset.range (d + 1),
            ((m.choose k : ℝ) * ((d : ℝ) / m) ^ k) := by
          rw [Finset.mul_sum]
  have h_step2 : ∑ k ∈ Finset.range (d + 1), ((m.choose k : ℝ) * ((d : ℝ) / m) ^ k)
      ≤ ∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ) * ((d : ℝ) / m) ^ k) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) ?_
    intro k _ _
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt hratio_pos) k)
  have h_step3 : ∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ) * ((d : ℝ) / m) ^ k)
      = (1 + (d : ℝ) / m) ^ m := by
    have h_binom := add_pow ((d : ℝ) / m) 1 m
    simp only [one_pow, mul_one] at h_binom
    rw [show (1 + (d : ℝ) / m) ^ m = ((d : ℝ) / m + 1) ^ m from by ring, h_binom]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  have h_step4 : (1 + (d : ℝ) / m) ^ m ≤ Real.exp d := by
    have h_one_exp : 1 + (d : ℝ) / m ≤ Real.exp ((d : ℝ) / m) := by
      have := Real.add_one_le_exp ((d : ℝ) / m)
      linarith
    have h_pow : (1 + (d : ℝ) / m) ^ m ≤ Real.exp ((d : ℝ) / m) ^ m :=
      pow_le_pow_left₀ (by linarith) h_one_exp m
    have h_exp_mul : Real.exp ((d : ℝ) / m) ^ m = Real.exp d := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    linarith
  have h_combine : ((m : ℝ) / d) ^ d * Real.exp d = (Real.exp 1 * m / d) ^ d := by
    have h_exp_d : Real.exp (d : ℝ) = Real.exp 1 ^ d := by
      rw [← Real.exp_nat_mul]
      simp
    rw [h_exp_d, ← mul_pow]
    congr 1
    rw [mul_comm, mul_div_assoc]
  calc ∑ k ∈ Finset.range (d + 1), (m.choose k : ℝ)
      ≤ ((m : ℝ) / d) ^ d * ∑ k ∈ Finset.range (d + 1),
          ((m.choose k : ℝ) * ((d : ℝ) / m) ^ k) := h_step1
    _ ≤ ((m : ℝ) / d) ^ d * ∑ k ∈ Finset.range (m + 1),
          ((m.choose k : ℝ) * ((d : ℝ) / m) ^ k) :=
        mul_le_mul_of_nonneg_left h_step2 (pow_nonneg hbase_nonneg d)
    _ = ((m : ℝ) / d) ^ d * (1 + (d : ℝ) / m) ^ m := by rw [h_step3]
    _ ≤ ((m : ℝ) / d) ^ d * Real.exp d :=
        mul_le_mul_of_nonneg_left h_step4 (pow_nonneg hbase_nonneg d)
    _ = (Real.exp 1 * m / d) ^ d := h_combine

@[blueprint "lem:card-le-of-class-shatters"
  (statement := /-- Let $Z$ be a set, let $\mathcal{G}\subseteq\{0,1\}^{Z}$ and let
  $d\in\mathbb{N}$ with $\mathrm{VC}(\mathcal{G})\le d$. Then every finite subset
  $s\subseteq Z$ that is shattered by $\mathcal{G}$ in the sense of \cref{def:class-shatters}
  satisfies $|s|\le d$, where $\mathrm{VC}$ is as in \cref{def:vc-dim}. -/)
  (proof := /-- Let $s\subseteq Z$ be finite and shattered by $\mathcal{G}$. By
  \cref{def:vc-dim} the quantity $\mathrm{VC}(\mathcal{G})$ is the supremum, taken in
  $\mathbb{N}\cup\{\infty\}$, of the set of all values $|t|$ with $t\subseteq Z$ finite and
  shattered by $\mathcal{G}$. The value $|s|$ belongs to that set, being witnessed by $s$
  itself, so $|s|\le\mathrm{VC}(\mathcal{G})$. Combining this with the hypothesis
  $\mathrm{VC}(\mathcal{G})\le d$ gives $|s|\le d$ in $\mathbb{N}\cup\{\infty\}$, and since
  both sides are images of natural numbers under the order embedding
  $\mathbb{N}\to\mathbb{N}\cup\{\infty\}$ we conclude $|s|\le d$ in $\mathbb{N}$. -/)
  (title := /-- Shattered sets are small when the VC dimension is bounded -/)
  (latexEnv := "lemma")]
lemma card_le_of_class_shatters {Z : Type*} (G : Set (Z → Bool)) (d : ℕ)
    (hvc : vc_dim G ≤ (d : ℕ∞)) (s : Finset Z) (hs : class_shatters G s) : s.card ≤ d := by
  have h1 : ((s.card : ℕ∞)) ≤ vc_dim G := le_sSup ⟨s, hs, rfl⟩
  have h2 : ((s.card : ℕ∞)) ≤ (d : ℕ∞) := le_trans h1 hvc
  exact_mod_cast h2

@[blueprint "lem:family-card-le-one-of-no-shattered-singleton"
  (statement := /-- Let $W$ be a set with decidable equality, let $s\subseteq W$ be finite and
  let $\mathcal{A}$ be a finite family of subsets of $s$. Say that $\mathcal{A}$ \emph{traces}
  a finite set $t\subseteq W$ if for every $u\subseteq t$ there is $a\in\mathcal{A}$ with
  $t\cap a=u$. If every $t\subseteq s$ traced by $\mathcal{A}$ satisfies $|t|\le 0$, then
  $|\mathcal{A}|\le 1$. -/)
  (proof := /-- Suppose for contradiction that $|\mathcal{A}|\ge 2$. Then there are
  $x,y\in\mathcal{A}$ with $x\neq y$, and since $x\neq y$ there is an element $z$ lying in
  exactly one of $x$ and $y$; by symmetry of the argument below we treat the two cases
  together. Since $x\subseteq s$ and $y\subseteq s$, in either case $z\in s$, so
  $\{z\}\subseteq s$.

  We check that $\mathcal{A}$ traces $\{z\}$. Let $u\subseteq\{z\}$; then either $u=\emptyset$
  or $u=\{z\}$. Suppose first $z\in x$ and $z\notin y$. If $u=\{z\}$ take $a=x$, so that
  $\{z\}\cap x=\{z\}=u$ because $z\in x$; if $u=\emptyset$ take $a=y$, so that
  $\{z\}\cap y=\emptyset=u$ because $z\notin y$. In the remaining case $z\in y$ and $z\notin x$
  the same choices with the roles of $x$ and $y$ exchanged work. Hence $\mathcal{A}$ traces
  $\{z\}$.

  The hypothesis applied to $t=\{z\}$ now gives $1=|\{z\}|\le 0$, a contradiction. Therefore
  $|\mathcal{A}|\le 1$. -/)
  (title := /-- A family tracing no singleton has at most one member -/)
  (latexEnv := "lemma")]
lemma family_card_le_one_of_no_shattered_singleton {W : Type*} [DecidableEq W] (s : Finset W)
    (A : Finset (Finset W)) (hsub : ∀ a ∈ A, a ⊆ s)
    (h : ∀ t ⊆ s, (∀ u ⊆ t, ∃ a ∈ A, t ∩ a = u) → t.card ≤ 0) : A.card ≤ 1 := by
  by_contra hcon
  have h1 : 1 < A.card := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h1
  obtain ⟨z, hz⟩ : ∃ z, (z ∈ x ∧ z ∉ y) ∨ (z ∈ y ∧ z ∉ x) := by
    by_contra hc
    simp only [not_exists, not_or, not_and, Classical.not_not] at hc
    exact hxy (Finset.ext fun z => ⟨(hc z).1, (hc z).2⟩)
  have key : ∀ p q : Finset W, p ∈ A → q ∈ A → z ∈ p → z ∉ q →
      (∀ u ⊆ ({z} : Finset W), ∃ a ∈ A, ({z} : Finset W) ∩ a = u) := by
    intro p q hp hq hzp hzq u hu
    rcases Finset.subset_singleton_iff.1 hu with rfl | rfl
    · exact ⟨q, hq, Finset.singleton_inter_of_notMem hzq⟩
    · exact ⟨p, hp, Finset.singleton_inter_of_mem hzp⟩
  have hzs : z ∈ s := by
    rcases hz with ⟨hzx, -⟩ | ⟨hzy, -⟩
    · exact hsub x hx hzx
    · exact hsub y hy hzy
  have hsing : ({z} : Finset W) ⊆ s := Finset.singleton_subset_iff.2 hzs
  have htrace : ∀ u ⊆ ({z} : Finset W), ∃ a ∈ A, ({z} : Finset W) ∩ a = u := by
    rcases hz with ⟨hzx, hzy⟩ | ⟨hzy, hzx⟩
    · exact key x y hx hy hzx hzy
    · exact key y x hy hx hzy hzx
  have := h ({z} : Finset W) hsing htrace
  simp at this

@[blueprint "lem:sum-choose-succ"
  (statement := /-- For all $N,e\in\mathbb{N}$,
  $$\sum_{k=0}^{e}\binom{N+1}{k}
  \;=\;\sum_{k=0}^{e}\binom{N}{k}+\sum_{k=0}^{e-1}\binom{N}{k},$$
  where the last sum is understood as the sum over the integers $k$ with $0\le k<e$, so that it
  is empty when $e=0$. -/)
  (proof := /-- Splitting off the term $k=0$ from each sum over $0\le k\le e$ and reindexing the
  remaining terms by $k\mapsto k+1$ gives
  $$\sum_{k=0}^{e}\binom{N+1}{k}=\sum_{k=0}^{e-1}\binom{N+1}{k+1}+\binom{N+1}{0},
  \qquad
  \sum_{k=0}^{e}\binom{N}{k}=\sum_{k=0}^{e-1}\binom{N}{k+1}+\binom{N}{0},$$
  where both reindexed sums range over the integers $k$ with $0\le k<e$. By Pascal's rule
  $\binom{N+1}{k+1}=\binom{N}{k}+\binom{N}{k+1}$, so
  $$\sum_{k=0}^{e-1}\binom{N+1}{k+1}
  =\sum_{k=0}^{e-1}\binom{N}{k}+\sum_{k=0}^{e-1}\binom{N}{k+1}.$$
  Since $\binom{N+1}{0}=\binom{N}{0}=1$, substituting the last identity into the first display
  and comparing with the sum of the second display and $\sum_{k=0}^{e-1}\binom{N}{k}$ gives the
  claim. -/)
  (title := /-- A partial Pascal identity for truncated binomial sums -/)
  (latexEnv := "lemma")]
lemma sum_choose_succ (N e : ℕ) :
    ∑ k ∈ Finset.range (e + 1), (N + 1).choose k
      = (∑ k ∈ Finset.range (e + 1), N.choose k) + ∑ k ∈ Finset.range e, N.choose k := by
  rw [Finset.sum_range_succ' (fun k => (N + 1).choose k) e,
    Finset.sum_range_succ' (fun k => N.choose k) e]
  have hpascal : ∀ k ∈ Finset.range e,
      (N + 1).choose (k + 1) = N.choose k + N.choose (k + 1) := by
    intro k _
    exact Nat.choose_succ_succ N k
  rw [Finset.sum_congr rfl hpascal, Finset.sum_add_distrib]
  simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

@[blueprint "lem:family-card-le-split-erase"
  (statement := /-- Let $W$ be a set with decidable equality, let $z\in W$ and let
  $\mathcal{A}$ be a finite family of finite subsets of $W$. Write
  $\mathcal{B}=\{a\setminus\{z\}: a\in\mathcal{A}\}$ and
  $\mathcal{C}=\{a\setminus\{z\}: a\in\mathcal{A},\ z\in a,\ a\setminus\{z\}\in\mathcal{A}\}$.
  Then $|\mathcal{A}|\le|\mathcal{B}|+|\mathcal{C}|$. -/)
  (proof := /-- Split $\mathcal{A}$ into the subfamily
  $\mathcal{A}_1=\{a\in\mathcal{A}: z\in a\ \text{and}\ a\setminus\{z\}\in\mathcal{A}\}$ and its
  complement $\mathcal{A}_2=\{a\in\mathcal{A}:\ \text{not}\ (z\in a\ \text{and}\
  a\setminus\{z\}\in\mathcal{A})\}$ inside $\mathcal{A}$, so that
  $|\mathcal{A}_1|+|\mathcal{A}_2|=|\mathcal{A}|$.

  The map $a\mapsto a\setminus\{z\}$ is injective on $\mathcal{A}_1$: if $a,a'\in\mathcal{A}_1$
  then $z\in a$ and $z\in a'$, hence $a=\{z\}\cup(a\setminus\{z\})$ and
  $a'=\{z\}\cup(a'\setminus\{z\})$, so $a\setminus\{z\}=a'\setminus\{z\}$ forces $a=a'$.
  Consequently $|\mathcal{C}|=|\mathcal{A}_1|$, since $\mathcal{C}$ is by definition the image
  of $\mathcal{A}_1$ under this map.

  The same map is injective on $\mathcal{A}_2$. Let $a,a'\in\mathcal{A}_2$ with
  $a\setminus\{z\}=a'\setminus\{z\}$. If $z\in a$ and $z\in a'$ then, as above, $a=a'$. If
  $z\notin a$ and $z\notin a'$ then $a=a\setminus\{z\}=a'\setminus\{z\}=a'$. Finally suppose
  $z\in a$ and $z\notin a'$ (the remaining case is symmetric). Then
  $a'=a'\setminus\{z\}=a\setminus\{z\}$, and $a'\in\mathcal{A}$, so
  $a\setminus\{z\}\in\mathcal{A}$; together with $z\in a$ this contradicts $a\in\mathcal{A}_2$.
  Hence $|\mathcal{A}_2|$ equals the cardinality of the image of $\mathcal{A}_2$ under
  $a\mapsto a\setminus\{z\}$, and that image is contained in $\mathcal{B}$ because
  $\mathcal{A}_2\subseteq\mathcal{A}$; therefore $|\mathcal{A}_2|\le|\mathcal{B}|$.

  Combining, $|\mathcal{A}|=|\mathcal{A}_1|+|\mathcal{A}_2|\le|\mathcal{C}|+|\mathcal{B}|$. -/)
  (title := /-- Splitting a set family along one element -/)
  (latexEnv := "lemma")]
lemma family_card_le_split_erase {W : Type*} [DecidableEq W] (z : W)
    (A : Finset (Finset W)) :
    A.card ≤ (A.image (fun a => a.erase z)).card
      + ((A.filter (fun a => z ∈ a ∧ a.erase z ∈ A)).image (fun a => a.erase z)).card := by
  classical
  have hinj₁ : Set.InjOn (fun a : Finset W => a.erase z)
      (A.filter (fun a => z ∈ a ∧ a.erase z ∈ A)) := by
    intro a ha a' ha' heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha ha'
    simp only at heq
    rw [← Finset.insert_erase ha.2.1, ← Finset.insert_erase ha'.2.1, heq]
  have hinj₂ : Set.InjOn (fun a : Finset W => a.erase z)
      (A.filter (fun a => ¬ (z ∈ a ∧ a.erase z ∈ A))) := by
    intro a ha a' ha' heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha ha'
    simp only at heq
    by_cases hza : z ∈ a
    · by_cases hza' : z ∈ a'
      · rw [← Finset.insert_erase hza, ← Finset.insert_erase hza', heq]
      · exfalso
        have hea : a' = a.erase z := by
          rw [heq, Finset.erase_eq_self.2 hza']
        exact ha.2 ⟨hza, hea ▸ ha'.1⟩
    · by_cases hza' : z ∈ a'
      · exfalso
        have hea : a = a'.erase z := by
          rw [← heq, Finset.erase_eq_self.2 hza]
        exact ha'.2 ⟨hza', hea ▸ ha.1⟩
      · rw [← Finset.erase_eq_self.2 hza, ← Finset.erase_eq_self.2 hza', heq]
  have hcard₁ : ((A.filter (fun a => z ∈ a ∧ a.erase z ∈ A)).image
      (fun a => a.erase z)).card = (A.filter (fun a => z ∈ a ∧ a.erase z ∈ A)).card :=
    Finset.card_image_of_injOn hinj₁
  have hcard₂ : ((A.filter (fun a => ¬ (z ∈ a ∧ a.erase z ∈ A))).image
      (fun a => a.erase z)).card = (A.filter (fun a => ¬ (z ∈ a ∧ a.erase z ∈ A))).card :=
    Finset.card_image_of_injOn hinj₂
  have hsubB : (A.filter (fun a => ¬ (z ∈ a ∧ a.erase z ∈ A))).image (fun a => a.erase z)
      ⊆ A.image (fun a => a.erase z) :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have hle : (A.filter (fun a => ¬ (z ∈ a ∧ a.erase z ∈ A))).card
      ≤ (A.image (fun a => a.erase z)).card := by
    rw [← hcard₂]
    exact Finset.card_le_card hsubB
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := A) (p := fun a => z ∈ a ∧ a.erase z ∈ A)
  omega

@[blueprint "lem:sauer-shelah-family"
  (statement := /-- Let $W$ be a set with decidable equality, let $d\in\mathbb{N}$, let
  $s\subseteq W$ be finite and let $\mathcal{A}$ be a finite family of subsets of $s$. Say that
  $\mathcal{A}$ \emph{traces} a finite set $t$ if for every $u\subseteq t$ there is
  $a\in\mathcal{A}$ with $t\cap a=u$. If every $t\subseteq s$ traced by $\mathcal{A}$ satisfies
  $|t|\le d$, then
  $$|\mathcal{A}|\;\le\;\sum_{k=0}^{d}\binom{|s|}{k}.$$ -/)
  (proof := /-- We argue by strong induction on the finite set $s$, the statement being
  quantified over all $d$ and all families $\mathcal{A}$; so we may assume the assertion for
  every proper subset of $s$, for every $d$ and every family.

  \emph{Case $s=\emptyset$.} Every $a\in\mathcal{A}$ satisfies $a\subseteq\emptyset$, hence
  $a=\emptyset$, so $\mathcal{A}\subseteq\{\emptyset\}$ and $|\mathcal{A}|\le 1$. On the other
  hand the term $k=0$ of the right-hand sum equals $\binom{0}{0}=1$ and all terms are
  nonnegative, so the sum is at least $1$. This gives the claim.

  \emph{Case $s\neq\emptyset$, $d=0$.} By \cref{lem:family-card-le-one-of-no-shattered-singleton}
  the hypothesis forces $|\mathcal{A}|\le 1$, while the right-hand side is
  $\binom{|s|}{0}=1$.

  \emph{Case $s\neq\emptyset$, $d=e+1$.} Choose $z\in s$ and put $s'=s\setminus\{z\}$, a proper
  subset of $s$ with $|s|=|s'|+1$. Define
  $\mathcal{B}=\{a\setminus\{z\}: a\in\mathcal{A}\}$ and
  $\mathcal{C}=\{a\setminus\{z\}: a\in\mathcal{A},\ z\in a,\ a\setminus\{z\}\in\mathcal{A}\}$;
  all members of $\mathcal{B}$ and of $\mathcal{C}$ are subsets of $s'$, since
  $a\subseteq s$ implies $a\setminus\{z\}\subseteq s'$.

  \emph{The family $\mathcal{B}$.} Let $t\subseteq s'$ be traced by $\mathcal{B}$; we show $t$ is
  traced by $\mathcal{A}$. Let $u\subseteq t$ and pick $b\in\mathcal{B}$ with $t\cap b=u$, say
  $b=a\setminus\{z\}$ with $a\in\mathcal{A}$. Since $z\notin t$ we have
  $t\cap a=t\cap(a\setminus\{z\})=u$. Thus $t$ is traced by $\mathcal{A}$, and $t\subseteq s$,
  so the hypothesis gives $|t|\le e+1$. The inductive hypothesis for $s'$ with the same
  $e+1$ therefore yields $|\mathcal{B}|\le\sum_{k=0}^{e+1}\binom{|s'|}{k}$.

  \emph{The family $\mathcal{C}$.} Let $t\subseteq s'$ be traced by $\mathcal{C}$; we show that
  $\{z\}\cup t$ is traced by $\mathcal{A}$. Let $u\subseteq\{z\}\cup t$ and put
  $u'=u\setminus\{z\}$, so $u'\subseteq t$. Pick $c\in\mathcal{C}$ with $t\cap c=u'$, say
  $c=a\setminus\{z\}$ where $a\in\mathcal{A}$, $z\in a$ and $a\setminus\{z\}\in\mathcal{A}$.
  If $z\in u$, take the member $a$: since $z\in a$ and $z\notin t$,
  $(\{z\}\cup t)\cap a=\{z\}\cup(t\cap a)=\{z\}\cup(t\cap c)=\{z\}\cup u'=u$. If $z\notin u$,
  take the member $a\setminus\{z\}\in\mathcal{A}$: as $z\notin a\setminus\{z\}$,
  $(\{z\}\cup t)\cap(a\setminus\{z\})=t\cap c=u'=u$. Hence $\{z\}\cup t$ is traced by
  $\mathcal{A}$ and is contained in $s$, so the hypothesis gives $|\{z\}\cup t|\le e+1$; since
  $z\notin t$ this means $|t|+1\le e+1$, i.e. $|t|\le e$. The inductive hypothesis for $s'$
  with $e$ yields $|\mathcal{C}|\le\sum_{k=0}^{e}\binom{|s'|}{k}$.

  \emph{Conclusion.} By \cref{lem:family-card-le-split-erase},
  $|\mathcal{A}|\le|\mathcal{B}|+|\mathcal{C}|$, so
  $$|\mathcal{A}|\;\le\;\sum_{k=0}^{e+1}\binom{|s'|}{k}+\sum_{k=0}^{e}\binom{|s'|}{k}
  \;=\;\sum_{k=0}^{e+1}\binom{|s'|+1}{k}\;=\;\sum_{k=0}^{d}\binom{|s|}{k},$$
  where the middle equality is \cref{lem:sum-choose-succ} applied with $N=|s'|$ and exponent
  bound $e+1$, and the last one uses $|s|=|s'|+1$. -/)
  (title := /-- The Sauer--Shelah lemma for set families -/)
  (latexEnv := "lemma")]
lemma sauer_shelah_family {W : Type*} [DecidableEq W] (s : Finset W) (d : ℕ)
    (A : Finset (Finset W)) (hsub : ∀ a ∈ A, a ⊆ s)
    (h : ∀ t ⊆ s, (∀ u ⊆ t, ∃ a ∈ A, t ∩ a = u) → t.card ≤ d) :
    A.card ≤ ∑ k ∈ Finset.range (d + 1), s.card.choose k := by
  classical
  induction s using Finset.strongInduction generalizing d A with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
    · have hA : A ⊆ {∅} := by
        intro a ha
        simp only [Finset.mem_singleton]
        exact Finset.subset_empty.1 (hsub a ha)
      have h1 : A.card ≤ 1 := by
        simpa using Finset.card_le_card hA
      have h2 : 1 ≤ ∑ k ∈ Finset.range (d + 1), Nat.choose 0 k := by
        have hmem : 0 ∈ Finset.range (d + 1) := Finset.mem_range.2 (Nat.succ_pos d)
        have := Finset.single_le_sum (f := fun k => Nat.choose 0 k)
          (fun k _ => Nat.zero_le _) hmem
        simpa using this
      have h3 : (∅ : Finset W).card = 0 := rfl
      rw [h3]
      omega
    · match d with
      | 0 =>
        have h1 : A.card ≤ 1 :=
          family_card_le_one_of_no_shattered_singleton s A hsub h
        simpa using h1
      | (e + 1) =>
        set s' : Finset W := s.erase z with hs'
        have hss' : s' ⊂ s := Finset.erase_ssubset hz
        have hs'card : s.card = s'.card + 1 := by
          rw [hs', Finset.card_erase_of_mem hz]
          have : 1 ≤ s.card := Finset.card_pos.2 ⟨z, hz⟩
          omega
        have hznot : z ∉ s' := Finset.notMem_erase z s
        set B : Finset (Finset W) := A.image (fun a => a.erase z) with hB
        set C : Finset (Finset W) :=
          (A.filter (fun a => z ∈ a ∧ a.erase z ∈ A)).image (fun a => a.erase z) with hC
        have hinter : ∀ (t a : Finset W), z ∉ t → t ∩ a = t ∩ a.erase z := by
          intro t a hzt
          ext w
          simp only [Finset.mem_inter, Finset.mem_erase]
          constructor
          · intro hw
            exact ⟨hw.1, fun hwz => hzt (hwz ▸ hw.1), hw.2⟩
          · intro hw
            exact ⟨hw.1, hw.2.2⟩
        have hBsub : ∀ b ∈ B, b ⊆ s' := by
          intro b hb
          rw [hB, Finset.mem_image] at hb
          obtain ⟨a, ha, rfl⟩ := hb
          exact Finset.erase_subset_erase z (hsub a ha)
        have hBh : ∀ t ⊆ s', (∀ u ⊆ t, ∃ b ∈ B, t ∩ b = u) → t.card ≤ e + 1 := by
          intro t hts ht
          refine h t (hts.trans (Finset.erase_subset z s)) ?_
          intro u hu
          obtain ⟨b, hb, hbu⟩ := ht u hu
          rw [hB, Finset.mem_image] at hb
          obtain ⟨a, ha, rfl⟩ := hb
          exact ⟨a, ha, by rw [hinter t a (fun hzt => hznot (hts hzt)), hbu]⟩
        have hCsub : ∀ c ∈ C, c ⊆ s' := by
          intro c hc
          rw [hC, Finset.mem_image] at hc
          obtain ⟨a, ha, rfl⟩ := hc
          exact Finset.erase_subset_erase z (hsub a (Finset.mem_filter.1 ha).1)
        have hCh : ∀ t ⊆ s', (∀ u ⊆ t, ∃ c ∈ C, t ∩ c = u) → t.card ≤ e := by
          intro t hts ht
          have hzt : z ∉ t := fun hzt => hznot (hts hzt)
          have hins : insert z t ⊆ s :=
            Finset.insert_subset hz (hts.trans (Finset.erase_subset z s))
          have htrace : ∀ u ⊆ insert z t, ∃ a ∈ A, insert z t ∩ a = u := by
            intro u hu
            obtain ⟨c, hc, hcu⟩ := ht (u.erase z) (by
              intro w hw
              have hw' := Finset.mem_erase.1 hw
              have := hu hw'.2
              rcases Finset.mem_insert.1 this with rfl | hwt
              · exact absurd rfl hw'.1
              · exact hwt)
            rw [hC, Finset.mem_image] at hc
            obtain ⟨a, ha, rfl⟩ := hc
            have haA := (Finset.mem_filter.1 ha).1
            have hza : z ∈ a := (Finset.mem_filter.1 ha).2.1
            have haeA : a.erase z ∈ A := (Finset.mem_filter.1 ha).2.2
            by_cases hzu : z ∈ u
            · refine ⟨a, haA, ?_⟩
              have : insert z t ∩ a = insert z (t ∩ a) := by
                rw [Finset.insert_inter_of_mem hza]
              rw [this, hinter t a hzt, hcu, Finset.insert_erase hzu]
            · refine ⟨a.erase z, haeA, ?_⟩
              have hzae : z ∉ a.erase z := Finset.notMem_erase z a
              rw [Finset.insert_inter_of_notMem hzae, hcu, Finset.erase_eq_self.2 hzu]
          have hcard := h (insert z t) hins htrace
          rw [Finset.card_insert_of_notMem hzt] at hcard
          omega
        have hBle : B.card ≤ ∑ k ∈ Finset.range (e + 1 + 1), s'.card.choose k :=
          ih s' hss' (d := e + 1) (A := B) hBsub hBh
        have hCle : C.card ≤ ∑ k ∈ Finset.range (e + 1), s'.card.choose k :=
          ih s' hss' (d := e) (A := C) hCsub hCh
        have hsplit : A.card ≤ B.card + C.card := family_card_le_split_erase z A
        have hid := sum_choose_succ s'.card (e + 1)
        rw [hs'card]
        omega

@[blueprint "lem:growth-function-le-sum-choose"
  (statement := /-- Let $Z$ be a set, let $\mathcal{G}\subseteq\{0,1\}^{Z}$ and let
  $d,m\in\mathbb{N}$ with $\mathrm{VC}(\mathcal{G})\le d$. Then
  $$\Gamma_{\mathcal{G}}(m)\;\le\;\sum_{k=0}^{d}\binom{m}{k},$$
  where $\Gamma_{\mathcal{G}}$ is the growth function of \cref{def:growth-function} and
  $\mathrm{VC}$ is as in \cref{def:vc-dim}. -/)
  (proof := /-- By \cref{def:growth-function}, $\Gamma_{\mathcal{G}}(m)$ is the supremum of the
  set of natural numbers of the form $|\mathcal{G}(s)|$ with $s\subseteq Z$ finite and $|s|=m$,
  where $\mathcal{G}(s)$ is the set of restrictions of members of $\mathcal{G}$ to $s$. Since
  every element of that set is bounded by $\sum_{k=0}^{d}\binom{m}{k}$, as we now show, the
  supremum is bounded by the same quantity.

  So fix a finite $s\subseteq Z$ with $|s|=m$ and write $W$ for the (finite) type of elements of
  $s$; thus $|W|=m$. The set $\mathcal{G}(s)$ of restrictions is a set of functions
  $W\to\{0,1\}$, hence finite, and we let $\mathcal{R}$ denote the corresponding finite family.
  The map sending a function $h\colon W\to\{0,1\}$ to the set $\{z\in W: h(z)=1\}$ is injective:
  if two functions determine the same set then they agree at every $z\in W$, because their
  values lie in $\{0,1\}$. Let $\mathcal{A}$ be the image of $\mathcal{R}$ under this map, so
  that $|\mathcal{A}|=|\mathcal{G}(s)|$, and every member of $\mathcal{A}$ is a subset of $W$.

  We verify the hypothesis of \cref{lem:sauer-shelah-family} for $\mathcal{A}$ over the ambient
  finite set $W$. Let $t\subseteq W$ be traced by $\mathcal{A}$, i.e. for every $u\subseteq t$
  there is $a\in\mathcal{A}$ with $t\cap a=u$. Let $t'\subseteq Z$ be the image of $t$ under the
  inclusion $W\to Z$; we claim $t'$ is shattered by $\mathcal{G}$ in the sense of
  \cref{def:class-shatters}. Let $b\colon Z\to\{0,1\}$ be arbitrary and apply the tracing
  property to $u=\{z\in t: b(z)=1\}$: there is $a\in\mathcal{A}$ with $t\cap a=u$, and by
  construction $a=\{z\in W: h(z)=1\}$ for some restriction $h$ of a member $g\in\mathcal{G}$.
  For $z\in t$ we then have $g(z)=1$ iff $z\in a$ iff $z\in u$ iff $b(z)=1$, hence $g(z)=b(z)$
  since both values lie in $\{0,1\}$. Thus $t'$ is shattered by $\mathcal{G}$, and
  \cref{lem:card-le-of-class-shatters} gives $|t'|\le d$. The inclusion $W\to Z$ is injective,
  so $|t|=|t'|\le d$.

  Therefore \cref{lem:sauer-shelah-family}, applied with the ambient set $W$ and the family
  $\mathcal{A}$, yields
  $|\mathcal{G}(s)|=|\mathcal{A}|\le\sum_{k=0}^{d}\binom{|W|}{k}=\sum_{k=0}^{d}\binom{m}{k}$,
  which is the required bound. -/)
  (title := /-- The growth function is bounded by a partial binomial sum -/)
  (latexEnv := "lemma")]
lemma growth_function_le_sum_choose {Z : Type*} (G : Set (Z → Bool)) (d m : ℕ)
    (hvc : vc_dim G ≤ (d : ℕ∞)) :
    growth_function G m ≤ ∑ k ∈ Finset.range (d + 1), m.choose k := by
  classical
  refine csSup_le' ?_
  rintro k ⟨s, hscard, rfl⟩
  set W := {x : Z // x ∈ s} with hW
  set R : Set (W → Bool) := (fun (g : Z → Bool) (z : W) => g z.1) '' G with hR
  have hRfin : R.Finite := Set.toFinite R
  set Rf : Finset (W → Bool) := hRfin.toFinset with hRf
  set A : Finset (Finset W) :=
    Rf.image (fun h => Finset.univ.filter (fun z => h z = true)) with hA
  have hinj : Set.InjOn (fun h : W → Bool => Finset.univ.filter (fun z => h z = true)) Rf := by
    intro h₁ _ h₂ _ heq
    funext z
    have : (z ∈ Finset.univ.filter (fun z => h₁ z = true))
        ↔ (z ∈ Finset.univ.filter (fun z => h₂ z = true)) := by
      simp only at heq
      rw [heq]
    simpa using Bool.eq_iff_iff.mpr (by simpa using this)
  have hAcard : A.card = R.ncard := by
    have hx : R.ncard = Rf.card := Set.ncard_eq_toFinset_card R hRfin
    rw [hA, Finset.card_image_of_injOn hinj, hx]
  have hmem : ∀ a ∈ A, ∃ g ∈ G, a = Finset.univ.filter (fun z : W => g z.1 = true) := by
    intro a ha
    rw [hA, Finset.mem_image] at ha
    obtain ⟨h, hh, rfl⟩ := ha
    rw [hRf, Set.Finite.mem_toFinset, hR] at hh
    obtain ⟨g, hgG, rfl⟩ := hh
    exact ⟨g, hgG, rfl⟩
  have hbound : ∀ t ⊆ (Finset.univ : Finset W),
      (∀ u ⊆ t, ∃ a ∈ A, t ∩ a = u) → t.card ≤ d := by
    intro t _ ht
    have hcs : class_shatters G (t.image (fun z : W => z.1)) := by
      intro b
      obtain ⟨a, haA, hint⟩ :=
        ht (t.filter (fun z : W => b z.1 = true)) (Finset.filter_subset _ _)
      obtain ⟨g, hgG, rfl⟩ := hmem a haA
      refine ⟨g, hgG, ?_⟩
      intro y hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hy
      have hmem' : (w ∈ t ∩ Finset.univ.filter (fun z : W => g z.1 = true))
          ↔ (w ∈ t.filter (fun z : W => b z.1 = true)) := by
        rw [hint]
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, hw] at hmem'
      exact Bool.eq_iff_iff.mpr hmem'
    have hcard : (t.image (fun z : W => z.1)).card = t.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    have hle := card_le_of_class_shatters G d hvc _ hcs
    omega
  have hkey := sauer_shelah_family (Finset.univ : Finset W) d A
    (fun a _ => Finset.subset_univ a) hbound
  have huniv : (Finset.univ : Finset W).card = m := by
    have : (Finset.univ : Finset W).card = s.card := by
      simp [hW]
    rw [this, hscard]
  rw [huniv] at hkey
  omega

@[blueprint "lem:sauer-lemma"
  (statement := /-- (Sauer's Lemma.) Let $Z$ be a set, let $\mathcal{G}\subseteq\{0,1\}^{Z}$ and
  let $d,m\in\mathbb{N}$ with $1\le d$, $\mathrm{VC}(\mathcal{G})\le d$ and $d\le m$. Then
  $$\Gamma_{\mathcal{G}}(m)\;\le\;\Bigl(\frac{e\,m}{d}\Bigr)^{d},$$
  where $\Gamma_{\mathcal{G}}$ is the growth function of \cref{def:growth-function},
  $\mathrm{VC}$ is as in \cref{def:vc-dim} and $e$ is Euler's number. -/)
  (proof := /-- By \cref{lem:growth-function-le-sum-choose}, applied with the hypothesis
  $\mathrm{VC}(\mathcal{G})\le d$, we have the combinatorial bound
  $$\Gamma_{\mathcal{G}}(m)\;\le\;\sum_{k=0}^{d}\binom{m}{k}$$
  as natural numbers; casting into $\mathbb{R}$ preserves this inequality and turns the
  right-hand side into $\sum_{k=0}^{d}\binom{m}{k}$ computed in $\mathbb{R}$, because the cast
  of a finite sum of natural numbers is the sum of the casts.

  By \cref{lem:binomial-sum-le-exp-pow}, applied with the hypotheses $1\le d$ and $d\le m$,
  $$\sum_{k=0}^{d}\binom{m}{k}\;\le\;\Bigl(\frac{e\,m}{d}\Bigr)^{d}.$$
  Chaining the two inequalities gives
  $\Gamma_{\mathcal{G}}(m)\le\bigl(e\,m/d\bigr)^{d}$, as required. -/)
  (title := /-- Sauer's Lemma -/)
  (latexEnv := "lemma")]
lemma sauer_lemma {Z : Type*} (G : Set (Z → Bool)) (d m : ℕ) (hd : 1 ≤ d)
    (hvc : vc_dim G ≤ (d : ℕ∞)) (hm : d ≤ m) :
    (growth_function G m : ℝ) ≤ (Real.exp 1 * m / d) ^ d := by
  have hcomb : growth_function G m ≤ ∑ k ∈ Finset.range (d + 1), m.choose k :=
    growth_function_le_sum_choose G d m hvc
  have hcast : (growth_function G m : ℝ) ≤ ∑ k ∈ Finset.range (d + 1), (m.choose k : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 hcomb
    rwa [Nat.cast_sum] at this
  exact le_trans hcast (binomial_sum_le_exp_pow d m hd hm)

@[blueprint "lem:logb-linear-upper-bound"
  (statement := /-- Let $n$, $M$ and $x$ be positive real numbers. Then
  $$n\log_2(e\,x\,M)\;\le\;\frac{x}{2}+n\log_2\Bigl(\frac{2nM}{\ln 2}\Bigr),$$
  where $\log_2$ is the binary logarithm, $\ln$ is the natural logarithm and $e$ is Euler's
  number. -/)
  (proof := /-- Since $n>0$, $M>0$ and $x>0$, and since $\ln 2>0$, the two numbers
  $a=e\,x\,M$ and $b=\dfrac{\ln 2}{2enM}$ are positive. The elementary inequality
  $\ln y\le y-1$, valid for every real $y>0$, applied to $y=ab>0$ together with the additivity
  of the logarithm on positive factors gives
  $$\ln a+\ln b\;=\;\ln(ab)\;\le\;ab-1 .$$
  We compute the two ingredients of this estimate. First,
  $$ab\;=\;e\,x\,M\cdot\frac{\ln 2}{2enM}\;=\;\frac{x\ln 2}{2n},$$
  where the cancellation of $e$, $M$ and one factor $2$ uses $e\neq 0$, $M\neq0$ and $n\neq0$.
  Second, $b^{-1}=e\cdot\dfrac{2nM}{\ln 2}$, so that
  $$\ln b\;=\;-\ln\bigl(b^{-1}\bigr)\;=\;-\Bigl(\ln e+\ln\frac{2nM}{\ln 2}\Bigr)
  \;=\;-\Bigl(1+\ln\frac{2nM}{\ln 2}\Bigr),$$
  using $\ln e=1$ and the positivity of $e$ and of $\dfrac{2nM}{\ln 2}$. Substituting both
  identities into the displayed estimate and rearranging yields
  $$\ln(e\,x\,M)\;\le\;\frac{x\ln 2}{2n}+\ln\Bigl(\frac{2nM}{\ln 2}\Bigr).$$
  Finally, multiplying this inequality by the positive factor $\dfrac{n}{\ln 2}$ preserves its
  direction, and by the definition $\log_2 y=\dfrac{\ln y}{\ln 2}$ we obtain
  $$n\log_2(e\,x\,M)\;\le\;\frac{n}{\ln 2}\Bigl(\frac{x\ln 2}{2n}
  +\ln\frac{2nM}{\ln 2}\Bigr)\;=\;\frac{x}{2}+n\log_2\Bigl(\frac{2nM}{\ln 2}\Bigr),$$
  which is the assertion. -/)
  (title := /-- A linear upper bound for a binary logarithm -/)
  (latexEnv := "lemma")]
lemma logb_linear_upper_bound (n M x : ℝ) (hn : 0 < n) (hM : 0 < M) (hx : 0 < x) :
    n * Real.logb 2 (Real.exp 1 * x * M) ≤
      x / 2 + n * Real.logb 2 (2 * n * M / Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : (0:ℝ) < Real.exp 1 * x * M := by positivity
  have hb : (0:ℝ) < Real.log 2 / (2 * Real.exp 1 * n * M) := by positivity
  have hkey := Real.log_le_sub_one_of_pos (mul_pos ha hb)
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt hb)] at hkey
  have hprod : Real.exp 1 * x * M * (Real.log 2 / (2 * Real.exp 1 * n * M))
      = x * Real.log 2 / (2 * n) := by
    have hne : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
    field_simp
  have hbval : Real.log (Real.log 2 / (2 * Real.exp 1 * n * M))
      = -(1 + Real.log (2 * n * M / Real.log 2)) := by
    have hrw : Real.log 2 / (2 * Real.exp 1 * n * M)
        = (Real.exp 1 * (2 * n * M / Real.log 2))⁻¹ := by
      have hne : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
      field_simp
    rw [hrw, Real.log_inv, Real.log_mul (Real.exp_ne_zero 1) (by positivity),
      Real.log_exp]
  rw [hprod, hbval] at hkey
  have hmain : Real.log (Real.exp 1 * x * M)
      ≤ x * Real.log 2 / (2 * n) + Real.log (2 * n * M / Real.log 2) := by linarith
  have heq : n * ((x * Real.log 2 / (2 * n) + Real.log (2 * n * M / Real.log 2))
      / Real.log 2) = x / 2 + n * (Real.log (2 * n * M / Real.log 2) / Real.log 2) := by
    field_simp
  simp only [Real.logb]
  calc n * (Real.log (Real.exp 1 * x * M) / Real.log 2)
      ≤ n * ((x * Real.log 2 / (2 * n) + Real.log (2 * n * M / Real.log 2))
        / Real.log 2) := by
        gcongr
    _ = x / 2 + n * (Real.log (2 * n * M / Real.log 2) / Real.log 2) := heq

@[blueprint "lem:one-lt-logb-two-scaled"
  (statement := /-- Let $n$ and $M$ be real numbers with $n\ge 1$, $M>0$ and $nM\ge 1$. Then
  $$\log_2\Bigl(\frac{2nM}{\ln 2}\Bigr)\;>\;1,$$
  where $\log_2$ is the binary logarithm and $\ln$ is the natural logarithm. -/)
  (proof := /-- Since $2>1$ we have $\ln 2>0$, and since $2>0$ and $2\neq 1$ the strict form of
  the elementary inequality $\ln y<y-1$, valid for every real $y>0$ with $y\neq1$, gives
  $\ln 2<2-1=1$. From the hypothesis $nM\ge1$ we get $2nM\ge2>2\ln 2$, and dividing this
  inequality by $\ln 2>0$ gives $\dfrac{2nM}{\ln 2}>2$. In particular $\dfrac{2nM}{\ln 2}>0$,
  so the strict monotonicity of $\log_2$ on the positive reals applies and yields
  $$\log_2\Bigl(\frac{2nM}{\ln 2}\Bigr)\;>\;\log_2 2\;=\;1,$$
  the last equality being the value of the binary logarithm at its base. -/)
  (title := /-- The scaled logarithm exceeds one -/)
  (latexEnv := "lemma")]
lemma one_lt_logb_two_scaled (n M : ℝ) (hn : 1 ≤ n) (hM : 0 < M) (hnM : 1 ≤ n * M) :
    1 < Real.logb 2 (2 * n * M / Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
    linarith
  have h2 : (2:ℝ) < 2 * n * M / Real.log 2 := by
    rw [lt_div_iff₀ hlog2]
    nlinarith
  have := Real.logb_lt_logb (b := 2) (by norm_num) (x := 2) (y := 2 * n * M / Real.log 2)
    (by norm_num) h2
  rwa [Real.logb_self_eq_one (by norm_num)] at this

@[blueprint "lem:technical-corollary"
  (statement := /-- For every integer $N\ge 1$ and every real $M>0$ with $N M\ge 1$ there exists
  a natural number $m$ such that
  $$N\le m\le 3N\log_2\Bigl(\frac{2NM}{\ln 2}\Bigr)
  \qquad\text{and}\qquad m>N\log_2(e\,m\,M),$$
  where $\log_2$ is the binary logarithm and $e$ is Euler's number. -/)
  (proof := /-- Write $L=N\log_2\bigl(2NM/\ln 2\bigr)$. Since $N\ge1$ as an integer we have
  $N\ge1$ as a real number, hence $N>0$, and \cref{lem:one-lt-logb-two-scaled}, applied with
  $n=N$ and the hypotheses $N\ge1$, $M>0$ and $NM\ge1$, gives
  $\log_2\bigl(2NM/\ln 2\bigr)>1$. Multiplying this strict inequality by $N\ge1>0$ yields
  $$L\;=\;N\log_2\Bigl(\frac{2NM}{\ln 2}\Bigr)\;>\;N\;\ge\;1,$$
  so in particular $L>1>0$ and $2L>0$.

  We take $m=\lfloor 2L\rfloor+1$, where $\lfloor\cdot\rfloor$ denotes the largest natural
  number not exceeding its (nonnegative) argument, and verify the three required properties.

  First, $N\le 2L$ because $L>N$, so by the defining property of the floor
  $N\le\lfloor 2L\rfloor$, and therefore $N\le\lfloor 2L\rfloor+1=m$.

  Second, $\lfloor 2L\rfloor\le 2L$ gives $m\le 2L+1$, and $L\ge1$ gives $2L+1\le 3L$; hence
  $$m\;\le\;3L\;=\;3N\log_2\Bigl(\frac{2NM}{\ln 2}\Bigr).$$

  Third, the floor satisfies $2L<\lfloor 2L\rfloor+1=m$, and in particular $m>2L>0$. Applying
  \cref{lem:logb-linear-upper-bound} with $n=N>0$, the same $M>0$ and $x=m>0$ gives
  $$N\log_2(e\,m\,M)\;\le\;\frac{m}{2}+N\log_2\Bigl(\frac{2NM}{\ln 2}\Bigr)
  \;=\;\frac{m}{2}+L .$$
  Combining this with $L<m/2$, which is exactly the inequality $2L<m$ established above, we
  conclude $N\log_2(e\,m\,M)<m/2+m/2=m$. Thus $m$ has all the required properties. -/)
  (title := /-- A technical logarithmic corollary -/)
  (latexEnv := "lemma")]
lemma technical_corollary (N : ℕ) (M : ℝ) (hN : 1 ≤ N) (hM : 0 < M) (hNM : 1 ≤ (N : ℝ) * M) :
    ∃ m : ℕ, N ≤ m ∧ (m : ℝ) ≤ 3 * (N : ℝ) * Real.logb 2 (2 * (N : ℝ) * M / Real.log 2) ∧
      (N : ℝ) * Real.logb 2 (Real.exp 1 * m * M) < m := by
  have hN1 : (1:ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  set L : ℝ := (N : ℝ) * Real.logb 2 (2 * (N : ℝ) * M / Real.log 2) with hLdef
  have hlogb1 : 1 < Real.logb 2 (2 * (N : ℝ) * M / Real.log 2) :=
    one_lt_logb_two_scaled (N : ℝ) M hN1 hM hNM
  have hLgt : (N : ℝ) < L := by
    rw [hLdef]
    nlinarith
  have hLpos : 0 < L := lt_of_le_of_lt (le_of_lt (lt_of_lt_of_le zero_lt_one hN1)) hLgt
  refine ⟨Nat.floor (2 * L) + 1, ?_, ?_, ?_⟩
  · have h1 : (N : ℝ) ≤ 2 * L := by linarith
    have h2 : (N : ℕ) ≤ Nat.floor (2 * L) := Nat.le_floor (by exact_mod_cast h1)
    omega
  · have h1 : (Nat.floor (2 * L) : ℝ) + 1 ≤ 2 * L + 1 := by
      have := Nat.floor_le (le_of_lt (by linarith : (0:ℝ) < 2 * L))
      linarith
    have h2 : (2 * L + 1 : ℝ) ≤ 3 * L := by linarith
    have hcast : ((Nat.floor (2 * L) + 1 : ℕ) : ℝ) = (Nat.floor (2 * L) : ℝ) + 1 := by
      push_cast
      ring
    rw [hcast, hLdef] at *
    linarith
  · have hmgt : 2 * L < ((Nat.floor (2 * L) + 1 : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one (2 * L)
      push_cast
      linarith
    have hmpos : (0:ℝ) < ((Nat.floor (2 * L) + 1 : ℕ) : ℝ) := by
      have : (0:ℝ) < 2 * L := by linarith
      linarith
    have hbound := logb_linear_upper_bound (N : ℝ) M ((Nat.floor (2 * L) + 1 : ℕ) : ℝ)
      hNpos hM hmpos
    rw [← hLdef] at hbound
    linarith

@[blueprint "lem:cot-trace-take-prefix"
  (statement := /-- Let $f\colon\Sigma^*\to\Sigma$ be a next-token generator, let
  $T,t\in\mathbb{N}$ with $t\le T$ and let $\mathbf{x}\in\Sigma^*$. Then the first
  $|\mathbf{x}|+t$ tokens of the $T$-step trace form the $t$-step trace:
  $$f_{\mathrm{CoT}}^{T}(\mathbf{x})\bigl[:|\mathbf{x}|+t\bigr]=f_{\mathrm{CoT}}^{t}(\mathbf{x}),$$
  where $f_{\mathrm{CoT}}^{T}$ is as in \cref{def:cot-trace}. -/)
  (proof := /-- Since $t\le T$ there is $k\in\mathbb{N}$ with $T=t+k$. By \cref{def:cot-trace}
  the trace $f_{\mathrm{CoT}}^{T}(\mathbf{x})$ is the $T$-fold iterate of the apply-and-append
  map of \cref{def:apply-append} applied to $\mathbf{x}$, and iterates compose additively, so
  $$f_{\mathrm{CoT}}^{t+k}(\mathbf{x})=f_{\mathrm{CoT}}^{k}
  \bigl(f_{\mathrm{CoT}}^{t}(\mathbf{x})\bigr).$$
  Write $\mathbf{y}=f_{\mathrm{CoT}}^{t}(\mathbf{x})$. By \cref{lem:cot-trace-length} we have
  $|\mathbf{y}|=|\mathbf{x}|+t$, so the claimed identity is
  $f_{\mathrm{CoT}}^{k}(\mathbf{y})\bigl[:|\mathbf{y}|\bigr]=\mathbf{y}$, which is exactly
  \cref{lem:cot-trace-prefix} applied to the prompt $\mathbf{y}$ with generation length
  $k$. -/)
  (title := /-- Truncating a chain-of-thought trace yields the shorter trace -/)
  (latexEnv := "lemma")]
lemma cot_trace_take_prefix (f : List Bool → Bool) (T t : ℕ) (ht : t ≤ T) (x : List Bool) :
    (cot_trace f T x).take (x.length + t) = cot_trace f t x := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le ht
  subst hk
  have hsplit : cot_trace f (t + k) x = cot_trace f k (cot_trace f t x) := by
    simp only [cot_trace]
    rw [Nat.add_comm t k, Function.iterate_add_apply]
  rw [hsplit, ← cot_trace_length f t x]
  exact cot_trace_prefix f k (cot_trace f t x)

@[blueprint "lem:cot-trace-eq-of-agree"
  (statement := /-- Let $f,g\colon\Sigma^*\to\Sigma$ be next-token generators, let
  $T\in\mathbb{N}$ be a generation length and let $\mathbf{x},\mathbf{u}\in\Sigma^*$. Assume
  that $f_{\mathrm{CoT}}^{T}(\mathbf{x})=\mathbf{u}$ and that
  $$g\bigl(\mathbf{u}[:|\mathbf{x}|+t]\bigr)=f\bigl(\mathbf{u}[:|\mathbf{x}|+t]\bigr)
  \qquad\text{for every integer } t \text{ with } 0\le t<T.$$
  Then $g_{\mathrm{CoT}}^{T}(\mathbf{x})=\mathbf{u}$, where $f_{\mathrm{CoT}}^{T}$ and
  $g_{\mathrm{CoT}}^{T}$ are as in \cref{def:cot-trace}. -/)
  (proof := /-- First note that for every $t$ with $0\le t\le T$ we have
  $$\mathbf{u}[:|\mathbf{x}|+t]=f_{\mathrm{CoT}}^{t}(\mathbf{x}),$$
  because $\mathbf{u}=f_{\mathrm{CoT}}^{T}(\mathbf{x})$ by hypothesis and
  \cref{lem:cot-trace-take-prefix} identifies the first $|\mathbf{x}|+t$ tokens of the $T$-step
  trace with the $t$-step trace.

  We prove by induction on $t$ that $g_{\mathrm{CoT}}^{t}(\mathbf{x})
  =\mathbf{u}[:|\mathbf{x}|+t]$ for every $t$ with $0\le t\le T$.

  For $t=0$ the displayed identity of the previous paragraph gives
  $\mathbf{u}[:|\mathbf{x}|+0]=f_{\mathrm{CoT}}^{0}(\mathbf{x})$, and by \cref{def:cot-trace}
  both $f_{\mathrm{CoT}}^{0}(\mathbf{x})$ and $g_{\mathrm{CoT}}^{0}(\mathbf{x})$ equal
  $\mathbf{x}$, so the two sides agree.

  Now let $t+1\le T$ and assume the claim for $t$; in particular $t<T$ and $t\le T$. By
  \cref{lem:cot-trace-append} together with \cref{def:apply-append},
  $$g_{\mathrm{CoT}}^{t+1}(\mathbf{x})=g_{\mathrm{CoT}}^{t}(\mathbf{x})
  \cdot g\bigl(g_{\mathrm{CoT}}^{t}(\mathbf{x})\bigr),$$
  where $\cdot$ denotes appending one token. By the inductive hypothesis
  $g_{\mathrm{CoT}}^{t}(\mathbf{x})=\mathbf{u}[:|\mathbf{x}|+t]$, so this equals
  $\mathbf{u}[:|\mathbf{x}|+t]\cdot g\bigl(\mathbf{u}[:|\mathbf{x}|+t]\bigr)$, and the
  hypothesis of the lemma at the index $t<T$ rewrites the appended token as
  $f\bigl(\mathbf{u}[:|\mathbf{x}|+t]\bigr)$. Applying the displayed identity of the first
  paragraph at $t$ and at $t+1$ turns the required equality into
  $$f_{\mathrm{CoT}}^{t}(\mathbf{x})\cdot f\bigl(f_{\mathrm{CoT}}^{t}(\mathbf{x})\bigr)
  =f_{\mathrm{CoT}}^{t+1}(\mathbf{x}),$$
  which is again \cref{lem:cot-trace-append} combined with \cref{def:apply-append}. This
  completes the induction.

  Taking $t=T$ gives $g_{\mathrm{CoT}}^{T}(\mathbf{x})=\mathbf{u}[:|\mathbf{x}|+T]$. By
  \cref{lem:cot-trace-length} and $\mathbf{u}=f_{\mathrm{CoT}}^{T}(\mathbf{x})$ we have
  $|\mathbf{u}|=|\mathbf{x}|+T$, so truncating $\mathbf{u}$ to its own length returns
  $\mathbf{u}$, and therefore $g_{\mathrm{CoT}}^{T}(\mathbf{x})=\mathbf{u}$. -/)
  (title := /-- Traces agreeing on the observed prefixes coincide -/)
  (latexEnv := "lemma")]
lemma cot_trace_eq_of_agree (f g : List Bool → Bool) (T : ℕ) (x u : List Bool)
    (hf : cot_trace f T x = u)
    (hag : ∀ t, t < T → g (u.take (x.length + t)) = f (u.take (x.length + t))) :
    cot_trace g T x = u := by
  have hpref : ∀ t, t ≤ T → u.take (x.length + t) = cot_trace f t x := by
    intro t ht
    rw [← hf]
    exact cot_trace_take_prefix f T t ht x
  have key : ∀ t, t ≤ T → cot_trace g t x = u.take (x.length + t) := by
    intro t
    induction t with
    | zero =>
      intro ht
      rw [hpref 0 ht]
      simp [cot_trace]
    | succ t ih =>
      intro ht
      have htT : t < T := Nat.lt_of_lt_of_le (Nat.lt_succ_self t) ht
      rw [cot_trace_append, apply_append, ih (le_of_lt htT), hag t htT,
        hpref t (le_of_lt htT), hpref (t + 1) ht, cot_trace_append, apply_append]
  have hlen : u.length = x.length + T := by
    rw [← hf]
    exact cot_trace_length f T x
  rw [key T le_rfl, ← hlen]
  simp

@[blueprint "lem:ncard-image-le-of-factor"
  (statement := /-- Let $I$, $A$, $B$ be sets with $A$ nonempty, let $S\subseteq I$ and let
  $a\colon I\to A$ and $b\colon I\to B$ be maps such that the image $b(S)$ is finite and such
  that for all $i,j\in S$ the equality $b(i)=b(j)$ implies $a(i)=a(j)$. Then the images satisfy
  $|a(S)|\le|b(S)|$. -/)
  (proof := /-- Using the axiom of choice, define $h\colon B\to A$ by
  $$h(c)=\begin{cases} a(i_c) & \text{if the set } \{i\in S: b(i)=c\} \text{ is nonempty,}\\
  a_0 & \text{otherwise,}\end{cases}$$
  where $i_c$ denotes a chosen element of $\{i\in S: b(i)=c\}$ in the first case and $a_0$ is a
  fixed element of the nonempty set $A$.

  We claim $a(S)\subseteq h\bigl(b(S)\bigr)$. Indeed, let $i\in S$ and consider
  $c=b(i)\in b(S)$. The set $\{j\in S: b(j)=c\}$ is nonempty since it contains $i$, so
  $h(c)=a(i_c)$ with $i_c\in S$ and $b(i_c)=c=b(i)$; by the hypothesis on $a$ and $b$ this
  gives $a(i_c)=a(i)$, hence $h(c)=a(i)$ and $a(i)\in h\bigl(b(S)\bigr)$.

  The set $h\bigl(b(S)\bigr)$ is finite, being the image of the finite set $b(S)$. Therefore
  the inclusion just proved gives $|a(S)|\le\bigl|h\bigl(b(S)\bigr)\bigr|$, and since the
  cardinality of an image of a finite set does not exceed the cardinality of that set,
  $\bigl|h\bigl(b(S)\bigr)\bigr|\le|b(S)|$. Chaining the two inequalities yields
  $|a(S)|\le|b(S)|$. -/)
  (title := /-- Counting images that factor through another map -/)
  (latexEnv := "lemma")]
lemma ncard_image_le_of_factor {I A B : Type*} [Nonempty A] (S : Set I) (a : I → A) (b : I → B)
    (hfin : (b '' S).Finite)
    (hab : ∀ i ∈ S, ∀ j ∈ S, b i = b j → a i = a j) :
    Set.ncard (a '' S) ≤ Set.ncard (b '' S) := by
  classical
  set h : B → A := fun c =>
    if hc : ∃ i ∈ S, b i = c then a hc.choose else Classical.arbitrary A with hh
  have hsub : a '' S ⊆ h '' (b '' S) := by
    rintro y ⟨i, hiS, rfl⟩
    refine ⟨b i, ⟨i, hiS, rfl⟩, ?_⟩
    have hc : ∃ j ∈ S, b j = b i := ⟨i, hiS, rfl⟩
    rw [hh]
    simp only [dif_pos hc]
    exact hab _ hc.choose_spec.1 _ hiS hc.choose_spec.2
  calc Set.ncard (a '' S) ≤ Set.ncard (h '' (b '' S)) :=
        Set.ncard_le_ncard hsub (hfin.image h)
    _ ≤ Set.ncard (b '' S) := Set.ncard_image_le hfin

@[blueprint "lem:restriction-ncard-le-growth"
  (statement := /-- Let $Z$ be an infinite set, let $\mathcal{G}\subseteq\{0,1\}^{Z}$, let
  $P\subseteq Z$ be a finite subset and let $n\in\mathbb{N}$ with $|P|\le n$. Then the set
  $\mathcal{G}(P)$ of restrictions to $P$ of the members of $\mathcal{G}$ satisfies
  $|\mathcal{G}(P)|\le\Gamma_{\mathcal{G}}(n)$, where $\Gamma_{\mathcal{G}}$ is the growth
  function of \cref{def:growth-function}. -/)
  (proof := /-- Since $Z$ is infinite and $|P|\le n$, there is a finite subset $Q\subseteq Z$
  with $P\subseteq Q$ and $|Q|=n$.

  By \cref{def:growth-function}, $\Gamma_{\mathcal{G}}(n)$ is the supremum of the set $K$ of
  natural numbers of the form $|\mathcal{G}(t)|$ for finite subsets $t\subseteq Z$ with
  $|t|=n$. The set $K$ is bounded above by $2^{n}$, because any such $t$ satisfies
  $|\mathcal{G}(t)|\le 2^{|t|}=2^{n}$ by \cref{lem:restriction-ncard-le-two-pow}. As
  $|Q|=n$, the value $|\mathcal{G}(Q)|$ belongs to $K$, whence
  $|\mathcal{G}(Q)|\le\Gamma_{\mathcal{G}}(n)$.

  It remains to show $|\mathcal{G}(P)|\le|\mathcal{G}(Q)|$. Restricting a function on $Q$ to
  the subset $P$ defines a map $\{0,1\}^{Q}\to\{0,1\}^{P}$ which sends $\mathcal{G}(Q)$ onto
  $\mathcal{G}(P)$, so $\mathcal{G}(P)$ is the image of $\mathcal{G}(Q)$ under this map. Since
  $\mathcal{G}(Q)$ is finite, being a subset of the finite set $\{0,1\}^{Q}$, the cardinality
  of its image is at most $|\mathcal{G}(Q)|$. Combining the two displayed bounds gives
  $|\mathcal{G}(P)|\le\Gamma_{\mathcal{G}}(n)$. -/)
  (title := /-- Restrictions to a small set are counted by the growth function -/)
  (latexEnv := "lemma")]
lemma restriction_ncard_le_growth {Z : Type*} [Infinite Z] (G : Set (Z → Bool)) (P : Finset Z)
    (n : ℕ) (hP : P.card ≤ n) :
    Set.ncard ((fun (g : Z → Bool) (z : {x : Z // x ∈ P}) => g z.1) '' G) ≤
      growth_function G n := by
  classical
  obtain ⟨Q, hPQ, hQ⟩ := Infinite.exists_superset_card_eq P n hP
  have hb : BddAbove {k : ℕ | ∃ t : Finset Z, t.card = n ∧
      k = Set.ncard ((fun (g : Z → Bool) (z : {x : Z // x ∈ t}) => g z.1) '' G)} := by
    refine ⟨2 ^ n, ?_⟩
    rintro k ⟨t, htc, rfl⟩
    exact htc ▸ restriction_ncard_le_two_pow G t
  have hQle : Set.ncard ((fun (g : Z → Bool) (z : {x : Z // x ∈ Q}) => g z.1) '' G) ≤
      growth_function G n := le_csSup hb ⟨Q, hQ, rfl⟩
  refine le_trans ?_ hQle
  have himg : (fun (g : Z → Bool) (z : {x : Z // x ∈ P}) => g z.1) '' G
      = (fun (c : {x : Z // x ∈ Q} → Bool) (z : {x : Z // x ∈ P}) => c ⟨z.1, hPQ z.2⟩) ''
        ((fun (g : Z → Bool) (z : {x : Z // x ∈ Q}) => g z.1) '' G) := by
    rw [Set.image_image]
  rw [himg]
  exact Set.ncard_image_le (Set.toFinite _)

@[blueprint "lem:prefix-growth-bound"
  (statement := /-- Let $\mathcal{F}\subseteq\Sigma^{\Sigma^*}$ be a base class of next-token
  generators, let $T\in\mathbb{N}$ be a generation length and let $m\in\mathbb{N}$. Then the
  growth function of the $0$--$1$ loss class of the chain-of-thought class satisfies
  $$\Gamma_{\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T})}(m)\;\le\;\Gamma_{\mathcal{F}}(mT),$$
  where $\mathcal{F}_{\mathrm{CoT}}^{T}$ is as in \cref{def:cot-class},
  $\mathcal{L}^{01}$ is as in \cref{def:loss-class} and $\Gamma$ is the growth function of
  \cref{def:growth-function}. -/)
  (proof := /-- By \cref{def:growth-function} the quantity
  $\Gamma_{\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T})}(m)$ is the supremum of the set of
  natural numbers of the form
  $\bigl|\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T})(S)\bigr|$ for finite subsets
  $S\subseteq\Sigma^*\times\Sigma^*$ with $|S|=m$. Since every element of that set is bounded
  by $\Gamma_{\mathcal{F}}(mT)$ as soon as the bound below is established, it suffices to prove
  $\bigl|\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T})(S)\bigr|\le\Gamma_{\mathcal{F}}(mT)$
  for one arbitrary such $S$; the supremum of a set of naturals all of whose elements are at
  most a given bound is itself at most that bound.

  So fix a finite $S\subseteq\Sigma^*\times\Sigma^*$ with $|S|=m$ and form the finite set of
  prefixes
  $$P=\bigl\{\mathbf{u}[:|\mathbf{x}|+t]\;:\;(\mathbf{x},\mathbf{u})\in S,\ 0\le t<T\bigr\},$$
  that is, $P$ is the union over the pairs $(\mathbf{x},\mathbf{u})\in S$ of the images of
  $\{0,\dots,T-1\}$ under $t\mapsto\mathbf{u}[:|\mathbf{x}|+t]$.

  \emph{Step 1: $|P|\le mT$.} The cardinality of a union indexed by $S$ of sets each of
  cardinality at most $T$ is at most $|S|\cdot T$, and for each $(\mathbf{x},\mathbf{u})\in S$
  the corresponding set is the image of a set of cardinality $T$, hence has cardinality at most
  $T$. Since $|S|=m$, this gives $|P|\le mT$.

  \emph{Step 2: rewriting the restrictions.} By \cref{def:loss-class} and \cref{def:cot-class},
  the class $\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T})$ is the image of $\mathcal{F}$
  under $f\mapsto\ell_f$, where
  $\ell_f(\mathbf{x},\mathbf{u})=1$ if $f_{\mathrm{CoT}}^{T}(\mathbf{x})\neq\mathbf{u}$ and
  $\ell_f(\mathbf{x},\mathbf{u})=0$ otherwise, with $f_{\mathrm{CoT}}^{T}$ as in
  \cref{def:cot-trace}. Composing with restriction to $S$ identifies
  $\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T})(S)$ with the image of $\mathcal{F}$ under
  the map $a$ sending $f$ to the tuple $\bigl(\ell_f(\mathbf{x},\mathbf{u})\bigr)_
  {(\mathbf{x},\mathbf{u})\in S}$.

  \emph{Step 3: the loss pattern factors through the values on $P$.} Let $b$ send
  $f\in\mathcal{F}$ to its restriction $f|_{P}$, and let $f,g\in\mathcal{F}$ satisfy
  $f|_{P}=g|_{P}$, i.e. $f(\mathbf{y})=g(\mathbf{y})$ for every $\mathbf{y}\in P$. Fix
  $(\mathbf{x},\mathbf{u})\in S$. For every $t$ with $0\le t<T$ the string
  $\mathbf{u}[:|\mathbf{x}|+t]$ lies in $P$ by the definition of $P$, so $f$ and $g$ agree at
  it. Hence \cref{lem:cot-trace-eq-of-agree}, applied with the roles of the two generators in
  either order, shows that $f_{\mathrm{CoT}}^{T}(\mathbf{x})=\mathbf{u}$ holds if and only if
  $g_{\mathrm{CoT}}^{T}(\mathbf{x})=\mathbf{u}$ holds. Consequently
  $\ell_f(\mathbf{x},\mathbf{u})=\ell_g(\mathbf{x},\mathbf{u})$ for every
  $(\mathbf{x},\mathbf{u})\in S$, that is $a(f)=a(g)$.

  \emph{Step 4: conclusion.} The set $\mathcal{F}(P)=b(\mathcal{F})$ is finite, being a subset
  of the finite set $\{0,1\}^{P}$. Step 3 verifies the hypothesis of
  \cref{lem:ncard-image-le-of-factor} for the maps $a$ and $b$ on $\mathcal{F}$, so
  $$\bigl|\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T})(S)\bigr|
  =\bigl|a(\mathcal{F})\bigr|\;\le\;\bigl|\mathcal{F}(P)\bigr|.$$
  By Step 1 we have $|P|\le mT$, so \cref{lem:restriction-ncard-le-growth} applied to the
  infinite set $\Sigma^*$, the class $\mathcal{F}$, the finite set $P$ and the integer $mT$
  gives $\bigl|\mathcal{F}(P)\bigr|\le\Gamma_{\mathcal{F}}(mT)$. Chaining the two inequalities
  yields
  $\bigl|\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T})(S)\bigr|\le\Gamma_{\mathcal{F}}(mT)$,
  as required. -/)
  (title := /-- The loss class of a chain-of-thought class grows no faster than the base class
  on prefixes -/)
  (latexEnv := "lemma")]
lemma prefix_growth_bound (F : Set (List Bool → Bool)) (T m : ℕ) :
    growth_function (loss_class (cot_class F T)) m ≤ growth_function F (m * T) := by
  classical
  refine csSup_le' ?_
  rintro k ⟨s, hs, rfl⟩
  set P : Finset (List Bool) :=
    s.biUnion (fun p => (Finset.range T).image (fun t => p.2.take (p.1.length + t))) with hPdef
  have hPcard : P.card ≤ m * T := by
    have hbound := Finset.card_biUnion_le_card_mul s
      (fun p : List Bool × List Bool =>
        (Finset.range T).image (fun t => p.2.take (p.1.length + t))) T ?_
    · rw [hPdef, hs] at *
      exact hbound
    · intro p _
      exact le_trans Finset.card_image_le (by simp)
  have hmemP : ∀ z : {x : List Bool × List Bool // x ∈ s}, ∀ t, t < T →
      z.1.2.take (z.1.1.length + t) ∈ P := by
    intro z t ht
    exact Finset.mem_biUnion.mpr ⟨z.1, z.2, Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, rfl⟩⟩
  have himage : (fun (g : List Bool × List Bool → Bool)
        (z : {x : List Bool × List Bool // x ∈ s}) => g z.1) '' loss_class (cot_class F T)
      = (fun (f : List Bool → Bool) (z : {x : List Bool × List Bool // x ∈ s}) =>
          !decide (cot_trace f T z.1.1 = z.1.2)) '' F := by
    simp only [loss_class, cot_class, Set.image_image]
  rw [himage]
  refine le_trans (ncard_image_le_of_factor F _
    (fun (f : List Bool → Bool) (z : {x : List Bool // x ∈ P}) => f z.1)
    (Set.toFinite _) ?_) (restriction_ncard_le_growth F P (m * T) hPcard)
  intro f _ g _ hbeq
  have hagree : ∀ y ∈ P, f y = g y := fun y hy => congrFun hbeq ⟨y, hy⟩
  funext z
  have hiff : cot_trace f T z.1.1 = z.1.2 ↔ cot_trace g T z.1.1 = z.1.2 := by
    constructor
    · intro h1
      refine cot_trace_eq_of_agree f g T z.1.1 z.1.2 h1 ?_
      intro t ht
      exact (hagree _ (hmemP z t ht)).symm
    · intro h1
      refine cot_trace_eq_of_agree g f T z.1.1 z.1.2 h1 ?_
      intro t ht
      exact hagree _ (hmemP z t ht)
  simp [hiff]

@[blueprint "lem:vc-cot-loss-class"
  (statement := /-- Let $\Sigma=\{0,1\}$, let $\mathcal{F}\subseteq\Sigma^{\Sigma^*}$ be a base
  class, let $T\in\mathbb{N}$ with $T\ge 1$ and let $d\in\mathbb{N}$ with $d\ge 1$ and
  $\mathrm{VC}(\mathcal{F})\le d$. Then there exists an integer $D$ with
  $$\mathrm{VC}\bigl(\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T})\bigr)\le D
  \qquad\text{and}\qquad
  D\;\le\;3\,d\,\log_2\Bigl(\frac{2T}{\ln 2}\Bigr),$$
  where $\mathcal{F}_{\mathrm{CoT}}^{T}$ is as in \cref{def:cot-class}, $\mathcal{L}^{01}$ is as
  in \cref{def:loss-class} and $\mathrm{VC}$ is as in \cref{def:vc-dim}. -/)
  (proof := /-- By \cref{lem:prefix-growth-bound} we have
  $\Gamma_{\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T})}(n)\le\Gamma_{\mathcal{F}}(nT)$ for
  every $n\in\mathbb{N}$. Since $\mathrm{VC}(\mathcal{F})\le d$ and $d\ge 1$,
  \cref{lem:sauer-lemma} gives, for every $n\ge d$,
  $$\Gamma_{\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T})}(n)
  \;\le\;\Gamma_{\mathcal{F}}(nT)\;\le\;\Bigl(\frac{e\,nT}{d}\Bigr)^{d}.$$
  Hence any $n$ with $n\ge d$ and $n>d\log_2\bigl(e\,nT/d\bigr)$ satisfies
  $\Gamma_{\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T})}(n)\le 2^{d\log_2(enT/d)}<2^{n}$.

  Apply \cref{lem:technical-corollary} with $N=d$ and $M=T/d$; the hypotheses hold because
  $d\ge 1$, $T\ge 1$ give $M>0$ and $NM=T\ge 1$. It produces an integer $D$ with
  $d\le D$, $D\le 3d\log_2\bigl(2T/\ln 2\bigr)$ and
  $D>d\log_2\bigl(e\,D\,T/d\bigr)$.

  We claim $\Gamma_{\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T})}(n)<2^{n}$ for every
  $n>D$. Indeed, for such $n$ we have $n\ge d$ and, since
  $x\mapsto x-d\log_2(exT/d)$ is nondecreasing for $x\ge D\ge d$, also
  $n>d\log_2\bigl(e\,nT/d\bigr)$; the displayed estimate then gives the claim. By
  \cref{lem:vc-dim-le-of-growth-lt} applied with this $D$ we conclude
  $\mathrm{VC}\bigl(\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T})\bigr)\le D$, and $D$
  satisfies the required numerical bound. -/)
  (title := /-- VC dimension of the chain-of-thought loss class over a binary alphabet -/)
  (latexEnv := "lemma")]
lemma vc_cot_loss_class (F : Set (List Bool → Bool)) (T d : ℕ) (hT : 1 ≤ T) (hd : 1 ≤ d)
    (hvc : vc_dim F ≤ (d : ℕ∞)) :
    ∃ D : ℕ, vc_dim (loss_class (cot_class F T)) ≤ (D : ℕ∞) ∧
      (D : ℝ) ≤ 3 * (d : ℝ) * Real.logb 2 (2 * (T : ℝ) / Real.log 2) := by
  have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hTpos : (0:ℝ) < (T:ℝ) := by exact_mod_cast hT
  have hdne : (d:ℝ) ≠ 0 := ne_of_gt hdpos
  have hTne : (T:ℝ) ≠ 0 := ne_of_gt hTpos
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hdM : (d:ℝ) * ((T:ℝ)/(d:ℝ)) = (T:ℝ) := by
    rw [mul_comm]; exact div_mul_cancel₀ (T:ℝ) hdne
  have hMpos : (0:ℝ) < (T:ℝ)/(d:ℝ) := div_pos hTpos hdpos
  have hNM : (1:ℝ) ≤ (d:ℝ) * ((T:ℝ)/(d:ℝ)) := by rw [hdM]; exact_mod_cast hT
  obtain ⟨m, hm_ge, hm_bound, hm_third⟩ :=
    technical_corollary d ((T:ℝ)/(d:ℝ)) hd hMpos hNM
  have h2dM : 2 * (d:ℝ) * ((T:ℝ)/(d:ℝ)) = 2 * (T:ℝ) := by rw [mul_assoc, hdM]
  rw [h2dM] at hm_bound
  refine ⟨m, ?_, hm_bound⟩
  have hmpos_nat : 0 < m := by omega
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hmpos_nat
  have hmne : (m:ℝ) ≠ 0 := ne_of_gt hmpos
  have hmge_real : (d:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm_ge
  have hlogA : Real.log (Real.exp 1 * ↑m * ((T:ℝ)/(d:ℝ)))
      = 1 + Real.log m + Real.log T - Real.log d := by
    rw [Real.log_mul (mul_ne_zero (Real.exp_ne_zero 1) hmne) (div_ne_zero hTne hdne),
        Real.log_mul (Real.exp_ne_zero 1) hmne,
        Real.log_div hTne hdne, Real.log_exp]
    ring
  have hthird : (d:ℝ) * (1 + Real.log m + Real.log T - Real.log d) < (m:ℝ) * Real.log 2 := by
    have h := hm_third
    rw [← Real.log_div_log, ← mul_div_assoc, div_lt_iff₀ hlog2] at h
    rwa [hlogA] at h
  have hArg : (0:ℝ) ≤ Real.log m + Real.log T - Real.log d := by
    have h1 : Real.log d ≤ Real.log m := Real.log_le_log hdpos hmge_real
    have h2 : (0:ℝ) ≤ Real.log T := Real.log_nonneg (by exact_mod_cast hT)
    linarith
  have h1leB : (1:ℝ) ≤ 1 + Real.log m + Real.log T - Real.log d := by linarith [hArg]
  have hdle2 : (d:ℝ) ≤ (d:ℝ) * (1 + Real.log m + Real.log T - Real.log d) :=
    le_mul_of_one_le_right (le_of_lt hdpos) h1leB
  have hdlt : (d:ℝ) < (m:ℝ) * Real.log 2 := lt_of_le_of_lt hdle2 hthird
  apply vc_dim_le_of_growth_lt (loss_class (cot_class F T)) m
  intro n hn
  have hnpos : 0 < n := by omega
  have hnpos_real : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
  have hnne : (n:ℝ) ≠ 0 := ne_of_gt hnpos_real
  have hn_real : (m:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hnTpos : 0 < n * T := Nat.mul_pos hnpos hT
  have hnTpos_real : (0:ℝ) < ↑(n*T) := by exact_mod_cast hnTpos
  have hdle : d ≤ n * T := by
    have h1 : d ≤ n := by omega
    have h2 : n ≤ n * T := by
      calc n = n * 1 := (mul_one n).symm
        _ ≤ n * T := by gcongr
    omega
  have hpref : growth_function (loss_class (cot_class F T)) n ≤ growth_function F (n * T) :=
    prefix_growth_bound F T n
  have hsauer : (growth_function F (n*T) : ℝ) ≤ (Real.exp 1 * ↑(n*T) / ↑d) ^ d :=
    sauer_lemma F d (n*T) hd hvc hdle
  have hlogB : Real.log (Real.exp 1 * ↑(n*T) / ↑d)
      = 1 + Real.log n + Real.log T - Real.log d := by
    rw [Nat.cast_mul,
        Real.log_div (mul_ne_zero (Real.exp_ne_zero 1) (mul_ne_zero hnne hTne)) hdne,
        Real.log_mul (Real.exp_ne_zero 1) (mul_ne_zero hnne hTne),
        Real.log_mul hnne hTne, Real.log_exp]
    ring
  have hlogdiv : Real.log ((n:ℝ)/(m:ℝ)) = Real.log n - Real.log m :=
    Real.log_div hnne hmne
  have hlogsub : Real.log ((n:ℝ)/(m:ℝ)) ≤ (n:ℝ)/(m:ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hcancel : (n:ℝ)/(m:ℝ) * (m:ℝ) = (n:ℝ) := div_mul_cancel₀ (n:ℝ) hmne
  have hLmul : (m:ℝ) * (Real.log n - Real.log m) ≤ (n:ℝ) - (m:ℝ) := by
    have h0 : (m:ℝ) * Real.log ((n:ℝ)/(m:ℝ)) ≤ (m:ℝ) * ((n:ℝ)/(m:ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hlogsub (le_of_lt hmpos)
    rw [hlogdiv] at h0
    nlinarith [h0, hcancel]
  have hlogmn_nonneg : (0:ℝ) ≤ Real.log n - Real.log m := by
    have hle : Real.log m ≤ Real.log n := Real.log_le_log hmpos (le_of_lt hn_real)
    linarith
  have step1 : (d:ℝ) * (Real.log n - Real.log m)
      ≤ (m:ℝ) * Real.log 2 * (Real.log n - Real.log m) :=
    mul_le_mul_of_nonneg_right (le_of_lt hdlt) hlogmn_nonneg
  have step2 : (m:ℝ) * Real.log 2 * (Real.log n - Real.log m)
      ≤ Real.log 2 * ((n:ℝ) - (m:ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hLmul (le_of_lt hlog2)
    calc (m:ℝ) * Real.log 2 * (Real.log n - Real.log m)
        = Real.log 2 * ((m:ℝ) * (Real.log n - Real.log m)) := by ring
      _ ≤ Real.log 2 * ((n:ℝ) - (m:ℝ)) := h
  have step3 : (d:ℝ) * (Real.log n - Real.log m) ≤ Real.log 2 * ((n:ℝ) - (m:ℝ)) :=
    le_trans step1 step2
  have hexpand : (d:ℝ) * (1 + Real.log n + Real.log T - Real.log d)
      = (d:ℝ) * (1 + Real.log m + Real.log T - Real.log d)
        + (d:ℝ) * (Real.log n - Real.log m) := by ring
  have hbasepos : (0:ℝ) < Real.exp 1 * ↑(n*T) / ↑d :=
    div_pos (mul_pos (Real.exp_pos 1) hnTpos_real) hdpos
  have hkey : (Real.exp 1 * ↑(n*T) / ↑d) ^ d < (2:ℝ) ^ n := by
    have hlog : Real.log ((Real.exp 1 * ↑(n*T) / ↑d) ^ d) < Real.log ((2:ℝ) ^ n) := by
      rw [Real.log_pow, Real.log_pow, hlogB, hexpand]
      nlinarith [hthird, step3]
    have h2 := Real.exp_lt_exp.mpr hlog
    rwa [Real.exp_log (pow_pos hbasepos d), Real.exp_log (pow_pos (by norm_num) n)] at h2
  have hgrowth_real : (growth_function (loss_class (cot_class F T)) n : ℝ) < (2:ℝ)^n := by
    have h1 : (growth_function (loss_class (cot_class F T)) n : ℝ)
        ≤ (growth_function F (n*T) : ℝ) := by exact_mod_cast hpref
    linarith [h1, hsauer, hkey]
  exact_mod_cast hgrowth_real

@[blueprint "lem:consistent-bad-event-iid-support"
  (statement := /-- Let $X$ be a set, let $D$ be a probability mass function on $X$, let
  $m\in\mathbb{N}$, and let $S\in X^{\mathrm{Fin}\,m}$ belong to the support of the
  $m$-fold i.i.d. law $D^m$. Then $S_i$ belongs to the support of $D$ for every
  $i\in\mathrm{Fin}\,m$. -/)
  (proof := /-- We argue by induction on $m$ using \cref{def:iid-sample}. The assertion is
  vacuous for $m=0$. For $m+1$, membership in the support of the two-stage law gives a first
  coordinate $x$ in the support of $D$ and a tail sample in the support of $D^m$. The zeroth
  coordinate is therefore in the support of $D$, while every successor coordinate is handled
  by the induction hypothesis. -/)
  (title := /-- Coordinates of a supported i.i.d. sample are supported -/)
  (latexEnv := "lemma")]
lemma consistent_bad_event_iid_support {X : Type*} (D : PMF X) (m : ℕ)
    {S : Fin m → X} (hS : S ∈ (iid_sample D m).support) (i : Fin m) :
    S i ∈ D.support := by
  induction m with
  | zero =>
      exact i.elim0
  | succ n ih =>
      simp only [iid_sample, PMF.support_bind, PMF.support_map, Set.mem_iUnion,
        Set.mem_image] at hS
      obtain ⟨x, hx, s, hs, rfl⟩ := hS
      refine Fin.cases hx (fun j => ih hs j) i

@[blueprint "lem:consistent-bad-event-iid-apply"
  (statement := /-- Let $X$ be a set, let $D$ be a probability mass function on $X$, let
  $m\in\mathbb{N}$, and let $S\in X^{\mathrm{Fin}\,m}$. Then the mass assigned to $S$ by
  the $m$-fold i.i.d. law is
  $$D^m(S)=\prod_{i\in\mathrm{Fin}\,m}D(S_i).$$ -/)
  (proof := /-- We use induction on $m$ and the recursive definition
  \cref{def:iid-sample}. For $m=0$, both sides equal one. At $m+1$, the outer two-stage sum
  has only the term $x=S_0$, and the push-forward sum for its tail has only the term
  $S\mathbin{\upharpoonright}\{1,\ldots,m\}$. The induction hypothesis identifies the
  latter mass with the product over the tail coordinates, and adjoining the zeroth factor
  gives the required product. -/)
  (title := /-- Point masses of an i.i.d. sample are coordinate products -/)
  (latexEnv := "lemma")]
lemma consistent_bad_event_iid_apply {X : Type*} (D : PMF X) :
    ∀ (m : ℕ) (S : Fin m → X), iid_sample D m S = ∏ i, D (S i) := by
  intro m
  induction m with
  | zero =>
      intro S
      have hS : S = fun i => i.elim0 := Subsingleton.elim _ _
      subst S
      simp [iid_sample, PMF.pure_apply]
  | succ n ih =>
      intro S
      rw [iid_sample, PMF.bind_apply, tsum_eq_single (S 0)]
      · rw [PMF.map_apply, tsum_eq_single (Fin.tail S)]
        · simp only [if_pos (Fin.cons_self_tail S).symm, ih, Fin.prod_univ_succ]
          rfl
        · intro s hs
          rw [if_neg]
          intro hEq
          apply hs
          funext i
          exact (congrFun hEq i.succ).symm
      · intro x hx
        rw [PMF.map_apply]
        apply mul_eq_zero_of_right
        rw [ENNReal.tsum_eq_zero]
        intro s
        split_ifs with hEq
        · exfalso
          apply hx
          simpa using (congrFun hEq 0).symm
        · rfl

@[blueprint "lem:consistent-bad-event-iid-measure"
  (statement := /-- Let $X$ be a countable measurable space in which singletons are measurable,
  let $D$ be a probability mass function on $X$, and let $m\in\mathbb{N}$. The measure
  associated with the recursively defined i.i.d. law $D^m$ is the finite product of $m$
  copies of the measure associated with $D$. -/)
  (proof := /-- Measures on a countable space agree if they agree on every singleton. For a
  tuple $S$, \cref{lem:consistent-bad-event-iid-apply} identifies its mass under $D^m$ with
  $\prod_i D(S_i)$. The finite product measure assigns the same mass to the singleton
  $\{S\}$, since its singleton formula is the product of the coordinate singleton masses.
  Hence the two measures coincide. -/)
  (title := /-- The recursive i.i.d. PMF induces the finite product measure -/)
  (latexEnv := "lemma")]
lemma consistent_bad_event_iid_measure {X : Type*} [Countable X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (D : PMF X) (m : ℕ) :
    (iid_sample D m).toMeasure = MeasureTheory.Measure.pi (fun _ : Fin m => D.toMeasure) := by
  apply MeasureTheory.Measure.ext_of_singleton
  intro S
  rw [PMF.toMeasure_apply_singleton (iid_sample D m) S (measurableSet_singleton S),
    MeasureTheory.Measure.pi_singleton, consistent_bad_event_iid_apply]
  apply Finset.prod_congr rfl
  intro i hi
  exact (PMF.toMeasure_apply_singleton D (S i) (measurableSet_singleton (S i))).symm

@[blueprint "lem:consistent-bad-event-ghost-lower-tail"
  (statement := /-- Let $X$ be countable, let $D$ be a probability mass function on $X$, let
  $E\subseteq X$, let $m\in\mathbb{N}$, and let $\varepsilon>0$. Put
  $p=D(E)$. If $p>\varepsilon$ and $m\varepsilon\ge8$, then an i.i.d. sample
  $S\sim D^m$ contains more than $m\varepsilon/2$ members of $E$ with probability at least
  $1/2$. -/)
  (proof := /-- Give $X$ the discrete measurable structure. By
  \cref{lem:consistent-bad-event-iid-measure}, the law of the sample is the finite product of
  $m$ copies of the measure induced by $D$. Let $N$ be the sum of the $m$ indicator variables
  of $E$. Each indicator has mean $p$ and variance at most $p$; independence of the coordinate
  projections therefore gives
  $\mathbb{E}N=mp$ and $\operatorname{Var}(N)\le mp$.

  Since $p>\varepsilon$, the event $N\le m\varepsilon/2$ is contained in
  $\{|N-mp|\ge mp/2\}$. Chebyshev's inequality and $mp>m\varepsilon\ge8$ give
  $$
  \mathbb{P}\{N\le m\varepsilon/2\}
  \le \frac{mp}{(mp/2)^2}=\frac4{mp}\le\frac12.
  $$
  Taking complements proves the claim. -/)
  (title := /-- A ghost sample detects a bad hypothesis with probability one half -/)
  (latexEnv := "lemma")]
lemma consistent_bad_event_ghost_lower_tail {X : Type*} [Countable X]
    (D : PMF X) (E : Set X) (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hp : ε < (D.toOuterMeasure E).toReal) (hmε : 8 ≤ (m : ℝ) * ε) :
    (1 : ENNReal) / 2 ≤
      (iid_sample D m).toOuterMeasure
        {S : Fin m → X |
          (m : ℝ) * ε / 2 <
            ∑ i, E.indicator (fun _ => (1 : ℝ)) (S i)} := by
  letI : MeasurableSpace X := ⊤
  let μ : MeasureTheory.Measure X := D.toMeasure
  let ν : MeasureTheory.Measure (Fin m → X) :=
    MeasureTheory.Measure.pi (fun _ : Fin m => μ)
  let e : X → ℝ := E.indicator 1
  let N : (Fin m → X) → ℝ := fun S => ∑ i, e (S i)
  let p : ℝ := (D.toOuterMeasure E).toReal
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  have hμE : μ.real E = p := by
    rw [MeasureTheory.measureReal_def,
      PMF.toMeasure_apply_eq_toOuterMeasure_apply D hE]
  have he_mem : MeasureTheory.MemLp e 2 μ := by
    exact MeasureTheory.memLp_indicator_const 2 hE 1 (Or.inr (by simp [μ]))
  have he_int : MeasureTheory.Integrable e μ := he_mem.integrable (by norm_num)
  have he_mean : ∫ x, e x ∂μ = p := by
    rw [show e = E.indicator (1 : X → ℝ) from rfl,
      MeasureTheory.integral_indicator_one hE, hμE]
  have he_sq : ∫ x, (e x) ^ 2 ∂μ = p := by
    calc
      ∫ x, (e x) ^ 2 ∂μ = ∫ x, e x ∂μ := by
        congr 1
        funext x
        simp [e, Set.indicator]
      _ = p := he_mean
  have he_var : ProbabilityTheory.variance e μ ≤ p := by
    calc
      ProbabilityTheory.variance e μ ≤ ∫ x, (e x) ^ 2 ∂μ :=
        ProbabilityTheory.variance_le_expectation_sq he_mem.1
      _ = p := he_sq
  have hcoord_mem : ∀ i : Fin m,
      MeasureTheory.MemLp (fun S : Fin m → X => e (S i)) 2 ν := by
    intro i
    exact he_mem.comp_measurePreserving
      (MeasureTheory.measurePreserving_eval (fun _ : Fin m => μ) i)
  have hcoord_mean : ∀ i : Fin m, ∫ S, e (S i) ∂ν = p := by
    intro i
    have hmp := MeasureTheory.measurePreserving_eval (fun _ : Fin m => μ) i
    have he_map : MeasureTheory.AEStronglyMeasurable e
        (MeasureTheory.Measure.map (Function.eval i) ν) := by
      rw [show ν = MeasureTheory.Measure.pi (fun _ : Fin m => μ) from rfl, hmp.map_eq]
      exact he_int.aestronglyMeasurable
    calc
      ∫ S, e (S i) ∂ν =
          ∫ x, e x ∂(MeasureTheory.Measure.map (Function.eval i) ν) :=
        (MeasureTheory.integral_map hmp.measurable.aemeasurable he_map).symm
      _ = ∫ x, e x ∂μ := by
        rw [show ν = MeasureTheory.Measure.pi (fun _ : Fin m => μ) from rfl, hmp.map_eq]
      _ = p := he_mean
  have hN_mem : MeasureTheory.MemLp N 2 ν := by
    simpa only [N] using
      (MeasureTheory.memLp_finsetSum (Finset.univ : Finset (Fin m))
        (fun i hi => hcoord_mem i))
  have hN_mean : ∫ S, N S ∂ν = (m : ℝ) * p := by
    rw [show N = fun S : Fin m → X => ∑ i, e (S i) from rfl]
    rw [MeasureTheory.integral_finsetSum]
    · simp only [hcoord_mean, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
    · intro i hi
      exact (hcoord_mem i).integrable (by norm_num)
  have hN_var : ProbabilityTheory.variance N ν ≤ (m : ℝ) * p := by
    calc
      ProbabilityTheory.variance N ν =
          ProbabilityTheory.variance (∑ i, fun S : Fin m → X => e (S i))
            (MeasureTheory.Measure.pi (fun _ : Fin m => μ)) := by
              congr 2
              funext S
              simp [N]
      _ = ∑ i : Fin m, ProbabilityTheory.variance e μ :=
        ProbabilityTheory.variance_sum_pi (fun _ => he_mem)
      _ ≤ ∑ _i : Fin m, p := Finset.sum_le_sum (fun i hi => he_var)
      _ = (m : ℝ) * p := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hp0 : 0 < p := lt_trans hε hp
  have hm0 : 0 < (m : ℝ) := by
    nlinarith
  have hmp8 : 8 < (m : ℝ) * p := by
    nlinarith
  have hc : 0 < (m : ℝ) * p / 2 := by positivity
  have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq hN_mem hc
  rw [hN_mean] at hcheb
  have hratio : ProbabilityTheory.variance N ν / ((m : ℝ) * p / 2) ^ 2 ≤ 1 / 2 := by
    calc
      ProbabilityTheory.variance N ν / ((m : ℝ) * p / 2) ^ 2
          ≤ ((m : ℝ) * p) / ((m : ℝ) * p / 2) ^ 2 := by
            gcongr
      _ ≤ 1 / 2 := by
        field_simp
        nlinarith
  have hdev : ν {S | (m : ℝ) * p / 2 ≤ |N S - (m : ℝ) * p|} ≤
      (1 : ENNReal) / 2 := by
    calc
      ν {S | (m : ℝ) * p / 2 ≤ |N S - (m : ℝ) * p|}
          ≤ ENNReal.ofReal
              (ProbabilityTheory.variance N ν / ((m : ℝ) * p / 2) ^ 2) := hcheb
      _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hratio
      _ = (1 : ENNReal) / 2 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
        congr 1
        norm_num
  have hlow_sub :
      {S : Fin m → X | N S ≤ (m : ℝ) * ε / 2} ⊆
        {S | (m : ℝ) * p / 2 ≤ |N S - (m : ℝ) * p|} := by
    intro S hS
    simp only [Set.mem_setOf_eq] at hS ⊢
    rw [abs_of_nonpos]
    · nlinarith
    · nlinarith
  have hlow : ν {S : Fin m → X | N S ≤ (m : ℝ) * ε / 2} ≤
      (1 : ENNReal) / 2 :=
    le_trans (MeasureTheory.measure_mono hlow_sub) hdev
  have he_meas : Measurable e := by
    exact measurable_const.indicator hE
  have hN_meas : Measurable N := by
    dsimp only [N]
    fun_prop
  have hhigh_meas : MeasurableSet {S : Fin m → X | (m : ℝ) * ε / 2 < N S} := by
    exact measurableSet_lt measurable_const hN_meas
  have hhigh : (1 : ENNReal) / 2 ≤
      ν {S : Fin m → X | (m : ℝ) * ε / 2 < N S} := by
    have hlow_meas : MeasurableSet {S : Fin m → X | N S ≤ (m : ℝ) * ε / 2} :=
      measurableSet_le hN_meas measurable_const
    have hcomp := MeasureTheory.measure_compl (μ := ν) hlow_meas (by simp)
    have hcompl :
        {S : Fin m → X | N S ≤ (m : ℝ) * ε / 2}ᶜ =
          {S | (m : ℝ) * ε / 2 < N S} := by ext S; simp
    rw [hcompl, MeasureTheory.measure_univ] at hcomp
    rw [hcomp]
    apply ENNReal.le_sub_of_add_le_left (by simp)
    calc
      ν {S : Fin m → X | N S ≤ (m : ℝ) * ε / 2} + (1 : ENNReal) / 2
          ≤ (1 : ENNReal) / 2 + (1 : ENNReal) / 2 := by
            simpa [add_comm] using add_le_add_right hlow ((1 : ENNReal) / 2)
      _ = 1 := by simpa [div_eq_mul_inv] using ENNReal.inv_two_add_inv_two
  change (1 : ENNReal) / 2 ≤
    (iid_sample D m).toOuterMeasure {S : Fin m → X | (m : ℝ) * ε / 2 < N S}
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply (iid_sample D m) hhigh_meas,
    consistent_bad_event_iid_measure D m]
  exact hhigh

@[blueprint "lem:consistent-bad-event-ghost-symmetrization"
  (statement := /-- Let $X$ and $Y$ be countable sets, with decidable equality on $Y$, let
  $\mathcal H\subseteq Y^X$, let $m\in\mathbb N$, and let $\varepsilon>0$ satisfy
  $m\varepsilon\ge8$. Let $A$ be consistent for $\mathcal H$ and let $D$ be realizable by
  $\mathcal H$. If $S,S'\sim D^m$ are independent, then the probability that
  $L_D(A(S))>\varepsilon$ is at most twice the probability that there is an
  $h\in\mathcal H$ which fits every coordinate of $S$ and makes more than
  $m\varepsilon/2$ errors on $S'$. -/)
  (proof := /-- Fix a bad sample $S$ in the support of $D^m$. Realizability and
  \cref{lem:consistent-bad-event-iid-support} show that the realizing hypothesis fits $S$;
  consistency therefore gives $A(S)\in\mathcal H$ and shows that $A(S)$ fits $S$. Apply
  \cref{lem:consistent-bad-event-ghost-lower-tail} to the error set of $A(S)$. Since its
  $D$-mass is greater than $\varepsilon$, an independent sample $S'$ contains more than
  $m\varepsilon/2$ errors with probability at least $1/2$. Thus the asserted two-sample event
  has conditional probability at least $1/2$ above each bad supported $S$.

  Expand both probabilities as sums of their point masses. Unsupported samples contribute
  zero. For every bad supported sample, the preceding conditional estimate gives
  $D^m(S)\le2D^m(S)\mathbb P_{S'}(W(S,S'))$. Summing this pointwise inequality proves the
  claim. -/)
  (title := /-- Ghost-sample symmetrization for a consistent rule -/)
  (latexEnv := "lemma")]
lemma consistent_bad_event_ghost_symmetrization {X Y : Type*} [Countable X] [Countable Y]
    [DecidableEq Y] (H : Set (X → Y)) (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hmε : 8 ≤ (m : ℝ) * ε) (A : (Fin m → X × Y) → (X → Y))
    (hA : supervised_consistent H m A) (D : PMF (X × Y)) (hD : realizable_dist H D) :
    (iid_sample D m).toOuterMeasure
        {S : Fin m → X × Y |
          ENNReal.ofReal ε < supervised_error D (A S)} ≤
      2 * ((iid_sample D m).bind fun S =>
        (iid_sample D m).map fun S' => (S, S')).toOuterMeasure
        {SS : (Fin m → X × Y) × (Fin m → X × Y) |
          ∃ h ∈ H, (∀ i, h (SS.1 i).1 = (SS.1 i).2) ∧
            (m : ℝ) * ε / 2 <
              ∑ i, ({z : X × Y | h z.1 ≠ z.2}.indicator
                (fun _ => (1 : ℝ))) (SS.2 i)} := by
  classical
  let Q : PMF (Fin m → X × Y) := iid_sample D m
  let B : Set (Fin m → X × Y) :=
    {S | ENNReal.ofReal ε < supervised_error D (A S)}
  let W : Set ((Fin m → X × Y) × (Fin m → X × Y)) :=
    {SS | ∃ h ∈ H, (∀ i, h (SS.1 i).1 = (SS.1 i).2) ∧
      (m : ℝ) * ε / 2 <
        ∑ i, ({z : X × Y | h z.1 ≠ z.2}.indicator
          (fun _ => (1 : ℝ))) (SS.2 i)}
  obtain ⟨hstar, hhstar, hstar_fit⟩ := hD
  have hJ :
      (Q.bind fun S => Q.map fun S' => (S, S')).toOuterMeasure W =
        ∑' S, Q S * Q.toOuterMeasure {S' | (S, S') ∈ W} := by
    rw [PMF.toOuterMeasure_bind_apply]
    apply tsum_congr
    intro S
    rw [PMF.toOuterMeasure_map_apply]
    rfl
  change Q.toOuterMeasure B ≤
    2 * (Q.bind fun S => Q.map fun S' => (S, S')).toOuterMeasure W
  rw [PMF.toOuterMeasure_apply, hJ, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro S
  by_cases hSB : S ∈ B
  · by_cases hSQ : S ∈ Q.support
    · have hfitstar : ∀ i, hstar (S i).1 = (S i).2 := by
        intro i
        exact hstar_fit (S i)
          (consistent_bad_event_iid_support D m hSQ i)
      have hout := hA S ⟨hstar, hhstar, hfitstar⟩
      let E : Set (X × Y) := {z | A S z.1 ≠ z.2}
      have herr_le_one : supervised_error D (A S) ≤ 1 := by
        calc
          supervised_error D (A S) ≤ D.toOuterMeasure Set.univ :=
            D.toOuterMeasure_mono (Set.subset_univ _)
          _ = 1 := by
            rw [PMF.toOuterMeasure_apply]
            simpa [Set.indicator] using D.tsum_coe
      have herr_top : supervised_error D (A S) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top herr_le_one
      have hp : ε < (D.toOuterMeasure E).toReal := by
        apply (ENNReal.ofReal_lt_iff_lt_toReal hε.le herr_top).mp
        exact hSB
      have hghost := consistent_bad_event_ghost_lower_tail D E m ε hε hp hmε
      have hsub :
          {S' : Fin m → X × Y |
            (m : ℝ) * ε / 2 <
              ∑ i, E.indicator (fun _ => (1 : ℝ)) (S' i)} ⊆
            {S' | (S, S') ∈ W} := by
        intro S' hS'
        refine ⟨A S, hout.1, hout.2, ?_⟩
        exact hS'
      have hcond : (1 : ENNReal) / 2 ≤ Q.toOuterMeasure {S' | (S, S') ∈ W} :=
        le_trans hghost (Q.toOuterMeasure_mono (fun S' hS' => hsub hS'.1))
      rw [Set.indicator_of_mem hSB]
      calc
        Q S = Q S * 1 := by rw [mul_one]
        _ = Q S * (2 * ((1 : ENNReal) / 2)) := by
          congr 1
          symm
          simpa [div_eq_mul_inv, two_mul] using ENNReal.inv_two_add_inv_two
        _ ≤ Q S * (2 * Q.toOuterMeasure {S' | (S, S') ∈ W}) := by
          gcongr
        _ = 2 * (Q S * Q.toOuterMeasure {S' | (S, S') ∈ W}) := by
          ac_rfl
    · have hQzero : Q S = 0 := by
        simpa [PMF.mem_support_iff] using hSQ
      simp [Set.indicator_of_mem hSB, hQzero]
  · simp [Set.indicator, hSB]

@[blueprint "lem:consistent-bad-event-independent-pair-apply"
  (statement := /-- Let $P$ be a probability mass function on a set $U$. The law obtained by
  drawing $u\sim P$, then drawing $v\sim P$ independently, and returning $(u,v)$ assigns the
  point $(u,v)$ the mass $P(u)P(v)$. -/)
  (proof := /-- Expand the two-stage draw as an outer sum over its first coordinate and the
  push-forward as an inner sum over its second coordinate. In the outer sum only the prescribed
  first coordinate can produce $(u,v)$, and in the inner sum only the prescribed second
  coordinate can do so. The two surviving factors are $P(u)$ and $P(v)$. -/)
  (title := /-- Point masses of two independent draws multiply -/)
  (latexEnv := "lemma")]
lemma consistent_bad_event_independent_pair_apply {U : Type*} (P : PMF U) (u v : U) :
    (P.bind fun x => P.map fun y => (x, y)) (u, v) = P u * P v := by
  rw [PMF.bind_apply, tsum_eq_single u]
  · rw [PMF.map_apply, tsum_eq_single v]
    · simp
    · intro y hy
      rw [if_neg]
      intro h
      apply hy
      exact (Prod.mk.inj h |>.2).symm
  · intro x hx
    rw [PMF.map_apply]
    apply mul_eq_zero_of_right
    rw [ENNReal.tsum_eq_zero]
    intro y
    rw [if_neg]
    intro h
    apply hx
    exact (Prod.mk.inj h |>.1).symm

@[blueprint "lem:consistent-bad-event-swap-count"
  (statement := /-- Let $a,b\in\{0,1\}^m$ and let $\varepsilon>0$. Among the
  $2^m$ coordinatewise swaps of the pairs $(a_i,b_i)$, the proportion for which every first
  coordinate is zero and more than $m\varepsilon/2$ second coordinates are one is at most
  $\exp(-m\varepsilon/4)$. -/)
  (proof := /-- Let $I$ be the set of coordinates at which at least one of $a_i,b_i$ is one.
  If no swap has the asserted property there is nothing to prove. Otherwise, a successful swap
  shows that no coordinate has $a_i=b_i=1$, and its number of ones in the second component is
  exactly $|I|$; hence $|I|>m\varepsilon/2$. Moreover, at every coordinate in $I$ a successful
  swap is forced, while its values on the complement of $I$ are arbitrary. Restriction to the
  complement is therefore injective on the successful swaps, so their number is at most
  $2^{m-|I|}$ and their proportion is at most $2^{-|I|}$.

  Applying $\log 2\ge1/2$ and $|I|>m\varepsilon/2$ gives
  $|I|\log2>m\varepsilon/4$. Monotonicity of the exponential consequently yields
  $2^{-|I|}=\exp(-|I|\log2)\le\exp(-m\varepsilon/4)$, as required. -/)
  (title := /-- Exponential bound for favorable coordinate swaps -/)
  (latexEnv := "lemma")]
lemma consistent_bad_event_swap_count (m : ℕ) (ε : ℝ) (a b : Fin m → Bool) :
    let good := (Finset.univ : Finset (Fin m → Bool)).filter fun σ =>
      (∀ i, (if σ i then b i else a i) = false) ∧
        (m : ℝ) * ε / 2 <
          ∑ i, if (if σ i then a i else b i) = true then (1 : ℝ) else 0
    ((good.card : ℕ) : ℝ) / (2 : ℝ) ^ m ≤ Real.exp (-((m : ℝ) * ε / 4)) := by
  classical
  dsimp only
  let active : Finset (Fin m) := Finset.univ.filter fun i => a i || b i
  let good : Finset (Fin m → Bool) := Finset.univ.filter fun σ =>
    (∀ i, (if σ i then b i else a i) = false) ∧
      (m : ℝ) * ε / 2 <
        ∑ i, if (if σ i then a i else b i) = true then (1 : ℝ) else 0
  change ((good.card : ℕ) : ℝ) / (2 : ℝ) ^ m ≤ _
  by_cases hgood : good.Nonempty
  · obtain ⟨σ, hσ⟩ := hgood
    have hσ' := (Finset.mem_filter.mp hσ).2
    have hsecond_active : ∀ i,
        (if σ i then a i else b i) = true ↔ i ∈ active := by
      intro i
      have hfirst := hσ'.1 i
      simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
      cases hai : a i <;> cases hbi : b i <;> cases hsi : σ i <;>
        simp_all
    have hcount_eq :
        (∑ i, if (if σ i then a i else b i) = true then (1 : ℝ) else 0) =
          (active.card : ℝ) := by
      calc
        (∑ i, if (if σ i then a i else b i) = true then (1 : ℝ) else 0) =
            ∑ i, if i ∈ active then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [if_congr (hsecond_active i) rfl rfl]
        _ = (active.card : ℝ) := by simp
    have hactive_large : (m : ℝ) * ε / 2 < (active.card : ℝ) := by
      calc
        (m : ℝ) * ε / 2 <
            ∑ i, if (if σ i then a i else b i) = true then (1 : ℝ) else 0 := hσ'.2
        _ = (active.card : ℝ) := hcount_eq
    have hforced : ∀ τ ∈ good, ∀ i ∈ active, τ i = a i := by
      intro τ hτ i hi
      have hτfirst := (Finset.mem_filter.mp hτ).2.1 i
      simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      cases hai : a i <;> cases hbi : b i <;> cases hti : τ i <;>
        simp_all
    let restrict : {τ // τ ∈ good} → ({i // i ∉ active} → Bool) :=
      fun τ i => τ.1 i.1
    have hrestrict : Function.Injective restrict := by
      intro s t hst
      apply Subtype.ext
      funext i
      by_cases hi : i ∈ active
      · rw [hforced s.1 s.2 i hi, hforced t.1 t.2 i hi]
      · exact congrFun hst ⟨i, hi⟩
    have hcard :
        good.card ≤ 2 ^ (m - active.card) := by
      have hc := Fintype.card_le_of_injective restrict hrestrict
      simpa [restrict, Fintype.card_congr (Equiv.refl Bool),
        Fintype.card_subtype_compl, Fintype.card_fin] using hc
    have hactive_le : active.card ≤ m := by
      simpa using active.card_le_univ
    have hloghalf := Real.log_le_sub_one_of_pos (x := (1 / 2 : ℝ)) (by norm_num)
    have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv] at hloghalf
      linarith
    have hexp_le :
        Real.exp (-((active.card : ℝ) * Real.log 2)) ≤
          Real.exp (-((m : ℝ) * ε / 4)) := by
      apply Real.exp_le_exp.mpr
      have hprod : (m : ℝ) * ε / 4 <
          (active.card : ℝ) * Real.log 2 := by
        nlinarith
      linarith
    have hpowexp :
        ((2 : ℝ) ^ active.card)⁻¹ =
          Real.exp (-((active.card : ℝ) * Real.log 2)) := by
      rw [Real.exp_neg]
      congr 1
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    calc
      ((good.card : ℕ) : ℝ) / (2 : ℝ) ^ m
          ≤ ((2 ^ (m - active.card) : ℕ) : ℝ) / (2 : ℝ) ^ m := by
            gcongr
      _ = ((2 : ℝ) ^ active.card)⁻¹ := by
        rw [Nat.cast_pow, Nat.cast_ofNat, pow_sub₀ _ (by norm_num) hactive_le]
        field_simp
      _ = Real.exp (-((active.card : ℝ) * Real.log 2)) := hpowexp
      _ ≤ Real.exp (-((m : ℝ) * ε / 4)) := hexp_le
  · have hzero : good.card = 0 := Finset.not_nonempty_iff_eq_empty.mp hgood |>
        congrArg Finset.card
    simp [hzero, Real.exp_nonneg]

@[blueprint "lem:consistent-bad-event-swap-growth"
  (statement := /-- Let $Z$ be countably infinite, let
  $\mathcal G\subseteq\{0,1\}^Z$, let $D$ be a probability mass function on $Z$, and let
  $m\in\mathbb N$. For independent $S,S'\sim D^m$, the probability that some
  $g\in\mathcal G$ vanishes on $S$ and is one on more than $m\varepsilon/2$ coordinates of
  $S'$ is at most
  $\Gamma_{\mathcal G}(2m)\exp(-m\varepsilon/4)$. -/)
  (proof := /-- Let $J$ be the joint law of $(S,S')$. For every swap mask
  $\sigma\in\{0,1\}^m$, interchange $S_i$ and $S'_i$ where $\sigma_i=1$. By
  \cref{lem:consistent-bad-event-independent-pair-apply} and
  \cref{lem:consistent-bad-event-iid-apply}, this operation preserves every point mass of
  $J$ and hence preserves the probability of the event.

  Average the event indicator over all $2^m$ swap masks and fix the resulting doubled sample.
  Let $P$ be its set of distinct observations; then $|P|\le2m$. By
  \cref{lem:restriction-ncard-le-growth}, at most
  $\Gamma_{\mathcal G}(2m)$ loss patterns occur on $P$. For each such pattern,
  \cref{lem:consistent-bad-event-swap-count} bounds the proportion of favorable masks by
  $\exp(-m\varepsilon/4)$. A finite union bound therefore bounds the averaged indicator by
  the product of these two quantities. Integrating over the doubled sample, whose joint mass
  sums to one, gives the asserted estimate. -/)
  (title := /-- Growth-function bound for the symmetrized bad event -/)
  (latexEnv := "lemma")]
lemma consistent_bad_event_swap_growth {Z : Type*} [Countable Z] [Infinite Z]
    (G : Set (Z → Bool)) (D : PMF Z) (m : ℕ) (ε : ℝ) :
    ((iid_sample D m).bind fun S =>
      (iid_sample D m).map fun S' => (S, S')).toOuterMeasure
        {SS : (Fin m → Z) × (Fin m → Z) |
          ∃ g ∈ G, (∀ i, g (SS.1 i) = false) ∧
            (m : ℝ) * ε / 2 <
              ∑ i, ({z : Z | g z = true}.indicator
                (fun _ => (1 : ℝ))) (SS.2 i)} ≤
      ENNReal.ofReal
        ((growth_function G (2 * m) : ℝ) * Real.exp (-((m : ℝ) * ε / 4))) := by
  classical
  let Q : PMF (Fin m → Z) := iid_sample D m
  let J : PMF ((Fin m → Z) × (Fin m → Z)) :=
    Q.bind fun S => Q.map fun S' => (S, S')
  let W : Set ((Fin m → Z) × (Fin m → Z)) :=
    {SS | ∃ g ∈ G, (∀ i, g (SS.1 i) = false) ∧
      (m : ℝ) * ε / 2 <
        ∑ i, ({z : Z | g z = true}.indicator
          (fun _ => (1 : ℝ))) (SS.2 i)}
  let swap (σ : Fin m → Bool)
      (SS : (Fin m → Z) × (Fin m → Z)) :
      (Fin m → Z) × (Fin m → Z) :=
    (fun i => if σ i then SS.2 i else SS.1 i,
      fun i => if σ i then SS.1 i else SS.2 i)
  have hswap_swap : ∀ σ SS, swap σ (swap σ SS) = SS := by
    intro σ SS
    apply Prod.ext
    · funext i
      cases h : σ i <;> simp [swap, h]
    · funext i
      cases h : σ i <;> simp [swap, h]
  have hJapply : ∀ S S', J (S, S') = Q S * Q S' := by
    intro S S'
    exact consistent_bad_event_independent_pair_apply Q S S'
  have hJswap : ∀ σ SS, J (swap σ SS) = J SS := by
    intro σ SS
    rw [show J (swap σ SS) =
      Q (swap σ SS).1 * Q (swap σ SS).2 from hJapply _ _,
      hJapply, consistent_bad_event_iid_apply,
      consistent_bad_event_iid_apply, consistent_bad_event_iid_apply,
      consistent_bad_event_iid_apply, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    cases h : σ i <;> simp [swap, h, mul_comm]
  have hmap : ∀ σ, J.map (swap σ) = J := by
    intro σ
    apply PMF.ext
    intro SS
    rw [PMF.map_apply, tsum_eq_single (swap σ SS)]
    · rw [if_pos (hswap_swap σ SS).symm, hJswap]
    · intro R hR
      rw [if_neg]
      intro hEq
      apply hR
      rw [← hswap_swap σ R, hEq, hswap_swap]
  have hinvariant : ∀ σ, J.toOuterMeasure W =
      J.toOuterMeasure (swap σ ⁻¹' W) := by
    intro σ
    calc
      J.toOuterMeasure W = (J.map (swap σ)).toOuterMeasure W := by rw [hmap]
      _ = J.toOuterMeasure (swap σ ⁻¹' W) := by
        rw [PMF.toOuterMeasure_map_apply]
  let masks : Finset (Fin m → Bool) := Finset.univ
  let goodMasks (SS : (Fin m → Z) × (Fin m → Z)) :
      Finset (Fin m → Bool) :=
    masks.filter fun σ => swap σ SS ∈ W
  have hmask_bound : ∀ SS,
      ((goodMasks SS).card : ℝ) / (2 : ℝ) ^ m ≤
        (growth_function G (2 * m) : ℝ) * Real.exp (-((m : ℝ) * ε / 4)) := by
    intro SS
    let P : Finset Z :=
      Finset.univ.image SS.1 ∪ Finset.univ.image SS.2
    have hS_mem : ∀ i, SS.1 i ∈ P := by
      intro i
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    have hS'_mem : ∀ i, SS.2 i ∈ P := by
      intro i
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    let res : (Z → Bool) → ({z : Z // z ∈ P} → Bool) :=
      fun g z => g z.1
    let patterns : Finset ({z : Z // z ∈ P} → Bool) :=
      Set.toFinset (res '' G)
    have hPcard : P.card ≤ 2 * m := by
      have h1 : (Finset.univ.image SS.1).card ≤ m := by
        simpa using (Finset.card_image_le :
          (Finset.univ.image SS.1).card ≤ (Finset.univ : Finset (Fin m)).card)
      have h2 : (Finset.univ.image SS.2).card ≤ m := by
        simpa using (Finset.card_image_le :
          (Finset.univ.image SS.2).card ≤ (Finset.univ : Finset (Fin m)).card)
      calc
        P.card ≤ (Finset.univ.image SS.1).card + (Finset.univ.image SS.2).card :=
          Finset.card_union_le _ _
        _ ≤ m + m := add_le_add h1 h2
        _ = 2 * m := by omega
    have hpatterns :
        patterns.card ≤ growth_function G (2 * m) := by
      have h := restriction_ncard_le_growth G P (2 * m) hPcard
      have heq : Set.ncard (res '' G) = patterns.card := by
        simpa [patterns] using Set.ncard_eq_toFinset_card' (res '' G)
      rw [← heq]
      simpa [res] using h
    let patternGood (c : {z : Z // z ∈ P} → Bool) :
        Finset (Fin m → Bool) :=
      (Finset.univ : Finset (Fin m → Bool)).filter fun σ =>
        (∀ i, (if σ i then c ⟨SS.2 i, hS'_mem i⟩
          else c ⟨SS.1 i, hS_mem i⟩) = false) ∧
          (m : ℝ) * ε / 2 <
            ∑ i, if (if σ i then c ⟨SS.1 i, hS_mem i⟩
              else c ⟨SS.2 i, hS'_mem i⟩) = true then (1 : ℝ) else 0
    have hcover : goodMasks SS ⊆ patterns.biUnion patternGood := by
      intro σ hσ
      have hσW := (Finset.mem_filter.mp hσ).2
      obtain ⟨g, hgG, hgfirst, hgsecond⟩ := hσW
      let c : {z : Z // z ∈ P} → Bool := res g
      have hc : c ∈ patterns := by
        simp only [patterns, Set.mem_toFinset, Set.mem_image]
        exact ⟨g, hgG, rfl⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨c, hc, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ σ, ?_, ?_⟩
      · intro i
        have hi := hgfirst i
        cases h : σ i <;> simp [c, res, swap, h] at hi ⊢ <;> exact hi
      · simp only [Set.indicator, swap] at hgsecond
        convert hgsecond using 1 <;>
          apply Finset.sum_congr rfl <;> intro i hi <;>
          cases h : σ i <;> simp [c, res, h]
    have hpattern_bound : ∀ c ∈ patterns,
        ((patternGood c).card : ℝ) ≤
          (2 : ℝ) ^ m * Real.exp (-((m : ℝ) * ε / 4)) := by
      intro c hc
      have h := consistent_bad_event_swap_count m ε
        (fun i => c ⟨SS.1 i, hS_mem i⟩)
        (fun i => c ⟨SS.2 i, hS'_mem i⟩)
      change ((patternGood c).card : ℝ) / (2 : ℝ) ^ m ≤ _ at h
      simpa [mul_comm] using (div_le_iff₀ (pow_pos (by norm_num) m)).mp h
    apply (div_le_iff₀ (pow_pos (by norm_num) m)).mpr
    calc
      ((goodMasks SS).card : ℝ)
          ≤ ((patterns.biUnion patternGood).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hcover
      _ ≤ (∑ c ∈ patterns, (patternGood c).card : ℕ) := by
            exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _c ∈ patterns,
          ((2 : ℝ) ^ m * Real.exp (-((m : ℝ) * ε / 4))) := by
            exact_mod_cast Finset.sum_le_sum hpattern_bound
      _ = (patterns.card : ℝ) *
          ((2 : ℝ) ^ m * Real.exp (-((m : ℝ) * ε / 4))) := by
            simp [mul_assoc]
      _ ≤ (growth_function G (2 * m) : ℝ) *
          ((2 : ℝ) ^ m * Real.exp (-((m : ℝ) * ε / 4))) := by
            gcongr
      _ = ((2 : ℝ) ^ m) *
          ((growth_function G (2 * m) : ℝ) *
            Real.exp (-((m : ℝ) * ε / 4))) := by ring
      _ = ((growth_function G (2 * m) : ℝ) *
          Real.exp (-((m : ℝ) * ε / 4))) * (2 : ℝ) ^ m := by ring
  have hmask_bound_enn : ∀ SS,
      ((goodMasks SS).card : ENNReal) / (2 : ENNReal) ^ m ≤
        ENNReal.ofReal
          ((growth_function G (2 * m) : ℝ) * Real.exp (-((m : ℝ) * ε / 4))):= by
    intro SS
    have h := ENNReal.ofReal_le_ofReal (hmask_bound SS)
    simpa [ENNReal.ofReal_div_of_pos, Real.exp_nonneg] using h
  have havg :
      J.toOuterMeasure W =
        ∑' SS, J SS * (((goodMasks SS).card : ENNReal) / (2 : ENNReal) ^ m) := by
    calc
      J.toOuterMeasure W =
          (∑' σ : Fin m → Bool, J.toOuterMeasure W) / (2 : ENNReal) ^ m := by
            rw [tsum_fintype, Finset.sum_const, Finset.card_univ,
              Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
            rw [Nat.cast_pow, Nat.cast_ofNat]
            symm
            calc
              (2 : ENNReal) ^ m * J.toOuterMeasure W / (2 : ENNReal) ^ m =
                  J.toOuterMeasure W * ((2 : ENNReal) ^ m / (2 : ENNReal) ^ m) := by
                    rw [mul_comm ((2 : ENNReal) ^ m), mul_div_assoc]
              _ = J.toOuterMeasure W := by
                rw [ENNReal.div_self (by positivity) (by simp), mul_one]
      _ = (∑' σ : Fin m → Bool,
          J.toOuterMeasure (swap σ ⁻¹' W)) / (2 : ENNReal) ^ m := by
            congr 1
            exact tsum_congr hinvariant
      _ = (∑' σ : Fin m → Bool, ∑' SS,
          (swap σ ⁻¹' W).indicator J SS) / (2 : ENNReal) ^ m := by
            simp only [PMF.toOuterMeasure_apply]
      _ = (∑' SS, ∑' σ : Fin m → Bool,
          (swap σ ⁻¹' W).indicator J SS) / (2 : ENNReal) ^ m := by
            rw [ENNReal.tsum_comm]
      _ = ∑' SS, J SS *
          (((goodMasks SS).card : ENNReal) / (2 : ENNReal) ^ m) := by
            rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
            apply tsum_congr
            intro SS
            simp only [Set.indicator, Set.mem_preimage, goodMasks, masks,
              Finset.card_filter, tsum_fintype]
            rw [show (∑ σ, if swap σ SS ∈ W then J SS else 0) =
                J SS * (↑(∑ σ, if swap σ SS ∈ W then (1 : ℕ) else 0) : ENNReal) by
              rw [Nat.cast_sum, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro σ hσ
              split_ifs <;> simp]
            exact mul_assoc _ _ _
  change J.toOuterMeasure W ≤ _
  rw [havg]
  calc
    (∑' SS, J SS * (((goodMasks SS).card : ENNReal) / (2 : ENNReal) ^ m))
        ≤ ∑' SS, J SS * ENNReal.ofReal
          ((growth_function G (2 * m) : ℝ) * Real.exp (-((m : ℝ) * ε / 4))) :=
      ENNReal.tsum_le_tsum (fun SS => by gcongr; exact hmask_bound_enn SS)
    _ = ENNReal.ofReal
        ((growth_function G (2 * m) : ℝ) * Real.exp (-((m : ℝ) * ε / 4))) := by
      rw [ENNReal.tsum_mul_right, J.tsum_coe, one_mul]

@[blueprint "lem:consistent-bad-event-growth-bound"
  (statement := /-- Let $\mathcal{H}\subseteq(\Sigma^*)^{\Sigma^*}$, let $m\in\mathbb{N}$,
  and let $\varepsilon>0$ satisfy $m\varepsilon\ge 8$. Let $A$ be a consistent learning rule
  for $\mathcal{H}$ on $m$ samples in the sense of \cref{def:supervised-consistent}, and let
  $\mathcal{D}$ be a distribution on $\Sigma^*\times\Sigma^*$ realizable by $\mathcal{H}$ in
  the sense of \cref{def:realizable-dist}. Then
  $$
  \mathbb{P}_{S\sim\mathcal{D}^{m}}
  \bigl\{L_{\mathcal{D}}(A(S))>\varepsilon\bigr\}
  \le
  2\,\Gamma_{\mathcal{L}^{01}(\mathcal{H})}(2m)
  \exp(-m\varepsilon/4),
  $$
  where the population error, loss class, growth function, and product distribution are those
  of \cref{def:supervised-error}, \cref{def:loss-class}, \cref{def:growth-function}, and
  \cref{def:iid-sample}, respectively. -/)
  (proof := /-- Draw an independent ghost sample $S'\sim\mathcal D^m$. By
  \cref{lem:consistent-bad-event-ghost-symmetrization}, the probability of
  $L_{\mathcal D}(A(S))>\varepsilon$ is at most twice the joint probability that there is an
  $h\in\mathcal H$ which fits every coordinate of $S$ and makes more than
  $m\varepsilon/2$ errors on $S'$.

  Associate to each such $h$ its loss function
  $\ell_h\in\mathcal L^{01}(\mathcal H)$ from \cref{def:loss-class}. The condition that
  $h$ fits $S$ is exactly $\ell_h(S_i)=0$ for every $i$, and its number of errors on $S'$ is
  exactly the number of indices for which $\ell_h(S'_i)=1$. Hence this two-sample event is
  contained in the loss-pattern event of
  \cref{lem:consistent-bad-event-swap-growth}, whose probability is at most
  $$
  \Gamma_{\mathcal L^{01}(\mathcal H)}(2m)\exp(-m\varepsilon/4).
  $$
  Multiplying this estimate by the preceding factor $2$ proves the claimed bound. -/)
  (title := /-- Growth-function bound for the bad event of a consistent rule -/)
  (latexEnv := "lemma")]
lemma consistent_bad_event_growth_bound (H : Set (List Bool → List Bool)) (m : ℕ)
    (ε : ℝ) (hε : 0 < ε) (hmε : 8 ≤ (m : ℝ) * ε)
    (A : (Fin m → List Bool × List Bool) → (List Bool → List Bool))
    (hA : supervised_consistent H m A) (D : PMF (List Bool × List Bool))
    (hD : realizable_dist H D) :
    (iid_sample D m).toOuterMeasure
        {S : Fin m → List Bool × List Bool |
          ENNReal.ofReal ε < supervised_error D (A S)} ≤
      ENNReal.ofReal
        (2 * (growth_function (loss_class H) (2 * m) : ℝ) *
          Real.exp (-((m : ℝ) * ε / 4))) := by
  classical
  let J : PMF ((Fin m → List Bool × List Bool) ×
      (Fin m → List Bool × List Bool)) :=
    (iid_sample D m).bind fun S => (iid_sample D m).map fun S' => (S, S')
  let WH : Set ((Fin m → List Bool × List Bool) ×
      (Fin m → List Bool × List Bool)) :=
    {SS | ∃ h ∈ H, (∀ i, h (SS.1 i).1 = (SS.1 i).2) ∧
      (m : ℝ) * ε / 2 <
        ∑ i, ({z : List Bool × List Bool | h z.1 ≠ z.2}.indicator
          (fun _ => (1 : ℝ))) (SS.2 i)}
  let WL : Set ((Fin m → List Bool × List Bool) ×
      (Fin m → List Bool × List Bool)) :=
    {SS | ∃ g ∈ loss_class H, (∀ i, g (SS.1 i) = false) ∧
      (m : ℝ) * ε / 2 <
        ∑ i, ({z : List Bool × List Bool | g z = true}.indicator
          (fun _ => (1 : ℝ))) (SS.2 i)}
  have hghost :
      (iid_sample D m).toOuterMeasure
          {S : Fin m → List Bool × List Bool |
            ENNReal.ofReal ε < supervised_error D (A S)} ≤
        2 * J.toOuterMeasure WH := by
    simpa [J, WH] using
      consistent_bad_event_ghost_symmetrization H m ε hε hmε A hA D hD
  have hsub : WH ∩ J.support ⊆ WL := by
    rintro SS ⟨⟨h, hh, hfit, herr⟩, hSS⟩
    refine ⟨(fun z : List Bool × List Bool => !decide (h z.1 = z.2)),
      ⟨h, hh, rfl⟩, ?_, ?_⟩
    · intro i
      simp [hfit i]
    · simpa [Set.indicator] using herr
  have hmono : J.toOuterMeasure WH ≤ J.toOuterMeasure WL :=
    J.toOuterMeasure_mono hsub
  have hswap :
      J.toOuterMeasure WL ≤
        ENNReal.ofReal
          ((growth_function (loss_class H) (2 * m) : ℝ) *
            Real.exp (-((m : ℝ) * ε / 4))) := by
    simpa [J, WL] using
      consistent_bad_event_swap_growth (loss_class H) D m ε
  calc
    (iid_sample D m).toOuterMeasure
        {S : Fin m → List Bool × List Bool |
          ENNReal.ofReal ε < supervised_error D (A S)}
        ≤ 2 * J.toOuterMeasure WH := hghost
    _ ≤ 2 * J.toOuterMeasure WL := by gcongr
    _ ≤ 2 * ENNReal.ofReal
        ((growth_function (loss_class H) (2 * m) : ℝ) *
          Real.exp (-((m : ℝ) * ε / 4))) := by gcongr
    _ = ENNReal.ofReal
        (2 * (growth_function (loss_class H) (2 * m) : ℝ) *
          Real.exp (-((m : ℝ) * ε / 4))) := by
      rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring

@[blueprint "lem:vc-growth-tail-threshold"
  (statement := /-- There is a universal constant $c>0$ with the following property. For every
  binary class $\mathcal{G}\subseteq\{0,1\}^{\Sigma^*\times\Sigma^*}$ and all
  $k,m\in\mathbb{N}$ satisfying $\mathrm{VC}(\mathcal{G})\le k$, if
  $\varepsilon,\delta\in(0,1)$ and
  $$
  m\ge c\,\frac{k\log(12/\varepsilon)+\log(2/\delta)}{\varepsilon},
  $$
  then $m\varepsilon\ge 8$ and
  $$
  2\,\Gamma_{\mathcal{G}}(2m)\exp(-m\varepsilon/4)\le\delta.
  $$ -/)
  (proof := /-- Take $c=1024$, and write
  $L=\log(12/\varepsilon)$, $R=\log(2/\delta)$, and $x=m\varepsilon$. Applying
  $\log t\le t-1$ at $t=1/2$ gives $\log 2\ge1/2$. Since
  $0<\varepsilon,\delta<1$, monotonicity of the logarithm gives
  $L>\log2\ge1/2$ and $R>\log2\ge1/2$. Multiplying the sample-size hypothesis by
  $\varepsilon>0$ yields
  $$x\ge1024(kL+R),$$
  which in particular implies $x\ge8$.

  If $k=0$, \cref{lem:growth-function-le-sum-choose} gives
  $\Gamma_{\mathcal{G}}(2m)\le\binom{2m}{0}=1$. The preceding bound also gives
  $x/4\ge R$, and therefore
  $$2\Gamma_{\mathcal{G}}(2m)e^{-x/4}\le2e^{-R}=\delta.$$

  Suppose now that $k\ge1$. Since $L\ge1/2$, the inequality
  $x\ge1024kL$ and the bounds $x=m\varepsilon\le m$ imply $k\le m$, hence $k\le2m$.
  Thus \cref{lem:sauer-lemma} gives
  $$\Gamma_{\mathcal{G}}(2m)\le B^k,
  \qquad B=\frac{2em}{k}.$$
  Put $y=x/k$, so that $B=(2e/\varepsilon)y$. We next estimate the two logarithms in
  $\log B=\log(2e/\varepsilon)+\log y$. The inequalities
  $\log2\le1$, $\log12\ge\log2\ge1/2$, and $\log\varepsilon<0$ imply
  $$\log(2e/\varepsilon)\le4L.$$
  Applying $\log t\le t-1$ to $t=y/16$, and using $\log16<15$ and $L\ge1/2$, gives
  $$\log y\le\frac{y}{16}+28L.$$
  Consequently
  $$\log B\le\frac{y}{16}+32L.$$
  After multiplication by $k$, the sample-size inequality yields
  $$
  k\log B\le\frac{x}{16}+32kL
  \le\frac{x}{16}+\frac{x}{32}\le\frac{x}{8}.
  $$
  Exponentiating and using the Sauer bound gives
  $\Gamma_{\mathcal{G}}(2m)\le e^{x/8}$. Finally, the same sample-size inequality implies
  $R\le x/8$, and hence
  $$
  2\Gamma_{\mathcal{G}}(2m)e^{-x/4}
  \le2e^{x/8}e^{-x/4}=2e^{-x/8}\le2e^{-R}=\delta.
  $$ -/)
  (title := /-- A VC sample threshold controls the growth-function tail -/)
  (latexEnv := "lemma")]
lemma vc_growth_tail_threshold :
    ∃ c : ℝ, 0 < c ∧
      ∀ (G : Set ((List Bool × List Bool) → Bool)) (k m : ℕ),
        vc_dim G ≤ (k : ℕ∞) →
        ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
          c * (((k : ℝ) * Real.log (12 / ε) + Real.log (2 / δ)) / ε) ≤ (m : ℝ) →
          8 ≤ (m : ℝ) * ε ∧
            ENNReal.ofReal
                (2 * (growth_function G (2 * m) : ℝ) *
                  Real.exp (-((m : ℝ) * ε / 4))) ≤
              ENNReal.ofReal δ := by
  refine ⟨1024, by norm_num, ?_⟩
  intro G k m hvc ε δ hε hε_one hδ hδ_one hsample
  have htwelve : (12 : ℝ) < 12 / ε := by
    rw [lt_div_iff₀ hε]
    nlinarith
  have hloghalf := Real.log_le_sub_one_of_pos (x := (1 / 2 : ℝ)) (by norm_num)
  have hlogtwo_lower : (1 / 2 : ℝ) ≤ Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv] at hloghalf
    linarith
  have hL : Real.log 2 < Real.log (12 / ε) :=
    Real.log_lt_log (by norm_num) (lt_trans (by norm_num) htwelve)
  have htwo : (2 : ℝ) < 2 / δ := by
    rw [lt_div_iff₀ hδ]
    nlinarith
  have hR : Real.log 2 < Real.log (2 / δ) :=
    Real.log_lt_log (by norm_num) htwo
  have hRpos : 0 < Real.log (2 / δ) :=
    lt_trans (Real.log_pos (by norm_num)) hR
  have hsample' :
      (1024 * ((k : ℝ) * Real.log (12 / ε) + Real.log (2 / δ))) / ε ≤ (m : ℝ) := by
    calc
      (1024 * ((k : ℝ) * Real.log (12 / ε) + Real.log (2 / δ))) / ε =
          1024 * (((k : ℝ) * Real.log (12 / ε) + Real.log (2 / δ)) / ε) := by ring
      _ ≤ (m : ℝ) := hsample
  have hx :
      1024 * ((k : ℝ) * Real.log (12 / ε) + Real.log (2 / δ)) ≤ (m : ℝ) * ε :=
    (div_le_iff₀ hε).mp hsample'
  have hk_nonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hLpos : 0 ≤ Real.log (12 / ε) :=
    le_trans (by norm_num) (le_trans hlogtwo_lower (le_of_lt hL))
  have hkL_nonneg : 0 ≤ (k : ℝ) * Real.log (12 / ε) :=
    mul_nonneg hk_nonneg hLpos
  have hmε : 8 ≤ (m : ℝ) * ε := by
    nlinarith
  refine ⟨hmε, ENNReal.ofReal_le_ofReal ?_⟩
  have hexpR : Real.exp (-Real.log (2 / δ)) = δ / 2 := by
    rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) hδ)]
    field_simp
  by_cases hk : k = 0
  · subst k
    have hgrowth_nat := growth_function_le_sum_choose G 0 (2 * m) hvc
    norm_num at hgrowth_nat
    have hgrowth : (growth_function G (2 * m) : ℝ) ≤ 1 := by
      exact_mod_cast hgrowth_nat
    have hdecay :
        Real.exp (-((m : ℝ) * ε / 4)) ≤ Real.exp (-Real.log (2 / δ)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc
      2 * (growth_function G (2 * m) : ℝ) * Real.exp (-((m : ℝ) * ε / 4)) ≤
          2 * 1 * Real.exp (-((m : ℝ) * ε / 4)) := by gcongr
      _ ≤ 2 * 1 * Real.exp (-Real.log (2 / δ)) := by gcongr
      _ = δ := by rw [hexpR]; ring
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hkpos_real : 0 < (k : ℝ) := by exact_mod_cast hkpos
    have hkne_real : (k : ℝ) ≠ 0 := ne_of_gt hkpos_real
    have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hmε_le_m : (m : ℝ) * ε ≤ (m : ℝ) := by
      nlinarith
    have hkm_real : (k : ℝ) ≤ (m : ℝ) := by
      nlinarith
    have hkm : k ≤ m := by exact_mod_cast hkm_real
    have hk_two_m : k ≤ 2 * m := by omega
    have hgrowth := sauer_lemma G k (2 * m) hkpos hvc hk_two_m
    have hmpos_real : 0 < (m : ℝ) := by nlinarith
    have hmpos : 0 < m := by exact_mod_cast hmpos_real
    let y : ℝ := (m : ℝ) * ε / (k : ℝ)
    let B : ℝ := Real.exp 1 * (2 * m : ℕ) / (k : ℝ)
    have hypos : 0 < y := by
      dsimp [y]
      positivity
    have hBpos : 0 < B := by
      dsimp [B]
      exact div_pos (mul_pos (Real.exp_pos 1) (by positivity)) hkpos_real
    have hBfac : B = (2 * Real.exp 1 / ε) * y := by
      dsimp [B, y]
      push_cast
      field_simp
    have hApos : 0 < 2 * Real.exp 1 / ε := by positivity
    have hlogtwo_upper : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
      linarith
    have hlogtwelve_lower : Real.log 2 ≤ Real.log 12 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hlogε : Real.log ε < 0 := Real.log_neg hε hε_one
    have hlogA_eq :
        Real.log (2 * Real.exp 1 / ε) = Real.log 2 + 1 - Real.log ε := by
      rw [Real.log_div (mul_ne_zero (by norm_num) (Real.exp_ne_zero 1)) (ne_of_gt hε),
        Real.log_mul (by norm_num) (Real.exp_ne_zero 1), Real.log_exp]
    have hlogL_eq : Real.log (12 / ε) = Real.log 12 - Real.log ε := by
      rw [Real.log_div (by norm_num) (ne_of_gt hε)]
    have hlogA : Real.log (2 * Real.exp 1 / ε) ≤ 4 * Real.log (12 / ε) := by
      rw [hlogA_eq, hlogL_eq]
      nlinarith
    have hzpos : 0 < y / 16 := div_pos hypos (by norm_num)
    have hlogz := Real.log_le_sub_one_of_pos hzpos
    have hlog_sixteen : Real.log (16 : ℝ) < 15 := by
      have h := Real.log_lt_sub_one_of_pos (x := (16 : ℝ)) (by norm_num) (by norm_num)
      norm_num at h
      exact h
    have hyfactor : y = (y / 16) * 16 := by ring
    have hlogy_eq : Real.log y = Real.log (y / 16) + Real.log 16 := by
      calc
        Real.log y = Real.log ((y / 16) * 16) := congrArg Real.log hyfactor
        _ = Real.log (y / 16) + Real.log 16 :=
          Real.log_mul (ne_of_gt hzpos) (by norm_num)
    have hlogy : Real.log y ≤ y / 16 + 28 * Real.log (12 / ε) := by
      rw [hlogy_eq]
      nlinarith
    have hlogB : Real.log B ≤ y / 16 + 32 * Real.log (12 / ε) := by
      rw [hBfac, Real.log_mul (ne_of_gt hApos) (ne_of_gt hypos)]
      linarith
    have hky : (k : ℝ) * y = (m : ℝ) * ε := by
      dsimp [y]
      field_simp
    have hbudget :
        32 * (k : ℝ) * Real.log (12 / ε) ≤ ((m : ℝ) * ε) / 32 := by
      nlinarith
    have hklogB : (k : ℝ) * Real.log B ≤ ((m : ℝ) * ε) / 8 := by
      have hmul := mul_le_mul_of_nonneg_left hlogB (le_of_lt hkpos_real)
      nlinarith
    have hlogB_scaled : Real.log B ≤ ((m : ℝ) * ε) / (8 * (k : ℝ)) := by
      apply (le_div_iff₀ (mul_pos (by norm_num) hkpos_real)).2
      nlinarith
    have hbase_exp : B ≤ Real.exp (((m : ℝ) * ε) / (8 * (k : ℝ))) := by
      rw [← Real.exp_log hBpos]
      exact Real.exp_le_exp.mpr hlogB_scaled
    have hpow : B ^ k ≤ Real.exp (((m : ℝ) * ε) / 8) := by
      calc
        B ^ k ≤ (Real.exp (((m : ℝ) * ε) / (8 * (k : ℝ)))) ^ k := by gcongr
        _ = Real.exp (((m : ℝ) * ε) / 8) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          field_simp
    have hgrowthB : (growth_function G (2 * m) : ℝ) ≤ B ^ k := by
      simpa [B] using hgrowth
    have hgrowth_exp :
        (growth_function G (2 * m) : ℝ) ≤ Real.exp (((m : ℝ) * ε) / 8) :=
      le_trans hgrowthB hpow
    have hRbudget : Real.log (2 / δ) ≤ ((m : ℝ) * ε) / 8 := by
      nlinarith
    have hdecay :
        Real.exp (-((m : ℝ) * ε / 8)) ≤ Real.exp (-Real.log (2 / δ)) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      2 * (growth_function G (2 * m) : ℝ) * Real.exp (-((m : ℝ) * ε / 4)) ≤
          2 * Real.exp (((m : ℝ) * ε) / 8) * Real.exp (-((m : ℝ) * ε / 4)) := by
            gcongr
      _ = 2 * (Real.exp (((m : ℝ) * ε) / 8) * Real.exp (-((m : ℝ) * ε / 4))) := by ring
      _ = 2 * Real.exp (((m : ℝ) * ε) / 8 + -((m : ℝ) * ε / 4)) := by
        rw [Real.exp_add]
      _ = 2 * Real.exp (-((m : ℝ) * ε / 8)) := by ring_nf
      _ ≤ 2 * Real.exp (-Real.log (2 / δ)) := by gcongr
      _ = δ := by rw [hexpR]; ring

@[blueprint "lem:loss-class-gen-bound"
  (statement := /-- (General Guarantee.) There is a universal constant $c>0$ such that the
  following holds for the domain $\mathcal{X}=\Sigma^*$ and the label space
  $\mathcal{Y}=\Sigma^*$. Let $\mathcal{H}\subseteq\mathcal{Y}^{\mathcal{X}}$ be a hypothesis
  class, let $k,m\in\mathbb{N}$ with
  $\mathrm{VC}\bigl(\mathcal{L}^{01}(\mathcal{H})\bigr)\le k$, and let
  $\varepsilon,\delta\in(0,1)$ satisfy
  $$m\;\ge\;c\cdot\frac{k\log(12/\varepsilon)+\log(2/\delta)}{\varepsilon}.$$
  Then for every consistent learning rule $A$ for $\mathcal{H}$ on $m$ samples, in the sense of
  \cref{def:supervised-consistent}, and every distribution $\mathcal{D}$ on
  $\mathcal{X}\times\mathcal{Y}$ realizable by $\mathcal{H}$ in the sense of
  \cref{def:realizable-dist}, with probability at least $1-\delta$ over $S\sim\mathcal{D}^{m}$
  the population error satisfies $L_{\mathcal{D}}(A(S))\le\varepsilon$, where
  $L_{\mathcal{D}}$ is as in \cref{def:supervised-error} and $\mathcal{D}^{m}$ is as in
  \cref{def:iid-sample}. -/)
  (proof := /-- Choose the universal constant $c>0$ furnished by
  \cref{lem:vc-growth-tail-threshold}. Fix $\mathcal{H}$, $k$, $m$, $\varepsilon$, and
  $\delta$ satisfying the hypotheses. Apply that lemma to
  $\mathcal{G}=\mathcal{L}^{01}(\mathcal{H})$. It yields both $m\varepsilon\ge8$ and
  $$
  2\,\Gamma_{\mathcal{L}^{01}(\mathcal{H})}(2m)
  \exp(-m\varepsilon/4)\le\delta.
  $$
  For any consistent rule $A$ and any realizable distribution $\mathcal{D}$,
  \cref{lem:consistent-bad-event-growth-bound} bounds the probability of
  $L_{\mathcal{D}}(A(S))>\varepsilon$ by the left-hand side of this inequality. Transitivity
  gives the required bound by $\delta$. -/)
  (title := /-- General guarantee for consistent rules via the loss-class VC dimension -/)
  (latexEnv := "lemma")]
lemma loss_class_gen_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (H : Set (List Bool → List Bool)) (k m : ℕ),
      vc_dim (loss_class H) ≤ (k : ℕ∞) →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        c * (((k : ℝ) * Real.log (12 / ε) + Real.log (2 / δ)) / ε) ≤ (m : ℝ) →
        ∀ A : (Fin m → List Bool × List Bool) → (List Bool → List Bool),
          supervised_consistent H m A →
          ∀ Dj : PMF (List Bool × List Bool), realizable_dist H Dj →
            (iid_sample Dj m).toOuterMeasure
                {S : Fin m → List Bool × List Bool |
                  ENNReal.ofReal ε < supervised_error Dj (A S)} ≤ ENNReal.ofReal δ := by
  obtain ⟨c, hc, htail⟩ := vc_growth_tail_threshold
  refine ⟨c, hc, ?_⟩
  intro H k m hvc ε δ hε hε_one hδ hδ_one hsample A hA D hD
  obtain ⟨hmε, hbound⟩ :=
    htail (loss_class H) k m hvc ε δ hε hε_one hδ hδ_one hsample
  exact (consistent_bad_event_growth_bound H m ε hε hmε A hA D hD).trans hbound

@[blueprint "lem:iid-sample-map"
  (statement := /-- Let $X$ and $Y$ be arbitrary sets, let $\mathcal{D}$ be a probability mass
  function on $X$, let $g\colon X\to Y$ be any map and let $m\in\mathbb{N}$. Then the $m$-fold
  i.i.d. sample distribution of the push-forward $g_{*}\mathcal{D}$ coincides with the
  push-forward of $\mathcal{D}^{m}$ under the coordinatewise map
  $(x_1,\dots,x_m)\mapsto(g(x_1),\dots,g(x_m))$, the i.i.d. sample distribution being that of
  \cref{def:iid-sample}. -/)
  (proof := /-- We argue by induction on $m$, both sides being read off from the recursion of
  \cref{def:iid-sample}.

  For $m=0$, the left-hand side is by \cref{def:iid-sample} the point mass at the unique
  function $\mathbf{0}\to X$ read into $Y$, and the right-hand side is the push-forward of the
  point mass at the empty tuple; since the push-forward of a point mass at a point $a$ is the
  point mass at the image of $a$, both sides are point masses, and their base points are
  functions on the empty index set $\mathrm{Fin}\,0$, hence equal by extensionality, there being
  no index at which they could differ.

  Assume the claim for $m$, i.e.
  $(g_{*}\mathcal{D})^{m}=(\text{coordinatewise }g)_{*}\mathcal{D}^{m}$. By
  \cref{def:iid-sample},
  $(g_{*}\mathcal{D})^{m+1}$ is obtained by drawing the first coordinate
  $y_0\sim g_{*}\mathcal{D}$ and then prepending it to a draw from $(g_{*}\mathcal{D})^{m}$.
  Because the push-forward $g_{*}\mathcal{D}$ appears in the position of the variable that is
  integrated out, drawing $y_0\sim g_{*}\mathcal{D}$ and continuing is the same as drawing
  $x_0\sim\mathcal{D}$ and continuing with $y_0=g(x_0)$; formally, push-forward composed with
  such a two-stage draw is rewritten by the identities expressing that push-forward commutes
  with the two-stage draw and that iterated push-forwards compose. After also substituting the
  inductive hypothesis, both sides become two-stage draws that first pick $x_0\sim\mathcal{D}$
  and then push $\mathcal{D}^{m}$ forward; so it suffices to compare, for each fixed
  $x_0\in X$ and each tuple $s\in X^{m}$, the tuple obtained by prepending $g(x_0)$ to
  $(g(s_1),\dots,g(s_m))$ with the tuple obtained by applying $g$ coordinatewise to the tuple
  $(x_0,s_1,\dots,s_m)$. These two functions on $\mathrm{Fin}\,(m+1)$ agree, since prepending a
  coordinate commutes with postcomposition by $g$: at the index $0$ both give $g(x_0)$, and at
  an index $j+1$ both give $g(s_j)$. Hence the two distributions coincide, which completes the
  induction. -/)
  (title := /-- I.i.d. sampling commutes with push-forward -/)
  (latexEnv := "lemma")]
lemma iid_sample_map {X Y : Type*} (D : PMF X) (g : X → Y) (m : ℕ) :
    iid_sample (D.map g) m = (iid_sample D m).map (fun x i => g (x i)) := by
  induction m with
  | zero =>
    simp only [iid_sample, PMF.pure_map]
    congr 1
    funext i
    exact i.elim0
  | succ n ih =>
    simp only [iid_sample, ih, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
    congr 1
    funext a
    congr 1
    funext s
    exact (Fin.comp_cons g a s).symm

@[blueprint "lem:cot-realizable"
  (statement := /-- Let $\mathcal{F}\subseteq\Sigma^{\Sigma^*}$ be a base class, let
  $T\in\mathbb{N}$, let $f_*\in\mathcal{F}$ and let $\mathcal{D}$ be a probability distribution
  on $\Sigma^*$. Then the joint distribution on $\Sigma^*\times\Sigma^*$ obtained by pushing
  $\mathcal{D}$ forward along
  $\mathbf{x}\mapsto\bigl(\mathbf{x},(f_*)_{\mathrm{CoT}}^{T}(\mathbf{x})\bigr)$ is realizable
  by the chain-of-thought class $\mathcal{F}_{\mathrm{CoT}}^{T}$, in the sense of
  \cref{def:realizable-dist}, where $\mathcal{F}_{\mathrm{CoT}}^{T}$ is as in
  \cref{def:cot-class}. -/)
  (proof := /-- Take the witness $h=(f_*)_{\mathrm{CoT}}^{T}$, which lies in
  $\mathcal{F}_{\mathrm{CoT}}^{T}$ by \cref{def:cot-class} because $f_*\in\mathcal{F}$. Every
  pair in the support of the push-forward distribution is of the form
  $\bigl(\mathbf{x},(f_*)_{\mathrm{CoT}}^{T}(\mathbf{x})\bigr)$ for some
  $\mathbf{x}\in\Sigma^*$ in the support of $\mathcal{D}$, and for such a pair the label is by
  construction the value of $h$ at the first coordinate. Hence the requirement of
  \cref{def:realizable-dist} holds. -/)
  (title := /-- The trace-labelled distribution is realizable by the chain-of-thought class -/)
  (latexEnv := "lemma")]
lemma cot_realizable (F : Set (List Bool → Bool)) (T : ℕ) (fstar : List Bool → Bool)
    (hf : fstar ∈ F) (D : PMF (List Bool)) :
    realizable_dist (cot_class F T) (D.map (fun x => (x, cot_trace fstar T x))) := by
  refine ⟨cot_trace fstar T, ⟨fstar, hf, rfl⟩, fun p hp => ?_⟩
  simp only [PMF.support_map, Set.mem_image] at hp
  obtain ⟨x, -, rfl⟩ := hp
  rfl

@[blueprint "lem:cot-consistent-induces-supervised"
  (statement := /-- Let $\mathcal{F}\subseteq\Sigma^{\Sigma^*}$ be a base class, let
  $T,m\in\mathbb{N}$ and let $A$ be a chain-of-thought consistent rule for $\mathcal{F}$ at
  length $T$ on $m$ traces, in the sense of \cref{def:cot-consistent-rule}. Then there exists a
  learning rule $A'\colon(\Sigma^*\times\Sigma^*)^{m}\to(\Sigma^*)^{\Sigma^*}$ such that
  \begin{enumerate}
    \item $A'$ is consistent for $\mathcal{F}_{\mathrm{CoT}}^{T}$ in the sense of
      \cref{def:supervised-consistent}, and
    \item for every tuple $(\mathbf{x}_1,\dots,\mathbf{x}_m)\in(\Sigma^*)^{m}$, every
      $f\in\mathcal{F}$ and every $\mathbf{y}\in\Sigma^*$, the hypothesis produced by $A$ from
      the traces $\mathbf{z}_i=f_{\mathrm{CoT}}^{T}(\mathbf{x}_i)$ is the last token of the
      trace produced by $A'$ from the labelled sample
      $\bigl((\mathbf{x}_i,\mathbf{z}_i)\bigr)_{i=1}^{m}$, that is,
      $$A(\mathbf{z}_1,\dots,\mathbf{z}_m)(\mathbf{y})
      =A'\bigl((\mathbf{x}_1,\mathbf{z}_1),\dots,(\mathbf{x}_m,\mathbf{z}_m)\bigr)
      (\mathbf{y})[-1].$$
  \end{enumerate}
  Here $\mathcal{F}_{\mathrm{CoT}}^{T}$ is as in \cref{def:cot-class}. -/)
  (proof := /-- Let $S=\bigl((\mathbf{x}_1,\mathbf{u}_1),\dots,(\mathbf{x}_m,\mathbf{u}_m)\bigr)$
  be a labelled sample and write $\mathbf{z}_i=\mathbf{u}_i$ for the observed labels. Consider
  first a sample $S$ admitting some $h\in\mathcal{F}_{\mathrm{CoT}}^{T}$ with
  $h(\mathbf{x}_i)=\mathbf{u}_i$ for all $i$. By \cref{def:cot-class} we have
  $h=f'_{\mathrm{CoT}}{}^{T}$ for some $f'\in\mathcal{F}$, so
  $\mathbf{u}_i=f'_{\mathrm{CoT}}{}^{T}(\mathbf{x}_i)$, and therefore
  $\mathbf{u}_i[:-(T+1)]=\mathbf{x}_i$ by \cref{lem:cot-input-trace}. Consequently the tuple of
  traces $(\mathbf{u}_1,\dots,\mathbf{u}_m)$ satisfies the hypothesis of
  \cref{def:cot-consistent-rule} with the witness $f'$, and hence there exists
  $\hat f\in\mathcal{F}$ with
  $\hat f_{\mathrm{CoT}}^{T}\bigl(\mathbf{u}_i[:-(T+1)]\bigr)=\mathbf{u}_i$ for all $i$ and
  $A(\mathbf{u}_1,\dots,\mathbf{u}_m)=\hat f_{\mathrm{e2e}}^{T}$. By choice, fix
  such an $\hat f=\hat f(S)$ for every sample $S$ of this kind, and define
  $A'(S)=\hat f(S)_{\mathrm{CoT}}^{T}$; for samples $S$ admitting no consistent member of
  $\mathcal{F}_{\mathrm{CoT}}^{T}$ define $A'(S)$ arbitrarily, say as the identity map on
  $\Sigma^*$.

  We verify the two assertions. For the first, let $S$ admit a consistent
  $h\in\mathcal{F}_{\mathrm{CoT}}^{T}$. Then $A'(S)=\hat f(S)_{\mathrm{CoT}}^{T}$ lies in
  $\mathcal{F}_{\mathrm{CoT}}^{T}$ by \cref{def:cot-class} since
  $\hat f(S)\in\mathcal{F}$, and, combining
  $\hat f(S)_{\mathrm{CoT}}^{T}\bigl(\mathbf{u}_i[:-(T+1)]\bigr)=\mathbf{u}_i$ with
  $\mathbf{u}_i[:-(T+1)]=\mathbf{x}_i$ established above, we get
  $A'(S)(\mathbf{x}_i)=\mathbf{u}_i$ for all $i$. This is exactly the requirement of
  \cref{def:supervised-consistent}.

  For the second, let $(\mathbf{x}_1,\dots,\mathbf{x}_m)$ be arbitrary, let $f\in\mathcal{F}$
  and put $\mathbf{z}_i=f_{\mathrm{CoT}}^{T}(\mathbf{x}_i)$ and
  $S=\bigl((\mathbf{x}_i,\mathbf{z}_i)\bigr)_{i=1}^{m}$. The sample $S$ admits the consistent
  hypothesis $f_{\mathrm{CoT}}^{T}\in\mathcal{F}_{\mathrm{CoT}}^{T}$, so the construction above
  applies and yields $A(\mathbf{z}_1,\dots,\mathbf{z}_m)=\hat f(S)_{\mathrm{e2e}}^{T}$ together
  with $A'(S)=\hat f(S)_{\mathrm{CoT}}^{T}$. By \cref{def:end-to-end} the map
  $\hat f(S)_{\mathrm{e2e}}^{T}$ is precisely the last token of
  $\hat f(S)_{\mathrm{CoT}}^{T}$, which is the asserted identity. -/)
  (title := /-- A chain-of-thought consistent rule is induced by a consistent trace learner -/)
  (latexEnv := "lemma")]
lemma cot_consistent_induces_supervised (F : Set (List Bool → Bool)) (T m : ℕ)
    (A : (Fin m → List Bool) → (List Bool → Bool)) (hA : cot_consistent_rule F T m A) :
    ∃ A' : (Fin m → List Bool × List Bool) → (List Bool → List Bool),
      supervised_consistent (cot_class F T) m A' ∧
        ∀ (x : Fin m → List Bool) (f : List Bool → Bool), f ∈ F →
          ∀ y : List Bool,
            A (fun i => cot_trace f T (x i)) y =
              (A' (fun i => (x i, cot_trace f T (x i))) y).getLastD false := by
  classical
  let good (S : Fin m → List Bool × List Bool) : Prop :=
    ∃ f ∈ F, A (fun i => (S i).2) = end_to_end f T ∧
      ∀ i, cot_trace f T (S i).1 = (S i).2
  let A' : (Fin m → List Bool × List Bool) → (List Bool → List Bool) := fun S =>
    if h : good S then cot_trace (Classical.choose h) T else id
  refine ⟨A', ?_, ?_⟩
  · intro S hS
    have hgood : good S := by
      rcases hS with ⟨h, ⟨f, hf, rfl⟩, hfit⟩
      have hz : ∃ f ∈ F, ∀ i, cot_trace f T (trace_input T (S i).2) = (S i).2 := by
        refine ⟨f, hf, ?_⟩
        intro i
        rw [← hfit i, cot_input_trace]
      obtain ⟨fhat, hfhat, hAeq, htrace⟩ := hA (fun i => (S i).2) hz
      refine ⟨fhat, hfhat, hAeq, ?_⟩
      intro i
      have hin : trace_input T (S i).2 = (S i).1 := by
        rw [← hfit i]
        exact cot_input_trace f T (S i).1
      calc
        cot_trace fhat T (S i).1 = cot_trace fhat T (trace_input T (S i).2) :=
          congrArg (cot_trace fhat T) hin.symm
        _ = (S i).2 := htrace i
    have hspec := Classical.choose_spec hgood
    simp only [A', dif_pos hgood]
    refine ⟨⟨Classical.choose hgood, hspec.1, rfl⟩, ?_⟩
    exact hspec.2.2
  · intro x f hf y
    have hgood : good (fun i => (x i, cot_trace f T (x i))) := by
      have hz : ∃ g ∈ F, ∀ i,
          cot_trace g T (trace_input T (cot_trace f T (x i))) = cot_trace f T (x i) := by
        refine ⟨f, hf, ?_⟩
        intro i
        rw [cot_input_trace]
      obtain ⟨fhat, hfhat, hAeq, htrace⟩ :=
        hA (fun i => cot_trace f T (x i)) hz
      refine ⟨fhat, hfhat, hAeq, ?_⟩
      intro i
      simpa only [cot_input_trace] using htrace i
    have hspec := Classical.choose_spec hgood
    simp only [A', dif_pos hgood]
    calc
      A (fun i => cot_trace f T (x i)) y = end_to_end (Classical.choose hgood) T y :=
        congrFun hspec.2.1 y
      _ = (cot_trace (Classical.choose hgood) T y).getLastD false := rfl

@[blueprint "lem:cot-error-le-supervised-error"
  (statement := /-- Let $\mathcal{D}$ be a probability distribution on $\Sigma^*$, let
  $f_*\colon\Sigma^*\to\Sigma$, let $T\in\mathbb{N}$, and let $h\colon\Sigma^*\to\Sigma$ and
  $H\colon\Sigma^*\to\Sigma^*$ satisfy $h(\mathbf{y})=H(\mathbf{y})[-1]$ for every
  $\mathbf{y}\in\Sigma^*$, where $\mathbf{w}[-1]$ denotes the last token of $\mathbf{w}$ with
  the convention of \cref{def:end-to-end} that the last token of the empty string is $0$. Then
  $$L^{01}_{\mathcal{D},f_*}(h)\;\le\;L_{\mathcal{D}'}(H),\qquad
  \mathcal{D}'=\bigl(\mathbf{x}\mapsto
  (\mathbf{x},(f_*)_{\mathrm{CoT}}^{T}(\mathbf{x}))\bigr)_{*}\mathcal{D},$$
  where $L^{01}_{\mathcal{D},f_*}$ is as in \cref{def:cot-loss}, the trace map
  $(f_*)_{\mathrm{CoT}}^{T}$ is as in \cref{def:cot-trace} and $L_{\mathcal{D}'}$ is as in
  \cref{def:supervised-error}. -/)
  (proof := /-- Since $\mathcal{D}'$ is the push-forward of $\mathcal{D}$ along
  $\mathbf{x}\mapsto\bigl(\mathbf{x},(f_*)_{\mathrm{CoT}}^{T}(\mathbf{x})\bigr)$, we have by
  \cref{def:supervised-error}
  $$L_{\mathcal{D}'}(H)=\mathbb{P}_{\mathbf{x}\sim\mathcal{D}}
  \bigl(H(\mathbf{x})\neq (f_*)_{\mathrm{CoT}}^{T}(\mathbf{x})\bigr).$$
  It therefore suffices to show the inclusion of events
  $$\bigl\{\mathbf{x}\;:\;h(\mathbf{x})\neq (f_*)_{\mathrm{e2e}}^{T}(\mathbf{x})\bigr\}
  \subseteq
  \bigl\{\mathbf{x}\;:\;H(\mathbf{x})\neq (f_*)_{\mathrm{CoT}}^{T}(\mathbf{x})\bigr\}.$$
  Let $\mathbf{x}$ belong to the left-hand set. By hypothesis
  $h(\mathbf{x})=H(\mathbf{x})[-1]$, and by \cref{def:end-to-end}
  $(f_*)_{\mathrm{e2e}}^{T}(\mathbf{x})=(f_*)_{\mathrm{CoT}}^{T}(\mathbf{x})[-1]$. Hence the
  last tokens of $H(\mathbf{x})$ and of $(f_*)_{\mathrm{CoT}}^{T}(\mathbf{x})$ differ, so the
  two strings differ, i.e. $\mathbf{x}$ belongs to the right-hand set. Monotonicity of the
  probability measure $\mathcal{D}$ now gives the claimed inequality, using
  \cref{def:cot-loss} for the left-hand side. -/)
  (title := /-- The end-to-end loss is dominated by the trace-level error -/)
  (latexEnv := "lemma")]
lemma cot_error_le_supervised_error (D : PMF (List Bool)) (fstar : List Bool → Bool) (T : ℕ)
    (h : List Bool → Bool) (H : List Bool → List Bool)
    (hH : ∀ y : List Bool, h y = (H y).getLastD false) :
    cot_loss D fstar T h ≤ supervised_error (D.map (fun x => (x, cot_trace fstar T x))) H := by
  unfold cot_loss supervised_error
  rw [PMF.toOuterMeasure_map_apply]
  refine PMF.toOuterMeasure_mono D ?_
  rintro x ⟨hx, -⟩
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hx ⊢
  intro hEq
  exact hx (by rw [hH x, hEq, end_to_end])

@[blueprint "lem:cot-consistent-generalization"
  (statement := /-- There is a universal constant $c>0$ such that the following holds. Let
  $\mathcal{F}\subseteq\Sigma^{\Sigma^*}$ be a base class, let $T,k,m\in\mathbb{N}$ with
  $\mathrm{VC}\bigl(\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T})\bigr)\le k$, and let
  $\varepsilon,\delta\in(0,1)$ satisfy
  $$m\;\ge\;c\cdot\frac{k\log(12/\varepsilon)+\log(2/\delta)}{\varepsilon}.$$
  Then for every chain-of-thought consistent rule $A$ for $\mathcal{F}$ at length $T$ on $m$
  traces, in the sense of \cref{def:cot-consistent-rule}, every distribution $\mathcal{D}$ on
  $\Sigma^*$ and every $f_*\in\mathcal{F}$, with probability at least $1-\delta$ over
  $\mathbf{x}_1,\dots,\mathbf{x}_m$ drawn i.i.d. from $\mathcal{D}$ we have
  $$L^{01}_{\mathcal{D},f_*}
  \bigl(A\bigl((f_*)_{\mathrm{CoT}}^{T}(\mathbf{x}_1),\dots,
  (f_*)_{\mathrm{CoT}}^{T}(\mathbf{x}_m)\bigr)\bigr)\;\le\;\varepsilon,$$
  with $L^{01}_{\mathcal{D},f_*}$ as in \cref{def:cot-loss} and the i.i.d. sample distribution
  as in \cref{def:iid-sample}. -/)
  (proof := /-- Let $c>0$ be the universal constant provided by
  \cref{lem:loss-class-gen-bound}, and let $\mathcal{F},T,k,m,\varepsilon,\delta,A,\mathcal{D}$
  and $f_*$ be as in the statement. Put $\mathcal{H}=\mathcal{F}_{\mathrm{CoT}}^{T}$ and let
  $\mathcal{D}'$ be the push-forward of $\mathcal{D}$ along
  $\mathbf{x}\mapsto\bigl(\mathbf{x},(f_*)_{\mathrm{CoT}}^{T}(\mathbf{x})\bigr)$.

  By \cref{lem:cot-realizable} the distribution $\mathcal{D}'$ is realizable by $\mathcal{H}$.
  By \cref{lem:cot-consistent-induces-supervised} there is a rule $A'$ that is consistent for
  $\mathcal{H}$ and satisfies, for every $(\mathbf{x}_1,\dots,\mathbf{x}_m)$,
  $$A\bigl((f_*)_{\mathrm{CoT}}^{T}(\mathbf{x}_1),\dots,
  (f_*)_{\mathrm{CoT}}^{T}(\mathbf{x}_m)\bigr)(\mathbf{y})
  =A'\bigl(S(\mathbf{x})\bigr)(\mathbf{y})[-1]
  \quad\text{for all }\mathbf{y}\in\Sigma^*,$$
  where $S(\mathbf{x})$ denotes the labelled sample
  $\bigl((\mathbf{x}_i,(f_*)_{\mathrm{CoT}}^{T}(\mathbf{x}_i))\bigr)_{i=1}^{m}$. Hence
  \cref{lem:cot-error-le-supervised-error}, applied with
  $h=A\bigl((f_*)_{\mathrm{CoT}}^{T}(\mathbf{x}_1),\dots\bigr)$ and
  $H=A'(S(\mathbf{x}))$, yields for every $(\mathbf{x}_1,\dots,\mathbf{x}_m)$
  $$L^{01}_{\mathcal{D},f_*}
  \bigl(A\bigl((f_*)_{\mathrm{CoT}}^{T}(\mathbf{x}_1),\dots,
  (f_*)_{\mathrm{CoT}}^{T}(\mathbf{x}_m)\bigr)\bigr)
  \;\le\;L_{\mathcal{D}'}\bigl(A'(S(\mathbf{x}))\bigr).$$
  Consequently the event that the left-hand side exceeds $\varepsilon$ is contained in the
  event that $L_{\mathcal{D}'}\bigl(A'(S(\mathbf{x}))\bigr)$ exceeds $\varepsilon$, and it
  suffices to bound the probability of the latter by $\delta$.

  The map $\mathbf{x}\mapsto S(\mathbf{x})$ is the coordinatewise application of
  $\mathbf{x}\mapsto\bigl(\mathbf{x},(f_*)_{\mathrm{CoT}}^{T}(\mathbf{x})\bigr)$, so by
  \cref{lem:iid-sample-map} the law of $S(\mathbf{x})$ when
  $\mathbf{x}\sim\mathcal{D}^{m}$ is exactly $(\mathcal{D}')^{m}$. Since
  $\mathrm{VC}\bigl(\mathcal{L}^{01}(\mathcal{H})\bigr)\le k$, since $A'$ is consistent for
  $\mathcal{H}$, since $\mathcal{D}'$ is realizable by $\mathcal{H}$ and since
  $m\ge c\bigl(k\log(12/\varepsilon)+\log(2/\delta)\bigr)/\varepsilon$, which is verbatim the
  sample-size hypothesis of \cref{lem:loss-class-gen-bound} for the same constant $c$,
  \cref{lem:loss-class-gen-bound} bounds the probability that
  $L_{\mathcal{D}'}(A'(S))>\varepsilon$ for $S\sim(\mathcal{D}')^{m}$ by $\delta$. Combining
  the last two statements bounds the probability of the event in question by $\delta$, which is
  the assertion. -/)
  (title := /-- Generalization guarantee for chain-of-thought consistent rules -/)
  (latexEnv := "lemma")]
lemma cot_consistent_generalization :
    ∃ c : ℝ, 0 < c ∧ ∀ (F : Set (List Bool → Bool)) (T k m : ℕ),
      vc_dim (loss_class (cot_class F T)) ≤ (k : ℕ∞) →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        c * (((k : ℝ) * Real.log (12 / ε) + Real.log (2 / δ)) / ε) ≤ (m : ℝ) →
        ∀ A : (Fin m → List Bool) → (List Bool → Bool), cot_consistent_rule F T m A →
          ∀ (D : PMF (List Bool)) (fstar : List Bool → Bool), fstar ∈ F →
            (iid_sample D m).toOuterMeasure
                {x : Fin m → List Bool |
                  ENNReal.ofReal ε < cot_loss D fstar T (A (fun i => cot_trace fstar T (x i)))}
              ≤ ENNReal.ofReal δ := by
  obtain ⟨c, hc, hgen⟩ := loss_class_gen_bound
  refine ⟨c, hc, ?_⟩
  intro F T k m hvc ε δ hε hε_one hδ hδ_one hsample A hA D fstar hf
  obtain ⟨A', hA', hAeq⟩ := cot_consistent_induces_supervised F T m A hA
  have hbound :=
    hgen (cot_class F T) k m hvc ε δ hε hε_one hδ hδ_one hsample A' hA'
      (D.map (fun x => (x, cot_trace fstar T x))) (cot_realizable F T fstar hf D)
  rw [iid_sample_map, PMF.toOuterMeasure_map_apply] at hbound
  refine (PMF.toOuterMeasure_mono (iid_sample D m) ?_).trans hbound
  rintro x hx
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hx ⊢
  exact hx.1.trans_le
    (cot_error_le_supervised_error D fstar T
      (A (fun i => cot_trace fstar T (x i)))
      (A' (fun i => (x i, cot_trace fstar T (x i)))) (hAeq x fstar hf))

@[blueprint "thm:cot-VC"
  (statement := /-- There is a universal constant $c>0$ such that the following holds. For every
  base class $\mathcal{F}\subseteq\{0,1\}^{\{0,1\}^{*}}$, every positive integer generation
  length $T$, and every $d\in\mathbb{N}$ satisfying $\mathrm{VC}(\mathcal{F})\le d$, the class
  $\mathcal{F}_{\mathrm{e2e}}^{T}$ is $\mathrm{CoT}$-learnable by every chain-of-thought
  consistent rule with sample-complexity function
  $$m_{\mathrm{CoT}}^{T}(\varepsilon,\delta)
  =\Bigl\lceil c\,\varepsilon^{-1}\bigl(d\log(2T)\log(12/\varepsilon)
  +\log(2/\delta)\bigr)\Bigr\rceil$$
  for $\varepsilon,\delta\in(0,1)$. Here $\mathcal{F}_{\mathrm{e2e}}^{T}$ is as in
  \cref{def:end-to-end-class}, $\mathrm{CoT}$-learnability with a specified sample-complexity
  function is as in \cref{def:cot-learnable-with}, chain-of-thought consistency is as in
  \cref{def:cot-consistent-rule}, the displayed function is that of
  \cref{def:cot-sample-bound}, and $\mathrm{VC}$ is as in \cref{def:vc-dim}. -/)
  (proof := /-- Let $c_0>0$ be the universal constant supplied by
  \cref{lem:cot-consistent-generalization}, and put $K=9/\ln 2$ and $c=Kc_0$. Since
  $\ln 2>0$, the constant $c$ is positive. We first show that for every admissible
  $\mathcal{F},T,d$ there is an integer $D$ such that
  $$\mathrm{VC}\bigl(\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T})\bigr)\le D
  \qquad\text{and}\qquad D\le Kd\log(2T).$$

  Suppose first that $d=0$. By \cref{lem:growth-function-le-sum-choose}, the hypothesis
  $\mathrm{VC}(\mathcal{F})\le0$ implies $\Gamma_{\mathcal{F}}(nT)\le1$ for every
  $n\in\mathbb{N}$. The estimate of \cref{lem:prefix-growth-bound} therefore gives
  $\Gamma_{\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T})}(n)\le1$. For every $n>0$ this is
  strictly smaller than $2^n$, so \cref{lem:vc-dim-le-of-growth-lt} gives
  $\mathrm{VC}(\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T}))\le0$. Thus $D=0$ has both
  required properties.

  Now suppose that $d\ge1$. By \cref{lem:vc-cot-loss-class} there is an integer $D$ such that
  $$\mathrm{VC}\bigl(\mathcal{L}^{01}(\mathcal{F}_{\mathrm{CoT}}^{T})\bigr)\le D,
  \qquad D\le3d\log_2\Bigl(\frac{2T}{\ln2}\Bigr).$$
  The standard inequalities $1/2\le\ln2<1$ imply
  $1/\ln2\le2$ and $\log(1/\ln2)\le1/\ln2-1\le1$. Since $T\ge1$, we also have
  $1\le2\log(2T)$. Consequently
  $$\log\Bigl(\frac{2T}{\ln2}\Bigr)
  =\log(2T)+\log(1/\ln2)\le3\log(2T),$$
  and division by the positive number $\ln2$ yields
  $D\le(9/\ln2)d\log(2T)=Kd\log(2T)$.

  Fix $\varepsilon,\delta\in(0,1)$. The three logarithms
  $\log(2T)$, $\log(12/\varepsilon)$, and $\log(2/\delta)$ are positive, and $K\ge1$.
  Hence the preceding bound on $D$ gives
  $$D\log(12/\varepsilon)+\log(2/\delta)
  \le K\bigl(d\log(2T)\log(12/\varepsilon)+\log(2/\delta)\bigr).$$
  Multiplying by $c_0/\varepsilon$ shows that the real quantity required by
  \cref{lem:cot-consistent-generalization} is at most
  $$c\,\varepsilon^{-1}
  \bigl(d\log(2T)\log(12/\varepsilon)+\log(2/\delta)\bigr).$$
  Its natural ceiling, which is exactly the function of \cref{def:cot-sample-bound}, is no
  smaller. Applying \cref{lem:cot-consistent-generalization} with the preceding value of $D$
  proves the learnability assertion of \cref{def:cot-learnable-with}. -/)
  (title := /-- Sample complexity of chain-of-thought learning in terms of VC dimension -/)
  (latexEnv := "theorem")]
theorem cot_VC :
    ∃ c : ℝ, 0 < c ∧ ∀ (F : Set (List Bool → Bool)) (T d : ℕ), 0 < T →
      vc_dim F ≤ (d : ℕ∞) → cot_learnable_with F T (cot_sample_bound c d T) := by
  obtain ⟨c₀, hc₀, hgen⟩ := cot_consistent_generalization
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
    convert Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) (by norm_num) using 1 <;> norm_num
  have hlog2_lt_one : Real.log 2 < 1 := by
    convert Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num) using 1 <;>
      norm_num
  refine ⟨9 * c₀ / Real.log 2, div_pos (mul_pos (by norm_num) hc₀) hlog2, ?_⟩
  intro F T d hT hvc
  have hT_one : 1 ≤ T := by omega
  obtain ⟨D, hDvc, hDbound⟩ :
      ∃ D : ℕ, vc_dim (loss_class (cot_class F T)) ≤ (D : ℕ∞) ∧
        (D : ℝ) ≤ (9 / Real.log 2) * (d : ℝ) * Real.log (2 * (T : ℝ)) := by
    rcases d.eq_zero_or_pos with rfl | hd
    · refine ⟨0, vc_dim_le_of_growth_lt _ 0 ?_, by norm_num⟩
      intro n hn
      have hloss := prefix_growth_bound F T n
      have hbase : growth_function F (n * T) ≤ 1 := by
        simpa using growth_function_le_sum_choose F 0 (n * T) hvc
      exact lt_of_le_of_lt (hloss.trans hbase) (Nat.one_lt_two_pow (Nat.ne_of_gt hn))
    · obtain ⟨D, hDvc, hDbound⟩ := vc_cot_loss_class F T d hT_one hd hvc
      refine ⟨D, hDvc, hDbound.trans ?_⟩
      have htwoTpos : 0 < 2 * (T : ℝ) := by positivity
      have hlog_twoT_lower : Real.log 2 ≤ Real.log (2 * (T : ℝ)) := by
        apply (Real.log_le_log_iff (by norm_num) htwoTpos).2
        exact_mod_cast (show 2 ≤ 2 * T by omega)
      have hinvlog_bound : 1 / Real.log 2 ≤ 2 := by
        apply (div_le_iff₀ hlog2).2
        nlinarith
      have hneglog : -Real.log (Real.log 2) ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (x := 1 / Real.log 2) (by positivity)
        rw [Real.log_div (by norm_num) hlog2.ne', Real.log_one] at h
        nlinarith
      have hlogquot :
          Real.log (2 * (T : ℝ) / Real.log 2) ≤ 3 * Real.log (2 * (T : ℝ)) := by
        rw [Real.log_div htwoTpos.ne' hlog2.ne']
        nlinarith
      have hlogb : Real.logb 2 (2 * (T : ℝ) / Real.log 2) ≤
          3 * Real.log (2 * (T : ℝ)) / Real.log 2 := by
        exact (div_le_div_iff_of_pos_right hlog2).2 hlogquot
      calc
        3 * (d : ℝ) * Real.logb 2 (2 * (T : ℝ) / Real.log 2)
            ≤ 3 * (d : ℝ) * (3 * Real.log (2 * (T : ℝ)) / Real.log 2) :=
          mul_le_mul_of_nonneg_left hlogb (by positivity)
        _ = (9 / Real.log 2) * (d : ℝ) * Real.log (2 * (T : ℝ)) := by ring
  unfold cot_learnable_with
  intro ε δ hε hε_one hδ hδ_one A hA P fstar hf
  have hlogT : 0 < Real.log (2 * (T : ℝ)) := by
    apply Real.log_pos
    have hTreal : (1 : ℝ) ≤ T := by exact_mod_cast hT_one
    nlinarith
  have hlogε : 0 < Real.log (12 / ε) := by
    apply Real.log_pos
    apply (lt_div_iff₀ hε).2
    nlinarith
  have hlogδ : 0 < Real.log (2 / δ) := by
    apply Real.log_pos
    apply (lt_div_iff₀ hδ).2
    nlinarith
  have hK : 1 ≤ 9 / Real.log 2 := by
    apply (le_div_iff₀ hlog2).2
    nlinarith
  have hdelta_scaled : Real.log (2 / δ) ≤ (9 / Real.log 2) * Real.log (2 / δ) := by
    calc
      Real.log (2 / δ) = 1 * Real.log (2 / δ) := by ring
      _ ≤ (9 / Real.log 2) * Real.log (2 / δ) :=
        mul_le_mul_of_nonneg_right hK hlogδ.le
  have hinside :
      (D : ℝ) * Real.log (12 / ε) + Real.log (2 / δ) ≤
        (9 / Real.log 2) *
          ((d : ℝ) * Real.log (2 * (T : ℝ)) * Real.log (12 / ε) + Real.log (2 / δ)) := by
    calc
      (D : ℝ) * Real.log (12 / ε) + Real.log (2 / δ)
          ≤ ((9 / Real.log 2) * (d : ℝ) * Real.log (2 * (T : ℝ))) *
              Real.log (12 / ε) + Real.log (2 / δ) :=
        add_le_add_left (mul_le_mul_of_nonneg_right hDbound hlogε.le) _
      _ ≤ ((9 / Real.log 2) * (d : ℝ) * Real.log (2 * (T : ℝ))) *
              Real.log (12 / ε) + (9 / Real.log 2) * Real.log (2 / δ) :=
        add_le_add_right hdelta_scaled _
      _ = (9 / Real.log 2) *
          ((d : ℝ) * Real.log (2 * (T : ℝ)) * Real.log (12 / ε) + Real.log (2 / δ)) := by
        ring
  have hreal :
      c₀ * (((D : ℝ) * Real.log (12 / ε) + Real.log (2 / δ)) / ε) ≤
        (9 * c₀ / Real.log 2) *
          (ε⁻¹ * ((d : ℝ) * Real.log (2 * (T : ℝ)) * Real.log (12 / ε) +
            Real.log (2 / δ))) := by
    calc
      c₀ * (((D : ℝ) * Real.log (12 / ε) + Real.log (2 / δ)) / ε)
          = (c₀ * ε⁻¹) * ((D : ℝ) * Real.log (12 / ε) + Real.log (2 / δ)) := by
        ring
      _ ≤ (c₀ * ε⁻¹) * ((9 / Real.log 2) *
            ((d : ℝ) * Real.log (2 * (T : ℝ)) * Real.log (12 / ε) +
              Real.log (2 / δ))) :=
        mul_le_mul_of_nonneg_left hinside (mul_nonneg hc₀.le (inv_nonneg.mpr hε.le))
      _ = (9 * c₀ / Real.log 2) *
          (ε⁻¹ * ((d : ℝ) * Real.log (2 * (T : ℝ)) * Real.log (12 / ε) +
            Real.log (2 / δ))) := by
        ring
  have hsample :
      c₀ * (((D : ℝ) * Real.log (12 / ε) + Real.log (2 / δ)) / ε) ≤
        (cot_sample_bound (9 * c₀ / Real.log 2) d T ε δ : ℝ) := by
    refine hreal.trans ?_
    exact Nat.le_ceil _
  exact hgen F T D (cot_sample_bound (9 * c₀ / Real.log 2) d T ε δ) hDvc
    ε δ hε hε_one hδ hδ_one hsample A hA P fstar hf
